(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * 宣言表(計画 §7.1)。型構成子のカインド、型エイリアス、クラス、インスタンス、
 * 予約述語(Integral / Fractional)の組み込み表と組み込み登録。
 * newtype 表は M5、effect 表は M6 で追加する。
 *)
open Aux
open Syntax
module T = Tree.Tree

(* ---- 型構成子のカインド表(MiniLang の conKinds) ---- *)

let con_kinds : (oid, Type.kind) Hashtbl.t = Hashtbl.create 64

(* 未知の構成子は飽和形とみなす(MiniLang:641 と同じ既定) *)
let con_kind c nargs = match Hashtbl.find_opt con_kinds c with Some k -> k | None -> Type.k_arrow nargs

(* ---- 型エイリアス(透過。展開時に毎回 elaborate する、§7.3) ---- *)

type alias_info = {
  al_name : oid;
  al_params : type_param list;
  al_kind : string option; (* : Type / : EffectRow *)
  al_body : T.type_exp;
}

let aliases : (oid, alias_info) Hashtbl.t = Hashtbl.create 64

let add_alias info =
  if Hashtbl.mem aliases info.al_name then
    type_error ("型エイリアス " ^ Type.name_of info.al_name ^ " が二重に宣言されています")
  else Hashtbl.add aliases info.al_name info

(* ---- newtype(データ宣言)表(M5、§7.3) ---- *)

type field_info = { fi_label : oid option; fi_ty : Type.ty (* パラメータは Generic マーク *) }

type ctor_info = { ct_name : oid; ct_fields : field_info list }

type data_info = {
  dd_name : oid;
  dd_params : Type.var_info list; (* Generic 変数の情報(vid で subst_params する) *)
  dd_ctors : ctor_info list; (* Never は [] *)
  dd_opaque : bool; (* newtype X = ??? *)
}

let datas : (oid, data_info) Hashtbl.t = Hashtbl.create 64

let ctor_owner : (oid, oid) Hashtbl.t = Hashtbl.create 128 (* ctor 名 → data 名 *)

let add_data info =
  if Hashtbl.mem datas info.dd_name then type_error ("newtype " ^ Type.name_of info.dd_name ^ " が二重に宣言されています")
  else (
    Hashtbl.add datas info.dd_name info;
    List.iter
      (fun ct ->
        if Hashtbl.mem ctor_owner ct.ct_name then
          type_error ("コンストラクタ " ^ Type.name_of ct.ct_name ^ " が二重に宣言されています(コンストラクタ名は大域一意)")
        else Hashtbl.add ctor_owner ct.ct_name info.dd_name)
      info.dd_ctors)

(* ---- エフェクト表(M6、§7.3 / D22) ---- *)

type effect_info = {
  ef_name : oid;
  ef_ops : (oid * Type.ty) list; (* 非修飾 op 名 → スキーマ TArrow(引数行, 返り値, ρ)(Generic 化済み) *)
}

let effects : (oid, effect_info) Hashtbl.t = Hashtbl.create 32

(* D22: 操作名の重複宣言を許す(sample.kel 自身が Console.write と File.write を宣言)。
   非修飾 op 名 → 宣言順の所属エフェクト列 *)
let op_index : (oid, oid list) Hashtbl.t = Hashtbl.create 64

let add_effect info =
  if Hashtbl.mem effects info.ef_name then
    type_error ("effect " ^ Type.name_of info.ef_name ^ " が二重に宣言されています")
  else (
    Hashtbl.add effects info.ef_name info;
    List.iter
      (fun (op, _) ->
        let prev = Option.value ~default:[] (Hashtbl.find_opt op_index op) in
        Hashtbl.replace op_index op (prev @ [ info.ef_name ]))
      info.ef_ops)

let find_effect e = Hashtbl.find_opt effects e

let op_candidates op = Option.value ~default:[] (Hashtbl.find_opt op_index op)

(* ---- クラス表 ---- *)

type class_info = {
  ci_name : oid;
  ci_param : Type.var_info; (* クラスパラメータの Generic 変数(インスタンス検査の代入点) *)
  ci_param_kind : Type.kind;
  ci_derive_structural : bool;
  ci_builtin : bool;
  ci_methods : (string * Type.ty) list; (* メソッド名 → Generic マーク済みスキーマ *)
}

let classes : (oid, class_info) Hashtbl.t = Hashtbl.create 64

let find_class c = Hashtbl.find_opt classes c

(* 組み込みと同名のユーザ宣言は「照合の上で受理」(実体は組み込みのまま)。
   sample.kel 自身がプレリュード相当の Add 等を宣言するため(§7.4 の運用裁定) *)
let add_class_decl info =
  match Hashtbl.find_opt classes info.ci_name with
  | Some prev when prev.ci_builtin -> `Builtin prev
  | Some _ -> type_error ("type class " ^ Type.name_of info.ci_name ^ " が二重に宣言されています")
  | None ->
      Hashtbl.add classes info.ci_name info;
      `Added

(* ---- インスタンス表: (クラス, 型構成子の頭) → 前提(§7.4) ---- *)

type instance_info = {
  ii_premises : (int * oid) list; (* 引数位置 → 要求クラス *)
  ii_builtin : bool;
  ii_methods : (oid * T.let_binding) list; (* ユーザ宣言のメソッド本体(interp のディスパッチ用) *)
}

let instances : (oid * oid, instance_info) Hashtbl.t = Hashtbl.create 256

(* コヒーレンス: 重複キーを拒否。それだけ(sample.kel:276)。
   組み込みと同じキーのユーザ宣言は照合の上で受理する(本体は検査される) *)
let add_instance ?(builtin = true) ?(methods = []) ~cls ~con premises =
  match Hashtbl.find_opt instances (cls, con) with
  | Some prev when prev.ii_builtin && not builtin ->
      (* 実体は組み込みのまま。ユーザ本体は検査済みという扱い *)
      ()
  | Some _ ->
      type_error
        ("インスタンス " ^ Type.name_of cls ^ "[" ^ Type.name_of con ^ "] が二重に宣言されています(コヒーレンス違反)")
  | None -> Hashtbl.add instances (cls, con) { ii_premises = premises; ii_builtin = builtin; ii_methods = methods }

let find_instance ~cls ~con = Hashtbl.find_opt instances (cls, con)

(* ---- 組み込み登録 ---- *)

(* 登録用の Generic 変数(vlevel は Generic では使われない) *)
let generic ?(kind = Type.KStar) ?(classes = []) () =
  Type.TVar (ref (Type.Generic { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes }))

let closed_args_row tys =
  List.fold_right (fun t acc -> Type.TRowExtend (Type.l_item, t, acc)) tys Type.TRowEmpty

(* (A, A, ...) => ret @ E 形のメソッドスキーマ。省略された @ は Generic 行変数(sample.kel:315-316) *)
let method_scheme ~cls ~arity ~ret =
  let a = generic ~classes:[ cls ] () in
  let eff = generic ~kind:Type.KRow () in
  (a, Type.TArrow (Type.TRecord (closed_args_row (List.init arity (fun _ -> a))), ret a, eff))

let intern = Type.intern

(* Ref / Array / Heap / Blocking の組み込み登録(§11.2。effect パラメータ構文が
   ソースに書けないため decls が直接登録する)。行は開いた Generic 尾部にする
   (MiniLang の newref と同じ形。閉じると他のエフェクトの下で呼べない) *)
let builtin_ops : (string * Type.ty) list ref = ref []

let register_ref_array () =
  let ref_oid = intern "Ref" and arr_oid = intern "Array" in
  Hashtbl.replace con_kinds ref_oid (Type.k_arrow 2);
  Hashtbl.replace con_kinds arr_oid (Type.k_arrow 1);
  let ginfo () = { Type.vid = new_oid (); vlevel = 0; vkind = Type.KStar; vcls = [] } in
  add_data { dd_name = ref_oid; dd_params = [ ginfo (); ginfo () ]; dd_ctors = []; dd_opaque = true };
  add_data { dd_name = arr_oid; dd_params = [ ginfo () ]; dd_ctors = []; dd_opaque = true };
  (* 操作なしの組み込みエフェクトラベル *)
  add_effect { ef_name = Type.eff_heap; ef_ops = [] };
  add_effect { ef_name = Type.eff_blocking; ef_ops = [] };
  let arrow args ret eff = Type.TArrow (Type.TRecord (closed_args_row args), ret, eff) in
  let heap_row h = Type.TRowExtend (Type.eff_heap, h, generic ~kind:Type.KRow ()) in
  let def name ty = builtin_ops := !builtin_ops @ [ (name, ty) ] in
  (* Ref.new : [h, A] (A) => Ref[h, A] @ {Heap[h] extends ρ} *)
  (let h = generic () and a = generic () in
   def "Ref.new" (arrow [ a ] (Type.TCon (ref_oid, [ h; a ])) (heap_row h)));
  (let h = generic () and a = generic () in
   def "Ref.get" (arrow [ Type.TCon (ref_oid, [ h; a ]) ] a (heap_row h)));
  (let h = generic () and a = generic () in
   def "Ref.set" (arrow [ Type.TCon (ref_oid, [ h; a ]); a ] Type.t_unit (heap_row h)));
  (* Array は h を持たない(§11.2。既知の穴も §12 に記録済み) *)
  (let h = generic () and a = generic () in
   def "Array.new" (arrow [ Type.t_int32; a ] (Type.TCon (arr_oid, [ a ])) (heap_row h)));
  (let a = generic () in
   def "Array.length" (arrow [ Type.TCon (arr_oid, [ a ]) ] Type.t_int32 (generic ~kind:Type.KRow ())));
  (let h = generic () and a = generic () in
   def "Array.get" (arrow [ Type.TCon (arr_oid, [ a ]); Type.t_int32 ] a (heap_row h)));
  (let h = generic () and a = generic () in
   def "Array.set" (arrow [ Type.TCon (arr_oid, [ a ]); Type.t_int32; a ] Type.t_unit (heap_row h)));
  (let a = generic () and e = generic ~kind:Type.KRow () in
   def "Array.each" (arrow [ Type.TCon (arr_oid, [ a ]); arrow [ a ] Type.t_unit e ] Type.t_unit e))

let register_builtins () =
  (* 組み込み型(D13: 実行できる幅は3種。他の名前の受理と拒否は elab が行う) *)
  List.iter
    (fun n -> Hashtbl.replace con_kinds (intern n) Type.KStar)
    [ "Boolean"; "Int32"; "Int64"; "Float64"; "String"; "Never" ];
  let numerics = [ "Int32"; "Int64"; "Float64" ] in
  (* クラスとメソッド(sample.kel:286-320 のプレリュード相当を decls 直登録。M4)。
     クラスパラメータ変数はクラス内で共有する(インスタンス検査の代入点、M7) *)
  let def_class name ~derive ~methods ~instances:insts =
    let cls = intern name in
    let pinfo = { Type.vid = new_oid (); vlevel = 0; vkind = Type.KStar; vcls = [ cls ] } in
    let a = Type.TVar (ref (Type.Generic pinfo)) in
    Hashtbl.replace classes cls
      {
        ci_name = cls;
        ci_param = pinfo;
        ci_param_kind = Type.KStar;
        ci_derive_structural = derive;
        ci_builtin = true;
        ci_methods = methods a;
      };
    List.iter (fun con -> add_instance ~cls ~con:(intern con) []) insts
  in
  let arrow2 a ret = Type.TArrow (Type.TRecord (closed_args_row [ a; a ]), ret, generic ~kind:Type.KRow ()) in
  let arrow1 a ret = Type.TArrow (Type.TRecord (closed_args_row [ a ]), ret, generic ~kind:Type.KRow ()) in
  def_class "Add" ~derive:false ~methods:(fun a -> [ ("add", arrow2 a a) ]) ~instances:("String" :: numerics);
  def_class "Sub" ~derive:false ~methods:(fun a -> [ ("sub", arrow2 a a) ]) ~instances:numerics;
  def_class "Mul" ~derive:false ~methods:(fun a -> [ ("mul", arrow2 a a) ]) ~instances:numerics;
  def_class "Div" ~derive:false ~methods:(fun a -> [ ("div", arrow2 a a) ]) ~instances:numerics;
  def_class "Eq" ~derive:true
    ~methods:(fun a -> [ ("eq", arrow2 a Type.t_boolean) ])
    ~instances:("String" :: "Boolean" :: numerics);
  def_class "Ord" ~derive:false
    ~methods:(fun a -> List.map (fun m -> (m, arrow2 a Type.t_boolean)) [ "lt"; "le"; "gt"; "ge" ])
    ~instances:("String" :: numerics);
  def_class "Show" ~derive:false
    ~methods:(fun a -> [ ("show", arrow1 a Type.t_string) ])
    ~instances:("String" :: "Boolean" :: numerics);
  (* 予約述語(D8)。メソッドなしのクラスとして表に相乗りさせる *)
  def_class "Integral" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Int32"; "Int64" ];
  def_class "Fractional" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Float64" ];
  (* Never は ctor ゼロのデータ宣言(complete_sig が Some [] を返し、節ゼロの match が網羅になる) *)
  add_data { dd_name = intern "Never"; dd_params = []; dd_ctors = []; dd_opaque = false };
  builtin_ops := [];
  register_ref_array ()

(* クラスメソッドと組み込み値を値環境に登録するための一覧(非修飾名と修飾名の両方、§7.4) *)
let builtin_values () =
  Hashtbl.fold
    (fun _ ci acc ->
      List.fold_left
        (fun acc (m, ty) -> (m, ty) :: (Type.name_of ci.ci_name ^ "." ^ m, ty) :: acc)
        acc ci.ci_methods)
    classes []
  @ !builtin_ops

let reset () =
  Hashtbl.reset con_kinds;
  Hashtbl.reset aliases;
  Hashtbl.reset classes;
  Hashtbl.reset instances;
  Hashtbl.reset datas;
  Hashtbl.reset ctor_owner;
  Hashtbl.reset effects;
  Hashtbl.reset op_index;
  register_builtins ()

let () = register_builtins ()
