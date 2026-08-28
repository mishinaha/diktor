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

(* ---- クラス表 ---- *)

type class_info = {
  ci_name : oid;
  ci_param_kind : Type.kind;
  ci_derive_structural : bool;
  ci_methods : (string * Type.ty) list; (* メソッド名 → Generic マーク済みスキーマ *)
}

let classes : (oid, class_info) Hashtbl.t = Hashtbl.create 64

let find_class c = Hashtbl.find_opt classes c

(* ---- インスタンス表: (クラス, 型構成子の頭) → 前提(§7.4) ---- *)

type instance_info = { ii_premises : (int * oid) list (* 引数位置 → 要求クラス *) }

let instances : (oid * oid, instance_info) Hashtbl.t = Hashtbl.create 256

(* コヒーレンス: 重複キーを拒否。それだけ(sample.kel:276) *)
let add_instance ~cls ~con premises =
  if Hashtbl.mem instances (cls, con) then
    type_error
      ("インスタンス " ^ Type.name_of cls ^ "[" ^ Type.name_of con ^ "] が二重に宣言されています(コヒーレンス違反)")
  else Hashtbl.add instances (cls, con) { ii_premises = premises }

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

let register_builtins () =
  (* 組み込み型(D13: 実行できる幅は3種。他の名前の受理と拒否は elab が行う) *)
  List.iter
    (fun n -> Hashtbl.replace con_kinds (intern n) Type.KStar)
    [ "Boolean"; "Int32"; "Int64"; "Float64"; "String"; "Never" ];
  let numerics = [ "Int32"; "Int64"; "Float64" ] in
  (* クラスとメソッド(sample.kel:286-320 のプレリュード相当を decls 直登録。M4) *)
  let def_class name ~derive ~methods ~instances:insts =
    let cls = intern name in
    Hashtbl.replace classes cls
      { ci_name = cls; ci_param_kind = Type.KStar; ci_derive_structural = derive; ci_methods = methods cls };
    List.iter (fun con -> add_instance ~cls ~con:(intern con) []) insts
  in
  def_class "Add" ~derive:false
    ~methods:(fun c -> [ ("add", snd (method_scheme ~cls:c ~arity:2 ~ret:(fun a -> a))) ])
    ~instances:("String" :: numerics);
  def_class "Sub" ~derive:false
    ~methods:(fun c -> [ ("sub", snd (method_scheme ~cls:c ~arity:2 ~ret:(fun a -> a))) ])
    ~instances:numerics;
  def_class "Mul" ~derive:false
    ~methods:(fun c -> [ ("mul", snd (method_scheme ~cls:c ~arity:2 ~ret:(fun a -> a))) ])
    ~instances:numerics;
  def_class "Div" ~derive:false
    ~methods:(fun c -> [ ("div", snd (method_scheme ~cls:c ~arity:2 ~ret:(fun a -> a))) ])
    ~instances:numerics;
  def_class "Eq" ~derive:true
    ~methods:(fun c -> [ ("eq", snd (method_scheme ~cls:c ~arity:2 ~ret:(fun _ -> Type.t_boolean))) ])
    ~instances:("String" :: "Boolean" :: numerics);
  def_class "Ord" ~derive:false
    ~methods:(fun c ->
      List.map
        (fun m -> (m, snd (method_scheme ~cls:c ~arity:2 ~ret:(fun _ -> Type.t_boolean))))
        [ "lt"; "le"; "gt"; "ge" ])
    ~instances:("String" :: numerics);
  def_class "Show" ~derive:false
    ~methods:(fun c -> [ ("show", snd (method_scheme ~cls:c ~arity:1 ~ret:(fun _ -> Type.t_string))) ])
    ~instances:("String" :: "Boolean" :: numerics);
  (* 予約述語(D8)。メソッドなしのクラスとして表に相乗りさせる *)
  def_class "Integral" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Int32"; "Int64" ];
  def_class "Fractional" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Float64" ];
  (* Never は ctor ゼロのデータ宣言(complete_sig が Some [] を返し、節ゼロの match が網羅になる) *)
  add_data { dd_name = intern "Never"; dd_params = []; dd_ctors = []; dd_opaque = false }

(* クラスメソッドを値環境に登録するための一覧(非修飾名と修飾名の両方、§7.4) *)
let builtin_values () =
  Hashtbl.fold
    (fun _ ci acc ->
      List.fold_left
        (fun acc (m, ty) -> (m, ty) :: (Type.name_of ci.ci_name ^ "." ^ m, ty) :: acc)
        acc ci.ci_methods)
    classes []

let reset () =
  Hashtbl.reset con_kinds;
  Hashtbl.reset aliases;
  Hashtbl.reset classes;
  Hashtbl.reset instances;
  Hashtbl.reset datas;
  Hashtbl.reset ctor_owner;
  register_builtins ()

let () = register_builtins ()
