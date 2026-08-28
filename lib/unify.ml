(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * レベル方式 HM の中核(計画 §7.2)。MiniLang.scala §5-§7 の直訳 +
 * Keleut 差分(TArrow 3要素、予約述語、Rigid の2役)。
 * level はグローバルにせず常に引数で渡す(R9)。
 *)
open Aux
open Syntax
open Type

(* ---- カインド計算(MiniLang:638-644)---- *)

let rec drop_arrows k n =
  if n = 0 then k
  else
    match kind_repr k with
    | KArrow (_, r) -> drop_arrows r (n - 1)
    | KVar r ->
        (* 使用位置からカインドを確定させる(D7) *)
        let res = new_kind_var () in
        r.k_link <- Some (KArrow (new_kind_var (), res));
        drop_arrows res (n - 1)
    | KStar | KRow -> type_error "型構成子ではない型に型引数が適用されています"

let var_info_of r = match !r with Unbound i | Generic i | Rigid i -> i | Link _ -> bug "var_info_of: Link"

let rec kind_of t =
  match repr t with
  | TRowEmpty | TRowExtend _ -> KRow
  | TVar r -> (var_info_of r).vkind
  | TCon (n, args) -> drop_arrows (Decls.con_kind n (List.length args)) (List.length args)
  | TApp (f, _) -> drop_arrows (kind_of f) 1
  | TArrow _ | TRecord _ | TVariant _ -> KStar

(* ---- occurs check + レベル調整 + Rigid 脱出検査(MiniLang:612-631)---- *)

let show_ref : (ty -> string) ref = ref (fun _ -> "<型>") (* Show が後から差し込む(循環回避) *)

let show t = !show_ref t

let show2_ref : (ty -> ty -> string) ref = ref (fun _ _ -> "<型>")

let show2 a b = !show2_ref a b

let rec occurs_adjust tv lvl t =
  match repr t with
  | TVar v ->
      if v == tv then type_error "occurs check に失敗しました(無限型が発生します)";
      (match !v with
      | Unbound i -> if i.vlevel > lvl then v := Unbound { i with vlevel = lvl }
      | Rigid i ->
          (* 剛定数はレベルを下げられない。下げる代わりにエラーにする *)
          if i.vlevel > lvl then type_error ("スコープ付きの型 " ^ show (TVar v) ^ " がスコープの外に漏れています")
      | Generic _ -> bug "単一化中に Generic 変数が現れました"
      | Link _ -> ())
  | TCon (_, args) -> List.iter (occurs_adjust tv lvl) args
  | TApp (f, a) ->
      occurs_adjust tv lvl f;
      occurs_adjust tv lvl a
  | TArrow (p, r, e) ->
      occurs_adjust tv lvl p;
      occurs_adjust tv lvl r;
      occurs_adjust tv lvl e
  | TRecord row | TVariant row -> occurs_adjust tv lvl row
  | TRowEmpty -> ()
  | TRowExtend (_, f, rest) ->
      occurs_adjust tv lvl f;
      occurs_adjust tv lvl rest

(* ---- クラス制約の伝播(MiniLang:662-696 + D8 の予約述語)---- *)

let is_predicate c = c = cls_integral || c = cls_fractional

(* 述語つき変数の台帳(宣言終了時の default_numerics が掃く) *)
let predicate_vars : tvar ref list ref = ref []

let rec add_class t c =
  let ci =
    match Decls.find_class c with Some ci -> ci | None -> type_error ("未知のクラス: " ^ name_of c)
  in
  if not (same_kind ci.ci_param_kind (kind_of t)) then
    type_error
      ("クラス " ^ name_of c ^ " は " ^ show_kind ci.ci_param_kind ^ " のクラスですが、" ^ show t ^ " に要求されました");
  match repr t with
  | TVar v -> (
      match !v with
      | Unbound i ->
          if not (List.mem c i.vcls) then (
            v := Unbound { i with vcls = c :: i.vcls };
            if is_predicate c then predicate_vars := v :: !predicate_vars)
      | Rigid i ->
          if not (List.mem c i.vcls) then
            if is_predicate c then
              type_error "型パラメータに数値リテラルは使えません。0i32 のように接尾辞を付けるか具体型を使ってください"
            else
              type_error
                ("型パラメータ " ^ show (TVar v) ^ " は " ^ name_of c ^ " のインスタンスではありません。[A: " ^ name_of c
               ^ "] のように制約を書いてください")
      | _ -> type_error (show t ^ " に " ^ name_of c ^ " 制約を付けられません"))
  | TCon (n, args) -> (
      match Decls.find_instance ~cls:c ~con:n with
      | Some { ii_premises; _ } ->
          List.iter (fun (i, c2) -> if i < List.length args then add_class (List.nth args i) c2) ii_premises
      | None -> type_error (name_of n ^ " は " ^ name_of c ^ " のインスタンスではありません"))
  | (TRecord row | TVariant row) when ci.ci_derive_structural ->
      (* 閉じた行への構造的導出(sample.kel:305-309)。開いた行は不可 *)
      let fields, tail = row_fields row in
      (match repr tail with
      | TRowEmpty -> List.iter (fun (_, f) -> add_class f c) fields
      | _ -> type_error ("行変数を含む型 " ^ show t ^ " に " ^ name_of c ^ " の構造的導出は適用できません(行が閉じていません)"))
  | TApp _ -> type_error ("制約 " ^ name_of c ^ " を " ^ show t ^ " に付けられません(頭が型変数の適用には制約を貼れません)")
  | other -> type_error (show other ^ " は " ^ name_of c ^ " のインスタンスではありません")

(* ---- 代入(MiniLang:703-715)---- *)

let bind v t =
  match !v with
  | Unbound { vlevel; vkind; vcls; _ } ->
      if not (same_kind vkind (kind_of t)) then
        type_error ("カインドが一致しません: " ^ show (TVar v) ^ " :: " ^ show_kind vkind ^ " と " ^ show t);
      occurs_adjust v vlevel t;
      List.iter (fun c -> add_class t c) vcls;
      v := Link t
  | _ -> bug "束縛できない変数への bind"

let unbound_var t = match t with TVar ({ contents = Unbound _ } as r) -> Some r | _ -> None

(* ---- 行の単一化 — Scoped Labels(MiniLang:794-842)---- *)

(* 行の中から最初の label を探して先頭に持ち上げ、(フィールド型, 残り) を返す。
   行変数を伸ばすときは新変数を「その変数自身のレベル」で作る(MiniLang:805-808 の罠回避)。
   フィールドは新変数経由で(呼び出し側の unify → bind で)単一化されるため
   レベル調整が必ず走る(既存バグ 0.2-11 の修正形) *)
let rec rewrite_row row label =
  match repr row with
  | TRowEmpty -> type_error ("ラベル " ^ name_of label ^ " がありません(行は閉じています)")
  | TRowExtend (l, f, rest) when l = label -> (f, rest)
  | TRowExtend (l, f, rest) ->
      let f2, rest2 = rewrite_row rest label in
      (f2, TRowExtend (l, f, rest2))
  | TVar v -> (
      match !v with
      | Unbound { vlevel; vkind = KRow; _ } ->
          let f2 = new_var vlevel in
          let rest2 = new_row_var vlevel in
          v := Link (TRowExtend (label, f2, rest2));
          (f2, rest2)
      | _ -> type_error ("行型ではありません: " ^ show (TVar v)))
  | t -> type_error ("行型ではありません: " ^ show t)

let rec unify a b =
  let t1 = repr a in
  let t2 = repr b in
  let same_var = match (t1, t2) with TVar r1, TVar r2 -> r1 == r2 | _ -> false in
  if not (t1 == t2 || same_var) then
    match (unbound_var t1, unbound_var t2) with
    | Some v, _ -> bind v t2
    | _, Some v -> bind v t1
    | None, None -> (
        match (t1, t2) with
        | TCon (n1, as1), TCon (n2, as2) when n1 = n2 && List.length as1 = List.length as2 ->
            List.iter2 unify as1 as2
        | TApp (f1, a1), TApp (f2, a2) ->
            unify f1 f2;
            unify a1 a2
        (* f a ~ List Int → f ~ List, a ~ Int(最後の引数を剥がす。MiniLang:752-757) *)
        | TApp (f, x), TCon (n, args) when args <> [] ->
            let init, last = split_last args in
            unify f (TCon (n, init));
            unify x last
        | TCon (n, args), TApp (f, x) when args <> [] ->
            let init, last = split_last args in
            unify (TCon (n, init)) f;
            unify last x
        | TArrow (p1, r1, e1), TArrow (p2, r2, e2) ->
            unify p1 p2;
            unify r1 r2;
            unify e1 e2
        | TRecord r1, TRecord r2 -> unify r1 r2
        | TVariant r1, TVariant r2 -> unify r1 r2
        | TRowEmpty, TRowEmpty -> ()
        | TRowExtend (l, f, rest), _ -> unify_row l f rest t2
        | _, TRowExtend (l, f, rest) -> unify_row l f rest t1
        (* ここに来る TVar は Rigid(unbound は上で処理済み)。専用エラー(§7.2) *)
        | (TVar _, _ | _, TVar _) -> type_error ("スコープ付きの型が一致しません: " ^ show2 t1 t2)
        | _ -> type_error ("型が一致しません: " ^ show2 t1 t2))

and split_last = function
  | [] -> bug "split_last: empty"
  | xs ->
      let rec go acc = function [ x ] -> (List.rev acc, x) | x :: tl -> go (x :: acc) tl | [] -> assert false in
      go [] xs

(* rewrite_row は row2 の末尾変数を書き換えるが、それが rest の末尾変数と同一だと
   ρ = <l : τ | ρ> の無限行になる。書き換え前に覚えて、束縛されていたらエラー(MiniLang:826-833) *)
and unify_row label field rest row2 =
  let tail_before = row_tail_var rest in
  let field2, rest2 = rewrite_row row2 label in
  (match tail_before with
  | Some tv -> ( match !tv with Link _ -> type_error "再帰的な行型が発生しました" | _ -> ())
  | None -> ());
  (try unify field field2
   with Type_error msg when label = eff_heap -> type_error ("別の run スコープのヒープを使おうとしています(" ^ msg ^ ")"));
  unify rest rest2

(* ---- 一般化(in-place、§7.2)---- *)

(* level より深い Unbound を Generic に書き換える。Rigid は決して一般化しない。
   予約述語つき変数はここで既定値に bind する(D8: Integral → Int32, Fractional → Float64) *)
let rec generalize level t =
  match repr t with
  | TVar v -> (
      match !v with
      | Unbound i when i.vlevel > level ->
          if List.mem cls_integral i.vcls then bind v t_int32
          else if List.mem cls_fractional i.vcls then bind v t_float64
          else v := Generic i
      | _ -> ())
  | TCon (_, args) -> List.iter (generalize level) args
  | TApp (f, a) ->
      generalize level f;
      generalize level a
  | TArrow (p, r, e) ->
      generalize level p;
      generalize level r;
      generalize level e
  | TRecord row | TVariant row -> generalize level row
  | TRowEmpty -> ()
  | TRowExtend (_, f, rest) ->
      generalize level f;
      generalize level rest

(* 宣言終了時: 台帳に残った述語つき弱変数を既定値に落とす(§7.2) *)
let default_numerics () =
  List.iter
    (fun v ->
      match !v with
      | Unbound { vcls; _ } ->
          if List.mem cls_integral vcls then bind v t_int32
          else if List.mem cls_fractional vcls then bind v t_float64
      | _ -> ())
    !predicate_vars;
  predicate_vars := []

(* ---- インスタンス化・skolem 化(共通の map_generics、MiniLang:875-919)---- *)

let map_generics_with memo f t =
  let rec go t =
    match repr t with
    | TVar v -> (
        match !v with
        | Generic i -> (
            match Hashtbl.find_opt memo i.vid with
            | Some t -> t
            | None ->
                let t = f i in
                Hashtbl.add memo i.vid t;
                t)
        | _ -> TVar v)
    | TCon (n, args) -> TCon (n, List.map go args)
    | TApp (g, a) -> tapp (go g) (go a)
    | TArrow (p, r, e) -> TArrow (go p, go r, go e)
    | TRecord row -> TRecord (go row)
    | TVariant row -> TVariant (go row)
    | TRowEmpty -> TRowEmpty
    | TRowExtend (l, fld, rest) -> TRowExtend (l, go fld, go rest)
  in
  go t

let map_generics f t = map_generics_with (Hashtbl.create 8) f t

(* Generic → 現在のレベルの新しい未定変数。カインドと制約集合ごとコピーする
   (ここが型クラスの複製点。既存実装はここが抜けていた、§7.2)。
   述語つき複製は台帳にも載せる *)
let instantiate level t =
  map_generics
    (fun i ->
      let v = new_var ~kind:i.vkind ~classes:i.vcls level in
      (match v with
      | TVar r when List.exists is_predicate i.vcls -> predicate_vars := r :: !predicate_vars
      | _ -> ());
      v)
    t

(* Generic → 現在のレベルの新しい剛定数(注釈の skolem 化) *)
let skolemize level t = map_generics (fun i -> TVar (ref (Rigid { i with vid = new_oid (); vlevel = level }))) t

(* Generic → 指定した型(データ宣言・エフェクト宣言のパラメータ置換) *)
let subst_params level args t =
  map_generics
    (fun i -> match List.assoc_opt i.vid args with Some t -> t | None -> new_var ~kind:i.vkind ~classes:i.vcls level)
    t

let reset () = predicate_vars := []
