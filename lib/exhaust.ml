(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * 網羅性・到達不能検査(計画 §7.5。MiniLang §12 = Maranget JFP 2007 の移植)。
 * 検査は遅延キューに積み、各 let 束縛群の generalize の直前に drain する
 * (generalize 後に close_variant_rows が走ると Generic 化済みの行変数に
 * unify を掛けて内部エラーになるため、§7.2)。
 *
 * 移植上の唯一の罠(§7.5): CRecord のラベルは重複する(タプル = _item の連なり)。
 * MiniLang:1645 の fs.toMap は使えないため、型の行のフィールド順に沿って
 * パターン側の同名フィールドを最左から順に割り当てる(ラベルごとのキュー)。
 *)
open Aux
open Syntax
open Type
module T = Tree.Tree

(* ---- 内部パターン(列数1の行列に載せる正規形、D18)---- *)

type lit = LBool of bool | LText of string | LNum of string

type ipat =
  | IWild
  | ILit of lit
  | IVariant of oid * ipat
  | ICtor of oid * oid * ipat list (* data, ctor, フィールド宣言順に整列済み *)
  | IRecord of (oid * ipat) list * bool (* フィールド列, closed? *)

(* 数値パターンの正規化(0x1 と 1 を同一視) *)
let norm_num (n : number) =
  if n.n_is_float then match float_of_string_opt n.n_text with Some f -> string_of_float f | None -> n.n_text
  else match int_of_string_opt n.n_text with Some i -> string_of_int i | None -> n.n_text

let rec convert ((_, p) as node : T.pat) : ipat =
  match p with
  | T.PWildcard | T.PVar _ -> IWild
  | T.PBool b -> ILit (LBool b)
  | T.PText s -> ILit (LText s)
  | T.PNumber n -> ILit (LNum (norm_num n))
  | T.PAnnot (sub, _) -> convert sub
  | T.PVariant (s, sub) -> IVariant (intern s, convert sub)
  | T.PRecord (fields, rest) ->
      IRecord (List.map (fun (l, sub) -> (intern l, convert sub)) fields, rest = None)
  | T.PCtor _ -> (
      match Tree.get_resolved node with
      | Some (Tree.RCtorPat (data, ctor, field_to_arg)) ->
          let args = match p with T.PCtor (_, args) -> args | _ -> assert false in
          let subs =
            Array.to_list
              (Array.map
                 (fun ai -> match ai with Some i -> convert (List.nth args i).T.cap_pat | None -> IWild)
                 field_to_arg)
          in
          ICtor (data, ctor, subs)
      | _ -> bug "PCtor が解決されていません(elab_pat が resolved を書いていない)")

(* ---- 構成子(MiniLang:1594-1608)---- *)

type ctor = CVariant of oid | CData of oid (* ctor 名 *) | CLit of lit | CRecord of oid list

let data_of_ctor c = Hashtbl.find Decls.datas (Hashtbl.find Decls.ctor_owner c)

let ctor_fields c = (List.find (fun ct -> ct.Decls.ct_name = c) (data_of_ctor c).Decls.dd_ctors).Decls.ct_fields

let arity = function
  | CVariant _ -> 1
  | CData c -> List.length (ctor_fields c)
  | CLit _ -> 0
  | CRecord ls -> List.length ls

let record_labels ty =
  match repr ty with TRecord row -> List.map fst (fst (row_fields row)) | _ -> []

let ctor_of (p : ipat) ty =
  match p with
  | IWild -> None
  | ILit l -> Some (CLit l)
  | IVariant (l, _) -> Some (CVariant l)
  | ICtor (_, c, _) -> Some (CData c)
  | IRecord _ -> Some (CRecord (record_labels ty))

let field_type_of row label =
  match List.assoc_opt label (fst (row_fields row)) with Some t -> t | None -> new_var 0

let sub_types c ty =
  match (c, repr ty) with
  | CVariant l, TVariant row -> [ field_type_of row l ]
  | CData ctor, TCon (n, args) when Hashtbl.mem Decls.datas n ->
      let dd = Hashtbl.find Decls.datas n in
      let subst =
        try List.map2 (fun (i : var_info) a -> (i.vid, a)) dd.Decls.dd_params args with Invalid_argument _ -> []
      in
      List.map (fun f -> Unify.subst_params 0 subst f.Decls.fi_ty) (ctor_fields ctor)
  | CRecord _, TRecord row -> List.map snd (fst (row_fields row))
  | CLit _, _ -> []
  | _ -> List.init (arity c) (fun _ -> new_var 0)

(* 型の行のフィールド順に沿い、パターン側の同名フィールドを最左から順に割り当てる *)
let align_record_pat labels fields =
  let used = Array.make (List.length fields) false in
  List.map
    (fun l ->
      let rec find i = function
        | [] -> IWild
        | (l2, p) :: rest ->
            if l2 = l && not used.(i) then (
              used.(i) <- true;
              p)
            else find (i + 1) rest
      in
      find 0 fields)
    labels

let specialize c _ty rows =
  List.concat_map
    (fun row ->
      match row with
      | [] -> []
      | h :: rest -> (
          match (h, c) with
          | IWild, _ -> [ List.init (arity c) (fun _ -> IWild) @ rest ]
          | IVariant (l1, sub), CVariant l2 when l1 = l2 -> [ sub :: rest ]
          | ICtor (_, l1, subs), CData l2 when l1 = l2 -> [ subs @ rest ]
          | ILit a, CLit b when a = b -> [ rest ]
          | IRecord (fs, _), CRecord labels -> [ align_record_pat labels fs @ rest ]
          | _ -> []))
    rows

let default_matrix rows =
  List.concat_map (fun row -> match row with IWild :: rest -> [ rest ] | _ -> []) rows

let complete_sig ty =
  match repr ty with
  | TVariant row -> (
      let fs, tail = row_fields row in
      match repr tail with
      | TRowEmpty -> Some (List.sort_uniq compare (List.map (fun (l, _) -> CVariant l) fs))
      | _ -> None (* 開いた行 = ラベルはいくらでも増えうる *))
  | TCon (n, _) when Hashtbl.mem Decls.datas n ->
      let dd = Hashtbl.find Decls.datas n in
      if dd.Decls.dd_opaque then None else Some (List.map (fun ct -> CData ct.Decls.ct_name) dd.Decls.dd_ctors)
  | TCon (n, []) when n = intern "Boolean" -> Some [ CLit (LBool true); CLit (LBool false) ]
  | TRecord row -> Some [ CRecord (List.map fst (fst (row_fields row))) ]
  | _ -> None

let rebuild c ws =
  match c with
  | CVariant l -> IVariant (l, List.hd ws) :: List.tl ws
  | CData l ->
      let n = arity (CData l) in
      let rec take n = function [] -> [] | x :: tl -> if n = 0 then [] else x :: take (n - 1) tl in
      let rec drop n = function [] -> [] | _ :: tl as xs -> if n = 0 then xs else drop (n - 1) tl in
      ICtor (Hashtbl.find Decls.ctor_owner l, l, take n ws) :: drop n ws
  | CLit l -> ILit l :: ws
  | CRecord ls ->
      let n = List.length ls in
      let rec take n = function [] -> [] | x :: tl -> if n = 0 then [] else x :: take (n - 1) tl in
      let rec drop n = function [] -> [] | _ :: tl as xs -> if n = 0 then xs else drop (n - 1) tl in
      IRecord (List.combine ls (take n ws), true) :: drop n ws

(* ---- 構造的ヴァリアントの行を閉じる(MiniLang:1699-1710)---- *)

let close_row ty =
  match repr ty with
  | TVariant row -> ( match row_tail_var row with Some tv -> Unify.unify (TVar tv) TRowEmpty | None -> ())
  | _ -> ()

let rec close_variant_rows rows tys =
  match tys with
  | [] -> ()
  | ty0 :: tys_tail ->
      if rows <> [] then (
        let ty0 = repr ty0 in
        let has_default = List.exists (fun r -> match r with IWild :: _ -> true | _ -> false) rows in
        let roots =
          List.sort_uniq compare (List.concat_map (fun r -> match r with h :: _ -> Option.to_list (ctor_of h ty0) | [] -> []) rows)
        in
        if (not has_default) && roots <> [] then close_row ty0;
        let ty = repr ty0 in
        List.iter (fun c -> close_variant_rows (specialize c ty rows) (sub_types c ty @ tys_tail)) roots;
        close_variant_rows (default_matrix rows) tys_tail)

(* ---- アルゴリズム I: 抜けているケースを1つ構成する ---- *)

let roots_of rows ty =
  List.sort_uniq compare (List.concat_map (fun r -> match r with h :: _ -> Option.to_list (ctor_of h ty) | [] -> []) rows)

let rec missing rows tys =
  match tys with
  | [] -> if rows = [] then Some [] else None
  | ty :: tys_tail -> (
      let ty = repr ty in
      let roots = roots_of rows ty in
      let sig_ = complete_sig ty in
      let is_complete =
        (* Some [] = 構成子ゼロ(Never)。節が無くても網羅(§7.5) *)
        match sig_ with
        | Some [] -> true
        | Some s -> roots <> [] && List.for_all (fun c -> List.mem c roots) s
        | None -> false
      in
      if is_complete then
        List.find_map
          (fun c ->
            match missing (specialize c ty rows) (sub_types c ty @ tys_tail) with
            | Some w -> Some (rebuild c w)
            | None -> None)
          (Option.get sig_)
      else
        match missing (default_matrix rows) tys_tail with
        | None -> None
        | Some w ->
            let head =
              match sig_ with
              | Some s -> (
                  match List.find_opt (fun c -> not (List.mem c roots)) s with
                  | Some c -> List.hd (rebuild c (List.init (arity c) (fun _ -> IWild)))
                  | None -> IWild)
              | None -> (
                  (* 整数は反例を構成する *)
                  let used = List.filter_map (function CLit (LNum n) -> Some n | _ -> None) roots in
                  if used <> [] then
                    let rec fresh i = if List.mem (string_of_int i) used then fresh (i + 1) else string_of_int i in
                    ILit (LNum (fresh 0))
                  else IWild)
            in
            Some (head :: w))

(* ---- アルゴリズム U: ベクトル q が useful か(冗長節の検出)---- *)

let rec useful rows q tys =
  match tys with
  | [] -> rows = []
  | ty :: tys_tail -> (
      let ty = repr ty in
      match ctor_of (List.hd q) ty with
      | Some c ->
          let q2 = match specialize c ty [ q ] with [ q2 ] -> q2 | _ -> bug "useful: specialize q" in
          useful (specialize c ty rows) q2 (sub_types c ty @ tys_tail)
      | None ->
          let roots = roots_of rows ty in
          let sig_ = complete_sig ty in
          let is_complete =
            match sig_ with
            | Some [] -> true
            | Some s -> roots <> [] && List.for_all (fun c -> List.mem c roots) s
            | None -> false
          in
          if is_complete then
            List.exists
              (fun c ->
                useful (specialize c ty rows) (List.init (arity c) (fun _ -> IWild) @ List.tl q) (sub_types c ty @ tys_tail))
              (Option.get sig_)
          else useful (default_matrix rows) (List.tl q) tys_tail)

(* ---- 表示 ---- *)

let show_lit = function LBool b -> string_of_bool b | LText s -> "\"" ^ String.escaped s ^ "\"" | LNum n -> n

let rec show_ipat = function
  | IWild -> "_"
  | ILit l -> show_lit l
  | IVariant (l, IRecord ([], true)) -> "#" ^ name_of l
  | IVariant (l, sub) -> "#" ^ name_of l ^ "(" ^ show_ipat sub ^ ")"
  | ICtor (_, c, []) -> name_of c
  | ICtor (_, c, subs) -> name_of c ^ "(" ^ String.concat ", " (List.map show_ipat subs) ^ ")"
  | IRecord ([], true) -> "()"
  | IRecord (fs, closed) ->
      if closed && fs <> [] && List.for_all (fun (l, _) -> l = l_item) fs then
        "(" ^ String.concat ", " (List.map (fun (_, p) -> show_ipat p) fs) ^ ")"
      else "{" ^ String.concat ", " (List.map (fun (l, p) -> name_of l ^ " = " ^ show_ipat p) fs) ^ "}"

(* ---- 検査キュー(§7.2)---- *)

type entry = { qe_rows : (T.pat * bool (* ガードつき *)) list; qe_ty : ty }

let pending : entry list ref = ref []

let queue rows ty = pending := !pending @ [ { qe_rows = rows; qe_ty = ty } ]

let check_entry { qe_rows; qe_ty } =
  let out = ref [] in
  let all = List.map (fun (p, guarded) -> ([ convert p ], guarded)) qe_rows in
  let unguarded = List.filter_map (fun (r, g) -> if g then None else Some r) all in
  let tys = [ qe_ty ] in
  close_variant_rows unguarded tys;
  (* ガード付き節は「必ずマッチ」と数えない(sample.kel:247-249)ので網羅性から除外 *)
  (match missing unguarded tys with
  | Some w -> out := !out @ [ "match が非網羅的です。例えば " ^ String.concat ", " (List.map show_ipat w) ^ " が漏れています" ]
  | None -> ());
  (* 到達不能: 先行するガード無し節だけを被覆として数える *)
  List.iteri
    (fun i (row, _) ->
      let prior = List.filteri (fun j _ -> j < i) all in
      let prior_unguarded = List.filter_map (fun (r, g) -> if g then None else Some r) prior in
      if not (useful prior_unguarded row tys) then out := !out @ [ Printf.sprintf "第 %d 節は到達不能です(冗長)" (i + 1) ])
    all;
  !out

let drain () =
  let entries = !pending in
  pending := [];
  List.concat_map check_entry entries

let reset () = pending := []
