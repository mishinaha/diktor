(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * 型のプリティプリンタ(計画 §7.7。MiniLang:491-590 を Keleut 表層構文に寄せた)。
 * - 複数の型を同じ命名で出す show_all
 * - Generic は A,B,...、値制限で残った弱変数は _A、Rigid は ς1、行は R1
 * - 制約前置 [A: Add + Mul](予約述語 Integral/Fractional は表示から除外)
 * - タプル再糖衣化: 全フィールドが _item の閉じた行は (A, B) に戻す(§14 TODO の義務)
 * - エフェクト省略: 空行・裸の行変数は @ を出さない
 *)
open Aux
open Syntax
open Type

let show_all ts =
  let names : (oid, string) Hashtbl.t = Hashtbl.create 16 in
  let constrained : (string * cls) list ref = ref [] in
  let star_pool = "ABCDE" in
  let arrow_pool = "FGH" in
  let star_count = ref 0 in
  let arrow_count = ref 0 in
  let row_count = ref 0 in
  let rigid_count = ref 0 in
  let pick pool i =
    String.make 1 pool.[i mod String.length pool] ^ if i >= String.length pool then string_of_int (i / String.length pool) else ""
  in
  let record_cs name cs =
    let cs = List.filter (fun c -> not (Unify.is_predicate c)) cs in
    if cs <> [] && not (List.mem_assoc name !constrained) then constrained := !constrained @ [ (name, cs) ];
    name
  in
  let name_of_var i ~generic =
    let n =
      match Hashtbl.find_opt names i.vid with
      | Some n -> n
      | None ->
          let base =
            match kind_repr i.vkind with
            | KRow ->
                incr row_count;
                "R" ^ string_of_int !row_count
            | KArrow _ ->
                let n = !arrow_count in
                incr arrow_count;
                pick arrow_pool n
            | _ ->
                let n = !star_count in
                incr star_count;
                pick star_pool n
          in
          let base = if generic then base else "_" ^ base in
          Hashtbl.add names i.vid base;
          base
    in
    record_cs n i.vcls
  in
  let rigid_name i =
    let n =
      match Hashtbl.find_opt names i.vid with
      | Some n -> n
      | None ->
          incr rigid_count;
          let n = "ς" ^ string_of_int !rigid_count in
          Hashtbl.add names i.vid n;
          n
    in
    record_cs n i.vcls
  in
  let is_tuple_row fields tail =
    (match repr tail with TRowEmpty -> true | _ -> false) && List.for_all (fun (l, _) -> l = l_item) fields
  in
  let rec go t =
    match repr t with
    | TVar v -> (
        match !v with
        | Unbound i -> name_of_var i ~generic:false
        | Generic i -> name_of_var i ~generic:true
        | Rigid i -> rigid_name i
        | Link t -> go t)
    | TCon (n, []) -> name_of n
    | TCon (n, args) -> name_of n ^ "[" ^ String.concat ", " (List.map go args) ^ "]"
    | TApp _ as t ->
        let h, args = app_spine t in
        go h ^ "[" ^ String.concat ", " (List.map go args) ^ "]"
    | TArrow (p, r, e) ->
        (* ^ の右辺が先に評価されると命名順が逆になるので let で順序を固定する *)
        let ps = go_args p in
        let rs = go r in
        let es = eff_suffix e in
        ps ^ " => " ^ rs ^ es
    | TRecord row -> (
        let fields, tail = row_fields row in
        if is_tuple_row fields tail && fields <> [] then
          "(" ^ String.concat ", " (List.map (fun (_, t) -> go t) fields) ^ if List.length fields = 1 then ",)" else ")"
        else
          match (fields, repr tail) with
          | [], TRowEmpty -> "{}"
          | [], tail -> "{extends " ^ go tail ^ "}"
          | fields, TRowEmpty -> "{" ^ String.concat ", " (List.map field fields) ^ "}"
          | fields, tail -> "{" ^ String.concat ", " (List.map field fields) ^ " extends " ^ go tail ^ "}")
    | TVariant row -> (
        let fields, tail = row_fields row in
        let case (l, t) = if is_unit t then "#" ^ name_of l else "#" ^ name_of l ^ "(" ^ go t ^ ")" in
        let parts = List.map case fields in
        let parts = match repr tail with TRowEmpty -> parts | tail -> parts @ [ go tail ] in
        match parts with [] -> "#|" (* 空ヴァリアント(Never 相当) *) | _ -> String.concat " | " parts)
    | TRowEmpty -> "{}"
    | TRowExtend _ as row -> eff_row row (* 裸の行はエフェクト行の書式で *)
  and field (l, t) = name_of l ^ ": " ^ go t
  and is_unit t = match repr t with TRecord r -> ( match repr r with TRowEmpty -> true | _ -> false) | _ -> false
  and go_args p =
    (* TArrow の引数は閉じた _item 行(D5)。開いていても壊れずに出す *)
    match repr p with
    | TRecord row ->
        let fields, tail = row_fields row in
        if is_tuple_row fields tail then "(" ^ String.concat ", " (List.map (fun (_, t) -> go t) fields) ^ ")"
        else go (TRecord row)
    | t -> go t
  and eff_row row =
    let fields, tail = row_fields row in
    let label (l, t) = if is_unit t then name_of l else name_of l ^ "[" ^ go t ^ "]" in
    let parts = List.map label fields in
    let ext = match repr tail with TRowEmpty -> "" | tail -> (if parts = [] then "extends " else " extends ") ^ go tail in
    "{" ^ String.concat ", " parts ^ ext ^ "}"
  and eff_suffix e =
    (* 空行・裸の行変数は省略(§7.7) *)
    match repr e with
    | TRowEmpty -> ""
    | TVar _ -> ""
    | row -> " @ " ^ eff_row row
  in
  let strs = List.map go ts in
  let ctx =
    match !constrained with
    | [] -> ""
    | cs ->
        "["
        ^ String.concat ", "
            (List.map (fun (n, cls) -> n ^ ": " ^ String.concat " + " (List.sort compare (List.map name_of cls))) cs)
        ^ "] "
  in
  (strs, ctx)

let show t =
  let strs, ctx = show_all [ t ] in
  ctx ^ List.hd strs

let show2 a b =
  let strs, _ = show_all [ a; b ] in
  match strs with [ x; y ] -> x ^ " と " ^ y | _ -> bug "show2"

let () =
  Unify.show_ref := show;
  Unify.show2_ref := show2
