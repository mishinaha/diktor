(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * 脱糖後 AST の S 式ダンパ(--dump-ast、計画 §8.7)。手書きで ppx を入れない。
 *)
open Syntax
open Tree.Tree

type sexp = A of string | L of sexp list

let rec pp fmt = function
  | A s -> Format.pp_print_string fmt s
  | L xs ->
      Format.fprintf fmt "@[<hov 1>(";
      List.iteri
        (fun i x ->
          if i > 0 then Format.fprintf fmt "@ ";
          pp fmt x)
        xs;
      Format.fprintf fmt ")@]"

let show_bin_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Eq -> "=="
  | Ne -> "!="
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | And -> "&&"
  | Or -> "||"

let quoted s = "\"" ^ String.escaped s ^ "\""

let sexp_of_tparam { tp_name; tp_arity; tp_classes } =
  let name = if tp_arity = 0 then A tp_name else L [ A tp_name; A (Printf.sprintf "arity=%d" tp_arity) ] in
  match tp_classes with
  | [] -> name
  | cs -> L (A ":" :: name :: List.map (fun c -> A (show_long_id c)) cs)

let rec sexp_of_ty (_, t) =
  match t with
  | EIdent li -> A (show_long_id li)
  | EApply (f, args) -> L (A "tapp" :: sexp_of_ty f :: List.map sexp_of_ty args)
  | EArrow (params, ret, eff) ->
      let base = [ A "=>"; L (List.map sexp_of_ty params); sexp_of_ty ret ] in
      L (match eff with None -> base | Some e -> base @ [ A "@"; sexp_of_ty e ])
  | EBraceRow (elems, ext) ->
      let elem = function
        | BField (l, t) -> L [ A (l ^ ":"); sexp_of_ty t ]
        | BLabel (li, []) -> A (show_long_id li)
        | BLabel (li, args) -> L (A (show_long_id li) :: List.map sexp_of_ty args)
      in
      let base = A "row" :: List.map elem elems in
      L (match ext with None -> base | Some t -> base @ [ A "extends"; sexp_of_ty t ])
  | EVariantCase (s, None) -> A ("#" ^ s)
  | EVariantCase (s, Some t) -> L [ A ("#" ^ s); sexp_of_ty t ]
  | EUnion ts -> L (A "union" :: List.map sexp_of_ty ts)
  | EHole -> A "_"

let rec sexp_of_pat (_, p) =
  match p with
  | PWildcard -> A "_"
  | PVar x -> A x
  | PBool b -> A (string_of_bool b)
  | PNumber n -> A (Lexer.show_number n)
  | PText s -> A (quoted s)
  | PRecord (fields, rest) ->
      let f (l, p) = L [ A (l ^ "="); sexp_of_pat p ] in
      let base = A "precord" :: List.map f fields in
      L (match rest with None -> base | Some r -> base @ [ A "..."; sexp_of_pat r ])
  | PCtor (li, args) -> L (A "pctor" :: A (show_long_id li) :: List.map sexp_of_ctor_arg_pat args)
  | PVariant (s, p) -> L [ A ("#" ^ s); sexp_of_pat p ]
  | PAnnot (p, t) -> L [ A "pannot"; sexp_of_pat p; sexp_of_ty t ]

and sexp_of_ctor_arg_pat { cap_label; cap_pat } =
  match cap_label with None -> sexp_of_pat cap_pat | Some l -> L [ A (l ^ "="); sexp_of_pat cap_pat ]

let rec sexp_of_exp (_, e) =
  match e with
  | Bool b -> A (string_of_bool b)
  | Number n -> A (Lexer.show_number n)
  | Text s -> A (quoted s)
  | Ident li -> A (show_long_id li)
  | Hole -> A "???"
  | Apply (f, a) -> L [ A "apply"; sexp_of_exp f; sexp_of_exp a ]
  | Construct (li, args) -> L (A "construct" :: A (show_long_id li) :: List.map sexp_of_ctor_arg args)
  | Variant (s, e) -> L [ A ("#" ^ s); sexp_of_exp e ]
  | BinOp (l, op, r) -> L [ A (show_bin_op op); sexp_of_exp l; sexp_of_exp r ]
  | Not e -> L [ A "!"; sexp_of_exp e ]
  | Lambda { l_params; l_body } -> L [ A "fn"; L (List.map sexp_of_pat l_params); sexp_of_exp l_body ]
  | Let (b, e) -> L [ A "let"; sexp_of_binding b; sexp_of_exp e ]
  | LetRec (bs, e) -> L [ A "letrec"; L (List.map sexp_of_binding bs); sexp_of_exp e ]
  | Seq es -> L (A "seq" :: List.map sexp_of_exp es)
  | Match (e, cs) -> L (A "match" :: sexp_of_exp e :: List.map sexp_of_clause cs)
  | RecordEmpty -> A "{}"
  | RecordExtend (rest, l, v) -> L [ A "extend"; A l; sexp_of_exp v; sexp_of_exp rest ]
  | RecordUpdate (r, l, v) -> L [ A "update"; A l; sexp_of_exp v; sexp_of_exp r ]
  | RecordRestriction (r, l) -> L [ A "restrict"; A l; sexp_of_exp r ]
  | RecordSelection (r, l) -> L [ A "select"; A l; sexp_of_exp r ]
  | Perform (li, args) -> L [ A "perform"; A (show_long_id li); sexp_of_exp args ]
  | Handle (e, cs) -> L (A "handle" :: sexp_of_exp e :: List.map sexp_of_clause cs)
  | Resume None -> L [ A "resume" ]
  | Resume (Some e) -> L [ A "resume"; sexp_of_exp e ]
  | Run (h, e) -> L [ A "run"; A h; sexp_of_exp e ]

and sexp_of_ctor_arg { ca_label; ca_exp } =
  match ca_label with None -> sexp_of_exp ca_exp | Some l -> L [ A (l ^ "="); sexp_of_exp ca_exp ]

and sexp_of_clause (_, { cl_pat; cl_guard; cl_body }) =
  let base = [ A "case"; sexp_of_pat cl_pat ] in
  let base = match cl_guard with None -> base | Some g -> base @ [ A "if"; sexp_of_exp g ] in
  L (base @ [ A "=>"; sexp_of_exp cl_body ])

and sexp_of_binding (_, b) =
  let tag = if b.lb_pub then "binding-pub" else "binding" in
  let base = [ A tag; sexp_of_pat b.lb_name ] in
  let base = match b.lb_tparams with [] -> base | ts -> base @ [ L (A "tparams" :: List.map sexp_of_tparam ts) ] in
  let base =
    match b.lb_params with None -> base | Some ps -> base @ [ L (A "params" :: List.map sexp_of_pat ps) ]
  in
  let base = match b.lb_ret with None -> base | Some t -> base @ [ A ":"; sexp_of_ty t ] in
  let base = match b.lb_eff with None -> base | Some t -> base @ [ A "@"; sexp_of_ty t ] in
  L (base @ [ A "="; sexp_of_exp b.lb_body ])

let sexp_of_ctor_decl { cd_name; cd_fields } =
  let f { fd_label; fd_ty } =
    match fd_label with None -> sexp_of_ty fd_ty | Some l -> L [ A (l ^ ":"); sexp_of_ty fd_ty ]
  in
  L (A cd_name :: List.map f cd_fields)

let rec sexp_of_decl (_, d) =
  match d with
  | DType t ->
      let base = [ A (if t.ta_pub then "type-pub" else "type"); A t.ta_name ] in
      let base = match t.ta_params with [] -> base | ps -> base @ [ L (List.map sexp_of_tparam ps) ] in
      let base = match t.ta_kind with None -> base | Some k -> base @ [ A (": " ^ k) ] in
      L (base @ [ A "="; sexp_of_ty t.ta_body ])
  | DNewtype n ->
      let base = [ A (if n.nt_pub then "newtype-pub" else "newtype"); A n.nt_name ] in
      let base = match n.nt_params with [] -> base | ps -> base @ [ L (List.map sexp_of_tparam ps) ] in
      let rhs = match n.nt_rhs with NtHole -> [ A "???" ] | NtCtors cs -> List.map sexp_of_ctor_decl cs in
      L (base @ rhs)
  | DEffect e ->
      let base = [ A (if e.ef_pub then "effect-pub" else "effect"); A e.ef_name ] in
      let base = match e.ef_params with [] -> base | ps -> base @ [ L (List.map sexp_of_tparam ps) ] in
      L (base @ List.map (fun (op, t) -> L [ A (op ^ ":"); sexp_of_ty t ]) e.ef_ops)
  | DClass c ->
      let base = [ A (if c.cls_pub then "class-pub" else "class"); A c.cls_name ] in
      let base = base @ [ L (List.map sexp_of_tparam c.cls_params) ] in
      let vals =
        List.map
          (fun v ->
            let vb = [ A "val"; A v.cv_name ] in
            let vb = match v.cv_tparams with [] -> vb | ts -> vb @ [ L (List.map sexp_of_tparam ts) ] in
            L (vb @ [ A ":"; sexp_of_ty v.cv_ty ]))
          c.cls_vals
      in
      let derives = List.map (fun d -> L [ A "derive"; A d ]) c.cls_derives in
      L (base @ vals @ derives)
  | DInstance i ->
      L
        (A "instance" :: A i.ins_class
        :: L (List.map sexp_of_ty i.ins_args)
        :: List.map sexp_of_decl i.ins_body)
  | DLet b -> L [ A "dlet"; sexp_of_binding b ]
  | DLetRec bs -> L (A "dletrec" :: List.map sexp_of_binding bs)
  | DModule (pub, name, ds) ->
      L (A (if pub then "module-pub" else "module") :: A name :: List.map sexp_of_decl ds)
  | DExtern e ->
      let base = [ A (if e.ex_pub then "extern-pub" else "extern"); A (quoted e.ex_abi); A e.ex_name ] in
      let base = match e.ex_tparams with [] -> base | ts -> base @ [ L (A "tparams" :: List.map sexp_of_tparam ts) ] in
      let base = base @ [ L (A "params" :: List.map sexp_of_pat e.ex_params) ] in
      let base = match e.ex_ret with None -> base | Some t -> base @ [ A ":"; sexp_of_ty t ] in
      let base = match e.ex_eff with None -> base | Some t -> base @ [ A "@"; sexp_of_ty t ] in
      L base
  | DExp e -> L [ A "exp"; sexp_of_exp e ]

let dump_decls out decls =
  let fmt = Format.formatter_of_out_channel out in
  List.iter (fun d -> Format.fprintf fmt "%a@." pp (sexp_of_decl d)) decls;
  Format.pp_print_flush fmt ()
