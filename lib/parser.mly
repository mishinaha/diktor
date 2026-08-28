(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * Keleut 文法(計画 §6)。骨格は spike の kel.mly(--strict で conflict 0、
 * sample.kel 全文パース済み)。設計判断は spike の [FIX-n] コメントと計画 §6 を参照。
 * 旧 Orphos 文法は git 履歴 f0cafd4 にある。
 *)
%parameter <Data : Syntax.Data>
%{
(* Workaround ocaml/dune#2450 *)
module Diktor = struct end

open Syntax
open Syntax.Make(Data)

let mk (sp, ep) x = (Data.allocate { Location.start = sp; Location.finish = ep }, x)

let is_upper s = s <> "" && s.[0] >= 'A' && s.[0] <= 'Z'

(* t._N の N(10進の桁列)か? *)
let is_index_label s =
  String.length s >= 2 && s.[0] = '_'
  && (let ok = ref true in
      String.iteri (fun i c -> if i > 0 && not (c >= '0' && c <= '9') then ok := false) s;
      !ok)

(* postfix_exp DOT id の意味アクション(§6.1)。
   先頭の連続する大文字成分 + 直後の1成分をパスに畳み、残りをレコード選択にする *)
let dot_select sloc e id =
  match e with
  | (_, Ident (LongId comps)) when List.for_all is_upper comps ->
      mk sloc (Ident (LongId (comps @ [ id ])))
  | _ ->
      if is_upper id then raise (Syntax_error ("レコードのラベルに大文字識別子は使えません: " ^ id))
      else if is_index_label id then
        (* t._N = (t \ _item)^N ._item(§6.4) *)
        let n = int_of_string (String.sub id 1 (String.length id - 1)) in
        let rec strip e n = if n = 0 then e else strip (mk sloc (RecordRestriction (e, "_item"))) (n - 1) in
        mk sloc (RecordSelection (strip e n, "_item"))
      else mk sloc (RecordSelection (e, id))

(* 引数リスト → _item レコード(D5)。ラベル付き引数は l = e でラベル指定 *)
let record_of_args sloc args =
  let rec row = function
    | [] -> mk sloc RecordEmpty
    | (label, v) :: tl ->
        let l = match label with Some l -> l | None -> "_item" in
        mk sloc (RecordExtend (row tl, l, v))
  in
  row args

let tuple_exp sloc exps = record_of_args sloc (List.map (fun e -> (None, e)) exps)

(* #Foo の引数 → ペイロード(§6.4: 1引数はそのもの、他はタプル) *)
let variant_payload sloc = function
  | [ (None, e) ] -> e
  | args ->
      if List.exists (fun (l, _) -> l <> None) args then
        raise (Syntax_error "#Foo(...) にラベル付き引数は使えません")
      else tuple_exp sloc (List.map snd args)

(* 呼び出しの意味アクション(§6.1)。パスの最後の成分が大文字なら Construct、
   小文字なら Apply。#Foo は Variant に畳む(spike [FIX-3]) *)
let call sloc callee args =
  match callee with
  | (_, Variant (s, (_, RecordEmpty))) -> mk sloc (Variant (s, variant_payload sloc args))
  | (_, Ident (LongId comps)) when is_upper (List.nth comps (List.length comps - 1)) ->
      mk sloc (Construct (LongId comps, List.map (fun (l, e) -> { ca_label = l; ca_exp = e }) args))
  | _ -> mk sloc (Apply (callee, record_of_args sloc args))

(* ブロック: items(decl 列)を Let / LetRec / Seq の式形へ(§4.2) *)
let rec block_of_items sloc items =
  match items with
  | [] -> mk sloc RecordEmpty
  | [ (_, DExp e) ] -> e
  | (_, DExp e) :: rest -> (
      match block_of_items sloc rest with
      | (_, Seq es) as r -> (fst r, Seq (e :: es))
      | r -> (fst e, Seq [ e; r ]))
  | (d, DLet b) :: rest -> (d, Let (b, block_of_items sloc rest))
  | (d, DLetRec bs) :: rest -> (d, LetRec (bs, block_of_items sloc rest))
  | _ :: _ -> raise (Syntax_error "この宣言はブロック内では使えません(let / let rec / 式のみ)")

(* with x = f(a) の脱糖(§6.4)。引数行の最内 RecordEmpty に継続を差し込む。
   pat が _ なら0引数、それ以外なら1引数の継続 *)
let with_splice sloc pat call k_body =
  let k_params = match snd pat with PWildcard -> [] | _ -> [ pat ] in
  let k = mk sloc (Lambda { l_params = k_params; l_body = k_body }) in
  match call with
  | (d, Apply (f, args)) ->
      let rec splice (ad, a) =
        match a with
        | RecordEmpty -> (ad, RecordExtend (mk sloc RecordEmpty, "_item", k))
        | RecordExtend (rest, l, v) -> (ad, RecordExtend (splice rest, l, v))
        | _ -> raise (Syntax_error "with: 呼び出しの引数形が不正です")
      in
      (d, Apply (f, splice args))
  | _ -> raise (Syntax_error "with の右辺は関数呼び出しでなければなりません")

let pat_tuple sloc pats rest_opt =
  (* rest_opt: None = 閉じた行(arity 検査)、Some p = 尾部束縛 *)
  mk sloc (PRecord (List.map (fun p -> ("_item", p)) pats, rest_opt))

let variant_pat_payload sloc = function
  | [ { cap_label = None; cap_pat = p } ] -> p
  | args ->
      if List.exists (fun a -> a.cap_label <> None) args then
        raise (Syntax_error "#Foo(...) パターンにラベル付き引数は使えません")
      else pat_tuple sloc (List.map (fun a -> a.cap_pat) args) None

let tuple_ty sloc tys = mk sloc (EBraceRow (List.map (fun t -> BField ("_item", t)) tys, None))

let variant_ty_payload sloc = function [ t ] -> t | ts -> tuple_ty sloc ts

(* 宣言への pub の適用 *)
let set_pub = function
  | DType t -> DType { t with ta_pub = true }
  | DNewtype n -> DNewtype { n with nt_pub = true }
  | DEffect e -> DEffect { e with ef_pub = true }
  | DClass c -> DClass { c with cls_pub = true }
  | DLet (d, b) -> DLet (d, { b with lb_pub = true })
  | DLetRec bs -> DLetRec (List.map (fun (d, b) -> (d, { b with lb_pub = true })) bs)
  | DModule (_, n, ds) -> DModule (true, n, ds)
  | DExtern e -> DExtern { e with ex_pub = true }
  | DInstance _ -> raise (Syntax_error "type instance に pub は付けられません")
  | DExp _ -> raise (Syntax_error "式文に pub は付けられません")

(* newtype の右辺(受理形を decl_body の意味アクションで解釈する) *)
type nt_rhs_raw = RhsNone | RhsShort of field_decl list | RhsCtors of ctor_decl list | RhsHole
%}

(* 維持(44個) *)
%token AND AT ASTERISK BIG_AMPERSAND BIG_EQ BIG_VERTICAL CASE COLON COMMA DOT
%token EFFECT EOF EQ EQ_GREATER EXCLAMATION EXCLAMATION_EQ FN GREATER HANDLE
%token HYPHEN IF LBRACKET LESS LET LOWLINE LPAREN MATCH MODULE NL PLUS RBRACKET
%token REC RPAREN SEMI SOLIDUS TYPE VAL VERTICAL WITH
%token <bool> BOOL
%token <string> LOWER_IDENTIFIER UPPER_IDENTIFIER TEXT
%token <Syntax.number> NUMBER

(* 新設(20個) *)
%token LBRACE_BLOCK LBRACE_RECORD LBRACE_TYPE RBRACE
%token BACKSLASH DOTDOTDOT LESS_EQ GREATER_EQ HOLE
%token CLASS INSTANCE DERIVE EXTENDS EXTERN NEWTYPE PERFORM PUB RESUME RUN
%token <string> HASH_IDENT

%start <Syntax.Make(Data).decl list> program

%%

%inline semi: NL { () } | SEMI { () }

%inline lbrace:
  | LBRACE_BLOCK  { () }
  | LBRACE_RECORD { () }
  | LBRACE_TYPE   { () }

lower_id: LOWER_IDENTIFIER { $1 }
upper_id: UPPER_IDENTIFIER { $1 }

(* 型・パターン位置の long_id。式位置では使わない(spike [FIX-1]) *)
upper_path:
  | upper_id                { [ $1 ] }
  | upper_path DOT upper_id { $1 @ [ $3 ] }
long_id:
  | lower_id                { LongId [ $1 ] }
  | upper_path              { LongId $1 }
  | upper_path DOT lower_id { LongId ($1 @ [ $3 ]) }

(* ------------------------------------------------------------------ *)
(* プログラム / 宣言                                                    *)
(* ------------------------------------------------------------------ *)

program: items EOF { $1 }

items:
  |                            { [] }
  | semi items                 { $2 }
  | item                       { [ $1 ] }
  | item semi items            { $1 :: $3 }
  | WITH pat EQ exp            { [ mk $sloc (DExp (with_splice $sloc $2 $4 (mk $sloc RecordEmpty))) ] }
  | WITH pat EQ exp semi items { [ mk $sloc (DExp (with_splice $sloc $2 $4 (block_of_items $sloc $6))) ] }

item: decl { $1 } | exp { mk $sloc (DExp $1) }

decl: PUB decl_body { mk $sloc (set_pub $2) } | decl_body { mk $sloc $1 }

decl_body:
  | LET binding                                        { DLet $2 }
  (* spike [FIX-6]: ASI が AND の前の NL を落とすので semi は挟まない *)
  | LET REC binding and_bindings                       { DLetRec ($3 :: $4) }
  | TYPE upper_id typarams_opt kind_annot_opt EQ ty
      { DType { ta_pub = false; ta_name = $2; ta_params = $3; ta_kind = $4; ta_body = $6 } }
  | TYPE CLASS upper_id typarams class_body
      { let vals, derives = $5 in
        DClass { cls_pub = false; cls_name = $3; cls_params = $4; cls_vals = vals; cls_derives = derives } }
  | TYPE INSTANCE upper_id LBRACKET ty_args RBRACKET instance_body
      { DInstance { ins_class = $3; ins_args = $5; ins_body = $7 } }
  | NEWTYPE upper_id typarams_opt newtype_rhs
      { let rhs =
          match $4 with
          | RhsNone -> NtCtors []
          | RhsHole -> NtHole
          | RhsCtors cs -> NtCtors cs
          (* newtype UserId(Int32) = newtype UserId = UserId(Int32) の略記(§6.4) *)
          | RhsShort fields -> NtCtors [ { cd_name = $2; cd_fields = fields } ]
        in
        DNewtype { nt_pub = false; nt_name = $2; nt_params = $3; nt_rhs = rhs } }
  | EFFECT upper_id typarams_opt EQ eff_decl_body
      { DEffect { ef_pub = false; ef_name = $2; ef_params = $3; ef_ops = $5 } }
  | MODULE upper_id module_body                        { DModule (false, $2, $3) }
  | EXTERN TEXT LET extern_sig
      { let name, tparams, params, (ret, eff) = $4 in
        DExtern { ex_pub = false; ex_abi = $2; ex_name = name; ex_tparams = tparams; ex_params = params;
                  ex_ret = ret; ex_eff = eff } }

and_bindings:
  |                          { [] }
  | AND binding and_bindings { $2 :: $3 }

(* spike [FIX-5]: 関数形とパターン束縛形。パターン側は bind_pat に制限し、
   小文字頭の ctor パターン(case print(m) 用)を排除する *)
binding:
  | lower_id typarams_opt LPAREN params RPAREN sig_tail EQ exp
      { let ret, eff = $6 in
        mk $sloc { lb_pub = false; lb_name = mk $sloc (PVar $1); lb_tparams = $2; lb_params = Some $4;
                   lb_ret = ret; lb_eff = eff; lb_body = $8 } }
  | bind_pat annot_opt EQ exp
      { mk $sloc { lb_pub = false; lb_name = $1; lb_tparams = []; lb_params = None;
                   lb_ret = $2; lb_eff = None; lb_body = $4 } }

(* spike [FIX-9]: 返り値注釈と関数の eff 行 *)
sig_tail:
  |              { (None, None) }
  | AT eff       { (None, Some $2) }
  | COLON ty_ret { $2 }
ty_ret:
  | union_ty        { (Some $1, None) }
  | union_ty AT eff { (Some $1, Some $3) }
  | arrow_ty        { (Some $1, None) }

annot_opt: { None } | COLON ty { Some $2 }

extern_sig: lower_id typarams_opt LPAREN params RPAREN sig_tail { ($1, $2, $4, $6) }

module_body:   lbrace items RBRACE { $2 }
instance_body: lbrace items RBRACE { $2 }

class_body: lbrace class_items RBRACE { $2 }
class_items:
  |                             { ([], []) }
  | semi class_items            { $2 }
  | class_item                  { (match $1 with Either.Left v -> ([ v ], []) | Either.Right d -> ([], [ d ])) }
  | class_item semi class_items
      { let vals, derives = $3 in
        match $1 with Either.Left v -> (v :: vals, derives) | Either.Right d -> (vals, d :: derives) }
class_item:
  | VAL lower_id typarams_opt COLON ty { Either.Left { cv_name = $2; cv_tparams = $3; cv_ty = $5 } }
  | DERIVE lower_id                    { Either.Right $2 }

newtype_rhs:
  |                           { RhsNone }
  | LPAREN ctor_fields RPAREN { RhsShort $2 }
  | EQ ctors                  { RhsCtors $2 }
  | EQ HOLE                   { RhsHole }

ctors: ctor { [ $1 ] } | ctor VERTICAL ctors { $1 :: $3 }
ctor:
  | upper_id                           { { cd_name = $1; cd_fields = [] } }
  | upper_id LPAREN ctor_fields RPAREN { { cd_name = $1; cd_fields = $3 } }
ctor_fields: { [] } | ctor_field_list { $1 }
ctor_field_list:
  | ctor_field                       { [ $1 ] }
  | ctor_field COMMA                 { [ $1 ] }
  | ctor_field COMMA ctor_field_list { $1 :: $3 }
ctor_field: ty { { fd_label = None; fd_ty = $1 } } | lower_id COLON ty { { fd_label = Some $1; fd_ty = $3 } }

eff_decl_body: lbrace eff_ops RBRACE { $2 }
eff_ops: { [] } | eff_op_list { $1 }
eff_op_list:
  | eff_op                   { [ $1 ] }
  | eff_op COMMA             { [ $1 ] }
  | eff_op COMMA eff_op_list { $1 :: $3 }
eff_op: lower_id COLON ty { ($1, $3) }

typarams_opt: { [] } | typarams { $1 }
typarams: LBRACKET typaram_list RBRACKET { $2 }
typaram_list: typaram { [ $1 ] } | typaram COMMA typaram_list { $1 :: $3 }
typaram: ty_ident hkt_opt cls_opt { { tp_name = $1; tp_arity = $2; tp_classes = $3 } }
ty_ident: lower_id { $1 } | upper_id { $1 }
hkt_opt: { 0 } | LBRACKET lowline_list RBRACKET { $2 }
lowline_list: LOWLINE { 1 } | LOWLINE COMMA lowline_list { 1 + $3 }
cls_opt: { [] } | COLON cls_list { $2 }
cls_list: upper_id { [ LongId [ $1 ] ] } | upper_id PLUS cls_list { LongId [ $1 ] :: $3 }

kind_annot_opt: { None } | COLON upper_id { Some $2 }

params: { [] } | param_list { $1 }
param_list:
  | param                  { [ $1 ] }
  | param COMMA            { [ $1 ] }
  | param COMMA param_list { $1 :: $3 }
param: pat annot_opt { match $2 with None -> $1 | Some t -> mk $sloc (PAnnot ($1, t)) }

(* ------------------------------------------------------------------ *)
(* 式                                                                  *)
(* ------------------------------------------------------------------ *)

exp:
  | FN LPAREN params RPAREN EQ_GREATER exp { mk $sloc (Lambda { l_params = $3; l_body = $6 }) }
  | postfixed                              { $1 }

postfixed:
  | postfixed MATCH clause_body  { mk $sloc (Match ($1, $3)) }
  | postfixed HANDLE clause_body { mk $sloc (Handle ($1, $3)) }
  | or_exp                       { $1 }

or_exp:  or_exp BIG_VERTICAL and_exp   { mk $sloc (BinOp ($1, Or, $3)) } | and_exp { $1 }
and_exp: and_exp BIG_AMPERSAND cmp_exp { mk $sloc (BinOp ($1, And, $3)) } | cmp_exp { $1 }
cmp_exp: add_exp cmp_op add_exp        { mk $sloc (BinOp ($1, $2, $3)) } | add_exp { $1 }
%inline cmp_op:
  | BIG_EQ { Eq } | EXCLAMATION_EQ { Ne } | LESS { Lt } | LESS_EQ { Le }
  | GREATER { Gt } | GREATER_EQ { Ge }
add_exp: add_exp add_op mul_exp { mk $sloc (BinOp ($1, $2, $3)) } | mul_exp { $1 }
%inline add_op: PLUS { Add } | HYPHEN { Sub }
mul_exp: mul_exp mul_op prefix_exp { mk $sloc (BinOp ($1, $2, $3)) } | prefix_exp { $1 }
%inline mul_op: ASTERISK { Mul } | SOLIDUS { Div }
prefix_exp:
  | EXCLAMATION prefix_exp { mk $sloc (Not $2) }
  (* 符号は parser が畳む(§5.5)。AST に単項マイナス演算子は存在しない *)
  | HYPHEN NUMBER          { mk $sloc (Number { $2 with n_text = "-" ^ $2.n_text }) }
  | postfix_exp            { $1 }

postfix_exp:
  | postfix_exp DOT lower_id            { dot_select $sloc $1 $3 }
  | postfix_exp DOT upper_id            { dot_select $sloc $1 $3 }
  | postfix_exp BACKSLASH lower_id      { mk $sloc (RecordRestriction ($1, $3)) }
  | postfix_exp LPAREN call_args RPAREN { call $sloc $1 $3 }
  | atom                                { $1 }

atom:
  | NUMBER { mk $sloc (Number $1) }
  | TEXT   { mk $sloc (Text $1) }
  | BOOL   { mk $sloc (Bool $1) }
  | HOLE   { mk $sloc Hole }
  | lower_id                                   { mk $sloc (Ident (LongId [ $1 ])) }
  | upper_id                                   { mk $sloc (Ident (LongId [ $1 ])) }
  | HASH_IDENT                                 { mk $sloc (Variant ($1, mk $sloc RecordEmpty)) }
  | PERFORM perform_op LPAREN call_args RPAREN { mk $sloc (Perform ($2, record_of_args $sloc $4)) }
  | RESUME LPAREN call_args RPAREN
      { (* 引数を record_of_args に通さない(§6.2): ペイロードは操作の返り値そのもの *)
        match $3 with
        | [] -> mk $sloc (Resume None)
        | [ (None, e) ] -> mk $sloc (Resume (Some e))
        | _ -> raise (Syntax_error "resume の引数は高々1個です") }
  | RUN lower_id run_body                      { mk $sloc (Run ($2, $3)) }
  | block                                      { $1 }
  | record_exp                                 { $1 }
  | paren_exp                                  { $1 }

perform_op: long_id { $1 }

block: LBRACE_BLOCK items RBRACE { block_of_items $sloc $2 }
(* spike [FIX-7]: run h {} は LBRACE_RECORD になるので union で受ける *)
run_body: lbrace items RBRACE { block_of_items $sloc $2 }

call_args: { [] } | arg_list { $1 }
arg_list:
  | arg                { [ $1 ] }
  | arg COMMA          { [ $1 ] }
  | arg COMMA arg_list { $1 :: $3 }
arg: lower_id EQ exp { (Some $1, $3) } | exp { (None, $1) }

record_exp:
  | LBRACE_RECORD RBRACE                        { mk $sloc RecordEmpty }
  | LBRACE_RECORD EXTENDS exp RBRACE            { $3 }
  | LBRACE_RECORD field_list RBRACE             { record_of_args $sloc (List.map (fun (l, e) -> (Some l, e)) $2) }
  | LBRACE_RECORD field_list EXTENDS exp RBRACE
      { let rec row = function
          | [] -> $4
          | (l, v) :: tl -> mk $sloc (RecordExtend (row tl, l, v))
        in
        row $2 }
  | LBRACE_RECORD exp WITH field_list RBRACE
      { (* {base with l = e}: base は字句分類の帰結で実質 lower_id 1個(§5.3) *)
        List.fold_left (fun acc (l, v) -> mk $sloc (RecordUpdate (acc, l, v))) $2 $4 }
field_list:
  | field                  { [ $1 ] }
  | field COMMA            { [ $1 ] }
  | field COMMA field_list { $1 :: $3 }
field:
  | lower_id EQ exp { ($1, $3) }
  | lower_id        { ($1, mk $sloc (Ident (LongId [ $1 ]))) } (* パンニング {a, b} = {a = a, b = b} *)

paren_exp:
  | LPAREN RPAREN                    { mk $sloc RecordEmpty }
  | LPAREN exp RPAREN                { $2 } (* グループ化。タプルにしない(§6.4) *)
  | LPAREN exp COMMA RPAREN          { tuple_exp $sloc [ $2 ] }
  | LPAREN exp COMMA exp_list RPAREN { tuple_exp $sloc ($2 :: $4) }
exp_list:
  | exp                { [ $1 ] }
  | exp COMMA          { [ $1 ] }
  | exp COMMA exp_list { $1 :: $3 }

clause_body: lbrace clauses RBRACE { $2 }
(* spike [FIX-8]: 節間の NL は ASI が落とす(CASE は can_begin_statement に無い) *)
clauses: clause { [ $1 ] } | clause clauses { $1 :: $2 }
clause: CASE pat guard_opt EQ_GREATER exp { mk $sloc { cl_pat = $2; cl_guard = $3; cl_body = $5 } }
guard_opt: { None } | IF exp { Some $2 }

(* ------------------------------------------------------------------ *)
(* パターン                                                            *)
(* ------------------------------------------------------------------ *)

pat:
  | LOWLINE                           { mk $sloc PWildcard }
  | NUMBER                            { mk $sloc (PNumber $1) }
  | HYPHEN NUMBER                     { mk $sloc (PNumber { $2 with n_text = "-" ^ $2.n_text }) }
  | TEXT                              { mk $sloc (PText $1) }
  | BOOL                              { mk $sloc (PBool $1) }
  | long_id
      { match $1 with
        | LongId [ x ] when not (is_upper x) -> mk $sloc (PVar x)
        | li -> mk $sloc (PCtor (li, [])) }
  | long_id LPAREN pat_args RPAREN    { mk $sloc (PCtor ($1, $3)) }
  | HASH_IDENT                        { mk $sloc (PVariant ($1, mk $sloc (PRecord ([], None)))) }
  | HASH_IDENT LPAREN pat_args RPAREN { mk $sloc (PVariant ($1, variant_pat_payload $sloc $3)) }
  | record_pat                        { $1 }
  | paren_pat                         { $1 }

(* spike [FIX-5]: let 束縛のパターン: 小文字頭の呼び出し形を持たない *)
bind_pat:
  | LOWLINE                            { mk $sloc PWildcard }
  | lower_id                           { mk $sloc (PVar $1) }
  | upper_path                         { mk $sloc (PCtor (LongId $1, [])) }
  | upper_path LPAREN pat_args RPAREN  { mk $sloc (PCtor (LongId $1, $3)) }
  | record_pat                         { $1 }
  | paren_pat                          { $1 }

pat_args: { [] } | pat_arg_list { $1 }
pat_arg_list:
  | pat_arg                    { [ $1 ] }
  | pat_arg COMMA              { [ $1 ] }
  | pat_arg COMMA pat_arg_list { $1 :: $3 }
pat_arg: lower_id EQ pat { { cap_label = Some $1; cap_pat = $3 } } | pat { { cap_label = None; cap_pat = $1 } }

(* レコードパターンは開いた行が既定(§4.2)。`{x}` は BLOCK に分類されるので
   union lbrace で受ける(§5.3。spike からの計画反映) *)
record_pat: lbrace rp_items RBRACE
  { let fields, rest = $2 in
    mk $sloc (PRecord (fields, Some (match rest with Some r -> r | None -> mk $sloc PWildcard))) }
rp_items:
  |                            { ([], None) }
  | DOTDOTDOT lower_id         { ([], Some (mk $sloc (PVar $2))) }
  | pat_field                  { ([ $1 ], None) }
  | pat_field COMMA rp_items   { let fs, r = $3 in ($1 :: fs, r) }
pat_field:
  | lower_id EQ pat { ($1, $3) }
  | lower_id        { ($1, mk $sloc (PVar $1)) } (* パンニング *)

(* タプルパターンは閉じた行(arity 検査)。(p) はグループ化、(p,) が1-タプル *)
paren_pat: LPAREN pp_items RPAREN
  { match $2 with
    | [ p ], None, false -> p
    | pats, rest, _ -> pat_tuple $sloc pats rest }
pp_items:
  |                        { ([], None, true) }
  | DOTDOTDOT lower_id     { ([], Some (mk $sloc (PVar $2)), true) }
  | pat                    { ([ $1 ], None, false) }
  | pat COMMA pp_items     { let ps, r, _ = $3 in ($1 :: ps, r, true) }

(* ------------------------------------------------------------------ *)
(* 型                                                                  *)
(* ------------------------------------------------------------------ *)

(* spike [FIX-2]: arrow は atom_ty ではなく ty の直下に置く *)
ty: union_ty { $1 } | arrow_ty { $1 }

arrow_ty: LPAREN ty_list0 RPAREN EQ_GREATER arrow_ret
  { let ret, eff = $5 in
    mk $sloc (EArrow ($2, ret, eff)) }
arrow_ret:
  | union_ty eff_opt { ($1, $2) }
  | arrow_ty         { ($1, None) } (* 入れ子 arrow の外側には @ を書けない(要括弧、§6.3) *)
eff_opt: { None } | AT eff { Some $2 }

union_ty:
  | union_ty VERTICAL app_ty { match $1 with (_, EUnion ts) -> mk $sloc (EUnion (ts @ [ $3 ])) | t -> mk $sloc (EUnion [ t; $3 ]) }
  | app_ty                   { $1 }

app_ty:
  | atom_ty                           { $1 }
  | atom_ty LBRACKET ty_args RBRACKET { mk $sloc (EApply ($1, $3)) }

ty_args: ty_arg { [ $1 ] } | ty_arg COMMA ty_args { $1 :: $3 }
ty_arg: ty { $1 } | LOWLINE { mk $sloc EHole }

atom_ty:
  | long_id                           { mk $sloc (EIdent $1) }
  | HASH_IDENT                        { mk $sloc (EVariantCase ($1, None)) }
  | HASH_IDENT LPAREN ty_list0 RPAREN
      { match $3 with
        | [] -> mk $sloc (EVariantCase ($1, None))
        | ts -> mk $sloc (EVariantCase ($1, Some (variant_ty_payload $sloc ts))) }
  | brace_ty                          { $1 }
  | LPAREN ty_list0 RPAREN            { tuple_ty $sloc $2 } (* 型位置の (A) は常に 1-タプル(§12) *)

ty_list0: { [] } | ty_list { $1 }
ty_list:
  | ty               { [ $1 ] }
  | ty COMMA         { [ $1 ] }
  | ty COMMA ty_list { $1 :: $3 }

(* spike [FIX-2b][FIX-10]: レコード型とエフェクト行を1本の非終端に統合(§4.2 EBraceRow)。
   record か row かは elab が要素の形で判定する *)
brace_ty:
  | lbrace RBRACE                            { mk $sloc (EBraceRow ([], None)) }
  | lbrace EXTENDS ty RBRACE                 { mk $sloc (EBraceRow ([], Some $3)) }
  | lbrace brace_item_list RBRACE            { mk $sloc (EBraceRow ($2, None)) }
  | lbrace brace_item_list EXTENDS ty RBRACE { mk $sloc (EBraceRow ($2, Some $4)) }
brace_item_list:
  | brace_item                       { [ $1 ] }
  | brace_item COMMA                 { [ $1 ] }
  | brace_item COMMA brace_item_list { $1 :: $3 }
brace_item:
  | lower_id COLON ty { BField ($1, $3) }   (* レコード型のフィールド *)
  | eff_name          { let li, args = $1 in BLabel (li, args) }   (* エフェクト行の要素 *)

eff:
  | eff_name { let li, args = $1 in
               match args with [] -> mk $sloc (EIdent li) | _ -> mk $sloc (EApply (mk $sloc (EIdent li), args)) }
  | brace_ty { $1 }
eff_name:
  | long_id                           { ($1, []) }
  | long_id LBRACKET ty_args RBRACKET { ($1, $3) }
