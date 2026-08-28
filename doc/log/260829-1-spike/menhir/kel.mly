(* Keleut 骨格文法 spike -- VERSION C (conflict 0)
   A からの修正点を [FIX-n] で示す。 *)

%token AND AT ASTERISK BIG_AMPERSAND BIG_EQ BIG_VERTICAL CASE COLON COMMA DOT
%token EFFECT EOF EQ EQ_GREATER EXCLAMATION EXCLAMATION_EQ FN GREATER HANDLE
%token HYPHEN IF LBRACKET LESS LET LOWLINE LPAREN MATCH MODULE NL PLUS RBRACKET
%token REC RPAREN SEMI SOLIDUS TYPE VAL VERTICAL WITH
%token LBRACE_BLOCK LBRACE_RECORD LBRACE_TYPE RBRACE
%token BACKSLASH DOTDOTDOT LESS_EQ GREATER_EQ HOLE
%token CLASS INSTANCE DERIVE EXTENDS EXTERN NEWTYPE PERFORM PUB RESUME RUN
%token <bool> BOOL
%token <string> LOWER_IDENTIFIER UPPER_IDENTIFIER TEXT HASH_IDENT NUMBER

%start <unit> program

%%

%inline semi: NL { () } | SEMI { () }

%inline lbrace:
  | LBRACE_BLOCK  { () }
  | LBRACE_RECORD { () }
  | LBRACE_TYPE   { () }

lower_id: LOWER_IDENTIFIER { () }
upper_id: UPPER_IDENTIFIER { () }

(* 型・パターン位置の long_id。式位置では使わない ([FIX-1]) *)
upper_path:
  | upper_id                { () }
  | upper_path DOT upper_id { () }
long_id:
  | lower_id                { () }
  | upper_path              { () }
  | upper_path DOT lower_id { () }

(* ------------------------------------------------------------------ *)
(* プログラム / 宣言                                                    *)
(* ------------------------------------------------------------------ *)

program: items EOF { () }

items:
  |                            { () }
  | semi items                 { () }
  | item                       { () }
  | item semi items            { () }
  | WITH pat EQ exp            { () }
  | WITH pat EQ exp semi items { () }

item: decl { () } | exp { () }

decl: PUB decl_body { () } | decl_body { () }

decl_body:
  | LET binding                                        { () }
  (* [FIX-6] ASI が AND の前の NL を落とすので semi は挟まない *)
  | LET REC binding and_bindings                       { () }
  | TYPE upper_id typarams_opt kind_annot_opt EQ ty    { () }
  | TYPE CLASS upper_id typarams class_body            { () }
  | TYPE INSTANCE upper_id LBRACKET ty_args RBRACKET instance_body { () }
  | NEWTYPE upper_id typarams_opt newtype_rhs          { () }
  | EFFECT upper_id typarams_opt EQ eff_decl_body      { () }
  | MODULE upper_id module_body                        { () }
  | EXTERN TEXT LET extern_sig                         { () }

and_bindings:
  |                          { () }
  | AND binding and_bindings { () }

(* [FIX-5] 関数形とパターン束縛形。パターン側は bind_pat に制限し、
   小文字頭の ctor パターン (case print(m) 用) を排除する *)
binding:
  | lower_id typarams_opt LPAREN params RPAREN sig_tail EQ exp { () }
  | bind_pat annot_opt EQ exp                                  { () }

(* [FIX-9] 返り値注釈と関数の eff 行 *)
sig_tail:
  |              { () }
  | AT eff       { () }
  | COLON ty_ret { () }
ty_ret:
  | union_ty        { () }
  | union_ty AT eff { () }
  | arrow_ty        { () }

annot_opt: { () } | COLON ty { () }

extern_sig: lower_id typarams_opt LPAREN params RPAREN sig_tail { () }

module_body:   lbrace items RBRACE { () }
instance_body: lbrace items RBRACE { () }

class_body: lbrace class_items RBRACE { () }
class_items:
  |                             { () }
  | semi class_items            { () }
  | class_item                  { () }
  | class_item semi class_items { () }
class_item:
  | VAL lower_id typarams_opt COLON ty { () }
  | DERIVE lower_id                    { () }

newtype_rhs:
  |                           { () }
  | LPAREN ctor_fields RPAREN { () }
  | EQ ctors                  { () }
  | EQ HOLE                   { () }

ctors: ctor { () } | ctor VERTICAL ctors { () }
ctor:
  | upper_id                           { () }
  | upper_id LPAREN ctor_fields RPAREN { () }
ctor_fields: { () } | ctor_field_list { () }
ctor_field_list:
  | ctor_field                       { () }
  | ctor_field COMMA                 { () }
  | ctor_field COMMA ctor_field_list { () }
ctor_field: ty { () } | lower_id COLON ty { () }

eff_decl_body: lbrace eff_ops RBRACE { () }
eff_ops: { () } | eff_op_list { () }
eff_op_list:
  | eff_op                   { () }
  | eff_op COMMA             { () }
  | eff_op COMMA eff_op_list { () }
eff_op: lower_id COLON ty { () }

typarams_opt: { () } | typarams { () }
typarams: LBRACKET typaram_list RBRACKET { () }
typaram_list: typaram { () } | typaram COMMA typaram_list { () }
typaram: ty_ident hkt_opt cls_opt { () }
ty_ident: lower_id { () } | upper_id { () }
hkt_opt: { () } | LBRACKET LOWLINE RBRACKET { () }
cls_opt: { () } | COLON cls_list { () }
cls_list: upper_id { () } | upper_id PLUS cls_list { () }

kind_annot_opt: { () } | COLON upper_id { () }

params: { () } | param_list { () }
param_list:
  | param                  { () }
  | param COMMA            { () }
  | param COMMA param_list { () }
param: pat annot_opt { () }

(* ------------------------------------------------------------------ *)
(* 式                                                                  *)
(* ------------------------------------------------------------------ *)

exp:
  | FN LPAREN params RPAREN EQ_GREATER exp { () }
  | postfixed                              { () }

postfixed:
  | postfixed MATCH clause_body  { () }
  | postfixed HANDLE clause_body { () }
  | or_exp                       { () }

or_exp:  or_exp BIG_VERTICAL and_exp   { () } | and_exp { () }
and_exp: and_exp BIG_AMPERSAND cmp_exp { () } | cmp_exp { () }
cmp_exp: add_exp cmp_op add_exp        { () } | add_exp { () }
%inline cmp_op:
  | BIG_EQ { () } | EXCLAMATION_EQ { () } | LESS { () } | LESS_EQ { () }
  | GREATER { () } | GREATER_EQ { () }
add_exp: add_exp add_op mul_exp { () } | mul_exp { () }
%inline add_op: PLUS { () } | HYPHEN { () }
mul_exp: mul_exp mul_op prefix_exp { () } | prefix_exp { () }
%inline mul_op: ASTERISK { () } | SOLIDUS { () }
prefix_exp:
  | EXCLAMATION prefix_exp { () }
  | HYPHEN NUMBER          { () }
  | postfix_exp            { () }

(* [FIX-1] 式位置では long_id を使わず、DOT 連鎖を一様に左再帰で食い、
   先頭の大文字成分をパスに畳むのは意味アクションの仕事にする。
   [FIX-3] #Foo(args) も postfix 呼び出し規則に相乗りさせ、
   意味アクションで Variant に畳む *)
postfix_exp:
  | postfix_exp DOT lower_id            { () }
  | postfix_exp DOT upper_id            { () }
  | postfix_exp BACKSLASH lower_id      { () }
  | postfix_exp LPAREN call_args RPAREN { () }
  | atom                                { () }

atom:
  | NUMBER { () } | TEXT { () } | BOOL { () } | HOLE { () }
  | lower_id                                { () }
  | upper_id                                { () }
  | HASH_IDENT                              { () }
  | PERFORM perform_op LPAREN call_args RPAREN { () }
  | RESUME LPAREN call_args RPAREN          { () }
  | RUN lower_id run_body                   { () }
  | block                                   { () }
  | record_exp                              { () }
  | paren_exp                               { () }

perform_op: long_id { () }

block: LBRACE_BLOCK items RBRACE { () }
(* [FIX-7] run h {} は LBRACE_RECORD になるので union で受ける *)
run_body: lbrace items RBRACE { () }

call_args: { () } | arg_list { () }
arg_list:
  | arg                { () }
  | arg COMMA          { () }
  | arg COMMA arg_list { () }
arg: lower_id EQ exp { () } | exp { () }

record_exp:
  | LBRACE_RECORD RBRACE                        { () }
  | LBRACE_RECORD EXTENDS exp RBRACE            { () }
  | LBRACE_RECORD field_list RBRACE             { () }
  | LBRACE_RECORD field_list EXTENDS exp RBRACE { () }
  | LBRACE_RECORD exp WITH field_list RBRACE    { () }
field_list:
  | field                  { () }
  | field COMMA            { () }
  | field COMMA field_list { () }
field: lower_id EQ exp { () } | lower_id { () }

paren_exp:
  | LPAREN RPAREN                    { () }
  | LPAREN exp RPAREN                { () }
  | LPAREN exp COMMA RPAREN          { () }
  | LPAREN exp COMMA exp_list RPAREN { () }
exp_list:
  | exp                { () }
  | exp COMMA          { () }
  | exp COMMA exp_list { () }

clause_body: lbrace clauses RBRACE { () }
(* [FIX-8] 節間の NL は ASI が落とす (CASE は can_begin_statement に無い) *)
clauses: clause { () } | clause clauses { () }
clause: CASE pat guard_opt EQ_GREATER exp { () }
guard_opt: { () } | IF exp { () }

(* ------------------------------------------------------------------ *)
(* パターン                                                            *)
(* ------------------------------------------------------------------ *)

pat:
  | LOWLINE                           { () }
  | NUMBER { () } | TEXT { () } | BOOL { () }
  | HYPHEN NUMBER                     { () }
  | long_id                           { () }
  | long_id LPAREN pat_args RPAREN    { () }
  | HASH_IDENT                        { () }
  | HASH_IDENT LPAREN pat_args RPAREN { () }
  | record_pat                        { () }
  | paren_pat                         { () }

(* [FIX-5] let 束縛のパターン: 小文字頭の呼び出し形を持たない *)
bind_pat:
  | LOWLINE                            { () }
  | lower_id                           { () }
  | upper_path                         { () }
  | upper_path LPAREN pat_args RPAREN  { () }
  | record_pat                         { () }
  | paren_pat                          { () }

pat_args: { () } | pat_arg_list { () }
pat_arg_list:
  | pat_arg                    { () }
  | pat_arg COMMA              { () }
  | pat_arg COMMA pat_arg_list { () }
pat_arg: lower_id EQ pat { () } | pat { () }

(* [FIX-4] ...rest を要素列の末尾要素として畳む *)
record_pat: LBRACE_RECORD rp_items RBRACE { () }
rp_items:
  |                            { () }
  | DOTDOTDOT lower_id         { () }
  | pat_field                  { () }
  | pat_field COMMA rp_items   { () }
pat_field: lower_id EQ pat { () } | lower_id { () }

paren_pat: LPAREN pp_items RPAREN { () }
pp_items:
  |                        { () }
  | DOTDOTDOT lower_id     { () }
  | pat                    { () }
  | pat COMMA pp_items     { () }

(* ------------------------------------------------------------------ *)
(* 型                                                                  *)
(* ------------------------------------------------------------------ *)

(* [FIX-2] arrow は atom_ty ではなく ty の直下に置く *)
ty: union_ty { () } | arrow_ty { () }

arrow_ty: LPAREN ty_list0 RPAREN EQ_GREATER arrow_ret { () }
arrow_ret:
  | union_ty eff_opt { () }
  | arrow_ty         { () }
eff_opt: { () } | AT eff { () }

union_ty:
  | union_ty VERTICAL app_ty { () }
  | app_ty                   { () }

app_ty:
  | atom_ty                           { () }
  | atom_ty LBRACKET ty_args RBRACKET { () }

ty_args: ty_arg { () } | ty_arg COMMA ty_args { () }
ty_arg: ty { () } | LOWLINE { () }

atom_ty:
  | long_id                           { () }
  | HASH_IDENT                        { () }
  | HASH_IDENT LPAREN ty_list0 RPAREN { () }
  | brace_ty                          { () }
  | LPAREN ty_list0 RPAREN            { () }   (* タプル型/グループ化 *)

ty_list0: { () } | ty_list { () }
ty_list:
  | ty               { () }
  | ty COMMA         { () }
  | ty COMMA ty_list { () }

(* [FIX-2b][FIX-10] レコード型とエフェクト行を 1 本の非終端に統合する。
   - 分けたままだと `@ {..}` の位置で record_ty と eff_row が reduce/reduce する
   - 統合しないと `type Request: EffectRow = {ReqId, Logger, Tracer}`
     (sample.kel:446) が型位置でパースできない
   record か row かは意味アクションが要素の形で判定する *)
brace_ty:
  | lbrace RBRACE                            { () }
  | lbrace EXTENDS ty RBRACE                 { () }
  | lbrace brace_item_list RBRACE            { () }
  | lbrace brace_item_list EXTENDS ty RBRACE { () }
brace_item_list:
  | brace_item                       { () }
  | brace_item COMMA                 { () }
  | brace_item COMMA brace_item_list { () }
brace_item:
  | lower_id COLON ty { () }   (* レコード型のフィールド *)
  | eff_name          { () }   (* エフェクト行の要素 *)

eff:
  | eff_name { () }
  | brace_ty { () }
eff_name:
  | long_id                           { () }
  | long_id LBRACKET ty_args RBRACKET { () }
