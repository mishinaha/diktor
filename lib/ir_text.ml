(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第19章 KIR の正準のテキスト

   本章は、第17章の `Ir.program` を正準のテキスト(`.kirt`)に印字する。
   規範は親リポジトリの `doc/IRSpec.md` の 12 節である。
   正準のテキストは、2 つの書き手(Diktor と RustKeleut のフロントエンド)と
   RustKeleut の逆アセンブラが、バイト単位で同じに出さなければならない。
   そのため、印字の自由度をすべて規則で潰してある。

   | 自由度 | 規則 |
   |---|---|
   | 改行と字下げ | 子がすべて葉のノードは 1 行、ほかは子ごとに改行して 2 桁下げる |
   | 行の幅 | 折り返さない |
   | 文字列の綴り | 0x20 から 0x7E のバイトだけをそのまま書き、ほかは小文字の 16 進のエスケープ |
   | `f64` の綴り | ビット列を 16 桁の 16 進で書く |
   | 短い名前の綴り | 名前の字句に合えば裸で、合わなければ文字列として書く |

   印字は 2 段で行う。
   まず `Ir.program` を、キーワード、原子、子のノードの 3 つからなる一様な木(`node`)に写す。
   次に、その木を字下げの規則で文字列にする。
   字下げの規則が見るのは木の形だけなので、規則を 1 か所に置ける。
   KIR の構文ごとに改行の位置を書く形にすると、構文を足すたびに規則を写し間違えうる。 *)

(* ## 19.1 一様な木

   正準のテキストのノードは、先頭のキーワード、原子の列、子のノードの列の順に並ぶ。
   原子と子が混ざる形は無く、原子はすべて子より前にある。
   原子は、整数、ビット列、文字列、名前の 4 種である。
   整数は綴りのまま持ち、`int`、`int32`、`int64` のどれから作っても同じ形になるようにする。
   印や型の綴り(`tail`、`i32` など)も名前の原子として書く。
   先頭のキーワード(`lit` など)は原子ではない。 *)
type atom = AInt of string | ABits of int64 | AStr of string | AName of string

type node = { kw : string; atoms : atom list; kids : node list }

let node ?(atoms = []) ?(kids = []) kw = { kw; atoms; kids }

let int n = AInt (string_of_int n)

let name s = AName s

let str s = AStr s

(* ## 19.2 字句の綴り

   名前の字句は、英字か `_` で始まり英数字と `_` が続く綴りを、`.` でつないだものである。
   ラベル、コンストラクタ、操作、メソッドの短い名前は、この字句に合えば裸で書き、
   合わなければ文字列として書く。
   記号は `/` を含むので、常に文字列になる。

   文字列は、二重引用符と逆斜線を逆斜線でエスケープし、0x20 から 0x7E のほかのバイトをそのまま書く。
   ほかのバイトは、逆斜線、`x`、小文字の 2 桁の 16 進で書く。
   UTF-8 の多バイト文字もバイトごとにエスケープするので、正準のテキストは ASCII だけからなる。
   文字列の中身が名前でも記号でも任意のバイト列でも、規則は同じである。 *)
let is_name s =
  let n = String.length s in
  let head c = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c = '_' in
  let body c = head c || (c >= '0' && c <= '9') in
  (* 位置 i から 1 つの成分を読み、成分の終わりの位置を返す。成分が空なら None *)
  let comp i =
    if i < n && head s.[i] then (
      let j = ref (i + 1) in
      while !j < n && body s.[!j] do
        incr j
      done;
      Some !j)
    else None
  in
  let rec go i = match comp i with Some j when j = n -> true | Some j when s.[j] = '.' -> go (j + 1) | _ -> false in
  go 0

let short s = if is_name s then AName s else AStr s

let escape buf s =
  Buffer.add_char buf '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | c when Char.code c >= 0x20 && Char.code c <= 0x7E -> Buffer.add_char buf c
      | c -> Buffer.add_string buf (Printf.sprintf "\\x%02x" (Char.code c)))
    s;
  Buffer.add_char buf '"'

let add_atom buf = function
  | AInt s | AName s -> Buffer.add_string buf s
  | ABits b -> Buffer.add_string buf (Printf.sprintf "0x%016Lx" b)
  | AStr s -> escape buf s

(* ## 19.3 字下げ

   ノードの開き括弧の桁を `c` とする。
   子がすべて葉(子を持たないノード)なら、ノード全体を 1 行に書き、要素を空白 1 個で区切る。
   子が 1 つも無いノードも、この規則で 1 行になる。
   ほかの場合は、1 行目にキーワードと原子を書き、各子を改行して桁 `c+2` から書く。
   閉じ括弧は最後の子の閉じ括弧のすぐ後ろに置く。
   最上位のノードは桁 0 から書き、それぞれを改行で終える。 *)
let is_leaf n = n.kids = []

let rec add_node buf col n =
  Buffer.add_char buf '(';
  Buffer.add_string buf n.kw;
  List.iter
    (fun a ->
      Buffer.add_char buf ' ';
      add_atom buf a)
    n.atoms;
  if List.for_all is_leaf n.kids then
    List.iter
      (fun k ->
        Buffer.add_char buf ' ';
        add_node buf col k)
      n.kids
  else
    List.iter
      (fun k ->
        Buffer.add_char buf '\n';
        Buffer.add_string buf (String.make (col + 2) ' ');
        add_node buf (col + 2) k)
      n.kids;
  Buffer.add_char buf ')'

(* ## 19.4 KIR から一様な木へ

   各構文の写し方は IRSpec 12.5 節の文法のとおりである。
   印の欄(`tail` と `ntail`、`yield` と `noyield` など)は、既定の値でも省かずに書く。
   省ける欄を設けると、省くかどうかの判断が書き手ごとにずれうるからである。 *)
open Ir

let rep r = name (rep_name r)

let tail_atom b = name (if b then "tail" else "ntail")

let yield_atom b = name (if b then "yield" else "noyield")

let lit_node = function
  | LBool b -> node "lit" ~atoms:[ name "bool"; name (if b then "true" else "false") ]
  | LI32 n -> node "lit" ~atoms:[ name "i32"; AInt (Int32.to_string n) ]
  | LI64 n -> node "lit" ~atoms:[ name "i64"; AInt (Int64.to_string n) ]
  | LF64 b -> node "lit" ~atoms:[ name "f64"; ABits b ]
  | LStr s -> node "lit" ~atoms:[ name "str"; str s ]

let var_node = function
  | VLocal i -> node "local" ~atoms:[ int i ]
  | VEnv i -> node "env" ~atoms:[ int i ]
  | VDParam i -> node "dparam" ~atoms:[ int i ]

let rec dict_node = function
  | DInst (i, ps) -> node "dinst" ~atoms:[ str i ] ~kids:(List.map dict_node ps)
  | DVar v -> var_node v
  | DRecord fs -> node "drecord" ~kids:(List.map dict_field fs)
  | DVariant fs -> node "dvariant" ~kids:(List.map dict_field fs)
  | DBuiltin (c, t) -> node "dbuiltin" ~atoms:[ str c; str t ]

and dict_field (l, d) = node "field" ~atoms:[ short l ] ~kids:[ dict_node d ]

let rec pat_node = function
  | PWild -> node "wild"
  | PBind i -> node "bind" ~atoms:[ int i ]
  | PLit l -> lit_node l
  | PRecord (fs, tl) ->
      let fields = List.map (fun (l, p) -> node "field" ~atoms:[ short l ] ~kids:[ pat_node p ]) fs in
      let kind, rest = match tl with Closed -> ("closed", []) | Open -> ("open", []) | Rest p -> ("rest", [ pat_node p ]) in
      node "record" ~atoms:[ name kind ] ~kids:(fields @ rest)
  | PCtor (t, c, fs) ->
      node "ctor" ~atoms:[ str t; short c ] ~kids:(List.map (fun (i, p) -> node "field" ~atoms:[ int i ] ~kids:[ pat_node p ]) fs)
  | PVariant (l, p) -> node "variant" ~atoms:[ short l ] ~kids:[ pat_node p ]

let part_node kw ?(atoms = []) p = node kw ~atoms:(atoms @ [ str p.p_fn ]) ~kids:(List.map var_node p.p_caps)

let rec exp_node = function
  | Lit l -> lit_node l
  | Lit_error (k, s) -> node "lit_error" ~atoms:[ name (lit_error_kind_name k); str s ]
  | Local i -> node "local" ~atoms:[ int i ]
  | Env i -> node "env" ~atoms:[ int i ]
  | Global g -> node "global" ~atoms:[ str g ]
  | Construct (t, c, fs) ->
      node "construct" ~atoms:[ str t; short c ] ~kids:(List.map (fun (i, e) -> node "field" ~atoms:[ int i ] ~kids:[ exp_node e ]) fs)
  | Variant (l, e) -> node "variant" ~atoms:[ short l ] ~kids:[ exp_node e ]
  | Call c -> node "call" ~atoms:[ tail_atom c.c_tail; yield_atom c.c_yield ] ~kids:(List.map exp_node (c.c_fn :: c.c_args))
  | Method (c, m, d, os) -> node "method" ~atoms:[ str c; short m ] ~kids:(List.map dict_node (d :: os))
  | Opcall (c, m, d, args) -> node "opcall" ~atoms:[ str c; short m ] ~kids:(dict_node d :: List.map exp_node args)
  | Not e -> node "not" ~kids:[ exp_node e ]
  | And (a, b) -> node "and" ~kids:[ exp_node a; exp_node b ]
  | Or (a, b) -> node "or" ~kids:[ exp_node a; exp_node b ]
  | Closure (f, cs) -> node "closure" ~atoms:[ str f ] ~kids:(List.map var_node cs)
  | Dictabs (f, cs) -> node "dictabs" ~atoms:[ str f ] ~kids:(List.map var_node cs)
  | Dictapp (e, ds) -> node "dictapp" ~kids:(exp_node e :: List.map dict_node ds)
  | Let (i, a, b) -> node "let" ~atoms:[ int i ] ~kids:[ exp_node a; exp_node b ]
  | Letpat (p, a, b) -> node "letpat" ~kids:[ pat_node p; exp_node a; exp_node b ]
  | Letrec (items, e) ->
      node "letrec" ~kids:(List.map (fun (i, e) -> node "rec" ~atoms:[ int i ] ~kids:[ exp_node e ]) items @ [ exp_node e ])
  | Seq es -> node "seq" ~kids:(List.map exp_node es)
  | Match (e, cls) -> node "match" ~kids:(exp_node e :: List.map clause_node cls)
  | Rec_empty -> node "rec_empty"
  | Rec_extend (l, v, r) -> node "rec_extend" ~atoms:[ short l ] ~kids:[ exp_node v; exp_node r ]
  | Rec_select (l, e) -> node "rec_select" ~atoms:[ short l ] ~kids:[ exp_node e ]
  | Rec_restrict (l, e) -> node "rec_restrict" ~atoms:[ short l ] ~kids:[ exp_node e ]
  | Rec_update (l, r, v) -> node "rec_update" ~atoms:[ short l ] ~kids:[ exp_node r; exp_node v ]
  | Perform (e, op, args) -> node "perform" ~atoms:[ str e; short op ] ~kids:(List.map exp_node args)
  | Handle h ->
      let ops = List.map (fun (op, cls, p) -> part_node "op" ~atoms:[ short op; name (clause_class_name cls) ] p) h.h_ops in
      let opt kw = function Some p -> [ part_node kw p ] | None -> [] in
      node "handle"
        ~atoms:[ tail_atom h.h_tail; str h.h_effect ]
        ~kids:((part_node "body" h.h_body :: ops) @ opt "return" h.h_return @ opt "cancel" h.h_cancel)
  | Resume (t, e) -> node "resume" ~atoms:[ tail_atom t ] ~kids:[ exp_node e ]
  | Hole -> node "hole"

and clause_node c =
  let guard = match c.cl_guard with Some g -> [ node "guard" ~kids:[ exp_node g ] ] | None -> [] in
  node "clause" ~kids:((pat_node c.cl_pat :: guard) @ [ exp_node c.cl_body ])

(* 関数の欄は、記号、種類、`yield` の印を原子にし、残りを子のノードにする。
   `pats` は種類が `opclause` の関数だけが持ち、パターンが 0 個でも書く。 *)
let fn_node f =
  let reps kw rs = node kw ~atoms:(List.map rep rs) in
  let pats = if f.f_kind = Opclause then [ node "pats" ~kids:(List.map pat_node f.f_pats) ] else [] in
  let guard = match f.f_guard with Some g -> [ node "guard" ~kids:[ exp_node g ] ] | None -> [] in
  node "fn"
    ~atoms:[ str f.f_sym; name (fn_kind_name f.f_kind); yield_atom f.f_yield ]
    ~kids:
      ([
         reps "params" f.f_params;
         reps "locals" f.f_locals;
         node "dicts" ~atoms:[ int f.f_dicts ];
         reps "caps" f.f_caps;
         node "result" ~atoms:[ rep f.f_result ];
       ]
      @ pats @ guard @ [ exp_node f.f_body ])

let global_node g =
  let atoms =
    match g.g_kind with
    | GBuiltin -> [ name "builtin" ]
    | GExtern { abi; impl; dicts } -> [ name "extern"; name (abi_name abi); str impl; int dicts ]
    | GFn f -> [ name "fn"; str f ]
    | GDictabs f -> [ name "dictabs"; str f ]
    | GValue r -> [ name "value"; rep r ]
  in
  node "global" ~atoms:(str g.g_sym :: atoms)

let step_node = function
  | Def_value (g, f) -> node "def_value" ~atoms:[ str g; str f ]
  | Def_pattern (f, gs, p) -> node "def_pattern" ~atoms:[ str f ] ~kids:[ node "globals" ~atoms:(List.map str gs); pat_node p ]
  | Def_fns gs -> node "def_fns" ~atoms:(List.map str gs)
  | Def_dictabs g -> node "def_dictabs" ~atoms:[ str g ]
  | Def_instance i -> node "def_instance" ~atoms:[ str i ]
  | Run_exp f -> node "run_exp" ~atoms:[ str f ]

(* ## 19.5 ファイル

   最上位のノードは、見出し、単位、型、エフェクト、クラス、インスタンス、大域、関数、
   初期化の順である。
   各表の中の並びは書き出しの段(第18章)が決めて `Ir.program` に入れてあるので、
   本章は表をその順のまま印字する。
   見出しの第 3 の数は必要な機能のビットで、0.y の版では常に 0 である。 *)
let program_nodes (p : program) =
  let major, minor = p.version in
  let header = node "kir" ~atoms:[ int major; int minor; int 0 ] in
  let units = List.map (fun u -> node "unit" ~atoms:[ str u.u_key ] ~kids:[ node "paths" ~atoms:(List.map str u.u_paths) ]) p.units in
  let types = List.map (fun t -> node "type" ~atoms:[ str t.t_sym ] ~kids:(List.map (fun c -> node "ctor" ~atoms:[ short c.ct_name; int c.ct_arity ]) t.t_ctors)) p.types in
  let effects =
    List.map
      (fun e ->
        node "effect" ~atoms:[ str e.e_sym ]
          ~kids:
            (List.map
               (fun o ->
                 node "op" ~atoms:[ short o.o_name; int o.o_arity; name (if o.o_never then "never" else "resume"); name (if o.o_runtime then "runtime" else "user") ])
               e.e_ops))
      p.effects
  in
  let classes = List.map (fun c -> node "class" ~atoms:[ str c.c_sym ] ~kids:(List.map (fun (m, k) -> node "method" ~atoms:[ short m; int k ]) c.c_methods)) p.classes in
  let instances =
    List.map
      (fun i ->
        node "instance" ~atoms:[ str i.i_sym; str i.i_class; str i.i_head ]
          ~kids:(node "premises" ~atoms:[ int i.i_premises ] :: List.map (fun (m, k, f) -> node "method" ~atoms:[ short m; int k; str f ]) i.i_methods))
      p.instances
  in
  let globals = List.map global_node p.globals in
  let fns = List.map fn_node p.functions in
  let inits = List.map (fun u -> node "init" ~atoms:[ str u.u_key ] ~kids:(List.map step_node u.u_init)) p.units in
  (header :: units) @ types @ effects @ classes @ instances @ globals @ fns @ inits

let to_string p =
  let buf = Buffer.create 65536 in
  List.iter
    (fun n ->
      add_node buf 0 n;
      Buffer.add_char buf '\n')
    (program_nodes p);
  Buffer.contents buf
