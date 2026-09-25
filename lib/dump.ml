(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第4章 AST を目で見る

   第3章(parser.mly)は表面構文を脱糖して AST を作る。
   脱糖の結果が意図どおりかを確かめるために、本章は AST を S 式で標準出力に書き出す。
   `diktor --dump-ast FILE` を実行すると、脱糖後の AST がこの形で出力される。

   本章はパイプラインの本線には入らない。
   第16章(driver.ml)は、`--dump-ast` のときはパースだけを行って結果を本章に渡し、
   精緻化を呼ばずに終わる。
   そのため、このダンプには型が出ない。
   型はまだ書き込まれていない(第5章(tree.ml)の `ty_field` は `None` のままである)。
   型を見るには、型検査の経路と第9章(show.ml)の印字を使う。

   本章の内容は次の 2 つである。

   - S 式への写像。AST のコンストラクタそれぞれに、短い名前を 1 つずつ割り当てる
   - 出力の読み方。出力から第3章の脱糖を逆にたどる手順(§4.2)

   写像は ppx(`deriving show` の類)を使わず、手で書く。
   Diktor は、教材として最初から最後まで読めるように、依存を menhir と sedlex の 2 つに絞っている。
   コンストラクタの数だけ手で書く手間は、依存を 1 つ増やさないために受け入れている。

   ### 前章から受け取るもの

   - 第3章が作った脱糖済みの `decl list`。注釈(位置と、まだ空の型の欄)は使わない

   ### 誰にも渡さないもの

   - 出力を読むのは、人間と `test/ast.t` の cram ゴールデンだけである。
     出力を AST に読み戻す機能はない(§4.2) *)
open Syntax
open Tree.Tree

(* ## 4.1 S 式は 2 つのコンストラクタで足りる

   S 式の型 `sexp` のコンストラクタは、原子(`A`)と括弧(`L`)の 2 つだけである。
   属性も、位置も、型も持たない。
   S 式を選んだ理由は 2 つある。
   括弧の対応さえ合っていれば人間が木構造を追えることと、
   1 行の差分がそのまま木のどこが変わったかを示すことである。

   整形は `Format` に任せる。
   `hov` ボックスにインデント 1 を与えているので、行を折り返しても、
   続きの要素が開き括弧の直後の桁にそろう。
   折り返す位置は、`Format` が右端(既定では 78 桁)に合わせて決める。
   要素の区切りには `@ ` を使う。
   `@ ` は「ここに空白を 1 個置く。ただし、行が詰まっていればここで改行してよい」という指示である。
   空白を直接書くと折り返しが起きず、深い木が 1 行に伸びて読めなくなる。 *)
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

(* ## 4.2 出力の読み方

   ダンプは次の 3 つの手順で使う。

   1. 表面構文を 1 行書く
   2. 第3章のどの脱糖が効くはずかを、出力を見る前に予想する
   3. `--dump-ast` の出力と予想を突き合わせる

   手順 3 で食い違ったときは、手順 2 の予想のほうが誤っていることが多い。
   脱糖の規約は、§3.5 にある arity 1 の 3 つの規約のように互いに関係しているので、
   記憶に頼って予想すると、どれか 1 つを取り違えやすい。

   代表的な対応を次の表に示す(実際のゴールデンは `test/ast.t` にある)。

   | 書いたもの | ダンプ | 確かめていること |
   |---|---|---|
   | `(1, 2)` | `(extend _item 1 (extend _item 2 {}))` | タプルは `_item` が重複する行 |
   | `(1)` | `1` | 式の括弧はグループ化(§3.5) |
   | `(1,)` | `(extend _item 1 {})` | 1 要素のタプルはカンマで作る |
   | `f(1, 2)` | `(apply f (extend _item 1 (extend _item 2 {})))` | 引数もタプルと同じ行 |
   | `t._1` | `(select _item (restrict _item t))` | 先頭を剥がしてから選ぶ(§3.4) |
   | `{x, y}` | `(extend x x (extend y y {}))` | パンニング |
   | `{r with x = 3}` | `(update x 3 r)` | 更新は脱糖しない(§3.20) |
   | `#Point(1, 2)` | `(#Point (extend _item 1 (extend _item 2 {})))` | 引数が 2 個ならタプル |
   | `#Empty` | `(#Empty {})` | 引数が無ければ Unit のペイロード |
   | `Some(1)` | `(construct Some 1)` | コンストラクタの引数は畳まない(§3.6) |
   | `Parser.bind(p)` | `(apply Parser.bind (extend _item p {}))` | 最後の成分が小文字なら適用 |
   | `Parser.Parser(g)` | `(construct Parser.Parser g)` | 最後の成分が大文字なら構築 |

   最後の 3 行を比べると、§3.6 の規則が括弧の形の違いとして出力に現れていることが分かる。
   `apply` の第 2 引数は常に行だが、`construct` の引数は畳まれずにそのまま並ぶ。
   ラベル付き引数を宣言の順に並べ替えるのは第11章なので、パーサは引数を畳まずに渡す。

   `with` の糖衣(§3.8)の働きは、ダンプで見ると分かりやすい。
   次のプログラムを考える。

   ```
   let f = fn() => {
     with x = bind(p)
     pure(x)
   }
   ```

   このダンプは、およそ次のようになる。

   ```
   (dlet
    (binding f =
     (fn ()
      (apply bind
       (extend _item p
        (extend _item (fn (x) (apply pure (extend _item x {}))) {}))))))
   ```

   継続 `fn (x) ...` は `bind` の引数行のいちばん内側、つまり最後の引数に入り、
   元の `p` は外側に残っている。
   これが `with_splice` の再帰の結果である。

   ダンプの出力は、`test/ast.t` の cram のゴールデンで固定している。
   `test/ast.t` は sample.kel 全文のダンプの行数も固定しているので、
   文法や脱糖を変えると、たいていどこかに差分が出る。
   差分は `dune promote` で取り込めるが、取り込む前に差分を目で確かめる。
   このゴールデンは、第3章の設計判断を写したものだからである。

   このダンプは AST に読み戻せない。
   原子は生のまま出し、位置も型も落とす。
   エスケープするのは下の `quoted` だけで、
   テキストリテラルと extern の ABI 名だけを `String.escaped` に通す。

   数値と演算子の表記は、本章では組み立てず、ほかの章の関数で出す。
   数値は第2章(lexer.ml)の `show_number` で出すので、
   桁区切りも接尾辞も `--dump-tokens` と同じ見え方になる。
   数値の表記を出す関数が 1 つしかないので、2 つのダンプの表記は食い違わない。
   演算子の字面は、第7章(prims.ml)の `show_bin_op` で出す。 *)
let quoted s = "\"" ^ String.escaped s ^ "\""

(* ## 4.3 型のダンプ

   型式は、第3章がほとんど畳まずに運んだ形のままである。
   そのため型のダンプも型式とほぼ 1 対 1 に対応し、畳まれた形が見えるのは次の 3 か所だけである。

   - `EBraceRow` は `row` として出る。
     レコード型 `{x: Int32}` もエフェクト行 `{Print, Log}` も同じ `row` になり、
     フィールドは `x:` を付けて並び、エフェクトのラベルは何も付けずに並ぶ。
     §3.23 で 1 本に統合した非終端の形がそのまま見える
   - 型の位置の `(A)` は `(row (_item: A))` になる。式と違い、常に 1 要素のタプルである(§3.20)
   - `#Foo(A, B)` のペイロードは `(row (_item: A) (_item: B))` に畳まれる

   `tapp` は `EApply`、`=>` は矢印で、矢印にはエフェクト行があるときだけ後ろに `@` が付く。
   `_` は `EHole`、つまり型引数に書いた `_` である。

   `sexp_of_tparam` は型パラメータの束縛子を出す。
   `F[_]` のように穴を持つ束縛子にだけ `arity=1` の形で穴の数が付き、
   クラス制約があるときだけ `:` で始まるリストになる(§3.17)。
   束縛子は名前だけのことが多いので、既定では裸の原子にし、情報があるときだけ括弧で包む。
   ダンプ全体が、既定値を出さないという方針に従う。
   そのため、出力に現れない項目は既定値だと読んでよい。 *)
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

(* ## 4.4 パターンのダンプ

   パターンのダンプで見るべき点は、行が開いているか閉じているかである(§3.9)。

   `precord` の末尾に `...` と尾部のパターンが付いていたら、開いた行である。
   第3章はレコードパターン `{x}` の尾部に必ず `PWildcard` を置くので、
   ダンプには `(precord (x= x) ... _)` のように、書いていない `_` が現れる。
   この `_` は誤りではなく、書いていないフィールドを無視するという既定の尾部である。

   タプルパターン `(x, y)` のダンプ `(precord (_item= x) (_item= y))` には `...` が付かない。
   尾部が無いので閉じた行であり、単一化は要素の数がぴったり合うことを要求する。
   第10章(exhaust.ml)の網羅性検査がタプルとレコードで違う振る舞いをするのは、
   この `...` の有無を受け取っているからである。

   `pctor` はコンストラクタパターンである。
   ラベル付きの引数は `l=` を先頭に付けた括弧になり、`sexp_of_ctor_arg_pat` がその分岐を担当する。
   式の側の `sexp_of_ctor_arg` と同じ形なのは、
   `Construct` と `PCtor` が同じラベル解決(第11章の `RCtor` / `RCtorPat`)を受けるからである。 *)
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

(* ## 4.5 式のダンプ

   式のダンプは §4.2 の表のとおりに出る。
   ここでは、表に載っていない点を補足する。

   レコードの 4 つの操作は `extend` / `update` / `restrict` / `select` で、
   引数の順は、ラベルを先、対象の行を後に固定している。
   `(extend x 1 (extend y 2 {}))` は書いた順に左から読め、いちばん右の `{}` が行の底になる。
   AST の `RecordExtend (rest, l, v)` とは引数の順が違うが、これは意図した違いである。
   データ構造は残りの行に 1 枚ずつ積む形で組むのが自然で、
   読むときは何のラベルかを先に知りたいからである。

   1 つのブロックの文の並びは、平らな `seq` として出る。
   第3章の `block_of_items` は、自分の畳み込みでは `Seq` の入れ子を作らないからである(§3.7)。
   ただし、末尾以外の文として書いた入れ子のブロックは、`seq` の中の `seq` として現れる。
   `{ 1; { 2; 3 }; 4 }` がその例である。
   末尾の位置にある入れ子のブロックは平らになる。
   末尾の式がブロックの値になる規則によって、外側の `seq` に吸収されるからである。

   `let` のダンプは右へ深くなる。
   ブロックのダンプでは、`let` の連なりが右下がりの階段になり、各段の右側がスコープの範囲になる。
   Keleut の `{ }` が宣言の列ではなく入れ子の `Let` であることが、この形から分かる。

   `resume` は、引数が無ければ `(resume)`、値があれば `(resume e)` になる(§3.19)。
   `???` は `Hole` で、未実装の穴を表す。
   型検査は通り、評価がここに到達すると実行時エラーになる。

   `sexp_of_binding` は束縛の情報をすべて並べる。
   `(params ...)` があるかどうかが、関数の形とパターン束縛の形の違いである(§3.16)。
   `binding-pub` というタグは `pub` が付いていることを表す。
   型パラメータ、返り値の注釈、エフェクトの注釈も、書かれているときだけ現れる。
   ここでも既定値は出さない。 *)
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
  | BinOp (l, op, r) -> L [ A (Prims.show_bin_op op); sexp_of_exp l; sexp_of_exp r ]
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

(* ## 4.6 宣言のダンプ

   宣言のダンプは平板である。
   第3章が宣言をほとんど脱糖しないからである。
   個々の宣言の形を変える脱糖は、次の `newtype` の短縮形だけである。

   - `newtype UserId(Int32)` は `(newtype UserId (UserId Int32))` になる。
     短縮形は、型名と同じ名前のコンストラクタ 1 個に展開される(§3.10)

   トップレベルの `with` は、個々の宣言ではなく宣言の列を脱糖する。
   `with` より後の宣言はまとめて継続の本体に入り、全体が 1 個の `exp` になる(§3.8)。

   `let {x, y} = p` のようなパターン束縛は脱糖されず、
   `binding` の名前の位置にパターンが入った形で出る。
   `test/ast.t` の block2 の `let (x, y) = pair()` がその例である。
   パターン束縛を単一ケースの match と同じように扱うのは、第11章(elab.ml)である。

   脱糖ではないが、`pub` の有無も `-pub` 付きのタグとして見える。
   これは `set_pub` が付ける修飾子(§3.10)を、そのままタグに出したものである。

   残りは形の確認である。
   `class` は `val` と `derive` を並べ、`instance` はクラス名、型引数、本体の宣言の列を並べる。
   `instance` の本体が `dlet` の列になるのは、第3章が本体を `items` で読むからである(§3.15)。
   前提つきインスタンスでは、束縛子があるときだけ `(tparams …)` がクラス名の前に出る
   (`test/premise.t` の pr11)。
   束縛子が無いインスタンスの出力には何も加わらない。
   これも既定値を出さない方針の例である。

   `sexp_of_decl` が再帰関数なのは、`module` と `instance` が宣言を含むからである。
   ダンプに現れる入れ子は、第11章の `flatten_modules` が平らにする前の形である。
   module の入れ子をどう平らにするかは、第11章で扱う。

   `lib/dune` は Warning 8(網羅していない match)を有効にしている。
   AST にコンストラクタを 1 つ足すと、コンパイラが本章の `match` に警告を出すので、
   ダンプが構文の変更に取り残されたことに気づける。
   ただし、Warning 8 は `warn-error` に含まれていないので、ビルドは通る。
   この仕組みは、ビルドの警告を読む運用があって初めて働く。 *)
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
      (* 束縛子があるときだけ tparams のリストを先に出す。既定値を出さないという
         本章の方針に従う *)
      let base = [ A "instance" ] in
      let base = match i.ins_tparams with [] -> base | ts -> base @ [ L (A "tparams" :: List.map sexp_of_tparam ts) ] in
      L (base @ (A i.ins_class :: L (List.map sexp_of_ty i.ins_args) :: List.map sexp_of_decl i.ins_body))
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

(* ## 4.7 出力の口

   `dump_decls` は、宣言 1 個につき 1 回、`%a@.` で書き出す。
   `@.` は改行して出力をフラッシュする指示なので、次の宣言は新しい行から始まる。
   宣言ごとに行を改めるのは、ゴールデンの差分を宣言の単位に保つためである。

   `Format` は、標準出力のチャネルとは別に自分のバッファを持つ。
   最後の `pp_print_flush` は、このバッファに残った分を出し切る。
   各宣言の `@.` もフラッシュし、`dump_decls` は最後の宣言の後に何も書かないので、
   この呼び出しは保険である。 *)
let dump_decls out decls =
  let fmt = Format.formatter_of_out_channel out in
  List.iter (fun d -> Format.fprintf fmt "%a@." pp (sexp_of_decl d)) decls;
  Format.pp_print_flush fmt ()
