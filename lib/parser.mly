(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第3章 構文解析と脱糖

   第2章(lexer.ml)が渡すのは、(トークン, 開始位置, 終了位置)の三つ組の列である。
   この列では、ASI が区切りを補い終え、`{` も 3 種類に分類し終えている。
   本章はこの列を LR(1) で読み、第5章(tree.ml)以降が扱う小さな AST に落とす。

   このファイルの仕事は 2 つに分かれる。

   | 仕事 | すること | 書いてある場所 |
   |---|---|---|
   | 形を認める | Keleut の表面構文を LR(1) の文法として記述する | 文法規則の並び(§3.14 以降) |
   | 糖衣を剥がす | 表面の糖衣を AST の素の形に直す | 冒頭の補助関数群(§3.4〜§3.10) |

   本章の主題は後者である。
   Keleut の AST は、表面構文の見た目に比べて小さい。
   その差のほぼすべてを、このファイルの冒頭の補助関数が吸収する。

   本章は、名前解決をせず、型も見ず、`case` の節が `return` 節なのか操作節なのかも決めない。
   判断の材料は形だけで、具体的には「識別子の先頭が大文字か」「ドットの連鎖か」「引数が何個か」の 3 つである。
   それ以外は第11章(elab.ml)の仕事である。

   ### 前章から受け取るもの

   - ASI を適用した後のトークン列。改行は意味のある位置にだけ `NL` として残っている
   - `LBRACE_BLOCK` / `LBRACE_RECORD` / `LBRACE_TYPE` に分類済みの `{`
   - 各トークンの開始位置と終了位置

   ### 次章以降へ渡すもの

   - 脱糖済みの `decl list`。第4章(dump.ml)が S 式として表示し、
     第11章(elab.ml)が型と解決結果を書き込む
   - 全ノードに付いた `Location.span`。エラーメッセージが指す位置はここで決まる *)

(* ## 3.1 `%parameter` で注釈の型を外から差し替える

   第1章(syntax.ml)の AST は `Syntax.Make (Data)` というファンクタの中にあり、
   ノードはすべて `(Data.t, 中身)` の対である。
   `Data.t` は 1 つのノードに貼りつける注釈で、`Data.allocate : Location.span -> t` がそれを作る。

   パーサも同じ形にする。
   menhir の `%parameter` は、生成するモジュール全体を、
   `Make (Data : Syntax.Data)` というファンクタで包む。
   つまり、第1章の `Syntax.Make` と本章の `Parser.Make` は対になっていて、
   両方に同じ `Data` を渡すと同じ木の型になる。

   こうするのは、木を作る側と木に書き込む側が別だからである。
   第5章(tree.ml)の `ElabData` は `ty_field` と `resolved` という可変フィールドを持ち、
   第11章(elab.ml)がそこへ型と解決結果を書く。
   パーサはそのフィールドの存在を知る必要がない。
   第16章(driver.ml)が `Parser.Make (Tree.ElabData)` を呼ぶだけで、両者がつながる。
   注釈が要らない用途なら第1章の `EmptyData` を渡せばよく、ノードの注釈は unit になる。
   本実装は `EmptyData` をどこでも使っておらず、見本として置いてあるだけである。

   これが成り立つのは、`Syntax.Make` が**アプリカティブ**なファンクタだからである。
   OCaml では、同じファンクタに同じ引数を与えて作った `F(X).t` どうしは同じ型になる。
   パーサの中で `Syntax.Make(Data).decl` として作った値は、この性質によって、
   `Tree.Tree.decl` としてそのまま elab に渡せる。
   `Make` が生成的(ジェネレーティブ)なファンクタだったら、ここで型が合わず、
   木を詰め替える無駄な往復が必要になる。

   代償もある。
   文法を変更するたびにファンクタ越しの型検査が走るのでビルドが重くなり、型エラーも読みにくくなる。
   割に合わなくなったら、`Data` を `ElabData` に固定して `%parameter` をやめるという選択肢がある。 *)
%parameter <Data : Syntax.Data>
%{
(* ## 3.2 dune のラッパーと、空モジュール 1 個による回避策

   次の 1 行は、Keleut とも構文解析とも関係がなく、ビルド系の問題を回避するためのものである。

   dune はライブラリを `Diktor` という名前でラップし、
   中の各モジュールを `Diktor__Syntax` のような実名に置き換える。
   一方 menhir は、生成したパーサの型を ocamlc に推論させて `.mli` に書き出す。
   dune の menhir ルールは、この型推論を既定で行う。
   この 2 つが噛み合わない。
   推論に使う一時モジュールが、ライブラリ自身のラッパー名 `Diktor` を参照して壊れる。
   これが ocaml/dune#2450 である。

   この問題には、同じ名前の空モジュールを冒頭で 1 個定義し、
   その名前を局所的に覆い隠すという回避策が知られている。
   この行を消して壊れるときは、黙って壊れるのではなく、ビルドが失敗する。
   そのため、外すときはビルドが通ることを確かめる。

   続く 2 つの `open` で、AST のコンストラクタと、
   意味アクションが投げる `Syntax_error`(第1章 syntax.ml で定義)を修飾なしで書けるようにする。 *)
module Diktor = struct end

open Syntax
open Syntax.Make(Data)

(* ## 3.3 位置は三つ組で運ぶ

   Diktor は**全ノード**に span を持たせる。
   まともなエラーメッセージを出すには、全ノードに位置が要るからである。
   一部のノードにしか位置が無いと、後から位置を足すときに全ノードの構築箇所を書き換えることになる。

   そのために、位置はトークンの値には載せず(`%token <Location.t> LET` のような形にはせず)、
   字句と構文のあいだをトークンとは別に流す。
   menhir の伝統的な API は `(Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a` という形をしていて、
   位置を `Lexing.lexbuf` の可変フィールドから読む。
   sedlex はその lexbuf を持たない。
   そこで第2章(lexer.ml)は、`MenhirLib.Convert.Simplified.traditional2revised` で改訂版の API に変換する。
   改訂版の API は `(unit -> token * position * position) -> 'a` という形で、
   トークンと開始位置と終了位置の三つ組を 1 個ずつ受け取る。
   この関数呼び出し 1 つが、字句層と構文層をつなぐ唯一の継ぎ目である。

   この変換により `$sloc` が実際の位置を返すので、意味アクションは `mk $sloc x` と書くだけで済む。
   位置の出所は、第2章が渡す三つ組の 1 か所だけである。
   全ノードに入れた位置は、第11章の `at_node` が型エラーに結びつけている。

   不変条件が 1 つある。
   **新しいノードは `mk` を通して作る**。
   例外は既にあるノードの位置を借りる場合だけで、しかも**借り元のノードを捨てるとき**に限る。
   本章でこれに当たるのは、`block_of_items` が宣言の位置を借りて `Let` と `LetRec` を作る箇所(§3.7)と、
   `with_splice` が引数行を差し替えるときに、
   外側の `Apply` と行ノードの位置を借りる箇所(§3.8)である。
   どちらも、借り元のノードはその場で捨てる。
   借りているのは位置だけではなく ElabData のレコードそのものなので、
   借り元のノードを捨てずに残すと、2 つのノードが型フィールドまで共有してしまう。
   §3.7 で `Seq` を例にこの問題を説明する。 *)
let mk (sp, ep) x = (Data.allocate { Location.start = sp; Location.finish = ep }, x)

(* ## 3.4 大文字かどうかの判定と `dot_select`

   Keleut には、モジュールのパスとフィールドの選択を書き分ける構文が無い。
   `Foo.bar` が「モジュール `Foo` の `bar`」なのか「変数 `Foo` のフィールド `bar`」なのかは、
   **先頭が大文字かどうか**だけで決まる。
   この判定をするのは `is_upper` だけで、このファイルの分岐の大半がこの 1 行に頼っている。

   式の位置でドットの連鎖に `long_id` 非終端を使うと、conflict が起きる。
   `Foo.bar` を読んだ時点で、`long_id` を伸ばすのか後置の選択に落とすのかが決まらず、
   shift/reduce になる。
   型の位置とパターンの位置には競合する DOT の規則が無いので `long_id` をそのまま使えるが、
   後置の選択と競合する式の位置では使えない。

   そこで文法の側は、`postfix_exp DOT id` という一様な左再帰の連鎖ですべてを読み、
   仕分けは意味アクション `dot_select` に任せる。
   規則は次の 1 つである。
   **先頭から続く大文字の成分とその直後の 1 成分をパスにまとめ、残りをレコードの選択にする。**
   `Db.Conn.exec.x` なら、`Db.Conn.exec` がパスで、`.x` が選択である。

   `t._N` は、`_item` を剥がす操作を繰り返す形に脱糖する。
   タプルは第1章のとおり `_item` を**重複させた**行で表し、
   Scoped Labels の最左一致では `t._item` が常に最初の要素を指す。
   2 番目の要素を取るには、最初の 1 つを剥がしてから選ぶ。
   つまり `(t \ _item)._item` である。
   一般に `t._N` は、`\ _item` を N 回適用してから `._item` を選ぶ。
   この短い再帰がタプルの射影のすべてで、専用の AST ノードも専用の型規則も要らない。
   剥がす側の仕組みは第8章(unify.ml)の `rewrite_row` にある。

   `t.0` と書くと構文エラーになる。
   `_0` は LOWER_IDENTIFIER なので選択の規則にそのまま乗るが、
   `0` は NUMBER なので乗らないからである。
   これは実装の都合ではなく、sample.kel:175 が意図した仕様である。
   `is_index_label` は綴りの形だけを見て、
   先頭が `_` で残りが 10 進の数字だけの名前を添字のラベルと判定する。 *)
let is_upper s = s <> "" && s.[0] >= 'A' && s.[0] <= 'Z'

let is_index_label s =
  String.length s >= 2 && s.[0] = '_'
  && (let ok = ref true in
      String.iteri (fun i c -> if i > 0 && not (c >= '0' && c <= '9') then ok := false) s;
      !ok)

let dot_select sloc e id =
  match e with
  | (_, Ident (LongId comps)) when List.for_all is_upper comps ->
      mk sloc (Ident (LongId (comps @ [ id ])))
  | _ ->
      if is_upper id then raise (Syntax_error ("レコードのラベルに大文字識別子は使えません: " ^ id))
      else if is_index_label id then
        (* t._N = (t \ _item)^N ._item *)
        let n = int_of_string (String.sub id 1 (String.length id - 1)) in
        let rec strip e n = if n = 0 then e else strip (mk sloc (RecordRestriction (e, "_item"))) (n - 1) in
        mk sloc (RecordSelection (strip e n, "_item"))
      else mk sloc (RecordSelection (e, id))

(* ## 3.5 引数リストは行になる

   Keleut の関数は多引数だが、型には多引数の矢印が無い。
   **引数は閉じた `_item` 行のレコード**であり、`TArrow` の第 1 引数はただのレコード型である。
   その変換が `record_of_args` で、`f(a, b)` は `Apply (f, {_item = a, _item = b})` になる。
   ラベル付きの引数 `l = e` を書いたときだけ、`_item` の代わりにそのラベルが入る。

   この表現から得られるものが 2 つある。
   1 つ目は、**arity の検査がただの単一化になる**ことである。
   引数の個数が違えば、閉じた行どうしの単一化が失敗する。
   2 つ目は、`fst[A, R](t: {_item: A extends R})` のような、タプルの先頭を取る前置多相の関数を、
   同じ仕組みでそのまま書けることである。
   タプルと引数リストが同じ表現だからである。

   行の組み方にも意味がある。
   `row` は末尾から畳むので、**先頭の要素が最も外側**の `RecordExtend` になる。
   第14章(interp.ml)が外側から評価すれば、引数の評価順は自然に a → b → c になる。
   評価順を別に決める必要はない。

   arity 1 に関わる規約は 3 つあり、**3 つとも別のもの**である。

   | 書き方 | 脱糖 | 理由 |
   |---|---|---|
   | `f(a)` | `{_item = a}`(1 要素の引数行) | 引数は常に行 |
   | `(a)` | `a` そのもの(グループ化) | 括弧はグループ化。1-タプルは `(a,)` |
   | `#Foo(a)` | ペイロード `a` そのもの | 下記 |

   `#Foo(a)` を 1 要素のタプルに包まないのは、
   式 `#Syntax((l, c))` とパターン `case #Syntax(l, c)` を単一化できるようにするためである。
   両方が「ペイロードは 2 要素のタプル」に落ちる必要があり、片方だけ余分に包むと合わない。
   `variant_payload` の 1 引数の場合がこの規約の実体で、
   同じ規約をパターン側と型側にも置いている(§3.9)。 *)
let record_of_args sloc args =
  let rec row = function
    | [] -> mk sloc RecordEmpty
    | (label, v) :: tl ->
        let l = match label with Some l -> l | None -> "_item" in
        mk sloc (RecordExtend (row tl, l, v))
  in
  row args

let tuple_exp sloc exps = record_of_args sloc (List.map (fun e -> (None, e)) exps)

let variant_payload sloc = function
  | [ (None, e) ] -> e
  | args ->
      if List.exists (fun (l, _) -> l <> None) args then
        raise (Syntax_error "#Foo(...) にラベル付き引数は使えません")
      else tuple_exp sloc (List.map snd args)

(* ## 3.6 `call` は先頭が大文字なら構築、小文字なら適用にする

   呼び出しの `(` を読んだ時点で、それが何であるかは 3 通りありうる。

   - `#Foo(...)` はヴァリアントの構築である。
     `atom` の `HASH_IDENT` が作った空のペイロードの `Variant` を、
     ここで実際のペイロードに差し替える。
     `atom` の側に引数リストを持たせると shift/reduce になるので、後置の呼び出しとして受ける
   - `Parser.Parser(...)` は、パスの最後の成分が大文字なので `Construct` になる
   - `Parser.bind(...)` は、最後の成分が小文字なので `Apply` になる

   `call` は最後の成分だけを見て判定する。
   `Parser.Parser` と `Parser.bind` が同じパスの接頭辞を持ちながら違う意味になるのはそのためで、
   「大文字はコンストラクタ、小文字は値」という Keleut の綴りの規約をそのまま使っている。

   `Construct` だけは引数を行に畳まず、ラベル(`ca_label`)を持たせたまま残す。
   コンストラクタのフィールドには宣言側の順序があり、
   ラベル付きの引数を実引数の位置へ並べ替えるには宣言表が要るからである。
   並べ替えは第11章(elab.ml)が行い、結果を第5章(tree.ml)の `resolved` に `RCtor` として書く。
   パーサは知らないことを推測せず、素材のまま渡す。 *)
let call sloc callee args =
  match callee with
  | (_, Variant (s, (_, RecordEmpty))) -> mk sloc (Variant (s, variant_payload sloc args))
  | (_, Ident (LongId comps)) when is_upper (List.nth comps (List.length comps - 1)) ->
      mk sloc (Construct (LongId comps, List.map (fun (l, e) -> { ca_label = l; ca_exp = e }) args))
  | _ -> mk sloc (Apply (callee, record_of_args sloc args))

(* ## 3.7 `block_of_items` で宣言の列を式にする

   `{ ... }` のブロックの中身は、トップレベルと同じ `items` 非終端で読む(§3.15)。
   読んだ結果は宣言の列なので、式にするにはここで畳み直す。

   - 末尾の式がブロックの値になる
   - `let` は、右側の残りすべてを本体にした `Let` になる。スコープが自然に効く
   - `let rec ... and ...` は `LetRec` になる
   - 値にならない式が並んだら `Seq` にまとめる
   - 空のブロック `{}` は `RecordEmpty` になる。Keleut の Unit は空レコードである

   `Seq` の畳み込みは、残りの文を畳んだ結果が `Seq es` なら、それを入れ子にせず、
   `e :: es` を列に持つ `Seq` を作る。
   こうして、1 つのブロックに並んだ文から `Seq` の入れ子を作らないようにしている。
   平らになるのは、畳み込みが自分で作る列と、末尾の位置にある入れ子のブロックだけである。
   末尾の入れ子のブロックはそのままブロックの値になるので、
   そのブロックが作った `Seq` の先頭に前の文が足されていく。
   非末尾の文として書いた入れ子のブロック `{ 1; { 2; 3 }; 4 }` は、入れ子の `Seq` のまま残る。
   これは `--dump-ast` で確かめられる。
   評価の意味はどちらでも同じである。

   `Let` と `LetRec` は位置を借りる(§3.3 の例外)。
   `let` 宣言自身の `d` を使うので、位置は正確である。
   借り元の宣言のノードはここで捨てるので、共有による副作用も無い。

   `Seq` は位置を借りず、2 か所とも `mk sloc` で新しいノードを作る。
   `fst` で借りられるのは span ではなく ElabData のレコードそのものなので、
   `Seq` が中の文の式ノードから借りると、`Seq` のノードとその文のノードが型フィールドまで共有する。
   すると elab が `Seq` に書き込む型が、その文の型を上書きする。
   たとえば型の付くブロック `{ 1; s }` で `s` が文字列リテラルのとき、
   数値リテラル `1` の型が String になる。
   その結果、第14章の `number_value` が実行時エラーで落ちる。
   `mk sloc` で作れば、位置はブロック全体になり、共有は起きない。
   パーサからは `Data.t` の中身を読めない(第1章の `allocate` だけが見える)ので、
   「先頭の文の始点から末尾の文の終点まで」の span を組むことはできず、
   `mk sloc` のほかに方法は無い。

   最後の分岐は、`items` をすべての位置で共有した代償である。
   `module` や `type` はブロックの中では式に落とせないので、ここで構文エラーにするしかない。
   文脈の違反は elab が検査するという原則に対して、この 1 行は例外である。 *)
let rec block_of_items sloc items =
  match items with
  | [] -> mk sloc RecordEmpty
  | [ (_, DExp e) ] -> e
  | (_, DExp e) :: rest -> (
      match block_of_items sloc rest with
      | (_, Seq es) -> mk sloc (Seq (e :: es))
      | r -> mk sloc (Seq [ e; r ]))
  | (d, DLet b) :: rest -> (d, Let (b, block_of_items sloc rest))
  | (d, DLetRec bs) :: rest -> (d, LetRec (bs, block_of_items sloc rest))
  | _ :: _ -> raise (Syntax_error "この宣言はブロック内では使えません(let / let rec / 式のみ)")

(* ## 3.8 `with_splice` で継続を引数の末尾に差し込む

   `with` は次の形の糖衣である。

   ```
   with x = f(a)
   残りの文…
   ```

   これは `f(a, fn(x) => 残りの文…)` になる。
   この糖衣を使うと、コールバックを取る API の呼び出しを、
   CPS を手で書かずに直列のコードとして書ける。

   実装は、引数行の最も内側の `RecordEmpty` を `RecordExtend (RecordEmpty, _item, k)` に差し替えるだけである。
   行は末尾から畳んである(§3.5)ので、最も内側は最後の引数であり、継続は引数リストの末尾に付く。
   継続が最後に評価されるという評価順も、同じ理由で自然に正しくなる。

   継続の引数の個数は 2 通りある。

   - `pat` が `_` なら **0 引数**の継続 `fn() => 残り`
   - それ以外なら **1 引数**の継続 `fn(pat) => 残り`

   この分岐は、`with _ = with_file(src)`(sample.kel:617, :619)が要求する `body: () => A` と、
   `with x = Parser.bind(...)`(:632)が要求する `(A) => ...` の両方を、同じ糖衣で満たすためにある。
   `_` のときも値を捨てる 1 引数の継続にすると、前者に型が付かない。

   右辺が呼び出しでなければエラーにする。
   行を差し込む先が無いからである。
   これは、パーサが形だけで判断できる数少ない意味上の検査の 1 つである。 *)
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

(* ## 3.9 閉じた行と開いた行の分かれ目

   ここからの 4 つの補助関数は、タプルとヴァリアントのペイロードを行として組み、
   その行を閉じるか開くかを決める。
   この選択は第8章(unify.ml)の単一化と第10章(exhaust.ml)の網羅性検査にそのまま効く。
   そのため、ここはパーサの中でいちばん意味論に近い場所である。

   - `pat_tuple` の `rest_opt` が `None` なら**閉じた行**である。
     要素数がぴったり合うことを単一化が要求する。これがタプルパターンの arity 検査そのものである
   - `Some p` なら尾部を `p` に束縛する。`(x, ...rest)` の形である
   - レコードパターン(§3.22)は逆に**開いた行が既定**である。書いていないフィールドがあっても通る

   タプルでは「全部で何個か」が意味を持ち、レコードでは「必要なものがあるか」が意味を持つ。
   その違いを、そのまま行の開閉に写している。

   `variant_pat_payload` と `variant_ty_payload` は、
   §3.5 の 1 引数の規約をパターン側と型側に置いたものである。
   式・パターン・型の 3 か所で同じ畳み方をしているので、
   `#Syntax((l, c))` と `case #Syntax(l, c)` が噛み合う。
   `tuple_ty` が閉じた `EBraceRow` を作るのは、型の位置のタプルにも arity があるからである。 *)
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

(* ## 3.10 `pub` と、`newtype` の右辺をいったん生の形で受ける理由

   `pub` は宣言の前に付く修飾子である。
   文法で「`pub` 付き」と「`pub` 無し」の 2 系統を書くと宣言の規則が倍になるので、
   `decl_body` を作ってから `set_pub` で被せる。
   ここで立てたフラグは第11章が読み、可視性の検査、完全注釈の検査、
   「@ を省略した pub は純粋」の検査の 3 つに使う。
   `pub` を付けられない宣言(`type instance` と式文)は、ここで弾く。

   `newtype` の右辺には 4 つの形がある。
   省略、短縮形 `newtype UserId(Int32)`、コンストラクタの並び、`???`(未実装の穴)である。
   このうち短縮形は `newtype UserId = UserId(Int32)` の略で、
   **コンストラクタの名前が型の名前と同じ**である。
   ところが、右辺を読む規則からは型の名前が見えない。
   そこで、`nt_rhs_raw` という生の中間形でいったん受け(§3.17)、
   名前が見えている `decl_body` の意味アクション(§3.15)で解釈する。
   こうすれば、短縮形のために文法を分けずに済む。 *)
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

type nt_rhs_raw = RhsNone | RhsShort of field_decl list | RhsCtors of ctor_decl list | RhsHole
%}

(* ## 3.11 トークン表

   トークンの宣言は 2 段に分かれていて、上段が 44 個、下段が 20 個である。
   下段には、この言語に特有の構文のトークンが多い。
   `{` の 3 分割、`\`(レコードからのフィールドの除去)、`...`(尾部の束縛)、`???`(穴)と、
   `class`、`instance`、`derive`、`extends`、`extern`、`newtype`、`perform`、`resume`、`run`、
   `pub` のキーワード群がそれにあたる。

   トークンは位置のペイロードを**持たない**(§3.3)。
   値を運ぶのは `BOOL`、2 種類の識別子、`TEXT`、`NUMBER`、`HASH_IDENT` の 6 種類だけで、
   ほかのトークンは名前がすべての情報である。 *)
%token AND AT ASTERISK BIG_AMPERSAND BIG_EQ BIG_VERTICAL CASE COLON COMMA DOT
%token EFFECT EOF EQ EQ_GREATER EXCLAMATION EXCLAMATION_EQ FN GREATER HANDLE
%token HYPHEN IF LBRACKET LESS LET LOWLINE LPAREN MATCH MODULE NL PLUS RBRACKET
%token REC RPAREN SEMI SOLIDUS TYPE VAL VERTICAL WITH
%token <bool> BOOL
%token <string> LOWER_IDENTIFIER UPPER_IDENTIFIER TEXT
%token <Syntax.number> NUMBER

%token LBRACE_BLOCK LBRACE_RECORD LBRACE_TYPE RBRACE
%token BACKSLASH DOTDOTDOT LESS_EQ GREATER_EQ HOLE
%token CLASS INSTANCE DERIVE EXTENDS EXTERN NEWTYPE PERFORM PUB RESUME RUN
%token <string> HASH_IDENT

(* ## 3.12 開始記号の型と、`Error` という名前の衝突

   開始記号の型は、`Syntax.Make(Data).decl list` と**完全なパスで**書く。
   menhir はこの型注釈を、生成する `.mli` のシグネチャにそのまま書き出す。
   冒頭の `open` はファンクタ本体の中でしか効かないので、
   シグネチャに現れる型はファンクタの外から辿れるパスでなければならない。
   修飾なしの `decl list` と書くと、生成された `.mli` がコンパイルできない。

   このパスは §3.1 のアプリカティブ性とつながっている。
   生成されるのは `Parser.Make (Data)` の中の `val program : ... -> Syntax.Make(Data).decl list` である。
   ドライバが `Parser.Make (Tree.ElabData)` を呼ぶと、
   返る型は `Syntax.Make(Tree.ElabData).decl list` になる。
   これは `Tree.Tree.decl list` と同じ型である。
   詰め替えずに elab に渡せるのは、この型の等式による。

   もう 1 つの問題は、例外の名前の衝突である。
   menhir は構文エラーを `Error` という名前の例外で投げる。
   第2章(lexer.ml)の字句エラーが同じ名前だと、ドライバの `try` がどちらを捕まえたのか区別できない。
   そのため、字句エラーは `Lex_error` という別の名前にしてある。
   第16章(driver.ml)はこの 2 つと、意味アクションが投げる `Syntax_error` の 3 種類を別々に捕まえ、
   字句エラーと構文エラーを区別して報告したうえで、どちらも終了コード 2 にそろえる。 *)
%start <Syntax.Make(Data).decl list> program

(* ## 3.13 `--strict` で conflict 0 を保つ

   `lib/dune` は menhir を `--explain --strict` で走らせる。

   menhir は既定では conflict を警告にとどめ、記述順と優先順位で黙って解決する。
   conflict を放置すると、ビルドは通るのに、文法の意味が書いたつもりと違っている状態になりうる。
   `--strict` は警告をエラーに変え、`--explain` は conflict の説明をファイルに書き出す。
   前者が無いと、後者を読む機会が来ない。
   `--strict` がエラーに変える警告には、宣言しただけで文法のどこにも使わないトークンも含まれる。
   そのため、§3.11 のトークンはすべて文法のどこかで使われている。

   conflict 0 は一度達成すれば終わる状態ではなく、文法を変えるたびに保ち続ける必要がある。
   conflict を 1 個でも許すには、`--strict` を外すか、優先順位の宣言で抑え込む(§3.18)ことになる。
   `--strict` を外せば、その後に増えた conflict も警告にとどまる。
   とくに reduce/reduce は記述順で黙って解決されるので、
   `let f(x) = e` が関数定義ではなく小文字のコンストラクタのパターンとして読まれる、といった事故が、
   **テストが通ったまま**起こりうる(§3.16)。

   その代わり、文法の書き方は制約を受ける。
   本章の設計判断のうち次の 5 つは、どれもそう書かないと conflict するから選んだ形である。

   - ドット連鎖を意味アクションに任せる(§3.4)
   - `#Foo(...)` を後置で受ける(§3.6)
   - 矢印型を分離する(§3.23)
   - 束縛パターンを別の言語にする(§3.16)
   - レコード型とエフェクト行を 1 本の規則に統合する(§3.23) *)

%%

(* ## 3.14 文法の骨組み

   ここから下が文法の本体である。
   まず 3 つの小さな非終端を用意する。

   `semi` は改行とセミコロンを同じものとして扱う。
   ASI(第2章)が意味のある改行だけを `NL` として残しているので、ここで両者を区別する理由が無い。

   `lbrace` は 3 つに分けた `{` を再び 1 つに束ねる。
   分割は式の位置の `{}` を LR(1) で解くために必要だが、
   module の本体やレコードパターンのように**どの分類で来ても意味が同じ**場所では、束ねて受ける。
   第2章は `{` を見た目で分類し、意味では分類しない。
   たとえば `run h {}` の `{}` は、中身が空なので `LBRACE_RECORD` に分類される。

   `long_id` は型の位置とパターンの位置で使うパスである。
   式の位置では、`perform` の直後の操作名(`perform_op`)を除いて使わない(§3.4)。
   `perform_op` は後置の選択と競合しないので、§3.4 の conflict は起きない。 *)

%inline semi: NL { () } | SEMI { () }

%inline lbrace:
  | LBRACE_BLOCK  { () }
  | LBRACE_RECORD { () }
  | LBRACE_TYPE   { () }

lower_id: LOWER_IDENTIFIER { $1 }
upper_id: UPPER_IDENTIFIER { $1 }

upper_path:
  | upper_id                { [ $1 ] }
  | upper_path DOT upper_id { $1 @ [ $3 ] }
long_id:
  | lower_id                { LongId [ $1 ] }
  | upper_path              { LongId $1 }
  | upper_path DOT lower_id { LongId ($1 @ [ $3 ]) }

(* ## 3.15 プログラムと宣言

   トップレベル、module の本体、`instance` の本体、ブロックは、同じ `items` 非終端で読む。
   文法を 4 種類に分けると、同じ規則を 4 回書いたうえに、
   4 通りの conflict に対処することになるからである。
   そのため、文脈の違反は原則として第11章(elab.ml)が検査する。
   ただし、ブロックの中に `module` を書いたときのように、ブロックの中で式に落とせない宣言は、
   §3.7 の `block_of_items` が構文エラーにする。

   `items` は余分な `semi` を読み飛ばす。
   ASI が改行を落とすかどうかの判断は完全ではないので、ここは寛容にしておくのが実際的である。

   `with` の規則を `items` に置くのは、
   この糖衣が「残りの文すべて」を継続の本体に取るからである(§3.8)。
   左再帰では書けないので、`WITH pat EQ exp semi items` と右再帰で受け、
   `items` の解析結果をそのまま `block_of_items` に通す。
   規則が 2 本あるのは、`with` がファイルやブロックの末尾に来た場合を 1 本目で受けるためで、
   このとき継続の本体は空レコード(Unit)になる。

   `pub` は `decl` の階層で被せる(§3.10)。
   `decl_body` の中で、`let rec` の `and` の前に `semi` を挟んでいないのは意図的である。
   ASI が `and` の前の改行を落とすので、そのまま並べるだけで足りる。
   `semi?` を足すと shift/reduce になる。 *)

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
  (* ASI が AND の前の NL を落とすので semi は挟まない *)
  | LET REC binding and_bindings                       { DLetRec ($3 :: $4) }
  | TYPE upper_id typarams_opt kind_annot_opt EQ ty
      { DType { ta_pub = false; ta_name = $2; ta_params = $3; ta_kind = $4; ta_body = $6 } }
  | TYPE CLASS upper_id typarams class_body
      { let vals, derives = $5 in
        DClass { cls_pub = false; cls_name = $3; cls_params = $4; cls_vals = vals; cls_derives = derives } }
  | TYPE INSTANCE typarams_opt upper_id LBRACKET ty_args RBRACKET instance_body
      { DInstance { ins_tparams = $3; ins_class = $4; ins_args = $6; ins_body = $8 } }
  | NEWTYPE upper_id typarams_opt newtype_rhs
      { let rhs =
          match $4 with
          | RhsNone -> NtCtors []
          | RhsHole -> NtHole
          | RhsCtors cs -> NtCtors cs
          (* newtype UserId(Int32) は newtype UserId = UserId(Int32) の略記 *)
          | RhsShort fields -> NtCtors [ { cd_name = $2; cd_fields = fields } ]
        in
        DNewtype { nt_pub = false; nt_name = $2; nt_params = $3; nt_rhs = rhs } }
  | EFFECT upper_id typarams_opt EQ eff_decl_body
      { DEffect { ef_pub = false; ef_name = $2; ef_params = $3; ef_ops = $5 } }
  | MODULE upper_id module_body                        { DModule (false, $2, $3) }
  | EXTERN TEXT LET extern_sig
      { let name, tparams, params, (ret, eff) = $4 in
        DExtern { ex_pub = false; ex_abi = $2; ex_name = name; ex_prim = name; ex_tparams = tparams;
                  ex_params = params; ex_ret = ret; ex_eff = eff } }

and_bindings:
  |                          { [] }
  | AND binding and_bindings { $2 :: $3 }

(* ## 3.16 束縛のパターンを別の言語に分ける

   `binding` には 2 つの形がある。
   関数形 `f[T](x, y): R @ E = body` と、パターン束縛形 `p: T = e` である。

   節のパターン(`pat`、§3.22)は、`case print(m)` のように**小文字**をコンストラクタの頭に許す。
   `print` が操作名なのか変数なのかはパーサには分からないので、形としては受けるしかない。
   一方、`let f(x) = e` は関数定義である。
   同じ `pat` を束縛側でも使うと、この 2 つが reduce/reduce の conflict になる。
   しかも reduce/reduce は記述順で黙って解決されるので、
   `--strict` が無ければ、ビルドは通るのに `let f(x) = e` の意味が違う文法ができてしまう(§3.13)。

   そこで文法を分ける。
   `bind_pat`(§3.22)は、`_`、変数、**大文字で始まる**コンストラクタ、レコード、タプルだけを受ける。
   小文字で始まる呼び出しの形は持たない。
   同じ「パターン」という言葉で呼ぶ 2 つのものが、置かれる位置によって別の言語になっている。

   末尾の注釈は `sig_tail` にまとめてある。
   返り値の型だけ、エフェクト行だけ、両方、どちらも書かない、の 4 通りである。
   `ty_ret` が `union_ty` と `arrow_ty` を分けて並べているのは §3.23 の矢印の分離の帰結で、
   関数自身の行を `@` で書けるのは、返り値の型を書かないときと、
   書いた返り値の型が矢印でないときである。
   矢印を返す関数では、返り値の型の後に書いた `@` は返り値の矢印に結合する。
   関数自身の行を書きたいときは、返り値の型を省いて `@` だけを書くか、
   返り値の矢印を型エイリアスにする。
   `extern` のシグネチャ(`extern_sig`)は、本体を持たない `binding` の頭で、
   同じ `sig_tail` を共有する。 *)

binding:
  | lower_id typarams_opt LPAREN params RPAREN sig_tail EQ exp
      { let ret, eff = $6 in
        mk $sloc { lb_pub = false; lb_name = mk $sloc (PVar $1); lb_tparams = $2; lb_params = Some $4;
                   lb_ret = ret; lb_eff = eff; lb_body = $8 } }
  | bind_pat annot_opt EQ exp
      { mk $sloc { lb_pub = false; lb_name = $1; lb_tparams = []; lb_params = None;
                   lb_ret = $2; lb_eff = None; lb_body = $4 } }

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

(* ## 3.17 宣言の細部

   `module_body` と `instance_body` は `items` を使い、
   `class_body` と `eff_decl_body` は専用の非終端を使う。
   前の 2 つは中身が普通の宣言の列だが、クラスの本体は `val` と `derive` しか、
   `effect` の本体は `op: ty` しか取れないからである。
   `class_items` が `Either` で 2 種類を仕分けているのは、
   1 回の走査で `cls_vals` と `cls_derives` に振り分けるためである。

   カンマ区切りのリストは、**最後の要素の後の末尾カンマを許す**。
   仕様 §0 は、カンマ区切りのリストならどの種類でも末尾カンマを置けると書いている。
   対象は引数、パラメータ、型引数、型パラメータ、レコード、タプル、パターン、エフェクト行、
   effect の操作、コンストラクタのフィールド、`F[_, _]` の穴である。
   区切りが `|` の `ctors` と、区切りが `+` の `cls_list` は、カンマ区切りではないので対象外である。
   sample.kel:590 の effect 本体や :755-758 のパラメータリストに実例がある。

   `...rest` と `extends T` は要素ではなくリストの**終端子**なので、その後にはカンマを書けない。
   `{x, ...r,}` や `{x: T extends R,}` は構文エラーになる。
   `test/trailing_comma.t` は、上のすべてのリストに末尾カンマを置けることと、
   終端子の前には置けるが後には置けないことを、ゴールデンテストで固定している。

   実装は `X | X COMMA | X COMMA list` の 3 択である。
   この形なら `(a)` と `(a,)` を意味アクションで区別でき、conflict も出ない。
   同じ手法が `pp_items` の真偽値にも出てくる(§3.22)。
   なお `[A,]` は「型引数 1 個と末尾カンマ」であって、1-タプルではない。
   角括弧は引数リストで、括弧の `(A,)`(§3.20)とは別物である。

   型パラメータの束縛子(`typaram`)は、名前、arity、クラス制約の 3 つの組である。
   `F[_]` と書いたときだけ `hkt_opt` が正の数になり、その場でカインドが `KArrow` に決まる。
   `[A]` や `[h]` のような裸の束縛子は、字句だけではカインドが決まらない。
   行変数なのか型なのかは使われ方で決まるので、第1章のカインド変数に任せる。

   `ty_ident` が大文字も小文字も受けるのは、リージョン変数 `h` を小文字で書くからである。
   仕様 §0 は識別子の大小の規則から型パラメータを外し、
   文法上は大小を問わないと書いている(sample.kel:50-51)。
   慣習では型を大文字、リージョン変数を小文字で書き、仕様 §10 の署名一覧がその例である。
   ただし、`run` が導入するリージョン変数だけは、文法上も小文字で始まる識別子に限る(sample.kel:52)。
   そのため `atom` の `run` の規則は `ty_ident` ではなく `lower_id` を取り、
   `run H` も `run _` も構文エラーになる(`test/nonfeatures.t` の case8 と case9)。

   同じ `typarams_opt` は `instance` の直後にも置け、
   前提つきのインスタンス `type instance[A: Eq] Eq[List[_]]`(仕様 §8)をこれで書く。
   `typaram` が前提のクラス制約をそのまま運べるので、前提のための新しい構文要素は要らない。
   `TYPE INSTANCE` の直後では、`[` なら shift して `typarams` へ進み、
   大文字の識別子なら空の `typarams_opt` へ reduce する。
   この 2 つは 1 トークンの先読みで分かれるので、conflict は出ない。

   `newtype_rhs` の 4 つの形は、§3.10 のとおり `nt_rhs_raw` で運ぶ。
   `params` の `param` は `pat annot_opt` で、注釈があれば `PAnnot` で包むだけである。
   その注釈に書かれた型パラメータを剛定数にするかどうかは第11章が判断する。 *)

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
typaram_list: typaram { [ $1 ] } | typaram COMMA { [ $1 ] } | typaram COMMA typaram_list { $1 :: $3 }
typaram: ty_ident hkt_opt cls_opt { { tp_name = $1; tp_arity = $2; tp_classes = $3 } }
ty_ident: lower_id { $1 } | upper_id { $1 }
hkt_opt: { 0 } | LBRACKET lowline_list RBRACKET { $2 }
lowline_list: LOWLINE { 1 } | LOWLINE COMMA { 1 } | LOWLINE COMMA lowline_list { 1 + $3 }
cls_opt: { [] } | COLON cls_list { $2 }
cls_list: upper_id { [ LongId [ $1 ] ] } | upper_id PLUS cls_list { LongId [ $1 ] :: $3 }

kind_annot_opt: { None } | COLON upper_id { Some $2 }

params: { [] } | param_list { $1 }
param_list:
  | param                  { [ $1 ] }
  | param COMMA            { [ $1 ] }
  | param COMMA param_list { $1 :: $3 }
param: pat annot_opt { match $2 with None -> $1 | Some t -> mk $sloc (PAnnot ($1, t)) }

(* ## 3.18 式の優先順位

   優先順位は非終端の階層で表し、`%left` のような優先順位の宣言は使わない。
   曖昧な文法を宣言で抑え込むと、`--strict` が何も言わなくなるからである(§3.13)。
   弱いほうから、次の順に並ぶ。

   `fn` → 後置の `match` / `handle` → `||` → `&&` → 比較 → 加減 → 乗除 → 前置 → 後置 → アトム

   後置の `match` / `handle` はどの二項演算子よりも弱いので、`x match {...} + 1` とは書けない。
   `(x match {...}) + 1` のように括弧が要る。

   比較は**非結合**である。
   `a < b < c` は文法の段階で落ちる。

   単項のマイナスは `HYPHEN NUMBER` の形でだけ受け、その場で負のリテラルに畳む。
   AST に単項マイナスの演算子は無い(sample.kel:94)。
   第2章(lexer.ml)の §2.1 が、同じ取り決めを字句の側から説明している。
   符号を字句の側で扱うと `1-2` が「1 と -2 の並置」になってしまうので、符号はパーサが扱う。
   二項の `-`(sample.kel:335 の `is_even(0 - n)` がその用例)と併存しても、conflict は出ない。 *)

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
  (* 符号はパーサが畳む。AST に単項マイナス演算子は無い *)
  | HYPHEN NUMBER          { mk $sloc (Number { $2 with n_text = "-" ^ $2.n_text }) }
  | postfix_exp            { $1 }

(* ## 3.19 後置とアトム

   後置は 3 種類ある。
   ドットによる選択(§3.4)、`\` によるフィールドの除去、呼び出し(§3.6)である。
   Keleut には**並置による適用が無い**ので、
   `f (x)` の `(` が呼び出しなのかグループ化なのかで迷う余地が無い。
   そのため、式の `(` を素直に読める。

   `atom` の `#Ident` は空のペイロードの `Variant` として作り、
   引数が付いていれば、後置の呼び出しの規則が `call` で差し替える(§3.6)。

   `resume` の引数だけは `record_of_args` を通さない。
   `resume(e)` の `e` は操作の返り値そのもので、引数リストではないからである。
   `{_item = e}` に包むと、第11章で操作の返り値の型と単一化できない。
   引数は高々 1 個で、0 個なら `Resume None` になる。
   ペイロードはラベル付きの引数行ではないので、ラベル付きの引数も拒む。
   `resume(x = e)` には、個数とは別の専用の文面を返す。
   個数についての文面を返すと、引数が 1 個の入力に「高々1個です」と出て、誤った診断になる。
   この形は、第14章(interp.ml)のアフィンな resume にそのまま対応する。

   `block` は `LBRACE_BLOCK` だけを受ける。
   しかし `run h {}` の `{}` は中身が空なので、字句の側で `LBRACE_RECORD` に分類される。
   そのため `run_body` は 3 種類を束ねた `lbrace` で受ける(§3.14)。 *)

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
      { (* 引数を record_of_args に通さない。ペイロードは操作の返り値 *)
        match $3 with
        | [] -> mk $sloc (Resume None)
        | [ (None, e) ] -> mk $sloc (Resume (Some e))
        | [ (Some _, _) ] -> raise (Syntax_error "resume の引数にラベルは付けられません")
        | _ -> raise (Syntax_error "resume の引数は高々1個です") }
  | RUN lower_id run_body                      { mk $sloc (Run ($2, $3)) }
  | block                                      { $1 }
  | record_exp                                 { $1 }
  | paren_exp                                  { $1 }

perform_op: long_id { $1 }

block: LBRACE_BLOCK items RBRACE { block_of_items $sloc $2 }
run_body: lbrace items RBRACE { block_of_items $sloc $2 }

call_args: { [] } | arg_list { $1 }
arg_list:
  | arg                { [ $1 ] }
  | arg COMMA          { [ $1 ] }
  | arg COMMA arg_list { $1 :: $3 }
arg: lower_id EQ exp { (Some $1, $3) } | exp { (None, $1) }

(* ## 3.20 レコード式と括弧

   レコード式には 5 つの形がある。
   空、`extends` だけ、フィールドの並び、並びと `extends`、そして更新 `{base with l = e}` である。
   `extends` は「残りの行をこの式から取る」という意味で、フィールドを外側から順に積み上げる。

   更新だけは `RecordUpdate` として AST に残す。
   拡張(`RecordExtend`)が同じラベルをもう 1 枚重ねるのに対し、
   更新は既にあるラベルを書き換える別の操作だからである。
   最左一致の下では、この 2 つは違う型を持つ。

   `{base with ...}` の `base` が識別子 1 個に限られるのは、字句の分類の帰結である。
   `{` の直後に来るものが分類を決める(§2.9)ので、ここに任意の式は置けない。
   基底に式を使いたいときは、`let` で束縛してから書く。
   字句層(§2.9)は識別子の大小を見ないので、
   `{P with x = 3}` のように大文字で始まる基底を書いた入力も、
   レコード更新として分類されてここへ届く。
   大文字で始まる識別子はコンストラクタであってレコードではないので、
   `record_exp` の最後の規則の意味アクションが `Syntax_error` で落とす。
   字句層に大小の区別を持ち込まないのは、§2.9 の表を 5 行のまま保つためである。

   パンニング `{a, b}` は `{a = a, b = b}` に展開する。
   式でもパターンでも同じ規則である。

   括弧には 3 つの形がある。
   `()` は空レコード(Unit)、`(e)` は**グループ化**、`(e,)` と `(e1, e2, ...)` はタプルである。
   §3.5 の表のとおり、式の位置の `(e)` を 1-タプルにしないことがここで効いている。
   一方、**型の位置の `(A)` は常に 1-タプル**である(§3.23)。
   式では括弧をグループ化に使う必要があり、型では `(A) => B` の引数リストと形を揃えたい。
   この 2 つの要求が両立しないので、同じ括弧が式と型で違う意味を持つ。 *)

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
      { (* {base with l = e}: 字句分類(§2.9)が base を識別子 1 個に絞る。
           大文字も通るので、レコードでないものはここで落とす *)
        (match $2 with
        | _, Ident (LongId [ x ]) when not (is_upper x) -> ()
        | _ -> raise (Syntax_error "レコード更新の基底は小文字始まりの識別子 1 個です"));
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
  | LPAREN exp RPAREN                { $2 } (* グループ化。タプルにしない *)
  | LPAREN exp COMMA RPAREN          { tuple_exp $sloc [ $2 ] }
  | LPAREN exp COMMA exp_list RPAREN { tuple_exp $sloc ($2 :: $4) }
exp_list:
  | exp                { [ $1 ] }
  | exp COMMA          { [ $1 ] }
  | exp COMMA exp_list { $1 :: $3 }

(* ## 3.21 節の列は空を許す

   `match` の節と `handle` の節は、同じ `clause` 非終端で読む。
   `return` や `cancel` のような節の名前も、`Console.write` のような操作名も、
   すべて `PCtor` の頭として受ける。
   どれが何なのかの分類は第11章(elab.ml)が行い、
   結果を第5章(tree.ml)の `resolved` に書く(§3.6 と同じ分担)。

   節の間に区切りを書かないのは、ASI が `case` の前の改行を落とすからである。
   `CASE` は、文を始められるトークンの集合に入っていない。

   `clauses` は空を許す。
   `n match {}` は節が 0 個の `match` である。
   これは書き間違いではない。
   `Never`(コンストラクタを持たない型)の値に対する、正しく網羅的な `match` である。
   値が存在しないので、扱うべき場合も無い。

   空を許すには、文法だけでなく第10章(exhaust.ml)の網羅性検査も対応していなければならない。
   Maranget の完全判定は、ふつう「コンストラクタの根が空でないこと」を条件に含める。
   しかしこの条件のままでは、`Never` に対する節が 0 個の `match` を誤って「非網羅」と判定してしまう。
   第10章の `sig_complete` は、シグネチャが空だと分かっているなら、
   根が空でも網羅と判定する(§10.10)。 *)

clause_body: lbrace clauses RBRACE { $2 }
clauses: { [] } | clause clauses { $1 :: $2 } (* 空 = Never の節ゼロ match *)
clause: CASE pat guard_opt EQ_GREATER exp { mk $sloc { cl_pat = $2; cl_guard = $3; cl_body = $5 } }
guard_opt: { None } | IF exp { Some $2 }

(* ## 3.22 パターンの 2 つの言語

   上が節のパターン `pat`、下が束縛のパターン `bind_pat` である。
   分けた理由は §3.16 で述べたとおりで、
   小文字で始まる呼び出しの形(`case print(m)` のため)を受けるのは `pat` だけである。

   `pat` の `long_id` 単独の場合は、小文字の 1 成分なら変数、
   それ以外なら引数 0 個のコンストラクタパターンになる。
   これは §3.4 と同じ、大文字かどうかの判定である。

   レコードパターンは**開いた行が既定**である。
   `rest` が `None` のときは `record_pat` の意味アクションが尾部に `PWildcard` を置くので、
   書いていないフィールドがあっても一致する。
   `{x}` と書いたときの `{` は字句の側で `LBRACE_BLOCK` に分類されるので、
   ここも `lbrace` で 3 種類を束ねて受ける。

   タプルパターンは逆に**閉じた行**である(§3.9)。
   `(p)` はグループ化、`(p,)` は 1-タプル、`(x, ...rest)` は尾部の束縛である。
   `rp_items` と `pp_items` は、`...rest` を列の終端子として、要素の列の末尾で受ける。
   これも conflict を避けるために選んだ形である。
   `pp_items` の 3 つ目の要素(真偽値)は「カンマを見たか」を運ぶためだけにあり、
   `(p)` と `(p,)` を意味アクションで区別するのに使う(§3.17 の末尾カンマと同じ手法)。

   パターンの文法に**無い**ものが 2 つあり、どちらも実装の都合ではなく仕様 §7 の決定である。
   or パターン(`case #Even | #Odd`)は入れない。
   パターンの文法に `|` を出さなければ、必要になってから足しても既存の文法と衝突しない。
   節パターンの型注釈(`case n: Int32 =>`)も無い。
   将来入れるなら、矢印を含む型注釈は括弧が必須になる(第2章 §2.10)。
   どちらも入っていないことを、`test/nonfeatures.t` がパースエラーの位置も含めて固定している。 *)

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

(* let 束縛のパターン。小文字頭の呼び出し形を持たない(§3.16) *)
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

paren_pat: LPAREN pp_items RPAREN
  { match $2 with
    | [ p ], None, false -> p
    | pats, rest, _ -> pat_tuple $sloc pats rest }
pp_items:
  |                        { ([], None, true) }
  | DOTDOTDOT lower_id     { ([], Some (mk $sloc (PVar $2)), true) }
  | pat                    { ([ $1 ], None, false) }
  | pat COMMA pp_items     { let ps, r, _ = $3 in ($1 :: ps, r, true) }

(* ## 3.23 型式の矢印を分け、ブレースを統合する

   型の文法には、1 本の規則にまとめようとすると conflict する箇所が 2 つある。

   1 つ目は矢印である。
   括弧の型を単一の規則にして矢印もそこで扱うと、
   `(A) => B | C`、`((A) => B)[C]`、入れ子の矢印に付く `@` の 3 か所で conflict する。
   そこで `arrow_ty` を `ty` の直下に分けて置く。
   矢印はヴァリアント和の要素にも型適用の頭にもならないので、
   `(A) => B | C` は返り値が `B | C` の矢印になる。
   型の位置の括弧は 1-タプルを作るので(§3.20)、`((A) => B)[C]` は 1-タプルを頭とする型適用になる。
   `@` は**直前(最も内側)の矢印に結合する**。
   `(A) => (B) => C @ E` の `@ E` は、内側の矢印 `(B) => C` に付く。
   `arrow_ret` の矢印の場合にだけ `@` が無いのがその表れで、
   入れ子の矢印の外側に `@` を書く構文は無い。
   内側の矢印を括弧で囲むと、返り値が 1-タプルになる。
   外側に `@` を付けたいときは、内側の矢印を型エイリアスにする。

   2 つ目はブレースである。
   レコード型 `{x: Int32}` とエフェクト行 `{Print, Log}` を別の非終端にすると reduce/reduce になる。
   `{` を読んだ時点では、どちらなのか分からないからである。
   そこで `brace_ty` の 1 本に統合し、要素を 2 択とする。
   1 つは `l: T`(レコード型のフィールド)、
   もう 1 つは `Name[args]`(エフェクトのラベル、または展開される行エイリアス)である。
   **どちらの意味なのかは、第11章が要素の形から判定する**。
   このおかげで、`@ {}`、`@ {Print extends E}`、`{ReqId, Logger, Tracer}`(sample.kel:648)が、
   すべて同じ規則に乗る。
   `effect` 宣言の本体はこの規則ではなく、`op: ty` だけを受ける専用の `eff_decl_body`(§3.17)で読む。

   仕様 §0 は、`@` の直後、EffectRow のエイリアスの右辺、
   effect 宣言の本体という 3 つの文脈の `{` を、
   読み分けの表でどれに分類されてもエフェクト行(または宣言の本体)として読むと定めている(sample.kel:26-28)。
   実装は先読みを止めず、どの分類で来ても同じ木に落とす(第2章 §2.9)。
   `brace_ty` も `eff_decl_body` も `{` を `lbrace` で受けるので、分類の違いは木に残らない。
   仕様は、3 種類を同じ構文木で表して意味解析の段階で区別することを認めており、
   この位置で先読みを止める実装でも結果は同じになると書いている。
   この等価性は `test/tokens.t` の effbrace と effield が確かめている。

   型の位置の `(A)` は常に 1-タプル `{_item: A}` である(§3.20)。
   `#Foo(A, B)` は §3.5 と同じ規約で畳む。
   文法はカインドの注釈を `COLON upper_id` としか書かず、
   `Type` なのか `EffectRow` なのかの解釈は第11章に任せる。
   ここでもパーサは形しか見ない。 *)

ty: union_ty { $1 } | arrow_ty { $1 }

arrow_ty: LPAREN ty_list0 RPAREN EQ_GREATER arrow_ret
  { let ret, eff = $5 in
    mk $sloc (EArrow ($2, ret, eff)) }
arrow_ret:
  | union_ty eff_opt { ($1, $2) }
  | arrow_ty         { ($1, None) } (* 入れ子の矢印の外側には @ を書けない(型エイリアスを使う) *)
eff_opt: { None } | AT eff { Some $2 }

union_ty:
  | union_ty VERTICAL app_ty { match $1 with (_, EUnion ts) -> mk $sloc (EUnion (ts @ [ $3 ])) | t -> mk $sloc (EUnion [ t; $3 ]) }
  | app_ty                   { $1 }

app_ty:
  | atom_ty                           { $1 }
  | atom_ty LBRACKET ty_args RBRACKET { mk $sloc (EApply ($1, $3)) }

ty_args: ty_arg { [ $1 ] } | ty_arg COMMA { [ $1 ] } | ty_arg COMMA ty_args { $1 :: $3 }
ty_arg: ty { $1 } | LOWLINE { mk $sloc EHole }

atom_ty:
  | long_id                           { mk $sloc (EIdent $1) }
  | HASH_IDENT                        { mk $sloc (EVariantCase ($1, None)) }
  | HASH_IDENT LPAREN ty_list0 RPAREN
      { match $3 with
        | [] -> mk $sloc (EVariantCase ($1, None))
        | ts -> mk $sloc (EVariantCase ($1, Some (variant_ty_payload $sloc ts))) }
  | brace_ty                          { $1 }
  | LPAREN ty_list0 RPAREN            { tuple_ty $sloc $2 } (* 型位置の (A) は常に 1-タプル *)

ty_list0: { [] } | ty_list { $1 }
ty_list:
  | ty               { [ $1 ] }
  | ty COMMA         { [ $1 ] }
  | ty COMMA ty_list { $1 :: $3 }

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
