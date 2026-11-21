(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第3章 構文解析と脱糖

   第2章(lexer.ml)が渡すのは、(トークン, 開始位置, 終了位置)の三つ組の並びである。
   この並びは、ASI で区切りを補い、`{` を 3 種類に分類した後のものである。
   本章はこの並びを LR(1) で読み、第5章(tree.ml)以降が扱う小さな AST に変換する。

   このファイルが行う処理は 2 つに分かれる。

   | 処理 | 内容 | 書いてある箇所 |
   |---|---|---|
   | 構文の認識 | Keleut の表面構文を LR(1) の文法として記述する | 文法規則の並び(§3.14 以降) |
   | 脱糖 | 表面構文の糖衣構文を、AST が持つ基本の形に直す | 冒頭の補助関数群(§3.4〜§3.10) |

   本章の主題は後者である。
   Keleut の AST は、表面構文の見た目に比べて小さい。
   その差のほぼすべてを、このファイルの冒頭の補助関数が吸収する。

   パーサは、名前解決をせず、型も見ず、`case` の節が `return` 節なのか操作節なのかも決めない。
   判断に使うのは構文の形だけで、
   具体的には「識別子の先頭が大文字か」「ドットの連鎖か」「引数が何個か」の 3 つである。
   それ以外は第11章(elab.ml)が決める。

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
   ノードはすべて `(Data.t, 内容)` の対である。
   `Data.t` は 1 つのノードに付ける注釈で、`Data.allocate : Location.span -> t` がそれを作る。

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
   注釈が不要な用途なら第1章の `EmptyData` を渡せばよく、ノードの注釈は位置だけになる。
   本実装は `EmptyData` をどこでも使っておらず、例として置いてあるだけである。

   これが成り立つのは、`Syntax.Make` が**アプリカティブ**なファンクタだからである。
   OCaml では、同じファンクタに同じ引数を与えて作った `F(X).t` どうしは同じ型になる。
   パーサの中で `Syntax.Make(Data).decl` として作った値は、この性質によって、
   `Tree.Tree.decl` としてそのまま elab に渡せる。
   `Make` が生成的(ジェネレーティブ)なファンクタだったら、ここで型が合わず、
   同じ内容の木を別の型で作り直す余分な処理が必要になる。

   代償もある。
   文法を変更するたびにファンクタ越しの型検査が行われるのでビルドに時間がかかり、
   型エラーも読みにくくなる。
   割に合わなくなったら、`Data` を `ElabData` に固定して `%parameter` をやめるという選択肢がある。 *)
%parameter <Data : Syntax.Data>
%{
(* ## 3.2 dune のラッパと、空モジュール 1 個による回避策

   次の 1 行は、Keleut とも構文解析とも関係がなく、ビルドシステムの問題を回避するためのものである。

   dune はライブラリを `Diktor` という名前でラップし、
   中の各モジュールを `Diktor__Syntax` のような実名に置き換える。
   一方 menhir は、生成したパーサの型を ocamlc に推論させて `.mli` に書き出す。
   dune の menhir ルールは、この型推論を既定で行う。
   この 2 つは両立しない。
   推論に使う一時モジュールが、ライブラリ自身のラッパ名 `Diktor` を参照して壊れる。
   これが ocaml/dune#2450 である。

   この問題には、同じ名前の空モジュールを冒頭で 1 個定義し、
   その名前を局所的に隠す(シャドーイング)という回避策が知られている。
   この行が必要かどうかは、ビルドで確かめられる。
   行を消して問題が残っていれば、ビルドが失敗する。

   続く 2 つの `open` で、AST のコンストラクタと、
   意味動作が投げる `Syntax_error_at`(第1章 syntax.ml で定義)を修飾なしで書けるようにする。 *)
module Diktor = struct end

open Syntax
open Syntax.Make(Data)

(* ## 3.3 位置は三つ組で渡す

   Diktor は**全ノード**に span を持たせる。
   エラーの位置を正しく示すメッセージを出すには、全ノードに位置が必要だからである。
   一部のノードにしか位置がないと、後から位置を追加するときに、
   ノードを作るすべての箇所を書き換えることになる。

   そのために、位置はトークンの値には入れず(`%token <Location.t> LET` のような形にはせず)、
   字句解析と構文解析の間で、トークンとは別に渡す。
   menhir の伝統的な API は `(Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a` という形をしていて、
   位置を `Lexing.lexbuf` の可変フィールドから読む。
   sedlex はその lexbuf を持たない。
   そこで本章のパーサは表形式(`--table`)で生成し、第16章(driver.ml)が増分 API で動かす。
   増分 API は、トークンと開始位置と終了位置の三つ組を 1 個ずつ受け取る。
   第2章(lexer.ml)の `read` がこの三つ組を返し、第16章の `parse_program` がそれをパーサに渡す。
   字句解析と構文解析がつながるのは、この受け渡しの 1 か所だけである。

   三つ組で渡すので `$sloc` が実際の位置を返し、意味動作は `mk $sloc x` と書くだけで済む。
   位置の元になるのは、第2章が渡す三つ組だけである。
   全ノードに入れた位置は、第11章の `at_node` が型エラーに結びつけている。

   不変条件が 1 つある。
   **新しいノードは `mk` を通して作る**。
   例外は既にあるノードの位置を借りる場合だけで、しかも**借り元のノードを捨てるとき**に限る。
   本章でこれに該当するのは、`block_of_items` が宣言の位置を借りて `Let` と `LetRec` を作る箇所(§3.7)と、
   `with_splice` が引数行を差し替えるときに、
   外側の `Apply` と行ノードの位置を借りる箇所(§3.8)である。
   どちらも、借り元のノードはその場で捨てる。
   借りているのは位置だけではなく ElabData のレコードそのものなので、
   借り元のノードを捨てずに残すと、2 つのノードが型フィールドまで共有してしまう。
   §3.7 で `Seq` を例にこの問題を説明する。

   `start_of` は、ノードの始まりの位置を第1章の `Data.loc` で読む。
   `syntax_error_at` は、位置を付けた構文エラーを投げる。
   意味動作が構文の形を拒否するときは、拒否した構文の始まりを位置にする。
   menhir は規則を還元するために次のトークンを先読みするので、
   最後に読んだトークンは拒否した構文の後ろにあり、エラーの位置を指さないからである。 *)
let mk (sp, ep) x = (Data.allocate { Location.start = sp; Location.finish = ep }, x)

let start_of (d, _) = (Data.loc d).Location.start

let syntax_error_at pos msg = raise (Syntax_error_at (pos, msg))

(* ## 3.4 大文字かどうかの判定と `dot_select`

   Keleut には、モジュールのパスとフィールドの選択を書き分ける構文がない。
   `Foo.bar` が「モジュール `Foo` の `bar`」なのか「変数 `Foo` のフィールド `bar`」なのかは、
   **先頭が大文字かどうか**だけで決まる。
   この判定をするのは `is_upper` だけで、このファイルの分岐の大半がこの 1 行に依存している。

   式の位置でドットの連鎖に非終端記号 `long_id` を使うと、conflict(競合)が起きる。
   `Foo.bar` を読んだ時点で、`long_id` を伸ばすのか後置の選択として読むのかが決まらず、
   shift/reduce の conflict になる。
   型の位置とパターンの位置には conflict を起こす DOT の規則がないので `long_id` をそのまま使えるが、
   後置の選択と conflict を起こす式の位置では使えない。

   そこで文法の側は、`postfix_exp DOT id` という一様な左再帰の連鎖ですべてを読み、
   パスと選択の区別は意味動作 `dot_select` に任せる。
   規則は次の 1 つである。
   **先頭から続く大文字の要素とその直後の 1 要素をパスにまとめ、残りをレコードの選択にする。**
   `Db.Conn.exec.x` なら、`Db.Conn.exec` がパスで、`.x` が選択である。

   `t._N` は、`_item` を取り除く操作を繰り返す形に脱糖する。
   タプルは第1章のとおり `_item` を**重複させた**行で表し、
   Scoped Labels の最左一致では `t._item` が常に最初の要素を指す。
   2 番目の要素を選ぶには、最初の 1 つを取り除いてから選ぶ。
   つまり `(t \ _item)._item` である。
   一般に `t._N` は、`\ _item` を N 回適用してから `._item` を選ぶ。
   タプルの要素の選択はこの短い再帰だけで実装でき、専用の AST ノードも専用の型規則も必要ない。
   `_item` を取り除く処理は第8章(unify.ml)の `rewrite_row` にある。

   `t.0` と書くと構文エラーになる。
   `_0` は LOWER_IDENTIFIER なので選択の規則にそのまま当てはまるが、
   `0` は NUMBER なので当てはまらないからである。
   これは実装の都合ではなく、sample.kel:175 が意図した仕様である。
   `is_index_label` は名前の表記だけを見て、
   先頭が `_` で残りが 10 進の数字だけの名前を添字のラベルと判定する。 *)
let is_upper s = s <> "" && s.[0] >= 'A' && s.[0] <= 'Z'

let is_index_label s =
  String.length s >= 2 && s.[0] = '_'
  && (let ok = ref true in
      String.iteri (fun i c -> if i > 0 && not (c >= '0' && c <= '9') then ok := false) s;
      !ok)

let dot_select sloc e (id_pos, id) =
  match e with
  | (_, Ident (LongId comps)) when List.for_all is_upper comps ->
      mk sloc (Ident (LongId (comps @ [ id ])))
  | _ ->
      if is_upper id then syntax_error_at id_pos ("レコードのラベルに大文字識別子は使えません: " ^ id)
      else if is_index_label id then
        (* t._N = (t \ _item)^N ._item *)
        let n = int_of_string (String.sub id 1 (String.length id - 1)) in
        let rec strip e n = if n = 0 then e else strip (mk sloc (RecordRestriction (e, "_item"))) (n - 1) in
        mk sloc (RecordSelection (strip e n, "_item"))
      else mk sloc (RecordSelection (e, id))

(* ## 3.5 引数リストは行になる

   Keleut の関数は多引数だが、型には多引数の矢印がない。
   **引数は閉じた `_item` 行のレコード**であり、`TArrow` の第 1 引数はただのレコード型である。
   その変換が `record_of_args` で、`f(a, b)` は `Apply (f, {_item = a, _item = b})` になる。
   ラベル付きの引数 `l = e` を書いたときだけ、`_item` の代わりにそのラベルが入る。

   この表現から得られるものが 2 つある。
   1 つ目は、**引数の個数(arity)の検査がただの単一化になる**ことである。
   引数の個数が違えば、閉じた行どうしの単一化が失敗する。
   両方の行がラベル `_item` だけの閉じた行なら、
   第8章 §8.7 と第11章 §11.12 が、この失敗を引数の個数の不一致として報告し直す。
   ラベル付きの引数を含む行の失敗は、行の単一化の報告のまま残る。
   2 つ目は、`fst[A, R](t: {_item: A extends R})` のような、
   タプルの先頭の要素を取り、残りの要素の行 `R` について多相な関数を、
   同じ仕組みでそのまま書けることである。
   タプルと引数リストが同じ表現だからである。

   行を作る順序にも意味がある。
   `row` は末尾から畳み込むので、**先頭の要素が最も外側**の `RecordExtend` になる。
   第14章(interp.ml)が外側から評価すれば、引数の評価順は自然に a → b → c になる。
   評価順を別に決める必要はない。

   括弧の中身が 1 個の場合に関わる規約は 3 つあり、**3 つとも別のもの**である。

   | 書き方 | 脱糖 | 理由 |
   |---|---|---|
   | `f(a)` | `{_item = a}`(1 要素の引数行) | 引数は常に行 |
   | `(a)` | `a` そのもの(グループ化) | 括弧はグループ化。1-タプルは `(a,)` |
   | `#Foo(a)` | ペイロード `a` そのもの | 下記 |

   `#Foo(a)` を 1 要素のタプルに包まないのは、
   式 `#Syntax((l, c))` とパターン `case #Syntax(l, c)` を単一化できるようにするためである。
   両方が「ペイロードは 2 要素のタプル」という同じ形になる必要があり、片方だけ余分に包むと合わない。
   `variant_payload` の 1 引数の場合がこの規約の実装で、
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
        syntax_error_at (fst sloc) "#Foo(...) にラベル付き引数は使えません"
      else tuple_exp sloc (List.map snd args)

(* ## 3.6 `call` は先頭が大文字なら構築、小文字なら適用にする

   呼び出しの `(` を読んだ時点で、それが何であるかは 3 通りある。

   - `#Foo(...)` はヴァリアントの構築である。
     `atom` の `HASH_IDENT` が作った空のペイロードの `Variant` を、
     ここで実際のペイロードに差し替える。
     `atom` の側に引数リストを持たせると shift/reduce の conflict になるので、
     後置の呼び出しとして読む
   - `Parser.Parser(...)` は、パスの最後の要素が大文字なので `Construct` になる
   - `Parser.bind(...)` は、最後の要素が小文字なので `Apply` になる

   `call` は最後の要素だけを見て判定する。
   `Parser.Parser` と `Parser.bind` が同じパスの接頭辞を持ちながら違う意味になるのはそのためで、
   「大文字で始まる名前はコンストラクタ、
   小文字で始まる名前は値」という Keleut の名前の規約をそのまま使っている。

   `Construct` だけは引数を行にまとめず、ラベル(`ca_label`)を持たせたまま残す。
   コンストラクタのフィールドには宣言側の順序があり、
   ラベル付きの引数を、宣言したフィールドの位置に対応づけるには宣言表が必要だからである。
   対応づけは第11章(elab.ml)が行い、結果を第5章(tree.ml)の `resolved` に `RCtor` として書く。
   パーサは知らないことを推測せず、読んだ形のまま渡す。 *)
let call sloc callee args =
  match callee with
  | (_, Variant (s, (_, RecordEmpty))) -> mk sloc (Variant (s, variant_payload sloc args))
  | (_, Ident (LongId comps)) when is_upper (List.nth comps (List.length comps - 1)) ->
      mk sloc (Construct (LongId comps, List.map (fun (l, e) -> { ca_label = l; ca_exp = e }) args))
  | _ -> mk sloc (Apply (callee, record_of_args sloc args))

(* ## 3.7 `block_of_items` で宣言の並びを式にする

   `{ ... }` のブロックの内容は、トップレベルと同じ非終端記号 `items` で読む(§3.15)。
   読んだ結果は宣言の並びなので、ここで 1 つの式にまとめる。

   - 末尾の式がブロックの値になる
   - `let` は、後ろに続く残りの文すべてを本体にした `Let` になる。これで束縛のスコープが残りの文になる
   - `let rec ... and ...` は `LetRec` になる
   - 末尾以外の位置に書いた式は、残りの文をまとめた結果と合わせて `Seq` にする
   - 空のブロック `{}` は `RecordEmpty` になる。Keleut の Unit は空レコードである

   `Seq` を作るときは、残りの文をまとめた結果が `Seq es` なら、それを入れ子にせず、
   `e :: es` を要素に持つ `Seq` を作る。
   こうして、1 つのブロックに並んだ文から `Seq` の入れ子を作らないようにしている。
   平らになるのは、`block_of_items` が自分で作る `Seq` と、
   末尾の位置にある入れ子のブロックだけである。
   末尾の入れ子のブロックはそのままブロックの値になるので、
   そのブロックが作った `Seq` の先頭に前の文が追加されていく。
   非末尾の文として書いた入れ子のブロック `{ 1; { 2; 3 }; 4 }` は、入れ子の `Seq` のまま残る。
   これは `--dump-ast` で確かめられる。
   評価の意味はどちらでも同じである。

   `Let` と `LetRec` は位置を借りる(§3.3 の例外)。
   `let` 宣言自身の `d` を使うので、位置は正確である。
   借り元の宣言のノードはここで捨てるので、§3.3 で述べた共有の問題も起きない。

   `Seq` は位置を借りず、2 か所とも `mk sloc` で新しいノードを作る。
   `fst` で借りられるのは span ではなく ElabData のレコードそのものなので、
   `Seq` が中の文の式ノードから借りると、`Seq` のノードとその文のノードが型フィールドまで共有する。
   すると elab が `Seq` に書き込む型が、その文の型を上書きする。
   たとえば型検査に通るブロック `{ 1; s }` で `s` が文字列リテラルのとき、
   数値リテラル `1` の型が String になる。
   その結果、第14章の `number_value` が、数値リテラルの型が不正だという実行時エラーを起こす。
   `mk sloc` で作れば、位置はブロック全体になり、共有は起きない。

   最後の分岐は、`items` をすべての位置で共有した代償である。
   `module` や `type` はブロックの中では式にできないので、ここで構文エラーにするしかない。
   文脈の違反は elab が検査するという原則に対して、この 1 行は例外である。

   `pub` を付けた `let` と `let rec` も、ブロックの中では構文エラーにする。
   公開できるのはファイルのトップレベルの宣言だけで、ブロックの中の宣言は外から見えない。
   トップレベルの `with` より後ろの文もブロックになる(§3.8)ので、
   `with` より後ろの `pub let` もここで拒否される。
   黙って受理すると、公開したつもりの宣言が import できない理由をユーザが探すことになる。
   どちらの構文エラーも、最後の分岐と同じく、拒否した宣言の始まり(`pub` を含む)を指す。 *)
let rec block_of_items sloc items =
  match items with
  | [] -> mk sloc RecordEmpty
  | [ (_, DExp e) ] -> e
  | (_, DExp e) :: rest -> (
      match block_of_items sloc rest with
      | (_, Seq es) -> mk sloc (Seq (e :: es))
      | r -> mk sloc (Seq [ e; r ]))
  | ((_, DLet (_, b)) as b_node) :: _ when b.lb_pub ->
      syntax_error_at (start_of b_node) "ブロックの中の let には pub を付けられません(with より後ろの宣言は公開できません)"
  | ((_, DLetRec bs) as b_node) :: _ when List.exists (fun (_, b) -> b.lb_pub) bs ->
      syntax_error_at (start_of b_node) "ブロックの中の let rec には pub を付けられません(with より後ろの宣言は公開できません)"
  | (d, DLet b) :: rest -> (d, Let (b, block_of_items sloc rest))
  | (d, DLetRec bs) :: rest -> (d, LetRec (bs, block_of_items sloc rest))
  | b_node :: _ -> syntax_error_at (start_of b_node) "この宣言はブロック内では使えません(let / let rec / 式のみ)"

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
   行は末尾から畳み込んである(§3.5)ので、最も内側は最後の引数であり、継続は引数リストの末尾に付く。
   継続が最後に評価されるという評価順も、同じ理由で自然に正しくなる。

   継続の引数の個数は 2 通りある。

   - `pat` が `_` なら **0 引数**の継続 `fn() => 残り`
   - それ以外なら **1 引数**の継続 `fn(pat) => 残り`

   この分岐は、`with _ = with_file(src)`(sample.kel:621, :623)が要求する `body: () => A` と、
   `with x = Parser.bind(...)`(:636)が要求する `(A) => ...` の両方を、同じ糖衣で満たすためにある。
   `_` のときも値を捨てる 1 引数の継続にすると、前者が型検査に通らない。

   右辺が呼び出しでなければ構文エラーにする。
   継続を差し込む先の引数行がないからである。
   これは、パーサが形だけで判断できる数少ない意味上の検査の 1 つである。

   継続を引数行に差し込む処理は `append_last_arg` に切り出し、末尾ブロック(§3.19)と共有する。
   差し込む先は、どちらも引数行の最も内側である。 *)
let append_last_arg sloc (d, f, args) k =
  let rec splice (ad, a) =
    match a with
    | RecordEmpty -> (ad, RecordExtend (mk sloc RecordEmpty, "_item", k))
    | RecordExtend (rest, l, v) -> (ad, RecordExtend (splice rest, l, v))
    | _ -> syntax_error_at (fst sloc) "with: 呼び出しの引数形が不正です"
  in
  (d, Apply (f, splice args))

let with_splice sloc pat call k_body =
  let k_params = match snd pat with PWildcard -> [] | _ -> [ pat ] in
  let k = mk sloc (Lambda { l_params = k_params; l_body = k_body }) in
  match call with
  | (d, Apply (f, args)) -> append_last_arg sloc (d, f, args) k
  | _ -> syntax_error_at (start_of call) "with の右辺は関数呼び出しでなければなりません"

(* 以下は末尾ブロック(§3.19)の補助関数である。
   `trailing_call` は、`{` の位置(lbrace_pos)と、その直前のトークンの終わり(prev_end)を受け取る。
   `{ case … }` が作る照合関数の仮引数の名前 `%arg` は、`%` が識別子の文字ではないので、
   ユーザの書く名前と衝突しない。 *)
let trailing_param = "%arg"

let trailing_record pos =
  raise (Syntax_error_at (pos, "末尾ブロックの内容にレコードの形は書けません(空の {} もレコードです。何もしない関数は { () } と書きます)"))

(* 末尾ブロックの位置に書かれたが末尾ブロックにならない波括弧の、3 つの形を表す。 *)
type trailing_other = Tb_record | Tb_params of Lexing.position | Tb_annot of Lexing.position

let trailing_other pos = function
  | Tb_record -> trailing_record pos
  | Tb_params pos ->
      raise (Syntax_error_at (pos,
        "末尾ブロックの引数は小文字の識別子 1 個です(2 個以上の引数を取る関数は fn(x, y) => 式 と書いて括弧の中に渡します)"))
  | Tb_annot pos ->
      raise (Syntax_error_at (pos,
        "末尾ブロックの引数に型注釈は書けません(型注釈の必要な関数は fn(x: T) => 式 と書いて括弧の中に渡します)"))

let trailing_misplaced pos =
  raise (Syntax_error_at (pos, "コンストラクタと構造的ヴァリアントには末尾ブロックを付けられません"))

let trailing_after_paren pos =
  raise (Syntax_error_at (pos,
    "括弧で囲んだ式には末尾ブロックを付けられません(関数を括弧の中の引数として渡します)"))

let trailing_call sloc callee args (lbrace_pos, prev_end, k) =
  if lbrace_pos.Lexing.pos_lnum <> prev_end.Lexing.pos_lnum then
    raise (Syntax_error_at (lbrace_pos, "末尾ブロックの { は、呼び出しと同じ行に書きます"));
  match call sloc callee args with
  | (d, Apply (f, a)) -> append_last_arg sloc (d, f, a) k
  | _ -> raise (Syntax_error_at (lbrace_pos, "コンストラクタと構造的ヴァリアントには末尾ブロックを付けられません"))

(* ## 3.9 閉じた行と開いた行の分かれ目

   ここからの 4 つの補助関数は、タプルとヴァリアントのペイロードを行として作り、
   その行を閉じるか開くかを決める。
   この選択は第8章(unify.ml)の単一化と第10章(exhaust.ml)の網羅性検査にそのまま影響する。
   そのため、ここはパーサの中でいちばん意味論に近い箇所である。

   - `pat_tuple` の `rest_opt` が `None` なら**閉じた行**である。
     要素数が一致することを単一化が要求する。これがタプルパターンの arity 検査そのものである
   - `Some p` なら、残りの要素をパターン `p` に束縛する。`(x, ...rest)` の形である
   - レコードパターン(§3.22)は逆に**開いた行が既定**である。パターンに書いていないフィールドが値にあっても、
     照合は成功する

   タプルでは「全部で何個か」が意味を持ち、レコードでは「必要なものがあるか」が意味を持つ。
   その違いを、そのまま行の開閉で表している。

   `variant_pat_payload` と `variant_ty_payload` は、
   §3.5 の 1 引数の規約をパターン側と型側に置いたものである。
   式、パターン、型の 3 か所で引数を同じ規約でまとめているので、
   `#Syntax((l, c))` と `case #Syntax(l, c)` を単一化できる。
   `tuple_ty` が閉じた `EBraceRow` を作るのは、型の位置のタプルにも arity があるからである。 *)
let pat_tuple sloc pats rest_opt =
  (* rest_opt: None = 閉じた行(arity 検査)、Some p = 残りの要素を p に束縛する *)
  mk sloc (PRecord (List.map (fun p -> ("_item", p)) pats, rest_opt))

let variant_pat_payload sloc = function
  | [ { cap_label = None; cap_pat = p } ] -> p
  | args ->
      if List.exists (fun a -> a.cap_label <> None) args then
        syntax_error_at (fst sloc) "#Foo(...) パターンにラベル付き引数は使えません"
      else pat_tuple sloc (List.map (fun a -> a.cap_pat) args) None

let tuple_ty sloc tys = mk sloc (EBraceRow (List.map (fun t -> BField ("_item", t)) tys, None))

let variant_ty_payload sloc = function [ t ] -> t | ts -> tuple_ty sloc ts

(* 前置の - を処理する。
   オペランドが括弧で囲んでいない数値リテラルなら、負のリテラルにまとめる。
   括弧はノードを残さないので、オペランドのソース上の長さと、
   リテラルの表記(接尾辞を含む)の長さを比べて判別する。 *)
let negate sloc (sp : Lexing.position) (ep : Lexing.position) e =
  match e with
  | (_, Number n)
    when (n.n_text = "" || n.n_text.[0] <> '-')
         && ep.Lexing.pos_cnum - sp.Lexing.pos_cnum = String.length n.n_text + String.length n.n_suffix_text ->
      mk sloc (Number { n with n_text = "-" ^ n.n_text })
  | _ -> mk sloc (Neg e)

(* ## 3.10 `pub` と、`newtype` の右辺をいったん解釈前の形で受け取る理由

   `pub` は宣言の前に付く修飾子である。
   文法で「`pub` 付き」と「`pub` なし」の 2 系統を書くと宣言の規則が倍になるので、
   `decl_body` を作ってから `set_pub` で公開のフラグを立てる。
   ここで立てたフラグは第11章が読み、可視性の検査、完全注釈の検査、
   「@ を省略した pub は純粋」の検査の 3 つに使う。
   `pub` を付けられない宣言(`type instance` と式文)は、ここで構文エラーにする。

   `type instance` の本体の `let` と `let rec` にも `pub` を付けられない。
   インスタンスのメソッドは名前で import するものではなく、
   クラスのメソッドの名前を通して、インスタンスが見える範囲から使う。
   したがって `pub` は可視性を何も変えず、LangSpec §15.2 の完全注釈の要求と、
   最も外側の `@` を省略した行を `@ {}` と読む規則だけを持ち込む。
   これを黙って受理すると、公開したつもりのメソッドがなぜ import できないのかをユーザが探すことになるので、
   本体を読み終えた時点で構文エラーにする(`check_instance_body`)。
   位置は `type` の位置にし、最初に見つかった `pub` のメソッドの名前をメッセージに入れる。
   本体の後ろのトークンを読んでから投げるので、
   最後に読んだトークンは本体の後ろにあり、エラーの位置を指さないからである。

   `newtype` の右辺には 3 つの形がある。
   省略、短縮形 `newtype UserId(Int32)`、コンストラクタの並びである。
   このうち短縮形は `newtype UserId = UserId(Int32)` の略で、
   **コンストラクタの名前が型の名前と同じ**である。
   ところが、右辺を読む規則からは型の名前が見えない。
   そこで、`nt_rhs_raw` という解釈前の中間形でいったん受け取り(§3.17)、
   名前が見えている `decl_body` の意味動作(§3.15)で解釈する。
   こうすれば、短縮形のために文法を分けずに済む。 *)
let set_pub pos = function
  | DType t -> DType { t with ta_pub = true }
  | DNewtype n -> DNewtype { n with nt_pub = true }
  | DEffect e -> DEffect { e with ef_pub = true }
  | DClass c -> DClass { c with cls_pub = true }
  | DLet (d, b) -> DLet (d, { b with lb_pub = true })
  | DLetRec bs -> DLetRec (List.map (fun (d, b) -> (d, { b with lb_pub = true })) bs)
  | DModule (_, n, ds) -> DModule (true, n, ds)
  | DExtern e -> DExtern { e with ex_pub = true }
  | DInstance _ -> syntax_error_at pos "type instance に pub は付けられません"
  | DExp _ -> syntax_error_at pos "式文に pub は付けられません"

let check_instance_body pos items =
  let name_of ((_, b) : let_binding) =
    match b.lb_name with (_, PVar x) -> x | _ -> "_"
  in
  let pub_binding = function
    | (_, DLet ((_, b) as bnode)) when b.lb_pub -> Some (name_of bnode)
    | (_, DLetRec bs) -> (
        match List.find_opt (fun (_, b) -> b.lb_pub) bs with Some bnode -> Some (name_of bnode) | None -> None)
    | _ -> None
  in
  match List.find_map pub_binding items with
  | Some x ->
      syntax_error_at pos ("type instance の本体の let には pub を付けられません(メソッドはクラスを import して使います): " ^ x)
  | None -> items

type nt_rhs_raw = RhsNone | RhsShort of field_decl list | RhsCtors of ctor_decl list
%}

(* ## 3.11 トークン表

   トークンの宣言は空行で 2 つに分かれていて、前半が 47 個、後半が 21 個である。
   後半には、この言語に特有の構文のトークンが多い。
   3 種類に分類した `{`、`\`(レコードからのフィールドの除去)、
   `...`(パターンの末尾で残りの要素やフィールドを束縛する)、`???`(穴)と、
   `class`、`instance`、`extends`、`extern`、`newtype`、`perform`、`resume`、`run`、
   `pub` のキーワードがそうである。

   トークンは位置のペイロードを**持たない**(§3.3)。
   値を持つのは `BOOL`、2 種類の識別子、`TEXT`、`NUMBER`、`HASH_IDENT` の 6 種類だけで、
   ほかのトークンは値を持たず、名前だけで区別する。 *)
%token AND AT ASTERISK BIG_AMPERSAND BIG_EQ BIG_VERTICAL CASE COLON COMMA DOT
%token EFFECT EOF EQ EQ_GREATER EXCLAMATION EXCLAMATION_EQ FN GREATER HANDLE
%token HYPHEN IF LBRACKET LESS LET LOWLINE LPAREN MATCH MODULE NL PERCENT PLUS RBRACKET
%token REC RPAREN SEMI SOLIDUS TYPE VAL VERTICAL WITH
%token THEN ELSE
%token <bool> BOOL
%token <string> LOWER_IDENTIFIER UPPER_IDENTIFIER TEXT
%token <Syntax.number> NUMBER

%token LBRACE_BLOCK LBRACE_RECORD LBRACE_TYPE RBRACE
%token BACKSLASH DOTDOTDOT LESS_EQ GREATER_EQ HOLE
%token CLASS INSTANCE EXTENDS EXTERN NEWTYPE PERFORM PUB RESUME RUN
%token FROM IMPORT
%token <string> HASH_IDENT

(* ## 3.12 開始記号の型と、`Error` という名前の衝突

   開始記号の型は、import 文の並びと宣言の並びの組で、
   宣言の並びは `Syntax.Make(Data).decl list` と**完全なパスで**書く。
   menhir はこの型注釈を、生成する `.mli` のシグネチャにそのまま書き出す。
   冒頭の `open` はファンクタ本体の中でしか有効でないので、
   シグネチャに現れる型はファンクタの外から参照できるパスでなければならない。
   修飾なしの `decl list` と書くと、生成された `.mli` がコンパイルできない。

   このパスは §3.1 のアプリカティブ性とつながっている。
   生成されるのは `Parser.Make (Data)` の中の `val program : ... -> Syntax.Make(Data).decl list` である。
   ドライバが `Parser.Make (Tree.ElabData)` を呼ぶと、
   返る型は `Syntax.Make(Tree.ElabData).decl list` になる。
   これは `Tree.Tree.decl list` と同じ型である。
   木を作り直さずに elab に渡せるのは、この型の等式による。

   もう 1 つの問題は、例外の名前の衝突である。
   menhir は構文エラーを `Error` という名前の例外で投げる。
   第2章(lexer.ml)の字句エラーが同じ名前だと、ドライバの `try` がどちらを捕捉したのか区別できない。
   そのため、字句エラーは `Lex_error` という別の名前にしてある。
   第16章(driver.ml)はこの 2 つと、
   意味動作が投げる `Syntax_error_at` の 3 種類を別々に捕捉し、
   字句エラーと構文エラーを区別して報告したうえで、どちらも終了コード 2 にそろえる。 *)
%start <Syntax.import_decl list * Syntax.Make(Data).decl list> program

(* ## 3.13 `--strict` で conflict 0 を保つ

   `lib/dune` は menhir を `--explain --strict --table` で実行する。
   `--table` は、第16章が増分 API でパーサを動かす(§3.3)ために付ける。

   menhir は既定では conflict を警告にとどめ、記述順と優先順位で黙って解決する。
   conflict を放置すると、ビルドは通るのに、
   文法の意味が書いたつもりと違っている状態になることがある。
   `--strict` は警告をエラーに変え、`--explain` は conflict の説明をファイルに書き出す。
   前者がないと、ビルドが止まらないので、後者の説明を読むきっかけがない。
   `--strict` がエラーに変える警告には、宣言しただけで文法のどこにも使わないトークンも含まれる。
   そのため、§3.11 のトークンはすべて文法のどこかで使われている。

   conflict 0 は一度達成すれば終わる状態ではなく、文法を変えるたびに保ち続ける必要がある。
   conflict を 1 個でも許すには、`--strict` を外すか、優先順位の宣言で抑え込む(§3.18)ことになる。
   `--strict` を外せば、その後に増えた conflict も警告にとどまる。
   とくに reduce/reduce は記述順で黙って解決されるので、
   `let f(x) = e` が関数定義ではなく小文字のコンストラクタのパターンとして読まれる、といった誤りが、
   **テストが通ったまま**起こることがある(§3.16)。

   その代わり、文法の書き方は制約を受ける。
   本章の設計判断のうち次の 6 つは、どれもそう書かないと conflict が起きるから選んだ形である
   (6 つ目は、意味上の理由と合わせて選んだ形である)。

   - ドットの連鎖の区別を意味動作に任せる(§3.4)
   - `#Foo(...)` を後置の呼び出しとして読む(§3.6)
   - 矢印型を分離する(§3.23)
   - 束縛パターンを別の言語にする(§3.16)
   - レコード型とエフェクト行を 1 本の規則に統合する(§3.23)
   - 末尾ブロックを付けられる位置を 3 つに限る(§3.19) *)

%%

(* ## 3.14 文法の骨組み

   ここから下が文法の本体である。
   まず 3 つの小さな非終端記号を用意する。

   `semi` は改行とセミコロンを同じものとして扱う。
   ASI(第2章)が意味のある改行だけを `NL` として残しているので、ここで両者を区別する理由がない。

   `lbrace` は、字句解析が 3 種類のトークンに分けた `{` を再び 1 つにまとめる。
   3 種類に分けるのは、式の位置の `{}` を LR(1) で解析するためである。
   module の本体やレコードパターンのように**どの分類で来ても意味が同じ**位置では、
   3 種類をまとめて受理する。
   第2章は `{` を見た目で分類し、意味では分類しない。
   たとえば `run h {}` の `{}` は、内容が空なので `LBRACE_RECORD` に分類される。

   `long_id` は型の位置とパターンの位置で使うパスである。
   式の位置では、`perform` の直後の操作名(`perform_op`)を除いて使わない(§3.4)。
   `perform_op` は後置の選択と conflict を起こさないので、§3.4 の問題は生じない。 *)

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

   トップレベル、module の本体、`instance` の本体、ブロックは、同じ非終端記号 `items` で読む。
   文法を 4 種類に分けると、同じ規則を 4 回書いたうえに、
   4 通りの conflict に対処することになるからである。
   そのため、その位置に書けない宣言かどうかは、原則として第11章(elab.ml)が検査する。
   ただし、ブロックの中に書いた `module` のように、式に変換できない宣言は、
   §3.7 の `block_of_items` が構文エラーにする。
   `type instance` の本体の `pub` も、§3.10 の `check_instance_body` が構文エラーにする。

   `items` は余分な `semi` を読み飛ばす。
   ASI が改行を捨てるかどうかの判断は完全ではないので、余分な区切りはここで受理しておく。

   `with` の規則を `items` に置くのは、
   この糖衣構文が、後ろに続く文のすべてを継続の本体にするからである(§3.8)。
   左再帰では書けないので、`WITH pat EQ exp semi items` という右再帰の規則で読み、
   `items` の解析結果をそのまま `block_of_items` に渡す。
   `with` の規則は 2 本ある。
   2 本目が上の右再帰の規則で、1 本目は `with` がファイルやブロックの末尾に来た場合を読む。
   このとき継続の本体は空レコード(Unit)になる。

   `pub` は `decl` の規則で付ける(§3.10)。
   `decl_body` の中で、`let rec` の `and` の前に `semi` を置いていないのは意図的である。
   ASI が `and` の前の改行を捨てるので、`binding` と `and` をそのまま並べるだけで足りる。
   `semi?` を追加すると shift/reduce の conflict になる。

   import 文はファイルの先頭にだけ書ける。
   `items` はブロックや module の本体と共有しているので、先頭の import の並びは、
   `program` の直下に置いた別の非終端記号 `header` で読む。
   import の後ろの区切りは `semis` がまとめて読み、その後の宣言の並びは `items_head` で読む。
   `items_head` は、`items` から先頭の区切りを読む規則 `semi items` を除いたものである。
   `header` に `semi header` を追加する形では、`items` の `semi items` と同じ区切りを
   2 通りに読むことになり、reduce/reduce の conflict が出る。
   ファイルの先頭に `;` を書いた後の import は、
   `;` が `items` の `semi items` で読まれるので、構文エラーになる。
   改行だけでは先頭の区切りは生じない。
   直前のトークンがないので、字句解析が最初の改行を捨てるからである。
   import の名前に書ける `.` は 1 個まで(`M.f`)で、`D.E.f` は 2 個目の `.` で構文エラーになる。 *)

program: header EOF { $1 }

header:
  | items                          { ([], $1) }
  | import_decl                    { ([ $1 ], []) }
  | import_decl semis header_after { let is, ds = $3 in ($1 :: is, ds) }

header_after:
  | items_head                     { ([], $1) }
  | import_decl                    { ([ $1 ], []) }
  | import_decl semis header_after { let is, ds = $3 in ($1 :: is, ds) }

semis: semi { () } | semi semis { () }

items_head:
  |                            { [] }
  | item                       { [ $1 ] }
  | item semi items            { $1 :: $3 }
  | WITH pat EQ exp            { [ mk $sloc (DExp (with_splice $sloc $2 $4 (mk $sloc RecordEmpty))) ] }
  | WITH pat EQ exp semi items { [ mk $sloc (DExp (with_splice $sloc $2 $4 (block_of_items $sloc $6))) ] }

import_decl:
  | FROM TEXT IMPORT import_name
      { { im_source = $2; im_names = [ $4 ]; im_loc = { Location.start = $startpos; Location.finish = $endpos } } }
  | FROM TEXT IMPORT LBRACE_RECORD import_name_list RBRACE
      { { im_source = $2; im_names = $5; im_loc = { Location.start = $startpos; Location.finish = $endpos } } }

import_name_list:
  | import_name                        { [ $1 ] }
  | import_name COMMA                  { [ $1 ] }
  | import_name COMMA import_name_list { $1 :: $3 }

import_name:
  | import_head              { { in_path = [ $1 ]; in_loc = { Location.start = $startpos; Location.finish = $endpos } } }
  | upper_id DOT import_head { { in_path = [ $1; $3 ]; in_loc = { Location.start = $startpos; Location.finish = $endpos } } }

import_head: upper_id { $1 } | lower_id { $1 }

items:
  |                            { [] }
  | semi items                 { $2 }
  | item                       { [ $1 ] }
  | item semi items            { $1 :: $3 }
  | WITH pat EQ exp            { [ mk $sloc (DExp (with_splice $sloc $2 $4 (mk $sloc RecordEmpty))) ] }
  | WITH pat EQ exp semi items { [ mk $sloc (DExp (with_splice $sloc $2 $4 (block_of_items $sloc $6))) ] }

item: decl { $1 } | exp { mk $sloc (DExp $1) }

decl: PUB decl_body { mk $sloc (set_pub $startpos $2) } | decl_body { mk $sloc $1 }

decl_body:
  | LET binding                                        { DLet $2 }
  (* ASI が AND の前の NL を捨てるので、semi は置かない *)
  | LET REC binding and_bindings                       { DLetRec ($3 :: $4) }
  | TYPE upper_id typarams_opt kind_annot_opt EQ ty
      { DType { ta_pub = false; ta_name = $2; ta_params = $3; ta_kind = $4; ta_body = $6 } }
  | TYPE CLASS upper_id typarams class_body
      { DClass { cls_pub = false; cls_name = $3; cls_params = $4; cls_vals = $5 } }
  | TYPE INSTANCE typarams_opt upper_id LBRACKET ty_args RBRACKET instance_body
      { DInstance { ins_tparams = $3; ins_class = $4; ins_args = $6; ins_body = check_instance_body $startpos $8 } }
  | NEWTYPE upper_id typarams_opt newtype_rhs
      { let rhs =
          match $4 with
          | RhsNone -> NtCtors []
          | RhsCtors cs -> NtCtors cs
          (* newtype UserId(Int32) は newtype UserId = UserId(Int32) の略記である *)
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

   節のパターン(`pat`、§3.22)は、`case print(m)` のように、
   コンストラクタの名前の位置に**小文字**で始まる名前を書ける。
   `print` が操作名なのか変数なのかはパーサには分からないので、形だけを見て受理する。
   一方、`let f(x) = e` は関数定義である。
   同じ `pat` を束縛の側でも使うと、この 2 つが reduce/reduce の conflict になる。
   しかも reduce/reduce は記述順で黙って解決されるので、
   `--strict` がなければ、ビルドは通るのに `let f(x) = e` の意味が違う文法ができてしまう(§3.13)。

   そこで文法を分ける。
   `bind_pat`(§3.22)は、`_`、変数、**大文字で始まる**コンストラクタ、
   レコード、タプルだけを受理する。
   小文字で始まる呼び出しの形は受理しない。
   どちらもパターンと呼ぶが、節の位置と束縛の位置では別の文法で読む。

   関数形の `)` の後ろの注釈は `sig_tail` にまとめてある。
   返り値の型だけ、エフェクト行だけ、両方、どちらも書かない、の 4 通りである。
   `ty_ret` が `union_ty` と `arrow_ty` を分けて並べているのは、
   型の文法が矢印を分離している(§3.23)からである。
   関数自身のエフェクト行を `@` で書けるのは、返り値の型を書かないときと、
   返り値の型が矢印型でないか、括弧で囲んだ矢印型のときである。
   矢印を返す関数では、返り値の型の後に書いた `@` は返り値の矢印に結合する。
   関数自身のエフェクト行を書きたいときは、返り値の型を省いて `@` だけを書くか、
   返り値の型を括弧で囲む(`((B) => C) @ E`)。
   `extern` のシグネチャ(`extern_sig`)は、関数形の `binding` から `=` と本体を除いた部分で、
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
   `class_body` と `eff_decl_body` は専用の非終端記号を使う。
   前の 2 つは内容が通常の宣言の並びだが、クラスの本体には `val` しか、
   `effect` の本体には `op: ty` しか書けないからである。

   カンマ区切りのリストでは、**最後の要素の後にもカンマ(末尾カンマ)を書ける**。
   sample.kel §0 は、カンマ区切りのリストならどの種類でも末尾カンマを置けると書いている。
   対象は引数、パラメータ、型引数、型パラメータ、レコード、タプル、パターン、エフェクト行、
   effect の操作、コンストラクタのフィールド、`F[_, _]` の穴である。
   区切りが `|` の `ctors` と、区切りが `+` の `cls_list` は、カンマ区切りではないので対象外である。
   sample.kel:594 の effect 本体や :759-762 のパラメータリストに実例がある。

   `...rest` と `extends T` は要素ではなく**リストを終える構文**なので、その後にはカンマを書けない。
   `{x, ...r,}` や `{x: T extends R,}` は構文エラーになる。
   `test/trailing_comma.t` は、上のすべてのリストに末尾カンマを置けることと、
   リストを終える構文の前には置けるが後には置けないことを、ゴールデンテストで固定している。

   実装は `X | X COMMA | X COMMA list` の 3 本の規則である。
   この形なら `(a)` と `(a,)` を意味動作で区別でき、conflict も出ない。
   `pp_items` の真偽値も同じ手法を使う(§3.22)。
   なお `[A,]` は、型引数 1 個の後に末尾カンマを置いた形であって、1-タプルではない。
   角括弧は引数リストで、括弧の `(A,)`(§3.20)とは別物である。

   型パラメータの束縛子(`typaram`)は、名前、arity、クラス制約の 3 つの組である。
   `F[_]` と書いたときだけ `hkt_opt` が正の数になり、その場でカインドが `KArrow` に決まる。
   `[A]` や `[h]` のように `[_]` を付けない束縛子は、書き方だけではカインドが決まらない。
   行変数なのか型なのかは使われ方で決まるので、第1章のカインド変数に任せる。

   `ty_ident` が大文字も小文字も受理するのは、リージョン変数 `h` を小文字で書くからである。
   sample.kel §0 は識別子の大小の規則から型パラメータを外し、
   文法上は大小を問わないと書いている(sample.kel:50-51)。
   慣習では型を大文字、リージョン変数を小文字で書き、
   sample.kel §10 のシグネチャの一覧がその例である。
   ただし、`run` が導入するリージョン変数だけは、文法上も小文字で始まる識別子に限る(sample.kel:52)。
   そのため `atom` の `run` の規則は `ty_ident` ではなく `lower_id` を取り、
   `run H` も `run _` も構文エラーになる(`test/nonfeatures.t` の case8 と case9)。

   同じ `typarams_opt` は `instance` の直後にも置け、
   前提付きインスタンス `type instance[A: Eq] Eq[List[_]]`(sample.kel §8)をこれで書く。
   `typaram` が前提のクラス制約をそのまま持てるので、前提のための新しい構文要素は必要ない。
   `TYPE INSTANCE` の直後では、`[` なら shift して `typarams` へ進み、
   大文字の識別子なら空の `typarams_opt` へ reduce する。
   この 2 つは 1 トークンの先読みで分かれるので、conflict は出ない。

   `newtype_rhs` の 3 本の規則は、§3.10 のとおり、読んだ形を `nt_rhs_raw` の値で返す。
   `params` の `param` は `pat annot_opt` で、注釈があれば `PAnnot` で包むだけである。
   その注釈に書かれた型パラメータを、
   スコーレム定数(型パラメータを固定した定数。コードでは `Rigid`)にするかどうかは第11章が判断する。 *)

module_body:   lbrace items RBRACE { $2 }
instance_body: lbrace items RBRACE { $2 }

class_body: lbrace class_items RBRACE { $2 }
class_items:
  |                             { [] }
  | semi class_items            { $2 }
  | class_item                  { [ $1 ] }
  | class_item semi class_items { $1 :: $3 }
class_item:
  | VAL lower_id typarams_opt COLON ty { { cv_name = $2; cv_tparams = $3; cv_ty = $5 } }

newtype_rhs:
  |                           { RhsNone }
  | LPAREN ctor_fields RPAREN { RhsShort $2 }
  | EQ ctors                  { RhsCtors $2 }

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

   優先順位は非終端記号の階層で表し、`%left` のような優先順位の宣言は使わない。
   曖昧な文法を宣言で抑え込むと、
   `--strict` を付けても conflict が報告されなくなるからである(§3.13)。
   優先順位の低いほうから、次の順に並ぶ。

   `fn` と `if` → 後置の `match` / `handle` → `||` → `&&` → 比較 → 加減 → 乗除と `%` → 前置 → 後置 → アトム

   後置の `match` / `handle` はどの二項演算子よりも優先順位が低いので、
   `x match {...} + 1` とは書けない。
   `(x match {...}) + 1` のように括弧が必要である。

   条件式 `if e1 then e2 else e3` は、`e1 match { case true => e2 case false => e3 }` に脱糖する。
   構文木にノードを追加しないので、型(第11章)、網羅性(第10章)、評価と末尾位置(第14章)には、
   `match` の規則がそのまま適用される。
   `else` の後ろの式は、`fn` の本体と同じく右へできるだけ長く読む。
   そのため `if c then a else b + 1` は `else (b + 1)` と読み、
   `if` の結果を演算に使うときは括弧が必要である。
   `else` は省略できない。
   省略できる形を追加すると、`if a then if b then x else y` の `else` をどちらの `if` に付けるかで、
   shift/reduce の conflict が 1 個出る。

   合成する 2 つの節のパターンには、条件 `e1` の位置を付ける。
   条件が `Boolean` でないと、第11章でパターンと照合対象の単一化が失敗し、
   第11章はそのエラーをパターンの位置で報告する。
   パターンに条件の位置を付けてあるので、エラーは条件の位置を指す。

   比較は**非結合**である。
   `a < b < c` は構文エラーになる。

   前置の `-` は `HYPHEN prefix_exp` の 1 本の規則で読む。
   オペランドが括弧で囲まない数値リテラルで、まだ負でなければ、その場で負のリテラルにまとめる。
   括弧はノードを残さないので、
   オペランドのソース上の長さをリテラルの表記の長さと比べて区別する(`negate`)。
   それ以外は `Neg` のノードにし、
   第11章と第14章が `Neg.neg` の呼び出しと同じように扱う(sample.kel:94)。
   第2章(lexer.ml)の §2.1 が、同じ取り決めを字句解析の側から説明している。
   符号を字句解析で扱うと、`1-2` が 1 と -2 を並べたものになってしまうので、符号はパーサが扱う。
   二項の `-`(sample.kel:335 の `is_even(0 - n)` がその用例)と併存しても、conflict は出ない。
   `HYPHEN NUMBER` の規則を残したまま `HYPHEN prefix_exp` を追加すると、
   reduce/reduce の conflict が出る。 *)

exp:
  | FN LPAREN params RPAREN EQ_GREATER exp { mk $sloc (Lambda { l_params = $3; l_body = $6 }) }
  | IF exp THEN exp ELSE exp
      { (* Boolean に対する match に脱糖する(§3.18)。パターンの位置は条件 e1 に置く *)
        let arm b sp ep body = mk (sp, ep) { cl_pat = mk $loc($2) (PBool b); cl_guard = None; cl_body = body } in
        mk $sloc (Match ($2, [ arm true $startpos($3) $endpos($4) $4; arm false $startpos($5) $endpos($6) $6 ])) }
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
%inline mul_op: ASTERISK { Mul } | SOLIDUS { Div } | PERCENT { Rem }
prefix_exp:
  | EXCLAMATION prefix_exp { mk $sloc (Not $2) }
  (* 括弧で囲まない数値リテラルに付いた - は負のリテラルにまとめ、それ以外は Neg にする *)
  | HYPHEN prefix_exp      { negate $sloc $startpos($2) $endpos($2) $2 }
  | postfix_exp            { $1 }

(* ## 3.19 後置とアトム

   後置は 4 種類ある。
   ドットによる選択(§3.4)、`\` によるフィールドの除去、呼び出し(§3.6)、末尾ブロックである。
   Keleut には、末尾ブロックを除いて**並置による適用がない**ので、
   `f (x)` の `(` は呼び出しとしてしか読めない。
   そのため、式の `(` の文法を単純に書ける。

   末尾ブロックは、呼び出しの最後の引数を、括弧の外に波括弧 `{ }` で書いた無名関数である。
   付けられる位置は、呼び出しの `)` の直後、ドットで選択した小文字の名前の直後、
   小文字の識別子の直後の 3 つである(`tb_call`)。
   内容には次の 3 つの形を書ける。

   | 内容 | 脱糖 |
   |---|---|
   | `{ 文の列 }` | `fn() => { 文の列 }` |
   | `{ x => 文の列 }` | `fn(x) => { 文の列 }` |
   | `{ case … }` | `fn(%arg) => %arg match { case … }` |

   作った関数は `append_last_arg`(§3.8)で引数行の最も内側に追加するので、
   `with` の継続と同じく最後の引数になる。
   末尾ブロックを任意の後置式の後ろに付けられるようにはしない。
   括弧はノードを残さない(§3.20)ので、
   意味動作は `(g(1)) { k }` と `g(1) { k }` を区別できない。
   また、任意の後置式の後ろと呼び出しの後ろの両方に付ける文法は、
   shift/reduce の conflict を 1 個生む。
   呼び出しの位置でも、`call`(§3.6)が構築にする形(大文字の名前や `#Tag` の呼び出し)に
   末尾ブロックを付けると、構文エラーにする。
   引数リストのない大文字の名前、`M.Foo`、`#Tag` と、括弧で囲んだ式の直後の `{` は、
   `tb_call` の診断用の規則が読む。
   これらの規則は `tb_brace` で `{` の 1 トークンだけを読み、内容を読まずに構文エラーにする。
   ほかの位置でこれらの式の直後に `{` が続く文法はないので、規則を追加しても conflict は生じない。

   末尾ブロックの位置の `{` も、字句解析が 3 種類に分類する(第2章 §2.9)。
   `{ x: T => … }` は `LBRACE_TYPE` に、`{ x, y => … }` は `LBRACE_RECORD` に分類されるので、
   `trailing_block` の規則では読めない。
   この 2 つとレコードの形は `trailing_other` が読み、型注釈、引数の誤り、
   レコードの形のどれかを返す。
   `tb_call` の規則が、返った値に応じて診断を出す。
   `{ (a, b) => … }` は `LBRACE_BLOCK` に分類されるので、`lambda_block` の規則が読む。
   この規則は `=>` まで読んだところで構文エラーにし、本体を読まない。

   末尾ブロックの `{` は直前のトークンと同じ行に書く。
   トップレベルとブロックの中では、改行が先に文を区切る(§2.10)ので、
   次の行の `{` は末尾ブロックとして読まれない。
   丸括弧、レコード、`case` のガードの中では改行が捨てられるので、
   `{` の位置の行を直前のトークンの行と比べて検査する。
   `{ x => … }` と `{ case … }` は単独では式にならないので、`lambda_block` を `atom` にも置き、
   末尾ブロックの位置以外に現れたときに専用の診断を出す。
   `{ 文の列 }` は単独でも正しいブロックなので、次の行に書くと独立した式文になる。

   末尾ブロックの診断は、`Syntax_error_at` で誤りのある `{` の位置を報告する。
   引数の誤り(`_`、括弧で囲んだパターン、型注釈、2 個以上の引数)では、引数の先頭を報告する。
   レコードの形と `{ _ =>` の診断は `}` の後ろのトークンを読んでから出るので、
   最後に読んだトークンの位置は誤りの位置を指さない。
   `tb_brace` は `{` を、`LBRACE_TYPE` の規則は名前を、
   `lambda_block` の括弧の規則と `LBRACE_RECORD` の規則は `=>` を読んだところで診断を出す。
   `LBRACE_RECORD` の規則は、2 個以上の名前だけを並べた形を引数の誤りと判定し、
   `{ x = 1 =>` や `{ x, =>` のようなそれ以外のフィールドの並びをレコードの形と判定する。

   `atom` の `#Ident` は空のペイロードの `Variant` として作り、
   引数が付いていれば、後置の呼び出しの規則が `call` で差し替える(§3.6)。

   `resume` の引数だけは `record_of_args` を通さない。
   `resume(e)` の `e` は操作の返り値そのもので、引数リストではないからである。
   `{_item = e}` に包むと、第11章で操作の返り値の型と単一化できない。
   引数は高々 1 個で、0 個なら `Resume None` になる。
   ペイロードはラベル付きの引数行ではないので、ラベル付きの引数も拒否する。
   `resume(x = e)` には、個数とは別の専用のメッセージを出す。
   個数についてのメッセージ `resume の引数は高々1個です` を出すと、
   引数が 1 個の入力に対して誤った診断になるからである。
   この形は、第14章(interp.ml)のアフィンな resume にそのまま対応する。

   `block` は `LBRACE_BLOCK` だけを受理する。
   しかし `run h {}` の `{}` は内容が空なので、字句解析が `LBRACE_RECORD` に分類する。
   そのため `run_body` は、3 種類をまとめた `lbrace` で読む(§3.14)。 *)

postfix_exp:
  | postfix_exp DOT lower_id            { dot_select $sloc $1 ($startpos($3), $3) }
  | postfix_exp DOT upper_id            { dot_select $sloc $1 ($startpos($3), $3) }
  | postfix_exp BACKSLASH lower_id      { mk $sloc (RecordRestriction ($1, $3)) }
  | postfix_exp LPAREN call_args RPAREN { call $sloc $1 $3 }
  | tb_call                             { $1 }
  | atom                                { $1 }

tb_call:
  | postfix_exp LPAREN call_args RPAREN trailing_block
      { trailing_call $sloc $1 $3 ($startpos($5), $endpos($4), $5) }
  | postfix_exp DOT lower_id trailing_block
      { trailing_call $sloc (dot_select $sloc $1 ($startpos($3), $3)) [] ($startpos($4), $endpos($3), $4) }
  | lower_id trailing_block
      { trailing_call $sloc (mk $loc($1) (Ident (LongId [ $1 ]))) [] ($startpos($2), $endpos($1), $2) }
  | postfix_exp LPAREN call_args RPAREN trailing_other { trailing_other $startpos($5) $5 }
  | postfix_exp DOT lower_id trailing_other            { trailing_other $startpos($4) $4 }
  | lower_id trailing_other                            { trailing_other $startpos($2) $2 }
  | tb_call trailing_block
      { raise (Syntax_error_at ($startpos($2), "末尾ブロックは 1 つの呼び出しに 1 個までです")) }
  | tb_call trailing_other
      { raise (Syntax_error_at ($startpos($2), "末尾ブロックは 1 つの呼び出しに 1 個までです")) }
  | upper_id tb_brace                                  { trailing_misplaced $startpos($2) }
  | postfix_exp DOT upper_id tb_brace                  { trailing_misplaced $startpos($4) }
  | HASH_IDENT tb_brace                                { trailing_misplaced $startpos($2) }
  | paren_exp tb_brace                                 { trailing_after_paren $startpos($2) }

trailing_other:
  | record_exp                          { Tb_record }
  | LBRACE_RECORD field_list EQ_GREATER
      { let punned (l, e) = match e with _, Ident (LongId [ x ]) -> x = l | _ -> false in
        if List.length $2 >= 2 && List.for_all punned $2 then Tb_params $startpos($2) else Tb_record }
  | LBRACE_TYPE lower_id                { Tb_annot $startpos($2) }
  | LBRACE_TYPE upper_id                { Tb_annot $startpos($2) }

tb_brace: LBRACE_BLOCK {} | LBRACE_RECORD {} | LBRACE_TYPE {}

trailing_block:
  | block                         { mk $sloc (Lambda { l_params = []; l_body = $1 }) }
  | lambda_block                  { $1 }

lambda_block:
  | LBRACE_BLOCK lower_id EQ_GREATER items RBRACE
      { mk $sloc (Lambda { l_params = [ mk $loc($2) (PVar $2) ]; l_body = block_of_items $loc($4) $4 }) }
  | LBRACE_BLOCK LOWLINE EQ_GREATER items RBRACE
      { raise (Syntax_error_at ($startpos($2),
          "末尾ブロックの引数に _ は書けません(引数なしは { 式 }、引数を捨てる 1 引数は { case _ => 式 })")) }
  | LBRACE_BLOCK paren_exp EQ_GREATER
      { raise (Syntax_error_at ($startpos($2),
          "末尾ブロックの引数は小文字の識別子 1 個です(引数のない関数は { 式 }、タプルを分解する関数は { case (a, b) => 式 } と書きます)")) }
  | LBRACE_BLOCK clause clauses RBRACE
      { let v = mk $sloc (Ident (LongId [ trailing_param ])) in
        mk $sloc (Lambda { l_params = [ mk $sloc (PVar trailing_param) ];
                           l_body = mk $sloc (Match (v, $2 :: $3)) }) }

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
      { (* 引数を record_of_args に通さない。ペイロードは操作の返り値である *)
        match $3 with
        | [] -> mk $sloc (Resume None)
        | [ (None, e) ] -> mk $sloc (Resume (Some e))
        | [ (Some _, _) ] -> syntax_error_at $startpos "resume の引数にラベルは付けられません"
        | _ -> syntax_error_at $startpos "resume の引数は高々1個です" }
  | PERFORM perform_op LPAREN call_args RPAREN trailing_block
      { raise (Syntax_error_at ($startpos($6), "perform には末尾ブロックを付けられません")) }
  | RESUME LPAREN call_args RPAREN trailing_block
      { raise (Syntax_error_at ($startpos($5), "resume には末尾ブロックを付けられません")) }
  | RUN lower_id run_body                      { mk $sloc (Run ($2, $3)) }
  | block                                      { $1 }
  | lambda_block
      { raise (Syntax_error_at ($startpos,
          "{ x => ... } と { case ... } は末尾ブロックとしてだけ書けます(呼び出しの直後の同じ行に置くか、fn(x) => ... と書きます)")) }
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
   `extends` は、残りの行をその後ろの式から取ることを表す。
   フィールドは、先頭のものが最も外側になるように `RecordExtend` で重ねる。

   更新だけは `RecordUpdate` として AST に残す。
   拡張(`RecordExtend`)は同じラベルのフィールドをもう 1 個外側に重ねるのに対し、
   更新はすでにあるラベルのフィールドを書き換える別の操作だからである。
   同じラベルのフィールドは最も左のものが選ばれる(最左一致、第8章 §8.6)ので、
   この 2 つは違う型を持つ。

   `{base with ...}` の `base` が識別子 1 個に限られるのは、字句解析の分類の結果である。
   `{` の直後に来るものが分類を決める(§2.9)ので、ここに任意の式は置けない。
   更新元のレコードに式を使いたいときは、`let` で束縛してから書く。
   `{` の分類(§2.9)は識別子の大文字と小文字を区別しないので、
   `{P with x = 3}` のように大文字で始まる名前を更新元に書いた入力も、
   レコード更新として分類され、`record_exp` の最後の規則で読まれる。
   大文字で始まる識別子はコンストラクタであってレコードではないので、
   この規則の意味動作が、更新元の位置を付けた構文エラーにする。
   分類の表で大文字と小文字を区別しないのは、§2.9 の表を 5 行のまま保つためである。

   フィールドの省略記法(punning) `{a, b}` は `{a = a, b = b}` に展開する。
   式でもパターンでも同じ規則である。

   括弧には 3 つの形がある。
   `()` は空レコード(Unit)、`(e)` は**グループ化**、`(e,)` と `(e1, e2, ...)` はタプルである。
   §3.5 の表のとおり、式の位置の `(e)` は 1-タプルにしない。
   型の位置のカンマのない `(A)` も同じくグループ化で、1-タプルは `(A,)` と書く(§3.23)。
   矢印の引数リスト `(A) => B` とは、`)` の後ろに `=>` が続くかどうかで区別する。
   式、パターン、型の 3 つで、括弧の読み方は同じである。 *)

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
      { (* {base with l = e}: 字句解析の分類(§2.9)が base を識別子 1 個に限る。
           大文字で始まる識別子も来るので、レコードでないものはここで構文エラーにする *)
        (match $2 with
        | _, Ident (LongId [ x ]) when not (is_upper x) -> ()
        | _ -> syntax_error_at $startpos($2) "更新元のレコードは小文字始まりの識別子 1 個です");
        List.fold_left (fun acc (l, v) -> mk $sloc (RecordUpdate (acc, l, v))) $2 $4 }
field_list:
  | field                  { [ $1 ] }
  | field COMMA            { [ $1 ] }
  | field COMMA field_list { $1 :: $3 }
field:
  | lower_id EQ exp { ($1, $3) }
  | lower_id        { ($1, mk $sloc (Ident (LongId [ $1 ]))) } (* 省略記法 {a, b} = {a = a, b = b} *)

paren_exp:
  | LPAREN RPAREN                    { mk $sloc RecordEmpty }
  | LPAREN exp RPAREN                { $2 } (* グループ化。タプルにしない *)
  | LPAREN exp COMMA RPAREN          { tuple_exp $sloc [ $2 ] }
  | LPAREN exp COMMA exp_list RPAREN { tuple_exp $sloc ($2 :: $4) }
exp_list:
  | exp                { [ $1 ] }
  | exp COMMA          { [ $1 ] }
  | exp COMMA exp_list { $1 :: $3 }

(* ## 3.21 節の並びは空でもよい

   `match` の節と `handle` の節は、同じ非終端記号 `clause` で読む。
   `return` や `cancel` のような節の名前も、`Console.write` のような操作名も、
   すべて `PCtor` の名前として読む。
   どれが何なのかの分類は第11章(elab.ml)が行い、
   結果を第5章(tree.ml)の `resolved` に書く(§3.6 と同じ分担)。

   節の間に区切りを書かないのは、ASI が `case` の前の改行を捨てるからである。
   `CASE` は、文を始められるトークンの集合に入っていない。

   `clauses` は空を許す。
   `n match {}` は節が 0 個の `match` である。
   これは書き間違いではない。
   `Never`(コンストラクタを持たない型)の値に対する、正しく網羅的な `match` である。
   値が存在しないので、扱うべき場合もない。

   空を許すには、文法だけでなく第10章(exhaust.ml)の網羅性検査も対応していなければならない。
   Maranget の方法では、通常、シグネチャが完全かどうかの条件に
   「先頭の列に現れるコンストラクタの集合(`roots`)が空でないこと」を加える。
   しかしこの条件を加えると、`Never` に対する節が 0 個の `match` を誤って網羅漏れ(診断では `非網羅的`)と判定してしまう。
   第10章の `sig_complete` は、コンストラクタが 0 個のシグネチャを先に判定し、
   `roots` が空でも完全と判定する(§10.10)。 *)

clause_body: lbrace clauses RBRACE { $2 }
clauses: { [] } | clause clauses { $1 :: $2 } (* 空は、Never に対する節が 0 個の match である *)
clause: CASE pat guard_opt EQ_GREATER exp { mk $sloc { cl_pat = $2; cl_guard = $3; cl_body = $5 } }
guard_opt: { None } | IF exp { Some $2 }

(* ## 3.22 パターンの 2 つの言語

   上が節のパターン `pat`、下が束縛のパターン `bind_pat` である。
   分けた理由は §3.16 で述べたとおりで、
   小文字で始まる呼び出しの形(`case print(m)` のため)を受理するのは `pat` だけである。

   `pat` の `long_id` 単独の場合は、小文字で始まる 1 要素の名前なら変数、
   それ以外なら引数 0 個のコンストラクタパターンになる。
   これは §3.4 と同じ、大文字かどうかの判定である。

   レコードパターンは**開いた行が既定**である。
   `rest` が `None` のときは `record_pat` の意味動作がパターンの末尾に `PWildcard` を置くので、
   書いていないフィールドがあっても一致する。
   `{x}` と書いたときの `{` は字句解析が `LBRACE_BLOCK` に分類するので、
   ここも 3 種類をまとめた `lbrace` で読む。

   タプルパターンは逆に**閉じた行**である(§3.9)。
   `(p)` はグループ化、`(p,)` は 1-タプル、`(x, ...rest)` は残りの要素の束縛である。
   `rp_items` と `pp_items` は、`...rest` をリストを終える構文として、要素の並びの末尾で読む。
   これも conflict を避けるために選んだ形である。
   `pp_items` が返す 3 つ目の値(真偽値)は、カンマを読んだかどうかを伝えるためだけにあり、
   `(p)` と `(p,)` を意味動作で区別するのに使う(§3.17 の末尾カンマと同じ手法)。

   パターンの文法に**ない**ものが 2 つあり、どちらも実装の都合ではなく sample.kel §7 の決定である。
   or パターン(`case #Even | #Odd`)は入れない。
   パターンの文法で `|` を使わずにおけば、
   必要になってから or パターンを追加しても、既存のパターンの読み方は変わらない。
   節のパターンの型注釈(`case n: Int32 =>`)もない。
   入れる場合は、矢印を含む型注釈を括弧で囲む必要がある(第2章 §2.10)。
   どちらも入っていないことを、`test/nonfeatures.t` が構文エラーの位置も含めて固定している。 *)

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

(* let 束縛のパターン。小文字で始まる呼び出しの形は受理しない(§3.16) *)
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
  | lower_id        { ($1, mk $sloc (PVar $1)) } (* 省略記法 *)

paren_pat: LPAREN pp_items RPAREN
  { match $2 with
    | [ p ], None, false -> p
    | pats, rest, _ -> pat_tuple $sloc pats rest }
pp_items:
  |                        { ([], None, true) }
  | DOTDOTDOT lower_id     { ([], Some (mk $sloc (PVar $2)), true) }
  | pat                    { ([ $1 ], None, false) }
  | pat COMMA pp_items     { let ps, r, _ = $3 in ($1 :: ps, r, true) }

(* ## 3.23 型の式の矢印を分け、波括弧を統合する

   型の文法には、1 本の規則にまとめようとすると conflict が起きる箇所が 2 つある。

   1 つ目は矢印である。
   括弧の型を単一の規則にして矢印もそこで扱うと、
   `(A) => B | C`、`((A) => B)[C]`、入れ子の矢印に付く `@` の 3 か所で conflict が起きる。
   そこで `arrow_ty` を `ty` の直下に分けて置く。
   括弧で囲まない矢印は、ヴァリアント型の要素にも型適用の先頭にもならないので、
   `(A) => B | C` は返り値が `B | C` の矢印になる。
   カンマのない括弧の型はグループ化なので(§3.20)、`((A) => B)[C]` は矢印を先頭に置いた型適用になり、
   第11章が `型適用の先頭は型名でなければなりません` と診断する。
   `@` は**直前(最も内側)の矢印に結合する**。
   `(A) => (B) => C @ E` の `@ E` は、内側の矢印 `(B) => C` に付く。
   `arrow_ret` の規則のうち、返り値が矢印の規則にだけ `@` がないのはそのためである。
   外側に `@` を付けたいときは、内側の矢印を括弧で囲んで `(A) => ((B) => C) @ E` と書く。
   括弧の中の矢印は `atom_ty` として読まれ、その後ろの `@` は外側の矢印に付く。

   2 つ目は波括弧である。
   レコード型 `{x: Int32}` とエフェクト行 `{Print, Log}` を別の非終端記号にすると reduce/reduce の conflict になる。
   `{` を読んだ時点では、どちらなのか分からないからである。
   そこで `brace_ty` の 1 本に統合し、要素には 2 つの形を書けるようにする。
   1 つは `l: T`(レコード型のフィールド)、
   もう 1 つは `Name[args]`(エフェクトのラベル、または展開される行エイリアス)である。
   **どちらの意味なのかは、第11章が要素の形から判定する**。
   そのため、`@ {}`、`@ {Print extends E}`、`{ReqId, Logger, Tracer}`(sample.kel:652)を、
   すべて同じ規則で読める。
   `effect` 宣言の本体はこの規則ではなく、
   `op: ty` だけを受理する専用の `eff_decl_body`(§3.17)で読む。

   sample.kel §0 は、`@` の直後、EffectRow のエイリアスの右辺、
   effect 宣言の本体という 3 つの位置の `{` を、
   判別の表でどれに分類されてもエフェクト行(または宣言の本体)として読むと定めている(sample.kel:26-28)。
   実装はこれらの位置でも先読みによる分類を止めず、どの分類で来ても同じ木にする(第2章 §2.9)。
   `brace_ty` も `eff_decl_body` も `{` を `lbrace` で読むので、分類の違いは木に残らない。
   仕様は、3 種類を同じ構文木で表して意味解析の段階で区別することを認めており、
   この位置で先読みを止める実装でも結果は同じになると書いている。
   この等価性は `test/tokens.t` の effbrace と effield が確かめている。

   型の位置のカンマのない `(A)` はグループ化で、1-タプル `{_item: A}` は `(A,)` と書く(§3.20)。
   括弧の中の並びは `paren_ty_items` が読み、カンマを書いたか空かを真偽値で返す。
   `#Foo(A, B)` の引数は、§3.5 と同じ規約でペイロードにまとめる。
   文法はカインドの注釈を `COLON upper_id` としか書かず、
   `Type` なのか `EffectRow` なのかの解釈は第11章に任せる。
   ここでもパーサは形しか見ない。 *)

ty: union_ty { $1 } | arrow_ty { $1 }

arrow_ty: LPAREN paren_ty_items RPAREN EQ_GREATER arrow_ret
  { let ret, eff = $5 in
    mk $sloc (EArrow (fst $2, ret, eff)) }
arrow_ret:
  | union_ty eff_opt { ($1, $2) }
  | arrow_ty         { ($1, None) } (* 外側の矢印に @ を書くときは、内側の矢印を括弧で囲む *)
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
  | LPAREN paren_ty_items RPAREN
      { (* カンマのない (A) はグループ化、(A,) と () と 2 要素以上はタプルである *)
        match $2 with [ t ], false -> t | tys, _ -> tuple_ty $sloc tys }

ty_list0: { [] } | ty_list { $1 }
(* 括弧の中の型の並び。第 2 要素は、カンマを書いたか空のときに真になる。
   矢印の引数リストと括弧の型の両方をこの規則で読むので、) を読むまで両者を区別しなくてよい *)
paren_ty_items:
  |                  { ([], true) }
  | ty               { ([ $1 ], false) }
  | ty COMMA         { ([ $1 ], true) }
  | ty COMMA ty_list { ($1 :: $3, true) }
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
