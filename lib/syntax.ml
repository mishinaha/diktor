(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第1章 型・カインド・行・AST

   本章は、実装全体で使う語彙を定める。
   以降の章はすべて、本章で定義する `Type.ty` と AST を使う。
   実装を読むときは本章から始め、型や AST の定義を確かめたいときも本章に戻る。

   本章は前の章から何も受け取らない。
   後の章へ渡すものは次の 2 つである。

   - `Type` モジュール：型の表現である。
     第8章(unify.ml)が破壊的に書き換え、第9章(show.ml)が表示し、第11章(elab.ml)が組み立てる。
   - `Syntax.Make` が作る AST：第3章(parser.mly)が組み立て、
     第5章(tree.ml)が精緻化の結果を書き込むフィールドを付け、第4章(dump.ml)が表示する。

   ## 実装の構成

   Diktor は、言語機能が必要とする情報を 1 つの仕組みにまとめず、
   情報の性質に合った 3 つの仕組みに分けて持つ。
   こうすると、実装の量が少なくて済む。
   3 つの仕組みは次のとおりである。

   | 仕組み | 表す情報 | 決まり方 |
   |---|---|---|
   | **レベル**(`vlevel`) | 一般化してよいかどうか、`run` のスコープの内か外か | 静的に、整数の比較 1 回で決まる |
   | **行**(row) | レコード、タプル、ヴァリアント、エフェクト | 動的に、最も内側のハンドラで決まる |
   | **型変数に付けた制約の集合**(`vcls`) | クラス制約と予約述語 | 型から決まり、プログラムのどの位置でも同じになる |

   言語機能と、それを実装する仕組みの対応は次のとおりである。
   左の列が Keleut の仕様(`../doc/sample.kel`)の機能、右の列が本実装での実現方法である。

   | 言語機能 | 実装に使う仕組み |
   |---|---|
   | HM 多相・let 一般化 | 型変数の `vlevel` |
   | ランク 1 多相 | 量化子を型に持たず、型変数の状態 `Generic` で表す |
   | 値制限 | 一般化するかどうかを構文で決め、一般化しない束縛ではレベルを下げる(第11章) |
   | レコード・タプル | 行と Scoped Labels。タプルは `_item` ラベルの行 |
   | 多引数関数 | `TArrow` の 1 番目の要素が、閉じた `_item` の行 |
   | 構造的ヴァリアント | `TVariant`。内容は行 1 個 |
   | 名目的データ | `TCon` と宣言表(第6章)。型に宣言を埋め込まない |
   | エフェクト | 同じ行を `TArrow` の 3 番目の要素に置く |
   | `run h` のスコープ安全性 | スコーレム定数 `Rigid` とレベル。ランク 2 多相は使わない |
   | 型クラス | `vcls` と辞書渡し。渡す証拠は型検査が組み立てる(第8章 §8.11、第14章 §14.6) |
   | 高階カインド | コンストラクタ `TApp` を 1 つ追加するだけで扱う。型レベルのλは持たない |
   | カインド推論 | `KVar`、`same_kind`、残ったカインド変数の既定化(時期は §1.6) |
   | 網羅性検査 | Maranget の usefulness(第10章) |
   | エフェクトの実行 | OCaml 5 の `Effect.Deep`(第14章) |

   多パラメータ型クラスは持たない。
   Keleut の仕様が明示的に除外しており(sample.kel:356)、
   そのおかげで型スキーム専用のデータ型を 1 つも持たずに済む。
   量化は型変数の状態 `Generic` だけで表せる。

   ## パイプライン

   ソースから実行結果までは、次の 4 つの段階に分かれる。

   ```
   ソース ─字句─▶ トークン列 ─構文─▶ AST ─精緻化─▶ 型付き木 ─評価─▶ 値
   ```

   - **字句**(第2章 lexer.ml)：3 つの層で文字をトークンにする。
     文字を生トークンに変える層、`{` をブロック、レコード、レコード型のどれかに決める層、
     ASI を行う層である。
   - **構文**(第3章 parser.mly)：Menhir で解析する。タプルや `t._0` はここで脱糖する。
   - **精緻化**(elaboration、第5章から第11章)：型を推論しながら、
     AST のノードに型と解決結果を書き込む。
     木は作り直さない。
     書き込むフィールドは第5章の `ElabData` にある。
   - **評価**(第12章から第14章)：型付き木をたどる。
     Keleut のエフェクトは OCaml 5 のエフェクトにそのまま対応させる。

   この 4 つの段階を順に呼び出すのは第16章(driver.ml)である。
   第17章から第22章は KIR を扱う。

   ## 章の対応表

   | 章 | ファイル | 何をするか |
   |---|---|---|
   | 1 | lib/syntax.ml | 型・カインド・行・AST(本章) |
   | 2 | lib/lexer.ml | 字句解析。3 つの層に分かれる |
   | 3 | lib/parser.mly | 構文解析と脱糖 |
   | 4 | lib/dump.ml | AST の表示 |
   | 5 | lib/tree.ml | 精緻化木。型検査は木への書き込み |
   | 6 | lib/decls.ml | 宣言環境 |
   | 7 | lib/prims.ml | 演算子と組み込みエフェクトの表 |
   | 8 | lib/unify.ml | 単一化 |
   | 9 | lib/show.ml | 型の表示 |
   | 10 | lib/exhaust.ml | 網羅性検査(Maranget) |
   | 11 | lib/elab.ml | 型推論の本体 |
   | 12 | lib/value.ml | 実行時の値 |
   | 13 | lib/builtin.ml | プリミティブと組み込み実行環境 |
   | 14 | lib/interp.ml | 評価器 |
   | 15 | lib/prelude.kel | プレリュード |
   | 16 | lib/driver.ml | ドライバと終了コード規約 |
   | 17 | lib/ir.ml | KIR の型 |
   | 18 | lib/ir_write.ml | 精緻化木から KIR への書き出し |
   | 19 | lib/ir_text.ml | KIR の正準なテキスト |
   | 20 | lib/ir_bin.ml | KIR のバイナリ |
   | 21 | lib/ir_check.ml | KIR の検証 |
   | 22 | lib/ir_eval.ml | KIR の評価器 |

   本章の本体は syntax.ml の §1.1〜§1.17 である。
   補助の 2 ファイルは最後に置く。
   §1.18 が aux.ml、§1.19 が location.ml である。 *)

open Aux

(* ## 1.1 名前と修飾名

   最初に 2 つのことを決める。
   名前をどう持つかと、構文エラーをどこから投げるかである。

   `long_id` は、`Console.write` や `Parser.Result` のように、
   名前をドットで区切って並べた修飾名である。
   型とパターンの位置では、文法がそのまま作る。
   式の位置では、第3章の意味動作(`dot_select`)が、
   先頭から続く大文字の要素とその直後の 1 要素をまとめて作る。
   そのため、最後の要素を除くすべての要素が大文字で始まる、という不変条件が成り立つ。
   第3章は、要素が大文字で始まるかどうかを調べて、
   `r.x.y` のようなレコードのフィールドの選択と修飾名による参照を、同じドットの構文から判別する。

   `Syntax_error_at` はエラーの位置を持つ構文エラーで、
   Menhir の `Parser.Error` とは別の例外である。
   投げるのは、第3章の意味動作と、第16章 §16.3a のパーサのドライバである。
   意味動作が投げるのは、構文エラーではあるが、
   文法の規則で拒否しようとすると LR(1) の文法でなくなるものである。
   たとえば、レコードのラベルに大文字の識別子を書いた場合である。
   §16.3a のドライバは、予約語を識別子の位置に書いたときのエラーを投げる。
   第16章は、`Parser.Error` も `Syntax_error_at` も、終了コード 2 のエラーにする。

   エラーの位置は、投げる側が指定する。
   意味動作は、多くの場合、拒否した構文の先頭を指定する。
   §16.3a のドライバは予約語の位置を指定する。
   Menhir は規則を還元するために次のトークンを先読みする。
   そのため、意味動作が例外を投げた時点で最後に読んだトークンは、
   拒否した構文より後ろにあることがあり、その位置はエラーの箇所を指さない。
   たとえば、末尾ブロックの内容として、
   `=>` を含まないレコードの形(`{ x = 1 }` や `{}`)を書いたときの診断と、
   `{ _ =>` の診断は、`}` の後ろのトークンを読んでから出る。
   末尾ブロックでは、誤った形を受理するためだけの規則を文法に置き、
   その意味動作から投げる(第3章 §3.19)。 *)

type long_id = LongId of string list

(* import 文 1 個。im_names の各要素の in_path は [A] か [A; b] で、長さは 2 までである *)
type import_name = { in_path : string list; in_loc : Location.span }

type import_decl = { im_source : string; im_names : import_name list; im_loc : Location.span }

exception Syntax_error_at of Lexing.position * string

let long_id components = LongId components

let show_long_id (LongId components) = String.concat "." components

(* ## 1.2 名前のインターン

   ここから `Type` モジュールに入る。
   最初に名前の扱いを決める。

   単一化は内側のループで行のラベルを何度も比較するので、文字列のまま比較すると時間がかかる。
   そこで、表のキーになる名前を整数(`oid`)に置き換える。
   `intern` は同じ文字列に同じ番号を返し、`name_of` は番号から名前を引く。

   名前を番号に置き換える表(インターン表)は、名前空間ごとに分けない。
   レコードのラベル、エフェクト名、操作の完全名、型構成子、クラス名、コンストラクタ名、
   `extern` 名を、すべて同じ表に入れる。
   名前が同じなら同じ `oid` になる。
   名前空間は、番号ではなく、番号をキーにする側の表で区別する。
   第6章の `Decls.effects` にあればエフェクト名、
   `Decls.con_kinds` にあれば型構成子である。

   起点(コマンド行で渡したファイル)以外の単位、つまり import したファイルの宣言の名前は、
   先頭に単位の接頭辞 `%N.` を付けて intern する(第6章 §6.4)。
   接頭辞を付けた名前(内部名)は別の `oid` になるので、別々のファイルにある同名の型は別の型になる。
   `display` と `display_of` は接頭辞を外した名前を返し、型の表示と診断に使う。
   表を引くキーには、接頭辞の付いた `name_of` の結果を使う。

   一方、値の識別子は整数に置き換えない。
   `let` で束縛した名前も変数の参照も文字列のままで、
   型検査の環境も評価器の環境も `Map.Make (String)` を使う(第11章、第12章)。
   したがって、型検査が行う名前の比較がすべて整数の比較になるわけではない。
   整数で比較するのは、行のラベルのように `oid` で表を引く名前だけである。

   この設計では、行のラベルを `=` 1 回で比較できる。
   その代わり、`oid` だけを見ても何の名前かは分からず、
   表を引く側が名前空間を知っていなければならない。

   行のラベル専用の別名の関数は置かず、ラベルもエフェクト名も型構成子も、
   `intern` と `name_of` の 1 組で扱う。
   同じ操作に 2 つの名前があると、読者がどちらを使うべきかを判断しなければならないからである。 *)

module Type = struct
  type level = int

  let intern_map : (string, oid) Hashtbl.t = Hashtbl.create 1024

  let name_map : (oid, string) Hashtbl.t = Hashtbl.create 1024

  let intern name =
    match Hashtbl.find_opt intern_map name with
    | Some oid -> oid
    | None ->
        let ret = new_oid () in
        Hashtbl.add intern_map name ret;
        Hashtbl.add name_map ret name;
        ret

  let name_of oid = Hashtbl.find name_map oid

  (* 単位の接頭辞 %N. を外した名前を返す。接頭辞は名前の先頭にだけ付く(第6章 §6.4) *)
  let display name =
    if String.length name > 1 && name.[0] = '%' then
      match String.index_opt name '.' with
      | Some i -> String.sub name (i + 1) (String.length name - i - 1)
      | None -> name
    else name

  let display_of oid = display (name_of oid)

(* ## 1.3 カインド

   カインドは構造だけを表し、制約を持たない。
   制約をカインドに持たせる設計は、制約の付く変数のカインドが `Type` であることを前提にする。
   `Functor[F]` の `F` のカインドは `[_] Type` なので、高階カインドではこの前提が成り立たない。
   そのため、制約は §1.4 で述べるように型変数そのものに付ける。

   `KRow` は、レコード、ヴァリアント、エフェクトで分けない。
   分けると、第8章の `rewrite_row` を 3 回書くことになる。
   行のラベルが何を意味するかは、
   その行を包むノード(`TRecord`、`TVariant`、`TArrow` の 3 番目の要素)が決める。

   ### カインド変数

   カインドは `KStar` / `KArrow` / `KRow` のほかに、カインド変数 `KVar` を持つ。
   理由は Keleut の表層構文にある。

   ```keleut
   let fst[A, R](t: {_item: A extends R}): A = t._item
   let with_log[A, E](body: () => A @ {Print extends E}): A @ E = ???
   ```

   `[A]` も `[R]` も `[E]` も、束縛子の書き方は同じである。
   `R` が行だと分かるのは `extends` の右に現れるからで、
   `E` が行だと分かるのは `@` の右に現れるからである。
   つまり、カインドは使われた位置からしか決まらない。
   唯一の例外が `F[_]`(sample.kel:439)で、これだけは束縛子の書き方でカインドが決まる。
   この扱いは `let` の束縛子に限らず、newtype の型パラメータにも当てはまる。
   仕様 §6 は、型パラメータのカインドを、
   同じ型宣言のグループに属する型の本体での使われ方から推論し、
   使われ方がなければ Type とすると定めている(sample.kel:246)。
   newtype での扱いは第11章 §11.31 で述べる。

   そこで、`[_]` が書いてあればその場でカインドを `KArrow` に決め、
   書いていなければ新しい `KVar` を与えて、使われた位置から推論する。
   使われた位置から決まらずに残った `KVar` は、`KStar` に決める。
   これを既定化(defaulting)と呼ぶ(既定化の時期は §1.6 で述べる)。
   カインドの推論は、カインドの単一化と、残ったカインド変数の既定化だけで行う。
   カインド多相(PolyKinds)は扱わない。 *)

  type kind =
    | KStar
    | KRow (* レコード、ヴァリアント、エフェクトの行で共通に使う *)
    | KArrow of kind * kind (* F[_] *)
    | KVar of kind_ref (* 使われた位置から推論し、残れば KStar へ既定化する(時期は §1.6) *)

  and kind_ref = { k_id : oid; mutable k_link : kind option }

(* ## 1.4 型変数に付くもの

   `cls` は制約の集合である。
   実体は `oid list` で、重複は追加するときに取り除く。
   1 つの変数に付く制約は多くても数個なので、リストで足りる。

   このリストには予約述語も入る。
   `Integral` と `Fractional` は、整数リテラルと小数リテラルの型を決めずに保留するための述語である。
   クラス制約と同じリストに入れるので、`1 + x` の型変数が `{Integral, Add}` を持つ場合も、
   特別な処理なしで扱える。
   ただし、予約述語の扱いは、次の点でクラス制約と異なる。

   - ユーザは同名のクラスを宣言できない(第11章の `register_class` が拒否する)。
     第11章は、型パラメータの制約に書いた予約述語と、予約述語のインスタンス宣言も拒否する。
   - 第8章は、予約述語の付いた変数を一般化せず、
     既定の型に決める(`generalize` と `default_numerics`)。
   - 第8章の曖昧性検査は、予約述語の付いた変数を報告しない。

   `var_info` は、型変数の 4 つの状態(§1.5)のうち `Link` を除く 3 つが共通に持つ情報で、
   変数の番号、レベル、カインド、制約の集合からなる。
   制約をカインドではなく変数に持たせる理由は §1.3 で述べた。

   制約の付いた変数は、第8章の `class_vars`(制約つき変数の一覧)にすべて記録する。
   この一覧は、既定化(§8.9)、曖昧性検査、一般化しない束縛のレベルの引き下げが使う。
   曖昧性検査は、型スキームの型から到達できない制約を報告する(§8.9)。

   スーパークラスは持たない。
   仕様 §8 がスーパークラスを導入しないと定めており、
   第11章はクラスパラメータに書いた制約を拒否する(§11.33)。 *)

  type cls = oid list

  type var_info = { vid : oid; vlevel : level; vkind : kind; vcls : cls }

(* ## 1.5 型

   型変数は可変参照で表す。
   `TVar of tvar ref` の `ref` が Union-Find のセル、`Link` が親へのポインタで、
   §1.7 の `repr` が経路圧縮付きの find に相当する。
   ランクによる併合はしない。
   型は木なので、経路圧縮だけで `Link` の連鎖は実用上十分に短くなる。

   型変数とカインド変数のセルは、必ず §1.6 の `set_tv` と `set_klink` で書き換える。
   書き換えの記録(`trailing`)が有効な間、この 2 つの関数は、
   書き換える前の内容に戻すクロージャを `trail` に追加する。
   対話的な実行(REPL、第16章)は、型検査や実行に失敗した入力が行った書き換えを、
   この記録を使って元に戻す。
   経路圧縮も、指す先が変わるときだけセルを書き換える。
   指す先が変わらない書き換えまで記録すると、
   評価器が数値リテラルの型を引くたびに記録が伸びるからである。

   型変数の状態は次の 4 つである。

   - `Unbound i`：**単一化変数**。まだ型が決まっていない変数で、
     `i.vlevel` が一般化してよいかどうかを決める。
   - `Link t`：すでに `t` と単一化した変数。
   - `Generic i`：一般化された変数、すなわち ∀ で束縛された変数。
   - `Rigid i`：**スコーレム定数**(skolem)。型パラメータを固定した定数である。
     ほかの型に束縛されることはなく、自分より浅いレベルへ漏れてはならない。

   型には、`TForall` に相当するノードがない。
   量化は、`Generic` の変数が型のどこかにある、という形でしか表せない。
   そのため、表せるのはランク 1 多相だけである。
   同じ理由で、制約(`[A: Add]`)を型の中に書く場所も不要である。
   制約は変数に付いたまま、変数と一緒に量化される。

   `Rigid` には 2 つの用途がある。
   `run h { ... }` のヒープをスコープの中に閉じ込めることと、
   型注釈のスコーレム化(本体の型が注釈以上に一般的でなければ受理しない検査)である。
   どちらも同じ手順を踏む。
   レベルを上げてスコーレム定数を作り、スコープの出口で、
   スコーレム定数が浅いレベルへ漏れていないかを調べる。
   単一化は単一化変数のレベルを下げるが、スコーレム定数のレベルは下げず、
   下げる必要があればエラーにする(第8章 §8.3)。

   ### レベル

   レベルは、その型変数が何重の束縛の内側で作られたかを表す。
   束縛の本体をレベル + 1 で推論し、推論の後で、
   レベルが現在のレベルより高い単一化変数だけを `Generic` にする。
   単純な実装は、環境の自由型変数を集めて、それ以外を一般化する。
   しかし、束縛のたびに環境を走査するので、束縛の入れ子が深いと、
   走査の時間の合計が入れ子の深さの 2 乗に比例して増える。
   レベルを使うと、変数を一般化してよいかどうかを整数の比較 1 回で判定できる。
   Rémy による古典的な最適化で、OCaml の型検査器も同じ仕組みを使う。
   レベルは、スコーレム定数の脱出検査にも使う(第8章)。

   ### `ty` のコンストラクタ

   - `TCon (c, args)`：名目的な型と組み込みのスカラー型を、引数をすべて与えた形(飽和形)で表す。
     宣言の内容(コンストラクタの並び)は型に埋め込まない。
     埋め込むと、再帰型で一般化と具体化が止まらなくなる。
     宣言の内容は第6章の宣言表が持つ。
   - `TApp (f, a)`：高階カインドのための型適用。適用の連鎖の先頭が型変数のときにしか現れない。
     この不変条件は §1.7 の `tapp` と `repr` が守る。
   - `TArrow (params, ret, eff)`：関数の型で、3 つの要素を持つ。
     1 番目が引数、2 番目が返り値、3 番目がエフェクト行である。
   - `TRecord row` / `TVariant row`：行を 1 個包むだけのコンストラクタ。
   - `TRowEmpty` / `TRowExtend (label, field, rest)`：行の本体。
     行の末尾が `TRowEmpty` なら閉じた行、型変数なら開いた行である。
     開いた行は、レコードなら「そのラベルを含み、ほかのフィールドは未定」、
     エフェクト行なら「そのエフェクトを起こすことがある」を意味する。
     同じラベルの重複を許すのが Scoped Labels である。
     lacks 制約を持たない代わりに、同じラベルは最も左のものから一致させる(第8章)。

   ### 引数をレコードにする理由

   `TArrow` の 1 番目の要素は、`_item` ラベルだけを並べた閉じた行を `TRecord` で包んだものである。
   `(A, B) => C` の引数は `{_item: A, _item: B}` になる。

   こうすると、次の 3 つの利点がある。

   - 引数の個数(arity)の検査が、閉じた行の単一化だけで済む(sample.kel:190-191)。
   - ラベル付きの引数 `Cons(tail = t)` を同じ仕組みで扱える。
   - タプルが行の糖衣構文になる。
     `fst[A, R](t: {_item: A extends R})` のように、
     タプルの先頭の要素だけを指定して残りを行変数で受ける多相な関数を、
     レコードの行多相と同じ仕組みで型検査できる。

   そのため、型にも AST にも値の表現にも、タプル専用のコンストラクタはない。

   一方、矢印はエフェクト行を持つ専用のノードなので、
   2 引数の型構成子の適用とみなして分解することができない。
   そのため、Haskell の `Functor ((->) r)` のように、
   関数型を部分適用して高階カインドのインスタンスにすることはできない。 *)

  type ty =
    | TCon of oid * ty list (* 名目的な型と組み込みの型構成子の飽和形 *)
    | TApp of ty * ty (* 高階カインドの型適用。連鎖の先頭が型変数のときだけ現れる(repr が保証する) *)
    | TArrow of ty * ty * ty (* 引数(_item 行の TRecord)* 返り値 * エフェクト行 *)
    | TRecord of ty
    | TVariant of ty (* 構造的ヴァリアント。行 1 個 *)
    | TRowEmpty
    | TRowExtend of oid * ty * ty (* label * field(エフェクトならラベル引数)* rest *)
    | TVar of tvar ref

  and tvar = Unbound of var_info | Link of ty | Generic of var_info | Rigid of var_info

  (* ---- kind ---- *)

(* ## 1.6 カインドの単一化と既定化

   カインドが `KVar` を持つので、カインドの比較はすべて単一化で行う。
   構造の等しさ(`=`)で比べると、未解決の `KVar` は、
   同じ変数どうしでない限りどのカインドとも一致しない。

   `same_kind` は、2 つのカインドが一致するかどうかを返す。
   片方が未解決の `KVar` なら、もう片方にリンクして一致させる。
   返り値を `bool` にしているのは、
   呼び出し元がカインドの不一致を自分のエラーメッセージで報告するためである。
   たとえば第8章の `bind` は、どちらのカインドが期待されたもので、どちらが実際のものかを知っている。

   ### 構造の一致を使わない理由と、既定化の時期

   第8章の `rewrite_row` は、変数が行変数かどうかを、
   `vkind = KRow` という構造の一致ではなく `same_kind` で判定する。
   arity が 0 の型パラメータのカインドは `new_kind_var ()` で作るので、
   行の位置で使われた変数のカインドは、`KVar` が `KRow` にリンクした形になる。
   構造の一致では、この形を行のカインドと判定できない。
   構造の一致で判定すると、次の 2 つが型エラーになる。
   1 つは sample.kel:195 の `fst` に `{x = 1, _item = ...}` を渡す式で、
   :201-203 のコメントがこれを説明している。
   もう 1 つは、:210-215 の `describe` に `#Other` を渡す `describe(#Other)` である。
   `describe(#Other)` の例は仕様の本文ではなく、回帰テスト test/verify_fixes.t にある。
   したがって、カインドを直接パターンで調べるコードは、誤りである可能性が高い。

   `default_kind` を呼ぶ時期は、型パラメータの種類によって異なる。
   newtype と型エイリアスのパラメータは、第11章のパス 1b の最後に既定化する。
   let の型パラメータ、extern の型パラメータ(§11.40)、
   前提付きインスタンスの対象の型の束縛子(§11.38)は、スコーレム定数として作るので、
   `release_rigids` がスコーレム定数を解放するとき(§11.27)に既定化する。
   クラスメソッドの型パラメータは、メソッドの型を組み立てた直後(§11.33)に既定化する。
   既定化しないと、`?k7` のような未解決のカインドが表示に現れ、
   使われる位置のない型パラメータのカインドがいつまでも決まらない。

   既定化は早すぎてもいけない。
   `same_kind` は未解決の `KVar` どうしを片方にリンクするので、
   宣言を 1 つ検査するたびに既定化すると、
   まだ本体を読んでいない別の宣言のカインド変数まで、リンクをたどって `KStar` に決めてしまう。
   たとえば、互いを参照する newtype `A2[E] = MkA(B2[E])` と `B2[E] = MkB(() => Unit @ E)` で、
   先に処理した `A2` を既定化すると、その時点で `B2` の `E` のカインドまで `Type` に決まる。
   そのため、newtype と型エイリアスの既定化は、
   パス 1b が型宣言のグループをすべて処理し終えるまで待つ(§11.39)。

   `show_kind` は Keleut の表記(`Type` / `Row` / `[_, _] Type`)に合わせる。
   `?k` の付いた表記は未解決の `KVar` を表し、既定化の後には現れないはずである。 *)

  (* セルの書き換えの記録(§1.5)。trailing が真の間、型変数とカインド変数の
     書き換えを、元に戻すクロージャとして trail に追加する *)
  let trailing = ref false

  let trail : (unit -> unit) list ref = ref []

  let set_klink (r : kind_ref) k =
    (if !trailing then
       let old = r.k_link in
       trail := (fun () -> r.k_link <- old) :: !trail);
    r.k_link <- k

  let set_tv (r : tvar ref) v =
    (if !trailing then
       let old = !r in
       trail := (fun () -> r := old) :: !trail);
    r := v

  let rec kind_repr = function
    | KVar ({ k_link = Some k; _ } as r) ->
        let k' = kind_repr k in
        if k' != k then set_klink r (Some k');
        k'
    | k -> k

  let new_kind_var () = KVar { k_id = new_oid (); k_link = None }

  (* arity 個の Type を取る型構成子のカインド。k_arrow 1 = KArrow (KStar, KStar) *)
  let rec k_arrow arity = if arity = 0 then KStar else KArrow (KStar, k_arrow (arity - 1))

  (* 単一化して、一致したかどうかを返す。未解決の KVar は、もう片方のカインドにリンクする *)
  let rec same_kind a b =
    match (kind_repr a, kind_repr b) with
    | KStar, KStar | KRow, KRow -> true
    | KArrow (a1, a2), KArrow (b1, b2) -> same_kind a1 b1 && same_kind a2 b2
    | KVar r1, KVar r2 when r1 == r2 -> true
    | KVar r, k | k, KVar r ->
        set_klink r (Some k);
        true
    | _ -> false

  (* 未解決の KVar を KStar へ既定化する(呼ぶ時期は §1.6) *)
  let rec default_kind k =
    match kind_repr k with
    | KVar r -> set_klink r (Some KStar)
    | KArrow (a, b) ->
        default_kind a;
        default_kind b
    | KStar | KRow -> ()

  let show_kind k =
    match kind_repr k with
    | KStar -> "Type"
    | KRow -> "Row"
    | KArrow _ as k ->
        (* F[_] の形式。引数の個数だけ _ を並べる *)
        let rec args = function KArrow (a, b) -> a :: args (kind_repr b) | _ -> [] in
        let n = List.length (args k) in
        "[" ^ String.concat ", " (List.init n (fun _ -> "_")) ^ "] Type"
    | KVar r -> "?k" ^ string_of_int r.k_id

  (* ---- ty ---- *)

(* ## 1.7 型適用の正規化

   高階カインドのための `ty` のコンストラクタは `TApp` 1 つだけである。
   ただし、`TCon (c, args)` をすべて適用の連鎖(スパイン)で表すと、
   宣言表からクラス制約の伝播まで、`TCon` を扱う箇所をすべて書き換えることになる。
   そこで、適用の連鎖の先頭が型変数のときだけ `TApp` を残す、という正規化を行う。
   先頭が具体的な型構成子なら、飽和形の `TCon` にまとめる。

   `tapp` は、この正規化を行うスマートコンストラクタである。
   `repr` は、関数位置の型変数が後から決まった場合に正規化し直す。
   `TApp (α, Int32)` の後で `α := List` が決まると、
   次に `repr` を呼んだ時点で `List[Int32]` になる。
   以降の関数は、まず `repr` を呼んでから `match` するのを基本形とする。
   そのため、`tapp` と `repr` の数行だけで、実装全体が正規化した型を扱える。

   `repr` の処理は 3 つある。
   `Link` の連鎖をたどって代表元を返すこと、たどりながら経路を圧縮すること、
   `TApp` の関数位置を正規化し直すことである。
   経路を圧縮しなくても結果は変わらないが、深い連鎖で計算量が悪化する。
   `f' == f` という物理的な等しさの判定は、
   関数位置が変わらなかったときに新しいノードを確保しないためのものである。

   `repr` は関数位置の連鎖だけを正規化する。
   `TApp (f, a)` の `a` の内部は正規化しないので、`a` を使う箇所がそれぞれ `repr` を呼ぶ。

   ### 一階の単一化で済む理由

   型変数が適用の関数位置に来ると、`F[A] ~ List[Int32]` には解が複数あるように見える。
   しかし、型レベルのλがなければ、解は 1 つに決まる。

   - `F := List, A := Int32` だけが解になる。
   - `F := λx. List[Int32]`(A を捨てる)や `F := λx. List[x]` は、λを書けないので候補にならない。

   つまり、`F[A] ~ G[B]` は `F ~ G, A ~ B` に構造的に分解でき、最汎単一化子(mgu)は 1 つである。
   Haskell の高階カインドが一階の単一化で済むのも、同じ理由による。
   本実装は次の 2 つの規則を守る。

   1. 型レベルのλを持たない。
   2. 部分適用できる型エイリアスを持たない(実質的に型レベルのλだからである)。

   どちらかを破ると、単一化の解が一意でなくなり(unitary でなくなり)、主要型も失われる。
   Keleut の `type` 宣言が再帰も部分適用もできないのは、言語仕様の側で規則 2 を守るためである。
   第11章の `expand_alias` がこれを検査する(§11.5)。

   `app_spine` は、`TApp` の連鎖を、先頭の型と引数の並びに分解する。
   第9章の表示が使う。 *)

  (* TApp の正規化。関数位置が TCon なら、その引数の末尾に加える *)
  let tapp f a = match f with TCon (c, args) -> TCon (c, args @ [ a ]) | f -> TApp (f, a)

  (* Link の連鎖の経路を圧縮し、TApp の関数位置を正規化し直す。
     以降の関数は、まず repr を呼んでから match するのを基本形とする *)
  let rec repr ty =
    match ty with
    | TVar ({ contents = Link t } as r) ->
        let t' = repr t in
        (* 圧縮で指す先が変わるときだけ書き換える。変わらない書き換えまで記録すると、評価中に記録が伸び続ける *)
        if t' != t then set_tv r (Link t');
        t'
    | TApp (f, a) ->
        let f' = repr f in
        (match f' with TCon (c, args) -> TCon (c, args @ [ a ]) | _ -> if f' == f then ty else TApp (f', a))
    | t -> t

  (* TApp の連鎖を (先頭の型, 引数の並び) に分解する *)
  let rec app_spine ty =
    match repr ty with
    | TApp (f, a) ->
        let h, args = app_spine f in
        (h, args @ [ a ])
    | t -> (t, [])

(* ## 1.8 行を分解する

   行に対する操作は次の 3 つだけで、レコード、タプル、ヴァリアント、エフェクトのすべてに使う。

   `row_fields` は、行をフィールドの並びと行の末尾に分解する。
   行の末尾は `TRowEmpty`(閉じた行)か型変数(開いた行)のどちらかである。
   開いた行 `{x: Int32 | ρ}` は「x を含み、ほかのフィールドは未定」を意味し、行多相はこの形で表す。

   `row_tail_var` は、行の末尾が型変数ならその変数を返す。
   第10章は、構造的ヴァリアントの網羅性を判定するとき、ほかのケースが来ないことを確定させるために、
   この変数を `TRowEmpty` に束縛する。
   これが行を閉じる操作である。

   `row_append` は、`a` のフィールドを `b` の前につなぐ(splice)。
   使うのは第11章の 4 か所である。
   ヴァリアント型 `#A | #B | R` の要素の連結(§11.4)、
   開いた行に展開されるエイリアスの連結(§11.5 の `splice_row`)、
   閉じた行の矢印の末尾を新しい行変数で開く `open_closed_arrow`(§11.26)、
   インスタンス本体の検査で、実装の閉じたエフェクト行の末尾を新しい行変数で開く箇所(§11.38)である。
   `a` が閉じていることは、どの呼び出し元についても第11章が検査している。
   `row_append` は、左側が開いた行で右側が空でなければ `bug` を呼ぶ。
   右側が空なら、左側をそのまま返す。
   型エラーではなく `Panic` を投げるのは、
   これがユーザの書いたプログラムのエラーではなく、実装の不変条件の違反だからである。
   この使い分けは、§1.18 の `Type_error` と `Panic` の 2 つの例外に対応する。 *)

  (* 行を (フィールドの並び, 行の末尾) に分解する。行の末尾は TRowEmpty か TVar である *)
  let rec row_fields ty =
    match repr ty with
    | TRowExtend (l, f, rest) ->
        let fs, tail = row_fields rest in
        ((l, f) :: fs, tail)
    | t -> ([], t)

  let row_tail_var ty = match snd (row_fields ty) with TVar r -> Some r | _ -> None

  (* a のフィールドを b の前につなぐ(splice)。a が閉じていることは elab が検査する *)
  let rec row_append a b =
    match repr a with
    | TRowExtend (l, f, rest) -> TRowExtend (l, f, row_append rest b)
    | TRowEmpty -> b
    | t -> ( match repr b with TRowEmpty -> t | _ -> bug "row_append: open row on the left")

(* ## 1.9 変数を作る

   `new_var` の既定は、カインドが `KStar` で、制約なしである。
   `new_row_var` は、カインドを `KRow` にして `new_var` を呼ぶ関数である。
   専用の名前があるので、行変数を作るつもりで `KStar` の変数を作る誤りを、
   コードを読んで見つけられる。

   スコーレム定数は、`new_rigid_ref` と `new_rigid` の 2 つの関数で作る。
   スコーレム定数を作る箇所は複数ある。
   `run` のヒープ、注釈の型パラメータ、インスタンス検査のスコーレム化である。
   このうち注釈の型パラメータは、`new_rigid_ref` で作る。
   `release_rigids` が後から内容を `Generic` に書き換える(第11章 §11.27)ので、
   `ref` そのものが必要だからである。
   `run` のヒープと、インスタンス検査が期待型の型変数をスコーレム定数に置き換えるとき(第11章 §11.38)は、
   型だけで足りるので `new_rigid` で作る。
   制約は、どちらの関数にも `?classes` で渡す。
   `new_rigid` は `new_rigid_ref` の結果を `TVar` で包むだけなので、
   `Rigid` を組み立てる式は `new_rigid_ref` の 1 か所にしかない。 *)

  let new_var ?(kind = KStar) ?(classes = []) level =
    TVar (ref (Unbound { vid = new_oid (); vlevel = level; vkind = kind; vcls = classes }))

  let new_row_var level = new_var ~kind:KRow level

  (* スコーレム定数のセルを作る。release_rigids のように後から内容を書き換える側は、
     ty ではなくこの ref を持つ必要がある(第11章 §11.27) *)
  let new_rigid_ref ?(kind = KStar) ?(classes = []) level =
    ref (Rigid { vid = new_oid (); vlevel = level; vkind = kind; vcls = classes })

  let new_rigid ?(kind = KStar) ?(classes = []) level = TVar (new_rigid_ref ~kind ~classes level)

  (* ---- 組み込みの名前 ---- *)

(* ## 1.10 組み込みの名前

   ここに並ぶ定数は、実装の各所が直接参照する少数の名前である。

   `l_item` はタプルのラベルである。
   `(1, 2)` の型は `{_item: Int32, _item: Int32}` になる。
   `t._0` は、第3章が「`_item` を 0 回取り除いてから `_item` を選択する」式に脱糖する。
   タプルは Scoped Labels を使って実装する。
   同じラベル `_item` を並べ、先頭から何番目の `_item` かで要素を区別する。

   組み込みのスカラー型は `Boolean` / `Int32` / `Int64` / `Float64` / `String` / `Never` の 6 つだけである。
   `Never` はコンストラクタが 0 個の名目的な型である。
   そのため、第10章の網羅性検査は、節のない `n match {}` を網羅的と判定する。
   ほかの幅の数値型(`Int8`、符号なし、`Float32`)は言語にない。
   その接尾辞は字句解析では受理し、第11章が型エラー(終了コード 1)にする。
   その型名は組み込みの名前ではないので、ユーザが型として宣言できる。

   `t_unit` には名目的な型を使わない。
   Unit は空のレコードである(sample.kel:59, :167)。
   `()` と `{}` は同じ型で、単一化はレコードと同じ処理で行う。
   `Unit` という名前は、プレリュードの型エイリアスとしてだけ存在する(第15章)。

   `cls_integral` / `cls_fractional` は予約述語(§1.4)である。
   第11章はユーザによる宣言を拒否し、
   第8章はこれらの付いた変数を一般化せずに既定の型 `Int32` / `Float64` に決める。
   既定化を一般化より先に行うので、これらの述語は通常は表示に現れない。

   `eff_heap` / `eff_blocking` は、操作を持たない組み込みのエフェクトラベルである。
   操作を持たないエフェクトは、文法が空の本体を許すので、
   `effect Silent = {}` のようにソースにも書ける。
   それでも第6章は、この 2 つを表に直接登録する。

   `Heap` は、`run` が導入し、`Ref` と `MutableArray` の操作が要求するラベルである。
   Keleut のエフェクト宣言はパラメータを取らない。
   §1.17 の `ef_params` は、Keleut の仕様に対応する構文のないフィールドである。
   Diktor の文法は型パラメータを受理してここに入れ、空でなければ第11章が拒否する。
   一方、型の式には `@ {Heap[h]}` と書けるので、
   `Ref` / `MutableArray` の操作の型を `extern` のシグネチャとして書くこと自体はできる(第6章 §6.11)。
   それでも §6.11 がこれらの操作の型をまとめて組み立てるのは、実装が OCaml 側の値と切り離せず、
   プレリュードにも置くと同じ情報を 2 か所で管理することになるからである。
   `Blocking` は同じ組み込みの表に入るラベルで、
   `extern` がブロックすることがあると宣言するために書く(sample.kel:796, :812)。
   C リンケージの `extern` で `@` を省略したときの既定の行にもなる(sample.kel:496, :798)。

   ### 予約型名

   組み込みの型名を `newtype Boolean = Yes` のように再宣言できると、新しいデータ型として登録され、
   網羅性検査と組み込みのインスタンスの両方が壊れる。
   そのため、第6章の予約型名の表(`reserved_type_names`)が再宣言を拒否する。
   第6章はこの表を、本節の定数からではなく、文字列を `intern` し直して作る。
   そのため、組み込みの名前を 1 つ追加するときは、第1章と第6章の 2 か所を直す。
   `Never` は予約型名の表に入れず、
   第6章の `register_builtins` がコンストラクタ 0 個のデータ宣言として登録する。
   `t_never` は、第10章が、節のない `match` の照合対象の型を `Never` に決めるときに使う。 *)

  let l_item = intern "_item" (* タプルのラベル(sample.kel §4) *)

  let t_boolean = TCon (intern "Boolean", [])

  let t_int32 = TCon (intern "Int32", [])

  let t_int64 = TCon (intern "Int64", [])

  let t_float64 = TCon (intern "Float64", [])

  let t_string = TCon (intern "String", [])

  let t_never = TCon (intern "Never", [])

  (* Unit は名目的な型ではなく、空のレコードである(sample.kel:59, :167)。
     Unit という名前は、プレリュードの型エイリアスとしてだけ存在する *)
  let t_unit = TRecord TRowEmpty

  (* 予約述語。ユーザによる宣言は拒否し、これらの付いた変数は一般化せずに既定の型に決める *)
  let cls_integral = intern "Integral"

  let cls_fractional = intern "Fractional"

  (* 操作を持たない組み込みのエフェクトラベル。decls.ml が Ref/Array/MutableArray の
     操作と一緒に直接登録する(理由は §1.10) *)
  let eff_heap = intern "Heap"

  (* 第 1 引数がリージョンである組み込みの型構成子。
     第8章は、この位置の不一致を述べるメッセージを選ぶのに使い、
     第9章は、この位置の型変数の表示名を選ぶのに使う *)
  let ty_ref = intern "Ref"

  let ty_mutable_array = intern "MutableArray"

  let eff_blocking = intern "Blocking"
end

(* ## 1.11 リテラルと演算子

   ここで `Type` モジュールを出て、表層構文の定義に移る。

   数値リテラルは、ソースの表記をそのまま保持する。
   多倍長整数のライブラリは使わない。
   `0xff` も `0b1010` も `1_000` も、文字列のまま持っておけば `Int32.of_string` が解釈できる。
   値に変換するのは評価のときで、そのとき第11章が決めた型を調べる。
   そのため、既定化の結果がそのまま実行に反映される。
   `1 + 2` の `Integral` が `Int32` に決まったことを、評価器は表記と型から知る。
   負のリテラルは、第3章が `HYPHEN NUMBER` を 1 つのリテラルにまとめて作る。

   `n_suffix` は `1i64` / `1u8` / `1f32` の接尾辞である。
   Diktor が実行できる数値型は `Int32` / `Int64` / `Float64` の 3 種だけである。
   ほかの幅の接尾辞は字句解析では受理し、第11章が型エラー(終了コード 1)にする。
   `n_suffix_text` は接尾辞の原文(なければ空文字列)で、診断とダンプはこちらを使う。
   解釈済みの `n_suffix` から表記を組み立て直すと、
   幅がオーバーフローする接尾辞や、`1i032` のような先頭のゼロが、書いたとおりに出ない(第2章 §2.1)。

   数値パターンの重複は、値で正規化してから検出する。
   `0x1` と `1` は同じパターンである(第10章)。
   表記のまま比べると、重複を見逃す。
   同じ値かどうかは、表記を `Int32`、`Int64`、
   `Float64` の 3 通りで読み取った値の組で判定する(第10章 §10.3)。
   3 通りのどれで読んでも等しい表記だけを同じパターンとみなし、
   浮動小数点数として読んだ値では ±0.0 を同じ値とする。
   この判定は実行時の照合より細かいので、違う値を同じパターンとみなすことはない。
   その代わり、実行時には同じ値になるパターンの重複を見逃すことがある。
   Int32 の列に並んだ `0xFFFFFFFF` と `-1` がその例である。

   `bin_op` は、仕様の演算子表(sample.kel:366-370)の縮小版である。
   演算子は `Apply` に脱糖しない。
   理由は 2 つある。
   `&&` と `||` は短絡評価するので関数呼び出しにできないことと、
   `!=` は `Eq.eq` の否定であって `Ne` というメソッドがないことである。
   この 2 つの例外を 1 つの表の中だけで扱うために、AST に演算子のノードを残し、
   第11章と第14章が第7章の同じ表を引く。
   エラーメッセージに演算子をソースの表記のまま表示できる、という利点もある。

   なお、Float64 の値の表示は、読み直すと元の値に戻る最短の表記(最短のラウンドトリップ表現)で、
   有限の値なら Float64 リテラルとして読み直せる(第12章 §12.7)。
   絶対値が 1e16 以上の値の最短の表記は、
   `12345678901234568` のように小数点も指数も持たないことがある。
   Keleut ではこの表記が整数リテラルになるので、表示器は `.0` を補う。
   非有限値(inf / nan)にはリテラルがないので、読み直せる対象に含まれない。 *)

type num_suffix = NsInt of int | NsUInt of int | NsFloat of int (* i64 / u8 / f32 *)

type number = { n_text : string; n_is_float : bool; n_suffix : num_suffix option; n_suffix_text : string }

type bin_op = Add | Sub | Mul | Div | Rem | Eq | Ne | Lt | Le | Gt | Ge | And | Or

(* ## 1.12 型パラメータの束縛子

   型パラメータの束縛子は、`[A]`、`[h]`、`[F[_]]`、`[A: Add + Mul]` のどの書き方も、
   1 つのレコード `type_param` で表す。

   `tp_name` の先頭の文字は、大文字でも小文字でもよい。
   仕様 §0 が、識別子の大文字と小文字の規則から型パラメータを外しているからである。
   慣習として、型は大文字、リージョン変数は `run h { ... }` の `h` のように小文字で書く(sample.kel:50-51)。
   仕様 §10 のシグネチャの一覧がその例である。
   型変数と値の識別子は文法上の位置で区別できるので、字句解析で区別する必要はない。

   `tp_arity` が 0 のとき、カインドは `KVar` になる。
   §1.3 で述べた、使われた位置からカインドを決める仕組みは、ここから始まる。
   `F[_]` と書けば `tp_arity = 1` になり、`KArrow` が確定する。
   この規則は `let` の束縛子にも newtype の束縛子にも当てはまる。

   例外はクラスパラメータ(`type class C[A]` の `A`)で、
   `tp_arity` が 0 なら `KStar` に固定する(§11.33)。
   クラスパラメータでも、`[F[_]]` と書けばカインドは `[_] Type` になる。
   インスタンスは型構成子ごとに宣言し、インスタンス表のキーも型構成子なので(第6章 §6.9)、
   行をパラメータに取るクラスは意味を持たない。
   仕様 §8 がこれを定めている(sample.kel:359-361)。
   エフェクトについて量化したいときは、クラスパラメータではなく、
   メソッドの型パラメータに行変数を取る(sample.kel:362-363)。
   第11章は、クラスパラメータを行として使う形を拒否し(`test/kinds.t` の classrow / classrow2)、
   メソッドの型パラメータに行変数を取る形は受理する(classrowok)。

   束縛子にカインドの注釈を書く構文(`[E: EffectRow]` のような書き方)はない。
   `tp_arity` が 0 の束縛子のカインドは、
   同じ型宣言のグループにある型の本体での使われ方からしか決まらない(sample.kel:246-247)。
   使われ方がなければ `KStar` に決まるので、行カインドの幽霊型パラメータ(phantom)を書く手段はない。
   仕様 §14 は、この注釈の構文を TODO として残している(sample.kel:879-881)。
   カインドを書けるのは型エイリアスだけである(`type Request: EffectRow`)。

   `tp_classes` の型は `long_id list` である。
   ただし、第3章の `cls_list` は、クラス名として大文字で始まる識別子 1 つしか受理しない。
   そのため、どの要素も名前 1 つだけの `long_id` になり、`[A: Prelude.Add]` は構文エラーになる。 *)

type type_param = {
  tp_name : string; (* 先頭は大文字でも小文字でもよい(リージョン変数は h のように小文字で書く) *)
  tp_arity : int;
      (* F[_] なら 1。0 ならカインドは KVar で、使われた位置から決める。
         クラスパラメータだけは KStar に固定する *)
  tp_classes : long_id list;
}

(* ## 1.13 Data ファンクタ

   AST のすべてのノードは `Data.t * ノード` の組である。
   `Data.t` は、ノードに付けるデータの型である。
   `Data` を差し替えることで、同じ AST の定義を、ノードに付けるデータの異なる木として再利用する。

   - `EmptyData` は `t = Location.span` で、位置のほかにデータを持たない最小の `Data` である。
     本実装はどこからも `EmptyData` を使っていない。
     `Data` を差し替えられるという性質を、
     説明文ではなくコードで示すためだけに置いてある(§3.1 も同じ例を指す)。
   - 第5章の `Tree.ElabData` は `{ oid; loc; mutable ty_field; mutable resolved; mutable dict }` である。
     位置に加えて、ノードの番号を持つ。
     さらに、型検査が決めた型、解決結果、辞書の情報を後から書き込むフィールドを持つ。

   第3章のパーサも、Menhir の `%parameter <Data : Syntax.Data>` で同じ `Data` をパラメータに取り、
   第16章のドライバが `Parser.Make (Tree.ElabData)` として適用する。
   そのため、パーサが作った木がそのまま精緻化木になり、木を変換するためのコピーは 1 回も起きない。
   これが成り立つのは、`Syntax.Make` がアプリカティブファンクタ(同じ引数から作れば同じ型になる)だからである。
   Menhir が生成したパーサとライブラリが別々に `Syntax.Make (ElabData)` と書いても、型が一致する。

   `allocate` は `Location.span` を受け取る。
   エラーに位置を表示するにはすべてのノードに span が必要で、
   後から追加しようとすると、ノードを作るすべての箇所を書き換えることになる。
   `loc` は、ノードに付けたデータからその span を取り出す。
   第3章のパーサは、意味動作が構文の形を拒否するとき、
   拒否した構文の始まりの位置を `loc` で読んで構文エラーに付ける。

   代償として、パターンマッチはすべて `(_, Ident ...)` の形になり、読みにくくなる。 *)

module type Data = sig
  type t

  val allocate : Location.span -> t

  val loc : t -> Location.span
end

module EmptyData : Data = struct
  type t = Location.span

  let allocate loc = loc

  let loc d = d
end

module Make (Data : Data) = struct
  (* ---- 型の式 ---- *)

(* ## 1.14 型の式

   `type_exp` はソースに書かれた型の構文であり、§1.5 の `ty` ではない。
   両者を分けるのは、構文解析の時点では、ソースに書かれた名前が何を指すか分からないからである。
   第11章の `elab_type` が、環境を調べながら `ty` へ変換する。

   `EIdent` は、型変数、型構成子、型エイリアス、エフェクト名のどれでもありうる。
   どれであるかは環境で決まり、字句や文法では決まらない。
   たとえば `E` という名前は、束縛子にあれば行変数で、宣言表にあればエフェクトである。

   `EBraceRow` 1 つで、レコード型、エフェクト行、`EffectRow` エイリアスの本体を表す。
   これらを別のノードに分けると、`@ {..}` の位置で reduce/reduce 衝突が起きる。
   そこで、要素の形(`BField` か `BLabel` か)で意味を判別する。

   `EArrow` の第 3 要素が `None` なら、`@` を省略している。
   省略した `@` の意味は、矢印の位置で決まる。
   入れ子の矢印で省略した `@` は `@ {}` として扱う(第11章 §11.4)。
   前方参照に使えるシグネチャを作れるのは、
   注釈の最も外側の矢印に `@` を明示した束縛か、`pub` を付けた束縛だけである(§11.36)。
   省略をこのように扱うのには理由がある。
   省略した `@` ごとに独立した行変数を作ると、
   本体を調べずに作ったシグネチャの中で、その行変数が何の制約も受けないまま一般化される。
   その結果、宣言の順序によってはエフェクトの検査が行われなくなる。

   `EUnion` は、`#A | #B | R` と `IoError | ParseError` の両方を表す。
   構造的ヴァリアントの合併とエフェクト行の合併を同じ縦棒で書くので、AST では区別しない。

   `EHole` は `List[_]` の穴である。
   パーサが `EHole` を作るのは型引数の位置だけで、
   実際の用途は `type instance` の対象の型(`type instance Functor[List[_]]`)に限られる。
   束縛子 `F[_]` の `_` は `EHole` にならない。
   パーサはこの `_` の個数を数えて、§1.12 の `tp_arity` にする。
   インスタンスの対象の型以外の型引数の位置に現れた `EHole` は、第11章が型エラーにする。 *)

  type type_exp' =
    | EIdent of long_id (* 型変数、型構成子、型エイリアス、エフェクト名のどれか。環境で決まる *)
    | EApply of type_exp * type_exp list (* List[A] / F[A] *)
    | EArrow of type_exp list * type_exp * type_exp option (* (A, B) => C @ E。@ を省略すると None *)
    | EBraceRow of brace_elem list * type_exp option (* { ... extends T }。要素の形で意味が決まる *)
    | EVariantCase of string * type_exp option (* #Foo(T) / #Foo *)
    | EUnion of type_exp list (* #A | #B | R / IoError | ParseError *)
    | EHole
        (* List[_] の穴。型引数の位置にだけ現れ、インスタンスの対象の型で使う。
           束縛子 F[_] の _ は EHole にせず、tp_arity にする *)

  and type_exp = Data.t * type_exp'

  and brace_elem =
    | BField of string * type_exp (* x: Float64 / read: () => String *)
    | BLabel of long_id * type_exp list (* Print / Heap[h] / ReqId(エフェクト行のラベルか、行に展開するエイリアス) *)

  (* ---- パターン ---- *)

(* ## 1.15 パターン

   `PRecord` は、レコードのパターンとタプルのパターンの両方を表す。
   第 2 要素の `pat option` だけで、次の 3 つの状態を区別する。

   | 第 2 要素 | 意味 | 対応する書き方 |
   |---|---|---|
   | `None` | 閉じた行 | タプルパターン。要素の個数を検査する |
   | `Some (_, PWildcard)` | 開いた行で、残りのフィールドは捨てる | レコードパターンの既定 |
   | `Some p` | 開いた行で、残りのフィールドを `p` に束縛する | `{x, ...rest}` |

   レコードパターンは既定で開いていて、タプルパターンは閉じている。
   仕様のこの違いを、コンストラクタを増やさずに表せる。

   `PCtor` は名目的な型のコンストラクタのパターンだが、`handle` の節のパターンにも使う。
   `write(msg) => ...` は、構文の上ではコンストラクタパターンと区別できないからである。
   どちらなのかは第11章が分類し、結果を第5章の `resolved` に書き込む。
   名前付き引数(`Cons(tail = t)`)があるので、
   実引数の位置とフィールドの位置の対応表も `resolved` に入る。

   `PAnnot` はパラメータの型注釈だけに使う。
   式に型注釈を付けるノードはない。
   `let b: Int64 = 0` の注釈も、関数の返り値とエフェクトの注釈も、
   すべて §1.16 の `let_binding` のフィールドに置く。
   スコーレム化の検査は束縛 1 つを単位に行うので、注釈も束縛に集めるほうが扱いやすい。

   `as` パターンは Keleut の構文にないので、AST にもない。
   or パターン、遅延パターン、リストや配列のリテラルパターンも持たない。
   Unit のパターンにも専用のノードはなく、`PRecord ([], None)` で表す。
   §1.10 で述べたとおり、Unit は空のレコードだからである。 *)

  type pat' =
    | PWildcard
    | PVar of string
    | PBool of bool
    | PNumber of number
    | PText of string
    | PRecord of (string * pat) list * pat option
        (* レコードとタプルの両方に使う。第 2 要素が None なら閉じた行(タプル。要素の個数を検査する)、
           Some p なら残りのフィールドを p に束縛する(...rest)。
           開くだけなら Some PWildcard(レコードパターンの既定) *)
    | PCtor of long_id * ctor_arg_pat list (* 位置引数か名前付き引数。handle の節のパターンにも使う *)
    | PVariant of string * pat
    | PAnnot of pat * type_exp (* パラメータの型注釈 (p: Point) *)

  and pat = Data.t * pat'

  and ctor_arg_pat = { cap_label : string option; cap_pat : pat }

  (* ---- 式 ---- *)

(* ## 1.16 式と束縛

   式のノードは大半が構文をそのまま表すので、設計上の選択が形に現れている箇所だけを述べる。

   `Apply` の第 2 引数は常に引数レコードである。
   `f(1, 2)` は `Apply (f, {_item = 1, _item = 2})` になる。
   関数適用のノードは 1 引数のままで、引数の個数は引数レコードの行が表す。

   `Construct` と `Variant` は別物である。
   前者は宣言された名目的な型のコンストラクタで、閉じた型を持ち、再帰型と型パラメータを使える。
   後者は構造的ヴァリアント `#Foo(e)` で、行多相の開いた型を持つ。
   後者のペイロードは常に 1 つの値で、
   複数に見えるものはタプル、つまり `_item` 行である。

   `RecordExtend` の評価順は value、rest である。
   コンストラクタの引数の順序(rest、label、value)と逆なので、読み間違えやすい。
   仕様(sample.kel:278)は、`{l = e extends r}` の `e` を先に、`r` を最後に評価すると定めている。
   第3章のタプルの脱糖は先頭の要素を最も外側に置くので、
   この順序なら `(a, b, c)` は左の要素から順に評価される。
   第14章も同じ順で評価する。

   `RecordUpdate` が別のノードなのは、
   `{r with l = e}` が、値の中でのフィールドの順序を保つ必要があるからである。
   フィールドを除去してから追加し直すと、順序が変わり、表示も変わる。

   `Match` の照合対象は 1 つである。
   Keleut は後置の `v match { ... }` しか持たない。
   複数の照合対象を持つように見える照合は、タプルに対する照合である。
   タプルは `_item` 行なので、この照合も 1 つの照合対象に対する照合として扱える。
   網羅性検査のパターン行列も、最初は 1 列である(第10章)。
   条件式 `if` も専用のノードを持たない。
   第3章が、`Boolean` に対する 2 節の `Match` に脱糖する。

   `resume` は名前ではなく、`Resume` という専用のノードで表す。
   構文が保証できるのは、`resume` を値として名前に束縛できないことまでで、
   `fn() => resume(x)` は書けてしまう。
   そのため、`resume` が second-class であること(節の外へ持ち出せないこと)は、2 段階の検査で守る。
   第11章は節の本体を走査して、無名関数と関数束縛の本体の中にある、その節の `Resume` を拒否する。
   この走査は、内側の `Handle` の節には入らない。
   第14章は、実行時に継続の生存フラグ(`r_alive`)を調べる。

   `Handle` の節は、`match` と共通の `clause` である。
   `return` 節、`cancel` 節、操作節の分類は第11章が行い、結果を `resolved` に書く。
   パーサに分類させないのは、操作名の解決に宣言表が必要だからである。

   `let_binding` には注釈を集めてあり(§1.15)、関数定義のパラメータもここに持つ。
   `lb_params` が `None` なら値束縛、`Some ps` なら関数定義で、
   パーサは `Lambda` を作らずにパラメータをここに残す。
   関数定義かどうかは、この 1 つのフィールドを調べるだけで決まる。
   第11章は、関数定義ならそのまま一般化する。
   値束縛なら、右辺が構文上の値(§11.9 の `is_value`)のときだけ、
   本体の単一化変数を一般化する(値制限、§11.28)。

   ### LetRec の右辺

   `LetRec` の右辺に関数でない式を許すと、型検査に通ったプログラムが実行時にエラーになる。
   そのため、第11章が関数でない右辺を拒否する。
   AST と文法では右辺を制限せず、任意の式を書けるままにしている。
   文法を狭めるより、検査を 1 か所に置くほうが、
   分かりやすいエラーメッセージを表示できるからである。 *)

  type exp' =
    | Bool of bool
    | Number of number
    | Text of string
    | Ident of long_id (* 変数か修飾名の参照。引数のないコンストラクタの参照もこのノードで表す *)
    | Hole (* ??? *)
    | Apply of exp * exp (* 第2引数は常に引数レコード *)
    | Construct of long_id * ctor_arg list (* Some(1) / Cons(tail = t)。名前付き引数も書ける *)
    | Variant of string * exp (* #Foo(e)。ペイロードは常に 1 つの値 *)
    | BinOp of exp * bin_op * exp (* elab / interp が prims.ml の表を引く *)
    | Not of exp (* ! だけ *)
    | Neg of exp (* 前置の -。Neg.neg を呼ぶ。数値リテラルに付いた - はパーサが負のリテラルにまとめる *)
    | Lambda of lambda (* fn(x, y) => e *)
    | Let of let_binding * exp
    | LetRec of let_binding list * exp
    | Seq of exp list (* 式文の並び。let を含むブロックは Let(b, 残り) の入れ子になる *)
    | Match of exp * clause list (* 照合対象は 1 つ *)
    | RecordEmpty
    | RecordExtend of exp * string * exp
        (* (rest, label, value)。評価は value → rest の順(sample.kel:278) *)
    | RecordUpdate of exp * string * exp (* {r with l = e}。フィールドの順序を保つための専用のノード *)
    | RecordRestriction of exp * string (* r \ l *)
    | RecordSelection of exp * string
    | Perform of long_id * exp (* perform print(msg)。解決した完全名は resolved に書く *)
    | Handle of exp * clause list
        (* 節は match と共通。分類は elab が行い、resolved に書く *)
    | Resume of exp option (* resume() / resume(e)。引数は record_of_args を通さず、式のまま持つ *)
    | Run of string * exp (* run h { ... } *)

  and exp = Data.t * exp'

  and ctor_arg = { ca_label : string option; ca_exp : exp }

  and lambda = { l_params : pat list; l_body : exp }

  and clause' = { cl_pat : pat; cl_guard : exp option; cl_body : exp }

  and clause = Data.t * clause'

  and let_binding' = {
    lb_pub : bool;
    lb_name : pat; (* 関数定義なら PVar。値束縛にはパターンを書ける(match に脱糖する) *)
    lb_tparams : type_param list; (* let f[A, E] の [A, E]。パーサが付けるのは関数束縛だけで、値束縛では常に空 *)
    lb_params : pat list option; (* None = 値束縛。Some ps = 関数定義 *)
    lb_ret : type_exp option; (* : T *)
    lb_eff : type_exp option; (* @ E *)
    lb_body : exp;
  }

  and let_binding = Data.t * let_binding'

  (* ---- 宣言 ---- *)

(* ## 1.17 宣言

   トップレベル、`module` の本体、`type instance` の本体は、同じ `decl` 型で表す。
   3 つとも宣言の並びだからである。
   例外は 2 つある。
   `type class` の本体は `val m: T` の並び、`effect` の本体は `op: (T) => U` の並びなので、
   専用のレコードを持たせる。

   設計上の選択が、AST の形や検査に現れている箇所を挙げる。

   - `cls_params` が 1 個であることは、第11章が検査する。
     多パラメータ型クラスを持たないという選択は、AST の形ではなく検査として現れる。
     文法は複数のパラメータを受理するので、第11章が専用のエラーメッセージを表示できる。
   - `ef_params` は、Keleut の仕様に対応する構文がないフィールドである。
     パーサが型パラメータの非終端記号をほかの宣言と共有しているのでフィールドだけがあり、
     空でなければ第11章が拒否する。
   - `ex_abi` は「prim」か「C」である。
     前者は組み込みプリミティブへの割り当て、後者は外部関数の呼び出し(FFI)である。
     Diktor が C リンケージで実装しているのは、
     既知名の数学関数 sin / cos / sqrt / exp / log だけである。
     実装は第13章 §13.4 に、それぞれの関数に要求する型は第6章 §6.2b にある。
     `extern` の再宣言は拒否する(§6.2)。
     再宣言を許すと、`__int32_add` のようなプリミティブに実装と異なる型を後から付けられ、
     型検査の結果が実装と食い違う。
   - `ex_prim` は実装名である。
     module の平坦化(第11章)は `ex_name` を `M.f` に修飾するが、
     `ex_prim` は修飾する前の元の名前のまま残る。
     実装表(第13章)の探索と、登録簿(第6章)のプレリュード保護は、こちらをキーにする。
     修飾名をキーにすると、`extern` を module の中に書くだけでプレリュード保護を回避できる。
     また、C の既知名を module の中で宣言すると、エラーにならないまま実装が見つからなくなる。
     二重宣言の検査だけは修飾名で行う(§6.2)。
     別々の module が同じ C シンボルを宣言する形を許すためである。
   - `newtype X` のように右辺を省いた宣言と `Never` は、コンストラクタが 0 個、
     すなわち `NtCtors []` である。
   - `DModule` の平坦化は第11章が行う。
     宣言の名前を修飾名に変え、修飾する前の名前から修飾名への別名の表を作る。
     module の入れ子と、module の中の effect 宣言、type class 宣言、式文は、
     Diktor が実装していない。
   - `DExp` はトップレベルの式文である(sample.kel:662)。
   - `ins_args` が 1 個であることは、第11章が検査する。
     その 1 個は `List[_]` のように `EHole` を含められる。
     本体が `let` だけであることは第11章が検査する。
   - `ins_tparams` は前提付きインスタンスの束縛子で、
     インスタンスの対象の型の `_` に左から順に対応する(仕様 §8)。
     専用の型は持たず、`type_param` を `let` / `class` / `newtype` と共有する。

   syntax.ml はここまでである。
   第1章の残りは補助の 2 ファイルで、§1.18(aux.ml)が通し番号と例外の定義、
   §1.19(location.ml)が位置を扱う。
   続く第2章(lexer.ml)は、この AST を組み立てるためのトークン列をソースから作る。 *)

  type type_alias' = {
    ta_pub : bool;
    ta_name : string;
    ta_params : type_param list;
    ta_kind : string option; (* : Type / : EffectRow。解釈は elab が行う *)
    ta_body : type_exp;
  }

  type ctor_decl = { cd_name : string; cd_fields : field_decl list }

  and field_decl = { fd_label : string option; fd_ty : type_exp }

  type newtype_rhs = NtCtors of ctor_decl list (* Never は [] *)

  type newtype' = { nt_pub : bool; nt_name : string; nt_params : type_param list; nt_rhs : newtype_rhs }

  type effect' = {
    ef_pub : bool;
    ef_name : string;
    ef_params : type_param list; (* Keleut にパラメータの構文はない。空でなければ elab が拒否する *)
    ef_ops : (string * type_exp) list;
  }

  type class_val = { cv_name : string; cv_tparams : type_param list; cv_ty : type_exp }

  type class_decl' = {
    cls_pub : bool;
    cls_name : string;
    cls_params : type_param list; (* 1 個であることは elab が検査する *)
    cls_vals : class_val list;
  }

  type extern_decl' = {
    ex_pub : bool;
    ex_abi : string; (* 「prim」 / 「C」 *)
    ex_name : string;
    ex_prim : string; (* 実装名。修飾する前の元の名前で、module の平坦化でも変わらない *)
    ex_tparams : type_param list;
    ex_params : pat list;
    ex_ret : type_exp option;
    ex_eff : type_exp option;
  }

  type decl' =
    | DType of type_alias'
    | DNewtype of newtype'
    | DEffect of effect'
    | DClass of class_decl'
    | DInstance of instance_decl'
    | DLet of let_binding
    | DLetRec of let_binding list
    | DModule of bool * string * decl list (* pub * 名前 * 本体 *)
    | DExtern of extern_decl'
    | DExp of exp (* トップレベルの式文(sample.kel:662) *)

  and decl = Data.t * decl'

  and instance_decl' = {
    ins_tparams : type_param list; (* 前提付きインスタンスの束縛子。対象の型の _ に左から順に対応する *)
    ins_class : string;
    ins_args : type_exp list; (* 1 個であることは elab が検査する。List[_] のように EHole を含められる *)
    ins_body : decl list; (* let だけであることは elab が検査する *)
  }
end
