(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第1章 型・カインド・行・AST

   本章は、実装全体で使う語彙を定める。
   以降の章はすべて、本章で定義する `Type.ty` と AST の上で動く。
   実装を読み始める場所であり、迷ったときに戻る場所でもある。

   本章は前の章から何も受け取らない。
   後の章へ渡すものは次の 2 つである。

   - `Type` モジュール：第8章(unify.ml)が破壊的に書き換え、第9章(show.ml)が印字し、
     第11章(elab.ml)が組み立てる型の表現。
   - `Syntax.Make` が作る AST：第3章(parser.mly)が組み立て、第5章(tree.ml)が注釈の欄を付け、
     第4章(dump.ml)が表示する。

   ## 見取り図

   Diktor は、機構を 1 つに統合するのではなく、運ぶものの性質に合った運び手を選ぶことで、
   実装の総量を抑える。
   Diktor の運び手は次の 3 つである。

   | 運び手 | 何を運ぶか | いつ決まるか |
   |---|---|---|
   | **レベル**(`vlevel`) | 一般化の可否、`run` のスコープの内外 | 静的に、整数の比較 1 回で |
   | **行**(row) | レコード、タプル、ヴァリアント、エフェクト | 動的に、最も内側のハンドラで |
   | **型変数に付けた制約の集合**(`vcls`) | クラス制約と予約述語 | 型から大域的に |

   言語機能と、それを実装する道具の対応は次のとおりである。
   左の列が Keleut の仕様(`../doc/sample.kel`)の機能、右の列が本実装での実現方法である。

   | 言語機能 | 実装に使う道具 |
   |---|---|
   | HM 多相・let 一般化 | 型変数の `vlevel` |
   | ランク 1 多相 | 量化子を型に持たず、`Generic` マークで表す |
   | 値制限 | レベルを上げるかどうかを構文で決めるだけ(第11章) |
   | レコード・タプル | 行と Scoped Labels。タプルは `_item` ラベルの行 |
   | 多引数関数 | `TArrow` の引数成分が閉じた `_item` 行 |
   | 構造的ヴァリアント | `TVariant`。中身は行 1 個 |
   | 名目的データ | `TCon` と宣言表(第6章)。型に宣言を埋め込まない |
   | エフェクト | 同じ行を `TArrow` の第3成分に載せる |
   | `run h` のスコープ安全性 | 剛定数 `Rigid` とレベル。ランク 2 多相は使わない |
   | 型クラス | `vcls` と、実行時の値のタグによる動的ディスパッチ |
   | 高階カインド | `TApp` を 1 つ足すだけ。型レベルλは持たない |
   | カインド推論 | `KVar`、`same_kind`、残ったカインド変数の既定化(時期は §1.6) |
   | 網羅性検査 | Maranget の usefulness(第10章) |
   | エフェクトの実行 | OCaml 5 の `Effect.Deep`(第14章) |

   多パラメータ型クラスは持たない。
   Keleut の仕様が明示的に除外しており(sample.kel:356)、
   そのおかげで型スキーマ専用のデータ型を 1 つも持たずに済む。
   量化は `Generic` マークだけで表せる。

   ## パイプライン

   ソースから実行結果までは、次の 4 つの区間に分かれる。

   ```
   ソース ─字句─▶ トークン列 ─構文─▶ AST ─精緻化─▶ 型付き木 ─評価─▶ 値
   ```

   - **字句**(第2章 lexer.ml)：生のトークン、`{` の 3 分割、ASI の 3 層。
   - **構文**(第3章 parser.mly)：Menhir で解析する。タプルや `t._0` はここで脱糖する。
   - **精緻化**(elaboration、第5章から第11章)：型を推論しながら、
     AST のノードに型と解決結果を書き込む。
     木は作り直さない。
     書き込む欄は第5章の `ElabData` にある。
   - **評価**(第12章から第14章)：型付き木をたどる。
     Keleut のエフェクトは OCaml 5 のエフェクトにそのまま写す。

   全体は第16章(driver.ml)が束ねる。

   ## 章の対応表

   | 章 | ファイル | 何をするか |
   |---|---|---|
   | 1 | lib/syntax.ml | 型・カインド・行・AST(本章) |
   | 2 | lib/lexer.ml | 字句解析。3 層と ASI |
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

   本章の本体は syntax.ml の §1.1〜§1.17 である。
   補助の 2 ファイルは最後に置く。
   §1.18 が aux.ml、§1.19 が location.ml である。 *)

open Aux

(* ## 1.1 名前と経路

   最初に決めることは 2 つある。
   名前をどう持つかと、構文エラーをどこから投げるかである。

   `long_id` は、`Console.write` や `Parser.Result` のような、ドットで区切った経路である。
   型とパターンの位置では文法がそのまま作る。
   式の位置では、第3章の意味アクション(`dot_select`)が、
   先頭から続く大文字の成分と直後の 1 成分を畳んで作る。
   そのため、最後の成分を除いてすべて大文字で始まる、という不変条件が付く。
   第3章は成分が大文字で始まるかどうかを見て、`r.x.y` のようなレコードの選択とパスの参照を、
   同じドットから読み分ける。

   `Syntax_error` は意味アクションが投げる構文エラーで、
   Menhir の `Parser.Error` とは別の系統である。
   文法で表現すると LR(1) が壊れるが、構文の誤りではある、という種類の誤りをここへ集める。
   たとえば、レコードのラベルに大文字の識別子を書いた場合である。
   第16章は、どちらの構文エラーも終了コード 2 にそろえる。 *)

type long_id = LongId of string list

exception Syntax_error of string

let long_id components = LongId components

let show_long_id (LongId components) = String.concat "." components

(* ## 1.2 名前のインターン

   ここから `Type` モジュールに入る。
   最初は名前の扱いである。

   行のラベルの比較は単一化の内側のループで何度も走るので、文字列のままでは重い。
   そこで、表の鍵になる名前を整数(`oid`)に置き換える。
   `intern` は同じ文字列に同じ番号を返し、`name_of` は番号から名前を引く。

   名前を置き換える表は、名前空間ごとに分けない。
   レコードのラベル、エフェクト名、操作の完全名、型構成子、クラス名、コンストラクタ名、
   `extern` 名を、すべて同じ表に入れる。
   綴りが同じなら同じ `oid` になる。
   名前空間の区別は、番号ではなく、番号を使う側の表が担う。
   第6章の `Decls.effects` に載っていればエフェクト名、
   `Decls.con_kinds` に載っていれば型構成子である。

   一方、値の識別子は整数にしない。
   `let` で束縛した名前も変数の参照も文字列のままで、
   型検査の環境も評価器の環境も `Map.Make (String)` を使う(第11章、第12章)。
   したがって、型検査の名前の比較がすべて整数の比較になっているわけではない。
   整数になっているのは、行のラベルのように表を引く経路だけである。

   この設計では、行のラベルの比較が `=` 1 回で済む。
   その代わり、`oid` を単独で見ても何の名前かは分からず、
   表を引く側が名前空間を知っていなければならない。

   行のラベル専用の別名は置かず、ラベルもエフェクト名も型構成子も、
   `intern` / `name_of` の 1 組で扱う。
   同じ操作に 2 つの名前があると、どちらを使うかを読み手が判断しなければならないからである。 *)

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

(* ## 1.3 カインド

   カインドは純粋に構造的で、制約を載せない。
   制約をカインドに載せる設計は、制約が `Type` の変数に付くことを前提にしている。
   `Functor[F]` の `F` はカインド `[_] Type` を持つので、この前提は高階カインドで崩れる。
   制約は、§1.4 で述べるように型変数そのものに付ける。

   `KRow` はレコード、ヴァリアント、エフェクトで分けない。
   分けると、第8章の `rewrite_row` を 3 回書くことになる。
   行のラベルが何を意味するかは、
   その行を包むノード(`TRecord` / `TVariant` / `TArrow` の第3成分)が決める。

   ### カインド変数

   カインドは `KStar` / `KArrow` / `KRow` のほかに、カインド変数 `KVar` を持つ。
   理由は Keleut の表層構文にある。

   ```keleut
   let fst[A, R](t: {_item: A extends R}): A = t._item
   let with_log[A, E](body: () => A @ {Print extends E}): A @ E = ???
   ```

   `[A]` も `[R]` も `[E]` も、束縛子の見た目は同じである。
   `R` が行だと分かるのは `extends` の右に現れたときで、
   `E` が行だと分かるのは `@` の右に現れたときである。
   つまり、カインドは使われた位置からしか決まらない。
   唯一の例外が `F[_]`(sample.kel:437)で、これだけは字句でカインドが確定する。
   この扱いは `let` の束縛子に限らず、newtype の型パラメータにも当てはまる。
   仕様 §6 は、型パラメータのカインドを
   「宣言群の中の型の本体での使われ方から推論する。使われ方がなければ Type とする」と定めている。
   newtype での扱いは第11章 §11.31 で述べる。

   そこで、`[_]` が書いてあればその場で `KArrow` を確定し、
   書いていなければ新しい `KVar` を与えて、使われた位置から推論する。
   使われた位置から決まらずに残った `KVar` は、`KStar` に既定化する(既定化の時期は §1.6 で述べる)。
   カインドの推論は、カインドの単一化と、残ったカインド変数の既定化だけで行う。
   カインド多相(PolyKinds)は扱わない。 *)

  type kind =
    | KStar
    | KRow (* record / variant / effect 行で共通。分けない *)
    | KArrow of kind * kind (* F[_] *)
    | KVar of kind_ref (* 使われた位置から推論し、残れば KStar へ既定化する(時期は §1.6) *)

  and kind_ref = { k_id : oid; mutable k_link : kind option }

(* ## 1.4 型変数に付くもの

   `cls` は制約の集合である。
   集合といっても `oid list` で、重複は追加するときに除く。
   1 つの変数に付く制約はせいぜい数個なので、連想配列を使うほどの価値はない。

   このリストには予約述語も入る。
   `Integral` と `Fractional` は、整数リテラルと小数リテラルの型を保留するための述語である。
   クラス制約と同じ場所に置くので、`1 + x` が `{Integral, Add}` を持つ状況を、
   特別な処理なしに正しく扱える。
   ただし、予約述語はクラス制約と次の点で扱いが異なる。

   - 利用者は同名のクラスを宣言できない(第11章の `register_class` が拒否する)。
     第11章は、型パラメータの制約に書いた予約述語と、予約述語のインスタンス宣言も拒否する。
   - 第8章は予約述語つきの変数を一般化せず、既定の型へ落とす(`generalize` と `default_numerics`)。
   - 第8章の曖昧性検査は、予約述語つきの変数を報告の対象にしない。

   `var_info` は、型変数の 4 つの状態(§1.5)が共有する中身で、カインドと制約の集合を持つ。
   制約をカインドではなく変数に持たせる理由は §1.3 で述べた。

   制約つきの変数は、第8章の台帳 `class_vars` にすべて控える。
   台帳は、既定化の掃き出し(§8.9)と、曖昧性検査の両方が使う。
   曖昧性検査は、スキーマの型から到達できない制約を報告する(§8.9)。

   スーパークラスは持たない。
   仕様 §8 がスーパークラスを導入しないと定めており、
   第11章はクラスのパラメータに書いた制約を拒否する(§11.33)。 *)

  type cls = oid list

  type var_info = { vid : oid; vlevel : level; vkind : kind; vcls : cls }

(* ## 1.5 型

   型変数は可変参照である。
   `TVar of tvar ref` の `ref` が Union-Find のセル、`Link` が親へのポインタ、
   §1.7 の `repr` が経路圧縮つきの find にあたる。
   ランクによる併合はしない。
   型は木なので、経路圧縮だけで実用上の深さは十分に浅くなる。

   型変数の状態は次の 4 つである。

   - `Unbound i`：**未定変数**。まだ決まっていない変数で、`i.vlevel` が一般化の可否を決める。
   - `Link t`：すでに `t` と単一化した変数。
   - `Generic i`：一般化された変数、すなわち ∀ で束縛された変数。
   - `Rigid i`：**剛定数**(skolem)。束縛されることはなく、自分より浅いレベルへ漏れてはならない。

   型の中には、`TForall` にあたるノードが無い。
   量化子は、`Generic` の付いた変数が型のどこかにある、という形でしか表せない。
   これがそのままランク 1 多相の制限になる。
   同じ理由で、制約(`[A: Add]`)を型の中に書き残す場所も要らない。
   制約は変数に付いたまま、変数と一緒に量化される。

   `Rigid` は 2 つの役を兼ねる。
   `run h { ... }` のヒープをスコープに閉じ込める役と、
   型注釈の skolem 化(注釈より一般的な型でしか本体を受け付けない検査)の役である。
   どちらも同じ手順を踏む。
   レベルを上げて剛定数を作り、出口で剛定数が浅いレベルへ漏れていないかを調べる。
   単一化は未定変数のレベルを下げるが、剛定数のレベルは下げず、
   下げる必要があればエラーにする(第8章 §8.3)。

   ### レベル

   レベルは、その型変数が何段目の束縛の内側で生まれたかを表す。
   本体をレベル + 1 で推論し、推論の後で、レベルが現在より高い未定変数だけを `Generic` にする。
   素朴な実装は環境の自由型変数を集めてそれ以外を一般化するが、
   環境の走査は深い入れ子で二乗の時間になる。
   レベルはこれを整数の比較 1 回に減らす、Rémy による古典的な最適化で、
   OCaml 自身の型検査器も同じ仕組みを使う。
   レベルは、剛定数の脱出検査にも使う(第8章)。

   ### 型の構成子

   - `TCon (c, args)`：名目型と組み込みスカラーの飽和形。
     宣言の中身(コンストラクタの並び)は型に埋め込まない。
     埋め込むと、再帰型で一般化とインスタンス化が止まらなくなる。
     中身は第6章の宣言表が持つ。
   - `TApp (f, a)`：高階カインドのための適用。頭が型変数のときにしか現れない。
     この不変条件は §1.7 の `tapp` と `repr` が守る。
   - `TArrow (params, ret, eff)`：矢印は 3 つ組である。
     第1成分は引数、第2成分は返り値、第3成分はエフェクト行である。
   - `TRecord row` / `TVariant row`：行を 1 個包むだけの構成子。
   - `TRowEmpty` / `TRowExtend (label, field, rest)`：行の本体。
     尾部が `TRowEmpty` なら閉じた行、型変数なら開いた行である。
     開いた行は、レコードなら「そのラベルを含み、ほかは未定」、
     エフェクト行なら「そのエフェクトを起こしうる」を意味する。
     同じラベルの重複を許すのが Scoped Labels で、
     lacks 制約を持たない代わりに最左一致で解決する(第8章)。

   ### 引数をレコードにする理由

   `TArrow` の第1成分は、`_item` ラベルだけを積んだ閉じた行を `TRecord` で包んだものである。
   `(A, B) => C` の引数は `{_item: A, _item: B}` になる。

   これで得られるものは次の 3 つである。

   - arity の検査が、閉じた行の単一化から自動的に出てくる(sample.kel:190-191)。
   - ラベル付きの引数 `Cons(tail = t)` が同じ経路に乗る。
   - タプルが行の糖衣になり、`fst[A, R](t: {_item: A extends R})` のような「タプルの前置多相」が、
     レコードの行多相と同じ機構で通る。

   そのため、型にも AST にも値の表現にも、タプル専用の構成子は無い。

   一方で、矢印はエフェクト行を持つ専用のノードなので、2 引数の型構成子として分解できない。
   Haskell の `Functor ((->) r)` のように、
   関数型そのものを部分適用して高階カインドのインスタンスにすることはできない。 *)

  type ty =
    | TCon of oid * ty list (* 名目/組込み構成子の飽和形 *)
    | TApp of ty * ty (* HKT。頭が型変数のときだけ現れる(repr が保証) *)
    | TArrow of ty * ty * ty (* 引数(_item 行の TRecord)* 返り値 * エフェクト行 *)
    | TRecord of ty
    | TVariant of ty (* 構造的ヴァリアント。行 1 個 *)
    | TRowEmpty
    | TRowExtend of oid * ty * ty (* label * field(エフェクトならラベル引数)* rest *)
    | TVar of tvar ref

  and tvar = Unbound of var_info | Link of ty | Generic of var_info | Rigid of var_info

  (* ---- kind ---- *)

(* ## 1.6 カインドの単一化と既定化

   カインドが `KVar` を持つので、カインドの比較はすべて単一化になる。
   構造の等しさ(`=`)で比べると、未解決の `KVar` は、
   同じ変数どうしでない限りどのカインドとも一致しない。

   `same_kind` は、一致するかどうかを返し、一致させるために `KVar` を張れるなら張る。
   返り値が `bool` なのは、呼び出し側がカインドの不一致を自分のエラーメッセージで報告するためである。
   たとえば第8章の `bind` は、どちらのカインドが期待でどちらが実際かを知っている。

   ### 構造の一致を使わない理由と、既定化の時期

   第8章の `rewrite_row` は、変数が行変数かどうかを、
   `vkind = KRow` の構造の一致ではなく `same_kind` で判定する。
   arity 0 の型パラメータには `new_kind_var ()` が与えられるので、
   行の位置で使われた変数のカインドは、`KVar` が `KRow` へリンクした形をしている。
   構造の一致はこの形を取りこぼす。
   構造の一致で判定すると、次の 2 つが型検査で落ちる。
   1 つは sample.kel:195 の `fst` に `{x = 1, _item = ...}` を渡す形で、
   :201-203 のコメントがこれを説明している。
   もう 1 つは :210-215 の `describe` で、`describe(#Other)` の形である。
   `describe(#Other)` の例は仕様の本文ではなく、回帰テスト test/verify_fixes.t にある。
   カインドを直接パターンで調べている箇所は、それだけで誤りの候補である。

   `default_kind` を呼ぶ時期は、型パラメータの種類で異なる。
   newtype と型エイリアスのパラメータは、第11章のパス 1b の後始末で既定化する。
   let の型パラメータ、extern の型パラメータ(§11.40)、前提つきインスタンスの頭の束縛子(§11.38)は、
   剛定数として作るので、`release_rigids` が剛定数を解放するとき(§11.27)に既定化する。
   クラスメソッドの型パラメータは、メソッドの型を組み立てた直後(§11.33)に既定化する。
   呼ばないと、`?k7` のような未解決のカインドが表示に漏れ、
   使われる位置の無い型パラメータのカインドがいつまでも決まらない。

   既定化は早すぎてもいけない。
   `same_kind` は未解決の `KVar` どうしを片方に張るので、宣言を 1 つ検査するたびに既定化すると、
   まだ本体を読んでいない別の宣言のカインド変数まで、張られた先をたどって `KStar` に固定される。
   たとえば、互いを参照する newtype `A2[E] = MkA(B2[E])` と `B2[E] = MkB(() => Unit @ E)` で、
   先に処理した `A2` を既定化すると、その時点で `B2` の `E` まで `Type` になる。
   そのため、newtype と型エイリアスの既定化は、
   パス 1b が宣言群をすべて処理し終えるまで待つ(§11.39)。

   `show_kind` は Keleut の表記(`Type` / `Row` / `[_, _] Type`)に合わせる。
   `?k` の付いた表記は、既定化の前にしか現れないはずのものである。 *)

  let rec kind_repr = function
    | KVar ({ k_link = Some k; _ } as r) ->
        let k' = kind_repr k in
        r.k_link <- Some k';
        k'
    | k -> k

  let new_kind_var () = KVar { k_id = new_oid (); k_link = None }

  (* arity 個の * を取る構成子カインド: k_arrow 1 = KArrow (KStar, KStar) *)
  let rec k_arrow arity = if arity = 0 then KStar else KArrow (KStar, k_arrow (arity - 1))

  (* 単一化しつつ一致するかを返す。KVar は相手に破壊的に張る *)
  let rec same_kind a b =
    match (kind_repr a, kind_repr b) with
    | KStar, KStar | KRow, KRow -> true
    | KArrow (a1, a2), KArrow (b1, b2) -> same_kind a1 b1 && same_kind a2 b2
    | KVar r1, KVar r2 when r1 == r2 -> true
    | KVar r, k | k, KVar r ->
        r.k_link <- Some k;
        true
    | _ -> false

  (* 未解決の KVar を KStar へ既定化する(呼ぶ時期は §1.6) *)
  let rec default_kind k =
    match kind_repr k with
    | KVar r -> r.k_link <- Some KStar
    | KArrow (a, b) ->
        default_kind a;
        default_kind b
    | KStar | KRow -> ()

  let show_kind k =
    match kind_repr k with
    | KStar -> "Type"
    | KRow -> "Row"
    | KArrow _ as k ->
        (* F[_] 形式: 引数の個数だけ _ を並べる *)
        let rec args = function KArrow (a, b) -> a :: args (kind_repr b) | _ -> [] in
        let n = List.length (args k) in
        "[" ^ String.concat ", " (List.init n (fun _ -> "_")) ^ "] Type"
    | KVar r -> "?k" ^ string_of_int r.k_id

  (* ---- ty ---- *)

(* ## 1.7 型適用の正規化

   高階カインドのための型の構成子は `TApp` 1 つだけである。
   ただし、`TCon (c, args)` をすべて適用の連鎖(スパイン)で表すと、
   宣言表からクラス制約の伝播まで、`TCon` を扱う箇所をすべて書き換えることになる。
   そこで、関数位置が型変数のときだけ `TApp` を残す正規化を採る。
   頭が具体的な構成子なら、飽和形の `TCon` に畳む。

   `tapp` は、この畳み込みを行うスマートコンストラクタである。
   `repr` は、後から頭が決まった場合に畳み直す。
   `TApp (α, Int32)` の後で `α := List` が決まったら、次に `repr` した時点で `List[Int32]` になる。
   以降の関数は、まず `repr` してから `match` するのを基本形とする。
   そのため、`tapp` と `repr` の数行だけで、正規化が実装全体に行き渡る。

   `repr` の仕事は 3 つある。
   `Link` の連鎖をたどって代表元を返すこと、たどりながら経路を圧縮すること、
   `TApp` の頭を正規化し直すことである。
   経路を圧縮しなくても答えは変わらないが、深い連鎖で計算量が悪化する。
   `f' == f` の物理等価の判定は、
   頭が変わらなかったときに新しいノードを割り当てないためのものである。

   `repr` が正規化するのは 1 段だけである。
   `TApp (f, a)` の `a` には触らないので、必要な場所でそれぞれ `repr` する。

   ### 一階の単一化で済む理由

   型変数が適用の関数位置に来ると、`F[A] ~ List[Int32]` には解が複数ありそうに見える。
   しかし、型レベルのλが無ければ、解は 1 つに決まる。

   - `F := List, A := Int32` だけが解になる。
   - `F := λx. List[Int32]`(A を捨てる)や `F := λx. List[x]` は、λが書けないので候補にならない。

   つまり、`F[A] ~ G[B]` は `F ~ G, A ~ B` に構造的に分解でき、mgu は 1 つである。
   Haskell の高階カインドが一階の単一化で済んでいるのも、同じ理由による。
   本実装は次の 2 つの規則を守る。

   1. 型レベルのλを持たない。
   2. 部分適用できる型シノニムを持たない(実質的に型レベルのλだからである)。

   どちらかを破ると、単一化の解が一意でなくなり(unitary でなくなり)、主要型も失われる。
   Keleut の `type` 宣言が再帰せず、部分適用もできないのは、規則 2 を言語仕様の側で守るためである。
   第11章の `expand_alias` がこれを検査する(§11.5)。

   `app_spine` は、`TApp` の連鎖を頭と引数の列に平らにする。
   表示(第9章)と、型クラスのディスパッチ(第11章、第14章)が使う。 *)

  (* TApp の正規化: 頭が飽和形の TCon なら引数に畳む *)
  let tapp f a = match f with TCon (c, args) -> TCon (c, args @ [ a ]) | f -> TApp (f, a)

  (* Link の連鎖の経路圧縮と、TApp の頭の再正規化。
     以降の関数は、まず repr してから match するのを基本形とする *)
  let rec repr ty =
    match ty with
    | TVar ({ contents = Link t } as r) ->
        let t' = repr t in
        r := Link t';
        t'
    | TApp (f, a) ->
        let f' = repr f in
        (match f' with TCon (c, args) -> TCon (c, args @ [ a ]) | _ -> if f' == f then ty else TApp (f', a))
    | t -> t

  (* TApp 連鎖を (頭, 引数列) に分解 *)
  let rec app_spine ty =
    match repr ty with
    | TApp (f, a) ->
        let h, args = app_spine f in
        (h, args @ [ a ])
    | t -> (t, [])

(* ## 1.8 行を分解する

   行に対する操作は次の 3 つだけで、レコード、タプル、ヴァリアント、エフェクトのすべてをまかなう。

   `row_fields` は、行をフィールドの列と尾部に分解する。
   尾部は `TRowEmpty`(閉じた行)か型変数(開いた行)のどちらかである。
   開いた行 `{x: Int32 | ρ}` は「x を含み、ほかは未定」を意味し、行多相はこの形で表す。

   `row_tail_var` は、尾部が変数ならその変数を返す。
   第10章は構造的ヴァリアントの網羅性を判定するとき、ほかのケースはもう来ないと確定させるために、
   この変数を `TRowEmpty` へ束縛する。
   これが行を閉じる操作である。

   `row_append` は、`a` のフィールドを `b` の前に積む(splice)。
   これを使うのは第11章の 3 か所である。
   ヴァリアント和 `#A | #B | R` の連結(§11.4)、
   開いた行に展開されるエイリアスの splice(§11.5 の `splice_row`)、
   明示したエフェクト注釈の行を剛定数で開く `open_explicit_eff`(§11.26)である。
   `a` が閉じていることは、どの呼び出し側でも第11章が検査している。
   `row_append` は、左側が開いていて右側が空でなければ `bug` を呼ぶ。
   右側が空なら、左側をそのまま返す。
   ここで型エラーではなく `Panic` を投げるのは、
   これが利用者の誤りではなく実装の不変条件違反だからである。
   この使い分けは、§1.18 の `Type_error` と `Panic` の 2 つの例外に対応する。 *)

  (* 行を (フィールド列, 尾部) に分解。尾部は TRowEmpty か TVar *)
  let rec row_fields ty =
    match repr ty with
    | TRowExtend (l, f, rest) ->
        let fs, tail = row_fields rest in
        ((l, f) :: fs, tail)
    | t -> ([], t)

  let row_tail_var ty = match snd (row_fields ty) with TVar r -> Some r | _ -> None

  (* a のフィールドを b の前に積む(splice)。a は閉じている前提(elab が検査) *)
  let rec row_append a b =
    match repr a with
    | TRowExtend (l, f, rest) -> TRowExtend (l, f, row_append rest b)
    | TRowEmpty -> b
    | t -> ( match repr b with TRowEmpty -> t | _ -> bug "row_append: open row on the left")

(* ## 1.9 変数を作る

   `new_var` の既定は、カインドが `KStar` で制約なしである。
   `new_row_var` は、カインドを `KRow` にした別名である。
   名前が付いているので、行変数を作るつもりで `KStar` の変数を作る誤りを、読んで見つけられる。

   剛定数は `new_rigid_ref` と `new_rigid` の 2 段で作る。
   剛定数を作る場所は、`run` のヒープ、注釈の型パラメータ、明示したエフェクト注釈と pub の尾部、
   インスタンス検査の skolem 化と、複数ある。
   このうち注釈の型パラメータと、明示したエフェクト注釈と pub の尾部は、`new_rigid_ref` で作る。
   これらは `release_rigids` が後から中身を `Generic` に書き換える(第11章 §11.27)ので、
   `ref` そのものが要る。
   `run` のヒープとインスタンス検査の skolem 化(第8章の `skolemize`)は、
   型だけで足りるので `new_rigid` で作る。
   制約は、どちらの関数にも `?classes` で渡す。
   `new_rigid` は `new_rigid_ref` の結果を `TVar` で包むだけなので、
   `Rigid` を組み立てる式は `new_rigid_ref` の 1 か所にしかない。 *)

  let new_var ?(kind = KStar) ?(classes = []) level =
    TVar (ref (Unbound { vid = new_oid (); vlevel = level; vkind = kind; vcls = classes }))

  let new_row_var level = new_var ~kind:KRow level

  (* 剛定数のセル。release_rigids のように後から中身を書き換える側は
     ty ではなくこの ref を持つ必要がある(第11章 §11.27) *)
  let new_rigid_ref ?(kind = KStar) ?(classes = []) level =
    ref (Rigid { vid = new_oid (); vlevel = level; vkind = kind; vcls = classes })

  let new_rigid ?(kind = KStar) ?(classes = []) level = TVar (new_rigid_ref ~kind ~classes level)

  (* ---- 組み込み名 ---- *)

(* ## 1.10 組み込みの名前

   ここに並ぶ `oid` は、実装のあちこちから名指しされる少数の名前である。

   `l_item` はタプルのラベルである。
   `(1, 2)` の型は `{_item: Int32, _item: Int32}` になる。
   `t._0` は、第3章が「`_item` を 0 回取り除いてから `_item` を選ぶ」式に脱糖する。
   同じラベルを重ねて位置で数えるのが、Scoped Labels の上でのタプルの実装である。

   組み込みのスカラー型は `Boolean` / `Int32` / `Int64` / `Float64` / `String` / `Never` の 6 つだけである。
   `Never` はコンストラクタが 0 個の名目型で、`n match {}` が網羅と判定される根拠になる(第10章)。
   ほかの数値の幅(`Int8`、符号なし、`Float32`)は、名前と接尾辞を受理したうえで、
   第11章が未実装エラー(終了コード 4)で拒否する。

   `t_unit` には名目型を使わない。
   Unit は空レコードである(sample.kel:59, :167)。
   `()` と `{}` は同じ型で、単一化はレコードの経路にそのまま乗る。
   `Unit` という名前は、プレリュードの型エイリアスとしてだけ存在する(第15章)。

   `cls_integral` / `cls_fractional` は予約述語(§1.4)である。
   第11章は利用者による宣言を拒否し、
   第8章はこれらの付いた変数を一般化せずに既定の型 `Int32` / `Float64` へ落とす。
   既定化を一般化より先に行うので、これらの述語は通常は表示に現れない。

   `eff_heap` / `eff_blocking` は、操作を持たない組み込みのエフェクトラベルである。
   操作を持たないエフェクトそのものは、文法が空の本体を許すので、
   `effect Silent = {}` のようにソースにも書ける。
   それでも第6章は、この 2 つを表へ直接登録する。

   `Heap` は、`run` が導入し、`Ref` と `MutableArray` の操作が要求するラベルである。
   Keleut のエフェクト宣言はパラメータを取らない。
   §1.17 の `ef_params` は場所だけ空いており、空でなければ第11章が拒否する。
   一方、型式の側では `@ {Heap[h]}` と書けるので、
   `Ref` / `MutableArray` の操作の型を、`extern` の署名として書くこと自体はできる(第6章 §6.11)。
   それでも §6.11 がこれらの操作の型をまとめて組み立てるのは、実装が OCaml 側の値と切り離せず、
   プレリュードに置くと二重管理になるからである。
   `Blocking` は同じ組み込みの表に入るラベルで、
   `extern` がブロックしうることを表明するために名指しする(sample.kel:792, :808)。

   ### 予約型名

   組み込みの型名を `newtype Boolean = Yes` のように再宣言できると、新しいデータ型として登録され、
   網羅性検査と組み込みのインスタンスが両方とも壊れる。
   そのため、第6章の予約型名の表(`reserved_type_names`)が再宣言を拒否する。
   第6章はこの表を、本節の定数からではなく、文字列から `intern` し直して作る。
   そのため、組み込みの名前を 1 つ足すときは、第1章と第6章の 2 か所を直す。
   `t_never` は定数の並びをそろえるための 1 行である。
   `Never` の名前は第6章の `add_data` が登録するので、この定数自体はどこからも使われていない。 *)

  let l_item = intern "_item" (* タプルのラベル(sample.kel §4) *)

  let t_boolean = TCon (intern "Boolean", [])

  let t_int32 = TCon (intern "Int32", [])

  let t_int64 = TCon (intern "Int64", [])

  let t_float64 = TCon (intern "Float64", [])

  let t_string = TCon (intern "String", [])

  let t_never = TCon (intern "Never", [])

  (* Unit は名目型ではなく空レコード(sample.kel:59, :167)。
     プレリュードの型エイリアスとしてのみ名前を持つ *)
  let t_unit = TRecord TRowEmpty

  (* 予約述語。利用者の宣言は拒否し、一般化せず既定の型に落とす *)
  let cls_integral = intern "Integral"

  let cls_fractional = intern "Fractional"

  (* 操作なしの組み込みエフェクトラベル。decls.ml が Ref/Array/MutableArray の
     操作と一緒に直接登録する(理由は §1.10) *)
  let eff_heap = intern "Heap"

  let eff_blocking = intern "Blocking"
end

(* ## 1.11 リテラルと演算子

   ここで `Type` を出て、表層の構文の側へ移る。

   数値リテラルは、字句のテキストをそのまま保持する。
   多倍長整数のライブラリは使わない。
   `0xff` も `0b1010` も `1_000` も、文字列のまま持っておけば `Int32.of_string` が解釈できる。
   値にするのは評価のときで、そのとき第11章が決めた型を見る。
   そのため、既定化の結果がそのまま実行に反映される。
   `1 + 2` の `Integral` が `Int32` に落ちたことを、評価器はテキストと型から知る。
   負のリテラルは、第3章が `HYPHEN NUMBER` を畳んで作る。

   `n_suffix` は `1i64` / `1u8` / `1f32` の接尾辞である。
   Diktor の実行時の数値型は `Int32` / `Int64` / `Float64` の 3 種だけで、
   ほかの幅は字句としては受理し、第11章が未実装エラー(終了コード 4)で拒否する。
   `n_suffix_text` は接尾辞の原文(無ければ空文字列)で、診断とダンプはこちらを使う。
   解釈済みの `n_suffix` から表記を組み立て直すと、
   桁あふれの幅や先頭のゼロ(`1i032`)の字面が失われる(第2章 §2.1)。

   数値パターンの重複は、値で正規化してから検出する。
   `0x1` と `1` は同じパターンである(第10章)。
   テキストのまま比べると、重複を取りこぼす。
   同値の判定は、字面を `Int32`、`Int64`、`Float64` の 3 通りで読んだ値の組で行う(第10章 §10.3)。
   どの読みでも等しい字面だけを同じパターンとみなし、浮動小数の読みでは ±0.0 を同じ値とする。
   この判定は実行時の照合より細かいので、違う値を同じパターンとみなすことはない。
   その代わり、実行時には同じ値になる組の重複を見逃す(Int32 の列の `0xFFFFFFFF` と `-1`)。

   `bin_op` は、仕様の演算子表(sample.kel:365-369)の縮小版である。
   演算子は `Apply` に脱糖しない。
   理由は 2 つある。
   `&&` と `||` は短絡評価するので関数呼び出しにできないこと、
   `!=` は `Eq.eq` の否定であって `Ne` というメソッドが無いことである。
   この 2 つの例外を表の中に閉じ込めるために、AST に演算子のノードを残し、
   第11章と第14章が第7章の同じ表を引く。
   エラーメッセージが演算子の姿を保てる、という利点もある。
   剰余 `%` は仕様の演算子表に無いので入れない(プリミティブとして提供する)。

   なお、Float の表示は最短往復表現で、有限値なら Float64 リテラルとして読み戻せる(第12章 §12.7)。
   絶対値が 1e16 以上の値の最短表現は、
   `12345678901234568` のように小数点も指数も持たないことがある。
   Keleut ではこの字面が整数リテラルになるので、表示器は `.0` を補う。
   非有限値(inf / nan)にはリテラルが無いので、往復の対象外である。 *)

type num_suffix = NsInt of int | NsUInt of int | NsFloat of int (* i64 / u8 / f32 *)

type number = { n_text : string; n_is_float : bool; n_suffix : num_suffix option; n_suffix_text : string }

type bin_op = Add | Sub | Mul | Div | Eq | Ne | Lt | Le | Gt | Ge | And | Or

(* ## 1.12 型パラメータの束縛子

   `[A]` / `[h]` / `[F[_]]` / `[A: Add + Mul]` を 1 つのレコードで受ける。

   `tp_name` は大文字でも小文字でもよい。
   仕様 §0 が、識別子の大文字と小文字の規則から型パラメータを外しているからである。
   慣習として、型は大文字、リージョン変数は `run h { ... }` の `h` のように小文字で書く(sample.kel:50-51)。
   仕様 §10 の署名一覧がその例である。
   型変数と値の識別子は文法上の位置で区別できるので、字句で分ける必要はない。

   `tp_arity` が 0 のとき、カインドは `KVar` になる。
   §1.3 で述べた、使われた位置でカインドを決める仕組みの入口がここである。
   `F[_]` と書けば `tp_arity = 1` になり、`KArrow` が確定する。
   この規則は `let` の束縛子にも newtype の束縛子にも当てはまる。

   例外は型クラス自身のパラメータ(`type class C[A]` の `A`)で、
   `tp_arity` が 0 なら `KStar` に固定する(§11.33)。
   クラスのパラメータでも、`[F[_]]` と書けばカインドは `[_] Type` になる。
   インスタンスは型構成子のタグで選ぶので、行をパラメータに取るクラスは意味を持たない。
   仕様 §8 がこれを定めている(sample.kel:358-360)。
   エフェクトについて量化したいときは、クラスのパラメータではなく、
   メソッドの型パラメータに行変数を取る(sample.kel:361-362)。
   第11章は、クラスのパラメータを行として使う形を拒否し(`test/kinds.t` の classrow / classrow2)、
   メソッドの型パラメータに行変数を取る形は受理する(classrowok)。

   束縛子にカインドの注記を書く構文(`[E: EffectRow]` のような書き方)は無い。
   `tp_arity` が 0 の束縛子のカインドは、
   宣言群の中の型の本体での使われ方からしか決まらない(sample.kel:246-247)。
   使われ方が無ければ `KStar` に既定化されるので、行カインドの phantom パラメータを書く手段は無い。
   仕様 §14 は、この注記の構文を TODO として残している(sample.kel:872-874)。
   カインドを書けるのはエイリアスの側だけである(`type Request: EffectRow`)。

   `tp_classes` は `long_id list` である。
   ただし、第3章の `cls_list` はクラス名として大文字の識別子 1 つしか受け付けない。
   そのため、要素は常に成分 1 つの経路になり、`[A: Prelude.Add]` は構文エラーになる。 *)

type type_param = {
  tp_name : string; (* 大文字/小文字どちらも可(リージョン変数 h 用) *)
  tp_arity : int; (* F[_] なら 1。0 ならカインドは KVar(使用位置から推論。型クラス自身のパラメータだけは KStar 固定) *)
  tp_classes : long_id list;
}

(* ## 1.13 Data ファンクタ

   AST の全ノードは `Data.t * ノード` の組である。
   `Data` を差し替えることで、同じ AST の定義を、注釈の異なる木として使い回す。

   - `EmptyData` は `t = unit` で、注釈を一切持たない最小の実体化である。
     本実装はどこからも `EmptyData` を使っていない。
     `Data` を差し替えられるという性質を、
     散文ではなくコードで示すためだけに置いてある(§3.1 も同じ例を指す)。
   - 第5章の `Tree.ElabData` は `{ oid; loc; mutable ty_field; mutable resolved }` である。
     位置に加えて、推論した型と解決結果を書き込む欄を持つ。

   第3章のパーサは、Menhir の `%parameter <Data : Syntax.Data>` で同じように仮引数化されており、
   第16章のドライバが `Parser.Make (Tree.ElabData)` で実体化する。
   つまり、パース木がそのまま精緻化木になり、変換のためのコピーは 1 回も起きない。
   これが成り立つのは、`Syntax.Make` がアプリカティブファンクタ(同じ引数から作れば同じ型になる)だからである。
   ジェネレータ側とライブラリ側で別々に `Syntax.Make (ElabData)` と書いても、型が一致する。

   `allocate` は `Location.span` を受け取る。
   エラーに位置を出すには全ノードに span が要り、
   後から足そうとすると全ノードの構築箇所を書き換えることになる。

   代償として、パターンマッチはすべて `(_, Ident ...)` の形になり、読みにくくなる。 *)

module type Data = sig
  type t

  val allocate : Location.span -> t
end

module EmptyData : Data = struct
  type t = unit

  let allocate _ = ()
end

module Make (Data : Data) = struct
  (* ---- 型式 ---- *)

(* ## 1.14 型式

   `type_exp` は表層に書かれた型の構文であり、§1.5 の `ty` ではない。
   両者を分けるのは、表層の名前がまだ何を指すか分からないからである。
   第11章の `elab_type` が、環境を見ながら `ty` へ変換する。

   `EIdent` は、型変数、型構成子、型エイリアス、エフェクト名のどれでもありうる。
   区別は環境が持ち、字句や文法では決まらない。
   `E` という 1 文字が、束縛子にあれば行変数、宣言表にあればエフェクトである。

   `EBraceRow` 1 つで、レコード型、エフェクト行、`EffectRow` エイリアスの本体を受ける。
   これらを別のノードに分けると、`@ {..}` の位置で reduce/reduce 衝突が起きる。
   そこで、要素の形(`BField` か `BLabel` か)で意味を読み分ける。

   `EArrow` の第3成分が `None` なら、`@` を省略している。
   省略の意味は文脈で決まる。
   入れ子の矢印で省略した `@` は `@ {}` に確定する(第11章 §11.4)。
   前方参照に使える署名になるのは、
   注釈の頭の矢印に `@` を明示した(または `pub` を付けた)束縛だけである(§11.36)。
   省略をこのように扱うのは、省略した `@` ごとに独立な行変数を作ると、
   本体を見ずに作った署名の中でその行変数が何にも縛られないまま一般化され、
   宣言の順序によってはエフェクト検査が抜け落ちるからである。

   `EUnion` は、`#A | #B | R` と `IoError | ParseError` の両方を受ける。
   構造的ヴァリアントの合併とエフェクト行の合併を同じ縦棒で書くので、AST では区別しない。

   `EHole` は `List[_]` の穴である。
   パーサが `EHole` を作るのは型引数の位置だけで、
   実際の用途は `type instance` の頭(`type instance Functor[List[_]]`)に限られる。
   `F[_]` の束縛子の `_` は `EHole` にならない。
   そちらは穴の個数を数えて、§1.12 の `tp_arity` にする。
   インスタンスの頭以外の型引数の位置に現れた `EHole` は、第11章が型エラーにする。 *)

  type type_exp' =
    | EIdent of long_id (* 型変数・構成子・エイリアス・エフェクト名。区別は環境 *)
    | EApply of type_exp * type_exp list (* List[A] / F[A] *)
    | EArrow of type_exp list * type_exp * type_exp option (* (A, B) => C @ E。@ 省略は None *)
    | EBraceRow of brace_elem list * type_exp option (* { ... extends T }。要素の形で意味が決まる *)
    | EVariantCase of string * type_exp option (* #Foo(T) / #Foo *)
    | EUnion of type_exp list (* #A | #B | R / IoError | ParseError *)
    | EHole (* List[_] の穴。型引数位置のみ。instance 頭で使う(F[_] 束縛子は tp_arity) *)

  and type_exp = Data.t * type_exp'

  and brace_elem =
    | BField of string * type_exp (* x: Float64 / read: () => String *)
    | BLabel of long_id * type_exp list (* Print / Heap[h] / ReqId(エフェクト行・行 splice) *)

  (* ---- パターン ---- *)

(* ## 1.15 パターン

   `PRecord` がレコードとタプルの両方を受け持つ。
   第2要素の `pat option` だけで、次の 3 つの状態を表す。

   | 第2要素 | 意味 | 書かれ方 |
   |---|---|---|
   | `None` | 閉じた行 | タプルパターン。arity を検査する |
   | `Some (_, PWildcard)` | 開いた行で、尾部は捨てる | レコードパターンの既定 |
   | `Some p` | 開いた行で、尾部を `p` に束縛する | `{x, ...rest}` |

   レコードパターンは既定で開いていて、タプルパターンは閉じている。
   仕様のこの違いを、コンストラクタを増やさずに表せる。

   `PCtor` は名目コンストラクタのパターンだが、`handle` の節の頭にも使う。
   `write(msg) => ...` は、構文の上ではコンストラクタパターンと区別できないからである。
   どちらなのかは第11章が分類し、結果を第5章の `resolved` に書き込む。
   ラベル指定の引数(`Cons(tail = t)`)があるので、
   実引数の位置とフィールドの位置の対応表も `resolved` に入る。

   `PAnnot` はパラメータの型注釈だけに使う。
   式のレベルの注釈ノードは持たない。
   `let b: Int64 = 0` の注釈も、関数の返り値とエフェクトの注釈も、
   すべて §1.16 の `let_binding` のフィールドに置く。
   skolem 化の検査が束縛 1 つを単位に走るので、注釈も束縛に集めるほうが素直である。

   `as` パターンは Keleut の表層構文に無いので、AST にも無い。
   or パターン、遅延パターン、リストや配列のリテラルパターンも持たない。
   Unit のパターンにも専用のノードは無く、`PRecord ([], None)` で表す。
   §1.10 で述べたとおり、Unit は空レコードだからである。 *)

  type pat' =
    | PWildcard
    | PVar of string
    | PBool of bool
    | PNumber of number
    | PText of string
    | PRecord of (string * pat) list * pat option
        (* レコード/タプル両用。第2要素: None = 閉じた行(タプルの arity 検査)、
           Some p = 尾部束縛(...rest)。開くだけなら Some PWildcard(レコードパターンの既定) *)
    | PCtor of long_id * ctor_arg_pat list (* 位置 / ラベル指定。handle 節の頭にも使う *)
    | PVariant of string * pat
    | PAnnot of pat * type_exp (* パラメータの型注釈 (p: Point) *)

  and pat = Data.t * pat'

  and ctor_arg_pat = { cap_label : string option; cap_pat : pat }

  (* ---- 式 ---- *)

(* ## 1.16 式と束縛

   式の形はおおむね素直なので、設計上の選択が形に現れている箇所だけを述べる。

   `Apply` の第2引数は常に引数レコードである。
   `f(1, 2)` は `Apply (f, {_item = 1, _item = 2})` になる。
   関数適用のノードは 1 引数のままで、arity は行が担う。

   `Construct` と `Variant` は別物である。
   前者は宣言された名目コンストラクタで、閉じた型を持ち、再帰型と型パラメータを使える。
   後者は構造的ヴァリアント `#Foo(e)` で、行多相の開いた型を持つ。
   後者のペイロードは常に 1 つの値で、
   複数に見えるものはタプル、つまり `_item` 行である。

   `RecordExtend` の評価順は value、rest である。
   フィールドの並びと逆なので、目で追うと間違えやすい。
   仕様(sample.kel:278)は、`{l = e extends r}` の `e` を先に、`r` を最後に評価すると定めている。
   第3章のタプルの脱糖は先頭を最も外側に置くので、
   この向きなら `(a, b, c)` は左の要素から順に評価される。
   第14章も同じ順で評価する。

   `RecordUpdate` が別のノードなのは、
   `{r with l = e}` が物理的なフィールドの順序を保つ必要があるからである。
   除去してから足し直すと順序が変わり、表示が変わる。

   `Match` のスクルティニは 1 つである。
   Keleut は後置の `v match { ... }` しか持たない。
   複数のスクルティニを持つように見える照合は、タプルに対する照合である。
   タプルは `_item` 行なので、この照合も 1 つのスクルティニに対する照合として扱える。
   網羅性検査のパターン行列も、入口では列数 1 である(第10章)。

   `resume` は名前ではなく、`Resume` という専用のノードで表す。
   構文が保証できるのは、`resume` を値として名前に束縛できないことまでで、
   `fn() => resume(x)` は書けてしまう。
   そのため、second-class であることを 2 段で守る。
   第11章が節の本体を走査してラムダの内側の `Resume` を拒否し、
   第14章が実行時に継続の生存フラグを見る。

   `Handle` の節は、`match` と共通の `clause` である。
   `return` 節、`cancel` 節、操作節の分類は第11章が行い、結果を `resolved` へ書く。
   パーサに分類させないのは、操作名の解決に宣言表が要るからである。

   `let_binding` は注釈を集める場所であり(§1.15)、関数定義のパラメータもここに持つ。
   `lb_params` が `None` なら値束縛、`Some ps` なら関数定義で、
   パーサは `Lambda` を作らずにパラメータをここに残す。
   関数定義かどうかは、この 1 つのフィールドを見るだけで決まる。
   第11章は、関数定義ならそのまま一般化し、
   値束縛なら右辺が構文的な値(§11.9 の `is_value`)のときだけ一般化する(値制限、§11.28)。

   ### LetRec の右辺

   `LetRec` の右辺に関数でない式を許すと、型検査を通ったプログラムが実行時に落ちる。
   そのため、第11章が関数でない右辺を拒否する。
   AST の側は任意の式を受け付ける。
   文法を狭めるより、検査を 1 か所に置くほうが、良いエラーメッセージを出せるからである。 *)

  type exp' =
    | Bool of bool
    | Number of number
    | Text of string
    | Ident of long_id (* 変数・パス参照。裸の ctor も *)
    | Hole (* ??? *)
    | Apply of exp * exp (* 第2引数は常に引数レコード *)
    | Construct of long_id * ctor_arg list (* Some(1) / Cons(tail = t)。ラベル付き引数 *)
    | Variant of string * exp (* #Foo(e)。ペイロードは常に単値 *)
    | BinOp of exp * bin_op * exp (* elab / interp が prims.ml の表を引く *)
    | Not of exp (* ! のみ *)
    | Lambda of lambda (* fn(x, y) => e *)
    | Let of let_binding * exp
    | LetRec of let_binding list * exp
    | Seq of exp list (* 式文の列。let を含むブロックは Let(b, 残り) の入れ子 *)
    | Match of exp * clause list (* スクルティニは 1 つ *)
    | RecordEmpty
    | RecordExtend of exp * string * exp
        (* (rest, label, value)。評価は value → rest の順(sample.kel:278) *)
    | RecordUpdate of exp * string * exp (* {r with l = e}。物理フィールド順保持のため専用ノード *)
    | RecordRestriction of exp * string (* r \ l *)
    | RecordSelection of exp * string
    | Perform of long_id * exp (* perform print(msg)。解決済み完全名は resolved へ *)
    | Handle of exp * clause list
        (* 節は match と共通。分類は elab が行い、resolved へ書く *)
    | Resume of exp option (* resume() / resume(e)。引数は record_of_args を通さない *)
    | Run of string * exp (* run h { ... } *)

  and exp = Data.t * exp'

  and ctor_arg = { ca_label : string option; ca_exp : exp }

  and lambda = { l_params : pat list; l_body : exp }

  and clause' = { cl_pat : pat; cl_guard : exp option; cl_body : exp }

  and clause = Data.t * clause'

  and let_binding' = {
    lb_pub : bool;
    lb_name : pat; (* 関数定義なら PVar。値束縛はパターン可(match に脱糖) *)
    lb_tparams : type_param list; (* let f[A, E] の [A, E]。値束縛にも付けられる *)
    lb_params : pat list option; (* None = 値束縛。Some ps = 関数定義 *)
    lb_ret : type_exp option; (* : T *)
    lb_eff : type_exp option; (* @ E *)
    lb_body : exp;
  }

  and let_binding = Data.t * let_binding'

  (* ---- 宣言 ---- *)

(* ## 1.17 宣言

   トップレベル、`module` の本体、`type instance` の本体を、同じ `decl` 型で受ける。
   3 つとも宣言の並びだからである。
   例外は 2 つある。
   `type class` の本体は `val m: T` の並び、`effect` の本体は `op: (T) => U` の並びなので、
   専用のレコードを持たせる。

   設計上の選択が、AST の形や検査に現れている箇所を挙げる。

   - `cls_params` が 1 個であることは、第11章が検査する。
     多パラメータ型クラスを持たないという選択は、AST の形ではなく検査として現れる。
     文法は複数のパラメータを受け付けるので、エラーメッセージを書ける。
   - `ef_params` は、Keleut に対応する構文が無いフィールドである。
     型パラメータの非終端記号を共有しているので場所だけ空いており、空でなければ第11章が拒否する。
   - `ex_abi` は「prim」か「C」である。
     前者は組み込みプリミティブへの割り当て、後者は外部関数の呼び出し(FFI)である。
     Diktor が C リンケージで実装しているのは、
     既知の名前の数学関数 sin / cos / sqrt / exp / log だけである。
     実装は第13章 §13.4 に、型の契約は第6章 §6.2b にある。
     `extern` の再宣言は拒否する(§6.2)。
     再宣言を許すと、`__int32_add` のようなプリミティブに実装と異なる型を後から付けられ、
     型検査の結果が実装と食い違う。
   - `ex_prim` は実装名である。
     module の平坦化(第11章)は `ex_name` を `M.f` に修飾するが、
     `ex_prim` は修飾する前の元の名前のまま残る。
     実装表(第13章)の探索と、登録簿(第6章)のプレリュード保護は、こちらを鍵にする。
     修飾名を鍵にすると、プレリュード保護を module の中から迂回でき、
     module に包んだ既知名の FFI の実装も黙って見つからなくなる。
     二重宣言の検査だけは修飾名で行う(§6.2)。
     別々の module が同じ C シンボルを包む形を許すためである。
   - `nt_rhs` の `NtHole` は `= ???` である。
     `Never` はコンストラクタが 0 個、すなわち `NtCtors []` である。
   - `DModule` の平坦化は第11章が行う(改名と、修飾する前の名前から修飾名への同義語表)。
     module の入れ子と、module の中の effect 宣言、type class 宣言、式文は、
     Diktor が実装していない。
   - `DExp` はトップレベルの式文である(sample.kel:658)。
   - `ins_args` は通常 1 個で、`List[_]` のように `EHole` を含められる。
     本体が `let` だけであることは第11章が検査する。
   - `ins_tparams` は前提つきインスタンスの束縛子で、頭の `_` に左から順に対応する(仕様 §8)。
     専用の型は持たず、`type_param` を `let` / `class` / `newtype` と共有する。

   syntax.ml はここまでである。
   残りは補助の 2 ファイルで、§1.18(aux.ml)が通し番号と例外の語彙、§1.19(location.ml)が位置を扱う。
   その次の第2章(lexer.ml)が、この AST を組み立てるためのトークン列をソースから切り出す。 *)

  type type_alias' = {
    ta_pub : bool;
    ta_name : string;
    ta_params : type_param list;
    ta_kind : string option; (* : Type / : EffectRow。解釈は elab *)
    ta_body : type_exp;
  }

  type ctor_decl = { cd_name : string; cd_fields : field_decl list }

  and field_decl = { fd_label : string option; fd_ty : type_exp }

  type newtype_rhs = NtCtors of ctor_decl list (* Never は [] *) | NtHole (* = ??? *)

  type newtype' = { nt_pub : bool; nt_name : string; nt_params : type_param list; nt_rhs : newtype_rhs }

  type effect' = {
    ef_pub : bool;
    ef_name : string;
    ef_params : type_param list; (* Keleut にパラメータ構文は無い。非空は elab が拒否 *)
    ef_ops : (string * type_exp) list;
  }

  type class_val = { cv_name : string; cv_tparams : type_param list; cv_ty : type_exp }

  type class_decl' = {
    cls_pub : bool;
    cls_name : string;
    cls_params : type_param list; (* 1 個であることは elab が検査する *)
    cls_vals : class_val list;
    cls_derives : string list; (* derive structural *)
  }

  type extern_decl' = {
    ex_pub : bool;
    ex_abi : string; (* 「prim」 / 「C」 *)
    ex_name : string;
    ex_prim : string; (* 実装名 = 非修飾の元の名前。module 平坦化でも変わらない *)
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
    | DExp of exp (* トップレベル式文(sample.kel:658) *)

  and decl = Data.t * decl'

  and instance_decl' = {
    ins_tparams : type_param list; (* 前提つきインスタンスの束縛子。頭の _ に左から対応する *)
    ins_class : string;
    ins_args : type_exp list; (* 通常 1 個。List[_] の EHole 可 *)
    ins_body : decl list; (* let のみであることは elab が検査 *)
  }
end
