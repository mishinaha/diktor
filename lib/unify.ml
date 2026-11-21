(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第8章 単一化

   本章は、型推論の中心である単一化を実装する。
   第11章(elab.ml)が構文から読み取る要求は、
   最終的にすべて「この型とこの型を等しくする」という 1 つの命令になる。
   その命令を実行するのが本章の `unify` で、
   ほかの関数はこの命令を安全に実行するための前処理と後処理である。

   本章は、ほかの章が定める次の 3 つを使う。
   第1章(syntax.ml)が定める型、カインド、行の表現と、
   第6章(decls.ml)が持つ宣言表、クラス表、インスタンス表と、
   第5章(tree.ml)の §5.1b が定める、型クラスの制約の証拠を表す型である。
   証拠(evidence)は、どのインスタンスの辞書を使うかを表す項である。
   本章がほかの章に公開する主な関数と、それを使う章は次のとおりである。

   | 関数 | 使う章 |
   |---|---|
   | `unify` | 第11章(elab.ml)の全規則、第10章(exhaust.ml)の 2 か所 |
   | `add_class` | 第11章の数値リテラルへの予約述語の要求と、第16章(driver.ml)が対話的な実行の結果を表示するときの `Show` の有無の判定 |
   | `generalize` | 第11章の let 束縛と、宣言から作る型スキーム |
   | `check_ambiguity` / `default_numerics` | 第11章の let 束縛と宣言の終わり |
   | `lower_levels` / `class_mark` | 第11章の一般化しない let 束縛 |
   | `reset` | 第11章の検査の開始時と、パス 2 の直前 |
   | `instantiate` | 第11章の型スキームの使用箇所のうち、制約を持たない操作の型スキーム(perform と操作節) |
   | `instantiate_ev` / `constraints_of` / `dkeys_of` | 第11章の型スキームの使用箇所(変数参照、演算子、前置の `-`、インスタンス本体の包摂検査)と、束縛の辞書パラメータ |
   | `constraints_of` | 上の行に加えて、第14章(interp.ml)と第18章(ir_write.ml)がクラスメソッドの辞書の位置と個数を求める箇所 |
   | `hole_mark` / `solve_holes` / `solve_holes_range` / `unsolved_holes` | 第11章の束縛と宣言と単位の終わり |
   | `display_evidence` | 第16章(driver.ml)の対話的な実行の結果の表示 |
   | `subst_params` | 第10章と第11章でのコンストラクタのフィールドの展開 |
   | `rewrite_row` | 第11章の検査モード(§11.19)のレコード拡張の分岐 |
   | `kind_of` / `var_info_of` / `map_generics_with` | 第11章の型の補助関数 |
   | `is_predicate` | 第9章(show.ml)の制約の表示と、第10章と第11章での予約述語の判定 |
   | `show_ref` | 第9章が型の表示関数を代入する変数(§8.2) |

   `bind` もほかの章から見えるが、呼び出すのは本章の `unify` と、
   `generalize` と `default_numerics` が使う `default_to` だけである。
   ほかの章に向けた関数ではないので、§8.5 で内部の手続きとして扱う。
   第10章が `unify` を呼び出すのは、構造的ヴァリアントの行を閉じる箇所(§10.9)と、
   節のない `match` の照合対象の型変数を `Never` に決める箇所(§10.13)の 2 か所である。
   第10章は、それ以外の箇所では型を書き換えない。

   Keleut の型には、単一化の実装に影響する次の特徴がある。

   | 特徴 | 本章での扱い |
   |---|---|
   | 矢印が 3 要素 | `TArrow` は引数の閉じた `_item` 行、返り値、エフェクト行を持つ |
   | カインド変数がある | `KVar` があるので、カインドの比較には `same_kind` を使う |
   | 予約述語 | 数値リテラルの `Integral` / `Fractional` を、クラス制約と同じ集合に入れる |
   | `Rigid` が 2 役 | スコーレム定数(スコープの中で固定した型を表す定数。コードでは `Rigid`)が、`run` のリージョン変数と、注釈の検査で固定する型パラメータの両方を表す |
   | 多パラメータ型クラスを持たない | 型スキーム専用の型を持たない |
   | レベルは引数 | 現在のレベルを可変のグローバル変数に置かない |

   本章の関数はレベルをすべて引数で受け取り、
   `generalize` や `instantiate` が現在のレベルをグローバル変数から暗黙に読むことはない。
   そのため、ある宣言の処理が残したレベルが、次の宣言の処理に影響することはない。
   その代わり、呼び出し元は正しいレベルを渡す責任を負う。 *)

open Aux
open Syntax
open Type

(* ## 8.1 カインドの計算

   Diktor は、カインド検査のための専用のパスを持たない。
   型構成子のカインドは宣言表から引き、適用された引数の個数だけ矢印を取り除く。
   `kind_of` と `drop_arrows` が調べるのは結果のカインドだけである。
   矢印の定義域、つまり型引数が宣言のパラメータのカインドと合うかどうかは、精緻化の側で照合する。
   型構成子の適用では宣言表のカインドと照合し(第11章 §11.3 の `elab_con_args`)、
   高カインドの型変数への適用 `F[A]` では `F` のカインドと照合する。
   どちらも、型引数を読んだその場で照合する。

   `drop_arrows` には `KVar` の場合がある。
   Keleut の型パラメータの束縛子は、`[A]` も `[R]` も `[E]` も書き方が同じで、
   型なのか行なのかは使われた位置からしか分からない。
   `F[_]` のように `[_]` が書いてあるときだけ、その場でカインドが `KArrow` に決まる。

   そのため、型引数を適用する時点で、適用される型のカインドがまだ分からないことは普通に起きる。
   `drop_arrows` は `KVar` に出会うと、
   その `KVar` を `KArrow (新しいカインド変数, 新しいカインド変数)` に決めて先へ進む。
   本実装のカインド推論はこれだけである。
   ここで決めた定義域を型引数と照合するのは、上に書いたとおり精緻化の側である。
   `drop_arrows` 自身は矢印の左を捨て、右だけを返す。
   未解決のまま残った `KVar` は、第1章の `default_kind` が `KStar` に決める(既定化、defaulting)。
   既定化の時期は型パラメータの種類で異なり、第1章 §1.6 にまとめてある。

   `var_info_of` は、型変数の 4 つの状態(`Unbound` / `Generic` / `Rigid` / `Link`)から `var_info` を取り出す。
   `Link` を渡されたときは `bug` を呼び出し、処理系のバグとして報告する。
   `repr` を通した後の `TVar` は `Link` ではない、という不変条件をここで確かめるためである。
   本章で型の構造をたどる関数は、どれも先に型を `repr` する。
   `repr` を省く関数は 3 つある。
   `unbound_var` は、呼び出し元の `unify` が `repr` 済みの型を渡す前提で省く(§8.5)。
   `note_literal` と `new_class_var` は、作ったばかりの変数だけを受け取るので省く。 *)

let rec drop_arrows k n =
  if n = 0 then k
  else
    match kind_repr k with
    | KArrow (_, r) -> drop_arrows r (n - 1)
    | KVar r ->
        (* 使われた位置でカインドを確定させる *)
        let res = new_kind_var () in
        set_klink r (Some (KArrow (new_kind_var (), res)));
        drop_arrows res (n - 1)
    | KStar | KRow -> type_error "型構成子ではない型に型引数が適用されています"

let var_info_of r = match !r with Unbound i | Generic i | Rigid i -> i | Link _ -> bug "var_info_of: Link"

let rec kind_of t =
  match repr t with
  | TRowEmpty | TRowExtend _ -> KRow
  | TVar r -> (var_info_of r).vkind
  | TCon (n, args) -> drop_arrows (Decls.con_kind n (List.length args)) (List.length args)
  | TApp (f, _) -> drop_arrows (kind_of f) 1
  | TArrow _ | TRecord _ | TVariant _ -> KStar

(* ## 8.2 型の表示関数を後から差し込む

   本章のエラーメッセージは型を表示する。
   一方、表示を担当する第9章(show.ml)も、制約を表示するときに本章の `is_predicate` を呼び出す。
   2 つのモジュールが互いを参照することになるが、OCaml のモジュールは循環して参照できない。
   そこで本章は表示関数を `ref` の変数に入れて持ち、show.ml の末尾が起動時に実際の関数を代入する。

   代入の前に呼び出されても、`<型>` という文字列を返すだけで、異常終了はしない。
   型エラーの本文に `<型>` が並ぶときは、
   show.ml のトップレベルの初期化が実行されていない(show.ml がリンクされていない)。 *)

let show_ref : (ty -> string) ref = ref (fun _ -> "<型>") (* Show が後から代入する(モジュールの循環を避けるため) *)

let show t = !show_ref t

let show2_ref : (ty -> ty -> string) ref = ref (fun _ _ -> "<型>")

let show2 a b = !show2_ref a b

let show_pair_ref : (ty -> ty -> string * string) ref = ref (fun _ _ -> ("<型>", "<型>"))

(* 2 つの型を、型変数の名前の表を共有して文字列化し、別々の文字列として返す *)
let show_pair a b = !show_pair_ref a b

(* ## 8.3 occurs check、レベル調整、脱出検査

   型変数 `tv` に型 `t` を代入する前に、`occurs_adjust` が `t` を 1 度だけ走査して、
   次の 3 つを同時に行う。

   - **occurs check**：`t` の中に `tv` 自身が現れたら、無限型になるのでエラーにする。
   - **レベル調整**：`t` の中の単一化変数のレベルを、`tv` のレベルまで下げる。
   - **脱出検査**：`t` の中に `tv` より深いレベルのスコーレム定数があれば、エラーにする。

   レベル調整を省くと、型システムが不健全になる。
   内側の let で作られた深いレベルの変数が外側の浅いレベルの変数と単一化されたなら、
   その変数はもう内側だけのものではない。
   代入は変数の生存範囲を外側へ広げるので、レベルは両者の小さいほうに合わせる。

   スコーレム定数のレベルは下げられない。
   スコーレム定数は、導入したスコープの外では意味を持たない定数として作るものだからである。
   下げるとスコーレム定数をスコープの外へ持ち出すことになるので、下げる代わりにエラーにする。

   `Rigid` は 2 つの役を兼ねる。
   `run h { ... }` が導入するリージョン変数 `h` と、
   `let f[A](...)` の注釈を検査するときの `A` である。
   どちらも、導入したスコープの外へ漏らしてはならないという同じ性質を持つので、
   `occurs_adjust` は `Rigid` の場合 1 つで両方を検査する。
   第11章は、`run` の規則(§11.17)でも let 束縛の規則(§11.28)でも、スコーレム定数を次の手順で扱う。

   1. レベルを上げる
   2. スコーレム定数を作る
   3. 出口で、スコーレム定数が浅いレベルへ漏れていないかを調べる

   `Generic` が現れたときは、`type_error` ではなく `bug` を呼び出す。
   `Generic` は一般化済みの型スキームの中にしか現れない。
   単一化に渡されたなら第11章(elab.ml)が `instantiate` を呼び忘れており、
   ユーザのプログラムの誤りではなく処理系のバグである。

   脱出を報告するときは、スコーレム定数が型パラメータなら、その名前と漏れの原因を添える。
   型パラメータのスコーレム定数が浅いレベルの変数に代入されるのは、
   その変数の型がまだ決まっておらず、型パラメータのスコープの外の型と共有されているときである。
   外側の注釈のない引数の型や、一般化しない束縛の型がこれに相当する。
   スコープの中で作られた変数も、外側の変数と単一化されると共有され、レベルが下がる。
   スコーレム定数の表示 `ς1` だけでは、どの型パラメータがどこへ漏れたのかが分からない。
   名前は、第11章の `make_rigids` がスコーレム定数を作るときに `rigid_tparams` に登録する。
   `run` のリージョン変数とインスタンス検査のスコーレム定数は登録しないので、
   報告に名前を添えない。 *)

let rigid_tparams : (oid, string) Hashtbl.t = Hashtbl.create 16

let escape_message v (i : var_info) =
  let name = show (TVar v) in
  let base = "スコープ付きの型 " ^ name ^ " がスコープの外に漏れています" in
  match Hashtbl.find_opt rigid_tparams i.vid with
  | None -> base
  | Some n ->
      base ^ "(" ^ name ^ " は型パラメータ " ^ n ^ " です。" ^ n
      ^ " のスコープの外の型と共有された、型の決まっていない変数(注釈の無い引数の型や、一般化されない束縛の型など)に "
      ^ n ^ " を入れようとしています)"

let rec occurs_adjust tv lvl t =
  match repr t with
  | TVar v ->
      if v == tv then type_error "occurs check に失敗しました(無限型が発生します)";
      (match !v with
      | Unbound i -> if i.vlevel > lvl then set_tv v (Unbound { i with vlevel = lvl })
      | Rigid i ->
          (* スコーレム定数はレベルを下げられない。下げる代わりにエラーにする *)
          if i.vlevel > lvl then type_error (escape_message v i)
      | Generic _ -> bug "単一化中に Generic 変数が現れました"
      | Link _ -> ())
  | TCon (_, args) -> List.iter (occurs_adjust tv lvl) args
  | TApp (f, a) ->
      occurs_adjust tv lvl f;
      occurs_adjust tv lvl a
  | TArrow (p, r, e) ->
      occurs_adjust tv lvl p;
      occurs_adjust tv lvl r;
      occurs_adjust tv lvl e
  | TRecord row | TVariant row -> occurs_adjust tv lvl row
  | TRowEmpty -> ()
  | TRowExtend (_, f, rest) ->
      occurs_adjust tv lvl f;
      occurs_adjust tv lvl rest

(* ## 8.4 クラス制約の伝播

   Keleut の型クラスの制約は、型変数そのものが持つフィールド(`vcls`)で伝播し、
   文脈の簡約(context reduction)は単一化の途中でその場で決定的に終わる。
   修飾型は持たない。
   どのインスタンスを選んだかは、ここでは記録せず、§8.11 の証拠として束縛の終わりに木へ書く。
   `add_class` がインスタンスの有無を確かめ、§8.11 の `evidence_of` が同じ規則で証拠を作る。
   片方だけを変えてはならない。
   `add_class t c` は「型 `t` はクラス `c` のインスタンスでなければならない」という要求を、
   `t` の形で場合分けして解決する。

   最初にカインドを調べる。
   ここで `=` ではなく `same_kind` を使う理由は §8.6 で述べる。

   | `t` の形 | 処理 |
   |---|---|
   | `Unbound` | 制約の集合に加え、制約つき変数の一覧(`class_vars`)にも追加する |
   | `Rigid` / `Generic` | 宣言されていない制約ならエラーにし、直し方を案内する |
   | `TCon` | インスタンス表を引き、インスタンスの前提(`ii_premises`)を型引数へ伝播する |
   | `TRecord` / `TVariant` | クラスが構造的導出を有効にしていれば、閉じた行の各フィールドへ伝播する |
   | `TApp` | 制約を付けられないのでエラーにする |

   `Generic` に制約が要求されるのは、
   宣言の型スキームの中(newtype のフィールドの型やクラスメソッドの型)で制約つきエイリアスを展開したときである。
   展開したエイリアスの制約が、パラメータを表す `Generic` に要求される。
   規則は `Rigid` と同じで、宣言済みの制約に含まれていれば満たされ、
   含まれていなければ `[A: Show]` のように制約を書くよう案内する。

   `Rigid` の場合のエラーメッセージは、要求された制約が予約述語かどうかで 2 通りに分かれる。
   予約述語 `Integral` はユーザが制約として書けないクラスなので、
   `let f[A: Add](x: A) = x + 1` に対して「A は Integral のインスタンスではない」と伝えても、
   ユーザには直す手段がない。
   そこで、`0i32` のように接尾辞を付けるか具体型を使うよう案内する。
   通常のクラスなら `[A: Add]` と書けば直るので、そう案内する。

   この例に `[A: Add]` を付けているのは、予約述語の分岐まで到達させるためである。
   制約を外した `let f[A](x: A) = x + 1` では、
   `+` の型スキームが持つ `Add` の要求のほうが先にスコーレム定数に達する。
   その結果、通常のクラスの分岐でエラーになり、次のメッセージを出す。

   ```
   型パラメータ ς1 は Add のインスタンスではありません。[A: Add] のように制約を書いてください
   ```

   注釈を経由する `let f[A](x: A): A = 1` でも、予約述語の分岐に到達する。

   構造的導出の分岐は sample.kel:392-396 の規則を実装する。
   カインドが `* -> *` のクラスはこの分岐に到達しない。
   構造的導出を持つのは組み込みの `Eq` だけで、そのパラメータのカインドは `Type` だからである。
   `Eq` のように構造的導出を持つクラスなら、レコードやヴァリアントを分解し、
   各フィールドに同じ制約を要求する。
   ただし、分解するのは行が閉じているときだけである。
   `{x: Int32 extends R}` の `R` に何が入るか分からない以上、比較できるとは保証できない。
   行変数ごとの制約 `[R: Eq]` を導入すれば開いた行も扱えるが、
   カインドの扱いと制約の解決の両方を変えることになるので、仕様はこれを採用しない。

   `TCon` の分岐は、インスタンス表に登録された前提を使う(前提の表は第6章 §6.9)。
   `Eq[List[_]]` の前提 `A: Eq` は `(0, Eq)` として表に入っている。
   `List[Opaque]` に `Eq` を要求すると、`Opaque` に `Eq` が伝播し、
   `Opaque は Eq のインスタンスではありません` というエラーになる。
   この診断には、前提をたどり始めた型とクラスが付く(`test/premise.t` の pr2 / pr3)。
   分岐の中の `if i < List.length args` は念のための検査で、偽になることはない。
   冒頭のカインドの照合が先にエラーにするので、
   前提が位置 `i` を持つなら `args` は `i + 1` 個以上ある。

   前提をたどって生じた要求が満たされないときは、満たされなかった型に加えて、
   前提をたどり始めた型とクラスも診断に添える。
   本章は、この型とクラスの組を要求の出どころと呼ぶ。
   `List[List[Opaque]]` に `Eq` を要求したなら、診断は次のようになる。

   ```
   Opaque は Eq のインスタンスではありません。List[List[Opaque]] が Eq であるための前提として要求されました
   ```

   添えるのはたどり始めた 1 組だけで、途中の `List[Opaque]` は書かない。
   途中の型を並べると、入れ子の深さに応じて文が長くなるからである。
   そのため `add_class` は、出どころを省略可能な引数 `via` で受け渡し、
   前提の分岐で初めて値を入れ、構造的導出の分岐ではそのまま渡す。
   メッセージに現れる型と出どころの型は、`show_pair` で名前の表を共有して文字列化する。
   別々に文字列化すると、型変数の名前は文字列化のたびに振り直されるので、
   同じ `ς1` が文の前半と後半で別の型パラメータを指すことがある。

   前提が単一化変数に達したときは、その時点では成否が決まらない。
   `Nil == Cons(MkOpaque(1i32), Nil)` では、左の `Nil` の型 `List[α]` に先に `Eq` が要求され、
   前提が `α` に `Eq` を付ける。
   `α` が `Opaque` に決まるのは右辺を読んだ後で、そこで `bind` が `add_class` を呼び出す。
   この呼び出しにも出どころを添えるため、
   前提が単一化変数に新しく制約を付けたときは、
   変数とクラスの組をキーにして、出どころを表 `premise_origins` に記録する。
   `bind` と §8.9 の `default_to` はその表を引き、
   出どころの型に現れる、いま束縛する変数を、代入する型に置き換えてから `via` に渡す。
   置き換えは表示のためだけのもので、セルを書き換えない(`subst_unbound`)。
   `repr` が経路圧縮を行うので、一時的に `Link` を張って表示してから戻す方法は使えない。

   `TApp` に制約を付けられないのは、修飾型を持たないからである。
   Haskell は `Show (f a)` のような制約を残して解決を後回しにできるが、
   本実装の制約は、型変数か、具体型の先頭の型構成子にしか付けられない。
   `TApp` への制約を扱うには、制約を型と一緒に受け渡す仕組みが必要になる。

   ### 制約つき変数の一覧 class_vars

   `class_vars` は、制約が付いた変数を記録する一覧である。
   この一覧は 3 つの処理が使う。
   1 つ目は、予約述語つきの変数を宣言の終わりに既定の型に決める処理(§8.9 の `default_numerics`)、
   2 つ目は、型から到達できない制約つき変数を報告する曖昧性検査(§8.9 の `check_ambiguity`)、
   3 つ目は、一般化しない束縛の終わりに深い変数のレベルを下げる処理(§8.9 の `lower_levels`)である。
   どれも、型がまだ決まっていない制約つき変数を扱うので、同じ一覧を使う。
   既定化は一覧の全体をたどって一覧を空にし、型から到達できるかどうかは調べない。
   到達できるかどうかを調べるのは曖昧性検査だけである。

   一覧の項目には、追加した順に通し番号を付ける。
   新しい項目は先頭に追加し、曖昧性検査が一覧を作り直すときも順序を保つので、
   一覧は番号の大きい順に並ぶ。
   `lower_levels` は、束縛の本体を推論する前に `class_mark` で記録した番号より大きい項目、
   つまりその本体を推論する間に追加された項目だけをたどる。 *)

let is_predicate c = c = cls_integral || c = cls_fractional

(* 制約つき変数の一覧。項目は (通し番号, 変数) で、番号の大きい順に並ぶ。
   宣言の終わりに default_numerics が、一覧の変数のうち予約述語の付いたものを既定の型に決めて
   一覧を空にする。
   check_ambiguity は、型から到達できない制約つき変数を報告する。
   lower_levels は、束縛の本体を推論する間に追加された変数のレベルを下げる *)
let class_vars : (int * tvar ref) list ref = ref []

(* 最後に振った通し番号。reset でも戻さないので、一覧を空にしても番号は重ならない *)
let class_seq = ref 0

let note_class_var v =
  incr class_seq;
  class_vars := (!class_seq, v) :: !class_vars

(* 現在の通し番号。これより後に一覧へ追加する項目は、これより大きい番号を持つ *)
let class_mark () = !class_seq

(* 数値リテラルが予約述語を付けた変数と、その述語と、リテラルの位置の組。
   既定化の失敗を報告する位置を探すのに使う(§8.9 の default_to)。
   default_numerics が宣言の終わりに空に戻す *)
let literal_origins : (tvar ref * oid * Location.span) list ref = ref []

let note_literal ~loc t c = match t with TVar r -> literal_origins := (r, c, loc) :: !literal_origins | _ -> ()

(* 証拠の穴の一覧(§8.11)。既定化の失敗を報告する位置を探すのにも使うので、ここで定義する *)
let holes : (int * Tree.hole) list ref = ref []

(* 前の宣言の終わりに記録した oid。
   これより大きい h_id を持つ穴は、現在の宣言で作ったものである。
   一般化しない束縛の穴は宣言をまたいで一覧に残るので、
   既定化の失敗の位置を探すときは、この値を下限にして前の宣言の穴を除外する *)
let decl_hole_floor = ref 0

(* 制約つきの新しい変数はここで作り、作った時点で一覧 class_vars に追加する。
   instantiate、subst_params、第11章のコンストラクタの具体化(dd_params の展開)もここを通る。
   単一化変数が制約を持つようになる経路は、この関数と、
   既存の単一化変数に制約を追加する add_class(数値リテラルの変数はこちらを通る)の 2 つで、
   どちらも一覧に追加する。
   そのため、一覧は制約つきの単一化変数をすべて含む。
   別の経路で作ると、その変数の制約は曖昧性検査の対象にならない *)
let new_class_var ~kind ~classes level =
  let v = new_var ~kind ~classes level in
  (match v with TVar r when classes <> [] -> note_class_var r | _ -> ());
  v

(* 前提をたどって単一化変数に達した制約の出どころ。
   キーは (変数の識別子, クラス) で、値はたどり始めた型とクラスの組である。
   bind がその変数を具体型に束縛するとき、ここから出どころを引いて add_class に渡す。
   セルの書き換えを記録している間(trailing が真の間)は、
   書き込みを取り消すクロージャも trail に追加する *)
let premise_origins : (int * oid, ty * oid) Hashtbl.t = Hashtbl.create 16

let note_premise_origin (i : var_info) c via =
  let key = (i.vid, c) in
  if not (Hashtbl.mem premise_origins key) then (
    Hashtbl.replace premise_origins key via;
    if !trailing then trail := (fun () -> Hashtbl.remove premise_origins key) :: !trail)

(* 型 ty の中の単一化変数 v を t に置き換えた型を返す。診断の表示にだけ使い、セルは書き換えない *)
let subst_unbound v t ty =
  let rec go ty =
    match repr ty with
    | TVar r when r == v -> t
    | TVar _ as ty -> ty
    | TCon (n, args) -> TCon (n, List.map go args)
    | TApp (g, a) -> tapp (go g) (go a)
    | TArrow (p, r, e) -> TArrow (go p, go r, go e)
    | TRecord row -> TRecord (go row)
    | TVariant row -> TVariant (go row)
    | TRowEmpty -> TRowEmpty
    | TRowExtend (l, fld, rest) -> TRowExtend (l, go fld, go rest)
  in
  go ty

(* via は、インスタンスの前提をたどって生じた要求のときだけ値を持つ。
   値は、たどり始めた型とクラスの組(要求の出どころ)である。
   要求が満たされないときは、その組を診断に添える *)
let rec add_class ?via t c =
  let ci =
    match Decls.find_class c with Some ci -> ci | None -> type_error ("未知のクラス: " ^ display_of c)
  in
  (* ty はメッセージに現れる型で、mk は ty を文字列化したものからメッセージを作る。
     出どころを添えるときは、ty と出どころの型を、名前の表を共有して文字列化する *)
  let fail ?advice ?ty mk =
    let origin vt vc = "。" ^ vt ^ " が " ^ display_of vc ^ " であるための前提として要求されました" in
    let shown, suffix =
      match (ty, via) with
      | Some ty, None -> (show ty, "")
      | None, None -> ("", "")
      | Some ty, Some (vt, vc) ->
          let s, o = show_pair ty vt in
          (s, origin o vc)
      | None, Some (vt, vc) -> ("", origin (show vt) vc)
    in
    type_error (mk shown ^ suffix ^ match advice with None -> "" | Some a -> "。" ^ a)
  in
  if not (same_kind ci.ci_param_kind (kind_of t)) then
    type_error
      ("クラス " ^ display_of c ^ " は " ^ show_kind ci.ci_param_kind ^ " のクラスですが、" ^ show t ^ " に要求されました");
  match repr t with
  | TVar v -> (
      match !v with
      | Unbound i ->
          if not (List.mem c i.vcls) then (
            set_tv v (Unbound { i with vcls = c :: i.vcls });
            note_class_var v;
            Option.iter (note_premise_origin i c) via)
      | Rigid i | Generic i ->
          (* Generic に制約が要求されるのは、宣言の型スキームの中(newtype のフィールドの型や
             クラスメソッドの型)で制約つきエイリアスを展開したときである。
             規則は Rigid と同じで、宣言済みの制約に含まれていれば満たされ、
             含まれていなければ制約を書くよう案内する *)
          if not (List.mem c i.vcls) then
            if is_predicate c then
              type_error "型パラメータに数値リテラルは使えません。0i32 のように接尾辞を付けるか具体型を使ってください"
            else
              fail
                ~advice:("[A: " ^ display_of c ^ "] のように制約を書いてください")
                ~ty:(TVar v)
                (fun s -> "型パラメータ " ^ s ^ " は " ^ display_of c ^ " のインスタンスではありません")
      | _ -> fail ~ty:t (fun s -> s ^ " に " ^ display_of c ^ " 制約を付けられません"))
  | TCon (n, args) -> (
      match Decls.find_instance ~cls:c ~con:n with
      | Some { ii_premises; _ } ->
          let via = match via with Some _ -> via | None -> Some (t, c) in
          List.iter (fun (i, c2) -> if i < List.length args then add_class ?via (List.nth args i) c2) ii_premises
      | None -> fail (fun _ -> display_of n ^ " は " ^ display_of c ^ " のインスタンスではありません"))
  | (TRecord row | TVariant row) when ci.ci_derive_structural ->
      (* 閉じた行への構造的導出(sample.kel:392-396)。開いた行には適用できない *)
      let fields, tail = row_fields row in
      (match repr tail with
      | TRowEmpty -> List.iter (fun (_, f) -> add_class ?via f c) fields
      | _ ->
          fail ~ty:t (fun s ->
              "行変数を含む型 " ^ s ^ " に " ^ display_of c ^ " の構造的導出は適用できません(行が閉じていません)"))
  | TApp _ -> fail ~ty:t (fun s -> "制約 " ^ display_of c ^ " を " ^ s ^ " に付けられません(頭が型変数の適用には制約を貼れません)")
  | other -> fail ~ty:other (fun s -> s ^ " は " ^ display_of c ^ " のインスタンスではありません")

(* ## 8.5 代入の 4 つの手順

   代入先になれるのは `Unbound` の変数だけである。
   `Rigid`、`Generic`、`Link` が `bind` に渡されることはなく、
   渡されたら処理系のバグなので `bug` を呼び出す。
   `bind` は次の 4 つの手順を、この順に行う。
   順序を入れ替えると正しく動かない。

   1. `same_kind` でカインドが一致するかを調べ、あわせて `KVar` を解決する
   2. `occurs_adjust` で occurs check、レベル調整、脱出検査を行う
   3. 変数に付いていた制約を、代入する型へ伝播する(`add_class`)
   4. `Link` を張る

   手順 2 は手順 4 より先でなければならない。
   `v := Link t` を先に実行すると、以後 `repr (TVar v)` は `t` を返すので、
   `t` の中に `v` が含まれていても `occurs_adjust` は `v` を見つけられない。
   occurs check が何も検出しないまま、無限型ができてしまう。

   手順 3 を手順 4 より先に行うのは、失敗したときに型の状態を壊さないためである。
   制約の伝播が `type_error` で失敗したとき、
   まだ `Link` を張っていなければ `v` は単一化変数のまま残り、
   型の状態が中途半端にならない。

   `unbound_var` は `repr` を呼び出さない。
   呼び出し元の `unify` が `repr` 済みの型を渡すことを前提にしている。 *)

let bind v t =
  match !v with
  | Unbound ({ vlevel; vkind; vcls; _ } as i) ->
      if not (same_kind vkind (kind_of t)) then
        type_error ("カインドが一致しません: " ^ show (TVar v) ^ " :: " ^ show_kind vkind ^ " と " ^ show t);
      occurs_adjust v vlevel t;
      List.iter
        (fun c ->
          let via =
            Option.map (fun (vt, vc) -> (subst_unbound v t vt, vc)) (Hashtbl.find_opt premise_origins (i.vid, c))
          in
          add_class ?via t c)
        vcls;
      set_tv v (Link t)
  | _ -> bug "束縛できない変数への bind"

let unbound_var t = match t with TVar ({ contents = Unbound _ } as r) -> Some r | _ -> None

(* ## 8.6 行の書き換えと最左一致

   Diktor の行は、Daan Leijen の *Extensible Records with Scoped Labels*(2005)に従う。
   通常の行型システムは、同じラベルを 2 度含まないという lacks 制約(`ρ \ x`)を課す。
   lacks 制約を使う方式も正しいが、制約を型と一緒に受け渡す必要があり、実装量が増える。

   Scoped Labels は逆に、ラベルの重複を許す。
   その代わり、次のように定める。

   - `r.x` は最も左の `x` を取り出す
   - `{x = e | 残り}` は無条件に追加でき、それまでの `x` は隠れる
   - `r \ x` は最も左の `x` を消し、隠れていた `x` が再び見える

   同じ名前のラベルは、レキシカルスコープの変数のように積み重なる。

   Keleut では、この最左一致が次の 3 つの場面で同じ意味を持つ。
   レコードでは手前のフィールドが優先され、エフェクト行では最も左のラベルが選ばれ、
   `run` の入れ子では内側のヒープが優先される。
   修飾なしで書いた操作名の解決は、この最左一致を使わない。
   行に現れる候補が 1 つのときだけ解決し、2 つ以上現れるときは修飾を求める(第11章 §11.20)。
   sample.kel:624 の `copy` の中の `write` は File と Console の両方の操作に該当するので、
   `File.write` と修飾してある。
   その操作がどの `File` のハンドラに届くかは最左一致で決まり、
   最も内側の `with_file` のハンドラに届く。

   中心になる関数は `rewrite_row row label` である。
   行の中から最初の `label` を探して先頭へ移し、`(フィールド型, 残り)` を返す。
   行の末尾が、まだ束縛されていない行変数(単一化変数)だったときは、
   その行変数を `TRowExtend (label, 新しい型変数, 新しい行変数)` に束縛して行を拡張する。
   この関数には注意点が 2 つある。

   ### 注意点 1:挿入する型変数のレベル

   行を拡張するときに作る 2 つの変数は、現在のレベルではなく、行変数自身のレベルで作る。
   現在のレベルで作ると、一般化してはならない変数を一般化してしまう。
   たとえば次の式を考える。

   ```
   fn(r) => { r.a; let g = fn() => r.b; ... }
   ```

   `r.b` が `r` の行を拡張するのは、`g` の右辺、つまり 1 段深いレベルの中である。
   `b` のフィールド型を現在のレベルで作ると、`g` を一般化するときにその変数が `Generic` になり、
   `g` に任意の `A` について `() => A` という型が付く。
   引数のフィールドから任意の型の値を取り出せることになるので、不健全である。

   行変数のレベルで作った新しい変数は、呼び出し元の `unify` が `bind` を通して相手の型と単一化する。
   そのとき `occurs_adjust` が実行され、相手の型に含まれる変数のレベルも下がる。

   ### 注意点 2:行変数のカインドは same_kind で調べる

   変数が行変数かどうかは、`vkind = KRow` という構造の比較ではなく、`same_kind` で判定する。
   第11章(elab.ml)の `make_rigids` は、
   arity が 0 の型パラメータ(`let fst[A, R](...)` の `R` のような束縛子)に `new_kind_var ()` を渡す。
   §8.1 で述べたとおり、束縛子のカインドは使われた位置で決まるからである。
   この `R` が行の位置で使われると、そのカインドは `KStar` でも `KRow` でもなく、
   リンク先が `KRow` である `KVar` になる。
   構造の比較ではこれを行変数と判定できない。

   構造の比較で判定すると、仕様の中心的な例が型エラーになる。
   1 つは、sample.kel:195 の `fst(t: {_item: A extends R})` に
   レコード `{x = 1, _item = ...}` を渡す例(sample.kel:201-203)で、
   行多相のレコードを使う。
   もう 1 つは、sample.kel:209-215 の `describe` に `#Other` を渡す例で、
   構造的ヴァリアントの残りの行を使う。
   この呼び出しは `test/verify_fixes.t` にある。
   第1章(syntax.ml)の `default_kind` が `KVar` を `KStar` に決めるまで(時期は第1章 §1.6)、
   カインドは決まっていないことがある。
   `vkind` に入った `KVar` は、カインドが決まった後も既定化した後も、
   リンクを持つ `KVar` のまま残る。
   そのため、カインドは構造では比較せず、`same_kind` で比較する。

   `same_kind` は比較しながら `KVar` を相手のカインドに単一化するので、
   ここを通った時点で `R` のカインドが `Row` に決まる。 *)

(* 最も左の label を先頭へ移し、(フィールド型, 残り) を返す。
   新しい変数は行変数自身のレベルで作る(§8.6 の注意点 1) *)
let rec rewrite_row row label =
  match repr row with
  | TRowEmpty -> type_error ("ラベル " ^ display_of label ^ " がありません(行は閉じています)")
  | TRowExtend (l, f, rest) when l = label -> (f, rest)
  | TRowExtend (l, f, rest) ->
      let f2, rest2 = rewrite_row rest label in
      (f2, TRowExtend (l, f, rest2))
  | TVar v -> (
      match !v with
      (* カインドは構造の比較でなく same_kind で調べる。[R] のような arity 0 の
         型パラメータは new_kind_var() を受け取り、行の位置で使われると
         KVar{→KRow} になるので、KRow との構造の比較では行変数と判定できない *)
      | Unbound { vlevel; vkind; _ } when same_kind vkind KRow ->
          let f2 = new_var vlevel in
          let rest2 = new_row_var vlevel in
          set_tv v (Link (TRowExtend (label, f2, rest2)));
          (f2, rest2)
      | Rigid { vkind; _ } when same_kind vkind KRow ->
          (* 注釈で固定された行にはラベルを追加できない。高階のエフェクト
             注釈を書き間違えたときに最初に出る診断なので、「行型では
             ありません: ς1」ではなく原因を述べる。§8.8 の Heap の
             診断と同じ方針である *)
          type_error
            ("行 " ^ show (TVar v) ^ " は注釈で固定された行変数なので、ラベル " ^ display_of label
           ^ " を足せません(注釈側に " ^ display_of label ^ " を(必要なら引数つきで)書き足してください)")
      | _ -> type_error ("行型ではありません: " ^ show (TVar v)))
  | t -> type_error ("行型ではありません: " ^ show t)

(* ## 8.7 単一化の本体

   単一化の本体は、型の構造に沿って両辺を分解する通常の単一化である。
   まず両辺を `repr` し、同じものなら何もしない。
   片方が単一化変数なら `bind` する。
   どちらでもなければ、形に従って分解する。

   最初の `same_var` は、OCaml での型変数の表現に合わせた判定である。
   OCaml の `TVar r` はヒープに確保される値なので、同じ `ref` を指す別の `TVar` の値が簡単にできる。
   そのため、同じ変数かどうかは `TVar` の値ではなく `ref` の物理等価で調べる。
   `TVar` の値の物理等価で比較すると、同じ変数どうしの単一化が `bind v (TVar v)` になり、
   occurs check が自分自身を見つけてエラーになる。

   ### 矢印

   `TArrow` は、引数と返り値に加えてエフェクト行も単一化する。
   呼び出し元の行と呼び出し先の関数の行をここで単一化するので、
   関数のエフェクトが呼び出し元の行に伝わる。
   Keleut の引数は閉じた `_item` 行のレコードなので、
   関数適用の引数の個数の不一致は行の単一化で検出できる。
   ただし、行の単一化の診断は、片方の行にラベル `_item` がないことしか伝えない。
   そこで、2 つの矢印の引数の行がどちらも閉じた `_item` 行で個数が違うときは、
   行の単一化に入る前に、`check_arity` が両方の矢印と個数を示して報告する。
   どちらかの行が開いているか、`_item` 以外のラベルを含むときは、そのまま行を単一化する。
   呼び出しの実引数の並びと仮引数の行の個数は、第11章 §11.12 の `check_call_arity` が比較する。

   ### 型適用(高カインド)

   高カインドの型を扱う分岐は、`TApp` を含む 3 つだけである。
   `TApp` どうしの分岐が 1 つと、`TApp` と `TCon` の分岐が左右の向きで 2 つである。

   ```
     f a ~ g b        →  f ~ g,  a ~ b
     f a ~ List Int   →  f ~ List,  a ~ Int      (最後の引数を分ける)
   ```

   一階の単一化のままで済むのは、Keleut が型レベルのλを持たないからである。
   λを書けるなら `f := λx. List Int` のような解も候補になり、
   最汎単一化子(mgu)が一意でなくなって主要型がなくなる。
   同じ理由で、型エイリアスの部分適用も認めない(第11章 §11.5 の `expand_alias` が拒否する)。
   第1章(syntax.ml)の `tapp` と `repr` は、適用される型が `TCon` なら、
   引数をその `TCon` の引数の並びの末尾に加えて正規化する。
   したがって `TApp` の連鎖の先頭は常に型変数で、分解の仕方は 1 通りに決まる。

   ### 最後の 2 つの場合

   `(TVar _, _ | _, TVar _)` の分岐に来る `TVar` は、
   常に `Rigid` である(`Unbound` は上の `bind` で処理済み)。
   ここで専用のメッセージを出すのは、この分岐がリージョンの取り違えを報告する主な経路だからである。
   `run` を入れ子にして外側のヒープの参照を内側で読もうとすると、
   `occurs_adjust` の脱出検査ではなく、この分岐でエラーになる。
   第11章は関数適用で、関数の型を先に呼び出し元の行と単一化し、その後で引数を検査する(§11.12)。
   `Ref.get` の行の `Heap` は、最左一致で内側の `run` の `Heap` と単一化されるので、
   `Ref.get` のリージョン変数は内側の `run` のスコーレム定数に決まる。
   その後で引数を検査すると、`Ref` の型引数の位置で、
   外側と内側の `run` が作った 2 つのスコーレム定数が一致しない。
   これは仕様どおりの拒否である。
   衝突が次のどちらかの位置で起きたときは、§8.8 の `unify_region` がこの分岐のメッセージを加工する。
   1 つはエフェクト行の `Heap` ラベルの引数である。
   もう 1 つは、`Ref` どうしまたは `MutableArray` どうしを `TCon` の分岐で単一化するときの第 1 引数である。
   スコーレム定数どうしの衝突なら、ほかのリージョンのものを使おうとしたと述べる文に、
   元のメッセージを括弧に入れて添える。
   スコーレム定数と型変数でない型の衝突なら、
   その型がリージョンではないと述べるメッセージに置き換える。
   高カインドの型変数への適用 `F[Int32, Int32]` と `Ref[ς1, Int32]` の単一化は、
   上の `TApp` と `TCon` の分岐で最後の引数から順に分けていき、
   `ς1` と `Int32` を `unify` で直接単一化する。
   この形は `unify_region` を通らないので、この分岐のメッセージのまま報告する。

   空の行と、注釈で固定された行変数(スコーレム定数である行変数)が衝突したときは、
   スコーレム定数が一致しない分岐より手前の分岐で、
   行が注釈で固定されていることを述べるメッセージを出す。
   「{} と ς1」が一致しないとだけ伝えても、ユーザは原因を読み取りにくいからである。
   このメッセージは原因だけを述べ、直し方を書かない。
   直し方は、衝突した束縛の種類と、空の行がどちらの側にあるかで変わるが、
   `unify` は、そのどちらの情報も受け取らない。
   値束縛は型パラメータを取れないので、行変数を新しく導入する直し方は使えない。
   空の行が初期化式や呼び出した関数の側にあるときは、注釈ではなくその関数の側を直す。

   スコーレム定数が一致しない分岐は、衝突した 2 つの型を `last_rigid_clash` に保存してから報告する。
   第11章の再帰群(§11.29)は、報告を受け取った後でこの組を調べ、
   衝突したスコーレム定数が再帰群のどの束縛の型パラメータかを求めて、原因に近い事実を報告に添える。
   報告のメッセージは型を表示用の名前でしか持たないので、
   どのスコーレム定数が衝突したかはこの組からしか分からない。 *)

let last_rigid_clash : (ty * ty) option ref = ref None

let item_arity t =
  match repr t with
  | TRecord row ->
      let fields, tail = row_fields row in
      if repr tail = TRowEmpty && List.for_all (fun (l, _) -> l = l_item) fields then Some (List.length fields) else None
  | _ -> None

let rec unify a b = unify_in ~structural:false a b

(* structural は、単一化している行がレコードかヴァリアントの行であることを表す(§8.8) *)
and unify_in ~structural a b =
  let t1 = repr a in
  let t2 = repr b in
  let same_var = match (t1, t2) with TVar r1, TVar r2 -> r1 == r2 | _ -> false in
  if not (t1 == t2 || same_var) then
    match (unbound_var t1, unbound_var t2) with
    | Some v, _ -> bind v t2
    | _, Some v -> bind v t1
    | None, None -> (
        match (t1, t2) with
        | TCon (n1, r1 :: as1), TCon (n2, r2 :: as2)
          when n1 = n2 && (n1 = ty_ref || n1 = ty_mutable_array) && List.length as1 = List.length as2 ->
            unify_region (name_of n1 ^ " の第 1 引数")
              (fun msg -> "ほかのリージョンの " ^ name_of n1 ^ " を使おうとしています(" ^ msg ^ ")")
              r1 r2;
            List.iter2 unify as1 as2
        | TCon (n1, as1), TCon (n2, as2) when n1 = n2 && List.length as1 = List.length as2 ->
            List.iter2 unify as1 as2
        | TApp (f1, a1), TApp (f2, a2) ->
            unify f1 f2;
            unify a1 a2
        (* f a ~ List Int → f ~ List, a ~ Int(最後の引数を分ける) *)
        | TApp (f, x), TCon (n, args) when args <> [] ->
            let init, last = split_last args in
            unify f (TCon (n, init));
            unify x last
        | TCon (n, args), TApp (f, x) when args <> [] ->
            let init, last = split_last args in
            unify (TCon (n, init)) f;
            unify last x
        | TArrow (p1, r1, e1), TArrow (p2, r2, e2) ->
            check_arity t1 t2 p1 p2;
            unify p1 p2;
            unify r1 r2;
            unify e1 e2
        | TRecord r1, TRecord r2 -> unify_in ~structural:true r1 r2
        | TVariant r1, TVariant r2 -> unify_in ~structural:true r1 r2
        | TRowEmpty, TRowEmpty -> ()
        | TRowExtend (l, f, rest), _ -> unify_row ~structural l f rest t2
        | _, TRowExtend (l, f, rest) -> unify_row ~structural l f rest t1
        (* Unbound は上で処理したので、ここに来る TVar はスコーレム定数である。
           そこで、スコーレム定数のためのメッセージで報告する。
           もう一方が空の行のときのために、
           行変数が注釈で固定されていることを述べる分岐を先に置く。
           「{} と ς1」が一致しないとだけ伝えても、
           ユーザは原因を読み取りにくいからである *)
        | ((TVar _ as rv), TRowEmpty) | (TRowEmpty, (TVar _ as rv)) ->
            type_error
              ("行 " ^ show rv ^ " は注釈で固定された行変数なので、空の行と一致させられません")
        | (TVar _, _ | _, TVar _) ->
            last_rigid_clash := Some (t1, t2);
            type_error ("スコープ付きの型が一致しません: " ^ show2 t1 t2)
        | _ -> type_error ("型が一致しません: " ^ show2 t1 t2))

(* 引数の行がどちらも閉じた _item 行で、個数が違えば、行の単一化に入る前に
   個数の不一致として報告する *)
and check_arity t1 t2 p1 p2 =
  match (item_arity p1, item_arity p2) with
  | Some n1, Some n2 when n1 <> n2 ->
      let strs = show2 t1 t2 in
      type_error
        ("引数の個数が一致しません: " ^ strs ^ "(引数は " ^ string_of_int n1 ^ " 個と " ^ string_of_int n2 ^ " 個です)")
  | _ -> ()

and split_last = function
  | [] -> bug "split_last: empty"
  | xs ->
      let rec go acc = function [ x ] -> (List.rev acc, x) | x :: tl -> go (x :: acc) tl | [] -> assert false in
      go [] xs

(* ## 8.8 行どうしの単一化と無限行

   `unify_row` は `<l : field | rest>` と `row2` を単一化する。
   `row2` から `l` を取り出し、フィールドどうしと残りどうしをそれぞれ単一化する。
   この手順には注意点が 1 つある。

   `rewrite_row` は `row2` の末尾の変数を書き換える。
   その変数が `rest` の末尾の変数と同じだった場合、
   結果は `ρ = <l : τ | ρ>` という無限行になる。
   型の occurs check はこの無限行を検出できない。
   書き換えが先に起きるので、`unify rest rest2` に進んだ時点では、
   すでに `rest` が拡張されているからである。

   そこで、書き換える前に `rest` の末尾の変数を記録しておき、
   書き換えた後にその変数が束縛されていたらエラーにする。
   この検査がないと、型推論が停止しなくなる。

   エフェクト行のフィールドの単一化が `Heap` ラベルで失敗したときは、
   `unify_region` が、失敗した 2 つの型の形に応じてメッセージを選ぶ。
   型の形は次の 3 通りである。
   1 つ目は元のメッセージに説明を添え、2 つ目は元のメッセージのまま報告し、
   3 つ目は別のメッセージに置き換える。

   - どちらもスコーレム定数のとき。
     ここに来るスコーレム定数には、`run` が作ったリージョン変数と、注釈の型パラメータがある。
     2 つのスコーレム定数は別のリージョンを表すので、
     ほかのリージョンのヒープを使おうとしていると述べる文に、元のメッセージを括弧に入れて添える。
     どちらの種類のスコーレム定数かは区別しないので、
     メッセージには「別の `run` のスコープ」とは書かない。
     注釈の型パラメータが表すリージョンも、`run` の本体から見ればほかのリージョンだからである。
   - 片方が単一化変数のとき。
     もう一方の型の形は問わない。
     `unify` はすぐに §8.5 の `bind` に進むので、失敗は `bind` の手順の中で起きる。
     失敗するのは、カインドの照合、§8.3 の occurs check と脱出検査、
     §8.4 の制約の伝播のどれかである。
     リージョンの取り違えではないので、元のメッセージのまま報告する。
   - どちらも単一化変数でなく、どちらかが型変数でないとき。
     `run` のリージョン変数と型パラメータは、単一化の中では型変数として現れる。
     `@ Heap[Int32]` の `Int32` は型変数でないので、リージョンを表していない。
     リージョン変数のカインドは `Type` なので、注釈の検査はこの形を拒否しない。
     元のメッセージのままスコーレム定数の名前 `ς1` を見せても、
     ユーザは自分が書いた `Int32` が原因だと読み取りにくい。
     そこで、その型がリージョンではないと述べるメッセージに置き換える。

   `Ref` と `MutableArray` の第 1 引数もリージョンを表すので、§8.7 の `unify` は、
   `Ref` どうしか `MutableArray` どうしを `TCon` として単一化するとき、
   その第 1 引数を `unify_region` で単一化する。
   まだ束縛されていない高カインドの型変数を引数に適用した型(§8.7 の `F[Int32, Int32]`)を、
   `TApp` の分岐が引数を 1 つずつ分けて単一化するときは、この経路に入らない。
   高カインドの型変数が先の単一化で `Ref` や `Ref[ς]` に束縛された後は、
   `repr` が `Ref` の `TCon` に正規化するので、
   引数の個数によらずこの経路に入る。
   どちらもスコーレム定数のときは、
   ほかのリージョンの `Ref` か `MutableArray` を使おうとしていると述べる。
   §8.7 で述べたとおり、入れ子の `run` で外側の参照を `Ref.get` で読む形は、
   `Heap` ラベルではなくこの位置でエラーになる。
   ほかのリージョンのものだと述べる文を添えないと、
   ユーザにはスコーレム定数の名前が一致しないことしか伝わらない。

   レコードとヴァリアントの行には、`Heap` ラベルのこの扱いを適用しない。
   構造的ヴァリアントのコンストラクタ `#Heap` のラベルも `eff_heap` と同じ名前になるが、
   その引数は値の型で、リージョンではない。
   そこで `unify` は、`TRecord` どうしと `TVariant` どうしの中の行を、
   `structural` を真にして `unify_in` に渡す。
   `unify_row` は、`structural` が真なら `Heap` ラベルのフィールドも `unify` で単一化する。
   `structural` の値は行の残りへ引き継ぎ、フィールドの型の中へは引き継がない。
   `#Heap(Int32)` を受け取る関数に `#Heap(String)` を渡すと、
   ラベルを `#Other` に替えたときと同じく、`unify` は型が一致しないと報告する。

   `rewrite_row` はラベルの名前だけで一致を判定し、
   ラベルの引数(`Heap[h]` の `h`)は見つけた後で単一化する。
   引数まで含めて一致を判定すると、どのラベルを選ぶかが引数に左右され、
   選択が決定的でなくなる。 *)

(* 書き換える前に rest の末尾の変数を記録し、書き換えた後にその変数が束縛されていたらエラーにする。
   こうして ρ = <l : τ | ρ> という無限行を検出する *)
and unify_row ~structural label field rest row2 =
  let tail_before = row_tail_var rest in
  let field2, rest2 = rewrite_row row2 label in
  (match tail_before with
  | Some tv -> ( match !tv with Link _ -> type_error "再帰的な行型が発生しました" | _ -> ())
  | None -> ());
  if label = eff_heap && not structural then
    unify_region "Heap の引数" (fun msg -> "ほかのリージョンのヒープを使おうとしています(" ^ msg ^ ")") field field2
  else unify field field2;
  unify_in ~structural rest rest2

(* リージョンの位置にある 2 つの型を単一化する。
   失敗したとき、どちらもスコーレム定数なら、both で元のメッセージに説明を添えて報告する。
   片方が単一化変数なら、失敗の原因は束縛のときの検査なので、
   元のメッセージのまま報告する。
   それ以外で、どちらかが型変数でなければ、その型はリージョンではないと述べる *)
and unify_region what both r1 r2 =
  let shape =
    match (repr r1, repr r2) with
    | TVar { contents = Rigid _ }, TVar { contents = Rigid _ } -> `Rigids
    | TVar { contents = Unbound _ }, _ | _, TVar { contents = Unbound _ } -> `Vars
    | TVar _, TVar _ -> `Vars
    | TVar _, t | t, _ -> `Non_region t
  in
  try unify r1 r2
  with Type_error msg -> (
    match shape with
    | `Non_region t ->
        type_error
          (what ^ " " ^ show t ^ " はリージョンではありません。" ^ what ^ "には run のリージョン変数か型パラメータを書きます")
    | `Rigids -> type_error (both msg)
    | `Vars -> type_error msg)

(* ## 8.9 一般化

   `generalize level t` は `t` を走査し、
   `level` より深いレベルの `Unbound` を `Generic` に書き換える。
   返り値はなく、型変数をその場で書き換える。

   置換を作り、新しい型を組み立てて返す方式にしないのは、第5章(tree.ml)の精緻化木のためである。
   第11章(elab.ml)は推論の途中で木のノードに型を書き込む。
   新しい型を作って返すと、書き込み済みの型と一般化後の型が別のものになり、木の中に古い型が残る。
   その場で書き換えれば、書き込み済みのノードの型も一般化後の型になる。

   `Rigid` は一般化しない。
   スコーレム定数はスコープの中で共有する定数で、「どんな型でもよい」とは逆の意味を持つ。
   一般化すると、`run` のリージョンの安全性も、注釈の検査も成り立たなくなる。
   スコーレム定数を `Generic` に書き換えるのは、束縛のスコープを出るときで、
   第11章の `release_rigids` が行う(§11.27)。

   ### 既定化は一般化より先に

   `generalize` は、変数の `vcls` に `Integral` が入っていれば、
   `Generic` にせず `Int32` に `bind` する。
   `Fractional` が入っていれば `Float64` に `bind` する。
   この順序は入れ替えられない。
   `bind` は `Unbound` しか受け付けないので、先に `Generic` にすると、
   後で `bind` を呼んだときに `bug` で停止する。
   そのため、同じ `match` の中で予約述語を先に調べる。

   予約述語をクラス制約と同じ集合に入れた効果がここに現れる。
   `1 + x` のような式で、`x` の型の変数に `{Integral, Add}` が同時に付いたとき、
   既定化は `Int32` を選ぶ。
   そのとき `add_class` が、`Int32` に `Add` のインスタンスがあることを確かめる。
   予約述語のための別の経路を書かなくても、この順序を守るだけで制約の検査と整合する。

   ### default_numerics が一覧の変数を既定の型に決める

   予約述語つきの変数には、一般化点に到達しないものもある。
   式文として捨てられた中間結果の型の変数などである。
   `default_numerics` は宣言の終わりに、それらを既定の型に決める。
   §8.4 で制約つき変数の一覧(`class_vars`)に追加した変数をここで処理し、処理の後は一覧を空に戻す。

   宣言の終わりには、`check_ambiguity`(`~all:true`)と `default_numerics` を実行する。
   網羅性検査の遅延キューはそれより早く処理する。
   let 束縛のグループでは `generalize` の直前に、
   トップレベルの式では推論の直後に処理する(第11章 §11.14)。
   `generalize` の後でキューを処理すると、
   第10章(exhaust.ml)が `Generic` になった行変数に `unify` を適用する。
   `unbound_var` は `Generic` を単一化変数と見なさないので、`unify` は `bind` へ進まず、
   §8.7 の、スコーレム定数である行変数の分岐に入る。
   その結果、構造的ヴァリアントの行を閉じる `match` が、原因と関係のない型エラーになる。
   この順序は、`Generic` を単一化に渡さないという、§8.3 と同じ前提を守るためのものである。

   ### 既定化の失敗を報告する位置

   既定化は、予約述語つきの変数に付いたほかの制約を、既定の型に決めるときに初めて確かめる。
   `1.5 % 2.0` の `Rem` は、型を `Float64` に決めた時点で、満たせないと分かる。
   この時点では式の検査が終わっているので、外側の `at_node` に任せると、
   報告の位置は束縛の名前か宣言の先頭になる。
   そこで既定化は、失敗した制約の発生位置を自分で探し、`Type_error_at` で報告する。
   発生位置の手がかりは 2 つある。
   1 つは証拠の穴(§8.11)で、穴は制約を持ち込んだ参照や演算子の位置を持つ。
   もう 1 つは `literal_origins` で、予約述語を付けたリテラルの位置を記録している。
   予約述語には穴がないので、`1 + 1.5` の `Fractional` の位置は `literal_origins` から求める。
   本章で位置つきの例外を出すのはこの経路だけである。 *)

(* 予約述語つきの変数 v を既定の型 t に束縛する。
   束縛の前に、v の制約を 1 つずつ t に付けてみて、失敗した制約 c の発生位置で報告する。
   発生位置は、現在の宣言で作った c の証拠の穴のうち、最も古いものの位置
   (制約を持ち込んだ参照や演算子)である。
   穴のない予約述語では、その述語を付けた最も古いリテラルの位置である。
   前の宣言の一般化しない束縛から伝わった制約のように、
   現在の宣言に c の発生位置が見つからなければ、
   既定の型を選んだ予約述語 pred を付けた最も古いリテラルの位置で報告する。
   それも見つからなければ、位置なしの Type_error のまま投げ、外側の at_node に任せる。
   Int32 と Float64 は型引数を持たないので、
   ここで付けた制約を bind がもう一度付けても結果は変わらない *)
let default_to ~pred v t =
  let same u = match repr u with TVar r -> r == v | _ -> false in
  let origin c =
    let from_holes =
      List.filter_map (fun (_, (h : Tree.hole)) -> if h.h_id > !decl_hole_floor && h.h_sol = None && h.h_cls = c && same h.h_ty then Some h.h_loc else None) !holes
    in
    let from_literals c = List.filter_map (fun (r, c', loc) -> if c' = c && same (TVar r) then Some loc else None) !literal_origins in
    match (List.rev from_holes, List.rev (from_literals c), List.rev (from_literals pred)) with
    | loc :: _, _, _ | [], loc :: _, _ | [], [], loc :: _ -> Some loc
    | [], [], [] -> None
  in
  (match !v with
  | Unbound i ->
      List.iter
        (fun c ->
          let via = Option.map (fun (vt, vc) -> (subst_unbound v t vt, vc)) (Hashtbl.find_opt premise_origins (i.vid, c)) in
          try add_class ?via t c
          with Type_error msg -> ( match origin c with Some loc -> raise (Type_error_at (loc, msg)) | None -> raise (Type_error msg)))
        i.vcls
  | _ -> ());
  bind v t

(* level より深い Unbound を Generic にする。Rigid は一般化しない。
   予約述語つきの変数は既定の型に bind する(Integral なら Int32、Fractional なら Float64) *)
let rec generalize level t =
  match repr t with
  | TVar v -> (
      match !v with
      | Unbound i when i.vlevel > level ->
          if List.mem cls_integral i.vcls then default_to ~pred:cls_integral v t_int32
          else if List.mem cls_fractional i.vcls then default_to ~pred:cls_fractional v t_float64
          else set_tv v (Generic i)
      | _ -> ())
  | TCon (_, args) -> List.iter (generalize level) args
  | TApp (f, a) ->
      generalize level f;
      generalize level a
  | TArrow (p, r, e) ->
      generalize level p;
      generalize level r;
      generalize level e
  | TRecord row | TVariant row -> generalize level row
  | TRowEmpty -> ()
  | TRowExtend (_, f, rest) ->
      generalize level f;
      generalize level rest

(* 一般化しない束縛の終わりに、`level` より深い `Unbound` を `level` まで下げる。
   値でない束縛も、一般化する束縛と同じく、本体を 1 つ深いレベルで推論する(第11章 §11.28)。
   型に残った変数を深いレベルのまま環境に置くと、後に続く一般化する束縛の `generalize` が、
   その変数を一般化してしまう。
   制約つき変数の一覧 `class_vars` のうち番号が `since` より大きい項目、
   つまり束縛の本体を推論する間に追加した変数も下げる。
   下げないと、その本体で生じた曖昧な制約を報告する位置が、後に続く無関係な束縛に移る。
   束縛より前に追加した項目は下げない。
   一覧の全体をたどらない理由は 2 つある。
   1 つは時間である。
   全体をたどると、値でない束縛を並べた本体で、束縛の数の 2 乗に比例する時間がかかる。
   もう 1 つは報告の位置である。
   全体をたどると束縛の外で生じた深い変数まで下げるので、
   無関係な値でない束縛を挟むだけで、曖昧な制約を報告する位置が変わる。
   範囲を限っても、値でない束縛を入れ子にすると、外側の束縛は内側の束縛で追加した項目もたどるので、
   時間は入れ子の深さと項目の数の積に比例する。
   `Rigid` と `Generic` は書き換えない *)
let lower_levels ~since level t =
  let lower v = match !v with Unbound i when i.vlevel > level -> set_tv v (Unbound { i with vlevel = level }) | _ -> () in
  let rec go t =
    match repr t with
    | TVar v -> lower v
    | TCon (_, args) -> List.iter go args
    | TApp (f, a) ->
        go f;
        go a
    | TArrow (p, r, e) ->
        go p;
        go r;
        go e
    | TRecord row | TVariant row -> go row
    | TRowEmpty -> ()
    | TRowExtend (_, f, rest) ->
        go f;
        go rest
  in
  let rec walk = function (n, v) :: rest when n > since -> lower v; walk rest | _ -> () in
  walk !class_vars;
  go t

(* 宣言の終わりに、制約つき変数の一覧(class_vars)に残っている予約述語つきの変数を、
   既定の型に決める。
   残っているのは、一般化されなかった変数である。
   予約述語のない変数はどちらの分岐にも該当しないので、何もしない。
   一覧を古い順にたどるので、既定化の失敗が 2 つ以上あるときは、先に作った変数の失敗を報告する *)
let default_numerics () =
  List.iter
    (fun (_, v) ->
      match !v with
      | Unbound { vcls; _ } ->
          if List.mem cls_integral vcls then default_to ~pred:cls_integral v t_int32
          else if List.mem cls_fractional vcls then default_to ~pred:cls_fractional v t_float64
      | _ -> ())
    (List.rev !class_vars);
  class_vars := [];
  literal_origins := [];
  decl_hole_floor := new_oid ()

(* 型に現れる変数の vid を acc に集める *)
let rec collect_vars t (acc : (oid, unit) Hashtbl.t) =
  match repr t with
  | TVar r -> ( match !r with Link _ -> () | _ -> Hashtbl.replace acc (var_info_of r).vid ())
  | TCon (_, args) -> List.iter (fun a -> collect_vars a acc) args
  | TApp (f, a) ->
      collect_vars f acc;
      collect_vars a acc
  | TArrow (p, r, e) ->
      collect_vars p acc;
      collect_vars r acc;
      collect_vars e acc
  | TRecord row | TVariant row -> collect_vars row acc
  | TRowEmpty -> ()
  | TRowExtend (_, f, rest) ->
      collect_vars f acc;
      collect_vars rest acc

(* 制約つき変数のうち、型スキームの型から到達できないものを曖昧として報告する。
   調べるのは level より深い変数、つまりこれから一般化する変数である。
   all が真なら、宣言の終わりまで残った変数をレベルによらず調べる。
   予約述語(Integral / Fractional)が付いた変数は既定化で型が決まるので、対象外にする。
   対象にすると、let ne = 1 != 2 のように既定化に頼る式がすべてエラーになる。
   kept には、制約つき変数の一覧(class_vars)の項目のうち、まだ Unbound である変数だけを残す。
   理由は 2 つある。
   1 つは、到達できない予約述語つきの変数を、default_numerics が処理できるように残すためである。
   もう 1 つは、Link や Generic になった項目を取り除いて、
   走査の時間を一覧の長さに比例する範囲に保つためである。
   一覧は instantiate のたびに長くなる。
   取り除いても、型の決まらない制約つき変数を多く持つ宣言では、
   曖昧性を調べる回数と一覧の長さの積に比例する時間がかかる。
   極端な入力では、時間が入力の長さの 2 乗に比例する *)
let check_ambiguity ~all ~level tys =
  let reach = Hashtbl.create 32 in
  List.iter (fun t -> collect_vars t reach) tys;
  let kept = ref [] in
  List.iter
    (fun ((_, v) as e) ->
      match !v with
      | Unbound i ->
          kept := e :: !kept;
          if
            (all || i.vlevel > level)
            && i.vcls <> []
            && (not (List.exists is_predicate i.vcls))
            && not (Hashtbl.mem reach i.vid)
          then
            type_error
              ("曖昧な制約: "
              ^ String.concat " + " (List.sort compare (List.map display_of i.vcls))
              ^ " を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)")
      | _ -> ())
    !class_vars;
  class_vars := List.rev !kept

(* ## 8.10 map_generics と Generic の置き換え

   `instantiate` / `instantiate_ev`(§8.11)/ `subst_params` は、
   どれも型を走査して `Generic` を別の型に置き換える。
   違うのは置き換える先だけなので、走査は `map_generics_with` の 1 つにまとめる。
   `map_generics_with` は `Hashtbl` のメモを持ち、同じ `vid` の `Generic` には同じ結果を返す。
   このメモがないと、`A => A` の 2 つの `A` が別々の型になり、多相型を正しく具体化できない。
   第11章の包摂検査(§11.38)も、`map_generics_with` を直接呼んで、
   クラス宣言の型の `Generic` を現在のレベルのスコーレム定数に置き換える。

   | 関数 | `Generic` の置き換え先 | 使う箇所 |
   |---|---|---|
   | `instantiate` | 現在のレベルの新しい単一化変数 | perform と handle の節(第11章) |
   | `instantiate_ev` | 同じ。制約ごとに証拠の穴を作って返す | 変数参照、演算子、前置の `-`、包摂検査(第11章) |
   | `subst_params` | 指定された型引数(なければ新しい単一化変数) | 宣言表の型の展開(第10章と第11章) |

   ### instantiate は型クラス制約を複製する

   `instantiate` は `new_class_var ~kind:i.vkind ~classes:i.vcls level` で、
   カインドと制約の集合をまとめて複製する。
   `let double(x) = x + x` を一般化すると、`x` の型の変数は `{Add}` を持つ `Generic` になり、
   `double` の型は `[A: Add] (A) => A` になる。
   `double` を使うたびに、具体化が `{Add}` を持つ新しい単一化変数を作る。
   その変数が `Int32` と単一化されると、`bind` が `add_class` を呼び、
   `Int32` に `Add` のインスタンスがあるかを確かめる。
   制約の検査に必要な処理はこれだけである。
   複製しなければ、制約は使用箇所に伝わらない。

   複製した変数に制約が付いていれば、`new_class_var` がその変数を制約つき変数の一覧にも追加する。
   §8.4 で述べたとおり、一般化点に到達しない制約つき変数を宣言の終わりに処理し、
   途中の一般化点では曖昧性を調べるためである。
   `instantiate_ev` はプログラムの中で最も多く呼ばれる関数なので、一覧が長くなり続けないよう、
   `default_numerics` が宣言ごとに一覧を空に戻し、`check_ambiguity` も不要になった項目を取り除く。
   `instantiate_ev` は同じ複製をした上で、制約ごとに証拠の穴を作って返す(§8.11)。

   ### スコーレム定数への置き換えは vcls を引き継ぐ

   包摂検査が期待型の `Generic` から作るスコーレム定数は、`vkind` と `vcls` をそのまま引き継ぎ、
   識別子とレベルだけを新しくする(`new_rigid ~kind:i.vkind ~classes:i.vcls`)。
   `vcls` を引き継がないと、クラス宣言が期待型に書いた制約がスコーレム定数から消える。
   すると、インスタンス側の推論結果が持つ制約つき変数をそのスコーレム定数に束縛しようとした時点で、
   `add_class` が型エラーを報告する。
   その結果、包摂検査は正しいインスタンスまで「制約を書いてください」と拒否する。

   この置き換えは注釈つきの let の検査には使わない。
   `let f[A: Add](x: A) = ...` の `A` をスコーレム定数にするのは第11章の `make_rigids`(§11.25)である。
   `make_rigids` は `Generic` を置き換えるのではなく、
   `tp_classes` から `vcls` を組み立てて `Rigid` を直接作る。
   第11章が注釈の検査に使う 2 つの関数は `make_rigids` / `release_rigids` で、
   包摂検査の置き換えはそこに含まれない。

   どちらの経路でも、宣言に書いていない制約はスコーレム定数に付かない。
   そのため、§8.4 の `Rigid` の場合は「`[A: C]` のように制約を書いてください」と案内できる。

   ### ランク 1 多相

   `generalize` を適用するのは、let 束縛の型と、宣言から作る型スキーム
   (newtype のフィールド型、操作の型、クラスメソッドの型、シグネチャ、extern)だけである。
   `instantiate` を適用するのは、環境や宣言表から取り出した型スキームだけである。
   変数参照、演算子のメソッド、perform と handle の節の操作、包摂検査がそれに該当する。
   無名関数の引数には、推論モードでは新しい単一化変数を、
   検査モードでは期待型のフィールド型を割り当てる。
   どちらの型も、無名関数の本体の中では一般化しない。
   そのため、引数を 2 つの異なる型で使うと単一化に失敗する。
   この呼び出し方の規則によって、多相はランク 1 に限られる。
   型の中に量化子を持たず、変数が `Generic` であることだけで多相を表す設計は、
   この規則を前提にしている。
   Keleut は多パラメータ型クラスを持たないので(sample.kel:356)、
   型スキーム専用のデータ型も不要である。
   本章には `Scheme` に相当する型がない。

   `reset` は、本章が持つ一覧と表を空に戻す。
   空にするのは、制約つき変数の一覧(`class_vars`)、`literal_origins`、
   証拠の穴の一覧(`holes`)、`premise_origins` である。
   `decl_hole_floor` も新しい番号に進める。
   呼び出し元は第11章の 3 か所にある。
   `start_program` は、プログラムの型検査を始める前の初期化として、
   警告の一覧や第10章のキューを空にする処理と並べて呼ぶ。
   `start_input` は、対話的な実行の入力ごとの初期化として、同じように呼ぶ。
   `process_decls` はパス 2 に入る直前に呼ぶ。
   これは、パス 1(インスタンスの対象の型や前方参照のシグネチャの instantiate)で追加された制約つき変数を、
   宣言ごとの曖昧性の判定に持ち込まないためである。
   `type_check_decls` は `start_program` を 1 回呼び、
   `process_decls` をプレリュードとユーザの宣言に 1 回ずつ呼ぶので、
   1 回の型検査で `reset` は 3 回実行される。 *)

let map_generics_with memo f t =
  let rec go t =
    match repr t with
    | TVar v -> (
        match !v with
        | Generic i -> (
            match Hashtbl.find_opt memo i.vid with
            | Some t -> t
            | None ->
                let t = f i in
                Hashtbl.add memo i.vid t;
                t)
        | _ -> TVar v)
    | TCon (n, args) -> TCon (n, List.map go args)
    | TApp (g, a) -> tapp (go g) (go a)
    | TArrow (p, r, e) -> TArrow (go p, go r, go e)
    | TRecord row -> TRecord (go row)
    | TVariant row -> TVariant (go row)
    | TRowEmpty -> TRowEmpty
    | TRowExtend (l, fld, rest) -> TRowExtend (l, go fld, go rest)
  in
  go t

let map_generics f t = map_generics_with (Hashtbl.create 8) f t

(* Generic を現在のレベルの新しい単一化変数に置き換える。
   vkind と vcls も複製するので、型クラス制約はここで複製される。
   制約つきの変数は、new_class_var が制約つき変数の一覧に追加する *)
let instantiate level t =
  map_generics
    (fun i ->
      new_class_var ~kind:i.vkind ~classes:i.vcls level)
    t

(* Generic を指定した型に置き換える。
   指定のない Generic は新しい単一化変数に置き換える。
   データ宣言の型パラメータに型引数を代入して、
   コンストラクタのフィールドの型を展開するのに使う *)
let subst_params level args t =
  map_generics
    (fun i -> match List.assoc_opt i.vid args with Some t -> t | None -> new_class_var ~kind:i.vkind ~classes:i.vcls level)
    t

(* ## 8.11 証拠の穴

   型クラスのメソッドの選択は、型検査が型から決める(第5章 §5.1b)。
   制約つきの型スキームを具体化するたびに、制約ごとに穴を 1 つ作り、穴の一覧 `holes` に追加する。
   穴の型は、具体化で作った単一化変数そのものである。
   束縛の終わりに `solve_holes` が、その束縛の中で作った穴を解く。
   穴の型が決まっていれば `evidence_of` で証拠を作り、
   決まっていなければ新しい番号で一覧に追加し直す。
   一覧に戻した穴は、外側の束縛の終わりか、宣言の終わりに解く。
   単位の終わりまで解けない穴は、第11章が曖昧性エラーにする。

   ### 正準順

   辞書は位置で渡すので、定義する側(束縛の辞書パラメータ)と使う側(具体化で作る穴)が、
   同じ順序で制約を並べなければならない。
   この順序を正準順(canonical order。型だけから一意に決まる順序)と呼ぶ。
   `constraints_of` は、型スキームの型を左から右へたどり、`Generic` 変数が最初に現れた順に、
   その変数の制約を並べる。
   レコードとヴァリアントの行では、フィールドをラベル名のバイト列の昇順にたどり、
   同じラベルのフィールドは外側のものを先にする。
   1 つの変数の制約は、クラスの順位の昇順に並べる。
   順位は第6章が記録する番号で、組み込みのクラス、宣言されたクラスの順に振ってある。
   予約述語(`Integral` / `Fractional`)は並びに入れない。
   正準順は KIR の辞書の引数の順序でもあり、
   別の処理系が型だけから同じ並びを作れなければならない。
   行の中のフィールドの順序と `vcls` の中の順序は、
   単一化がソースのどの部分を先に処理したかで変わるので、どちらも正準順には使わない。
   `dkeys_of` は、正準順に並べた制約のキー(変数の `vid` とクラスの組)の並びを返す。
   `instantiate_ev` は、`map_generics_with` のメモから各 `Generic` の置き換え先を取り出して穴を作るので、
   置き換えの関数が呼ばれる順序には依存しない。
   型に現れない型パラメータは正準順に入らない。

   ### 証拠の作り方

   `evidence_of ~params c t` は、型 `t` がクラス `c` の制約を満たすことの証拠を作る。
   `params` は、囲む束縛の辞書パラメータのキーの並びである。

   | `t` の形 | 証拠 |
   |---|---|
   | `Generic` でキーが `params` にある | `EvParam` |
   | `Generic` でキーが `params` にない | `Unsolved_param`(第11章が曖昧性エラーにする) |
   | `Rigid` でキーが `params` にある | `EvParam` |
   | `Rigid` でキーが `params` にないもの、`Unbound` | 新しい穴 |
   | `TCon` | `EvInst`。前提の証拠は `ii_premises` の順 |
   | 構造的導出を持つクラスの `TRecord` / `TVariant` | `EvRecord` / `EvVariant`。閉じた行の各フィールドの証拠を、正準順と同じくラベル名の昇順に並べたもの |

   インスタンスがあることと、行が閉じていることは、ここでは確かめない。
   制約の付いた変数が具体的な型に束縛された時点で、
   `bind` が `add_class` を呼んで確かめているからである。
   それでも `TCon` のインスタンスが見つからない場合と、表のどれにも該当しない形は、
   処理系のバグなので `bug` で報告する。 *)

module TT = Tree

let hole_seq = ref 0

let hole_mark () = !hole_seq

let note_hole h =
  incr hole_seq;
  holes := (!hole_seq, h) :: !holes

let new_hole ~loc c t =
  let h = { TT.h_id = new_oid (); h_cls = c; h_ty = t; h_loc = loc; h_sol = None } in
  note_hole h;
  h

(* 行を先頭からたどり、(ラベル, フィールドの型) の並びと行の末尾を返す。
   行の末尾には repr を適用してある *)
let row_spine t =
  let rec go acc t = match repr t with TRowExtend (l, f, rest) -> go ((l, f) :: acc) rest | t' -> (List.rev acc, t') in
  go [] t

(* ラベル名のバイト列の昇順に並べる。
   同じラベルのフィールドは、外側のものが先になる順序を保つ *)
let sort_row_fields fields = List.stable_sort (fun (l1, _) (l2, _) -> String.compare (Type.name_of l1) (Type.name_of l2)) fields

let constraints_of t =
  let seen = Hashtbl.create 8 in
  let acc = ref [] in
  let rec go t =
    match repr t with
    | TVar v -> (
        match !v with
        | Generic i when not (Hashtbl.mem seen i.vid) ->
            Hashtbl.add seen i.vid ();
            let cs = List.filter (fun c -> not (is_predicate c)) i.vcls in
            let cs = List.stable_sort (fun a b -> compare (Decls.class_rank a) (Decls.class_rank b)) cs in
            List.iter (fun c -> acc := (i, c) :: !acc) cs
        | _ -> ())
    | TCon (_, args) -> List.iter go args
    | TApp (f, a) ->
        go f;
        go a
    | TArrow (p, r, e) ->
        go p;
        go r;
        go e
    | TRecord row | TVariant row -> go row
    | TRowEmpty -> ()
    | TRowExtend _ ->
        let fields, rest = row_spine t in
        List.iter (fun (_, f) -> go f) (sort_row_fields fields);
        go rest
  in
  go t;
  List.rev !acc

let dkeys_of t = List.map (fun ((i : var_info), c) -> (i.vid, c)) (constraints_of t)

(* instantiate と同じ置き換えを行い、置き換えた型と、正準順に並べた穴の並びを返す *)
let instantiate_ev ~loc level t =
  let cs = constraints_of t in
  let memo = Hashtbl.create 8 in
  let t' = map_generics_with memo (fun i -> new_class_var ~kind:i.vkind ~classes:i.vcls level) t in
  let hs = List.map (fun ((i : var_info), c) -> new_hole ~loc c (Hashtbl.find memo i.vid)) cs in
  (t', hs)

exception Unsolved_param of TT.hole * var_info

let rec evidence_of ~loc ~params ~(origin : TT.hole) c t =
  match repr t with
  | TVar v -> (
      match !v with
      | Generic i -> if List.mem (i.vid, c) params then TT.EvParam (i.vid, c) else raise (Unsolved_param (origin, i))
      | Rigid i when List.mem (i.vid, c) params -> TT.EvParam (i.vid, c)
      | _ -> TT.EvHole (new_hole ~loc c t))
  | TCon (n, args) -> (
      match Decls.find_instance ~cls:c ~con:n with
      | Some { ii_premises; _ } ->
          TT.EvInst (c, n, List.map (fun (i, c2) -> evidence_of ~loc ~params ~origin c2 (List.nth args i)) ii_premises)
      | None -> bug ("証拠: インスタンスがありません: " ^ display_of c ^ "[" ^ display_of n ^ "]"))
  | (TRecord row | TVariant row) as t' ->
      let structural = match Decls.find_class c with Some ci -> ci.Decls.ci_derive_structural | None -> false in
      if not structural then bug ("証拠: 構造的導出の無いクラスの構造的な型です: " ^ display_of c);
      let fields = sort_row_fields (fst (row_fields row)) in
      let evs = List.map (fun (l, f) -> (l, evidence_of ~loc ~params ~origin c f)) fields in
      (match t' with TRecord _ -> TT.EvRecord evs | _ -> TT.EvVariant evs)
  | _ -> bug ("証拠: 解けない型 " ^ show t)

(* 穴の一覧のうち、番号が lo より大きく hi 以下の穴を解く。
   解いた穴は一覧から外す。
   型の決まっていない穴は新しい番号で一覧に追加し直し、
   外側の束縛の終わりか、宣言の終わりに解く *)
let rec solve_holes ~since ~params = solve_holes_range ~lo:since ~hi:max_int ~params

and solve_holes_range ~lo ~hi ~params =
  let mine, older = List.partition (fun (n, _) -> n > lo && n <= hi) !holes in
  holes := older;
  List.iter
    (fun (_, (h : TT.hole)) ->
      if h.h_sol = None then
        match repr h.h_ty with
        | TVar { contents = Unbound _ } -> note_hole h
        | TVar { contents = Rigid i } when not (List.mem (i.vid, h.h_cls) params) -> note_hole h
        | _ -> h.h_sol <- Some (evidence_of ~loc:h.h_loc ~params ~origin:h h.h_cls h.h_ty))
    (List.rev mine)

(* 対話的な実行で結果を表示するための証拠を作る。
   穴は一覧に追加せず、型の決まっていない部分は解けていない穴のまま返す *)
let rec display_evidence c t =
  match repr t with
  | TCon (n, args) -> (
      match Decls.find_instance ~cls:c ~con:n with
      | Some { ii_premises; _ } -> TT.EvInst (c, n, List.map (fun (i, c2) -> display_evidence c2 (List.nth args i)) ii_premises)
      | None -> bug "display_evidence: インスタンスがありません")
  | TRecord row -> TT.EvRecord (List.map (fun (l, f) -> (l, display_evidence c f)) (sort_row_fields (fst (row_fields row))))
  | TVariant row -> TT.EvVariant (List.map (fun (l, f) -> (l, display_evidence c f)) (sort_row_fields (fst (row_fields row))))
  | _ ->
      TT.EvHole
        { TT.h_id = new_oid (); h_cls = c; h_ty = t; h_loc = { Location.start = Lexing.dummy_pos; finish = Lexing.dummy_pos }; h_sol = None }

let unsolved_holes () = List.filter (fun (_, (h : TT.hole)) -> h.h_sol = None) !holes

let reset () =
  class_vars := [];
  literal_origins := [];
  decl_hole_floor := new_oid ();
  Hashtbl.reset premise_origins;
  holes := []
