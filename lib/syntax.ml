(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第1章 — 型・カインド・行・AST

   この章は本全体の語彙表です。以降のすべての章は、ここで定義した
   `Type.ty` と AST の上でしか仕事をしません。読み始める場所であり、
   迷ったら戻ってくる場所でもあります。

   前章から受け取るものはありません。ここが入口です。
   次章以降へ渡すものは 2 つあります。

   - `Type` モジュール — 第8章 (unify.ml) が破壊的に動かし、
     第9章 (show.ml) が印字し、第11章 (elab.ml) が組み立てる型の宇宙。
   - `Syntax.Make` が作る AST — 第3章 (parser.mly) が組み立て、
     第5章 (tree.ml) が注釈欄を付け、第4章 (dump.ml) が覗きます。

   ## 見取り図

   実装の総量を抑える鍵は、**運ぶものの性質に応じて正しい運び手を選ぶ**
   ことです。機構を 1 つに統合することではありません。
   Diktor の運び手は 3 つあります。

   | 運び手 | 何を運ぶか | いつ決まるか |
   |---|---|---|
   | **レベル** (`vlevel`) | 一般化の可否、`run` スコープの内外 | 静的、整数比較 1 回 |
   | **行 (row)** | レコード・タプル・ヴァリアント・エフェクト | 動的、最も内側のハンドラ |
   | **型変数に貼った制約集合** (`vcls`) | クラス制約と予約述語 | 型から大域的に |

   言語機能と道具の対応は次のとおりです。左の列が Keleut の仕様
   (`../doc/sample.kel`)、右の列がこの実装の答えです。

   | 言語機能 | 実装に使う道具 |
   |---|---|
   | HM 多相・let 一般化 | 型変数の `vlevel` |
   | ランク 1 多相 | 量化子を型に持たず `Generic` マークで表す |
   | 値制限 | レベルを上げるかどうかを構文で決めるだけ (第11章) |
   | レコード・タプル | 行 + Scoped Labels。タプルは `_item` ラベルの行 (D4) |
   | 多引数関数 | `TArrow` の引数成分が閉じた `_item` 行 (D5) |
   | 構造的ヴァリアント | `TVariant`。中身は行 1 個 |
   | 名目的データ | `TCon` + 宣言表 (第6章)。型に宣言を埋めない |
   | エフェクト | 同じ行を `TArrow` の第3成分に載せる |
   | `run h` のスコープ安全性 | 剛定数 `Rigid` + レベル。ランク 2 は使わない |
   | 型クラス | `vcls` + 実行時の値タグによる動的ディスパッチ (D3) |
   | 高階カインド | `TApp` を 1 つ足すだけ。型レベルλは入れない |
   | カインド推論 | `KVar` + `same_kind` + 宣言終了時の既定化 (D7) |
   | 網羅性検査 | Maranget の usefulness (第10章) |
   | エフェクトの実行 | OCaml 5 の `Effect.Deep` (D2、第14章) |

   多引数クラスは入れません (D11)。Keleut の仕様が明示的に排除しており
   (sample.kel:318)、そのおかげで**型スキーマ用のデータ型を 1 つも
   持たずに済みます**。量化は `Generic` マークだけで表現できます。

   ## パイプライン

   ソースから答えまでの道は 4 区間です。

   ```
   ソース ─字句─▶ トークン列 ─構文─▶ AST ─精緻化─▶ 型付き木 ─評価─▶ 値
   ```

   - **字句** (第2章 lexer.ml): 生トークン、`{` の 3 分割、ASI の 3 層。
   - **構文** (第3章 parser.mly): Menhir。タプルや `t._0` はここで脱糖。
   - **精緻化** (第5・6・7・8・9・10・11章): 型を推論しながら、AST の
     ノードに型と解決結果を**書き込みます**。これが elaboration です。
     木は作り直しません。書き込む欄は第5章の `ElabData` にあります。
   - **評価** (第12・13・14章): 型付き木を辿ります。Keleut のエフェクトは
     OCaml 5 のエフェクトにそのまま写します。

   全体を束ねるのは第16章 (driver.ml) です。

   ## 章の対応表

   | 章 | ファイル | 何をするか |
   |---|---|---|
   | 1 | lib/syntax.ml | 型・カインド・行・AST(この章) |
   | 2 | lib/lexer.ml | 字句解析 — 3 層と ASI |
   | 3 | lib/parser.mly | 構文解析と脱糖 |
   | 4 | lib/dump.ml | AST を目で見る |
   | 5 | lib/tree.ml | 精緻化木 — 型検査は木への書き込み |
   | 6 | lib/decls.ml | 宣言環境 |
   | 7 | lib/prims.ml | 演算子と組み込みエフェクトの表 |
   | 8 | lib/unify.ml | 単一化 |
   | 9 | lib/show.ml | 型の表示 |
   | 10 | lib/exhaust.ml | 網羅性検査 (Maranget) |
   | 11 | lib/elab.ml | 型推論の本体 |
   | 12 | lib/value.ml | 実行時の値 |
   | 13 | lib/builtin.ml | プリミティブと組み込み実行環境 |
   | 14 | lib/interp.ml | 評価器 |
   | 15 | lib/prelude.kel | プレリュード |
   | 16 | lib/driver.ml | ドライバと終了コード規約 |

   この章の本体は syntax.ml の §1.1〜§1.17 です。脇役の 2 ファイルは
   最後に付けます — §1.18 が aux.ml、§1.19 が location.ml です。 *)

open Aux

(* ## 1.1 名前と経路

   最初に決めることが 2 つあります。**名前をどう持つか**と、
   **エラーをどこから投げるか**です。

   `long_id` は `Console.write` や `Parser.Result` のようなドット区切りの
   経路です。型・パターン位置では文法がそのまま作り、式位置では
   第3章の意味アクション (`dot_select`) が「先頭の連続する大文字成分 +
   直後の 1 成分」を畳んで作ります。だから最後の成分を除いてすべて
   大文字始まりである、という不変条件が付きます。`r.x.y` のような
   レコード選択とパス参照を、同じドットから読み分けるための規約です。

   `Syntax_error` は**意味アクションが投げる**構文エラーで、Menhir の
   `Parser.Error` とは別系統です。文法で表現すると LR(1) が壊れるが
   構文の誤りではある、という種類の誤り(たとえばレコードのラベルに
   大文字識別子を書いた場合)をここへ集めます。第16章はどちらも
   終了コード 2 に揃えます。 *)

type long_id = LongId of string list

exception Syntax_error of string

let long_id components = LongId components

let show_long_id (LongId components) = String.concat "." components

(* ## 1.2 名前のインターン

   `Type` モジュールに入ります。まずは名前の扱いです。

   行のラベル比較は単一化の内側ループで何度も走るので、文字列のままでは
   重すぎます。そこで**表の鍵になる名前を整数 (`oid`) に潰します**。
   `intern` は同じ文字列に同じ番号を返し、`name_of` が逆を引きます。

   潰す対象を名前空間ごとに分けないのが裁定です。レコードのラベル、
   エフェクト名と操作の完全名、型構成子、クラス名、コンストラクタ名、
   `extern` 名 — 全部同じ表に入れます。同じ綴りなら同じ `oid` に
   なります。名前空間の区別は、番号ではなく**使う側の表**が担います。
   第6章の `Decls.effects` に載っていればエフェクト名、`Decls.con_kinds`
   に載っていれば型構成子、という具合です。

   逆に、**値の識別子は潰していません**。`let` で束縛した名前も変数参照も
   文字列のままで、型検査の環境も評価器の環境も `Map.Make (String)` を
   鍵にします (第11章・第12章)。ですから「型検査のあらゆる名前比較が
   整数比較になっている」わけではありません。整数になっているのは、
   行のラベルのように**表を引く**経路だけです。

   この設計の利点は、行のラベル比較が `=` 1 回になることです。
   代償は、`oid` を単体で見ても何の名前か分からないことで、つまり
   **表を引く側が名前空間を知っている責任を持ちます**。実際にこれで
   困った箇所は今のところありません。

   名前空間ごとに表を分けないので、ラベルもエフェクト名も型構成子も
   `intern` / `name_of` の 1 組で足ります。以前は行を扱う側のために
   `label_to_oid` / `oid_to_label` という別名を置いていましたが、
   呼び出し側が 1 つも現れなかったので消しました (M19 / G1a)。
   **同じ操作に 2 つの名前を与えると、どちらを使うかの判断が読み手の
   負担になります。** *)

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

   カインドは**純粋に構造的**です。制約はカインドに載せません。
   `Functor[F]` の `F` は `[_] Type` のカインドを持つので、
   「制約は `Type` の変数に付く」という前提が高階カインドで崩れます。
   制約は §1.4 のとおり型変数そのものに貼ります。

   `KRow` を record / variant / effect で分けないのも裁定です。分けると
   第8章の `rewrite_row` を 3 回書くはめになります。行のラベルが何を
   意味するかは、その行を包んでいるノード(`TRecord` / `TVariant` /
   `TArrow` の第3成分)が決めます。

   ### MiniLang との差 — カインド変数 (D7)

   お手本の MiniLang はカインドを `KStar` / `KArrow` / `KRow` の 3 つで
   打ち止めにし、宣言表から引くだけで済ませています。Diktor は
   **`KVar` を 1 つ足します**。理由は Keleut の表層構文にあります。

   ```keleut
   let fst[A, R](t: {_item: A extends R}): A = t._item
   let with_log[A, E](body: () => A @ {Print extends E}): A @ E = ???
   ```

   `[A]` も `[R]` も `[E]` も、束縛子の見た目は同じです。`R` が行だと
   分かるのは `extends` の右に現れたときで、`E` が行だと分かるのは
   `@` の右に現れたときです。つまり**カインドは使用位置からしか
   決まりません**。唯一の例外が `F[_]`(sample.kel:382)で、これだけは
   字句でカインドが確定します。この扱いは `let` の束縛子だけのものでは
   なく、M23 (D80) からは newtype の型パラメータも同じ扱いに入りました
   — 仕様 §6 が「本体での使われ方から推論し、使われ方が無ければ Type」と
   定めたとおりです(第11章 §11.31)。

   そこで、`[_]` が書いてあればその場で `KArrow` を確定し、無ければ
   新しい `KVar` を与えて使用位置から推論し、宣言群の検査が終わった
   時点で残った `KVar` を `KStar` に既定化します(§1.6)。これは MiniLang の
   まとめが「カインドを推論したいだけなら Algorithm W をもう一度回して
   残ったカインド変数を `*` に既定化するだけで足りる」と書いている
   道そのもので、PolyKinds には踏み込みません。追加はおよそ 30 行です。 *)

  type kind =
    | KStar
    | KRow (* record / variant / effect 行で共通。分けない *)
    | KArrow of kind * kind (* F[_] *)
    | KVar of kind_ref (* D7。宣言終了時 KStar に既定化 *)

  and kind_ref = { k_id : oid; mutable k_link : kind option }

(* ## 1.4 型変数に貼りつくもの

   `cls` は制約集合です。集合と言いつつ `oid list` で、重複は
   追加時に弾きます。1 つの変数に付く制約はせいぜい数個なので、
   連想配列を持ち出す価値がありません。

   このリストには**予約述語**も相乗りします (D8)。`Integral` と
   `Fractional` は整数・小数リテラルの型を保留するための述語で、
   クラス制約と同じ場所に置くことで `1 + x` が `{Integral, Add}` を
   持つ、という状況が自動的に正しく扱えます。ユーザは同名のクラスを
   宣言できず(第11章の `register_class` が拒否)、一般化されずに
   既定値へ落とされる(第8章の `default_numerics`)、という 2 点だけが
   クラス制約との違いです。

   `var_info` は 4 状態が共有する中身です (D6)。カインドと制約集合を
   v0 から持たせています。MiniLang のまとめが「先に型クラスを入れて
   から制約をカインドから変数へ移すと作り直しになる。最初から変数に
   貼っておくのが賢明」と警告しているとおりです。

   なお MiniLang は制約付き変数を作った時点で台帳に控え、曖昧性検査に
   使います。Diktor の台帳 (第8章の `class_vars`) も M17 から同じです —
   制約つき変数をすべて控え、既定化の掃き出し (§8.9) と曖昧性検査
   (D48。スキーマの型から到達できない制約を報告する) の両方に使います。
   かつては予約述語つきだけを控えて既定化にしか使わず「残っている穴の
   1 つ」でしたが、その穴は塞がりました。v1 の予定項目にはスーパー
   クラスがありましたが、仕様 §8 が 2026-09-12 の改訂で「入れない」と
   確定したので、予定からも外れました (D98、§11.33)。 *)

  type cls = oid list

  type var_info = { vid : oid; vlevel : level; vkind : kind; vcls : cls }

(* ## 1.5 型

   型変数は**可変参照**です。`TVar of tvar ref` の `ref` が Union-Find の
   セルで、`Link` が親ポインタ、§1.7 の `repr` が経路圧縮つきの find です。
   ランクによる併合はしません — 型は木なので、経路圧縮だけで
   実用上の深さは潰れます。

   型変数の状態は 4 つです。

   - `Unbound i` — まだ未定。`i.vlevel` が一般化の可否を決めます。
   - `Link t` — すでに `t` と単一化済み。
   - `Generic i` — **一般化された**変数、すなわち ∀ で束縛された変数。
   - `Rigid i` — **剛定数** (skolem)。決して束縛されず、自分より浅い
     レベルへ漏れてはいけません。

   ここで最も重要なのは、型の中に `TForall` に当たるノードが
   **存在しない**ことです。量化子は「`Generic` の付いた変数が型の
   どこかにある」という形でしか表現できず、これがそのまま
   **ランク 1 多相**の制約になっています。同じ理由で、制約
   (`[A: Add]`) を型の中に書き残す場所も要りません。制約は変数に
   貼りついたまま一緒に量化されます。

   `Rigid` は 2 役です。`run h { ... }` のヒープをスコープに閉じ込める
   役と、型注釈の skolem 化(注釈より一般的な型でしか本体を
   受け付けない検査)の役。どちらも「レベルを上げて剛定数を作り、
   出口で浅いレベルへ漏れていないか見る」という同じ 3 行で、
   将来に存在型を足すときも同じ形になります。

   > 柔らかい変数は寿命を縮められる。剛定数は縮められない。

   ### レベル

   レベルとは「その型変数が何段目の束縛の内側で生まれたか」です。
   本体をレベル+1 で推論し、推論後に**レベルが現在より高い**未定変数
   だけを `Generic` にします。素朴な実装は環境の自由型変数を集めて
   それ以外を一般化しますが、環境走査は深い入れ子で二乗になります。
   レベルはこれを整数比較 1 回に落とす Rémy の古典的な最適化で、
   OCaml 自身の型検査器も同じ仕組みです。そしてレベルは剛定数の
   脱出検査という第 2 の仕事も兼ねます (第8章)。

   ### 型の構成子

   - `TCon (c, args)` — 名目型と組み込みスカラーの**飽和形**。
     宣言の中身(コンストラクタの並び)は型に埋めません。埋めると
     再帰型で一般化とインスタンス化が無限に走ります。中身は
     第6章の宣言表が持ちます。
   - `TApp (f, a)` — 高階カインドのための適用。**頭が型変数のときにしか
     現れません**。この不変条件は §1.7 の `tapp` と `repr` が守ります。
   - `TArrow (params, ret, eff)` — 矢印は 3 つ組です。第1成分は
     引数、第2成分は返り値、第3成分は**エフェクト行**。
   - `TRecord row` / `TVariant row` — 行を 1 個包むだけ。
   - `TRowEmpty` / `TRowExtend (label, field, rest)` — 行の本体。
     尾部が `TRowEmpty` なら閉じた行、型変数なら開いた行です。
     開いた行はレコードなら「そのラベルを含み、他は未定」、
     エフェクト行なら「そのエフェクトを起こしうる」を意味します。
     同じラベルの重複を許すのが Scoped Labels で、lacks 制約を
     捨てる代わりに最左一致で解決します (第8章)。

   ### なぜ引数がレコードなのか (D5)

   `TArrow` の第1成分は、`_item` ラベルだけを積んだ**閉じた行**を
   `TRecord` で包んだものです。`(A, B) => C` の引数は
   `{_item: A, _item: B}` になります。

   これで得られるものが 3 つあります。arity の検査が閉じた行の
   単一化から自動的に出ること (sample.kel:161-162)。ラベル付き引数
   `Cons(tail = t)` が同じ経路に乗ること。そしてタプルが行の糖衣に
   なり (D4)、`fst[A, R](t: {_item: A extends R})` のような
   「タプルの前置多相」がレコードの行多相と**同じ機構**で通ること。
   型・AST・値表現から `TTuple` を全廃できたのはこの裁定の帰結です。

   代償も正直に書いておきます。矢印がエフェクト行を持つ専用ノード
   である以上、矢印を 2 引数の型構成子として分解することはできません。
   Haskell で言う `Functor ((->) r)` — 関数型そのものを部分適用して
   高階カインドのインスタンスにすること — は書けません。 *)

  type ty =
    | TCon of oid * ty list (* 名目/組込み構成子の飽和形 *)
    | TApp of ty * ty (* HKT。頭が型変数のときだけ現れる(repr が保証) *)
    | TArrow of ty * ty * ty (* 引数(_item 行の TRecord)* 返り値 * エフェクト行 *)
    | TRecord of ty
    | TVariant of ty (* 構造的ヴァリアント。行1個 *)
    | TRowEmpty
    | TRowExtend of oid * ty * ty (* label * field(エフェクトならラベル引数)* rest *)
    | TVar of tvar ref

  and tvar = Unbound of var_info | Link of ty | Generic of var_info | Rigid of var_info

  (* ---- kind ---- *)

(* ## 1.6 カインドの単一化と既定化

   `KVar` を入れた瞬間に、**カインドの比較はすべて単一化になります**。
   MiniLang は `k != kt` の構造比較 1 行で済ませていますが、それは
   カインドが閉じた有限集合だったからです。Diktor で同じことを
   書くと、未解決の `KVar` どうしが常に不一致になります。

   `same_kind` は「一致するかを返し、一致するために `KVar` を張れるなら
   張る」関数です。返り値が `bool` なのは、呼び出し側がカインド不一致を
   自分のエラーメッセージで報告したいからです(第8章の `bind` は
   どちらのカインドが期待でどちらが実際かを知っています)。

   > カインドに変数を入れたら、カインドの比較はすべて単一化になる。

   ### 実際に踏んだ罠

   第8章の `rewrite_row` は当初、行変数かどうかを
   `vkind = KRow` の**構造マッチ**で判定していました。ところが arity 0 の
   型パラメータには `new_kind_var ()` が与えられるので、行位置で
   使われた変数のカインドは `KVar` が `KRow` へリンクした形をしています。
   構造マッチはこれを取りこぼし、sample.kel:166 の `fst`(:172-174 の
   コメントが説明している `{x = 1, _item = ...}` を渡す形)と :181-186 の
   `describe`(`describe(#Other)` の形。この再現例は仕様本文ではなく
   回帰テスト test/verify_fixes.t にあります)が型検査に落ちていました。判定を
   `same_kind` に置き換えて直りました。**カインドを直接パターンで
   見ている箇所は、それだけでバグ候補です。**

   `default_kind` は宣言**群**の検査が終わった時点で走ります (D7、D81)。
   忘れると `?k7` のような未解決カインドが表示に漏れ、
   使用位置の無い型パラメータのカインドが永久に決まりません。

   もう 1 つの罠は、早すぎる既定化です。`same_kind` は未解決の `KVar`
   どうしを片方に**張る**ので、宣言 1 つの検査が終わるたびに既定化すると、
   まだ本体を読んでいない別の宣言のカインド変数まで、張られた先を辿って
   `KStar` に固定されます。相互参照する newtype `A2[E] = MkA(B2[E])` と
   `B2[E] = MkB(() => Unit @ E)` で、先に処理した `A2` を既定化した瞬間に
   `B2` の `E` まで `Type` になる形です。だから newtype(と M28 からは型
   エイリアス)の既定化は第11章の 1b の後始末 — 宣言群が全部終わったあと —
   に置いてあります(§11.39)。

   `show_kind` は Keleut の表記に合わせます — `Type` / `Row` /
   `[_, _] Type`。`?k` 付きは既定化前にだけ見えるはずのものです。 *)

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

  (* 宣言終了時: 未解決の KVar を KStar に既定化する(D7) *)
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

(* ## 1.7 型適用の正規化 — tapp と repr

   高階カインドのために増えた型は `TApp` **ただ 1 つ**です。ただし
   `TCon (c, args)` を全部スパインに置き換えると、宣言表からクラス
   制約の伝播まで全箇所を触ることになります。そこで
   **関数位置が型変数のときだけ `TApp` を残す**正規化を採ります。
   頭が具体的な構成子なら飽和形 `TCon` に畳んでしまう、ということです。

   `tapp` がその畳み込みを行うスマートコンストラクタで、`repr` が
   「あとから頭が決まった」場合の畳み直しを行います。`TApp (α, Int32)`
   の後で `α := List` が決まったら、次に `repr` した時点で
   `List[Int32]` になります。以降のあらゆる関数は
   **まず `repr` してから match** が基本形なので、この数行を足すだけで
   正規化が実装全体に行き渡ります。

   `repr` の仕事は 3 つです。`Link` 連鎖をたどって代表元を返すこと。
   たどりながら経路を圧縮すること。そして `TApp` の頭を再正規化する
   こと。経路圧縮を忘れても答えは変わりませんが、深い連鎖で
   計算量が悪化します。`f' == f` の物理等価判定は、頭が変わらなかった
   ときに新しいノードを割り当てないための細工です。

   `repr` が 1 段しか正規化しないことにも注意してください。
   `TApp (f, a)` の `a` は触りません。必要な場所で各自 `repr` します。

   ### なぜ一階の単一化のままでいられるのか

   型変数が適用の**関数位置**に来ると `F[A] ~ List[Int32]` に複数解が
   ありそうに見えますが、**型レベルλが無ければ**そうなりません。

   - `F := List, A := Int32` — これだけです。
   - `F := λx. List[Int32]`(A を捨てる)や `F := λx. List[x]` は、
     λが書けないので候補になりません。

   つまり `F[A] ~ G[B]` は `F ~ G, A ~ B` に**構造分解**でき、mgu は
   1 つです。Haskell の高階カインドが一階単一化で済んでいるのは
   この理由です。よって本実装は 2 つの硬い規則を守ります。

   > **規則 1: 型レベルλを入れない。**
   > **規則 2: 部分適用できる型シノニムを入れない**(実質的に型λだから)。

   この 2 つを破った瞬間、単一化が unitary でなくなり、主要型も
   失われます。Keleut の `type` 宣言が非再帰かつ部分適用禁止なのは、
   規則 2 を**言語仕様の側で**守るためです (第6章と第11章が検査します)。

   `app_spine` は `TApp` の連鎖を頭と引数列に平らにします。表示
   (第9章) と、型クラスのディスパッチ (第11章・第14章) が使います。 *)

  (* TApp の正規化: 頭が飽和形 TCon なら引数に畳む(MiniLang の tapp) *)
  let tapp f a = match f with TCon (c, args) -> TCon (c, args @ [ a ]) | f -> TApp (f, a)

  (* Link 連鎖の経路圧縮 + TApp の頭の再正規化。
     以降の全関数は「まず repr してから match」を鉄則にする *)
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

   行に対する操作は 3 つだけです。この 3 つで、レコード・タプル・
   ヴァリアント・エフェクトのすべてを賄います。

   `row_fields` は行を「フィールドの列 + 尾部」に分解します。尾部は
   `TRowEmpty`(閉じた行)か型変数(開いた行)のどちらかです。
   開いた行 `{x: Int32 | ρ}` は「x を含み、他は未定」を意味し、
   これが**行多相の正体**です。

   `row_tail_var` は尾部が変数ならそれを返します。第10章が
   構造的ヴァリアントの網羅性を判定するとき、「もう他のケースは
   来ない」と宣言するために尾部を `TRowEmpty` へ束縛します。
   行を閉じる操作です。

   `row_append` は `a` のフィールドを `b` の前に積みます (splice)。
   `{Print extends E}` のようなエフェクト行の合成や、`extends` を
   含むレコード型がこれを使います。`a` が閉じていることは
   呼び出し側(第11章)が検査済みで、破れていたら `bug` を投げます。
   ここで型エラーではなく panic を投げるのは、これが**ユーザの誤りでは
   なく実装の不変条件違反**だからです。この使い分けは §1.18 の
   `Type_error` と `Panic` の 2 つの例外に対応しています。 *)

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

   既定は `KStar`・制約なしです。`new_row_var` はカインドを `KRow` に
   した別名で、名前が付いているだけで得があります — 行変数を作る
   つもりで `KStar` の変数を作ってしまう事故が読んで分かります。

   `new_rigid` は `?classes` を取ります。剛定数を作る場所は `run` の
   ヒープ、注釈の型パラメータ、明示エフェクト注釈と pub の尾部、
   インスタンス検査の skolem 化 — と複数ありますが、後の方は制約を
   運ぶか、あとから中身を書き換えるために `ref` そのものを要ります。
   だから `new_rigid_ref` と `new_rigid` の 2 段にしてあり、**`Rigid` を
   組み立てる式はこの 1 か所しかありません** (M19 / G5)。 *)

  let new_var ?(kind = KStar) ?(classes = []) level =
    TVar (ref (Unbound { vid = new_oid (); vlevel = level; vkind = kind; vcls = classes }))

  let new_row_var level = new_var ~kind:KRow level

  (* 剛定数のセル。release_rigids のように後から中身を書き換える側は
     ty ではなくこの ref を持つ必要がある(第11章 §11.27) *)
  let new_rigid_ref ?(kind = KStar) ?(classes = []) level =
    ref (Rigid { vid = new_oid (); vlevel = level; vkind = kind; vcls = classes })

  let new_rigid ?(kind = KStar) ?(classes = []) level = TVar (new_rigid_ref ~kind ~classes level)

  (* ---- 組み込み名(v0) ---- *)

(* ## 1.10 組み込みの名前

   ここに並ぶ `oid` は、実装のあちこちから名指しされる少数の名前です。
   1 か所に集めておくことが、第6章の「予約名の再宣言拒否」の土台に
   なります。

   `l_item` はタプルのラベルです (D4)。`(1, 2)` は
   `{_item: Int32, _item: Int32}` に、`t._0` は
   「`_item` を 0 回剥がしてから `_item` を選ぶ」に脱糖されます
   (第3章)。同じラベルを重複させて位置で数える、というのが
   Scoped Labels のうえでのタプルの実装です。

   組み込みスカラーは v0 では 6 つだけです。`Boolean` / `Int32` /
   `Int64` / `Float64` / `String` / `Never`。`Never` は
   コンストラクタが 0 個の名目型で、`n match {}` が網羅と判定される
   根拠になります (第10章)。他の数値幅(`Int8`、符号なし、`Float32`)は
   名前と接尾辞を**受理はして**、第11章が「v0 では未対応です」という
   型エラーで拒否します (D13)。

   `t_unit` に名目型はありません。**Unit は空レコード**です
   (sample.kel:51,144)。`()` と `{}` は同じ型で、単一化はレコードの
   経路にそのまま乗ります。`Unit` という名前はプレリュードの型
   エイリアスとしてのみ存在します (第15章)。

   `cls_integral` / `cls_fractional` は予約クラスです (D8)。ユーザ宣言は
   拒否され、一般化されず、既定値 `Int32` / `Float64` に落ちます。
   既定化を一般化より先に走らせるので、通常は表示に出ません。

   `eff_heap` / `eff_blocking` は**操作を持たない**組み込みエフェクト
   ラベルです。操作ゼロのエフェクト自体はソースにも書けます — 文法は
   `effect Silent = {}` のように空の本体を許します。にもかかわらず
   第6章がこの 2 つを表へ直接登録するのは、別の理由からです。

   `Heap` は `run` が導入し `Ref` と `MutableArray` の操作が要求する
   ラベルです。エフェクト**宣言**にパラメータを与える構文は v0 に
   ありません(§1.17 の `ef_params` は場所だけ空いていて、非空なら
   第11章が拒否します)が、型式の側では `@ {Heap[h]}` と書けるので、
   `Ref` / `MutableArray` の操作の型を `extern` の署名として書くこと自体は
   できます(第6章 §6.11)。それでも第6章 (decls.ml) の §6.11 がまとめて
   組み立てるのは、実装が OCaml 側の値と分かちがたく、プレリュードに
   置くと二重管理になるからです。`Blocking` は同じ組み込み表に相乗りするラベルで、
   `extern` がブロックしうることを表明するために名指しします
   (sample.kel:709,722)。

   ### 実際に踏んだ罠

   組み込みの型名を `newtype Boolean = Yes` のように再宣言すると、
   新しいデータ型として通ってしまい、網羅性検査と組み込み
   インスタンスの両方が破綻しました。いまは第6章の予約型名テーブルが
   再宣言を拒否します。名前をここに集めておくことが、その検査を
   「表を 1 つ引くだけ」にしています。ただし第6章はここの `ty` では
   なく文字列から `intern` し直します — 集めてあるのは**名前**であって
   定義ではなく、名前を 1 つ足すときに直す場所は第1章と第6章の
   2 か所です (M19 / G7e)。`t_never` はこの表を揃えるための 1 行で、
   `Never` の名前は第6章の `add_data` から引かれるため、この定数自体は
   使っていません。 *)

  let l_item = intern "_item" (* タプルのラベル(sample.kel §14 の TODO への裁定) *)

  let t_boolean = TCon (intern "Boolean", [])

  let t_int32 = TCon (intern "Int32", [])

  let t_int64 = TCon (intern "Int64", [])

  let t_float64 = TCon (intern "Float64", [])

  let t_string = TCon (intern "String", [])

  let t_never = TCon (intern "Never", [])

  (* Unit は名目型ではなく空レコード(sample.kel:51,144)。
     プレリュードの型エイリアスとしてのみ名前を持つ *)
  let t_unit = TRecord TRowEmpty

  (* 予約クラス(D8)。ユーザ宣言は拒否、一般化せず既定値に落とす *)
  let cls_integral = intern "Integral"

  let cls_fractional = intern "Fractional"

  (* 操作なしの組み込みエフェクトラベル。エフェクト宣言にパラメータを
     与える構文が v0 に無いので、decls.ml が Ref/Array/MutableArray ごと
     直接登録する(§1.10) *)
  let eff_heap = intern "Heap"

  let eff_blocking = intern "Blocking"
end

(* ## 1.11 リテラルと演算子

   `Type` を出て、表層構文の側へ移ります。

   数値リテラルは**字句テキストをそのまま保持**します (D13)。
   多倍長整数ライブラリは使いません。`0xff` も `0b1010` も `1_000` も、
   文字列のまま持っておけば `Int32.of_string` が理解します。値に
   するのは評価時で、そのとき第11章が決めた型を見ます。だから
   **既定化の結果がそのまま実行に反映されます** — `1 + 2` の
   `Integral` が `Int32` に落ちたことを、評価器はテキストと型から
   知ります。

   `n_suffix` は `1i64` / `1u8` / `1f32` の接尾辞です。v0 の実行時
   数値型は `Int32` / `Int64` / `Float64` の 3 種だけで、他の幅は
   字句としては受理し、第11章が型エラーで拒否します。負のリテラルは第3章が
   `HYPHEN NUMBER` を畳んで作ります。`n_suffix_text` は接尾辞の**原文**
   (無ければ空文字列)で、診断とダンプはこちらを使います — 解釈済みの
   `n_suffix` から表記を再構成すると、桁あふれの幅や先頭ゼロ (`1i032`) の
   字面が失われます (第2章 §2.1)。

   数値パターンの重複検出は**値で正規化**して行います。`0x1` と `1` は
   同じパターンです(第10章)。テキストのまま比較すると取りこぼします。
   同値関係は実行時の照合に合わせます — 整数は 64 ビット全域、浮動小数は
   IEEE の等価(±0.0 は同じパターン)です (D24)。

   `bin_op` は仕様の演算子表 (sample.kel:322-326) の縮小版です。
   演算子を `Apply` に脱糖しないのが裁定です (D9)。理由は 2 つ。
   `&&` と `||` は短絡するので関数呼び出しに落とせないこと、`!=` は
   `Eq.eq` の否定であって `Ne` というメソッドが存在しないこと。
   この 2 つの例外を**表の中に閉じ込める**ために、AST にノードを残し、
   第11章と第14章が第7章の同じ表を引きます。エラーメッセージが
   演算子の姿を保てるという副次的な利点もあります。剰余 `%` は
   仕様の演算子表に無いので入れません(プリミティブとして提供します)。

   なお Float の表示は最短往復表現で、有限値なら**必ず Float64 リテラル
   として読み戻せます**(第12章 §12.7)。かつては絶対値 1e16 以上の値が
   `12345678901234568` のように小数点も指数も持たない字面 — Keleut では
   整数リテラル — になり得ましたが、表示器が `.0` を補完して塞ぎました。
   非有限値 (inf / nan) にはリテラルが無いので、往復の対象外です。 *)

type num_suffix = NsInt of int | NsUInt of int | NsFloat of int (* i64 / u8 / f32 *)

type number = { n_text : string; n_is_float : bool; n_suffix : num_suffix option; n_suffix_text : string }

type bin_op = Add | Sub | Mul | Div | Eq | Ne | Lt | Le | Gt | Ge | And | Or

(* ## 1.12 型パラメータ束縛子

   `[A]` / `[h]` / `[F[_]]` / `[A: Add + Mul]` を 1 つのレコードで受けます。

   `tp_name` は大文字でも小文字でも構いません。リージョン変数は
   `run h { ... }` のように小文字で書かれます (sample.kel §10)。
   型変数と値の識別子は文法上の位置で区別できるので、字句で分ける
   必要がありません。

   `tp_arity` が 0 のときカインドは `KVar` になります。ここが §1.3 で
   述べた D7 の入口です。`F[_]` と書けば `tp_arity = 1` で `KArrow` が
   確定します。M23 (D80) からはこの記述が newtype の束縛子にも当てはまります
   — それまでは newtype も `KStar` 決め打ちで、ここは嘘でした。型クラス自身の
   パラメータ(`type class C[A]` の `A`)だけは今も `KStar` 固定です — インスタンスの
   選択が型構成子のタグで行われる以上、行のクラスは意味を持たないという読みで、
   仕様への確認は計画 260912-1 の C.10 の 7 にあります。

   `tp_classes` は `long_id list` です。クラス名も経路で書けるので
   (`Prelude.Add`)、素の文字列にはしていません。 *)

type type_param = {
  tp_name : string; (* 大文字/小文字どちらも可(リージョン変数 h 用) *)
  tp_arity : int; (* F[_] なら 1。0 ならカインドは KVar(使用位置から推論。型クラス自身のパラメータだけは KStar 固定) *)
  tp_classes : long_id list;
}

(* ## 1.13 Data ファンクタ — 同じ AST を二度使う

   AST の全ノードは `Data.t * ノード` のペアです。`Data` を差し替える
   ことで、**同じ AST 定義を注釈の異なる木として使い回します**。

   - `EmptyData` は `t = unit`。注釈を一切持たない最小の実体化です。
     **本実装ではどこからも実体化していません** — `Data` を差し替え
     られるという性質を、散文ではなくコードで見せるためだけに置いて
     あります(§3.1 も同じ見本を指します。M19 / G1b)。
   - 第5章の `Tree.ElabData` は
     `{ oid; loc; mutable ty_field; mutable resolved }`。位置に加えて、
     推論した型と**解決結果**を書き込む欄を持ちます。

   第3章のパーサは Menhir の `%parameter <Data : Syntax.Data>` で
   同じように仮引数化されており、第16章のドライバが
   `Parser.Make (Tree.ElabData)` で実体化します。つまり
   **パース木がそのまま精緻化木になり、変換のコピーが 1 回も起きません**。
   `Syntax.Make` がアプリカティブファンクタである(同じ引数から作れば
   同じ型になる)ことがこれを許しています。ジェネレータ側とライブラリ側で
   別々に `Syntax.Make (ElabData)` と書いても型が一致します。

   `allocate` が受け取るのは `Location.span` です (D16)。以前は
   `unit -> t` でした。エラーに位置を出すには**全ノード**に span が要り、
   後付けすると全ノードの構築箇所を書き換えることになります。
   MiniLang のまとめも「型に出所(ソース位置)を持たせるのは、実用上は
   最重要の改善点」と書いています。ついでにトークンから位置ペイロードを
   外したことで、位置が 2 トークンずれる旧バグも消えました。

   代償は、全パターンマッチが `(_, Ident ...)` の形になることです。
   読みにくさと引き換えに、あらゆるノードが位置と型の置き場所を
   持ちます。 *)

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

(* ## 1.14 型式 — まだ型ではないもの

   `type_exp` は**表層に書かれた型の構文**であって、§1.5 の `ty` では
   ありません。両者を分けるのは、表層の名前がまだ何者か分からない
   からです。第11章の `elab_type` が環境を見ながら `ty` へ落とします。

   `EIdent` は型変数・型構成子・型エイリアス・エフェクト名の
   どれでもあり得ます。区別は環境が持ちます。字句や文法では
   決まりません — `E` という 1 文字が、束縛子にあれば行変数、
   宣言表にあればエフェクトです。

   `EBraceRow` が 1 つでレコード型・エフェクト行・`EffectRow` エイリアスの
   本体を受けます。分けたくなりますが、分けると `@ {..}` の位置で
   reduce/reduce 衝突になることが試作で確認されています。要素の形
   (`BField` か `BLabel` か)で意味が決まる、という読み分けにしています。

   `EArrow` の第3成分が `None` なら `@` の省略です。省略の意味は
   文脈依存で、ここは実際に不健全性を踏んだ場所でもあります。
   かつて注釈内の省略 `@` が独立な行変数を生むため、前方参照された関数が
   過剰に一般化され、宣言順によってはエフェクト検査が丸ごと抜けていました。
   いまは入れ子の省略 `@` は `@ {}` に確定し(第11章 §11.4、M26)、前方参照に
   使えるのは注釈の**頭**の矢印に `@` が明示されたものだけです (§11.36)。

   `EUnion` は `#A | #B | R` と `IoError | ParseError` の両方を受けます。
   構造的ヴァリアントの合併とエフェクト行の合併が同じ縦棒で書かれる
   ので、AST では区別しません。

   `EHole` は `List[_]` の穴です。作られるのは**型引数の位置だけ**で、
   実際の用途は `type instance` の頭 (`type instance Functor[List[_]]`) に
   限られます。よく混同しますが、`F[_]` の束縛子の `_` は `EHole` に
   なりません — そちらは個数を数えて §1.12 の `tp_arity` になります。
   型引数位置に現れた `EHole` も、インスタンス頭以外では第11章が
   型エラーにします。 *)

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

   `PRecord` がレコードとタプルの両方を担います。第2要素が肝で、
   3 つの状態を 1 つのフィールドで表しています。

   | 第2要素 | 意味 | 書かれ方 |
   |---|---|---|
   | `None` | 閉じた行 | タプルパターン。arity が検査される |
   | `Some (_, PWildcard)` | 開いた行、尾部は捨てる | レコードパターンの既定 |
   | `Some p` | 開いた行、尾部を `p` に束縛 | `{x, ...rest}` |

   「レコードパターンは既定で開いている、タプルパターンは閉じている」
   という仕様の差が、コンストラクタを増やさずに表現できています。

   `PCtor` は名目コンストラクタのパターンですが、**`handle` の節の頭にも
   使います**。`write(msg) => ...` は構文的にはコンストラクタパターンと
   区別できないからです。どちらなのかの分類は第11章が行い、結果を
   第5章の `resolved` に書き込みます。ラベル指定の引数
   (`Cons(tail = t)`)があるので、実引数の位置とフィールドの位置の
   対応表も `resolved` へ入ります。

   `PAnnot` はパラメータの型注釈だけです。**式レベルの注釈ノードは
   持ちません**。`let b: Int64 = 0` の注釈も関数の返り値・エフェクト
   注釈も、すべて §1.16 の `let_binding` のフィールドに置きます。
   skolem 化の検査が束縛 1 つを単位に走るので、注釈も束縛に
   集めるほうが素直です。

   消したものも書いておきます。`as` パターン (`PCapture`) は表層構文に
   無く、消したことで 8 か所の特別扱いが消えました。or パターン、
   遅延パターン、リスト・配列リテラルパターンも v0 にはありません。
   `PUnit` は `PRecord ([], None)` に吸収されました — §1.10 のとおり
   Unit が空レコードだからです。 *)

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

   式の形はおおむね素直なので、裁定が現れている箇所だけ書きます。

   **`Apply` の第2引数は常に引数レコードです** (D5)。`f(1, 2)` は
   `Apply (f, {_item = 1, _item = 2})` です。関数適用のノードは
   1 引数のままで、arity は行が担います。

   **`Construct` と `Variant` は別物です。** 前者は宣言された名目
   コンストラクタで、閉じた型を持ち、再帰型と型パラメータが使えます。
   後者は構造的ヴァリアント `#Foo(e)` で、行多相の開いた型を持ちます。
   ペイロードは常に単値です — 複数個に見えるものはタプル、つまり
   `_item` 行です。

   **`RecordExtend` の評価順は value → rest です**。フィールドの
   並びと逆なので目で追うと間違えます。仕様 (sample.kel:240) が
   `{l = e extends r}` を「`e` が先、`r` が最後」と定めているためで、
   タプルの脱糖が先頭を最も外側に置く (第3章) ので、この向きだと
   `(a, b, c)` が a → b → c の順に評価されます。第14章も同じ順です。

   `RecordUpdate` が別ノードなのは、`{r with l = e}` が
   **物理的なフィールド順を保つ**必要があるからです。除去して
   足し直すと順序が変わり、表示が変わります。

   **`Match` のスクルティニは 1 つです** (D18)。Keleut は後置の
   `v match { ... }` しか持ちません。MiniLang の多スクルティニに
   見えるものは、タプル = `_item` 行なので同じ行列に落ちます。
   網羅性検査の内部表現だけは列数 1 のパターン行列にします (第10章)。

   **`Resume` が専用ノードなのは D19 です。** 構文が保証できるのは
   「`resume` を値として名前に束縛できない」ことまでで、
   `fn() => resume(x)` は依然として書けてしまいます。だから
   second-class 性は 2 段構えで守ります — 第11章が節の本体を走査して
   ラムダの内側の `Resume` を拒否し、第14章が実行時に
   継続の生存フラグを見ます。

   **`Handle` の節は `match` と共通の `clause` です。** `return` 節・
   `cancel` 節・操作節の分類は第11章が行い、結果を `resolved` へ
   書きます。パーサに分類させないのは、操作名の解決に宣言表が
   要るからです (D22)。

   `let_binding` は注釈の集積地です。`lb_params` が `None` なら
   値束縛、`Some ps` なら関数定義 — パーサは `Lambda` を作らずに
   パラメータをここに残します。値制限の判定と、関数だけに許される
   一般化の判定が、この 1 フィールドを見るだけで済みます。

   ### 実際に踏んだ罠

   `LetRec` の右辺が関数でない場合、型検査を通ったうえで実行時に
   必ず落ちていました。いまは第11章が拒否します。AST 側は依然として
   任意の式を受けます — 文法を狭めるより、検査を 1 か所に置くほうが
   エラーメッセージを良くできるからです。 *)

  type exp' =
    | Bool of bool
    | Number of number
    | Text of string
    | Ident of long_id (* 変数・パス参照。裸の ctor も *)
    | Hole (* ??? *)
    | Apply of exp * exp (* 第2引数は常に引数レコード(D5) *)
    | Construct of long_id * ctor_arg list (* Some(1) / Cons(tail = t)。ラベル付き引数 *)
    | Variant of string * exp (* #Foo(e)。ペイロードは常に単値 *)
    | BinOp of exp * bin_op * exp (* D9: elab / interp が prims.ml の表を引く *)
    | Not of exp (* ! のみ *)
    | Lambda of lambda (* fn(x, y) => e *)
    | Let of let_binding * exp
    | LetRec of let_binding list * exp
    | Seq of exp list (* 式文の列。let を含むブロックは Let(b, 残り) の入れ子 *)
    | Match of exp * clause list (* 単一スクルティニ(D18) *)
    | RecordEmpty
    | RecordExtend of exp * string * exp
        (* (rest, label, value)。評価は value → rest の順(sample.kel:240、計画 §8.3) *)
    | RecordUpdate of exp * string * exp (* {r with l = e}。物理フィールド順保持のため専用ノード *)
    | RecordRestriction of exp * string (* r \ l *)
    | RecordSelection of exp * string
    | Perform of long_id * exp (* perform print(msg)。解決済み完全名は resolved へ *)
    | Handle of exp * clause list
        (* 節は match と共通。分類は elab が行い resolved へ(計画 §7.3) *)
    | Resume of exp option (* D19。resume() / resume(e)。引数は record_of_args を通さない *)
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

   トップレベル・`module` の本体・`type instance` の本体を、
   **同じ `decl` 型**で受けます。3 つとも「宣言の並び」だからです。
   例外は 2 つ — `type class` の本体は `val m: T` の並び、
   `effect` の本体は `op: (T) => U` の並びなので、専用のレコードを
   持たせています。

   裁定が形に出ている場所を拾います。

   - `cls_params` が 1 個であることは第11章が検査します (D11)。
     多引数クラスを入れない裁定が、AST ではなく検査として現れます。
     文法は複数受けられるので、エラーメッセージを書けます。
   - `ef_params` は Keleut に対応する構文が**無い**フィールドです。
     型パラメータの非終端を共有しているので場所だけ空いており、
     非空なら第11章が拒否します。
   - `ex_abi` は 「prim」 か 「C」。前者は組み込みプリミティブへの
     割り当て、後者は実 FFI の予定地で、v0 では既知名の数学関数だけです。
     `extern` の**再宣言は拒否**します — 一度は
     `__int32_add` に嘘の型を後付けできてしまい、型検査ごと嘘に
     なりました。
   - `ex_prim` は**実装名**です。module の平坦化 (第11章) は `ex_name` を
     `M.f` に修飾しますが、`ex_prim` は元の非修飾名のまま残ります。
     実装表 (第13章) の探索と、登録簿 (第6章) のプレリュード保護の鍵は
     こちら。修飾名を鍵にすると、プレリュード保護が module の中から迂回
     でき、module に包んだ既知名 FFI の実装も黙って見つからなくなります
     (かつて両方が実測できました)。二重宣言の検査だけは修飾名で行います
     (§6.2 — 別々の module が同じ C シンボルを包む形を残すため)。
   - `nt_rhs` の `NtHole` は `= ???` です。`Never` はコンストラクタが
     0 個、すなわち `NtCtors []` です。
   - `DModule` の平坦化は第11章が行います(改名 + 非修飾名から
     修飾名への同義語表)。module 内 `let` の相互参照と module の
     入れ子は v0 では未対応です。
   - `DExp` はトップレベルの式文です (sample.kel:580)。
   - `ins_args` は通常 1 個で、`List[_]` のように `EHole` を含めます。
     本体が `let` だけであることは第11章が検査します。
   - `ins_tparams` は前提つきインスタンスの束縛子で、頭の `_` へ左から順に
     対応します (仕様 §8、D93)。**型は増えていません** — `type_param` を
     `let` / `class` / `newtype` と共有しています。

   syntax.ml はここまでです。残りは脇役 2 つ — §1.18 (aux.ml) が
   通し番号と例外の語彙、§1.19 (location.ml) が位置。
   そのあとの第2章 (lexer.ml) が、この AST を組み立てるための
   トークン列をソースから切り出します。 *)

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
    cls_params : type_param list; (* 1個であることは elab が検査(D11) *)
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
    | DExp of exp (* トップレベル式文(sample.kel:580) *)

  and decl = Data.t * decl'

  and instance_decl' = {
    ins_tparams : type_param list; (* 前提つきインスタンスの束縛子。頭の _ に左から対応(D93) *)
    ins_class : string;
    ins_args : type_exp list; (* 通常1個。List[_] の EHole 可 *)
    ins_body : decl list; (* let のみであることは elab が検査 *)
  }
end
