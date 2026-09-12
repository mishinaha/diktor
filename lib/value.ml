(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第12章 — 実行時の値

   ここから先は型が済んだ世界です。第11章 (elab.ml) が精緻化木のノードに型と
   `resolved` を書き込み、第5章 (tree.ml) の窓口越しにそれを渡してきました。
   本章の仕事はただ一つ、**その木を走らせたときに現れるものをどう表すか**を
   決めることです。評価規則そのものは第14章 (interp.ml)、プリミティブの中身は
   第13章 (builtin.ml) にあります。

   受け取るもの:

   - `Tree.Tree` の式・パターン(型注釈と `resolved` 入り)
   - `Syntax.Type` のインターン表。レコードとヴァリアントのラベル、操作名、
     コンストラクタ名は、型側とまったく同じ `Type.intern` の `oid` として持ちます。
     照合は整数の比較 1 回です。ただし**変数名だけは文字列のまま**で、
     §12.3 の環境のキーになります

   渡すもの:

   - 値の型 `t` と、その上のレコード演算(第13章・第14章が使う)
   - エフェクトのプロトコル `Op` と巻き戻し例外 `Unwind`(第14章が意味を与える)
   - 実行時エラー `Runtime_error`(第16章 (driver.ml) が終了コードに翻訳する)

   本章の設計判断は 1 行で言えます。**仕様が「同一物」と言っているものを、
   実装で別物にしない。** 計画 §13 の 2 が最大のレバレッジと呼んだ点です。
   Unit は空レコード、タプルはラベル `_item` の並んだレコード、
   操作を持たないエフェクトは型レベル専用。専用のコンストラクタを 1 つ足すたびに、
   等価・パターン照合・印字・行演算の四箇所すべてに分岐が波及します。

   > 仕様が同一物と呼ぶものに、実装で名前を 2 つ与えない。 *)
open Aux
open Syntax
module T = Tree.Tree
module SMap = Map.Make (String)

(* ## 12.1 値の一覧 — タグがそのまま実行時クラスになる

   | コンストラクタ | 表すもの | ディスパッチのタグ |
   |---|---|---|
   | `VBool` | 真偽値 | `Boolean` |
   | `VInt32` / `VInt64` / `VFloat64` | 3 つの数値型 | 同名の型構成子 |
   | `VText` | 文字列 | `String` |
   | `VRecord` | レコード・タプル・Unit | **なし**(構造的) |
   | `VVariant` | 構造的ヴァリアント | **なし**(構造的) |
   | `VData` | `newtype` の値 | `d_type` |
   | `VClosure` / `VPrim` | ユーザ関数 / 組み込み関数 | なし |
   | `VRef` / `VArray` | 可変セル / 配列 | `Ref` / `Array` |

   Diktor の型クラスは実行時に値のタグで解決します(計画 D3。第14章の
   `tycon_of_value` と `dispatch`)。右端の列は、その値を見せられたディスパッチャが
   どの型構成子の名前でインスタンス表を引くかです。要点は、**構造的な型である
   `VRecord` と `VVariant` にタグが無い**ことです。行で組み立てられる型は
   名目的な名前を持たないため、`derive structural` の構造的導出へ落ちます。
   タグが無いのはこの 2 つだけではありません。`VClosure` / `VPrim` にも
   ありませんが、こちらは構造的導出にも回りません — 関数にインスタンスは
   付かないからです。表の「なし」は 2 種類あって、**片方は構造へ落ち、
   もう片方は行き止まり**だと読んでください。

   MiniLang が型クラスを型変数に貼った制約集合で静的に解いたのに対し、
   Diktor は elab の判定と実行時の選択を**コヒーレンス**という 1 本の約束で
   結んでいます。同じ (クラス, 型構成子) に実体が 1 つしか無い以上、
   静的に選ぼうが動的に選ぼうが答えは一致します。

   `VData` が `d_type` と `d_ctor` の 2 つの `oid` を持つのは、
   ディスパッチが型で、パターン照合がコンストラクタで引くからです。
   `d_fields` は宣言順に詰めた配列で、名前付き引数の並べ替えは
   第11章が `resolved` の `RCtor` に添えた位置表で済ませてあります。
   実行時に名前で探す作業は残っていません。

   代償も書いておきます。この表現は**フィールドを名前で持たない**ので、
   `VData` の印字はコンストラクタ名と位置だけになり、レコードのように
   ラベル付きでは出せません(§12.7)。 *)

type t =
  | VBool of bool
  | VInt32 of int32
  | VInt64 of int64
  | VFloat64 of float
  | VText of string
  | VRecord of (oid * t) list (* Scoped Labels: 重複可・順序つき。先頭が最新。Unit = VRecord [] *)
  | VVariant of oid * t (* ペイロードは常に単値 *)
  | VData of { d_type : oid; d_ctor : oid; d_fields : t array }
  | VClosure of closure
  | VPrim of prim
  | VRef of t ref
  | VArray of t array

(* ## 12.2 クロージャの環境が可変である理由 — `let rec` を後から縛る

   `c_env` だけが `mutable` です。理由は再帰束縛ひとつです。

   `let rec even(n) = ... odd(n - 1)` を評価するとき、`even` のクロージャを
   作る時点では `odd` を含む環境がまだ存在しません。かといって環境を先に
   作ろうにも、その環境が指すべきクロージャがまだありません。
   鶏と卵なので、第14章 (`eval_rec_bindings`) は 3 段で解きます。

   1. 束縛群のクロージャを、いまの環境を指した状態で全部作る
   2. その全部を束縛した `locals` を作る
   3. **全クロージャの `c_env` をその `locals` に差し替える**(バックパッチ)

   OCaml 側で `let rec` を使って循環データを組む手もありますが、
   環境が不変 Map である以上「自分を含む Map」は素直には書けません。
   可変フィールド 1 つで買えるなら安いほうです。

   守るべき不変条件は 2 つあります。

   - バックパッチは束縛群のすべてのクロージャに対して、**本体が一度でも
     呼ばれる前に**完了していること
   - 右辺は関数でなければならないこと

   後者は 260829-2b の敵対的検証で埋めた穴です。3 段の手順が成り立つのは、
   右辺がクロージャ、つまり**評価を遅らせられる形**だからです。
   `let rec x = x + 1` のような非関数の右辺には置き場所がありません
   — 環境ができる前に評価するほかなく、その環境こそ作りたかったものです。
   第14章はここを実行時エラーにしますが、それ以前に型検査を通っていたのが
   問題でした。修正は第11章で拒否する側に入れてあります。
   実行時に必ず落ちるものを型検査で通してよい理由はありません。

   > 循環はデータ構造で組むか、可変フィールド 1 つで組むか。
   > 3 段の手順を守るなら後者のほうが安い。

   `prim` の `p_fn` が引数レコードを 1 つ取ることも書いておきます。
   Keleut の関数は多値を取り単値を返し、arity は矢印型の一部です
   (sample.kel:198-200)。呼び出し規約は「引数を並べたレコードを 1 個渡す」に
   統一されていて、ユーザ関数もプリミティブも同じ形で呼ばれます。 *)

and closure = {
  mutable c_env : env; (* let rec のバックパッチのため mutable *)
  c_params : T.pat list;
  c_body : T.exp;
}

and prim = { p_name : string; p_fn : t -> t (* 引数レコードを受け取る *) }

(* ## 12.3 環境の二層 — 可変な大域と不変な局所

   `globals` は可変ハッシュ表、`locals` は不変 Map です。この非対称は意図的です。

   - `globals` を全員で共有すると、トップレベルの相互参照と前方参照が
     ただで通ります。宣言を上から順に流し込むだけで、後から足された名前が
     先に作られたクロージャからも見えます
   - `locals` が不変なら、クロージャは `c_env` に**そのときの Map をそのまま**
     持てば済みます。コピーも寿命管理も要りません。第14章の評価が
     `{ env with locals }` を気軽に作れるのはこのおかげです

   逆に言えば、局所束縛の追加コストは Map の対数時間です。
   環境をハッシュ表 1 枚にして push/pop する実装より、深い再帰では
   わずかに遅く、そのかわりクロージャ捕獲が O(1) で正しくなります。 *)

and env = {
  globals : (string, t) Hashtbl.t;
  locals : t SMap.t;
  resume : resume option;
  (* 出身 module(D43)。module 内の宣言から作られた閉包はこれを覚え、
     非修飾名が globals に無かったとき module スコープの値同義語を引く。
     第11章の current_module の評価器側の対応物 *)
  mod_scope : string option;
}

(* ## 12.4 `resume` が値として存在しない理由(D19)

   一覧表(§12.1)に継続がありません。**これは書き忘れではなく設計です。**

   Keleut の `resume` は second-class です。仕様(sample.kel:353-356)は
   「変数に束縛する、クロージャに閉じ込める、返り値にする、はいずれも不可」と
   はっきり書いています。この制限があるからこそ、操作節を抜けた時点で継続の
   生死が確定し、`resume` を呼ばずに抜けたら自動巻き戻しという規則が成立します。

   計画 §8.2 の値表現には当初 `VResume of resume` が並んでいました。
   実装ではこれを落としています(実装記録 260829-2 の乖離 8)。
   値のコンストラクタとして存在した瞬間、`resume` はレコードに入れられ、
   配列に入れられ、関数から返せてしまいます。**値になれるものは、どこへでも
   行けます。** 一覧表に無ければ、どこへも行けません。

   そのかわり継続は環境の第 3 の欄 `resume` として運ばれ、操作節の本体を
   評価するあいだだけ `Some` になります。第14章はハンドラの `effc` で
   `{ env with locals; resume = Some r }` を作り、`return` 節・`cancel` 節・
   ガード式では `resume = None` に落とします。**節の外では文字どおり見えません。**

   それでも `fn() => resume(x)` は構文としては書けてしまうので、
   D19 は 2 段構えです。

   - 静的: 第11章が操作節の本体を走査し、`Lambda` の内側の `Resume` を
     エラーにする(内側の `Handle` 節に入ったら打ち切る)
   - 動的: ここの `r_alive` を節の終了時に `false` にし、
     持ち出された継続の呼び出しを実行時エラーにする

   `r_used` はアフィン性(高々 1 回)を守ります。OCaml 5 の継続はワンショット
   なので 2 度目は `Continuation_already_resumed` になりますが、
   その OCaml の例外をユーザに見せるのではなく、こちらで先に
   「resume は高々1回しか呼べません」と言うために持っています。
   Keleut がアフィン + second-class を選んだことと OCaml 5 の
   ワンショット継続が一致している、というのが計画 D2 の勘所でした。

   > second-class を守る最も確実な方法は、値の一覧に載せないことである。 *)

(* resume は second-class(D19)。値ではなく env 経由で操作節の本体だけに見える *)
and resume = {
  r_k : (t, t) Effect.Deep.continuation;
  mutable r_used : bool;
  mutable r_alive : bool;
}

(* ## 12.5 プロトコルの宣言 — `Op` と `Unwind`

   エフェクトの意味論は第14章のものですが、**型としての宣言だけ**はここに置きます。
   値と同じ場所に置かないと、第13章の `with_runtime` と第14章のハンドラが
   同じ `Op` を指せないからです。

   `Op` が運ぶのは (完全操作名の `oid`, 引数レコード) の 2 つだけです。

   - **完全操作名**: elab が `resolved` に書いた `Console.write` のような
     修飾済みの名前です。操作名の重複宣言は許されており(計画 D22。sample.kel
     自身が `Console.write` と `File.write` を両方宣言しています)、非修飾の
     `write` がどちらかを決めるのは第11章の仕事です。実行時には決着済みの
     `oid` の整数比較しか残りません
   - **引数レコード**: 呼び出し規約が §12.2 のとおり統一されているので
     (計画 D5)、操作の引数も普通の関数と同じ 1 個のレコードです

   `Unwind` はハンドラの**活性化 id** と、保留中の節の値を運びます。
   ここで id が AST ノードの id ではなく活性化ごとの採番であることが
   決定的に重要で、同じ `handle` 式が入れ子に活性化したとき
   (再帰の中の `handle`、`with_file` の 2 回呼び)、内側が外側宛の `Unwind` を
   自分宛と誤認して飲み込む誤動作を実測しています。第14章が `new_oid ()` で
   採番する理由です。

   自動巻き戻しを普通の例外ではなく専用の例外にしたのは、
   ユーザの例外(`Runtime_error` など)と区別して、自分宛の 1 枚だけが
   吸収するためです。ここでは宣言だけ。3 径路(値で抜ける・resume 済み・
   例外で抜ける)の扱いと `discontinue` の必然性は第14章で語ります。 *)

(* エフェクトのプロトコル(計画 §8.4): 完全操作名 oid * 引数レコード *)
type _ Effect.t += Op : oid * t -> t Effect.t

(* ハンドラ活性化 id * 保留中の節の値(計画 §8.4 の自動巻き戻し) *)
exception Unwind of oid * t

exception Runtime_error of string

let runtime_error msg = raise (Runtime_error msg)

(* ## 12.6 レコード演算 — Scoped Labels の実行時版

   第8章 (unify.ml) の `rewrite_row` が型の側で最左一致を実装したのと同じ規則を、
   ここでは値の側で実装します。**型と値で規則が食い違ったらその瞬間に不健全**
   なので、この節は型検査器の鏡だと思って読んでください。

   `VRecord` は (ラベル, 値) の**順序つきリスト**で、同じラベルが何度でも
   現れます。先頭が最新です。

   | 演算 | 意味 | 型側の対応 |
   |---|---|---|
   | `record_select` | 最左の同名を取り出す | 行からのフィールド取り出し |
   | `record_extend` | 先頭に cons する | `TRowExtend` |
   | `record_restrict` | 最左の同名を 1 つだけ消す | 行の尾部を取る |
   | `record_take` | 選択と制限を同時に | パターン照合が使う |
   | `record_update` | 最左の同名をその場で差し替える | ラベルは不変、型は変わりうる |

   3 つ気をつける点があります。

   **消すのは 1 つだけ。** `record_restrict` が同名を全部消してしまうと、
   `{x = 2 extends {x = 1}}` から `x` を取り除いたときに `x = 1` が
   復活しなくなります。Scoped Labels の重複はシャドウイングであって
   上書きではありません。

   **`record_update` は cons ではない。** `restrict` してから `extend` すれば
   同じラベル集合にはなりますが、そのフィールドが物理的に先頭へ移動します。
   異なるラベル間の物理順序は観測されうる(印字・構造的等価の実装)ため、
   その場での差し替えにしてあります(計画 §8.2)。

   ただし、値側と型側でやっていることがずれるのはここだけなので、表の右列を
   補足しておきます。型側の `RecordUpdate`(第11章 (elab.ml))はまさに
   「制限してから拡張」で型付けており、行はそのまま持ち越されるのではなく
   組み直されます。だから `{r with l = e}` はラベル集合こそ変えないものの、
   **フィールドの型は変えられます**。`r : {x: Int32, y: Int32}` に
   `{r with x = 文字列}` を書けば、結果は `{x: String, y: Int32}` です。
   値側がその場差し替えなのは物理順序を保つためであって、
   「行が変わらないから」ではありません。

   **順序が違っても等しいことがある。** 上の理由から、構造的等価は
   リストを頭から突き合わせる比較では**誤り**です。第14章の `structural_eq` は
   左のフィールドを順に見ながら右から `record_take` で最左同名を抜いて消す、
   という形で書かれています。`record_take` がここに居るのはそのためです。

   `unit` が `VRecord []` であることも、この節の一部です。Unit は特別な値
   ではなく、フィールドがゼロ個のレコードです。ブロックの末尾式が無いときも、
   `Async.sleep` を握り潰したときも、返るのはこれです。

   > 行の型は最左で一致する。値も最左で一致させる。 *)

  (* ---- レコード演算(Scoped Labels、計画 §8.2) ---- *)

let record_fields = function VRecord fs -> fs | _ -> runtime_error "レコードではない値へのレコード演算"

(* 最左の label を選択 *)
let record_select v label =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then x else go rest
  in
  go (record_fields v)

let record_extend v label x = VRecord ((label, x) :: record_fields v)

(* 最左の label を1つ消す(隠れていた同名が復活する) *)
let record_restrict v label =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then rest else (l, x) :: go rest
  in
  VRecord (go (record_fields v))

(* 選択 + 制限(パターン照合用) *)
let record_take v label =
  let rec go acc = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then (x, VRecord (List.rev_append acc rest)) else go ((l, x) :: acc) rest
  in
  go [] (record_fields v)

(* 最左の label をその場で差し替える(物理フィールド順を保つ、計画 §8.2) *)
let record_update v label x =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, y) :: rest -> if l = label then (l, x) :: rest else (l, y) :: go rest
  in
  VRecord (go (record_fields v))

let unit = VRecord []

(* ## 12.7 印字 — 診断と `show` は同じ表示器を使う

   ここの `show` は**実行時エラーメッセージのため**の印字です。
   Keleut のプログラムから見える `show` は `Show` クラスのメソッドで、
   その実体は第13章の `builtin_method` にあります。呼ばれる場所は
   違いますが、**Float64 の表示器は 1 つだけ**にして両方がそれを使います
   (D27)。かつて診断側だけ `string_of_float`(`%.12g` 相当)のままで、
   `0.1 + 0.2` の値が「match のどの節にも一致しません: 0.3」と、
   実際とは違う字面で報告されていました。表示器が 2 つあると、
   片方だけ直した状態が生まれます。

   その表示器 `float_repr` の要件は 2 段です(260829-2b で最短往復に
   直したものを、さらに 1 段強めました)。

   1. **`float_of_string` に対して往復する。** 出した字面を読み戻したら
      元の値に戻ること。桁を落とせば見た目は綺麗になりますが、その
      綺麗さは「同じ値だ」という誤った情報を伝えます。`0.1 + 0.2` が
      `0.30000000000000004` と出るのは正しい仕事です。
   2. **有限値なら、Keleut の Float64 リテラルとして読み戻せる。**
      `%g` の最短往復は `12345678901234568` のように小数点も指数も
      持たない字面を出すことがあり、それは Keleut では整数リテラルです。
      小数点も指数も無ければ `.0` を足します(往復は壊れません —
      小数部 0 は値を変えないので)。

   アルゴリズムは素朴です。`%.1g` から桁を 1 つずつ上げ、
   `float_of_string` で読み戻して一致したところで止める。IEEE binary64 は
   17 桁あれば必ず往復するので、17 で打ち切ります。最短表現の専用
   アルゴリズム(Ryu や Grisu)を持ち込まないのは、毎回最大 17 回の
   `sprintf` で足りるからです。表示は評価の内側ループではありません。

   整数値だけ `%.1f` で別扱いにしているのは、**型を見せるため**です。
   `%g` は 1.0 を `1` と印字しますが、Keleut の `1` は既定化 (D8) で
   Int32 になる別の値です。1e16 で切っているのは、それ以上は `%.1f` の
   桁数が延々と伸びるためで、大きい側は指数表記の最短往復 + `.0` の
   補完で受けます。

   非有限値は往復の原則の**外**です。Keleut には inf / nan のリテラルが
   無いので、読み戻せる字面はそもそも存在しません。黙って原則を破るのでは
   なく、`inf` / `-inf` / `nan` と表示すると決めます (D27)。NaN の符号を
   落とすのは、既定 NaN の符号ビットがアーキテクチャで違い(x86 は 1、
   ARM は 0)、言語からは観測できないからです — 見せると環境差だけが
   字面に漏れ、ゴールデンが環境で割れます。専用枝を先頭に置いたことで、
   NaN のとき往復探索が 17 回空回りしていた無駄も消えました。

   > 往復できない値があるなら、往復できないと書く。環境差を字面に漏らさない。

   この関数のもう 1 つの見どころは §12.1 の設計が素直に効いている箇所です。
   タプルが専用の値でないので、フィールドが 0 個なら `()`、
   全部が `_item` なら丸括弧の並び、それ以外なら波括弧、と
   **1 つの枝を 3 通りに読み分ける**だけで済みます。
   タプル専用のコンストラクタを持っていたら、ここに分岐がもう 1 本
   増えていたはずです — そして等価・パターン・行演算にも 1 本ずつ。

   丸括弧の並びには例外が 1 つあります。**1 要素のときは `(x,)`** と
   末尾カンマを打ちます(仕様 §4、D101)。`(x)` は式でもパターンでも
   ただのグループ化なので、実行時エラーに出た値をそのまま貼り戻すと
   1 要素タプルにならないからです。第9章 §9.3 が型に、第10章 §10.12 が
   網羅性の反例に、同じ規則を持っています。空のときに型は `{}`、
   値は `()` と出す非対称は意図的です — 仕様 §4 の「空行は `{}` のまま」は
   型の表示の規則で、値とパターンの位置では `()` が貼り戻せる字面です。 *)

let float_repr f =
  (* 非有限の専用枝は .0 補完より前に置く(順序を誤ると inf.0 が出る) *)
  if Float.is_nan f then "nan"
  else if f = Float.infinity then "inf"
  else if f = Float.neg_infinity then "-inf"
  else if Float.is_integer f && Float.abs f < 1e16 then Printf.sprintf "%.1f" f
  else
    let rec go p =
      if p > 17 then Printf.sprintf "%.17g" f
      else
        let s = Printf.sprintf "%.*g" p f in
        if float_of_string s = f then s else go (p + 1)
    in
    let s = go 1 in
    if String.exists (fun c -> c = '.' || c = 'e' || c = 'E') s then s else s ^ ".0"

  (* ---- 印字(実行時エラーの表示用) ---- *)

let rec show v =
  match v with
  | VBool b -> string_of_bool b
  | VInt32 n -> Int32.to_string n
  | VInt64 n -> Int64.to_string n
  | VFloat64 f -> float_repr f
  | VText s -> "\"" ^ String.escaped s ^ "\""
  | VRecord fs ->
      if fs = [] then "()"
      else if List.for_all (fun (l, _) -> l = Type.l_item) fs then
        (* 1 要素は (x,)。(x) は式でもパターンでもグループ化なので貼り戻せない(仕様 §4、D101) *)
        "(" ^ String.concat ", " (List.map (fun (_, x) -> show x) fs) ^ (match fs with [ _ ] -> ",)" | _ -> ")")
      else "{" ^ String.concat ", " (List.map (fun (l, x) -> Type.name_of l ^ " = " ^ show x) fs) ^ "}"
  | VVariant (l, VRecord []) -> "#" ^ Type.name_of l
  | VVariant (l, p) -> "#" ^ Type.name_of l ^ "(" ^ show p ^ ")"
  | VData { d_ctor; d_fields; _ } ->
      if Array.length d_fields = 0 then Type.name_of d_ctor
      else Type.name_of d_ctor ^ "(" ^ String.concat ", " (Array.to_list (Array.map show d_fields)) ^ ")"
  | VClosure _ -> "<fn>"
  | VPrim p -> "<prim " ^ p.p_name ^ ">"
  | VRef _ -> "<ref>"
  | VArray a -> "[" ^ String.concat ", " (Array.to_list (Array.map show a)) ^ "]"
