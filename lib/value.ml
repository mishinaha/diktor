(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第12章 実行時の値

   本章は、型検査を終えたプログラムを実行するときの値の表現を定める。
   第11章(elab.ml)は精緻化木のノードに型と `resolved` を書き込み、
   第5章(tree.ml)の窓口を通して評価器に渡す。
   評価規則は第14章(interp.ml)に、プリミティブの実装は第13章(builtin.ml)にある。

   本章が使うものは次の 2 つである。

   - `Tree.Tree` の式とパターン(型注釈と `resolved` が書き込まれたもの)
   - `Syntax.Type` のインターン表。
     レコードとヴァリアントのラベル、操作名、コンストラクタ名は、
     型の側と同じ `Type.intern` の `oid` で持つので、
     照合は整数の比較 1 回で済む。
     ただし変数名だけは文字列のまま持ち、§12.3 の環境のキーにする

   本章が外へ渡すものは次のとおりである。

   - 値の型 `t` と、その上のレコード演算(第13章と第14章が使う)
   - エフェクトのプロトコル `Op` と巻き戻しの例外 `Unwind`(意味は第14章が与える)
   - 実行時エラー `Runtime_error`(第16章(driver.ml)が終了コードに翻訳する)

   本章の設計の方針は、仕様が同じものとして扱うものに、実装で別々の表現を与えないことである。
   Unit は空のレコード、タプルはラベル `_item` が並んだレコードで表し、
   操作を持たないエフェクトは型の上にだけ存在する。
   Unit やタプルに専用のコンストラクタを足さないのは、1 つ足すごとに、
   等価、パターン照合、印字、行演算の 4 か所すべてに分岐が増えるからである。 *)
open Aux
open Syntax
module T = Tree.Tree
module SMap = Map.Make (String)

(* ## 12.1 値の一覧とディスパッチのタグ

   | コンストラクタ | 表すもの | ディスパッチのタグ |
   |---|---|---|
   | `VBool` | 真偽値 | `Boolean` |
   | `VInt32` / `VInt64` / `VFloat64` | 3 つの数値型 | 同じ名前の型構成子 |
   | `VText` | 文字列 | `String` |
   | `VRecord` | レコード、タプル、Unit | なし(構造的) |
   | `VVariant` | 構造的ヴァリアント | なし(構造的) |
   | `VData` | `newtype` の値 | `d_type` |
   | `VClosure` / `VPrim` | ユーザ関数 / 組み込み関数 | なし |
   | `VRef` | 可変セル | `Ref` |
   | `VArray` / `VMutArray` | 不変配列 / 可変配列 | `Array` / `MutableArray` |

   Diktor は型クラスのメソッドを、実行時に値のタグで解決する。
   解決するのは第14章の `tycon_of_value` と `dispatch` である。
   右端の列は、ディスパッチがその値を受け取ったときに、
   どの型構成子の名前でインスタンス表を引くかを示す。

   表の「なし」には 2 種類ある。
   構造的な型の値である `VRecord` と `VVariant` はタグを持たない。
   行で組み立てる型は名目的な名前を持たないので、
   これらの値は `derive structural` による構造的導出に回る。
   関数の値である `VClosure` / `VPrim` もタグを持たないが、関数にはインスタンスが付かないので、
   構造的導出の対象にもならず、どのインスタンスにも行き着かない。

   インスタンスがあることは型検査(elab)が静的に確かめ、実体は第14章の `dispatch` が実行時に選ぶ。
   この 2 つを結びつけるのが**コヒーレンス**、
   つまり同じ (クラス, 型構成子) に実体が 1 つしかないという性質である。
   実体が 1 つなら、静的に選んでも動的に選んでも同じ実体になる。

   `VData` が `d_type` と `d_ctor` の 2 つの `oid` を持つのは、
   ディスパッチは型で引き、パターン照合はコンストラクタで引くからである。
   `d_fields` はフィールドを宣言の順に詰めた配列である。
   名前付き引数の並べ替えは、第11章が `resolved` の `RCtor` に添えた位置の表で済んでいるので、
   実行時に名前でフィールドを探すことはない。

   その代わり、この表現はフィールドを名前で持たない。
   そのため `VData` の印字はコンストラクタ名と位置だけになり、
   レコードのようにラベル付きでは出せない(§12.7)。 *)

type t =
  | VBool of bool
  | VInt32 of int32
  | VInt64 of int64
  | VFloat64 of float
  | VText of string
  | VRecord of (oid * t) list (* Scoped Labels: 重複可、順序つき。先頭が最新。Unit = VRecord [] *)
  | VVariant of oid * t (* ペイロードは常に単値 *)
  | VData of { d_type : oid; d_ctor : oid; d_fields : t array }
  | VClosure of closure
  | VPrim of prim
  | VRef of t ref
  | VArray of t array
  | VMutArray of t array

(* ## 12.2 クロージャの環境が可変である理由

   クロージャのフィールドのうち、`mutable` なのは `c_env` だけである。
   `c_env` を可変にするのは、再帰束縛のためである。

   `let rec even(n) = ... odd(n - 1)` を評価するとき、
   `even` のクロージャを作る時点では、`odd` を含む環境はまだ存在しない。
   一方、環境を先に作ろうとしても、その環境に入れるクロージャがまだない。
   そこで第14章の `eval_rec_bindings` は、次の 3 段で両者を作る。

   1. 束縛群のクロージャを、いまの環境を指した状態ですべて作る
   2. それらをすべて束縛した `locals` を作る
   3. すべてのクロージャの `c_env` を、その `locals` に差し替える(バックパッチ)

   OCaml の `let rec` で循環したデータを組む方法もあるが、環境は不変の Map なので、
   自分自身を含む Map は素直には書けない。
   可変のフィールドを 1 つ置くほうが簡単である。

   この手順は、次の 2 つの不変条件に依存する。

   - バックパッチは、束縛群のすべてのクロージャについて、どの本体も呼ばれる前に完了している
   - 右辺は関数である

   右辺が関数でなければならないのは、
   3 段の手順が右辺の評価を遅らせられることを前提にしているからである。
   右辺がクロージャなら、本体の評価は呼び出しの時点まで遅れる。
   `let rec x = x + 1` のような関数でない右辺は、環境ができる前に評価するしかないが、
   その環境こそがこれから作ろうとしているものである。
   関数でない右辺は実行時に必ず落ちるので、第11章が型検査の段階で拒否する。
   第14章の `eval_rec_bindings` にも同じ内容の実行時エラーがあるが、
   型検査を通ったプログラムがそこに到達することはない。

   `closure` と同じ型宣言にある `prim` の `p_fn` は、引数レコードを 1 つ受け取る。
   Keleut の関数は複数の引数を取って 1 個の値を返し、
   引数の個数(arity)は矢印型の一部である(sample.kel:273-275)。
   呼び出し規約は、引数を並べたレコードを 1 個渡す形に統一してあり、
   ユーザ関数もプリミティブも同じ形で呼ぶ。 *)

and closure = {
  mutable c_env : env; (* let rec のバックパッチのため mutable *)
  c_params : T.pat list;
  c_body : T.exp;
}

and prim = { p_name : string; p_fn : t -> t (* 引数レコードを受け取る *) }

(* ## 12.3 環境の 2 つの層

   `globals` は可変のハッシュ表、`locals` は不変の Map である。
   この非対称は、次の理由による。

   - `globals` を全体で共有すると、トップレベルの相互参照と前方参照が追加の仕組みなしに通る。
     宣言を上から順に流し込むだけで、後から足した名前が、先に作ったクロージャからも見える
   - `locals` が不変なら、クロージャは `c_env` にそのときの Map をそのまま持てばよく、
     コピーも寿命の管理も要らない。
     第14章の評価が `{ env with locals }` を気軽に作れるのはこのためである

   その代わり、局所束縛を 1 つ追加するたびに、Map への挿入に対数時間がかかる。
   この 2 層の構成は、環境をハッシュ表 1 つにして push と pop で管理する実装と比べると、
   深い再帰ではわずかに遅いが、クロージャによる環境の捕獲を O(1) で正しく行える。 *)

and env = {
  globals : (string, t) Hashtbl.t;
  locals : t SMap.t;
  resume : resume option;
  (* 出身の module。module 内の宣言から作ったクロージャはこれを覚えておき、
     非修飾名が globals に無かったとき、module スコープの値同義語を引く。
     第6章(decls.ml)の current_module に対応する評価器の側の情報 *)
  mod_scope : string option;
}

(* ## 12.4 `resume` が値でない理由

   §12.1 の一覧表には継続が無い。
   Diktor は継続を値として表さない。

   Keleut の `resume` は second-class である。
   仕様(sample.kel:542-545)は、`resume` を節の外へ持ち出す手段について、
   「変数への束縛、クロージャへの閉じ込め、返り値としての持ち出しは、いずれもできない」と定める。
   この制限があるので、操作節を抜けた時点で継続が生きているかどうかが確定し、
   `resume` を呼ばずに節を抜けたら自動で巻き戻すという規則が成り立つ。

   継続を表すコンストラクタ(`VResume` のようなもの)が値の型 `t` にあれば、
   `resume` をレコードや配列に入れたり、関数から返したりできてしまう。
   `t` にそのコンストラクタが無いので、継続を値としてどこかへ運ぶことはできない。

   その代わり、継続は環境の 3 つ目のフィールド `resume` に入れて運ぶ。
   このフィールドは、操作節の本体を評価するあいだだけ `Some` になる。
   第14章はハンドラの `effc` で `{ env with locals; resume = Some r }` を作り、
   `return` 節、`cancel` 節、ガード式では `resume = None` にする。
   したがって、節の外からは継続が見えない。

   それでも、`fn() => resume(x)` は構文としては書ける。
   そこで、second-class の制限を 2 段で守る。

   - **静的な検査**：第11章が操作節の本体を走査し、`Lambda` の内側の `Resume` をエラーにする
     (内側の `Handle` に出会ったら、本体だけを走査し、節には入らない)
   - **動的な検査**：節が終わるときに `r_alive` を `false` にし、
     持ち出された継続の呼び出しを実行時エラーにする

   `r_used` はアフィン性(呼び出しは高々 1 回)を守る。
   OCaml 5 の継続はワンショットなので、2 度目の再開は `Continuation_already_resumed` になる。
   `r_used` を持つのは、2 度目の再開を OCaml に渡す前に止め、OCaml の例外の代わりに、
   Keleut のエラーとして「resume は高々1回しか呼べません(アフィン)」と報告するためである。
   Keleut の `resume` はアフィンかつ second-class で、OCaml 5 の継続はワンショットである。
   両者の性質が合っているので、Keleut の継続を OCaml 5 の継続でそのまま表せる。 *)

(* resume は second-class。値ではなく env を通して、操作節の本体からだけ見える *)
and resume = {
  r_k : (t, t) Effect.Deep.continuation;
  mutable r_used : bool;
  mutable r_alive : bool;
}

(* ## 12.5 プロトコルの宣言 `Op` と `Unwind`

   エフェクトの意味は第14章が与えるが、型としての宣言だけは本章に置く。
   第13章の `with_runtime` と第14章のハンドラが同じ `Op` を参照するには、
   両方から見える値の章に宣言を置く必要がある。

   `Op` が運ぶのは、完全操作名の `oid` と引数レコードの 2 つだけである。

   - **完全操作名**：elab が `resolved` に書いた、`Console.write` のような修飾済みの名前である。
     別々のエフェクトが同じ名前の操作を宣言してよく、
     sample.kel 自身も `Console.write` と `File.write` を両方宣言している。
     非修飾の `write` がどちらを指すかは第11章が決めるので、
     実行時に残るのは解決済みの `oid` の整数比較だけである
   - **引数レコード**：呼び出し規約が §12.2 のとおり統一されているので、
     操作の引数も普通の関数と同じく 1 個のレコードである

   `Unwind` は、ハンドラの活性化 id と、保留中の節の値を運ぶ。
   この id は AST のノードの id ではなく、ハンドラの活性化ごとに振る番号である。
   同じ `handle` 式が入れ子に活性化したとき(再帰の中の `handle` や、`with_file` の 2 回の呼び出し)、
   ノードの id を使うと、内側のハンドラが外側宛の `Unwind` を自分宛と取り違えて飲み込んでしまう。
   第14章が `new_oid ()` で活性化ごとに採番するのはそのためである。

   自動の巻き戻しに専用の例外を使うのは、ほかの例外(`Runtime_error` など)と区別し、
   宛先のハンドラだけがそれを受け止めるようにするためである。
   節の終わり方は 3 つの経路に分かれる。
   resume 済みで値を返す場合、resume せずに値を返す場合、例外で抜ける場合である。
   それぞれの扱いと、`discontinue` が必要な理由は第14章で述べる。 *)

(* エフェクトのプロトコル。完全操作名の oid と引数レコードを運ぶ *)
type _ Effect.t += Op : oid * t -> t Effect.t

(* 自動の巻き戻し。ハンドラの活性化 id と保留中の節の値を運ぶ *)
exception Unwind of oid * t

exception Runtime_error of string

let runtime_error msg = raise (Runtime_error msg)

(* ## 12.6 レコード演算

   第8章(unify.ml)の `rewrite_row` は、型の側で最左一致の規則を実装している。
   本節は同じ規則を値の側で実装する。
   型と値で規則が食い違うと不健全になるので、本節の演算は型の側の規則にそのまま対応させる。

   `VRecord` は (ラベル, 値) の順序つきのリストで、同じラベルが何度でも現れてよい。
   先頭が最も新しいフィールドである。

   | 演算 | 意味 | 型の側の対応 |
   |---|---|---|
   | `record_select` | 最左の同名のフィールドを取り出す | 行からのフィールドの取り出し |
   | `record_extend` | 先頭に cons する | `TRowExtend` |
   | `record_restrict` | 最左の同名のフィールドを 1 つだけ消す | 行の残りを取る |
   | `record_take` | 選択と制限を同時に行う | パターン照合が使う |
   | `record_update` | 最左の同名のフィールドをその場で差し替える | ラベルは変わらず、型は変わりうる |

   これらの演算には、注意する点が 3 つある。

   1 つ目に、`record_restrict` が消すのは 1 つだけである。
   同名のフィールドをすべて消すと、`{x = 2 extends {x = 1}}` から `x` を取り除いたときに、
   `x = 1` が再び見えるようにならない。
   Scoped Labels での重複は隠蔽(シャドウイング)であって、上書きではない。

   2 つ目に、`record_update` は cons ではない。
   `restrict` してから `extend` しても同じラベルの集合になるが、
   そのフィールドが物理的に先頭へ移動する。
   異なるラベルの間の物理的な順序は印字(実行時エラーに出る値)から観測できるので、
   `record_update` はフィールドをその場で差し替える。

   値の側と型の側で処理がずれるのはこの演算だけなので、表の右列を補足する。
   型の側の `RecordUpdate`(第11章(elab.ml))は、制限してから拡張する形で型を付けるので、
   行はそのまま持ち越されず、組み直される。
   そのため `{r with l = e}` はラベルの集合を変えないが、フィールドの型は変えられる。
   `r : {x: Int32, y: Int32}` に対して `{r with x = 文字列}` と書けば、
   結果は `{x: String, y: Int32}` になる。
   値の側がその場で差し替えるのは物理的な順序を保つためであり、行が変わらないからではない。

   3 つ目に、フィールドの順序が違っても等しいレコードがある。
   そのため、構造的等価をリストの先頭から突き合わせる比較で実装すると誤りになる。
   第14章の `structural_eq` は、左のフィールドを順に見ながら、
   右のレコードから `record_take` で最左の同名のフィールドを取り出して消していく。
   `record_take` はそのための演算である。

   `unit` が `VRecord []` であることも、本節の規則の一部である。
   Unit は特別な値ではなく、フィールドを 1 つも持たないレコードである。
   第14章の評価器は、ブロックに末尾の式が無いときにこの値を返す。
   `with_runtime`(§13.6)は、`Async.sleep` を何もせずに再開するときにこの値を渡す。 *)

  (* ---- レコード演算(Scoped Labels) ---- *)

let record_fields = function VRecord fs -> fs | _ -> runtime_error "レコードではない値へのレコード演算"

(* 最左の label を選択する *)
let record_select v label =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then x else go rest
  in
  go (record_fields v)

let record_extend v label x = VRecord ((label, x) :: record_fields v)

(* 最左の label を 1 つ消す(隠れていた同名のフィールドが再び見える) *)
let record_restrict v label =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then rest else (l, x) :: go rest
  in
  VRecord (go (record_fields v))

(* 選択と制限を同時に行う(パターン照合と構造的等価が使う) *)
let record_take v label =
  let rec go acc = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then (x, VRecord (List.rev_append acc rest)) else go ((l, x) :: acc) rest
  in
  go [] (record_fields v)

(* 最左の label をその場で差し替える(フィールドの物理的な順序を保つ) *)
let record_update v label x =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, y) :: rest -> if l = label then (l, x) :: rest else (l, y) :: go rest
  in
  VRecord (go (record_fields v))

let unit = VRecord []

(* ## 12.7 印字と Float64 の表示器

   本節の `show` は、実行時エラーのメッセージに値を載せるための印字である。
   Keleut のプログラムから見える `show` は `Show` クラスのメソッドで、
   組み込みの 5 つの型の実体は第13章の `builtin_method` にある
   (`List` と `Option` の実体は第15章 §15.8 のプレリュードにあり、Keleut で書いてある)。
   2 つの `show` は呼ばれる場所が違うが、Float64 の表示器は `float_repr` 1 つだけにして、
   両方がそれを使う。
   表示器が 2 つあると、片方だけを変えたときに、同じ値が診断と `show` で違う字面になる。
   たとえば診断だけが `string_of_float`(`%.12g` 相当)を使うと、
   `0.1 + 0.2` の値を、実際の値とは違う `0.3` という字面で報告してしまう。

   `float_repr` の要件は次の 2 つである。

   1. **`float_of_string` に対して往復する**：出した字面を読み戻すと、元の値に戻る。
      桁を落とせば見た目は短くなるが、違う値を同じ値のように見せてしまう。
      `0.1 + 0.2` が `0.30000000000000004` と表示されるのは正しい。
   2. **有限値は、Keleut の Float64 リテラルとして読み戻せる**：
      `%g` の最短往復は、`12345678901234568` のように小数点も指数も持たない字面を出すことがあり、
      Keleut ではそれは整数リテラルになる。
      小数点も指数も無ければ `.0` を足す(小数部の 0 は値を変えないので、往復は壊れない)。

   アルゴリズムは素朴である。
   `%.1g` から桁を 1 つずつ増やし、`float_of_string` で読み戻して一致したところで止める。
   IEEE binary64 は 17 桁あれば必ず往復するので、17 桁で打ち切る。
   最短表現の専用のアルゴリズム(Ryu や Grisu)を使わないのは、
   表示が評価の内側のループに入らないので、最大 17 回の `sprintf` で足りるからである。

   整数値だけを `%.1f` で別に扱うのは、型を見せるためである。
   `%g` は 1.0 を `1` と印字するが、Keleut の `1` は既定化で Int32 になる別の値である。
   1e16 で区切るのは、それ以上の値では `%.1f` の桁数が値の大きさに応じて伸び続けるからで、
   大きい側の値は最短往復と `.0` の補完で扱う。
   仕様は、絶対値が 1e16 未満の整数値を小数点表記で出すと定めており(sample.kel:109)、
   この分岐と境界はそれをそのまま写している。

   指数表記の指数部からは、`+` と先頭の `0` を除く。
   たとえば `1e+16` ではなく `1e16`、`1e-05` ではなく `1e-5` と出す。
   `%g` は C の慣習に従って `e+16` の形を出す。
   これに対して仕様 §2 は、有効数字を 1 桁ずつ増やして最初に読み戻せた表記を使い、
   そのとき指数部の `+` と先頭の `0` を除くと定めている(sample.kel:109-110)。

   仕様の「最短」は有効数字の桁数についての性質で、
   固定小数点表記と指数表記のどちらを選ぶかには関わらない(sample.kel:111-113)。
   そのため、「最短」を整数値にそのまま当てはめて、`100000.0` を `1e5` にすることはしない。
   `%g` は、指数が -4 より小さい値を指数表記にする。
   `0.0001` は固定小数点表記に、`0.00001` は指数表記になる。
   この境界をそのまま使うのが仕様どおりである(`test/numeric.t` の short)。

   仕様は `.0` の補完を、絶対値が 1e16 未満の整数値の場合とそれ以外の場合の両方に課している(sample.kel:110-112)。
   ただし `%.1f` の字面は常に小数点を持つので、補完が必要になるのは最短往復の分岐だけである。
   そのため、`.0` を足す 1 行は下の `else` の中にしかない。

   非有限値は往復の原則の外にある。
   Keleut には inf や nan のリテラルが無いので、読み戻せる字面がそもそも存在しない。
   そこで、非有限値は `inf` / `-inf` / `nan` と表示する。
   NaN の符号を落とすのは、既定の NaN の符号ビットがアーキテクチャによって違い(x86 は 1、ARM は 0)、
   しかも言語からは観測できないからである。
   符号を表示すると、環境の違いだけが字面に現れ、ゴールデンテストの結果が環境によって変わる。
   非有限値の分岐は先頭に置くので、NaN のときに往復の探索が走ることはない。

   `show` の `VRecord` の分岐には、§12.1 の設計がそのまま効いている。
   タプルは専用の値ではないので、フィールドが 0 個なら `()`、すべてが `_item` なら丸括弧の並び、
   それ以外なら波括弧というように、1 つの分岐を 3 通りに読み分けるだけで済む。
   タプル専用のコンストラクタがあれば、ここに分岐がもう 1 つ増え、
   等価、パターン照合、行演算にも分岐が 1 つずつ増える。

   丸括弧の並びには例外が 1 つある。
   要素が 1 つのときは、`(x,)` のように末尾にカンマを付ける(sample.kel:182)。
   `(x)` は式でもパターンでもただのグループ化なので、末尾のカンマが無いと、
   実行時エラーに出た値をそのまま貼り戻しても 1 要素のタプルにならない。
   仕様 §4 は、`_item` だけからなる閉じた行をタプルの表記に戻して表示する対象を定めている(sample.kel:179-180)。
   対象は「型の表示、型エラーの文面、実行時エラーに出る値、網羅性警告の反例の 4 つすべて」である。
   前の 2 つは第9章 §9.3 が、実行時エラーに出る値は本節が、網羅性警告の反例は第10章 §10.12 が扱う。

   空の行を、型では `{}`、値では `()` と表示する非対称も、仕様の定めによる(sample.kel:181-182)。
   空の行は、どの位置でも `{}` と `()` のどちらで書いても同じものを指すので、
   仕様は型を Unit の表記に、値とパターンを 0 要素のタプルの表記にそろえた(sample.kel:183-185)。
   本節が出す `()` は、値の位置にそのまま貼り戻せる表記である。 *)

let float_repr f =
  (* 非有限値の分岐は .0 の補完より前に置く(順序を誤ると inf.0 が出る) *)
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
    (* 指数部の + と先頭の 0 を落とす(仕様 §2、sample.kel:110)。
       1e+16 は 1e16 に、1e-05 は 1e-5 になる。読み戻しは壊れない *)
    let s =
      match String.index_opt s 'e' with
      | None -> s
      | Some i ->
          let mant = String.sub s 0 i and ex = String.sub s (i + 1) (String.length s - i - 1) in
          let sign, digits =
            if String.length ex > 0 && (ex.[0] = '+' || ex.[0] = '-') then
              ((if ex.[0] = '-' then "-" else ""), String.sub ex 1 (String.length ex - 1))
            else ("", ex)
          in
          let rec strip d = if String.length d > 1 && d.[0] = '0' then strip (String.sub d 1 (String.length d - 1)) else d in
          mant ^ "e" ^ sign ^ strip digits
    in
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
        (* 1 要素は (x,)。(x) は式でもパターンでもグループ化なので貼り戻せない(仕様 §4) *)
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
  | VMutArray a -> "<mutable [" ^ String.concat ", " (Array.to_list (Array.map show a)) ^ "]>"
