(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第12章 実行時の値

   本章は、型検査を終えたプログラムを実行するときの値の表現を定める。
   第11章(elab.ml)は精緻化木のノードに型と `resolved` を書き込み、
   評価器は第5章(tree.ml)の関数でそれを読む。
   評価規則は第14章(interp.ml)に、プリミティブの実装は第13章(builtin.ml)にある。

   本章が使うものは次の 2 つである。

   - `Tree.Tree` の式とパターン(型と `resolved` が書き込まれたもの)
   - `Syntax.Type` のインターン表。
     レコードとヴァリアントのラベル、操作名、コンストラクタ名は、
     型の側と同じ `Type.intern` の `oid` で持つので、
     照合は整数の比較 1 回で済む。
     ローカル変数の名前だけは文字列のまま持ち、§12.3 の環境の `locals` のキーにする

   本章がほかの章に渡すものは次のとおりである。

   - 値の型 `t` と、レコードの値に対する演算(第13章と第14章が使う)
   - エフェクトのプロトコル `Op` と、巻き戻しの例外 `Unwind`(意味は第14章が与える)
   - 実行時エラー `Runtime_error`(第16章(driver.ml)が終了コードに変換する)
   - 値を表示する `show` と、Float64 の表示器 `float_repr`(§12.7)

   本章は、仕様が同じものとして扱うものに、実装で別々の表現を与えない。
   Unit は空のレコード、タプルはラベル `_item` が並んだレコードで表し、
   操作を持たないエフェクトは型の上にだけ存在する。
   Unit やタプルに専用のコンストラクタを設けないのは、1 つ設けるごとに、
   等価、パターン照合、表示、行演算の 4 か所すべてに分岐が増えるからである。 *)
open Aux
open Syntax
module T = Tree.Tree
module SMap = Map.Make (String)

(* 辞書パラメータのキー (型変数の vid, クラスの oid) で引く Map *)
module DMap = Map.Make (struct
  type t = int * int

  let compare ((v1, c1) : t) ((v2, c2) : t) =
    let r = Int.compare v1 v2 in
    if r <> 0 then r else Int.compare c1 c2
end)

(* ## 12.1 値の一覧

   | コンストラクタ | 表すもの |
   |---|---|
   | `VBool` | 真偽値 |
   | `VInt32` / `VInt64` / `VFloat64` | 3 つの数値型 |
   | `VText` | 文字列 |
   | `VRecord` | レコード、タプル、Unit |
   | `VVariant` | 構造的ヴァリアント |
   | `VData` | `newtype` の値 |
   | `VClosure` / `VPrim` | ユーザ関数 / 組み込み関数 |
   | `VRef` | 可変参照 |
   | `VArray` / `VMutArray` | 不変配列 / 可変配列 |
   | `VDict` | 型クラスの辞書 |
   | `VDictAbs` | 辞書を受け取る値 |

   型クラスのメソッドをどのインスタンスで呼ぶかは、型検査が型から決め、
   証拠として木に書く(第5章 §5.1b)。
   第14章は証拠から辞書 `VDict` を作り、辞書が指す (クラス, 型構成子) でインスタンス表を引く。
   値のタグは使わない。
   辞書パラメータを持つ束縛(制約付きの型パラメータを持つ関数や、制約付きで一般化した値)の値は
   `VDictAbs` で、辞書の並びを受け取って値を返す。
   型検査が選んだインスタンスと、実行時に使う実装が一致することは、**コヒーレンス**が保証する。
   コヒーレンスは、同じ (クラス, 型構成子) のインスタンスが 1 つしかないという性質である。

   `VData` が持つ `oid` はコンストラクタの `d_ctor` だけで、パターン照合はこれを比較する。
   値が属する型の `oid` は持たない。
   型クラスのインスタンスは辞書で選ぶので、実行時に値から型を知る必要がないからである。
   `d_fields` はフィールドを宣言の順に詰めた配列である。
   名前付き引数は、第11章が `resolved` の `RCtor` に添えた位置の表で宣言の順に並べ替えるので、
   実行時に名前でフィールドを探すことはない。

   その代わり、この表現はフィールドの名前を持たない。
   そのため `VData` の表示はコンストラクタ名と、宣言の順に並べたフィールドの値だけになり、
   レコードのようにラベルを付けては表示できない(§12.7)。 *)

type t =
  | VBool of bool
  | VInt32 of int32
  | VInt64 of int64
  | VFloat64 of float
  | VText of string
  | VRecord of (oid * t) list (* Scoped Labels。同じラベルの重複を許す順序つきのリストで、先頭が最も新しい。Unit は VRecord [] *)
  | VVariant of oid * t (* ペイロードは常に 1 個の値 *)
  | VData of { d_ctor : oid; d_fields : t array }
  | VClosure of closure
  | VPrim of prim
  | VRef of t ref
  | VArray of t array
  | VMutArray of t array
  | VDict of dict (* 辞書。型検査が選んだインスタンスと前提の辞書(第5章 §5.1b の証拠を評価したもの) *)
  | VDictAbs of dict_abs (* 辞書パラメータを持つ束縛の値。辞書の並びを受け取って値を返す *)

(* DInst は型クラスのインスタンスの辞書で、(クラス, 型構成子) と前提の辞書の並びを持つ。
   メソッドの実装は辞書に入れず、メソッドを呼び出す時点でインスタンス表から引く(第14章 §14.6)。
   DInst の最後の引数は、選んだメソッドのキャッシュである。
   DRecord と DVariant は構造的な Eq の辞書で、ラベルごとに値の型の辞書を持つ。
   DPending は型の決まっていない制約の辞書で、対話的な実行が結果を表示するときにだけ現れる *)
and dict =
  | DInst of oid * oid * t list * (string * t) list ref
  | DRecord of (oid * t) list
  | DVariant of (oid * t) list
  | DPending

(* 辞書を受け取る値。da_arity は受け取る辞書の個数である。
   da_last は、直前に受け取った辞書の並びとその結果のキャッシュである。
   次に受け取った並びの各要素が直前のものと物理的に同じなら、da_fn を呼ばずに結果を再利用する *)
and dict_abs = { da_name : string; da_arity : int; da_fn : t list -> t; mutable da_last : (t list * t) option }

(* ## 12.2 クロージャの環境が可変である理由

   クロージャのフィールドのうち、`mutable` なのは `c_env` だけである。
   `c_env` を可変にするのは、再帰束縛のためである。

   `let rec even(n) = ... odd(n - 1)` を評価するとき、
   `even` のクロージャを作る時点では、`odd` を含む環境はまだ存在しない。
   一方、環境を先に作ろうとしても、その環境に入れるクロージャがまだない。
   そこで第14章の `eval_rec_bindings` は、次の 3 段階の手順で両者を作る。

   1. 再帰群のクロージャを、`c_env` が現在の環境を指す状態ですべて作る
   2. それらをすべて束縛した `locals` を作る
   3. すべてのクロージャの `c_env` を、その `locals` を持つ環境に差し替える(バックパッチ)

   OCaml の `let rec` で循環したデータを作る方法もあるが、環境は不変の Map なので、
   自分自身を含む Map はそのままでは書けない。
   可変のフィールドを 1 つ置くほうが簡単である。

   辞書パラメータを持つ束縛は `VDictAbs` になり、バックパッチの対象にならない。
   この値は、辞書を受け取るたびに、手順 2 の `locals` を持つ環境でクロージャを作る。

   この手順は、次の 2 つの不変条件に依存する。

   - バックパッチは、再帰群のどのクロージャの本体が呼ばれるよりも前に、
     すべてのクロージャについて完了している
   - 右辺は関数である

   右辺が関数でなければならないのは、
   3 段階の手順が、右辺の評価を遅らせられることを前提にしているからである。
   右辺がクロージャなら、本体の評価は呼び出しの時点まで遅れる。
   `let rec x = x + 1` のような関数でない右辺は、環境ができる前に評価するしかないが、
   その環境は、これから作ろうとしているものである。
   関数でない右辺は、実行すれば必ず実行時エラーになるので、第11章が型検査の段階で拒否する。
   第14章の `eval_rec_bindings` にも同じ内容の実行時エラーがあるが、
   型検査に通ったプログラムがそこに到達することはない。

   `closure` と同じ型宣言にある `prim` の `p_fn` は、引数レコードを 1 つ受け取る。
   Keleut の関数は複数の引数を取って 1 個の値を返し、
   引数の個数(arity)は矢印型の一部である(sample.kel:273-275)。
   呼び出し規約は、引数を並べたレコードを 1 個渡す形に統一してあり、
   ユーザ関数もプリミティブも同じ形で呼ぶ。 *)

and closure = {
  mutable c_env : env; (* let rec のバックパッチのために可変にする *)
  c_params : T.pat list;
  c_body : T.exp;
}

and prim = { p_name : string; p_fn : t -> t (* 引数レコードを受け取る *) }

(* ## 12.3 環境の 2 つの層

   `globals` は可変のハッシュ表、`locals` は不変の Map である。
   2 つの層のデータ構造が違うのは、次の理由による。

   - `globals` を全体で共有すると、トップレベルの相互参照と前方参照が、追加の仕組みなしに動く。
     宣言を上から順に登録するだけで、後から追加した値が、先に作ったクロージャからも見える。
     キーは第11章が解決した参照先の宣言(`Tree.gref`)で、同名の再束縛は別のキーになる
   - `locals` が不変なら、クロージャは `c_env` にそのときの Map をそのまま持てばよく、
     コピーも寿命の管理も不要である。
     第14章の評価器が `{ env with locals }` を束縛のたびに作れるのはこのためである

   その代わり、ローカルの束縛を 1 つ追加するたびに、Map への挿入に対数時間がかかる。
   この 2 層の構成は、環境をハッシュ表 1 つにして push と pop で管理する実装と比べると、
   深い再帰ではわずかに遅いが、クロージャによる環境のキャプチャを O(1) で正しく行える。

   型クラスの辞書パラメータはローカルの層に属し、`locals` とは別の不変の Map `dicts` に、
   キー (型変数の vid, クラスの oid) で置く(第14章 §14.1)。
   ユーザが書く名前とはキーの空間が別なので衝突せず、整数の組の比較だけで引ける。
   `locals` と同じく不変なので、クロージャは `c_env` に環境を持つだけで辞書もキャプチャする。 *)

and env = {
  globals : (Tree.gref, t) Hashtbl.t;
  locals : t SMap.t;
  dicts : t DMap.t;
  resume : resume option;
}

(* ## 12.4 `resume` が値でない理由

   §12.1 の一覧表には継続がない。
   Diktor は継続を値として表さない。

   仕様は `resume` を第二級(second-class)の値と呼ぶ。
   ここでいう第二級は、`resume` を節の外へ持ち出せないという意味である。
   仕様(sample.kel:546-549)は、持ち出す手段について、
   「変数への束縛、クロージャへのキャプチャ、返り値としての持ち出しは、いずれもできない」と定める。
   この制限があるので、操作節を抜けた時点で継続が生きているかどうかが確定し、
   `resume` を呼ばずに節を抜けたら自動で巻き戻すという規則が成り立つ。

   継続を表すコンストラクタ(`VResume` のようなもの)が値の型 `t` にあれば、
   `resume` をレコードや配列に入れたり、関数から返したりできてしまう。
   `t` にそのコンストラクタがないので、継続を値として節の外へ渡すことはできない。

   その代わり、継続は環境のフィールド `resume` に入れて渡す。
   このフィールドは、操作節の本体を評価するあいだだけ `Some` になる。
   第14章はハンドラの `effc` で `{ env with locals; resume = Some r }` を作り、
   `return` 節、`cancel` 節、ガード式、再開しない操作の節では `resume = None` にする。
   したがって、操作節の本体の外からは継続が見えない。

   それでも、`fn() => resume(x)` は構文としては書ける。
   そこで、第二級の制限を次の 2 つの検査で守る。

   - **静的な検査**：第11章が操作節の本体を走査し、
     `Lambda` の本体と関数束縛の本体の中にある `Resume` を型エラーにする。
     内側の `Handle` では、本体だけを走査し、節は走査しない
   - **動的な検査**：節が終わるときに `r_alive` を `false` にし、
     持ち出された継続の呼び出しを実行時エラーにする

   `r_used` はアフィン性(呼び出しは高々 1 回)を守る。
   OCaml 5 の継続はワンショットなので、2 度目の再開は `Continuation_already_resumed` になる。
   `r_used` を持つのは、2 度目の再開を OCaml に渡す前に止め、OCaml の例外の代わりに、
   Keleut の実行時エラー `resume は高々1回しか呼べません(アフィン)` として報告するためである。
   Keleut の `resume` はアフィンかつ第二級であり、
   この性質がワンショットという OCaml 5 の継続の性質と合っているので、
   Keleut の継続を OCaml 5 の継続でそのまま表せる。 *)

(* resume は第二級である。値ではなく env のフィールドとして渡すので、
   操作節の本体からだけ見える *)
and resume = {
  r_k : (t, t) Effect.Deep.continuation;
  mutable r_used : bool;
  mutable r_alive : bool;
}

(* ## 12.5 プロトコルの宣言 `Op` と `Unwind`

   エフェクトの意味は第14章が与えるが、型としての宣言だけは本章に置く。
   第13章の `with_runtime` と第14章のハンドラが同じ `Op` を参照するには、
   両方の章から見える本章に宣言を置く必要がある。

   `Op` が持つのは、完全な操作名の `oid` と引数レコードの 2 つだけである。

   - **完全な操作名**：第11章が `resolved` に書いた、`Console.write` のような修飾済みの名前である。
     別々のエフェクトが同じ名前の操作を宣言してよく、
     標準環境の `Console.write` と、sample.kel が宣言する `File.write` がその例である。
     修飾なしで書いた `write` がどちらを指すかは第11章が決めるので、
     実行時に行うのは、解決済みの `oid` の整数比較だけである
   - **引数レコード**：呼び出し規約が §12.2 のとおり統一されているので、
     操作の引数も通常の関数と同じく 1 個のレコードである

   `Unwind` は、宛先のハンドラの id と、`unwind` 型の値を持つ。
   `unwind` 型の値は、再開する操作の節が `resume` を呼ばずに終わったときの節の値 `UValue` か、
   再開しない操作の節の本体を評価するクロージャ `UClause` である。
   `Unwind` が持つハンドラの id は、AST のノードの id ではなく、
   ハンドラの起動(`handle` 式の 1 回の評価)ごとに振る番号である。
   同じ `handle` 式が入れ子で起動する場面(再帰の中の `handle` や、
   `with_file` を 2 回呼んだ入れ子)で、
   ノードの id を使うと、内側のハンドラが、
   外側のハンドラ宛ての `Unwind` を自分宛てと取り違えて受け取ってしまう。
   第14章が `new_oid ()` で起動ごとに採番するのはそのためである。

   自動の巻き戻しに専用の例外を使うのは、ほかの例外(`Runtime_error` など)と区別し、
   宛先のハンドラだけがそれを受け取るようにするためである。
   再開する操作の節の終わり方は、次の 3 つの経路に分かれる。
   resume した後で値を返す場合、resume せずに値を返す場合、例外で抜ける場合である。
   再開しない操作の節の経路は 1 つで、本体を評価する前に継続を捨てる。
   それぞれの扱いと、`discontinue` が必要な理由は第14章で述べる。 *)

(* エフェクトのプロトコル。完全な操作名の oid と引数レコードを持つ *)
type _ Effect.t += Op : oid * t -> t Effect.t

(* 自動の巻き戻しが渡すもの。
   再開する操作の節が resume を呼ばずに終わったときの節の値か、
   再開しない操作の節の本体を評価するクロージャである *)
type unwind = UValue of t | UClause of (unit -> t)

(* 自動の巻き戻しの例外。宛先のハンドラの起動の id と、unwind 型の値を持つ *)
exception Unwind of oid * unwind

exception Runtime_error of string

let runtime_error msg = raise (Runtime_error msg)

(* ## 12.6 レコード演算

   第8章(unify.ml)の `rewrite_row` は、型の側で最左一致の規則を実装している。
   最左一致は、同じラベルが複数あるときに最も左のものを選ぶ規則である。
   本節は同じ規則を値の側で実装する。
   型と値で規則が食い違うと型システムが健全でなくなるので、
   本節の演算は型の側の規則にそのまま対応させる。

   `VRecord` は (ラベル, 値) の順序つきのリストで、同じラベルが何度でも現れてよい。
   先頭が最も新しいフィールドである。

   | 演算 | 意味 | 型の側の対応 |
   |---|---|---|
   | `record_select` | 最も左の同名のフィールドの値を返す | 行からのフィールドの取り出し |
   | `record_extend` | 先頭にフィールドを追加する | `TRowExtend` |
   | `record_restrict` | 最も左の同名のフィールドを 1 つだけ取り除く | 行の残りを取る |
   | `record_take` | 選択と除去を同時に行う | パターン照合が使う |
   | `record_update` | 最も左の同名のフィールドをその場で差し替える | ラベルは変わらず、型は変わることがある |

   これらの演算には、注意する点が 3 つある。

   1 つ目に、`record_restrict` が取り除くのは 1 つだけである。
   同名のフィールドをすべて取り除くと、`{x = 2 extends {x = 1}}` から `x` を取り除いたときに、
   `x = 1` が再び見えるようにならない。
   Scoped Labels では、重複したラベルは前のフィールドを隠す(シャドーイング)だけで、上書きはしない。

   2 つ目に、`record_update` は先頭への追加ではない。
   `record_restrict` の後に `record_extend` を行ってもラベルの集合は同じになるが、
   そのフィールドが物理的に先頭へ移動する。
   異なるラベルの間の物理的な順序は、実行時エラーに出る値の表示から観測できるので、
   `record_update` はフィールドをその場で差し替える。

   値の側と型の側で処理が違うのはこの演算だけなので、表の右の列を補足する。
   型の側の `RecordUpdate`(第11章(elab.ml))は、フィールドを除去してから拡張する形で型を付けるので、
   行はそのまま引き継がれず、組み直される。
   そのため `{r with l = e}` はラベルの集合を変えないが、フィールドの型は変えられる。
   `r : {x: Int32, y: Int32}` に対して `{r with x = 文字列}` と書けば、
   結果は `{x: String, y: Int32}` になる。
   値の側がその場で差し替えるのは物理的な順序を保つためであり、行が変わらないからではない。

   3 つ目に、フィールドの順序が違っても等しいレコードがある。
   そのため、構造的等価を、2 つのリストを先頭から順に比較する形で実装すると誤りになる。
   第14章の `record_eq`(§14.7)は、型検査が作った証拠のラベルを順に選び、
   両辺のレコードから `record_take` で最も左の同名のフィールドを取り出して比較し、
   残りのレコードで比較を続ける。
   第14章のレコードのパターンの照合も、同じように `record_take` でフィールドを 1 つずつ取り出す。

   `unit` が `VRecord []` であることも、本節の規則の一部である。
   Unit は特別な値ではなく、フィールドを 1 つも持たないレコードである。
   第14章の評価器は、ブロックに末尾の式がないときにこの値を返す。
   `with_runtime`(§13.6)は、`Console.write` を処理した後の継続にこの値を渡す。 *)

  (* ---- レコード演算(Scoped Labels) ---- *)

let record_fields = function VRecord fs -> fs | _ -> runtime_error "レコードではない値へのレコード演算"

(* 最も左の label の値を返す *)
let record_select v label =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.display_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then x else go rest
  in
  go (record_fields v)

let record_extend v label x = VRecord ((label, x) :: record_fields v)

(* 最も左の label を 1 つ取り除く。隠れていた同名のフィールドが再び見えるようになる *)
let record_restrict v label =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.display_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then rest else (l, x) :: go rest
  in
  VRecord (go (record_fields v))

(* 選択と除去を同時に行い、値と残りのレコードの組を返す。パターン照合と構造的等価が使う *)
let record_take v label =
  let rec go acc = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.display_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then (x, VRecord (List.rev_append acc rest)) else go ((l, x) :: acc) rest
  in
  go [] (record_fields v)

(* 最も左の label の値をその場で差し替える。フィールドの物理的な順序は変わらない *)
let record_update v label x =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.display_of label ^ " がありません")
    | (l, y) :: rest -> if l = label then (l, x) :: rest else (l, y) :: go rest
  in
  VRecord (go (record_fields v))

let unit = VRecord []

(* ## 12.7 値の表示と Float64 の表示器

   本節の `show` は、実行時エラーのメッセージと対話的な実行の結果に値を表示するための関数である。
   Keleut のプログラムから見える `show` は `Show` クラスのメソッドで、
   組み込みの 5 つの型の実装は第13章の `builtin_method` にある。
   `List` と `Option` の実装は第15章 §15.8 のプレリュードにあり、Keleut で書いてある。
   2 つの `show` は呼ばれる箇所が違うが、Float64 の表示器は `float_repr` 1 つだけにして、
   両方がそれを使う。
   表示器が 2 つあると、片方だけを変えたときに、同じ値が診断と `show` で違う表記になる。
   たとえば診断だけが `string_of_float`(`%.12g` 相当)を使うと、
   `0.1 + 0.2` の値を、実際の値とは違う `0.3` という表記で報告してしまう。

   `float_repr` の要件は次の 2 つである。

   1. **`float_of_string` で読み戻すと元の値に戻る**(ラウンドトリップ)。
      桁を減らせば見た目は短くなるが、違う値を同じ値のように見せてしまう。
      `0.1 + 0.2` が `0.30000000000000004` と表示されるのは正しい。
   2. **有限値は、Keleut の Float64 リテラルとして読み戻せる**。
      `%g` で作った読み戻せる最短の表記は、
      `12345678901234568` のように小数点も指数も持たないことがあり、
      Keleut ではそれは整数リテラルになる。
      小数点も指数もなければ `.0` を加える。
      小数部の 0 は値を変えないので、`.0` を加えても元の値に読み戻せる。

   `float_repr` は、`%.1g` から有効数字を 1 桁ずつ増やし、
   `float_of_string` で読み戻して一致したところで止める。
   IEEE binary64 の値は有効数字が 17 桁あれば必ず元の値に読み戻せるので、17 桁で打ち切る。
   最短の表記を求める専用のアルゴリズム(Ryu や Grisu)を使わないのは、
   値の表示は評価器の最も内側のループで行う処理ではなく、最大 17 回の `sprintf` で足りるからである。

   整数値だけを `%.1f` で別に扱うのは、表記から型が分かるようにするためである。
   `%g` は 1.0 を `1` と書くが、Keleut の `1` は既定化で Int32 になる別の値である。
   1e16 で区切るのは、それ以上の値では `%.1f` の桁数が値の大きさに応じて増え続けるからである。
   絶対値が 1e16 以上の整数値は、読み戻せる最短の表記を求める分岐と `.0` の補完で扱う。
   仕様は、絶対値が 1e16 未満の整数値を小数点表記にすると定めており(sample.kel:109)、
   この分岐と境界は仕様のとおりである。

   指数表記の指数部には、`+` と先頭の `0` を書かない。
   たとえば `1e+16` ではなく `1e16`、`1e-05` ではなく `1e-5` と書く。
   `%g` は C の慣習に従って `e+16` の形で書く。
   これに対して仕様 §2 は、有効数字を 1 桁ずつ増やして最初に読み戻せた表記を使い、
   そのとき指数部の `+` と先頭の `0` を書かないと定めている(sample.kel:109-110)。

   仕様の「最短」は有効数字の桁数についての規則で、
   固定小数点表記と指数表記のどちらを選ぶかには関わらない(sample.kel:112-113)。
   そのため、「最短」を整数値にそのまま適用して、`100000.0` を `1e5` にすることはしない。
   `%g` は、指数が -4 より小さい値を指数表記にする。
   `0.0001` は固定小数点表記に、`0.00001` は指数表記になる。
   仕様に従うには、この境界をそのまま使えばよい(`test/numeric.t` の `short.kel` が確かめる)。

   仕様は `.0` の補完を、絶対値が 1e16 未満の整数値の場合とそれ以外の場合の両方に定めている(sample.kel:110-111)。
   ただし `%.1f` の表記には必ず小数点があるので、補完が必要になるのは、
   読み戻せる最短の表記を求める分岐だけである。
   そのため、`.0` を加える 1 行は下の `else` の中にしかない。

   非有限値には、読み戻すと元の値に戻るという要件を適用しない。
   Keleut には inf や nan のリテラルがないので、読み戻せる表記が存在しない。
   そこで、非有限値は `inf`、`-inf`、`nan` と表示する。
   NaN の符号を表示しないのは、既定の NaN の符号ビットがアーキテクチャによって違い(x86 は 1、
   ARM は 0)、
   しかも言語からは観測できないからである。
   符号を表示すると、アーキテクチャの違いだけが表記に現れ、
   ゴールデンテストの結果がアーキテクチャによって変わる。
   非有限値の分岐は先頭に置くので、NaN のときに読み戻せる表記を探すことはない。

   `show` の `VRecord` の分岐は、§12.1 の設計のおかげで 1 つで済む。
   タプルは専用の値ではないので、この分岐の中で、フィールドが 0 個なら `()`、
   すべてが `_item` なら丸括弧の並び、それ以外なら波括弧と、3 通りに書き分けるだけでよい。
   タプル専用のコンストラクタがあれば、ここに分岐がもう 1 つ増え、
   等価、パターン照合、行演算にも分岐が 1 つずつ増える。

   丸括弧の並びには例外が 1 つある。
   要素が 1 つのときは、`(x,)` のように末尾にカンマを付ける(sample.kel:182)。
   `(x)` は式でもパターンでもグループ化なので、末尾のカンマがないと、
   実行時エラーに出た値をそのままソースに書いても 1 要素のタプルにならない(sample.kel:186)。
   仕様 §4 は、`_item` だけからなる閉じた行をタプルの表記に戻して表示する対象を定めている(sample.kel:179-180)。
   対象は「型の表示、型エラーのメッセージ、実行時エラーに出る値、
   網羅性警告の反例の 4 つすべて」である。
   最初の 2 つは第9章 §9.3 が、実行時エラーに出る値は本節が、
   網羅性警告の反例は第10章 §10.12 が扱う。

   空の行を、型では `{}`、値では `()` と表示するという違いも、仕様の定めによる(sample.kel:181-182)。
   空の行は、どの位置でも `{}` と `()` のどちらで書いても同じものを指すので、
   仕様は型を Unit の表記に、値とパターンを 0 要素のタプルの表記にそろえた(sample.kel:183-185)。
   本節が表示する `()` は、値の位置にそのまま書ける表記である。 *)

let float_repr f =
  (* 非有限値の分岐は .0 の補完より前に置く。順序を誤ると inf.0 と表示してしまう *)
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
    (* 指数部の + と先頭の 0 を取り除く(仕様 §2、sample.kel:110)。
       1e+16 は 1e16 に、1e-05 は 1e-5 になる。取り除いても同じ値に読み戻せる *)
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

  (* ---- 値の表示(実行時エラーと対話的な実行の表示用) ----
     fn_name が偽なら、組み込み関数も <fn> と表示する(対話的な実行の表示) *)

let rec show ?(fn_name = true) v =
  let show v = show ~fn_name v in
  match v with
  | VBool b -> string_of_bool b
  | VInt32 n -> Int32.to_string n
  | VInt64 n -> Int64.to_string n
  | VFloat64 f -> float_repr f
  | VText s -> "\"" ^ String.escaped s ^ "\""
  | VRecord fs ->
      if fs = [] then "()"
      else if List.for_all (fun (l, _) -> l = Type.l_item) fs then
        (* 1 要素は (x,) と表示する。(x) は式でもパターンでもグループ化なので、タプルとして書けない(仕様 §4) *)
        "(" ^ String.concat ", " (List.map (fun (_, x) -> show x) fs) ^ (match fs with [ _ ] -> ",)" | _ -> ")")
      else "{" ^ String.concat ", " (List.map (fun (l, x) -> Type.display_of l ^ " = " ^ show x) fs) ^ "}"
  | VVariant (l, VRecord []) -> "#" ^ Type.display_of l
  | VVariant (l, p) -> "#" ^ Type.display_of l ^ "(" ^ show p ^ ")"
  | VData { d_ctor; d_fields; _ } ->
      if Array.length d_fields = 0 then Type.display_of d_ctor
      else Type.display_of d_ctor ^ "(" ^ String.concat ", " (Array.to_list (Array.map show d_fields)) ^ ")"
  | VClosure _ -> "<fn>"
  | VPrim p -> if fn_name then "<prim " ^ Type.display p.p_name ^ ">" else "<fn>"
  | VRef _ -> "<ref>"
  | VArray a -> "[" ^ String.concat ", " (Array.to_list (Array.map show a)) ^ "]"
  | VMutArray a -> "<mutable [" ^ String.concat ", " (Array.to_list (Array.map show a)) ^ "]>"
  | VDict _ -> "<dict>"
  | VDictAbs _ -> "<fn>"
