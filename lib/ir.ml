(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第17章 KIR の型

   KIR(Keleut Intermediate Representation)は、型検査と精緻化を済ませたプログラムを、
   評価器と別の処理系の両方が読める形式で書き出した中間言語である。
   仕様は親リポジトリの `doc/IRSpec.md` が定めていて、
   本章はその構造を OCaml の型で書いたものである。
   本章は型だけを持ち、木から KIR を作る処理も、KIR を出力する処理も持たない。

   第5章の精緻化木は、そのままでは別の処理系に渡せない。
   木は次の 3 つを木の外に置いているからである。

   | 木の外にあるもの | KIR での書き方 |
   |---|---|
   | ノードの oid、穴の番号、ハンドラの起動の番号 | 書かない。グローバルは、単位(§17.10)のキーと修飾名からなるシンボルで指定する |
   | ローカルの名前を引く表と、クロージャがキャプチャする環境の全体 | ローカルはスロットの番号で、キャプチャは関数ごとの並びで書く |
   | インスタンスの対象の型、メソッドの辞書の位置、組み込みの表 | 辞書の式と、表の項目として書く |

   KIR は木であり、ANF にはしない。
   子は、正準なテキスト(canonical。一意に決まる形。IRSpec 12 節)に現れる順に評価する。
   評価の順を入れ替える式(レコードの拡張など)も、テキストには評価の順に書く。
   そのため、本章の型のコンストラクタの引数も、評価の順に並べる。

   ## 名前の扱い

   本章の型は、名前を文字列のまま持つ。
   シンボル(`main/loop` のようなグローバルの名前)、ラベル、
   操作やメソッドの修飾しない名前のどれも `string` である。
   バイナリの文字列表と添字は、符号化のときに作る。
   表の順序はテキストから決まる規則で定まるので、型に添字を持たせる必要はない。 *)

(* ## 17.1 Rep

   Rep は、値の実行時の表現の種類である。
   束縛の型の先頭の型構成子が `Boolean`、`Int32`、`Int64`、`Float64`、`String` ならその Rep にし、
   それ以外(型変数を含む)は `RAny` にする。
   Rep は検証と最適化のためのもので、プログラムの意味を変えない。 *)
type rep = RBool | RI32 | RI64 | RF64 | RStr | RAny

(* ## 17.2 リテラル

   数値のリテラルは、書き出す段階で型に合わせて値を確定させる。
   `Float64` は IEEE 754 のビット列を `int64` に入れて持つ。
   ビット列で持つので、NaN のペイロードと負のゼロがそのまま残る。
   文字列は任意のバイト列である。

   範囲外の数値リテラルは値を持たず、`Lit_error` の式になる。
   評価したときに初めて実行時エラーにするためである。 *)
type lit = LBool of bool | LI32 of int32 | LI64 of int64 | LF64 of int64 | LStr of string

type lit_error_kind = Lit_range

(* ## 17.3 変数とキャプチャ

   関数の中の値は 3 か所から読む。
   スロット(引数とローカルの束縛)、キャプチャした値の並び、辞書の引数の並びである。
   クロージャを作るときのキャプチャの並びには、この 3 種類のどれでも書ける。
   コンストラクタに `V` を付けるのは、式のコンストラクタ `Local`、
   `Env` と名前が重ならないようにするためである。 *)
type var = VLocal of int | VEnv of int | VDParam of int

(* ## 17.4 辞書の式

   辞書の式は、型検査が解いた証拠(evidence。どのインスタンスの辞書を使うかを表す項)を平坦にしたものである。
   穴を経由する連鎖は書き出す段階でたどり終えるので、ここには残らない。

   | 形 | 意味 |
   |---|---|
   | `DInst (i, ps)` | ユーザが宣言したインスタンス `i` に、前提の辞書 `ps` を渡したもの |
   | `DVar v` | 辞書の引数(`VDParam`)か、キャプチャした辞書(`VEnv`) |
   | `DRecord fs` | 閉じたレコード型の構造的な `Eq`。ラベルとフィールドの辞書の組を、ラベル名のバイト列の昇順(同じラベルは外側が先)に並べる |
   | `DVariant fs` | 閉じたヴァリアント型の構造的な `Eq`。並びは `DRecord` と同じ |
   | `DBuiltin (c, t)` | 組み込みのインスタンス。クラスのシンボルと型構成子のシンボルで指定する |

   `DRecord` の辞書は、この並びの順に項目を比較する。
   結果が偽の項目があれば、そこで全体の結果を偽に決め、残りの項目の辞書を呼ばない。
   ユーザのインスタンスが実行時エラーになるか停止しない場合は、
   残りの項目を比較するかどうかで動作が変わるので、この順序と、
   途中で比較をやめることは観測できる。 *)
type dict =
  | DInst of string * dict list
  | DVar of var
  | DRecord of (string * dict) list
  | DVariant of (string * dict) list
  | DBuiltin of string * string

(* ## 17.5 パターン

   パターンは 6 種類ある。
   型注釈のパターンは実行時に何もしないので、書き出す段階で取り除く。

   レコードのパターンの末尾は 3 種類ある。
   `Closed` はタプルのパターン、`Open` は既定のレコードのパターン、`Rest p` は `...rest` である。
   照合では `Closed` と `Open` を区別しない。
   `Closed` のパターンに残りのフィールドがないことは、型検査が保証しているからである。

   コンストラクタのパターンは、照合するフィールドだけを、フィールドの位置の昇順に持つ。
   省略したフィールドは照合しない。 *)
type record_tail = Closed | Open | Rest of pat

and pat =
  | PWild
  | PBind of int
  | PLit of lit
  | PRecord of (string * pat) list * record_tail
  | PCtor of string * string * (int * pat) list
  | PVariant of string * pat

(* ## 17.6 操作節の分類

   N は返り値の型が `Never` の操作の節である。
   T は、本体の `resume` がすべて末尾 `resume` である節で、`resume` のない節も含む。
   G はそれ以外の節である。 *)
type clause_class = N | T | G

(* ## 17.7 式

   コンストラクタの引数は評価の順に並べる。
   `Rec_extend (l, v, r)` は値 `v` を先に、元のレコード `r` を後に評価し、
   `Rec_update (l, r, v)` は元のレコード `r` を先に、値 `v` を後に評価する。
   `Construct` の組 `(フィールドの位置, 式)` の並びはソースに書いた順で、格納先だけを位置で示す。

   `Call` の `tail` は末尾呼び出しの印である。
   `yield` は、呼び出し先が継続をキャプチャすることがあるかどうかの印である。
   `yield` が偽になるのは、呼び出し先の型のエフェクト行が閉じていて、
   ラベルがプレリュードの `Console`、組み込みの `Heap`、組み込みの `Blocking` だけのときである。
   `--no-prelude` で起点(コマンド行で渡したファイル)が宣言した `Console` は、
   プレリュードの `Console` として扱わない。

   `Method` はメソッドの値を作る。
   インスタンスを選ぶのは、その値を呼んだとき(引数を評価した後)である。
   `Opcall` は演算子として書いた呼び出しで、`Call (Method ...)` と同じ時点でインスタンスを選ぶ。
   違いは、`Opcall` が末尾呼び出しにならないことである。

   `Closure`、`Dictabs`、ハンドラの各部分は、関数表のシンボルとキャプチャの並びを持つ。
   `Letrec` の各項目の式は `Closure` か `Dictabs` に限る。 *)
type exp =
  | Lit of lit
  | Lit_error of lit_error_kind * string
  | Local of int
  | Env of int
  | Global of string
  | Construct of string * string * (int * exp) list
  | Variant of string * exp
  | Call of call
  | Method of string * string * dict * dict list
  | Opcall of string * string * dict * exp list
  | Not of exp
  | And of exp * exp
  | Or of exp * exp
  | Closure of string * var list
  | Dictabs of string * var list
  | Dictapp of exp * dict list
  | Let of int * exp * exp
  | Letpat of pat * exp * exp
  | Letrec of (int * exp) list * exp
  | Seq of exp list
  | Match of exp * clause list
  | Rec_empty
  | Rec_extend of string * exp * exp
  | Rec_select of string * exp
  | Rec_restrict of string * exp
  | Rec_update of string * exp * exp
  | Perform of string * string * exp list
  | Handle of handle
  | Resume of bool * exp
  | Hole

and call = { c_tail : bool; c_yield : bool; c_fn : exp; c_args : exp list }

(* `Match` の節は、パターン、ガード、本体を持つ。
   ガードは、パターンが一致した節だけで評価する。 *)
and clause = { cl_pat : pat; cl_guard : exp option; cl_body : exp }

(* ハンドラ式は、エフェクトのシンボルと、本体、操作節、`return` 節、`cancel` 節の関数を持つ。
   本体と節を別々の関数にするのは、バックエンドが継続をフレームの境界で切れるようにするためである。
   操作節の項目は、操作の修飾しない名前、分類、関数の順に並べる。 *)
and handle = {
  h_tail : bool;
  h_effect : string;
  h_body : part;
  h_ops : (string * clause_class * part) list;
  h_return : part option;
  h_cancel : part option;
}

and part = { p_fn : string; p_caps : var list }

(* ## 17.8 関数

   関数表の項目は、種類、引数とローカルのスロットの Rep、辞書の引数の個数、キャプチャの Rep、
   結果の Rep、`yield` の印、本体を持つ。
   スロットの番号は引数が先で、`f_params` の後に `f_locals` が続く。

   操作節の関数だけが `f_pats` と `f_guard` を持つ。
   `f_pats` は引数ごとのパターンで、i 番目のパターンを `Local i` と照合する。
   一致しなければ、その節を飛ばして次の節を試す。
   それ以外の種類の関数では、引数のパターンは本体の `Letpat` に書く。 *)
type fn_kind = Lambda | Opclause | Retclause | Cancelclause | Handlebody | Thunk | Dictabs_fn

type fn = {
  f_sym : string;
  f_kind : fn_kind;
  f_yield : bool;
  f_params : rep list;
  f_locals : rep list;
  f_dicts : int;
  f_caps : rep list;
  f_result : rep;
  f_pats : pat list;
  f_guard : exp option;
  f_body : exp;
}

(* ## 17.9 表

   型は、コンストラクタの並びを持ち、各コンストラクタは名前とフィールドの個数を持つ。
   組み込みの型はコンストラクタを持たない。

   エフェクトの操作は、引数の個数、返り値の型が `Never` かどうか、
   ランタイムが処理するかどうかを持つ。
   ランタイムが処理する操作は、プレリュードの `Console`(シンボル `prelude/Console`)の `write` だけである。
   `--no-prelude` で起点が宣言した `Console` の操作はユーザが処理する。

   クラスのメソッドは、名前と、クラスの辞書を除いたメソッド自身の辞書の個数を持つ。
   インスタンスは、クラス、対象の型の先頭の型構成子、前提の個数、メソッドの実装の並びを持つ。
   実装の項目は、メソッドの名前、メソッド自身の辞書の個数、実装の関数のシンボルである。
   実装の関数は、前提の辞書の後にメソッド自身の辞書を続けて受け取る。 *)
type ctor = { ct_name : string; ct_arity : int }

type ty = { t_sym : string; t_ctors : ctor list }

type op = { o_name : string; o_arity : int; o_never : bool; o_runtime : bool }

type eff = { e_sym : string; e_ops : op list }

type cls = { c_sym : string; c_methods : (string * int) list }

type instance = {
  i_sym : string;
  i_class : string;
  i_head : string;
  i_premises : int;
  i_methods : (string * int * string) list;
}

(* グローバルは 5 種類ある。

   | 種類 | 値 |
   |---|---|
   | `GFn f` | 関数 `f` のクロージャ。キャプチャはない |
   | `GValue r` | 初期化手順が評価して格納する値。Rep は `r` |
   | `GDictabs f` | 辞書を受け取る関数 `f`。辞書を渡すたびに `f` の本体を評価する |
   | `GExtern` | プリミティブか C の関数。辞書を受け取るものは、受け取った辞書を捨てる |
   | `GBuiltin` | 組み込みの値(付録 A) | *)
type abi = Prim | C

type global_kind =
  | GFn of string
  | GValue of rep
  | GDictabs of string
  | GExtern of { abi : abi; impl : string; dicts : int }
  | GBuiltin

type global = { g_sym : string; g_kind : global_kind }

(* ## 17.10 単位と初期化

   単位は、プログラムを構成するコンパイル単位である(IRSpec 2 節)。
   単位は、キー、元のファイルを示す表示用のパスの並び、初期化手順の並びを持つ。
   `Def_pattern (f, gs, p)` は、`thunk` の関数 `f` の値をパターン `p` と照合し、
   グローバルの並び `gs` に格納する。
   `p` の `PBind k` は、スロットではなく、`gs` の k 番目を指す。 *)
type step =
  | Def_value of string * string
  | Def_pattern of string * string list * pat
  | Def_fns of string list
  | Def_dictabs of string
  | Def_instance of string
  | Run_exp of string

type unit_ = { u_key : string; u_paths : string list; u_init : step list }

(* ## 17.11 プログラム

   1 つのプログラムは、プレリュードと組み込みを含むすべての単位を持ち、それだけで完結する。
   各表の順序は IRSpec 12 節の規則に従う。 *)
type program = {
  version : int * int;
  units : unit_ list;
  types : ty list;
  effects : eff list;
  classes : cls list;
  instances : instance list;
  globals : global list;
  functions : fn list;
}

(* バージョンは 1.0 である。
   ライタ(writer。Keleut のソースから KIR を作る処理系)はこのバージョンを書く。
   リーダ(reader。KIR を読む処理系)は、
   メジャーバージョンが同じならマイナーバージョンによらず受理し、
   メジャーバージョンが違えば拒否する。
   マイナーバージョンで追加できるのは、スキップできるセクションと、
   必須機能ビットを立てたときだけ使える新しい命令だけだからである。
   未知の必須機能ビットは、ヘッダの検査で別に拒否する。 *)
let version = (1, 0)

(* ## 17.12 テキストでの名前

   Rep、関数の種類、操作節の分類などをテキストに書くときの名前を、ここ 1 か所で定義する。
   第19章(ir_text.ml)の正準なテキストと、第21章(ir_check.ml)の診断がこの名前を使う。 *)
let rep_name = function RBool -> "bool" | RI32 -> "i32" | RI64 -> "i64" | RF64 -> "f64" | RStr -> "str" | RAny -> "any"

let fn_kind_name = function
  | Lambda -> "lambda"
  | Opclause -> "opclause"
  | Retclause -> "retclause"
  | Cancelclause -> "cancelclause"
  | Handlebody -> "handlebody"
  | Thunk -> "thunk"
  | Dictabs_fn -> "dictabs"

let clause_class_name = function N -> "N" | T -> "T" | G -> "G"

let abi_name = function Prim -> "prim" | C -> "C"

let lit_error_kind_name = function Lit_range -> "lit_range"

(* シンボルが属する単位のキーは、シンボルの最後の `/` より前の部分である。
   修飾名と、持ち上げた関数(ラムダリフティングで取り出した関数)の接尾辞は `/` を含まないので、
   この規則でキーが決まる。 *)
let unit_of_symbol s = match String.rindex_opt s '/' with Some i -> String.sub s 0 i | None -> s
