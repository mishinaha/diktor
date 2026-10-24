(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第17章 KIR の型

   KIR(Keleut Intermediate Representation)は、型検査と精緻化を済ませたプログラムを、
   評価器と別の処理系の両方が読める形に書き出した中間言語である。
   規範は親リポジトリの `doc/IRSpec.md` にあり、本章はその型を OCaml で写したものである。
   本章は型だけを持ち、木から KIR を作る処理も印字も持たない。

   第5章の精緻化木は、そのままでは別の処理系に渡せない。
   木は次の 3 つを木の外に置いているからである。

   | 木の外にあるもの | KIR での置き場所 |
   |---|---|
   | ノードの oid、穴の番号、ハンドラの起動の番号 | 書かない。大域は単位の鍵と修飾名からなる記号で名指す |
   | 局所の名前を引く表と、クロージャが捕まえる環境の全体 | 局所はスロットの番号、捕獲は関数ごとの列 |
   | インスタンスの頭、メソッドの辞書の位置、組み込みの表 | 辞書の式と、表の項目として書く |

   KIR は木であり、ANF にはしない。
   子は、正準のテキスト(IRSpec 12 節)に現れる順に評価する。
   順を変える式(レコードの拡張など)は、テキストに書く順そのものを評価の順に揃えてある。
   そのため、本章の型の構成子の引数も、評価の順に並べる。

   ## 名前の扱い

   本章の型は、名前を文字列のまま持つ。
   記号(`main/loop` のような大域の名前)、ラベル、操作やメソッドの短い名前のどれも `string` である。
   バイナリの文字列の表と添字は、符号化のときに作る。
   表の並びはテキストから決まる規則で定めるので、型に添字を持たせる必要は無い。 *)

(* ## 17.1 Rep

   Rep は、値の機械の上の表現の種類である。
   束縛の型の頭が `Boolean`、`Int32`、`Int64`、`Float64`、`String` ならその Rep にし、
   ほか(型変数を含む)は `RAny` にする。
   Rep は検証と最適化のためのもので、プログラムの意味を変えない。 *)
type rep = RBool | RI32 | RI64 | RF64 | RStr | RAny

(* ## 17.2 リテラル

   数値のリテラルは、書き出す段で型に合わせて値を確定させる。
   `Float64` は IEEE 754 のビット列を `int64` に入れて持つ。
   ビット列で持つので、NaN の積載と負のゼロがそのまま残る。
   文字列は任意のバイト列である。

   範囲外の数値リテラルは値を持たず、`Lit_error` の式になる。
   評価したときに初めて実行時エラーにするためである。 *)
type lit = LBool of bool | LI32 of int32 | LI64 of int64 | LF64 of int64 | LStr of string

type lit_error_kind = Lit_range

(* ## 17.3 変数と捕獲

   関数の中の値は 3 か所から読む。
   スロット(引数と局所の束縛)、捕獲した値の列、辞書の引数の列である。
   クロージャを作るときの捕獲の列には、この 3 種のどれでも書ける。
   構成子に `V` を付けるのは、式の `Local` と `Env` と名前を分けるためである。 *)
type var = VLocal of int | VEnv of int | VDParam of int

(* ## 17.4 辞書の式

   辞書の式は、型検査が解いた証拠を平坦にしたものである。
   穴を経由する鎖は書き出す段でたどり終え、ここには残らない。

   | 形 | 意味 |
   |---|---|
   | `DInst (i, ps)` | 利用者が宣言したインスタンス `i` に、前提の辞書 `ps` を渡したもの |
   | `DVar v` | 辞書の引数(`VDParam`)か、捕獲した辞書(`VEnv`) |
   | `DRecord fs` | 閉じたレコード型の構造的な `Eq`。ラベルの綴りの昇順(同じラベルは外側が先)のラベルと、フィールドの辞書 |
   | `DVariant fs` | 閉じたヴァリアント型の構造的な `Eq`。並びは `DRecord` と同じ |
   | `DBuiltin (c, t)` | 組み込みのインスタンス。クラスと型構成子の記号で名指す |

   `DRecord` の比較は、並びの順に項目を比べる。
   偽の項目に出会えば、そこで結果を偽とし、残りの項目の辞書を呼ばない。
   利用者のインスタンスが実行時エラーになるか停止しないとき、この止まり方は観測できる。 *)
type dict =
  | DInst of string * dict list
  | DVar of var
  | DRecord of (string * dict) list
  | DVariant of (string * dict) list
  | DBuiltin of string * string

(* ## 17.5 パターン

   パターンは 6 種である。
   型注釈のパターンは実行時に何もしないので、書き出す段で外す。

   レコードのパターンの尾部は 3 つの状態を持つ。
   `Closed` はタプルのパターン、`Open` は既定のレコードのパターン、`Rest p` は `...rest` である。
   照合では `Closed` と `Open` を区別しない。
   残りのフィールドが無いことは型検査が保証しているからである。

   コンストラクタのパターンは、照合するフィールドだけを、フィールドの位置の昇順に持つ。
   省略したフィールドには触れない。 *)
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
   T は、本体の `resume` がすべて末尾の `resume` である節で、`resume` の無い節も含む。
   G はそれ以外の節である。 *)
type clause_class = N | T | G

(* ## 17.7 式

   構成子の引数は評価の順に並べる。
   `Rec_extend (l, v, r)` は値 `v` を先に、基底 `r` を後に評価し、
   `Rec_update (l, r, v)` は基底 `r` を先に、値 `v` を後に評価する。
   `Construct` の組 `(フィールドの位置, 式)` の列はソースに書いた順で、格納先だけを位置で示す。

   `Call` の `tail` は末尾呼び出しの印、
   `yield` は呼び出し先が継続の取り出しを起こしうるかの印である。
   `yield` が偽になるのは、呼び出し先の型のエフェクト行が閉じていて、
   ラベルがプレリュードの `Console`、組み込みの `Heap`、組み込みの `Blocking` だけのときである。
   `--no-prelude` で起点が宣言した `Console` は数えない。

   `Method` はメソッドの値を作る。
   インスタンスを選ぶのは、その値を呼んだとき(引数を評価した後)である。
   `Opcall` は演算子の形の呼び出しで、`Call (Method ...)` と同じ時点でインスタンスを選ぶ。
   違いは、`Opcall` が末尾呼び出しにならないことである。

   `Closure`、`Dictabs`、ハンドラの各部分は、関数の表の記号と捕獲の列を持つ。
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

(* ハンドラ式は、エフェクトの記号と、本体、操作節、`return` 節、`cancel` 節の関数を持つ。
   本体と節を別々の関数にするのは、後段が継続をフレームの境目で切れるようにするためである。
   操作節の項目は、操作の短い名前、分類、関数の順に並べる。 *)
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

   関数の表の項目は、種類、引数と局所のスロットの Rep、辞書の引数の数、捕獲の Rep、
   結果の Rep、`yield` の印、本体を持つ。
   スロットの番号は引数が先で、`f_params` の後に `f_locals` が続く。

   操作節の関数だけが `f_pats` と `f_guard` を持つ。
   `f_pats` は引数ごとのパターンで、i 番目のパターンを `Local i` と照合する。
   一致しなければ、その節を飛ばして次の節を試す。
   ほかの種類の関数では、引数のパターンは本体の `Letpat` に書く。 *)
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

   型は、コンストラクタの名前とフィールドの数の列を持つ。
   組み込みの型はコンストラクタを持たない。

   エフェクトの操作は、引数の数、返り値の型が `Never` かどうか、実行時が処理するかどうかを持つ。
   実行時が処理する操作は、プレリュードの `Console`(記号 `prelude/Console`)の `write` だけである。
   `--no-prelude` で起点が宣言した `Console` の操作は利用者が処理する。

   クラスのメソッドは、名前と、クラスの辞書を除いたメソッド自身の辞書の数を持つ。
   インスタンスは、クラス、頭の型構成子、前提の数、メソッドの実装の列を持つ。
   実装の項目は、メソッドの名前、メソッド自身の辞書の数、実装の関数の記号である。
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

(* 大域の種類は 5 つである。

   | 種類 | 値 |
   |---|---|
   | `GFn f` | 関数 `f` のクロージャ。捕獲は無い |
   | `GValue r` | 初期化の手順が評価して置く値。Rep は `r` |
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

   単位は、鍵、元のファイルの表示の綴りの列、初期化の手順の列を持つ。
   `Def_pattern (f, gs, p)` は、`thunk` の関数 `f` の値をパターン `p` と照合し、
   大域の列 `gs` に置く。
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
   各表の並びは IRSpec 12 節の規則に従う。 *)
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

(* 版は 0.2 である。
   1.0 より前は、読み手は書き手と同じ版だけを受け付ける。 *)
let version = (0, 2)

(* ## 17.12 テキストの綴り

   テキストとバイナリに共通する綴りを、ここに 1 か所だけ置く。 *)
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

(* 記号の単位の鍵は、記号の最後の `/` より前の部分である。
   修飾名と、持ち上げた関数の接尾辞は `/` を含まないので、この規則で鍵が決まる。 *)
let unit_of_symbol s = match String.rindex_opt s '/' with Some i -> String.sub s 0 i | None -> s
