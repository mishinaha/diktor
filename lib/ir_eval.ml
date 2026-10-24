(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第22章 KIR の評価器

   本章は、第17章の `Ir.program` を評価する。
   第14章の評価器が精緻化木を歩くのに対し、本章は KIR の木を歩く。
   意味の規範は親リポジトリの `doc/IRSpec.md` で、
   本章はその 5 節(評価順序)、6 節(関数と捕獲)、7 節(辞書)、8 節(パターン)、
   9 節(エフェクト)、10 節(初期化)、11 節(論理的な深さ)を、そのまま OCaml に写したものである。

   本章の評価器は、第14章の評価器と同じ出力と同じ終了状態を出すことを目標にする。
   KIR を書き出して読み戻し、本章で評価した結果が第14章の結果と一致すれば、
   書き出し、符号化、読み込みのどこにも意味の取りこぼしが無いことの証拠になる。
   そのため、実行時エラーの文面(IRSpec 付録 B)、標準出力の書き方、例外の種類を、
   第14章とそろえる。

   ## 第14章と同じにするもの、違えるもの

   | 項目 | 第14章 | 本章 |
   |---|---|---|
   | 値 | 第12章の `Value.t` | 本章の `v`(22.1 節) |
   | 実行時エラー | `Value.Runtime_error` | 同じ例外 |
   | 標準出力 | `Builtin.with_runtime` が `Console.write` を `sink` へ送る | 同じ |
   | プリミティブ | 第13章の表 | 同じ表を、値を写して呼ぶ |
   | 再帰の限度 | OCaml のスタック | 論理的な深さ(IRSpec 11 節) |
   | ハンドラ式 | `Effect.Deep` に写す | 同じ写し方で、深さの規則を足す(22.14 節) |

   値を第12章と別にするのは、第12章のクロージャが精緻化木の本体と環境を持つからである。
   KIR のクロージャは、関数の表の項目と捕獲の列の組である。
   第12章の `VPrim` に包むと、診断の印字が `<fn>` でなく `<prim …>` になり、
   引数をレコードに詰め直す手間も呼び出しのたびに掛かる。
   プリミティブは数と文字列しか受け取らないので、呼ぶときだけ値を写せば足りる。

   ## 2 つの段

   評価は 2 段で行う。
   まず KIR の木を、記号を引き終えた木(22.2 節の `cexp`)に写す。
   大域の参照は大域の欄そのものを指し、クロージャは関数の表の項目そのものを指す。
   次に、写した木を歩いて評価する。
   評価のたびに記号でハッシュ表を引くと、
   大域を読むたびと演算子を呼ぶたびに文字列のハッシュが掛かる。
   写す段で 1 回だけ引けば、評価は配列と欄を読むだけになる。

   ## ハンドラ式の扱い

   ハンドラ式は、第14章 §14.9 と同じく、1 つの `Effect.Deep.match_with` に写す。
   節の選び方、巻き戻しの順序、`cancel` 節の打ち切り、`resume` の検査の順序は、
   第14章の写し方をそのまま使う。
   そうすれば、第14章が固定している振る舞いと同じ結果になる。
   第14章に無いのは、深さの数え方(IRSpec 11 節)である。
   深さは OCaml のスタックからは得られないので、本章はフレームと起動に明示の数を持たせる(22.6 節)。

   ## API

   `run ~max_depth ~sink program` は、`program` の初期化の手順を順に実行する。
   正常に終われば `()` を返す。
   誤りは例外で返し、終了状態への写しは第16章の受け皿に任せる。

   | 例外 | 意味 | 受け皿の終了状態 |
   |---|---|---|
   | `Value.Runtime_error msg` | 実行時エラー(論理的な深さの限度を含む) | 3 |
   | `Sys_error msg` | 標準出力に書けない | 74 |
   | `Aux.Panic msg` | 処理系の誤り(KIR が型の付かない形をしている) | 3 |

   第14章の `Interp.run_units` と同じ例外を同じ意味で使うので、
   第16章は評価器を差し替えるだけで、診断の文面と終了状態をそのまま保てる。
   終了状態を返す関数にしないのは、文面の印字と flush の順序を受け皿の 1 か所に保つためである。 *)
open Aux
module Type = Syntax.Type

(* ## 22.1 値

   値の種類は次のとおりである。

   | 構成子 | 値 |
   |---|---|
   | `VBool`、`VI32`、`VI64`、`VF64`、`VStr` | Rep が `any` でない 5 種の値 |
   | `VRec` | レコード。先頭が最も外側のフィールドで、同じラベルが重なってよい。Unit は空のレコード |
   | `VVariant` | ヴァリアント。ラベルと積載値 1 個 |
   | `VData` | 名目的な型の値。コンストラクタの名前とフィールドの配列 |
   | `VClo` | クロージャ。種類 `lambda` の関数と捕獲の配列 |
   | `VDabs` | 辞書の抽象。種類 `dictabs` の関数と捕獲の配列 |
   | `VMeth` | メソッドの値。インスタンスはまだ選んでいない(IRSpec 5.4 節) |
   | `VBuiltin` | 組み込みの値(IRSpec 付録 A.4) |
   | `VExtern` | `extern` の大域。プリミティブか C の関数 |
   | `VRef`、`VArray`、`VMutArray` | 組み込みの参照と配列 |
   | `VDict` | 捕獲に置いた辞書 |

   辞書は値と別の型 `dv` で表し、捕獲に置くときだけ `VDict` で包む。
   辞書の引数(`dparam`)は、フレームの辞書の配列から読む。

   捕獲の配列は、作った後に書き換えることがある。
   `letrec` は群の値をすべて作ってから捕獲を埋めるからである(IRSpec 5.1 節)。 *)
type v =
  | VBool of bool
  | VI32 of int32
  | VI64 of int64
  | VF64 of float
  | VStr of string
  | VRec of (string * v) list
  | VVariant of string * v
  | VData of string * v array
  | VClo of rfn * v array
  | VDabs of rfn * v array
  | VMeth of meth
  | VBuiltin of builtin
  | VExtern of ext
  | VRef of v ref
  | VArray of v array
  | VMutArray of v array
  | VDict of dv

(* 関数の表の項目。スロットの数を前もって数え、写した本体を持つ。
   操作節の関数は、写したガードも持つ。
   本体とガードは、表のすべての項目を作ってから写して書き込む。
   本体は別の関数の項目を指すので、項目が先にそろっていなければならない *)
and rfn = { fn : Ir.fn; nparams : int; nslots : int; mutable body : cexp; mutable guard : cexp option }

(* メソッドの値は、クラス、メソッドの名前、クラスの位置の辞書、メソッド自身の辞書を持つ *)
and meth = { m_cls : string; m_name : string; m_dict : dv; m_own : dv list }

(* `extern` の大域は、表示名、実装名、実装を持つ。
   実装が無いものは呼んだときに実行時エラーにする(IRSpec 付録 B の 17 番と 18 番) *)
and ext = { x_display : string; x_impl : string; x_fn : (Value.t -> Value.t) option }

(* 辞書の値。`DInst` は初期化の印を持つインスタンスの表の項目を指し、
   `DBuiltin` は組み込みのインスタンスのメソッドの実装の表を指す *)
and dv = DInst of inst * dv list | DRecord of (string * dv) list | DVariant of (string * dv) list | DBuiltin of bi

(* インスタンスの表の項目。`i_impls` はメソッドの名前と実装の関数の組で、
   `i_values` は、辞書の引数の数が 0 の実装を `def_instance` が評価した値である *)
and inst = { ins : Ir.instance; i_impls : (string * rfn) list; mutable i_ready : bool; mutable i_values : (string * v) list }

(* 組み込みのインスタンス。メソッドの名前から実装への表を持つ *)
and bi = { bi_methods : (string * (Value.t -> Value.t)) list }

(* 組み込みの値。名前は付録 A.4 の記号である *)
and builtin =
  | BRef_new
  | BRef_get
  | BRef_set
  | BArray_length
  | BArray_get
  | BArray_each
  | BMut_new
  | BMut_length
  | BMut_get
  | BMut_set
  | BMut_freeze
  | BPinned

(* ## 22.2 写した木

   `cexp` は KIR の式の木と同じ形で、記号を引き終えたものである。

   | KIR の式 | 写した先で記号の代わりに持つもの |
   |---|---|
   | `global` | 大域の欄 `gcell` |
   | `construct` | コンストラクタの名前とフィールドの数 |
   | `closure`、`dictabs` | 関数の表の項目 `rfn` |
   | 辞書の `dinst`、`dbuiltin` | インスタンスの表の項目と、組み込みの実装の表 |
   | `perform` | 実行時が処理する操作かどうかの区別と、診断に書く操作の名前 |
   | `handle` | 本体と各節の関数の表の項目 |
   | 引数の列 | 配列 |

   大域の欄は、初期化済みの印を `g_val` が `Some` であることで表す(IRSpec 10.3 節)。
   欄は、初期化の前に読んだときの診断に書く名前も持つ。 *)
and gcell = { g_display : string; mutable g_val : v option }

and cexp =
  | CLit of v
  | CLit_error of string
  | CLocal of int
  | CEnv of int
  | CGlobal of gcell
  | CConstruct of string * int * (int * cexp) list
  | CVariant of string * cexp
  | CCall of bool * cexp * cexp array
  | CMethod of string * string * cdict * cdict list
  | COpcall of string * string * cdict * cexp array
  | CNot of cexp
  | CAnd of cexp * cexp
  | COr of cexp * cexp
  | CClosure of rfn * Ir.var array
  | CDictabs of rfn * Ir.var array
  | CDictapp of cexp * cdict array
  | CLet of int * cexp * cexp
  | CLetpat of Ir.pat * cexp * cexp
  | CLetrec of (int * bool * rfn * Ir.var array) list * cexp
  | CSeq of cexp list
  | CMatch of cexp * cclause list
  | CRec_empty
  | CRec_extend of string * cexp * cexp
  | CRec_select of string * cexp
  | CRec_restrict of string * cexp
  | CRec_update of string * cexp * cexp
  | CPerform_runtime of cexp array
  | CPerform_user of string * string * string * cexp array
  | CHandle of chandle
  | CResume of bool * cexp
  | CHole

and cclause = { cc_pat : Ir.pat; cc_guard : cexp option; cc_body : cexp }

(* ハンドラ式。各部分は、関数の表の項目と、ハンドラ式を評価したフレームから読む捕獲の列である。
   操作節の項目は、操作の短い名前、分類、部分の順に並べる *)
and chandle = {
  ch_eff : string;
  ch_body : rfn * Ir.var array;
  ch_ops : (string * Ir.clause_class * rfn * Ir.var array) list;
  ch_ret : (rfn * Ir.var array) option;
  ch_cancel : (rfn * Ir.var array) option;
}

and cdict = CDInst of inst * cdict list | CDParam of int | CDEnv of int | CDRecord of (string * cdict) list | CDVariant of (string * cdict) list | CDBuiltin of bi

let unit_v = VRec []

(* ## 22.3 診断の印字

   実行時エラーの文面に埋める値は、第12章の `show` と同じ綴りで書く(IRSpec 付録 B)。
   数の綴りと `Float64` の表示器は第12章のものをそのまま使う。
   関数の値は、第14章で `VClosure` か `VDictAbs` になるものを `<fn>` と書く。
   第14章で `VPrim` になるもの(組み込みの値、`extern`、メソッドの値)は `<prim 名前>` と書く。
   メソッドの値の名前は、第14章と同じく `クラス.メソッド` である。 *)

(* 記号から単位の鍵と、再束縛の印 `#n` を除いた修飾名。
   診断に書く大域の名前、`extern` の表示名、クラスと型の名前は、どれもこの規則で作る *)
let display_of_symbol s =
  let s = match String.rindex_opt s '/' with Some i -> String.sub s (i + 1) (String.length s - i - 1) | None -> s in
  match String.rindex_opt s '#' with
  | Some i when i + 1 < String.length s && String.for_all (fun c -> c >= '0' && c <= '9') (String.sub s (i + 1) (String.length s - i - 1)) ->
      String.sub s 0 i
  | _ -> s

let builtin_name = function
  | BRef_new -> "Ref.new"
  | BRef_get -> "Ref.get"
  | BRef_set -> "Ref.set"
  | BArray_length -> "Array.length"
  | BArray_get -> "Array.get"
  | BArray_each -> "Array.each"
  | BMut_new -> "MutableArray.new"
  | BMut_length -> "MutableArray.length"
  | BMut_get -> "MutableArray.get"
  | BMut_set -> "MutableArray.set"
  | BMut_freeze -> "MutableArray.freeze"
  | BPinned -> "pinned"

let all_builtins = [ BRef_new; BRef_get; BRef_set; BArray_length; BArray_get; BArray_each; BMut_new; BMut_length; BMut_get; BMut_set; BMut_freeze; BPinned ]

let rec show v =
  match v with
  | VBool b -> string_of_bool b
  | VI32 n -> Int32.to_string n
  | VI64 n -> Int64.to_string n
  | VF64 f -> Value.float_repr f
  | VStr s -> "\"" ^ String.escaped s ^ "\""
  | VRec fs ->
      if fs = [] then "()"
      else if List.for_all (fun (l, _) -> l = "_item") fs then
        "(" ^ String.concat ", " (List.map (fun (_, x) -> show x) fs) ^ (match fs with [ _ ] -> ",)" | _ -> ")")
      else "{" ^ String.concat ", " (List.map (fun (l, x) -> Type.display l ^ " = " ^ show x) fs) ^ "}"
  | VVariant (l, VRec []) -> "#" ^ Type.display l
  | VVariant (l, p) -> "#" ^ Type.display l ^ "(" ^ show p ^ ")"
  | VData (c, fs) ->
      if Array.length fs = 0 then Type.display c else Type.display c ^ "(" ^ String.concat ", " (Array.to_list (Array.map show fs)) ^ ")"
  | VClo _ | VDabs _ -> "<fn>"
  | VMeth m -> "<prim " ^ display_of_symbol m.m_cls ^ "." ^ m.m_name ^ ">"
  | VBuiltin b -> "<prim " ^ builtin_name b ^ ">"
  | VExtern x -> "<prim " ^ x.x_display ^ ">"
  | VRef _ -> "<ref>"
  | VArray a -> "[" ^ String.concat ", " (Array.to_list (Array.map show a)) ^ "]"
  | VMutArray a -> "<mutable [" ^ String.concat ", " (Array.to_list (Array.map show a)) ^ "]>"
  | VDict _ -> "<dict>"

let runtime_error = Value.runtime_error

let as_bool = function VBool b -> b | v -> bug ("Boolean ではない値: " ^ show v)

(* ## 22.4 レコード

   レコードの操作は第12章 §12.6 と同じ規則である。
   先頭が最も外側のフィールドで、選択、制限、更新はどれも最も外側の同名のフィールドに効く。
   更新はフィールドの位置を変えない。 *)
let record_fields = function VRec fs -> fs | v -> bug ("レコードではない値: " ^ show v)

let rec assoc_first l = function [] -> None | (l', x) :: rest -> if String.equal l l' then Some x else assoc_first l rest

let record_select r l = match assoc_first l (record_fields r) with Some x -> x | None -> bug ("ラベルがありません: " ^ l)

(* 最も外側の `l` を取り出し、値と残りを返す。ラベルが無ければ `None` *)
let record_take fs l =
  let rec go acc = function
    | [] -> None
    | ((l', x) as f) :: rest -> if String.equal l l' then Some (x, List.rev_append acc rest) else go (f :: acc) rest
  in
  go [] fs

let record_restrict r l = match record_take (record_fields r) l with Some (_, rest) -> VRec rest | None -> bug ("ラベルがありません: " ^ l)

let record_update r l x =
  let rec go = function [] -> bug ("ラベルがありません: " ^ l) | (l', y) :: rest -> if String.equal l l' then (l', x) :: rest else (l', y) :: go rest in
  VRec (go (record_fields r))

(* ## 22.5 プリミティブの呼び出し

   `extern` と組み込みのインスタンスのメソッドは、第13章の表の実装を使う。
   表の実装は第12章の値を受け取るので、呼ぶときに引数を写し、結果を写し戻す。
   引数と結果は Rep が `any` でない値か Unit に限られ、ほかの値が来たら処理系の誤りである。 *)
let to_value = function
  | VBool b -> Value.VBool b
  | VI32 n -> Value.VInt32 n
  | VI64 n -> Value.VInt64 n
  | VF64 f -> Value.VFloat64 f
  | VStr s -> Value.VText s
  | VRec [] -> Value.unit
  | v -> bug ("プリミティブに渡せない値: " ^ show v)

let of_value = function
  | Value.VBool b -> VBool b
  | Value.VInt32 n -> VI32 n
  | Value.VInt64 n -> VI64 n
  | Value.VFloat64 f -> VF64 f
  | Value.VText s -> VStr s
  | Value.VRecord [] -> unit_v
  | v -> bug ("プリミティブが返した値を写せません: " ^ Value.show v)

let call_prim f args = of_value (f (Value.VRecord (Array.to_list (Array.map (fun a -> (Type.l_item, to_value a)) args))))

(* ## 22.6 論理的な深さ

   深さは IRSpec 11 節の規則で数える。
   末尾でない呼び出しは呼ばれた側を 1 つ深くし、末尾の呼び出しは呼び出し元の深さを引き継ぐ。
   ハンドラ式と操作節の深さの規則は、22.14 節で扱う。

   限度の検査は、深さが増える境目に入る前に行う。
   新しい深さが限度を超えたら、実行時エラーにする。
   その誤りが伝播している間は、限度を予備 `R = max(1024, L / 64)` だけ広げる。
   予備は、巻き戻しの途中で走る `cancel` 節のためのものである。
   予備の中でさらに限度を超えると、同じ文面の実行時エラーになり、
   それを起こした `cancel` 節の打ち切り(22.14 節)が記録する。
   限度の誤りを捕まえるのは、この打ち切りだけである。
   `cancel` 節は、走る前の限度を覚えておき、節を出るときにその値へ戻す。
   外で伝播している誤りが限度の誤りなら、覚えた値はすでに予備の分だけ広く、
   入れ子の `cancel` 節も予備の中で走る。
   外の誤りがほかの誤りなら、節の中で限度を超えて打ち切られた後、限度は `L` に戻る。
   限度の誤りが最上位に届いたときは、プログラムが終わる。

   ### 錨からの差

   継続を深さ `c` で再開すると、継続の中の文脈の深さと、
   継続の中で始まったハンドラの起動の深さが、どれも `c − h` だけずれる(IRSpec 11.4 節)。
   `h` は、その継続を取り出したハンドラの起動の深さである。
   中断した計算は OCaml のファイバーの中にあり、
   その中のフレームを外からたどって書き換えることはできない。
   そこで、深さを絶対の値でなく、錨(`anchor`)からの差で持つ。
   錨は、プログラムの根の錨か、ハンドラの起動ごとに 1 つ作る錨である。
   根の錨の深さは 0 である。
   起動の錨は、親の錨と差を持ち、その深さは親の錨の深さに差を足したもので、起動の深さ `h` にあたる。
   フレームも錨と差を持ち、フレームの深さは錨の深さに差を足したものである。

   継続を再開するときは、その継続を取り出した起動の錨の親と差を、
   `resume` を評価したフレームの錨と差に付け替える。
   継続の中のフレームとハンドラの起動は、どれもこの起動の錨を経由して深さが決まる(22.14 節)。
   そのため、付け替え 1 回で、ずらすべきものがすべてずれる。

   錨の深さは、親をたどって差を足せば求まる。
   毎回たどると、ハンドラの入れ子が深いほど呼び出しが遅くなるので、求めた値を錨に覚えておく。
   付け替えのたびに世代の番号を進め、覚えた値は、覚えたときと同じ世代の間だけ使う。

   ### OCaml のスタック

   末尾の呼び出しは OCaml の末尾呼び出しに保つ(第14章の冒頭の規約 1 と同じ)。
   そのため、末尾呼び出しのループは深さも OCaml のスタックも増やさない。
   末尾でない呼び出しは OCaml のスタックも使い、
   1 段あたりの量は、呼ばれた関数の中で次の呼び出しを囲む式の入れ子が深いほど増える。
   1 本のスタックの上で再帰すると、入れ子の深いプログラムでは、
   論理的な深さが限度に届く前に OCaml のスタックの上限に届く。

   OCaml 5 のスタックの上限は、ファイバーのスタックごとに掛かる。
   そこで、末尾でない呼び出しの呼ばれた側の深さが 4096 の倍数になるたびに、
   その呼び出しを新しいファイバーの中で走らせる。
   このファイバーのハンドラは、値も例外もエフェクトもそのまま外へ通すので、意味には効かない。
   1 本のスタックが持つのは、末尾でない呼び出しの高々 4096 段の分である。
   各段の中の式の入れ子は、KIR のノードの深さの上限(IRSpec 13.9 節)の下にある。
   こうして、スタックの上限は 1 本のスタックの量にだけ掛かり、段の数には掛からなくなる。
   それでも、限度に届く前に評価が止まる場合が 3 つ残る。
   1 つ目は、4096 段の分のスタックが 1 本のスタックの上限を超える場合である。
   OCAMLRUNPARAM の `l` で上限を絞ったときや、各段の中の入れ子が極端に深いときに起こり、
   スタックオーバーフローの実行時エラーになる。
   これに届くかどうかは、段の数でなく、4096 段の中の入れ子の深さで決まる。
   2 つ目は、生きている継続が長い鎖をなす場合である。
   OCaml 5 の GC は継続の鎖を C のスタックの上で再帰してたどるので、
   システムのスタックが尽きて SIGSEGV で落ちることがある。
   落ちるかどうかは GC の時機とシステムのスタックの大きさで決まり、木の評価器にも同じ弱さがある。
   3 つ目は、機械のメモリが尽きる場合である。
   全体で使う領域は、段の数と各段の入れ子の深さに比例して増える。

   間隔を短くすると、1 本のスタックの量は減るが、ファイバーの数が増える。
   `perform` から宛先のハンドラまでの間にあるファイバーは、どれもエフェクトを外へ送り直すので、
   深い再帰の底で操作を繰り返し起こすプログラムは、ファイバーの数に比例して遅くなる。
   4096 は、OCAMLRUNPARAM でスタックの上限を 1M 語に絞っても、
   8 重のブロックで囲んだ再帰の 1 本のスタックが上限に届かない間隔である。 *)
let default_max_depth = 1 lsl 20

let reserve_of l = max 1024 (l / 64)

(* 限度を超えたときの文面。受け皿は先頭に「実行時エラー: 」を付けて標準エラーに書く *)
let depth_limit_message l = Printf.sprintf "論理的な深さが限度 %d を超えました" l

(* 錨。根の錨は親を持たず、差が 0 である。
   `an_memo` は、世代 `an_gen` のときに求めた錨の深さである *)
type anchor = { mutable an_parent : anchor option; mutable an_off : int; mutable an_memo : int; mutable an_gen : int }

(* 評価の全体で 1 つの状態。限度、根の錨、錨の世代の番号、ハンドラの起動の番号を持つ *)
type ctx = { c_max : int; mutable c_limit : int; c_root : anchor; mutable c_gen : int; mutable c_inst : int }

let root_anchor () = { an_parent = None; an_off = 0; an_memo = 0; an_gen = -1 }

(* 錨の深さ。覚えた値が今の世代のものでない錨を根の側へたどって集め、
   根に近いものから順に値を決めて覚える。
   たどる部分を末尾再帰で書くので、起動の入れ子が深くても OCaml のスタックを使わない *)
let anchor_depth ctx a =
  match a.an_parent with
  | None -> a.an_off
  | Some _ when a.an_gen = ctx.c_gen -> a.an_memo
  | Some _ ->
      let rec up a pending =
        match a.an_parent with
        | None -> (a.an_off, pending)
        | Some p -> if a.an_gen = ctx.c_gen then (a.an_memo, pending) else up p (a :: pending)
      in
      let base, pending = up a [] in
      List.fold_left
        (fun d x ->
          let d = d + x.an_off in
          x.an_memo <- d;
          x.an_gen <- ctx.c_gen;
          d)
        base pending

let depth_error ctx =
  ctx.c_limit <- ctx.c_max + reserve_of ctx.c_max;
  runtime_error (depth_limit_message ctx.c_max)

(* 錨 `a` と差 `off` の文脈から 1 段深い境目に入る。
   新しい深さを返し、限度を超えるなら入る前に誤りにする *)
let enter_depth ctx a off =
  let d = anchor_depth ctx a + off + 1 in
  if d > ctx.c_limit then depth_error ctx else d

(* 新しいファイバーで走らせる深さの間隔 4096 から 1 を引いた値 *)
let chunk_mask = 4095

(* 値も例外もエフェクトもそのまま外へ通すファイバーの中で `f` を走らせる *)
let in_fiber (f : unit -> 'a) : 'a =
  Effect.Deep.match_with f () { retc = Fun.id; exnc = raise; effc = (fun (type b) (_ : b Effect.t) -> None) }

(* ## 22.7 フレーム

   関数を 1 回呼ぶたびに、フレームを 1 つ作る。
   フレームは、スロットの配列、捕獲の配列、辞書の引数の配列、深さの錨と差、`resume` の宛先を持つ。
   スロットは引数が先で、局所が続く(IRSpec 6.4 節)。
   1 つのスロットを束縛する箇所はちょうど 1 つなので、
   パターンの照合はスロットに直接書き込み、失敗しても書いたものを戻さない。
   失敗した節のスロットは、その節の中からしか読まれないからである。

   `resume` の宛先(22.14 節の `resumption`)を持つのは、T と G の操作節の本体のフレームと、
   その中で評価したハンドラ式の本体のフレームである。
   ハンドラ式の本体の中の `resume` は、
   そのハンドラ式を囲む操作節の継続を再開するので(IRSpec 9.2 節)、
   本体のフレームは、ハンドラ式を評価したフレームの宛先を受け継ぐ。
   ほかのフレームは宛先を持たない。 *)
type frame = { slots : v array; caps : v array; dicts : dv array; anchor : anchor; off : int; res : resumption option }

(* 継続を再開する権利。継続、ハンドラの起動の番号と錨、
   継続の深さの差 `Δ = p − h`、使ったかどうかの印、節の中にいるかどうかの印を持つ *)
and resumption = {
  rs_inst : int;
  rs_k : (v, v) Effect.Deep.continuation;
  rs_anchor : anchor;
  rs_delta : int;
  mutable rs_used : bool;
  mutable rs_alive : bool;
}

let new_slots r = if r.nslots = 0 then [||] else Array.make r.nslots unit_v

let frame_depth ctx fr = anchor_depth ctx fr.anchor + fr.off

(* 起動の錨の親。起動の錨は必ず親を持つ *)
let anchor_parent x = match x.an_parent with Some a -> a | None -> bug "ハンドラの起動の錨に親がありません"

(* 利用者の操作の `perform` が送るエフェクト。
   エフェクトの記号、操作の短い名前、診断に書く名前、引数、`perform` のフレームの錨と差を持つ *)
type request = { q_eff : string; q_op : string; q_name : string; q_args : v array; q_anchor : anchor; q_off : int }

type _ Effect.t += Perform : request -> v Effect.t

(* 巻き戻しの通知(22.14 節)。第14章の `Unwind` と同じ規約で、値が本章の `v` である *)
type unwind = UValue of v | UClause of (unit -> v)

exception Unwind of int * unwind

(* 末尾の `resume` が、継続を再開せずに節の包みまで値を運ぶための例外(22.14 節) *)
exception Tail_resume of int * v

(* ## 22.8 パターン

   照合は IRSpec 8 節の規則である。
   照合に成功すれば真を返し、束縛はスロットに書く。
   `f64` のリテラルは IEEE 754 の `==` で比べるので、OCaml の `=` を使う。
   `Float.equal` は NaN 同士を等しいとするので使わない。
   ラベルの無いレコードとの照合は、実行時エラーでなく照合の失敗である。 *)
let rec match_pat slots (p : Ir.pat) v =
  match p with
  | Ir.PWild -> true
  | Ir.PBind n ->
      slots.(n) <- v;
      true
  | Ir.PLit l -> (
      match (l, v) with
      | Ir.LBool b, VBool b' -> b = b'
      | Ir.LI32 n, VI32 n' -> Int32.equal n n'
      | Ir.LI64 n, VI64 n' -> Int64.equal n n'
      | Ir.LF64 bits, VF64 f -> Int64.float_of_bits bits = f
      | Ir.LStr s, VStr s' -> String.equal s s'
      | _ -> false)
  | Ir.PRecord (fields, tail) -> (
      match v with
      | VRec fs ->
          let rec go fs = function
            | [] -> ( match tail with Ir.Rest p0 -> match_pat slots p0 (VRec fs) | Ir.Closed | Ir.Open -> true)
            | (l, p) :: rest -> (
                match record_take fs l with Some (x, fs') -> match_pat slots p x && go fs' rest | None -> false)
          in
          go fs fields
      | _ -> false)
  | Ir.PCtor (_, c, fields) -> (
      match v with
      | VData (c', fs) when String.equal c c' -> List.for_all (fun (i, p) -> match_pat slots p fs.(i)) fields
      | _ -> false)
  | Ir.PVariant (l, p) -> ( match v with VVariant (l', x) when String.equal l l' -> match_pat slots p x | _ -> false)

(* 操作節の引数のパターンを、`i` 番から先の引数のスロットと順に照合する *)
let rec match_params slots i = function [] -> true | p :: ps -> match_pat slots p slots.(i) && match_params slots (i + 1) ps

(* ## 22.9 KIR の木を写す

   表を記号で引き、22.2 節の `cexp` に写す。
   記号が表に無いのは、検証器を通った KIR では起こらないので、処理系の誤りにする。 *)
type tables = {
  t_fns : (string, rfn) Hashtbl.t;
  t_globals : (string, gcell) Hashtbl.t;
  t_gkinds : (string, Ir.global_kind) Hashtbl.t;
  t_insts : (string, inst) Hashtbl.t;
  t_arity : (string * string, int) Hashtbl.t;
  t_ops : (string * string, Ir.op) Hashtbl.t;
  t_bis : (string * string, bi) Hashtbl.t;
}

let find t tbl what k = match Hashtbl.find_opt tbl k with Some x -> x | None -> bug (what ^ "がありません: " ^ t k)

let find_fn t f = find Fun.id t.t_fns "関数" f

(* 組み込みのインスタンス(IRSpec 付録 A.3)の実装の表を、クラスと型の組ごとに 1 回だけ作る。
   第13章の表は単位の鍵の無い名前で引くので、記号から名前の部分を取り出して渡す。
   付録 A.2 のクラスのメソッドのうち、その型に実装のあるものだけを表に入れる。 *)
let builtin_instance t (p : Ir.program) cls ty =
  match Hashtbl.find_opt t.t_bis (cls, ty) with
  | Some b -> b
  | None ->
      let methods =
        match List.find_opt (fun (c : Ir.cls) -> String.equal c.c_sym cls) p.classes with
        | Some c -> List.map fst c.c_methods
        | None -> bug ("クラスがありません: " ^ cls)
      in
      let b =
        {
          bi_methods =
            List.filter_map
              (fun m -> Option.map (fun f -> (m, f)) (Builtin.builtin_method (display_of_symbol cls) (display_of_symbol ty) m))
              methods;
        }
      in
      Hashtbl.replace t.t_bis (cls, ty) b;
      b

let rec link_dict t p (d : Ir.dict) : cdict =
  match d with
  | Ir.DInst (i, ps) -> CDInst (find Fun.id t.t_insts "インスタンス" i, List.map (link_dict t p) ps)
  | Ir.DVar (Ir.VDParam i) -> CDParam i
  | Ir.DVar (Ir.VEnv i) -> CDEnv i
  | Ir.DVar (Ir.VLocal _) -> bug "辞書の式にスロットがあります"
  | Ir.DRecord fs -> CDRecord (List.map (fun (l, d) -> (l, link_dict t p d)) fs)
  | Ir.DVariant fs -> CDVariant (List.map (fun (l, d) -> (l, link_dict t p d)) fs)
  | Ir.DBuiltin (c, ty) -> CDBuiltin (builtin_instance t p c ty)

let lit_value = function
  | Ir.LBool b -> VBool b
  | Ir.LI32 n -> VI32 n
  | Ir.LI64 n -> VI64 n
  | Ir.LF64 bits -> VF64 (Int64.float_of_bits bits)
  | Ir.LStr s -> VStr s

let rec link t p (e : Ir.exp) : cexp =
  let link = link t p and link_dict = link_dict t p in
  let args es = Array.of_list (List.map link es) in
  match e with
  | Ir.Lit l -> CLit (lit_value l)
  | Ir.Lit_error (Ir.Lit_range, text) -> CLit_error text
  | Ir.Local i -> CLocal i
  | Ir.Env i -> CEnv i
  | Ir.Global g -> CGlobal (find Fun.id t.t_globals "大域" g)
  | Ir.Construct (ty, c, fs) ->
      CConstruct (c, find (fun (ty, c) -> ty ^ " " ^ c) t.t_arity "コンストラクタ" (ty, c), List.map (fun (i, e) -> (i, link e)) fs)
  | Ir.Variant (l, e) -> CVariant (l, link e)
  | Ir.Call c -> CCall (c.c_tail, link c.c_fn, args c.c_args)
  | Ir.Method (cls, m, d, own) -> CMethod (cls, m, link_dict d, List.map link_dict own)
  | Ir.Opcall (cls, m, d, es) -> COpcall (cls, m, link_dict d, args es)
  | Ir.Not e -> CNot (link e)
  | Ir.And (a, b) -> CAnd (link a, link b)
  | Ir.Or (a, b) -> COr (link a, link b)
  | Ir.Closure (f, cs) -> CClosure (find_fn t f, Array.of_list cs)
  | Ir.Dictabs (f, cs) -> CDictabs (find_fn t f, Array.of_list cs)
  | Ir.Dictapp (e, ds) -> CDictapp (link e, Array.of_list (List.map link_dict ds))
  | Ir.Let (n, a, b) -> CLet (n, link a, link b)
  | Ir.Letpat (pat, a, b) -> CLetpat (pat, link a, link b)
  | Ir.Letrec (items, body) ->
      let item (n, e) =
        match e with
        | Ir.Closure (f, cs) -> (n, false, find_fn t f, Array.of_list cs)
        | Ir.Dictabs (f, cs) -> (n, true, find_fn t f, Array.of_list cs)
        | _ -> bug "letrec の項目が closure でも dictabs でもありません"
      in
      CLetrec (List.map item items, link body)
  | Ir.Seq es -> CSeq (List.map link es)
  | Ir.Match (e, cls) -> CMatch (link e, List.map (fun (c : Ir.clause) -> { cc_pat = c.cl_pat; cc_guard = Option.map link c.cl_guard; cc_body = link c.cl_body }) cls)
  | Ir.Rec_empty -> CRec_empty
  | Ir.Rec_extend (l, a, b) -> CRec_extend (l, link a, link b)
  | Ir.Rec_select (l, e) -> CRec_select (l, link e)
  | Ir.Rec_restrict (l, e) -> CRec_restrict (l, link e)
  | Ir.Rec_update (l, a, b) -> CRec_update (l, link a, link b)
  | Ir.Perform (eff, op, es) -> (
      match Hashtbl.find_opt t.t_ops (eff, op) with
      | Some o when o.Ir.o_runtime -> CPerform_runtime (args es)
      | Some _ -> CPerform_user (eff, op, display_of_symbol eff ^ "." ^ op, args es)
      | None -> bug ("操作がありません: " ^ eff ^ "." ^ op))
  | Ir.Handle h ->
      let part (q : Ir.part) = (find_fn t q.p_fn, Array.of_list q.p_caps) in
      CHandle
        {
          ch_eff = h.h_effect;
          ch_body = part h.h_body;
          ch_ops =
            List.map
              (fun (o, cls, q) ->
                let r, cs = part q in
                (o, cls, r, cs))
              h.h_ops;
          ch_ret = Option.map part h.h_return;
          ch_cancel = Option.map part h.h_cancel;
        }
  | Ir.Resume (tail, e) -> CResume (tail, link e)
  | Ir.Hole -> CHole

(* ## 22.10 評価

   `eval` は写した式を評価する。
   子は、構成子の引数の順(正準のテキストに現れる順)に評価する。
   値を 1 つずつ `let` で束縛し、OCaml の未規定の評価順に任せない。
   引数の列は配列の添字の昇順に埋める。

   末尾位置の子(`let` の続き、`seq` の最後、`match` の節の本体、`and` と `or` の右辺)は、
   OCaml の末尾位置で評価する。
   `call` の印が `tail` なら、呼ばれた側の本体の評価も OCaml の末尾呼び出しになる。
   末尾位置の計算は書き手が済ませ、検証器が確かめてあるので、本章は印を読むだけである。 *)
let rec eval ctx fr (e : cexp) : v =
  match e with
  | CLit v -> v
  | CLit_error text -> runtime_error ("数値リテラルが範囲外です: " ^ text)
  | CLocal i -> fr.slots.(i)
  | CEnv i -> fr.caps.(i)
  | CGlobal c -> ( match c.g_val with Some v -> v | None -> runtime_error ("未束縛の変数: " ^ c.g_display))
  | CConstruct (c, n, fields) ->
      let arr = Array.make n unit_v in
      List.iter
        (fun (i, e) ->
          let x = eval ctx fr e in
          arr.(i) <- x)
        fields;
      VData (c, arr)
  | CVariant (l, e) ->
      let x = eval ctx fr e in
      VVariant (l, x)
  | CCall (tail, f, args) ->
      let f = eval ctx fr f in
      let args = match args with [| a |] -> [| eval ctx fr a |] | _ -> eval_args ctx fr args in
      if tail then apply ctx fr.anchor fr.off f args
      else
        let d = enter_depth ctx fr.anchor fr.off in
        if d land chunk_mask <> 0 then apply ctx fr.anchor (fr.off + 1) f args
        else in_fiber (fun () -> apply ctx fr.anchor (fr.off + 1) f args)
  | CMethod (cls, m, d, own) ->
      let dd = eval_dict fr d in
      let own = List.map (eval_dict fr) own in
      VMeth { m_cls = cls; m_name = m; m_dict = dd; m_own = own }
  | COpcall (cls, m, d, args) ->
      let dd = eval_dict fr d in
      (* 2 項の演算子は引数をこの枠の中で評価し、深い再帰で OCaml のスタックの枠を 1 つ減らす *)
      let args =
        match args with
        | [| a; b |] ->
            let x = eval ctx fr a in
            let y = eval ctx fr b in
            [| x; y |]
        | _ -> eval_args ctx fr args
      in
      let d = enter_depth ctx fr.anchor fr.off in
      if d land chunk_mask <> 0 then call_method ctx fr.anchor (fr.off + 1) cls m dd [] args
      else in_fiber (fun () -> call_method ctx fr.anchor (fr.off + 1) cls m dd [] args)
  | CNot e -> VBool (not (as_bool (eval ctx fr e)))
  | CAnd (a, b) -> if as_bool (eval ctx fr a) then eval ctx fr b else VBool false
  | COr (a, b) -> if as_bool (eval ctx fr a) then VBool true else eval ctx fr b
  | CClosure (r, cs) -> VClo (r, Array.map (read_var fr) cs)
  | CDictabs (r, cs) -> VDabs (r, Array.map (read_var fr) cs)
  | CDictapp (e, ds) ->
      let f = eval ctx fr e in
      let ds = Array.map (eval_dict fr) ds in
      let d = enter_depth ctx fr.anchor fr.off in
      if d land chunk_mask <> 0 then dictapp ctx fr.anchor (fr.off + 1) f ds
      else in_fiber (fun () -> dictapp ctx fr.anchor (fr.off + 1) f ds)
  | CLet (n, e1, e2) ->
      let x = eval ctx fr e1 in
      fr.slots.(n) <- x;
      eval ctx fr e2
  | CLetpat (p, e1, e2) ->
      let x = eval ctx fr e1 in
      if match_pat fr.slots p x then eval ctx fr e2 else runtime_error ("パターンに値が一致しません: " ^ show x)
  | CLetrec (items, body) ->
      (* 値をすべて作ってスロットに置いてから、捕獲を埋める。
         そのため、捕獲は群のどのスロットも読める *)
      let made =
        List.map
          (fun (n, is_dabs, r, cs) ->
            let caps = Array.make (Array.length cs) unit_v in
            fr.slots.(n) <- (if is_dabs then VDabs (r, caps) else VClo (r, caps));
            (caps, cs))
          items
      in
      List.iter (fun (caps, cs) -> Array.iteri (fun i c -> caps.(i) <- read_var fr c) cs) made;
      eval ctx fr body
  | CSeq es ->
      let rec go = function
        | [] -> unit_v
        | [ last ] -> eval ctx fr last
        | e :: rest ->
            let _ = eval ctx fr e in
            go rest
      in
      go es
  | CMatch (scrut, clauses) ->
      let x = eval ctx fr scrut in
      let rec try_clauses = function
        | [] -> runtime_error ("match のどの節にも一致しません: " ^ show x)
        | c :: rest -> (
            if not (match_pat fr.slots c.cc_pat x) then try_clauses rest
            else
              match c.cc_guard with
              | Some g -> if as_bool (eval ctx fr g) then eval ctx fr c.cc_body else try_clauses rest
              | None -> eval ctx fr c.cc_body)
      in
      try_clauses clauses
  | CRec_empty -> unit_v
  | CRec_extend (l, ev, er) ->
      let x = eval ctx fr ev in
      let r = eval ctx fr er in
      VRec ((l, x) :: record_fields r)
  | CRec_select (l, e) -> record_select (eval ctx fr e) l
  | CRec_restrict (l, e) -> record_restrict (eval ctx fr e) l
  | CRec_update (l, er, ev) ->
      let r = eval ctx fr er in
      let x = eval ctx fr ev in
      record_update r l x
  | CPerform_runtime args ->
      (* 実行時が処理する操作(プレリュードの `Console.write`)は、第13章の最も外側のハンドラへ送る。
         深さは変えず、限度の検査もしない *)
      let args = eval_args ctx fr args in
      let a = Value.VRecord (Array.to_list (Array.map (fun a -> (Type.l_item, to_value a)) args)) in
      of_value (Effect.perform (Value.Op (Builtin.op_console_write, a)))
  | CPerform_user (eff, op, name, args) -> (
      let args = eval_args ctx fr args in
      let q = { q_eff = eff; q_op = op; q_name = name; q_args = args; q_anchor = fr.anchor; q_off = fr.off } in
      (* どのハンドラも受け取らなければ、第14章と同じ形の例外にして、第16章の受け皿に操作の名前を渡す *)
      match Effect.perform (Perform q) with
      | x -> x
      | exception Effect.Unhandled (Perform _) -> raise (Effect.Unhandled (Value.Op (Type.intern name, Value.unit))))
  | CHandle h -> eval_handle ctx fr h
  | CResume (tail, e) -> eval_resume ctx fr tail e
  | CHole -> runtime_error "??? に到達しました"

and eval_args ctx fr args =
  let n = Array.length args in
  let arr = Array.make n unit_v in
  for i = 0 to n - 1 do
    arr.(i) <- eval ctx fr args.(i)
  done;
  arr

and read_var fr = function Ir.VLocal i -> fr.slots.(i) | Ir.VEnv i -> fr.caps.(i) | Ir.VDParam i -> VDict fr.dicts.(i)

(* 辞書の式の評価(IRSpec 5.2 節)。エフェクトを起こさず、実行時エラーにもならない *)
and eval_dict fr (d : cdict) : dv =
  match d with
  | CDInst (i, ps) -> DInst (i, List.map (eval_dict fr) ps)
  | CDParam i -> fr.dicts.(i)
  | CDEnv i -> ( match fr.caps.(i) with VDict d -> d | v -> bug ("辞書ではない捕獲: " ^ show v))
  | CDRecord fs -> DRecord (List.map (fun (l, d) -> (l, eval_dict fr d)) fs)
  | CDVariant fs -> DVariant (List.map (fun (l, d) -> (l, eval_dict fr d)) fs)
  | CDBuiltin b -> DBuiltin b

(* ## 22.11 呼び出し

   `apply ctx a off f args` は、値 `f` を引数の配列とともに、錨 `a` と差 `off` の深さで呼ぶ。
   この深さは呼ばれた側の深さで、呼び出し元が末尾かどうかで決めて渡す。
   クロージャは、新しいフレームを作って本体を OCaml の末尾で評価する。
   種類 `lambda` の仮引数は、変数ならスロットそのもの、ほかのパターンなら本体の `letpat` なので、
   引数をスロットの先頭に並べるだけでよい(IRSpec 6.3 節)。 *)
and apply ctx a off f args =
  match f with
  | VClo (r, caps) ->
      if Array.length args <> r.nparams then bug ("引数の個数が一致しません: " ^ r.fn.Ir.f_sym);
      let slots = new_slots r in
      Array.blit args 0 slots 0 r.nparams;
      eval ctx { slots; caps; dicts = [||]; anchor = a; off; res = None } r.body
  | VMeth m -> call_method ctx a off m.m_cls m.m_name m.m_dict m.m_own args
  | VExtern x -> call_extern x args
  | VBuiltin b -> call_builtin ctx a off b args
  | v -> bug ("関数ではない値を呼びました: " ^ show v)

and call_extern x args =
  match x.x_fn with
  | Some f -> call_prim f args
  | None ->
      runtime_error
        ("未実装のプリミティブ: " ^ x.x_display ^ if String.equal x.x_display x.x_impl then "" else "(実装名 " ^ x.x_impl ^ " が見つかりません)")

(* 辞書の適用(IRSpec 7.5 節)。`dictabs` の値は、辞書を受け取って本体を評価する。
   辞書を受け取る `extern` は、辞書を捨てて自分を返す *)
and dictapp ctx a off f ds =
  match f with
  | VDabs (r, caps) ->
      if Array.length ds <> r.fn.Ir.f_dicts then bug ("辞書の個数が一致しません: " ^ r.fn.Ir.f_sym);
      eval ctx { slots = new_slots r; caps; dicts = ds; anchor = a; off; res = None } r.body
  | VExtern _ -> f
  | v -> bug ("辞書を受け取らない値に辞書を渡しました: " ^ show v)

(* ## 22.12 メソッドの選択

   メソッドの値を呼ぶと、引数を評価し終えた後で、辞書からメソッドを選ぶ(IRSpec 5.4 節)。
   利用者のインスタンスは、初期化の前なら実行時エラーにする。
   実装の関数の辞書の数が 0 なら、`def_instance` が評価した値を使う。
   ほかは、前提の辞書とメソッド自身の辞書を渡して実装の関数の本体を評価し、得た値を呼ぶ。
   どちらも、メソッドの値を 1 回呼ぶことを、選んだ実装を 1 回呼ぶことと数える。
   実装の本体の評価も、得た値の呼び出しも、呼ばれた側の深さで行う。

   構造的な `Eq` の辞書は、項目の順にフィールドを取り出して比べる(IRSpec 7.6 節)。
   比べるたびに、フィールドの辞書のメソッドを末尾でない呼び出しとして呼ぶ。 *)
and call_method ctx a off cls m d own args =
  match d with
  | DInst (i, ps) ->
      if not i.i_ready then
        runtime_error
          (display_of_symbol i.ins.Ir.i_class ^ "[" ^ display_of_symbol i.ins.Ir.i_head
         ^ "] のインスタンスは宣言より前の位置では使えません(実行はまだ実体を持ちません。インスタンス宣言を使用より前に置いてください)");
      let f =
        match assoc_first m i.i_values with
        | Some f -> f
        | None -> (
            match assoc_first m i.i_impls with
            | Some r -> dictapp ctx a off (VDabs (r, [||])) (Array.of_list (ps @ own))
            | None -> bug ("メソッドがありません: " ^ i.ins.Ir.i_sym ^ "." ^ m))
      in
      apply ctx a off f args
  | DBuiltin b -> (
      match assoc_first m b.bi_methods with Some f -> call_prim f args | None -> bug ("組み込みのメソッドがありません: " ^ cls ^ "." ^ m))
  | DRecord fs ->
      if cls <> "builtin/Eq" then bug "構造的な辞書を Eq 以外に使いました";
      let x, y = arg2 args in
      VBool (record_eq ctx a off fs (record_fields x) (record_fields y))
  | DVariant fs -> (
      if cls <> "builtin/Eq" then bug "構造的な辞書を Eq 以外に使いました";
      match arg2 args with
      | VVariant (l1, p1), VVariant (l2, p2) ->
          VBool
            (String.equal l1 l2
            && match assoc_first l1 fs with Some d -> eq_with ctx a off d p1 p2 | None -> bug ("ヴァリアントの辞書にラベルがありません: " ^ l1))
      | _ -> bug "ヴァリアントではない値を比べました")

and arg2 args = if Array.length args = 2 then (args.(0), args.(1)) else bug "引数が 2 個ではありません"

and eq_with ctx a off d x y =
  let n = enter_depth ctx a off in
  as_bool
    (if n land chunk_mask <> 0 then call_method ctx a (off + 1) "builtin/Eq" "eq" d [] [| x; y |]
     else in_fiber (fun () -> call_method ctx a (off + 1) "builtin/Eq" "eq" d [] [| x; y |]))

and record_eq ctx a off fs xs ys =
  match fs with
  | [] -> xs = [] && ys = []
  | (l, d) :: rest -> (
      match (record_take xs l, record_take ys l) with
      | Some (x, xs'), Some (y, ys') -> eq_with ctx a off d x y && record_eq ctx a off rest xs' ys'
      | _ -> bug ("構造的な比較でラベルがありません: " ^ l))

(* ## 22.13 組み込みの値

   組み込みの値(IRSpec 付録 A.4)の振る舞いと誤りの文面は、第14章 §14.10 と同じである。
   利用者の関数を呼ぶ `Array.each` と `pinned` は、その呼び出しを末尾でない呼び出しとして数える。
   組み込み自身はそれを呼んだ呼び出しの呼ばれた側の深さで走るので、
   利用者の関数はそれより 1 つ深く走る。
   組み込みを末尾でない呼び出しで呼んだときは、呼び出しの位置の深さ + 2 になる。 *)
and call_builtin ctx a off b args =
  let callback f xs =
    let d = enter_depth ctx a off in
    if d land chunk_mask <> 0 then apply ctx a (off + 1) f xs else in_fiber (fun () -> apply ctx a (off + 1) f xs)
  in
  let index a i =
    let i = Int32.to_int i in
    if i < 0 || i >= Array.length a then runtime_error "配列の範囲外です" else i
  in
  match (b, args) with
  | BRef_new, [| x |] -> VRef (ref x)
  | BRef_get, [| VRef r |] -> !r
  | BRef_set, [| VRef r; x |] ->
      r := x;
      unit_v
  | BArray_length, [| VArray a |] -> VI32 (Int32.of_int (Array.length a))
  | BArray_get, [| VArray a; VI32 i |] -> a.(index a i)
  | BArray_each, [| VArray a; f |] ->
      Array.iter (fun x -> ignore (callback f [| x |])) a;
      unit_v
  | BMut_new, [| VI32 n; x |] ->
      if Int32.to_int n < 0 then runtime_error "MutableArray.new: 長さが負です" else VMutArray (Array.make (Int32.to_int n) x)
  | BMut_length, [| VMutArray a |] -> VI32 (Int32.of_int (Array.length a))
  | BMut_get, [| VMutArray a; VI32 i |] -> a.(index a i)
  | BMut_set, [| VMutArray a; VI32 i; x |] ->
      a.(index a i) <- x;
      unit_v
  | BMut_freeze, [| VMutArray a |] -> VArray (Array.copy a)
  | BPinned, [| f |] -> callback f [||]
  | _ -> bug ("組み込みの値の呼び出しが不正です: " ^ builtin_name b)

(* ## 22.14 ハンドラ式

   ハンドラ式は、第14章 §14.9 と同じく、評価するたびに 1 つの `Effect.Deep.match_with` になる。
   起動ごとの番号、`Unwind` の規約、3 つの経路、再開しない操作の節を `exnc` の末尾で評価すること、
   `cancel` 節の打ち切り、`resume` の検査の順序は、どれも第14章 §14.9 の説明のとおりである。
   本節は、第14章と違うところと、深さの規則(IRSpec 11.2 節)の当てはめ方を書く。

   ### 第14章と違うところ

   第14章は節の振り分けを精緻化木の印から決めるが、本章は KIR の分類(N、T、G)を読む。
   操作節の引数のパターンとガードは、`opclause` の関数の `pats` とガードの欄にある。
   パターンを引数のスロットと照合し、一致したらガードを評価する。

   第14章は節の本体の末尾の背骨をたどって末尾の `resume` を見つけるが、
   本章は `resume` の `tail` の印を読む。
   末尾の `resume` は、検査を済ませて使った印を立てた後、値を例外 `Tail_resume` に載せて投げる。
   節の本体の末尾位置は OCaml の末尾位置なので、
   この例外は途中に捕まえる箇所の無いまま節の包みに届く。
   包みは例外の場合の枝で `continue` を発行する。
   この枝は例外を捕まえる範囲(trap)を抜けた後にあるので、`continue` は末尾での発行になり、
   T の節で再開を繰り返すループは一定の領域で走る(第14章の「末尾 resume」と同じ理由)。
   例外は起動の番号を持ち、包みは自分の番号のものだけを受け取る。

   利用者の操作の `perform` は、本章のエフェクト `Perform` を送る。
   `effc` は、エフェクトの記号が自分のものと同じなら、その操作の節を持たなくても受け取る。
   どの節にも一致しなければ実行時の誤りであり、外側のハンドラへ送り直さない(IRSpec 9.4 節)。
   プレリュードの `Console.write` は第12章の `Op` のままなので、どのハンドラも受け取らずに、
   第13章の `with_runtime` へ届く。

   ### 深さ

   起動の錨(22.6 節)は、ハンドラ式を評価したフレームの錨と差を親と差に持つ。
   そのため起動の深さ `h` は、ハンドラ式を評価した文脈の深さになる。
   各部分のフレームの錨と差は次のとおりである。

   | 部分 | 錨 | 差 | 深さ |
   |---|---|---|---|
   | 本体 | 起動の錨 | 1 | `h + 1` |
   | 節の選択(パターンとガード)と T の節の本体 | `perform` のフレームの錨 | `perform` のフレームの差 + 1 | `p + 1` |
   | G の節の本体 | 起動の錨の親 | 起動の錨の差 + 1 | `h + 1` |
   | N の節の本体、`return` 節、`cancel` 節 | 起動の錨の親 | 起動の錨の差 | `h` |

   本体の深さは、ハンドラを連鎖に入れる前に限度と比べる。
   節の選択の深さは、節を試す前に限度と比べる。
   G の節の本体の深さは、節の包みの中で限度と比べる。
   どちらで限度を超えても、継続はまだ使っていないので、継続を捨てて巻き戻す。
   T の節の本体は節の選択と同じ深さなので、比べ直さない。

   G の節の本体を起動の錨そのものからの差にしないのは、
   末尾でない `resume` が起動の錨を付け替えても、節の本体の深さは変わらないからである。
   N の節の本体、`return` 節、`cancel` 節は、走るときに起動の錨の親と差を読む。
   再開した計算の中で走る `return` 節は、付け替えた後の深さ、つまり `resume` を評価した深さで走る。
   これは、その値が `resume` の値になること(IRSpec 9.5 節)と合う。

   末尾でない `resume` は、深さ `c` で評価したとき、再開した `perform` が深さ `c + Δ` になる。
   `Δ = p − h` は、`perform` を受け取ったときに求めて `resumption` に置く。
   継続の中のものはまとめてずれるので、`Δ` は継続が中断している間は変わらない。
   `c + Δ` は、使った印を立てる前に限度と比べる。
   超えたら、継続をまだ使っていないので、節が `resume` の前に脱出したときと同じく、
   継続を捨てて巻き戻す。
   超えなければ、使った印を立て、
   起動の錨を `resume` を評価したフレームの錨と差に付け替えてから再開する。

   T の節(とガード)を評価している間は、そのハンドラと、
   `perform` の位置からそのハンドラまでのハンドラが連鎖から外れる。
   その節から外側のハンドラの G の操作を起こすと、
   外れていたハンドラは外側の継続の中の文脈からだけ届く。
   これらのハンドラの錨も、T の節の本体のフレームの錨も、
   `perform` のフレームの錨を経由して外側の起動の錨に届く。
   そのため、外側の継続を再開して付け替えると、これらの深さもずれる(IRSpec 11.4 節)。

   末尾の `resume` は錨を付け替えない。
   T の節の末尾の `resume` は節の選択の前の状態に戻すだけで、継続は取り出したときの深さのまま続く。
   G の節の末尾の `resume` も、節の本体を捨てて継続をハンドラ式の位置に付け直すので、
   再開した計算は取り出したときの深さのまま続く。 *)
and eval_handle ctx fr h =
  ignore (enter_depth ctx fr.anchor fr.off);
  ctx.c_inst <- ctx.c_inst + 1;
  let inst = ctx.c_inst in
  let x = { an_parent = Some fr.anchor; an_off = fr.off; an_memo = 0; an_gen = -1 } in
  let part (r, cs) = (r, Array.map (read_var fr) cs) in
  let body_r, body_caps = part h.ch_body in
  let ops = List.map (fun (o, cls, r, cs) -> (o, cls, r, Array.map (read_var fr) cs)) h.ch_ops in
  let ret = Option.map part h.ch_ret in
  let cancel = Option.map part h.ch_cancel in
  let run_cancel () =
    match cancel with
    | None -> ()
    | Some (r, caps) ->
        (* cancel 節の中の例外は抑制してログに記録する(第14章 §14.9 の「cancel 節の実行文脈」)。
           節の中で限度を超えて予備に広げた限度は、節を出るときに節の前の値へ戻す *)
        let saved = ctx.c_limit in
        (try ignore (eval ctx { slots = new_slots r; caps; dicts = [||]; anchor = anchor_parent x; off = x.an_off; res = None } r.body)
         with
         | Value.Runtime_error msg -> !Interp.cancel_log msg
         | Unwind _ -> !Interp.cancel_log "cancel 節から操作の巻き戻しで脱出しようとしました"
         | Sys_error msg -> !Interp.cancel_log ("標準出力に書き出せません: " ^ msg)
         | ex -> !Interp.cancel_log (Printexc.to_string ex));
        ctx.c_limit <- saved
  in
  Effect.Deep.match_with
    (fun () -> eval ctx { slots = new_slots body_r; caps = body_caps; dicts = [||]; anchor = x; off = 1; res = fr.res } body_r.body)
    ()
    {
      retc =
        (fun v ->
          match ret with
          | None -> v
          | Some (r, caps) ->
              let slots = new_slots r in
              slots.(0) <- v;
              eval ctx { slots; caps; dicts = [||]; anchor = anchor_parent x; off = x.an_off; res = None } r.body);
      exnc =
        (fun ex ->
          match ex with
          | Unwind (id, UValue v) when id = inst -> v
          | Unwind (id, UClause f) when id = inst -> f ()
          | ex ->
              run_cancel ();
              raise ex);
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Perform q when String.equal q.q_eff h.ch_eff -> (
              let cands = List.filter (fun (o, _, _, _) -> String.equal o q.q_op) ops in
              Some (fun (k : (a, v) Effect.Deep.continuation) -> handle_op ctx inst x q cands k))
          | _ -> None);
    }

(* 起動 `inst`(錨 `x`)が操作 `q` を受け取った。
   節を選び、分類に従って節を評価する。
   包みの 3 つの経路は第14章 §14.9 と同じである *)
and handle_op ctx inst x q cands (k : (v, v) Effect.Deep.continuation) =
  let p = anchor_depth ctx q.q_anchor + q.q_off in
  let delta = p - anchor_depth ctx x in
  let select () =
    ignore (enter_depth ctx q.q_anchor q.q_off);
    let rec go = function
      | [] -> None
      | (_, cls, r, caps) :: rest -> (
          let slots = new_slots r in
          Array.blit q.q_args 0 slots 0 r.nparams;
          if not (match_params slots 0 r.fn.Ir.f_pats) then go rest
          else
            let gfr = { slots; caps; dicts = [||]; anchor = q.q_anchor; off = q.q_off + 1; res = None } in
            match r.guard with
            | None -> Some (cls, r, gfr)
            | Some g -> if as_bool (eval ctx gfr g) then Some (cls, r, gfr) else go rest)
    in
    go cands
  in
  match select () with
  | exception ex -> Effect.Deep.discontinue k ex
  | None ->
      let args = VRec (Array.to_list (Array.map (fun a -> ("_item", a)) q.q_args)) in
      Effect.Deep.discontinue k (Value.Runtime_error ("handle のどの節にも一致しません: " ^ q.q_name ^ show args))
  | Some (Ir.N, r, gfr) ->
      Effect.Deep.discontinue k
        (Unwind (inst, UClause (fun () -> eval ctx { gfr with anchor = anchor_parent x; off = x.an_off } r.body)))
  | Some (cls, r, gfr) -> (
      let rs = { rs_inst = inst; rs_k = k; rs_anchor = x; rs_delta = delta; rs_used = false; rs_alive = true } in
      match
        let bfr =
          match cls with
          | Ir.G ->
              let a = anchor_parent x in
              ignore (enter_depth ctx a x.an_off);
              { gfr with anchor = a; off = x.an_off + 1; res = Some rs }
          | Ir.T | Ir.N -> { gfr with res = Some rs }
        in
        eval ctx bfr r.body
      with
      | v ->
          rs.rs_alive <- false;
          if rs.rs_used then v else Effect.Deep.discontinue k (Unwind (inst, UValue v))
      | exception Tail_resume (id, v) when id = inst ->
          rs.rs_alive <- false;
          Effect.Deep.continue k v
      | exception ex ->
          rs.rs_alive <- false;
          if rs.rs_used then raise ex else Effect.Deep.discontinue k ex)

(* `resume`。検査の順序は第14章の `take_resume` と同じで、引数を評価した後で、
   節の中にいるか、まだ使っていないかを調べる。
   末尾でない `resume` は、さらに再開した `perform` の深さを限度と比べてから使った印を立てる *)
and eval_resume ctx fr tail e =
  match fr.res with
  | None -> runtime_error "resume は操作節の中でのみ使えます"
  | Some rs ->
      let v = eval ctx fr e in
      if not rs.rs_alive then runtime_error "resume を節の外で呼び出しました(second-class)"
      else if rs.rs_used then runtime_error "resume は高々1回しか呼べません(アフィン)"
      else if tail then (
        rs.rs_used <- true;
        raise (Tail_resume (rs.rs_inst, v)))
      else (
        if frame_depth ctx fr + rs.rs_delta > ctx.c_limit then depth_error ctx;
        rs.rs_used <- true;
        let x = rs.rs_anchor in
        x.an_parent <- Some fr.anchor;
        x.an_off <- fr.off;
        ctx.c_gen <- ctx.c_gen + 1;
        Effect.Deep.continue rs.rs_k v)

(* ## 22.15 表を作る

   関数の表の項目を先にすべて作り、続けて大域とインスタンスの表を作り、最後に本体を写す。
   組み込みの値は、プログラムの開始の時点で初期化済みである(IRSpec 10.3 節)。 *)
let build_tables (p : Ir.program) =
  let t =
    {
      t_fns = Hashtbl.create 256;
      t_globals = Hashtbl.create 256;
      t_gkinds = Hashtbl.create 256;
      t_insts = Hashtbl.create 64;
      t_arity = Hashtbl.create 64;
      t_ops = Hashtbl.create 32;
      t_bis = Hashtbl.create 32;
    }
  in
  List.iter
    (fun (f : Ir.fn) ->
      let nparams = List.length f.f_params in
      Hashtbl.replace t.t_fns f.f_sym { fn = f; nparams; nslots = nparams + List.length f.f_locals; body = CHole; guard = None })
    p.functions;
  List.iter
    (fun (g : Ir.global) ->
      Hashtbl.replace t.t_gkinds g.g_sym g.g_kind;
      let init =
        match g.g_kind with
        | Ir.GBuiltin -> (
            match List.find_opt (fun b -> String.equal ("builtin/" ^ builtin_name b) g.g_sym) all_builtins with
            | Some b -> Some (VBuiltin b)
            | None -> bug ("組み込みの値がありません: " ^ g.g_sym))
        | _ -> None
      in
      Hashtbl.replace t.t_globals g.g_sym { g_display = display_of_symbol g.g_sym; g_val = init })
    p.globals;
  List.iter
    (fun (i : Ir.instance) ->
      let impls = List.map (fun (m, _, f) -> (m, find_fn t f)) i.i_methods in
      Hashtbl.replace t.t_insts i.i_sym { ins = i; i_impls = impls; i_ready = false; i_values = [] })
    p.instances;
  List.iter (fun (ty : Ir.ty) -> List.iter (fun (c : Ir.ctor) -> Hashtbl.replace t.t_arity (ty.t_sym, c.ct_name) c.ct_arity) ty.t_ctors) p.types;
  List.iter (fun (e : Ir.eff) -> List.iter (fun (o : Ir.op) -> Hashtbl.replace t.t_ops (e.e_sym, o.o_name) o) e.e_ops) p.effects;
  Hashtbl.iter
    (fun _ r ->
      r.body <- link t p r.fn.Ir.f_body;
      r.guard <- Option.map (link t p) r.fn.Ir.f_guard)
    t.t_fns;
  t

(* ## 22.16 初期化

   単位を並んだ順に、各単位の手順を書いた順に実行する(IRSpec 10.1 節)。
   最上位の手順は深さ 0 で走る。
   `thunk` の関数の本体は、手順そのものとして深さ 0 で評価し、呼び出しとは数えない。
   `def_instance` の実装の関数の評価も同じである。 *)
let eval_thunk t ctx f =
  let r = find_fn t f in
  eval ctx { slots = new_slots r; caps = [||]; dicts = [||]; anchor = ctx.c_root; off = 0; res = None } r.body

let define t g v = (find Fun.id t.t_globals "大域" g).g_val <- Some v

(* 種類が `fn`、`dictabs`、`extern` の大域を、評価せずに初期化済みにする *)
let define_fn t g =
  match Hashtbl.find_opt t.t_gkinds g with
  | Some (Ir.GFn f) -> define t g (VClo (find_fn t f, [||]))
  | Some (Ir.GDictabs f) -> define t g (VDabs (find_fn t f, [||]))
  | Some (Ir.GExtern { abi; impl; _ }) ->
      let abi = match abi with Ir.Prim -> "prim" | Ir.C -> "C" in
      define t g (VExtern { x_display = display_of_symbol g; x_impl = impl; x_fn = Builtin.find_extern ~abi impl })
  | Some _ -> bug ("def_fns に関数でない大域があります: " ^ g)
  | None -> bug ("大域がありません: " ^ g)

let exec_step t ctx (s : Ir.step) =
  match s with
  | Ir.Def_value (g, f) -> define t g (eval_thunk t ctx f)
  | Ir.Def_pattern (f, gs, p) ->
      let x = eval_thunk t ctx f in
      let slots = Array.make (List.length gs) unit_v in
      if not (match_pat slots p x) then runtime_error ("パターンに値が一致しません: " ^ show x);
      List.iteri (fun i g -> define t g slots.(i)) gs
  | Ir.Def_fns gs -> List.iter (define_fn t) gs
  | Ir.Def_dictabs g -> define_fn t g
  | Ir.Def_instance i ->
      (* 辞書の引数の数が 0 の実装を、メソッドを書いた順に 1 回だけ評価する。
         評価し終えるまで、インスタンスは初期化の前である *)
      let x = find Fun.id t.t_insts "インスタンス" i in
      List.iter
        (fun (m, r) ->
          if r.fn.Ir.f_dicts = 0 then
            let v = eval_thunk t ctx r.fn.Ir.f_sym in
            x.i_values <- x.i_values @ [ (m, v) ])
        x.i_impls;
      x.i_ready <- true
  | Ir.Run_exp f -> ignore (eval_thunk t ctx f)

(* ## 22.17 入口

   全体を第13章の `Builtin.with_runtime` の中で走らせる。
   `Console.write` の書き込みと、書き込みが失敗したときの扱いは、第14章とまったく同じになる。 *)
let run ?(max_depth = default_max_depth) ~sink (p : Ir.program) =
  let t = build_tables p in
  let ctx = { c_max = max_depth; c_limit = max_depth; c_root = root_anchor (); c_gen = 0; c_inst = 0 } in
  ignore
    (Builtin.with_runtime ~sink (fun () ->
         List.iter (fun (u : Ir.unit_) -> List.iter (exec_step t ctx) u.u_init) p.units;
         Value.unit))
