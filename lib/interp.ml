(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第14章 評価器

   本章は処理系の中心で、木をたどって値を作る。
   受け取るのは、第11章(elab.ml)が型と解決結果を書き込んだ木、
   第12章(value.ml)の値の表現とレコード演算、
   第13章(builtin.ml)のプリミティブと最も外側のハンドラである。
   第16章(driver.ml)へ渡すのは、正常に終了したか、どの例外で終わったかだけである。

   評価器の大半は、木を単純に走査するだけである。
   込み入っている部分は 2 つある。
   エフェクトハンドラ(§14.9)と、型クラスの辞書(§14.6 と §14.7)である。
   前者は Keleut の意味論を OCaml 5 の `Effect.Deep` で実装する部分である。
   後者は、型検査が木に書いた証拠(どのインスタンスの辞書を使うかを表す項)から辞書を作り、
   メソッドを選ぶ部分である。
   どちらも、誤って実装してもエラーにならず、誤りに気づきにくい。

   ## Keleut のハンドラと OCaml 5 の Effect.Deep の対応

   Diktor は、Keleut のエフェクトを OCaml 5 の `Effect.Deep` にそのまま対応させる。
   対応は次のとおりである。

   | Keleut(sample.kel §9) | OCaml 5 の Effect.Deep |
   |---|---|
   | 深いハンドラ `handle { … }` | `match_with` 1 つ |
   | `perform op(args)` | `Effect.perform (Op (op, args))` |
   | `resume(e)` | `Effect.Deep.continue k v` |
   | resume を呼ばずに節を抜ける | `discontinue k (Unwind (inst, UValue v))` |
   | 再開しない操作の節 | 節の本体の前に `discontinue`、本体は `exnc` の末尾で評価 |
   | `case return(x)` | `retc`(親のスタック上で実行される) |
   | `case cancel` | `exnc` の中で節を実行する |
   | 最も内側のハンドラが操作を受け取る | `effc` が `None` を返せば外側へ進む |
   | resume はアフィン(高々 1 回) | ワンショット継続(先に評価器が検査する) |
   | resume の返り値の型が handle 式全体の型 | `continue` の型が `match_with` の型 |
   | cancel 節を LIFO の順に実行する巻き戻し | fiber の入れ子から自動で決まる |

   後始末の順序は、fiber の入れ子という OCaml の側の構造から決まる。
   そのため、評価器は後始末の順序を管理しなくてよい。

   ## 本章が守る 3 つの規約

   1. 末尾呼び出しの規約。
      `eval` の末尾位置(`Apply` のクロージャ本体、`Match` の節本体、ブロックの末尾式)では、
      OCaml の末尾呼び出しを保つ。
      とくに、`eval` の再帰を `try … with` で囲まない。
      Keleut には while がなく、反復の手段は再帰だけなので、末尾呼び出しの最適化が行われなくなると、
      普通のループがスタックを使い尽くす。
      この規約が当てはまらないのは、操作節の本体(短い経路では `resume` の引数)、操作節のガード、
      cancel 節の本体である。
      操作節の本体とガードは §14.9 の 3 つの経路を判定するために、
      cancel 節の本体は中の例外を抑制するために、
      try ブロックの中で評価する。
      そのため、これらの中の末尾位置にある関数呼び出しは、末尾呼び出しにならない。
      操作節の本体のうち、末尾の背骨(本体から末尾位置だけをたどった経路。§14.9)にある
      `resume` だけは、try ブロックを抜けてから、継続を末尾呼び出しで再開する。
      再開しない操作の節の本体は、継続を捨てた後に try ブロックの外で評価するので、
      末尾位置を保つ(§14.9)。

   2. 評価順序を let で固定する。
      OCaml は関数適用で引数を評価する順序を規定しておらず、現行のコンパイラは右から左に評価する。
      Keleut の仕様は左から右(sample.kel:277)なので、
      `apply (eval env f) (eval env arg)` と書くと順序が逆になる。
      値を 1 つずつ `let` で束縛し、OCaml が規定していない順序に依存しないようにする。

   3. 例外をエラーメッセージにする処理(種別を付けて文字列にする)は、
      driver の最も外側で 1 回だけ行う。
      途中で例外を捕捉して別の例外に作り直すと、規約 1 に違反する。
      さらに、例外はエフェクトの巻き戻しにも使っている(§14.9 の `Unwind`)ので、
      途中で捕捉して扱いを誤ると、意味論が壊れる。

   ## 本章の構成

   表(§14.1)、パターン照合(§14.2)、数値リテラル(§14.3)、`eval` の骨格(§14.4)、適用(§14.5)、
   辞書とメソッドの選択(§14.6)、構造的等価(§14.7)、束縛(§14.8)、ハンドラ(§14.9)、
   組み込み値(§14.10)、クラスメソッドの参照(§14.11)、宣言の実行(§14.12)、`run`(§14.13)、
   本章の限界(§14.14)、対話的な実行(§14.15)の順に述べる。 *)
open Aux
open Syntax
open Value
module T = Tree.Tree

(* ## 14.1 実行時に引く表

   型クラスのメソッドをどのインスタンスで呼ぶかは、型検査が型から決め、
   証拠として木に書く(第5章 §5.1b)。
   評価器は証拠から辞書を作り(§14.6)、辞書が指す (クラス, 型構成子) でインスタンス表を引く。
   実行時の値のタグは調べない。
   必要な表は、ユーザが宣言したインスタンスの `instance_impls` と、
   第13章の組み込みのメソッド表である。
   型構成子は第1章のインターン表の oid で表し、型と同じ番号を使う。
   辞書パラメータは、環境の `dicts` に、キー (型変数の vid, クラスの oid) で置く(第12章 §12.3)。
   `dicts` は環境の一部なので、クロージャは `c_env` に入れた環境とともに辞書もキャプチャする。
   辞書のための別の仕組みは持たない。
   キーを整数の組のまま比べるので、辞書を引くたびに名前の文字列を作ることはない。 *)

(* ユーザが宣言したインスタンスのメソッド。(クラス, 型構成子) から、
   メソッド名と実装の対のリストを引く。
   実装は、前提の辞書とメソッド自身の辞書を受け取って値を返す関数である。
   書き込むのは exec_decl の DInstance だけで、jreplace を使う *)
let instance_impls : (oid * oid, (oid * (Value.t list -> Value.t)) list) Hashtbl.t = Hashtbl.create 32

(* 辞書パラメータのキー(型変数の vid, クラスの oid)を、診断のために文字列にする *)
let dkey_name ((v, c) : Tree.dkey) = "$d" ^ string_of_int v ^ ":" ^ string_of_int c

let bind_dicts env ks ds = { env with dicts = List.fold_left2 (fun m k d -> DMap.add k d m) env.dicts ks ds }

(* 辞書パラメータを含まない証拠から作る辞書は、穴ごとに 1 回だけ作ってキャッシュする *)
let closed_cache : (oid, Value.t) Hashtbl.t = Hashtbl.create 64

let rec closed_ev (e : Tree.evidence) =
  match e with
  | Tree.EvParam _ -> false
  | Tree.EvInst (_, _, subs) -> List.for_all closed_ev subs
  | Tree.EvRecord fs | Tree.EvVariant fs -> List.for_all (fun (_, e) -> closed_ev e) fs
  | Tree.EvHole h -> ( match h.Tree.h_sol with Some e -> closed_ev e | None -> false)

let dict_params_of node = match Tree.get_dict node with Tree.DAbs ks | Tree.DMethod (ks, _, _) -> ks | _ -> []

(* `cancel_log` は、cancel 節で抑制した例外の出力先である。
   仕様 sample.kel:585 は、cancel 節について次のように定めている。
   cancel 節から外へは脱出できない。
   例外に相当するものが起きると、その cancel 節の実行はそこで終わるが、
   脱出は抑制してログに記録し、外側の後始末を続ける。
   ライブラリが stderr に直接書かないよう、関数の参照を 1 つ挟み、
   driver(第16章)がその関数を差し替える。 *)

(* cancel 節の中の例外を記録する関数(sample.kel:585)。driver が差し替える *)
let cancel_log : (string -> unit) ref = ref (fun _ -> ())

(* ## 14.2 パターン照合

   `match_pat` は、照合に成功したら束縛を追加した locals を `Some` で返し、
   失敗したら `None` を返す。
   失敗を例外にしないのは、照合の失敗が match の次の節へ進むための正常な制御で、
   エラーではないからである。

   注意が必要なのは次の 3 点である。

   - レコードは最左一致で照合する(Scoped Labels、第12章)。
     `record_take` が最も左の同名のラベルを 1 つ取り出して残りを返すので、
     同名のラベルを 2 つ持つ値から 2 回取り出すと、2 回目は隠れていたほうのフィールドが得られる。
     ラベルがないときに `record_take` が投げる `Runtime_error` は、ここでは照合の失敗なので、
     `exception` パターンで受けて `None` に変える。
     実行時エラーとして外へは出さない。
   - コンストラクタパターンは表を引くだけである。
     位置引数とラベル引数の混在や、省略されたフィールドの扱いは、
     elab が `field_to_arg` にまとめている(第5章(tree.ml)の `resolved`)。
     `None` は、そのフィールドに対応するパターンが書かれていないことを表す。
     ここで名前解決をやり直すと、elab と interp が同じ規則を二重に実装することになり、
     両者が食い違うことがある。
   - 数値パターンは、表記ではなく値で比べる。
     リテラルの表記を照合対象の値の型で読み直してから比べるので、`0x1` と `1` は一致する。
     第10章(exhaust.ml)の重複検出も、表記を数値として読んでから比べる。

   `bind_pat_exn` は、反駁できない(どの値にも一致する)はずの位置で使う。
   `let`、関数の引数、`return` 節である。
   操作節の引数には使わない。
   操作節の引数は `match_pat` で照合し、一致しなければ次の節へ進む(§14.9)。
   `let`、`let rec`、`fn` の引数と `return` 節に書いた反駁可能な(一致しない値がある)パターンは、
   `Exhaust.queue` で網羅性検査の対象になる。
   ただし網羅性検査は、既定では警告を出すだけである(`--strict-exhaustive` ではエラーになる)。
   警告を受けたまま実行したプログラムでは、値がパターンに一致しないことがあり、
   そのとき `bind_pat_exn` は実行時エラーにする。 *)

let rec match_pat locals ((_, p) as node : T.pat) v =
  match p with
  | T.PWildcard -> Some locals
  | T.PVar x -> Some (SMap.add x v locals)
  | T.PAnnot (sub, _) -> match_pat locals sub v
  | T.PBool b -> ( match v with VBool b2 when b = b2 -> Some locals | _ -> None)
  | T.PText s -> ( match v with VText s2 when String.equal s s2 -> Some locals | _ -> None)
  | T.PNumber n -> (
      match v with
      | VInt32 x -> ( match Int32.of_string_opt n.n_text with Some y when x = y -> Some locals | _ -> None)
      | VInt64 x -> ( match Int64.of_string_opt n.n_text with Some y when x = y -> Some locals | _ -> None)
      | VFloat64 x -> ( match float_of_string_opt n.n_text with Some y when x = y -> Some locals | _ -> None)
      | _ -> None)
  | T.PVariant (s, sub) -> (
      match v with VVariant (l, payload) when l = Type.intern s -> match_pat locals sub payload | _ -> None)
  | T.PRecord (fields, rest) -> (
      let rec go locals remaining = function
        | [] -> (
            match rest with None -> Some locals | Some rp -> match_pat locals rp remaining)
        | (l, sub) :: tl -> (
            match record_take remaining (Type.intern l) with
            | x, remaining' -> ( match match_pat locals sub x with Some locals -> go locals remaining' tl | None -> None)
            (* ラベルがないのは照合の失敗であって、実行時エラーではない *)
            | exception Runtime_error _ -> None)
      in
      match v with VRecord _ -> go locals v fields | _ -> None)
  | T.PCtor (_, args) -> (
      match Tree.get_resolved node with
      | Some (Tree.RCtorPat (_, ctor, field_to_arg)) -> (
          match v with
          | VData d when d.d_ctor = ctor ->
              let rec go locals fi =
                if fi >= Array.length field_to_arg then Some locals
                else
                  match field_to_arg.(fi) with
                  (* 省略されたフィールドは照合しない *)
                  | None -> go locals (fi + 1)
                  | Some ai -> (
                      match match_pat locals (List.nth args ai).T.cap_pat d.d_fields.(fi) with
                      | Some locals -> go locals (fi + 1)
                      | None -> None)
              in
              go locals 0
          | _ -> None)
      | _ -> bug "PCtor が解決されていません")

let bind_pat_exn locals pat v =
  match match_pat locals pat v with
  | Some locals -> locals
  | None -> runtime_error ("パターンに値が一致しません: " ^ show v)

(* ## 14.3 数値リテラル

   `1` が `Int32`、`Int64`、`Float64` のどれなのかは、表記からは決まらない。
   決めるのは型検査で、既定化(defaulting)の結果がノードの型に書かれている。
   評価器は実行時に型を持ち運ばない。
   elab が書き込んだ型を評価器が読むのはここだけで、
   ほかのノードでは `resolved`(解決結果)と辞書の情報(§14.6)しか読まない。

   リテラルの表記は、字句解析が読み取ったまま(`0x` 接頭辞やアンダースコアの区切りを含む)保持されており、
   OCaml の `Int32.of_string` はそれをそのまま解釈できる。
   範囲外のリテラルで起きる `Failure` は、`Runtime_error` に変換する。
   変換しないと、ユーザのプログラムの誤りである範囲外のリテラルを、
   driver(第16章)の最上位の例外ハンドラの最後の節が `内部エラー: 予期しない例外です` として報告する。
   終了コードは `Runtime_error` の場合と同じ 3 だが、ユーザには処理系のバグに見える。 *)

let number_value node (n : number) =
  let head =
    match Type.repr (Tree.get_ty node) with
    | Type.TCon (c, _) -> Type.name_of c
    | _ -> runtime_error "数値リテラルの型が解決されていません"
  in
  try
    match head with
    | "Int32" -> VInt32 (Int32.of_string n.n_text)
    | "Int64" -> VInt64 (Int64.of_string n.n_text)
    | "Float64" -> VFloat64 (float_of_string n.n_text)
    | t -> runtime_error ("数値リテラルの型が不正です: " ^ t)
  with Failure _ -> runtime_error ("数値リテラルが範囲外です: " ^ Lexer.show_number n)

(* ## 14.4 eval の骨格

   本体は、木を単純に走査するだけである。
   以下では、ノードごとの注意点だけを述べる。

   ### 評価順序

   `Apply`、`BinOp`、`RecordUpdate` は、規約 2 に従って `let` で左から右の順序に固定する。
   OCaml に任せると右から左になり、
   副作用のあるプログラム(perform を含む)の出力の順序が仕様と食い違う。

   `RecordExtend (rest, l, v)` だけは、v を先に、rest を後に評価する。
   仕様(sample.kel:278)が、`{l = e extends r}` では e を先に、r を最後に評価すると定めている。
   タプルの脱糖がこの規則に従うので、`(a, b, c)` は a、b、c の順に評価される。
   この順序は AST のフィールドの順序と逆なので、コードを読むときに間違えやすい。

   `Construct` は、評価の順序と格納の順序を分ける。
   評価はソースの順、格納は宣言したフィールドの順である。
   `List.iteri` でソースの順に評価し、書き込み先は elab が作った `arg_to_field` の表で引く。

   ### ノードごとの要点

   - `Ident` は 3 段階で引く。
     locals(不変の Map)、elab が `resolved` に書いたトップレベルの参照先(`RVar`)、
     引数のないコンストラクタ(`RCtor`)の順である。
     トップレベルの参照先は、globals(可変の Hashtbl)をキー `Tree.gref` で引く。
     globals は可変で、値は名前を評価する時点で引く。
     関数の本体に書いた名前は、関数を呼び出した時点で引くことになる。
     そのため、トップレベルの相互参照と前方参照が、
     追加のコードなしで動く(第12章 §12.3 の環境の 2 つの層)。
     同名の再束縛は、束縛ノードごとに別のキーになるので、前の束縛を上書きしない(§14.12)。
     `RVar` のキーが globals にないのは、初期化の前のグローバル変数を読んだ場合で、
     実行時エラーにする。
     `resolved` が `RVar` でも `RCtor` でもなければ、型検査の解決と評価器の解決が食い違っている。
     型検査が訪れなかった `Ident` を評価したか、
     型検査がローカルと判断した名前が実行時の locals にないかのどちらかで、
     どちらも処理系のバグ(`bug`)として報告する。
   - `BinOp` は第7章(prims.ml)の表を引くだけである。
     `Neg` も同じく、第7章の `neg_method` で `Neg.neg` を呼ぶ。
     `&&` と `||` だけは、短絡評価で右辺を評価しないことがあるので、型クラスのメソッドにできない。
     `!=` は `Eq.eq` の否定として同じ表に入っている。
   - `Match` では、節のガードが偽なら次の節へ進む。
     `try_clauses` は末尾再帰で、節本体の `eval` も末尾位置にある(規約 1)。
     ハンドラの操作節も同じ規則で、
     パターンが一致しないときもガードが偽のときも次の節へ進む(§14.9)。
   - `Perform` は、elab が `resolved` に書いた完全な操作名の oid をそのまま使う。
     修飾なしで書いた操作名の解決(第11章 §11.20)は型検査で済んでおり、実行時に名前を探すことはない。
   - `Resume` は、継続を消費済みにする前に引数を評価する。
     `resume(f())` の `f` が例外で脱出すれば、resume は未消費のまま、
     節が例外で脱出した経路(§14.9。`discontinue` で継続を捨てる)に進む。
     ただし、引数の中の入れ子の resume がすでに継続を再開していれば、
     この経路は例外をそのまま再送出し、継続を捨てない。
     先に消費済みにしてから引数を評価すると、引数が例外で脱出したときに、
     この経路が継続を再開済みと判断し、再開していない継続を捨てなくなる。
     この分岐で評価するのは、節本体の末尾の背骨(§14.9)の外にある `resume` だけである。
     背骨の上の `resume` は §14.9 の `eval_clause_tail` が処理し、その経路でも `take_resume` が
     引数を先に評価する。
   - `Run` は、実行時には本体を評価するだけである。
     `run h { … }` の `h` は型の上にしか存在しない。
     リージョンの安全性は、第11章のスコーレム定数(型パラメータを固定した定数。コードでは
     `Rigid`)とレベルが保証している。
     操作を持たないエフェクトラベル(`Heap`、`Blocking`)には、実行時の処理がない。
     行から `Blocking` を取り除く組み込み関数 `pinned` も、
     実行時には渡された関数を呼ぶだけである(§14.10)。
     型検査で保証した性質を、実行時に検査し直すことはしない。 *)

(* 操作節の本体を末尾の背骨に沿って評価した結果(§14.9)。
   `Clause_resume v` は、背骨の末尾の `resume(v)` に達したことを表す。
   継続はまだ再開していない。再開は、呼び出し元が try ブロックを抜けてから行う *)
type clause_end = Clause_value of Value.t | Clause_resume of Value.t

(* 初期化の前のグローバル変数を読んだときの診断に書く名前。ソースに書いた参照の表記ではなく、
   module の修飾を含み、単位の接頭辞 `%N.` を取り除いた名前にする。
   KIR のリーダも、グローバルのシンボルから同じ名前を作れるようにするためである *)
let global_display = function Tree.GDecl (_, x) -> Type.display x | Tree.GBuiltin x -> x | Tree.GMethod q -> Type.display q

let rec eval env ((_, e) as node : T.exp) : Value.t =
  match e with
  | T.Bool b -> VBool b
  | T.Text s -> VText s
  | T.Number n -> number_value node n (* 評価器が elab の型を読む唯一の箇所(§14.3) *)
  | T.Hole -> runtime_error "??? に到達しました"
  | T.Ident li -> (
      let name = show_long_id li in
      match SMap.find_opt name env.locals with
      | Some v -> with_evidence env node v
      | None -> (
          match Tree.get_resolved node with
          | Some (Tree.RVar g) -> (
              match Hashtbl.find_opt env.globals g with
              | Some v -> with_evidence env node v
              | None -> runtime_error ("未束縛の変数: " ^ global_display g))
          (* Ident として書いた、引数のないコンストラクタ *)
          | Some (Tree.RCtor (_, c, _)) -> VData { d_ctor = c; d_fields = [||] }
          | _ -> bug ("Ident が解決されていません: " ^ name)))
  | T.Lambda { l_params; l_body } -> VClosure { c_env = env; c_params = l_params; c_body = l_body }
  | T.Apply (f, arg) ->
      (* 左から右に評価する。OCaml が規定していない評価順序に任せない(規約 2) *)
      let vf = eval env f in
      let va = eval env arg in
      apply vf va
  | T.Construct (_, args) -> (
      match Tree.get_resolved node with
      | Some (Tree.RCtor (_, c, arg_to_field)) ->
          let fields = Array.make (Array.length arg_to_field) unit in
          List.iteri
            (fun ai (a : T.ctor_arg) ->
              (* 評価はソースの順、格納は宣言したフィールドの順(resolved の対応表) *)
              fields.(arg_to_field.(ai)) <- eval env a.T.ca_exp)
            args;
          VData { d_ctor = c; d_fields = fields }
      | _ -> bug "Construct が解決されていません")
  | T.Variant (s, payload) -> VVariant (Type.intern s, eval env payload)
  | T.BinOp (l, op, r) -> (
      match Prims.bin_op_sem op with
      | Prims.OpBool -> (
          (* 短絡評価(sample.kel:369) *)
          match op with
          | And -> if Builtin.as_bool (eval env l) then eval env r else VBool false
          | Or -> if Builtin.as_bool (eval env l) then VBool true else eval env r
          | _ -> bug "OpBool")
      | Prims.OpMethod (cls, m) ->
          (* 辞書はオペランドより先に作る。辞書を作っても副作用はない。
             後で作ると、右辺を評価している間も env が参照されたまま残る *)
          let d = op_dict env node in
          let vl = eval env l in
          let vr = eval env r in
          apply (select_method ~cls:(Type.intern cls) d m []) (VRecord [ (Type.l_item, vl); (Type.l_item, vr) ])
      | Prims.OpMethodNot (cls, m) ->
          let d = op_dict env node in
          let vl = eval env l in
          let vr = eval env r in
          VBool (not (Builtin.as_bool (apply (select_method ~cls:(Type.intern cls) d m []) (VRecord [ (Type.l_item, vl); (Type.l_item, vr) ])))))
  | T.Not e -> VBool (not (Builtin.as_bool (eval env e)))
  | T.Neg e ->
      let cls, m = Prims.neg_method in
      let d = op_dict env node in
      let v = eval env e in
      apply (select_method ~cls:(Type.intern cls) d m []) (VRecord [ (Type.l_item, v) ])
  | T.Let (b, rest) ->
      let locals = eval_binding env b in
      eval { env with locals } rest
  | T.LetRec (bs, rest) ->
      let locals = eval_rec_bindings env bs in
      eval { env with locals } rest
  | T.Seq es ->
      let rec go = function
        | [] -> unit
        | [ last ] -> eval env last (* 末尾式は末尾呼び出しのまま *)
        | s :: rest ->
            let _ = eval env s in
            go rest
      in
      go es
  | T.Match (scrut, clauses) ->
      let v = eval env scrut in
      let rec try_clauses = function
        | [] -> runtime_error ("match のどの節にも一致しません: " ^ show v)
        | ((_, c) : T.clause) :: rest -> (
            match match_pat env.locals c.T.cl_pat v with
            | None -> try_clauses rest
            | Some locals -> (
                let env2 = { env with locals } in
                match c.T.cl_guard with
                (* ガードが偽なら次の節へ進む *)
                | Some g -> if Builtin.as_bool (eval env2 g) then eval env2 c.T.cl_body else try_clauses rest
                | None -> eval env2 c.T.cl_body))
      in
      try_clauses clauses
  | T.RecordEmpty -> unit
  | T.RecordExtend (rest, l, v) ->
      (* v が先、rest が後(sample.kel:278。AST のフィールドの順序と逆) *)
      let vv = eval env v in
      let vrest = eval env rest in
      record_extend vrest (Type.intern l) vv
  | T.RecordUpdate (r, l, v) ->
      let vr = eval env r in
      let vv = eval env v in
      record_update vr (Type.intern l) vv
  | T.RecordRestriction (r, l) -> record_restrict (eval env r) (Type.intern l)
  | T.RecordSelection (r, l) -> record_select (eval env r) (Type.intern l)
  | T.Perform (_, arg) -> (
      match Tree.get_resolved node with
      | Some (Tree.ROp op) ->
          let va = eval env arg in
          Effect.perform (Op (op, va))
      | _ -> bug "Perform が解決されていません")
  | T.Handle (body, clauses) -> eval_handle env body clauses
  | T.Resume arg ->
      (* この分岐で評価するのは、節本体の末尾の背骨の外にある resume だけである。
         背骨の上の resume は §14.9 の eval_clause_tail が処理する *)
      let r, v = take_resume env arg in
      (* この resume は末尾位置にない。再開した計算が、再開しない操作の節によって終わったときは、
         ハンドラの exnc がその節の本体を評価し終えており、その値がここに戻る *)
      Effect.Deep.continue r.r_k v
  | T.Run (_, body) -> eval env body (* 実行時には本体を評価するだけである。リージョンの安全性は型が保証する *)

(* ## 14.5 関数の適用

   関数は複数の引数を受け取って 1 つの値を返す。
   引数は 1 つのレコードにまとめて渡す。
   したがって適用は、引数レコードのフィールドを仮引数のパターンに順に束縛するだけである。

   引数の個数の不一致は、型検査に通ったプログラムでは起きない。
   引数の個数は矢印型の一部であり、
   型検査が閉じた `_item` 行の単一化として検査しているからである(sample.kel:190-191)。
   それでも個数の検査を残してある。
   プリミティブを経由した呼び出しや処理系のバグで壊れた引数が来たときに、
   `List.fold_left2` の `Invalid_argument` のような無関係な例外ではなく、
   個数の不一致として報告するためである。

   束縛を追加する元の環境を `c.c_env.locals`(定義時の環境)にすることで、静的スコープを実装している。
   呼び出し元の locals は混ざらない。 *)

and apply vf vargs =
  match vf with
  | VClosure c ->
      let fields = record_fields vargs in
      if List.length fields <> List.length c.c_params then
        runtime_error
          (Printf.sprintf "引数の個数が一致しません(%d 引数の関数に %d 個)" (List.length c.c_params) (List.length fields))
      else
        let locals =
          List.fold_left2 (fun locals p (_, v) -> bind_pat_exn locals p v) c.c_env.locals c.c_params fields
        in
        (* 本体は末尾位置(規約 1) *)
        eval { c.c_env with locals } c.c_body
  | VPrim p -> p.p_fn vargs
  | VDictAbs _ as v -> bug ("辞書を受け取る値を関数として適用しました(辞書の渡し忘れ): " ^ show v)
  | v -> runtime_error ("関数ではない値を適用しました: " ^ show v)

(* ## 14.6 辞書とメソッドの選択

   型検査が木に書いた証拠(第5章 §5.1b)から辞書を作り、メソッドを選ぶ。
   実行時の値のタグは調べない。
   辞書パラメータを持つ値(`VDictAbs`)には、
   その値を使う位置の `DUse` の証拠を評価して得た辞書の並びを渡す。
   メソッドの値は、`method_selector`(§14.11)が作る `VDictAbs` である。
   この値は辞書を受け取って関数を返し、その関数は、
   呼び出された時点でインスタンス表からメソッドを選ぶ。
   メソッドを選ぶ時点を呼び出しの時点にするのは、
   インスタンス宣言より前の位置で辞書を作るプログラムも、
   宣言の後に呼び出すなら動くようにするためである(§14.12)。
   セレクタのクラスと辞書のクラスが食い違うのは、辞書の渡し方の誤りなので、`bug` として報告する。 *)

and with_evidence env node v =
  match Tree.get_dict node with Tree.DUse hs -> apply_dicts v (List.map (fun h -> eval_ev env (Tree.EvHole h)) hs) | _ -> v

and apply_dicts v ds =
  match v with
  | VDictAbs da -> (
      match da.da_last with
      | Some (ds0, r) when List.length ds0 = List.length ds && List.for_all2 ( == ) ds0 ds -> r
      | _ ->
          let r = da.da_fn ds in
          da.da_last <- Some (ds, r);
          r)
  | _ -> bug ("辞書を受け取らない値に辞書を渡しました: " ^ show v)

and op_dict env node = match Tree.get_dict node with Tree.DUse [ h ] -> eval_ev env (Tree.EvHole h) | _ -> bug "演算子に証拠がありません"

and eval_ev env (ev : Tree.evidence) =
  match ev with
  | Tree.EvParam k -> (
      match DMap.find_opt k env.dicts with Some d -> d | None -> bug ("辞書パラメータが束縛されていません: " ^ dkey_name k))
  | Tree.EvInst (c, n, subs) -> VDict (DInst (c, n, List.map (eval_ev env) subs, ref []))
  | Tree.EvRecord fs -> VDict (DRecord (List.map (fun (l, e) -> (l, eval_ev env e)) fs))
  | Tree.EvVariant fs -> VDict (DVariant (List.map (fun (l, e) -> (l, eval_ev env e)) fs))
  | Tree.EvHole { Tree.h_sol = Some (Tree.EvParam _ as e); _ } -> eval_ev env e
  | Tree.EvHole h -> (
      match Hashtbl.find_opt closed_cache h.Tree.h_id with
      | Some d -> d
      | None -> (
          match h.Tree.h_sol with
          | Some e ->
              let d = eval_ev env e in
              if closed_ev e then Hashtbl.replace closed_cache h.Tree.h_id d;
              d
          | None -> VDict DPending))

(* 辞書 d からメソッド meth の実装を選ぶ。cls はセレクタのクラス、own はメソッド自身の辞書 *)
and select_method ~cls d meth own =
  match d with
  | VDict (DInst (c, _, _, _)) when c <> cls -> bug ("辞書のクラスが違います: " ^ Type.display_of c ^ " と " ^ Type.display_of cls)
  | VDict (DInst (_, _, _, cache)) when own = [] && List.mem_assoc meth !cache -> List.assoc meth !cache
  | VDict (DInst (c, n, ps, cache)) -> (
      let memo v =
        if own = [] then cache := (meth, v) :: !cache;
        v
      in
      memo
      @@
      match Hashtbl.find_opt instance_impls (c, n) with
      | Some ms -> ( match List.assoc_opt (Type.intern meth) ms with Some f -> f (ps @ own) | None -> bug ("メソッドがありません: " ^ meth))
      | None -> (
          match Builtin.builtin_method (Type.name_of c) (Type.name_of n) meth with
          | Some f -> VPrim { p_name = Type.name_of c ^ "." ^ meth; p_fn = f }
          | None ->
              (* 型検査はパス 1c でインスタンス表をそろえるので、宣言より前の位置での使用を受理する。
                 評価器は宣言を実行した順に表へ書き込むので、その時点ではまだ実装が表にない。
                 黙って続けず、実行時エラーにする *)
              if Decls.find_instance ~cls:c ~con:n <> None then
                runtime_error
                  (Type.display_of c ^ "[" ^ Type.display_of n
                 ^ "] のインスタンスは宣言より前の位置では使えません(実行はまだ実体を持ちません。インスタンス宣言を使用より前に置いてください)")
              else bug ("インスタンスがありません: " ^ Type.display_of c ^ "[" ^ Type.display_of n ^ "]")))
  | VDict (DRecord fs) ->
      if cls <> Type.intern "Eq" then bug "構造的な辞書を Eq 以外に使いました";
      VPrim { p_name = "Eq.eq"; p_fn = (fun args -> let a, b = Builtin.arg2 args in VBool (record_eq fs a b)) }
  | VDict (DVariant fs) ->
      if cls <> Type.intern "Eq" then bug "構造的な辞書を Eq 以外に使いました";
      VPrim { p_name = "Eq.eq"; p_fn = (fun args -> let a, b = Builtin.arg2 args in VBool (variant_eq fs a b)) }
  | VDict DPending -> runtime_error "型の決まっていない制約の辞書を使いました"
  | v -> bug ("辞書ではない値: " ^ show v)

(* ## 14.7 構造的等価

   `{p = 1, q = 2}` と `{q = 2, p = 1}` は同じ値である。
   行の型は最左一致で決まる一方、異なるラベルの間には順序がない。
   そのため、値のフィールドのリストを先頭から順に比べるのは誤りである。
   型検査が作った `EvRecord` は、閉じた行の型のラベルごとに、
   そのフィールドの型の `Eq` の辞書を持つ。
   左辺と右辺から、そのラベルの最も左のフィールドを取り出して取り除き、フィールドの辞書で比べる。
   最後に両辺が空になれば一致である。
   フィールドの型が名目的な型なら、その型のインスタンスの辞書で比べるので、
   ユーザが宣言した `Eq` を無視して値の構造を比べることはない。
   ヴァリアントは、まずラベルを比べ、同じなら行の中のそのラベルの辞書でペイロードを比べる。
   `Float64` の比較は組み込みの `eq` に任せるので、IEEE の意味論(NaN ≠ NaN)のとおりになる。 *)

and eq_with d x y = Builtin.as_bool (apply (select_method ~cls:(Type.intern "Eq") d "eq" []) (VRecord [ (Type.l_item, x); (Type.l_item, y) ]))

(* 閉じたレコード型の構造的な Eq。証拠のラベルの順(ラベル名のバイト列の昇順)にラベルを選び、
   両辺から最も左の同名のフィールドを取り出して、そのフィールドの辞書で比べる。
   異なるラベルの間の物理的な順序は、値によって違うことがある *)
and record_eq fs a b =
  match fs with
  | [] -> record_fields a = [] && record_fields b = []
  | (l, d) :: rest ->
      let x, a' = record_take a l in
      let y, b' = record_take b l in
      eq_with d x y && record_eq rest a' b'

and variant_eq fs a b =
  match (a, b) with
  | VVariant (l1, p1), VVariant (l2, p2) -> l1 = l2 && eq_with (List.assoc l1 fs) p1 p2
  | _ -> bug "variant_eq: ヴァリアントではない値"

(* ## 14.8 let と let rec

   `eval_binding_value` は、束縛に引数リストが付いていれば、右辺を評価せずにクロージャを作る。
   `let f(x) = …` の右辺は関数の本体であって、束縛の時点で評価する式ではない。

   `let rec` は、クロージャの生成、環境の構築、`c_env` のバックパッチの 3 段階で束縛する。
   相互再帰する関数は、自分たちを含む環境をキャプチャする必要がある。
   その環境はクロージャができあがるまで作れないので、
   クロージャを作った後で `c_env` を書き換えて循環を作る。
   第12章のクロージャのフィールドのうち `c_env` だけが mutable なのは、
   このバックパッチのためである。
   第12章には `resume` の `r_used` と `r_alive` という mutable なフィールドもあるが、
   これらは §14.9 のアフィン性と second-class の検査のためにある。

   右辺が関数でないときは実行時エラーにするが、この分岐には到達しない。
   `let rec x = x + 1` のように、型検査には通るのに実行すれば必ず実行時エラーになるプログラムは、
   elab が拒否するからである。

   トップレベルの `let rec`(§14.12)にバックパッチが不要なのは、
   globals が共有の可変な表で、名前を評価する時点で値を引くからである。 *)

and eval_binding_value_plain env ((_, b) : T.let_binding) =
  match b.T.lb_params with
  | Some ps -> VClosure { c_env = env; c_params = ps; c_body = b.T.lb_body }
  | None -> eval env b.T.lb_body

(* 辞書パラメータを持つ束縛は、辞書を受け取って束縛の値を評価する VDictAbs にする。
   値束縛の初期化式は、名前を使うたびに評価する(§14.6) *)
and eval_binding_value env bnode =
  match dict_params_of bnode with
  | [] -> eval_binding_value_plain env bnode
  | ks -> VDictAbs { da_last = None; da_name = "let"; da_arity = List.length ks; da_fn = (fun ds -> eval_binding_value_plain (bind_dicts env ks ds) bnode) }

and eval_binding env ((_, b) as bnode : T.let_binding) =
  let v = eval_binding_value env bnode in
  bind_pat_exn env.locals b.T.lb_name v

and eval_rec_bindings env (bs : T.let_binding list) =
  (* クロージャの生成 → 環境の構築 → c_env のバックパッチ。辞書パラメータを持つ束縛は、
     再帰群の環境をキャプチャし、辞書を受け取るたびにクロージャを作る VDictAbs にする。こちらはバックパッチしない *)
  let genv = ref env in
  let closures =
    List.map
      (fun (((_, b) as bnode) : T.let_binding) ->
        let name = match snd b.T.lb_name with T.PVar x -> x | _ -> runtime_error "let rec は名前束縛のみです" in
        let ps, body =
          match b.T.lb_params with
          | Some ps -> (ps, b.T.lb_body)
          | None -> (
              match snd b.T.lb_body with
              | T.Lambda { l_params; l_body } -> (l_params, l_body)
              | _ -> runtime_error "let rec の右辺は関数でなければなりません")
        in
        match dict_params_of bnode with
        | [] ->
            let c = { c_env = env; c_params = ps; c_body = body } in
            (name, VClosure c, Some c)
        | ks ->
            ( name,
              VDictAbs
                { da_last = None; da_name = name; da_arity = List.length ks; da_fn = (fun ds -> VClosure { c_env = bind_dicts !genv ks ds; c_params = ps; c_body = body }) },
              None ))
      bs
  in
  let locals = List.fold_left (fun locals (n, v, _) -> SMap.add n v locals) env.locals closures in
  genv := { env with locals };
  List.iter (function _, _, Some c -> c.c_env <- { env with locals } | _ -> ()) closures;
  locals

(* ## 14.9 ハンドラ

   1 つの `handle` 式は、1 つの `Effect.Deep.match_with` になる。
   節の種類は、elab が `resolved` に書いた値を読むだけで判別する。
   値は `ROp`、`RNeverOp`、`RReturnClause`、`RCancelClause` の 4 種類である。
   操作名の解決はここでは行わない。

   ### 起動ごとの inst

   `inst` は、Handle ノードを評価するたびに `new_oid ()` で採番する。
   ハンドラは、ソースに書かれた位置ではなく、起動(handle 式の 1 回の評価)ごとに区別する。
   AST のノードの id を流用すると、
   同じ handle 式が入れ子に起動する場面(再帰の中の handle や、`with_file` を 2 回呼んだ入れ子)で、
   内側のハンドラが、外側のハンドラ宛ての `Unwind` を自分宛てと取り違えて受け取ってしまう。
   取り違えると、handle 式が誤った値を返す。
   たとえば `#Err(boom)` を返すべきところで、`#Ok(#Err(boom))` を返す。

   ### Unwind のプロトコル

   `Unwind (inst, u)` は、例外として送る通知である。
   `inst` 番のハンドラに、handle 式全体の値をそこで決めるよう依頼する。
   `u` は 2 種類ある。
   再開する操作の節が resume を呼ばずに返した値 `UValue v` と、
   再開しない操作の節の本体を評価するクロージャ `UClause f` である。
   クロージャは、受け取ったハンドラの `exnc` が評価する(下の「再開しない操作の節」)。

   `UValue v` を送るときは、次の 4 段階で handle 式の値が決まる。

   1. 節が resume を呼ばずに `v` を返す。
   2. `discontinue k (Unwind (inst, UValue v))` で、捨てる継続の中にこの例外を送り込む。
   3. 中断していた計算が、内側から巻き戻る。
      途中のハンドラは、自分宛てでない `Unwind` を `exnc` で受け取り、
      `cancel` 節を実行してから再送出する。
   4. 最後に自分の `exnc` が `id = inst` を確認して `v` を返す。
      再開する操作の節では、これが handle 式の値になる。

   後始末が LIFO になるのは、この経路が fiber の入れ子を逆にたどるからである。
   評価器には、順序を管理するコードがない。
   仕様(sample.kel:572-585)は defer 構文を持たず、後始末をハンドラの cancel 節に書くと定めている。
   実装では、その規則がこの 4 段階に対応する。

   ### 3 つの経路

   再開する操作の節では、`effc` が返す関数の処理は、
   節の評価がどう終わったかによって 3 つの経路に分かれる。

   | 節の終わり方 | 処理 | 理由 |
   |---|---|---|
   | resume した後に値 `v` を返した | `v` を返す | 継続は消費済みで、返り値が handle 式の値になる |
   | resume せずに値 `v` を返した | `discontinue k (Unwind (inst, UValue v))` | 捨てた継続の中の cancel 節を実行する |
   | 例外 `ex` で脱出した | resume していなければ `discontinue k ex` | 継続の中と自分の、両方の cancel 節を実行する |

   resume せずに値 `v` を返した経路で `v` を直接返すと、
   捨てた継続の中にあるハンドラの `cancel` 節が実行されず、資源が漏れる。
   回帰テストは `test/eval.t` の effects.kel である。
   このテストは `with_res` を 2 つ重ね、外側の `try_` に継続を捨てさせる。
   出力は `cancel inner`、`cancel outer` の順になる。

   なお、ハンドラの節が自分の継続を捨てたとき、
   そのハンドラ自身の `return` 節と `cancel` 節は実行されない。
   評価器はその継続を `discontinue` で捨てるが、送り込んだ `Unwind` は、
   自分の `exnc` が handle 式の値として受け取る。
   これは意図した動作である。
   ここで cancel 節を実行すると、`try_` が正常に `#Err` を返すときにも後始末が実行されてしまう。
   資源を持つハンドラが自分で継続を捨てるなら、後始末はその節の中に書く。

   例外 `ex` で脱出した経路は、実装するときに書き忘れやすい。
   節の中で `???` に到達した場合も、実行時エラーが起きた場合も、
   外側のハンドラ宛ての `Unwind` が通過した場合も、
   `discontinue` が必要である。
   これを書き忘れると、捨てた継続の中の cancel 節も、自分の cancel 節も実行されない。
   `effc` の中で `discontinue` を使わずに `raise` した例外は、親のスタック上を伝播するので、
   自分の `exnc` を通らない。
   回帰テストは `test/eval.t` の holecancel.kel で、
   節本体が `???` でも内側の cancel 節が実行されることを確かめる。
   仕様(LangSpec.md §13.6)は、`resume` を呼ぶ前に節が脱出したとき、継続はまだ生きているので、
   そのハンドラ自身の `cancel` 節を実行すると定めている。
   `resume` が戻った後の脱出では、継続は消費済みなので、自分の `cancel` 節は実行されない。
   回帰テストは `test/eval.t` の clauseerr、clauseresumed、clausestop である。

   3 つの経路の規約は、第13章 §13.6 の最も外側のハンドラ(`with_runtime` の `Console.write`)にも当てはまる。

   ### 再開しない操作の節

   返り値の型が `Never` の操作(再開しない操作。第11章 §11.15)の節には、
   第11章が `resolved` に `RNeverOp` を書く。
   この節には `resume` を書けないので、継続を捨てる時点を節の評価の前に移せる。
   `effc` は、節を選んだ後、節の本体を評価するクロージャ `f` を作り、
   `discontinue k (Unwind (inst, UClause f))` を末尾呼び出しで呼んで継続を捨てる。
   捨てる継続の中のハンドラは、内側から外側の順に `cancel` 節を実行する。
   最後に自分の `exnc` が自分宛ての `Unwind` を受け取り、`f` を末尾呼び出しで呼ぶ。
   その値が handle 式の値になる。
   継続がないので、3 つの経路を判定する try ブロック(コードでは `match … with exception`)は不要である。
   本体の実行時エラーはそのまま `exnc` の外へ出て、自分の `exnc` には戻らないので、
   自分の `cancel` 節は実行されない。
   本体から操作を起こして外側のハンドラが継続を捨てるときも同じである。
   同じエフェクトの操作を起こし直す場合でも、別のエフェクトの再開しない操作でも、
   resume しない外側の節でも変わらない。

   送った `Unwind` が、捨てる継続の中の `cancel` 節の抑制(下の「cancel 節の実行文脈」)で止まることがある。
   `cancel` 節が再開しない操作を起こした場合である。
   このとき、自分宛ての `Unwind` は自分の `exnc` に届かず、`f` は呼ばれない。
   ハンドラの本体はそのまま続く。
   `discontinue` の値は、その本体の値か、先に始まっていた別の破棄で実行された節の値になる。
   ここで破棄とは、節が継続を捨て、その中に `Unwind` を送り込むことである。
   後者になるのは、破棄を進めているハンドラ自身が `cancel` 節からの操作を受け取ったときである。
   このときは、先の破棄の `Unwind` が自分の `exnc` に届き、そこで先の操作の節の本体が実行される。
   どの節の本体が実行されるかは、どの `Unwind` が `exnc` に届いたかだけで決まるので、
   破棄ごとの目印も、目印の照合も不要である。
   本体を `effc` の中で、`discontinue` が戻った後に評価する実装では、
   `discontinue` が先の破棄の値を持って戻ったときに、`Unwind` を抑制された節の本体を実行しないよう、
   破棄ごとの目印で区別しなければならない。
   回帰テストは `test/never_ops.t` の cancelnormal と cancelsame である。

   先の破棄で実行された節の値が、同じハンドラの再開する操作の節にある、
   末尾位置にない `resume` の返り値になることもある。
   捨てる継続の中の `cancel` 節がその操作を起こし、
   その節が末尾位置にない `resume` で再開した場合である。
   再開した計算が先の破棄で終わると、`exnc` が評価した節の値を持って `continue` が戻る。
   仕様(LangSpec.md §13.6)は、末尾位置にない `resume` で再開した計算の中では、
   節の値がその `resume` の返り値になると定めており、この動作はそれに従っている。
   回帰テストは `test/never_ops.t` の cancelresume である。
   §14.4 の `Resume` は返り値を調べないので、`continue` は末尾呼び出しである。

   `effc` は `discontinue` を末尾呼び出しで呼ぶので、
   `discontinue` が戻るのを待つフレームを残さない。
   `Unwind` を抑制されたハンドラは、破棄を進めているハンドラ自身のことも、別のハンドラのこともある。
   どちらの場合も、抑制の後にそのハンドラの本体の中で評価される節の本体(再試行の再帰など)は、
   抑制の回数が増えてもスタックを余分に使わない。
   回帰テストは `test/tail_calls.t` の retrycancel と retrycancelvia である。

   仕様(LangSpec.md §13.6)は、再開しない操作の節の本体をハンドラの外側で評価し、
   ハンドラ自身の `return` 節と `cancel` 節を実行しないと定めている。
   内側の `cancel` 節が節の本体より先に実行される順序は `test/never_ops.t` の order が、
   本体が末尾位置にあること(LangSpec.md §5.7)は `test/tail_calls.t` の retry が検査する。

   ### 末尾 resume

   3 つの経路を判定するには、節の評価を try ブロック(`match … with exception`)で囲む必要がある。
   この try ブロックの内側で `continue` を呼ぶと、`continue` が `effc` の末尾呼び出しでなくなる。
   継続の再開が末尾呼び出しでないと、perform のたびにスタックが伸びる。
   fiber のスタックは伸長できるので、既定の上限では Stack_overflow になりにくいが、
   perform の回数に比例してメモリを使い、大幅に遅くなる。
   Keleut は反復を再帰で書くので、perform を含むループは、
   節の末尾 `resume` が継続を末尾呼び出しで再開することを前提にしている。

   そこで、節本体の末尾の背骨にある `Resume` では、継続を try ブロックの内側で再開しない。
   背骨は、操作節の本体から末尾位置だけをたどった経路である。
   たどるのは、`Seq` の最後、`Let` と `LetRec` の本体の式、`Match` の節本体、
   `&&` と `||` の右辺、`Run` の本体である。
   `eval_clause_tail` は背骨をたどり、背骨の末尾の `Resume` に達したら、
   引数を評価して検査を済ませ、継続を再開せずに `Clause_resume v` を返す。
   背骨から外れた部分は `eval` で評価し、`Clause_value v` を返す。
   `effc` は、try ブロックを抜けた後の値の分岐で、
   `Clause_resume v` なら `continue k v` を末尾呼び出しで呼ぶ。
   `Clause_value v` なら、resume した後に値を返した経路か、resume せずに値を返した経路に進む。

   背骨は `Handle` と `Lambda` の中には入らない。
   内側の `handle` の本体にある `resume` は、内側のハンドラのフレームの中から呼ばれるので、
   末尾呼び出しにならない。
   内側の `handle` の return 節と、クロージャの本体には、
   外側の操作節の `resume` を書けない(第11章 §11.21、§11.24)。
   そのため、背骨の上の `Resume` は、どれも評価中の操作節の resume である。
   背骨の外の `Resume` は、`eval` の中で `continue` を呼び、その結果を値として返す。

   背骨に `Resume` のない節は、背骨をたどらずに `eval` で評価する。
   `eval_handle` は、ハンドラを起動するときに各節の背骨を 1 回ずつ調べ(`spine_has_resume`)、
   結果を節と対にして持つ。
   調べるコストは背骨の大きさ(`Match` のすべての節を含む)に比例し、perform のたびには掛からない。
   resume しない節の本体から深く再帰するプログラムでは、背骨をたどる関数が再帰の 1 段ごとに
   スタックを余分に使う。
   この区別がないと、同じスタックの上限で、スタックオーバーフローになる深さが浅くなる。
   この区別は操作節の単位なので、`match` の一方の節で resume し、他方の節で再帰する操作節では、
   再帰する節も背骨をたどり、スタックオーバーフローになる深さは浅いままである。

   節本体が構文上 `Resume` そのものである節は、さらに短い経路を通る。
   `case op(x) => resume(…)` の形の節は多く、プレリュードのハンドラ(`with_stdout`)もこの形である。
   短い経路も `take_resume` と同じく、引数を評価した後で `r_alive` と `r_used` を調べる。
   そのため、引数の中の入れ子の `resume` は継続を再開し、
   その後で外側の `resume` がアフィン性の検査で実行時エラーになる。
   これは背骨をたどる経路と同じ動作で、どちらの経路でも、エラーの前に継続の出力が見える。
   `test/resume_guard.t` が、短い経路でこの順序を検査する。
   `test/eval.t` の perf.kel(10 万回の println)が短い経路の回帰テストである。
   `test/tail_calls.t` は、スタックの上限を小さくしても、
   両方の経路でスタックが増えないことを検査する。

   短い経路も背骨をたどる経路も、3 つの経路の規約を守る。
   try ブロックで囲むのは、節の評価(短い経路では引数の評価)だけである。
   その中で例外が起きたら、resume していなければ `discontinue` する。
   囲まないと、`resume(???)` の形の節で、捨てた継続の cancel 節も自分の cancel 節も実行されない。
   回帰テストは `test/eval.t` の tailresume.kel である。
   再開した計算から出てきた例外は、
   try ブロックの外で呼んだ `continue` からそのまま `effc` の外へ出る。
   これは、継続を消費済みの節が例外を再送出する場合(例外で脱出した経路で、
   resume 済みのとき)と同じ結果である。

   `continue` は値の分岐、つまり例外を捕捉する範囲(trap)を抜けた後にあるので、
   末尾呼び出しのままである。
   OCaml は、値の分岐を trap の外に置いてコンパイルする。
   一方、`continue` を trap の内側に置くと、perform のたびにスタックが伸びる。

   `eval_handle` は `match_with` を末尾呼び出しで呼ぶ。
   `match_with` の結果を受け取ってから別の処理をする実装にすると、`return` 節の経路で
   `eval_handle` のフレームが再帰の 1 段ごとに残り、
   `test/tail_calls.t` の retc.kel が、
   スタックの上限を小さくしたときにスタックオーバーフローになる。
   再開しない操作の節の本体を、`match_with` の後ではなく `exnc` の末尾で評価するのは、
   このためである。

   ### アフィンな resume と second-class

   `r_used` はアフィン性(高々 1 回)を、`r_alive` は second-class(節の外へ持ち出さない)を、
   実行時に検査するためのフラグである。
   OCaml も 2 度目の `continue` で `Continuation_already_resumed` を投げるが、
   それでは Keleut のエラーの説明にならないので、先に評価器が検査して日本語のメッセージを出す。
   second-class の検査は 2 つあり、実行時の `r_alive` はその一方である。
   もう一方は、節本体の無名関数や関数束縛の本体に、
   その節の `resume` があれば拒否する構文上の検査で、
   elab にある。

   ### cancel 節の実行文脈

   `run_cancel` は `exnc` の中、つまり巻き戻しの途中で実行される。
   このとき有効なのは外側のハンドラだけで、
   `exnc` を実行しているハンドラ自身は、すでに外れている。
   `Effect.Deep.match_with` の `exnc` は、fiber を巻き戻した後に親のスタックで呼ばれるので、
   `run_cancel` の中で `Effect.perform` しても自分の `effc` には届かない。
   cancel 節から自分の操作を perform すると、外側にある同じエフェクトのハンドラに届く。
   第11章 §11.24 が cancel 節を外側のエフェクト行で型付けするのは、この動作に対応している。
   届いた先の節が resume せずに抜けると、`Unwind` が cancel 節を通過しようとする。
   `cancel` 節から再開しない操作を起こした場合に、
   その操作のハンドラが送る `Unwind` も同じである(上の「再開しない操作の節」)。
   `run_cancel` はそれを cancel 節の中の例外として抑制し(仕様 sample.kel §9 の抑制規則)、
   ログに記録するだけで外へは出さない。
   回帰テストは `test/eval.t` の cancelouter と cancelnores である。

   cancel 節の中の例外をすべて抑制してログに記録するのは、仕様(sample.kel:585)の規則である。
   既知の例外(`Runtime_error`、`Unwind`、`Sys_error`)は日本語のメッセージにし、
   それ以外の例外は `Printexc.to_string` で文字列にしてからログに渡す。

   `retc` と `run_cancel` が `cl_guard` を読まないのは、
   elab が return 節と cancel 節のガードを拒否するからである(第11章 §11.24)。

   ### 操作節の選択

   操作節はソースの順に試し、パターンが一致しないときもガードが偽のときも次の節へ進む。
   これは `Match`(§14.4)と同じ規則である。
   ガードは resume のない環境で評価する(ガードから継続は見えない。第11章 §11.24)。
   どの節も選ばれなかったときは、`discontinue` で実行時エラーを送る。
   elab は、各操作について、引数のパターンが必ず一致する節を 1 つ以上要求する(第11章 §11.24)。
   これは、ガードがなく、その節だけを持つ match が引数の並びについて網羅的になる節である。
   この検査に通っていれば、この分岐には到達しない。
   それでも、防御のためにこの分岐を残してある。
   `discontinue` を使わない `raise` にしないのは、3 つの経路の規約どおり、
   捨てた継続の cancel 節を実行するためである。

   Diktor は、どの節にも一致しなかった操作を外側のハンドラへ回す処理(re-perform)を実装していない。
   仕様にも、その規則はない(sample.kel:515)。
   機構としては実装できる。
   `effc` が返す関数は fiber の外で実行されるので、そこから `Effect.perform` すれば、
   自分を飛ばして外側のハンドラに届く。
   実装しないのは、型付けができないからである。
   handle の型付けは対象のエフェクト E を行から取り除くので(第11章 §11.24)、
   ガードが偽の `E.op` を外へ回すと、E を持たないエフェクト行の位置で E の操作が起き、
   型と実行が合わなくなる。
   仕様は関数型の行を書いたとおりに読み(sample.kel:475)、
   行にラベルを追加して暗黙に合わせる一般の規則を持たない。
   その例外である、使用時に行を開く規則(sample.kel:476)は、閉じた行の関数を、
   ラベルの多い行の位置で使えるようにするだけで、
   行からラベルを取り除くことはない。
   そのため、E を取り除く型付けと、E の操作を外へ回す実行を両立させる手段がない。 *)

(* resume の引数を評価し、アフィン性と second-class の検査を済ませて、継続を消費済みにする。
   継続の再開は呼び出し元が行う。
   引数を先に評価するので、引数の評価中に例外が起きたとき、引数の中の入れ子の resume が
   継続を再開していなければ、resume は未消費のまま、節が例外で脱出した経路(§14.9)に進む。
   再開済みなら、呼び出し元は例外をそのまま再送出する。
   先に消費済みにしてから引数を評価すると、引数が例外で脱出したときに、
   呼び出し元が継続を再開済みと判断し、再開していない継続を捨てなくなる *)
and take_resume env arg =
  match env.resume with
  | None -> runtime_error "resume は操作節の中でのみ使えます"
  | Some r ->
      let v = match arg with Some e -> eval env e | None -> unit in
      if not r.r_alive then runtime_error "resume を節の外で呼び出しました(second-class)"
      else if r.r_used then runtime_error "resume は高々1回しか呼べません(アフィン)"
      else (
        r.r_used <- true;
        (r, v))

(* 操作節の本体を、末尾の背骨に沿って評価する(§14.9)。
   背骨は、操作節の本体から末尾位置だけをたどった経路である。
   たどるのは、`Seq` の最後、`Let` と `LetRec` の本体の式、`Match` の節本体、
   `&&` と `||` の右辺、`Run` の本体である。
   それ以外のノードは `eval` で評価し、結果を `Clause_value` で返す。
   `Handle` と `Lambda` の中には入らないので、背骨の上の `Resume` は、
   どれもこの節の resume である *)
and eval_clause_tail env ((_, e) as node : T.exp) : clause_end =
  match e with
  | T.Resume arg ->
      let _, v = take_resume env arg in
      Clause_resume v
  | T.Seq es ->
      let rec go = function
        | [] -> Clause_value unit
        | [ last ] -> eval_clause_tail env last
        | s :: rest ->
            let _ = eval env s in
            go rest
      in
      go es
  | T.Let (b, rest) ->
      let locals = eval_binding env b in
      eval_clause_tail { env with locals } rest
  | T.LetRec (bs, rest) ->
      let locals = eval_rec_bindings env bs in
      eval_clause_tail { env with locals } rest
  | T.Match (scrut, clauses) ->
      (* 節の選び方は §14.4 の Match と同じである *)
      let v = eval env scrut in
      let rec try_clauses = function
        | [] -> runtime_error ("match のどの節にも一致しません: " ^ show v)
        | ((_, c) : T.clause) :: rest -> (
            match match_pat env.locals c.T.cl_pat v with
            | None -> try_clauses rest
            | Some locals -> (
                let env2 = { env with locals } in
                match c.T.cl_guard with
                | Some g ->
                    if Builtin.as_bool (eval env2 g) then eval_clause_tail env2 c.T.cl_body else try_clauses rest
                | None -> eval_clause_tail env2 c.T.cl_body))
      in
      try_clauses clauses
  | T.BinOp (l, And, r) -> if Builtin.as_bool (eval env l) then eval_clause_tail env r else Clause_value (VBool false)
  | T.BinOp (l, Or, r) -> if Builtin.as_bool (eval env l) then Clause_value (VBool true) else eval_clause_tail env r
  | T.Run (_, body) -> eval_clause_tail env body
  | _ -> Clause_value (eval env node)

(* 節本体の末尾の背骨に `Resume` があれば真を返す。背骨の定義は `eval_clause_tail` と同じである *)
and spine_has_resume ((_, e) : T.exp) =
  match e with
  | T.Resume _ -> true
  | T.Seq es -> ( match List.rev es with last :: _ -> spine_has_resume last | [] -> false)
  | T.Let (_, rest) | T.LetRec (_, rest) -> spine_has_resume rest
  | T.Match (_, clauses) -> List.exists (fun ((_, c) : T.clause) -> spine_has_resume c.T.cl_body) clauses
  | T.BinOp (_, (And | Or), r) -> spine_has_resume r
  | T.Run (_, body) -> spine_has_resume body
  | _ -> false

and eval_handle env body clauses =
  (* inst は Handle ノードを評価するたびに採番する。同じ handle 式が入れ子に起動したときに、
     内側のハンドラが、外側のハンドラ宛ての Unwind を自分宛てと取り違えないようにするためである *)
  let inst = new_oid () in
  let op_clauses =
    List.filter_map
      (fun (cl : T.clause) ->
        match Tree.get_resolved cl with
        | Some (Tree.ROp op) -> Some (op, (cl, `Resumable (spine_has_resume (snd cl).T.cl_body)))
        | Some (Tree.RNeverOp op) -> Some (op, (cl, `Never))
        | _ -> None)
      clauses
  in
  let ret_clause = List.find_opt (fun cl -> Tree.get_resolved cl = Some Tree.RReturnClause) clauses in
  let cancel_clause = List.find_opt (fun cl -> Tree.get_resolved cl = Some Tree.RCancelClause) clauses in
  let run_cancel () =
    match cancel_clause with
    | None -> ()
    | Some (_, c) -> (
        (* cancel 節の中の例外は抑制してログに記録する(sample.kel:585) *)
        try ignore (eval { env with resume = None } c.T.cl_body)
        with
        | Runtime_error msg -> !cancel_log msg
        | Unwind _ -> !cancel_log "cancel 節から操作の巻き戻しで脱出しようとしました"
        | Sys_error msg -> !cancel_log ("標準出力に書き出せません: " ^ msg)
        | ex -> !cancel_log (Printexc.to_string ex))
  in
  let clause_arg_pats (c : T.clause') =
    match snd c.T.cl_pat with T.PCtor (_, aps) -> List.map (fun (ap : T.ctor_arg_pat) -> ap.T.cap_pat) aps | _ -> []
  in
  Effect.Deep.match_with (fun () -> eval env body) ()
    {
      retc =
        (fun v ->
          (* return 節は親のスタック上で実行される *)
          match ret_clause with
          | None -> v
          | Some (_, c) ->
              let pat = match clause_arg_pats c with [ p ] -> p | _ -> bug "return 節のパターン" in
              let locals = bind_pat_exn env.locals pat v in
              eval { env with locals; resume = None } c.T.cl_body);
      exnc =
        (fun ex ->
          match ex with
          (* 自分宛ての巻き戻しである。再開する操作の節の値はそのまま返し、再開しない操作の
             節の本体は、ここから末尾呼び出しで評価する。どちらも handle 式の値になる *)
          | Unwind (id, UValue v) when id = inst -> v
          | Unwind (id, UClause f) when id = inst -> f ()
          | ex ->
              (* 外側のハンドラ宛ての巻き戻しか、実行時エラーが通過する。cancel 節を実行してから再送出する *)
              run_cancel ();
              raise ex);
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Op (op, args) -> (
              match List.filter (fun (o, _) -> o = op) op_clauses with
              | [] -> None (* 自分の操作でなければ外側のハンドラへ進む *)
              | cands ->
                  Some
                    (fun (k : (a, _) Effect.Deep.continuation) ->
                      let fields = record_fields args in
                      let rec bind locals ps fs =
                        match (ps, fs) with
                        | [], [] -> Some locals
                        | p :: ps, (_, v) :: fs -> (
                            match match_pat locals p v with Some locals -> bind locals ps fs | None -> None)
                        | _ -> bug "操作節の引数の個数が合いません"
                      in
                      (* 節をソースの順に試す。パターンが一致しないときもガードが偽のときも
                         次の節へ進む(§14.4 の Match と同じ規則)。ガードは resume のない環境で
                         評価するので、ガードから継続は見えない *)
                      let rec select = function
                        | [] -> None
                        | (_, (((_, c) : T.clause), tail)) :: rest -> (
                            match bind env.locals (clause_arg_pats c) fields with
                            | None -> select rest
                            | Some locals -> (
                                match c.T.cl_guard with
                                | None -> Some (locals, c, tail)
                                | Some g ->
                                    if Builtin.as_bool (eval { env with locals; resume = None } g) then
                                      Some (locals, c, tail)
                                    else select rest))
                      in
                      match select cands with
                      (* 節の選択(引数の照合とガードの評価)も try ブロックの中で行う。ガードで
                         起きた例外も、ガードを通過する外側のハンドラ宛ての Unwind も、
                         3 つの経路の規約どおり discontinue で継続に送る。discontinue を使わずに
                         raise した例外は fiber に届かないので、捨てた継続の cancel 節も
                         自分の cancel 節も実行されない *)
                      | exception ex -> Effect.Deep.discontinue k ex
                      | None ->
                          (* どの節も選ばれなかった。elab は各操作に、ガードがなく、引数のパターンが
                             必ず一致する節を 1 つ以上要求するので(第11章 §11.24)、その検査に通っていれば到達しない。
                             防御のために残した分岐である。3 つの経路の規約どおり、raise ではなく
                             discontinue を使い、捨てた継続の cancel 節を実行する *)
                          Effect.Deep.discontinue k
                            (Runtime_error ("handle のどの節にも一致しません: " ^ Type.display_of op ^ show args))
                      | Some (locals, c, `Never) ->
                          (* 再開しない操作の節である。節の本体を評価するクロージャを Unwind に入れ、
                             discontinue を末尾呼び出しで呼んで継続を捨てる。捨てた継続の中の
                             cancel 節が実行された後、自分の exnc がクロージャを受け取って本体を
                             評価する。継続がないので、本体の例外に備える try ブロックは不要で、
                             自分の cancel 節も実行されない。送った Unwind を cancel 節が抑制した
                             ときは、Unwind は exnc に届かず、本体は評価されない。
                             discontinue を末尾呼び出しで呼ぶので、この関数のフレームは残らない *)
                          Effect.Deep.discontinue k
                            (Unwind (inst, UClause (fun () -> eval { env with locals; resume = None } c.T.cl_body)))
                      | Some (locals, c, `Resumable tail) -> (
                          match snd c.T.cl_body with
                          | T.Resume arg -> (
                              (* 節本体が resume そのものである節の短い経路(§14.9)。try ブロックで
                                 囲むのは引数の評価だけで、continue は値の分岐(try ブロックを
                                 抜けた後)にあるので、継続を末尾呼び出しで再開する。検査の順序は
                                 take_resume と同じで、引数を評価した後で r_alive と r_used を調べ、
                                 それから r_used を true にする。引数の中の入れ子の resume は継続を
                                 再開し、その後で外側の resume がアフィン性の検査で実行時エラーに
                                 なる。引数が例外で脱出したときは、背骨をたどる経路と同じく、
                                 resume していなければ discontinue して、捨てた継続の cancel 節を
                                 実行する。引数の中の resume が k を消費済みなら、例外をそのまま
                                 再送出する *)
                              let r = { r_k = k; r_used = false; r_alive = true } in
                              match arg with
                              | None ->
                                  r.r_used <- true;
                                  r.r_alive <- false;
                                  Effect.Deep.continue k unit
                              | Some e -> (
                                  match
                                    let v = eval { env with locals; resume = Some r } e in
                                    if not r.r_alive then runtime_error "resume を節の外で呼び出しました(second-class)"
                                    else if r.r_used then runtime_error "resume は高々1回しか呼べません(アフィン)"
                                    else (
                                      r.r_used <- true;
                                      v)
                                  with
                                  | v ->
                                      r.r_alive <- false;
                                      Effect.Deep.continue k v
                                  | exception ex ->
                                      r.r_alive <- false;
                                      if r.r_used then raise ex else Effect.Deep.discontinue k ex))
                          | _ when not tail -> (
                              (* 背骨に resume のない節は、背骨をたどらずに評価する *)
                              let r = { r_k = k; r_used = false; r_alive = true } in
                              match eval { env with locals; resume = Some r } c.T.cl_body with
                              | v ->
                                  r.r_alive <- false;
                                  if r.r_used then v else Effect.Deep.discontinue k (Unwind (inst, UValue v))
                              | exception ex ->
                                  r.r_alive <- false;
                                  if r.r_used then raise ex else Effect.Deep.discontinue k ex)
                          | _ -> (
                              let r = { r_k = k; r_used = false; r_alive = true } in
                              match eval_clause_tail { env with locals; resume = Some r } c.T.cl_body with
                              | Clause_resume v ->
                                  (* 背骨の末尾の resume である。continue は値の分岐(try ブロックを
                                     抜けた後)にあるので、継続を末尾呼び出しで再開する *)
                                  r.r_alive <- false;
                                  Effect.Deep.continue k v
                              | Clause_value v ->
                                  r.r_alive <- false;
                                  (* resume していなければ、Unwind を送って継続を巻き戻し、
                                     自分の exnc で v を受け取る *)
                                  if r.r_used then v else Effect.Deep.discontinue k (Unwind (inst, UValue v))
                              | exception ex ->
                                  (* 節が例外で脱出したときも、resume していなければ
                                     discontinue して、捨てた継続の中の cancel 節を実行する。
                                     これを省くと資源が漏れる *)
                                  r.r_alive <- false;
                                  if r.r_used then raise ex else Effect.Deep.discontinue k ex))))
          | _ -> None);
    }

(* ## 14.10 組み込み値

   `Ref` は OCaml の `ref` で、`Array` と `MutableArray` はどちらも OCaml の配列である。
   リージョンの安全性(`run h { … }` の外へ持ち出せないこと)は、
   第11章のスコーレム定数とレベルが型で保証する。
   そのため、実行時には値を包むことも検査することもない。
   §14.4 の `Run` が本体を評価するだけなのも、同じ理由である。

   値の表現だけは 2 つに分けている。
   `VArray` が不変配列、`VMutArray` が可変配列で、内容はどちらも `Value.t array` である。
   分けているのは表示(§12.7)のためで、実行時の動作が違うからではない。
   どのインスタンスのメソッドで表示するかは型検査が型から決めるので(§14.6)、
   値のコンストラクタの違いは、組み込みの `show` が可変配列を不変配列と区別して表示するためだけに使う。
   `type instance[A: Show] Show[Array[_]]` と `type instance[H, A: Show] Show[MutableArray[_, _]]` は、
   どちらも宣言も使用もできる。
   リージョンの型パラメータにも制約を付けた前提 `[H: Show, A: Show]` を持つインスタンスは、
   宣言はできるが、使う位置で型エラーになる。
   `run` のスコーレム定数には制約がないからである。

   `MutableArray.freeze` はコピーを作る。
   仕様(sample.kel §10)が要求するのは、freeze の後に元の可変配列へ書き込んでも、
   取り出した配列は変わらない、という観測できる動作だけである。
   コピーするかどうかは実装が選ぶ、と仕様は明記している。
   配列を共有したままこの動作を守るには、線形性か copy-on-write が必要である。
   Diktor はどちらも持たないので、単純にコピーする。
   コピーは浅いので、要素が可変配列である配列では、コピーと元の配列が同じ要素を共有し、
   リージョンの内側ではその共有を観測できる。
   しかし、そうした配列は要素の型に `h` を持つので、リージョンの外へは持ち出せない。

   一方、配列の範囲検査は実行時に行う。
   配列の型は長さを持たないので、型検査では範囲を保証できない。
   負の長さの `MutableArray.new` も、同じ理由で実行時に拒否する。

   `Array.each` は、渡された関数を `apply` で呼ぶ。
   その関数の中で `perform` が起きても、エフェクトは外側のハンドラまで届く。
   OCaml のエフェクトは、間にある `Array.iter` のスタックフレームを越えて伝わるからである。
   エフェクトが組み込み関数を越えて伝わるようにするための特別な仕組みは不要である。 *)

let register_builtin_values globals =
  let reg n f = Hashtbl.replace globals (Tree.GBuiltin n) (VPrim { p_name = n; p_fn = f }) in
  reg "Ref.new" (fun args -> VRef (ref (Builtin.arg1 args)));
  reg "Ref.get" (fun args -> match Builtin.arg1 args with VRef r -> !r | v -> runtime_error ("Ref ではありません: " ^ show v));
  reg "Ref.set" (fun args ->
      match Builtin.arg_values args with
      | [ VRef r; v ] ->
          r := v;
          unit
      | _ -> runtime_error "Ref.set の引数が不正です");
  reg "Array.length" (fun args ->
      match Builtin.arg1 args with VArray a -> VInt32 (Int32.of_int (Array.length a)) | _ -> runtime_error "Array ではありません");
  reg "Array.get" (fun args ->
      match Builtin.arg_values args with
      | [ VArray a; VInt32 i ] ->
          let i = Int32.to_int i in
          (* 配列の型は長さを持たないので、範囲は実行時に検査する *)
          if i < 0 || i >= Array.length a then runtime_error "配列の範囲外です" else a.(i)
      | _ -> runtime_error "Array.get の引数が不正です");
  reg "Array.each" (fun args ->
      match Builtin.arg_values args with
      | [ VArray a; f ] ->
          Array.iter (fun x -> ignore (apply f (VRecord [ (Type.l_item, x) ]))) a;
          unit
      | _ -> runtime_error "Array.each の引数が不正です");
  reg "MutableArray.new" (fun args ->
      match Builtin.arg_values args with
      | [ VInt32 n; init ] ->
          if Int32.to_int n < 0 then runtime_error "MutableArray.new: 長さが負です"
          else VMutArray (Array.make (Int32.to_int n) init)
      | _ -> runtime_error "MutableArray.new の引数が不正です");
  reg "MutableArray.length" (fun args ->
      match Builtin.arg1 args with
      | VMutArray a -> VInt32 (Int32.of_int (Array.length a))
      | _ -> runtime_error "MutableArray ではありません");
  reg "MutableArray.get" (fun args ->
      match Builtin.arg_values args with
      | [ VMutArray a; VInt32 i ] ->
          let i = Int32.to_int i in
          if i < 0 || i >= Array.length a then runtime_error "配列の範囲外です" else a.(i)
      | _ -> runtime_error "MutableArray.get の引数が不正です");
  reg "MutableArray.set" (fun args ->
      match Builtin.arg_values args with
      | [ VMutArray a; VInt32 i; v ] ->
          let i = Int32.to_int i in
          if i < 0 || i >= Array.length a then runtime_error "配列の範囲外です"
          else (
            a.(i) <- v;
            unit)
      | _ -> runtime_error "MutableArray.set の引数が不正です");
  (* freeze はコピーを作る。仕様(sample.kel §10)は、freeze の後に元の可変配列へ書き込んでも、
     取り出した配列は変わらないと定めている。配列を共有しない最も単純な方法で、これを満たす *)
  reg "MutableArray.freeze" (fun args ->
      match Builtin.arg1 args with
      | VMutArray a -> VArray (Array.copy a)
      | _ -> runtime_error "MutableArray ではありません");
  (* pinned は、渡された関数を呼ぶだけの関数として実装する。Blocking について仕様が定める
     観測できる動作は、並列度を減らさないことと、キャンセルポイントにならないことの 2 つである。
     Diktor はタスクを 1 つしか持たず、キャンセルポイントも持たないので、
     関数を呼ぶだけでどちらも満たす。スケジューラを持たないので、
     タスクを専用のスレッドに固定することもしない。Blocking はトップレベルに残せるので
     (sample.kel §12)、pinned を通さないプログラムも実行できる。Blocking は操作を持たないので、
     その場合もランタイムが受け取る操作はない *)
  reg "pinned" (fun args -> apply (Builtin.arg1 args) unit)

(* ## 14.11 クラスメソッドの識別子参照

   `eq(a, b)` や `show(x)` のようなメソッドの識別子参照のために、
   辞書を受け取ってメソッドを選ぶ値(`method_selector`)を globals に置く。
   メソッドを選ぶのは、globals に置いた時点ではなく、
   辞書を受け取った関数が呼ばれた時点である(§14.6)。
   そのため、メソッドを参照する関数をインスタンス宣言より前に定義しても、
   インスタンス宣言より後に呼べば、そのインスタンスが使われる。
   インスタンス宣言より前に呼び出しを評価すると、§14.6 の実行時エラーになる。

   この値は、メソッドごとに 1 個だけ、キー `GMethod Cls.m` で globals に置く。
   非修飾名 `map` と修飾名 `Functor.map` のどちらで書いても、
   elab が同じ参照先を `resolved` に書く(第11章 §11.33)。
   非修飾名がどのクラスのメソッドを指すか、あるいはどのトップレベルの値を指すかは、elab が決める。
   パス 1b は、クラスメソッドとトップレベルの値のうち、その名前を先に宣言したほうを選ぶ。
   クラスより後に置いた同名のトップレベルの let は、その let より後のコードでメソッドの名前を隠す。
   ここでの登録の順序は関係しない。
   クラスメソッドと同名のトップレベル束縛は、束縛ノードのキー(`GDecl`)で別に置かれるので、
   この値を上書きしない。

   下の実装は、走査の結果をクラス名でソートしてから登録する。
   キーはクラスごとに別なので登録の順序は結果を変えないが、
   ハッシュ表の走査の順序に由来する非決定性を残さないために、念のためソートしている。 *)

(* クラスメソッドを識別子で参照したときの値を作る。この値は辞書の並びを受け取り、
   クラスパラメータの位置の辞書とメソッド自身の辞書に分け、呼ばれた時点でメソッドを選ぶ関数を返す。
   クラスパラメータの位置は、型スキームの制約の正準順の中で求める *)
let method_selector (ci : Decls.class_info) (m, scheme) =
  let cls_name = Type.name_of ci.Decls.ci_name in
  let cs = Unify.constraints_of scheme in
  let rec index j = function
    | [] -> bug ("メソッドの型にクラスパラメータがありません: " ^ m)
    | ((i : Type.var_info), c) :: rest -> if i.Type.vid = ci.Decls.ci_param.Type.vid && c = ci.Decls.ci_name then j else index (j + 1) rest
  in
  let idx = index 0 cs in
  VDictAbs
    {
      da_last = None;
      da_name = cls_name ^ "." ^ m;
      da_arity = List.length cs;
      da_fn =
        (fun ds ->
          let d = List.nth ds idx in
          let own = List.filteri (fun j _ -> j <> idx) ds in
          VPrim { p_name = cls_name ^ "." ^ m; p_fn = (fun args -> apply (select_method ~cls:ci.Decls.ci_name d m own) args) });
    }

let register_class_methods globals =
  Hashtbl.fold (fun _ ci acc -> ci :: acc) Decls.classes []
  |> List.sort (fun (a : Decls.class_info) b -> compare (Type.name_of a.Decls.ci_name) (Type.name_of b.Decls.ci_name))
  |> List.iter (fun (ci : Decls.class_info) ->
         let cls_name = Type.name_of ci.Decls.ci_name in
         List.iter
           (fun ((m, _) as ms) -> Hashtbl.replace globals (Tree.GMethod (cls_name ^ "." ^ m)) (method_selector ci ms))
           ci.Decls.ci_methods)

(* ## 14.12 宣言の実行

   トップレベルの `let` と `let rec` は、globals に直接置く。
   バックパッチが不要な理由は、§14.8 で述べた。

   本章でインスタンス表(`instance_impls`)に書き込むのは、`type instance` の処理だけである。
   この処理は、インスタンスの対象の型の名前を別名表で引く。
   第11章の `flatten_modules` は、型検査の前に module を平坦化し、
   `module BigInt { newtype BigInt … }` の型の名前を `BigInt.BigInt` に変える。
   インスタンスの対象の型として書かれた非修飾名をそのままキーにすると、
   宣言したインスタンスが実行時に見つからない。
   そこで `Decls.resolve_con` に通して、elab と同じ名前にそろえる。
   別名は module ごとと単位ごとのスコープを持つ。
   そのため `exec_decl` は、最初に `Decls.with_decl_scope` で、
   宣言した module と単位を `Decls.current_module` と `Decls.current_unit` に設定してから引く。
   elab も同じ `with_decl_scope` を使う。
   回帰テストは `test/verify_fixes.t` の modinst.kel である。
   組み込みのインスタンスと同じ `(cls, con)` を持つ宣言は、elab が宣言の時点で拒否するので、
   ここに来る宣言が組み込みのインスタンスを差し替えることはない。

   `extern` は、実装がなければ、呼ばれた時点で実行時エラーになる prim を登録する。
   宣言だけして呼ばないプログラムを実行できるようにするためである。
   登録済みの名前の extern を再宣言すると、elab が拒否する。
   実装と合わない型で宣言し直せないようにするためである(登録表が保護する範囲は第6章 §6.2)。

   `DLet` と `DExtern` の分岐は、束縛した値を、
   束縛ノードと名前の組のキー(`GDecl`)で globals に置く。
   同名の束縛を再び宣言しても、束縛ノードが違うのでキーも違い、前の束縛は残る。
   それより前に作られたクロージャは、elab が書いた前の束縛のキーで引くので、
   定義した時点の束縛を参照する。

   `type`、`newtype`、`effect`、`type class` は、実行時には何もしない。
   値を作らない宣言で、必要な情報は第6章の表に入っている。
   `module` は、平坦化を済ませていればここには来ない。 *)

(* globals とインスタンス表への書き込みを記録する(§14.15)。journaling が真の間、
   書き込む前の内容に戻すクロージャを journal に追加する *)
let journaling = ref false

let journal : (unit -> unit) list ref = ref []

let jreplace t k v =
  (if !journaling then
     let old = Hashtbl.find_opt t k in
     journal := (fun () -> match old with Some o -> Hashtbl.replace t k o | None -> Hashtbl.remove t k) :: !journal);
  Hashtbl.replace t k v

(* トップレベルの束縛を、参照先のキー(`Tree.gref`)で globals に置く。キーは束縛ノードごとに別なので、
   同名の再束縛も前の束縛を上書きしない *)
let bind_globals env names_values =
  List.iter (fun (g, v) -> jreplace env.globals g v) names_values;
  env

let exec_decl env ((_, d) as node : T.decl) =
  (* インスタンスの対象の型の名前は、宣言した module と単位のスコープで別名表を引いて解決する(resolve_con)。
     そのために、Decls の current_module と current_unit を一時的に設定する *)
  Decls.with_decl_scope (Tree.oid_of node) @@ fun () ->
  match d with
  | T.DLet ((_, b) as bnode) ->
      let v = eval_binding_value env bnode in
      let bound = bind_pat_exn SMap.empty b.T.lb_name v in
      bind_globals env (List.map (fun (n, v) -> (Tree.GDecl (Tree.oid_of bnode, n), v)) (SMap.bindings bound))
  | T.DLetRec bs ->
      (* 再帰群のクロージャは globals を共有し、自己参照と相互参照は呼び出し時に参照先のキーで引くので、
         バックパッチは不要である(§14.8) *)
      List.iter
        (fun ((_, b) as bnode : T.let_binding) ->
          let x = match snd b.T.lb_name with T.PVar x -> x | _ -> runtime_error "let rec は名前束縛のみです" in
          jreplace env.globals (Tree.GDecl (Tree.oid_of bnode, x)) (eval_binding_value env bnode))
        bs;
      env
  | T.DExp e ->
      (* 辞書パラメータを持つ式文(制約付きで一般化した構文上の値)は、評価しない *)
      (match Tree.get_dict node with Tree.DAbs _ -> () | _ -> ignore (eval env e));
      env
  | T.DInstance i ->
      let cls = Decls.resolve_class (Type.intern i.T.ins_class) in
      (* module の平坦化で作った別名を解決する(BigInt.BigInt など)。組み込みのインスタンスと同じキーの
         ユーザの宣言は elab が拒否するので、ここに来る宣言は組み込みのインスタンスを差し替えない *)
      let con =
        match i.T.ins_args with
        | [ (_, T.EIdent (LongId comps)) ] -> Decls.resolve_con (Type.intern (String.concat "." comps))
        | [ (_, T.EApply ((_, T.EIdent (LongId comps)), _)) ] -> Decls.resolve_con (Type.intern (String.concat "." comps))
        | _ -> bug "インスタンス頭が解決できません"
      in
      (* 各メソッドは、前提の辞書とメソッド自身の辞書の並びを受け取って実装を返す関数にする。
         前提のキーとメソッドのキーに、受け取った辞書を対応づけた環境で、メソッドの束縛を評価する。
         実装の型が辞書パラメータを持つときは、評価した値に adapter の証拠から作った辞書を渡す。
         前提もメソッド自身の制約もないメソッドは、宣言を実行するときに 1 回だけ評価する *)
      let pk = match Tree.get_dict node with Tree.DInstance ks -> ks | _ -> [] in
      let np = List.length pk in
      let method_fn bnode eval_in =
        let mk, adapter = match Tree.get_dict bnode with Tree.DMethod (_, mk, ad) -> (mk, ad) | _ -> ([], []) in
        let build ds =
          let pds = List.filteri (fun j _ -> j < np) ds and mds = List.filteri (fun j _ -> j >= np) ds in
          let env' = bind_dicts (bind_dicts env pk pds) mk mds in
          let v = eval_in env' in
          if adapter = [] then v else apply_dicts v (List.map (fun h -> eval_ev env' (Tree.EvHole h)) adapter)
        in
        if pk = [] && mk = [] then (
          let v = build [] in
          fun _ -> v)
        else build
      in
      let methods =
        List.concat_map
          (fun ((_, d) : T.decl) ->
            match d with
            | T.DLet ((_, b) as bnode) -> (
                match snd b.T.lb_name with
                | T.PVar x -> [ (Type.intern x, method_fn bnode (fun env' -> eval_binding_value env' bnode)) ]
                | _ -> [])
            | T.DLetRec bs ->
                List.filter_map
                  (fun (((_, b) as bnode) : T.let_binding) ->
                    match snd b.T.lb_name with
                    | T.PVar x -> Some (Type.intern x, method_fn bnode (fun env' -> SMap.find x (eval_rec_bindings env' bs)))
                    | _ -> None)
                  bs
            | _ -> [])
          i.T.ins_body
      in
      jreplace instance_impls (cls, con) methods;
      env
  | T.DExtern ex ->
      let impl =
        (* 宣言の ABI で実装の表を選ぶ。実装を引くキーは、修飾しない名前 ex_prim である。
           globals に登録するキーは、宣言ノードの oid と修飾名 ex_name を持つ GDecl である *)
        match Builtin.find_extern ~abi:ex.T.ex_abi ex.T.ex_prim with
        | Some f -> f
        (* 実装がなくても宣言は受理し、呼ばれた時点で実行時エラーにする。表を引いたキーは ex_prim なので、
           修飾名と違うときは、メッセージに両方を入れる *)
        | None ->
            fun _ ->
              runtime_error
                ("未実装のプリミティブ: " ^ Type.display ex.T.ex_name
                ^ if ex.T.ex_name = ex.T.ex_prim then "" else "(実装名 " ^ ex.T.ex_prim ^ " が見つかりません)")
      in
      (* 制約付きの型パラメータを持つ extern は、辞書を受け取って捨てる。実装は OCaml の関数で、辞書を使わない *)
      let prim = VPrim { p_name = ex.T.ex_name; p_fn = impl } in
      let v =
        match Tree.get_dict node with
        | Tree.DAbs (_ :: _ as ks) -> VDictAbs { da_last = None; da_name = ex.T.ex_name; da_arity = List.length ks; da_fn = (fun _ -> prim) }
        | _ -> prim
      in
      bind_globals env [ (Tree.GDecl (Tree.oid_of node, ex.T.ex_name), v) ]
  | T.DType _ | T.DNewtype _ | T.DEffect _ | T.DClass _ -> env
  | T.DModule _ ->
      (* 平坦化を済ませていれば到達しない。到達したら不変条件の違反で、処理系のバグである *)
      bug "module が平坦化されていません(flatten_modules を先に呼んでください)"

(* ## 14.13 run

   `run_units` は、単位の並び(先頭がプレリュード)を順に実行する。
   どの単位も同じグローバル環境で実行する。
   値の参照は型検査が木に書いた参照先で引き、型とコンストラクタの内部名は単位ごとに別なので、
   別々の単位の同じ名前が実行時に混ざることはない。
   `run` は単位が 1 個の場合である。

   実行の全体は `Builtin.with_runtime`(第13章)の中で行う。
   `with_runtime` はランタイムが提供するエフェクトのハンドラで、
   `Console.write` の文字列を出力先へ送る。
   このハンドラも受け取らなかった操作は `Effect.Unhandled` になり、driver が操作名を含めて報告する。
   ハンドラをプログラムの最も外側に置くことで、
   操作を未処理として扱う箇所をここ 1 か所にしている。

   `start_program` は、インスタンス表 `instance_impls` と、
   辞書パラメータを含まない証拠から作った辞書のキャッシュ `closed_cache` を空にする。
   同じプロセスで `run` を繰り返し呼ぶ場合(第16章の `eval_string`)に、
   前回の実行で登録したインスタンスと辞書を次の実行に残さないためである。
   残っていると、同じプログラムの結果が、それより前に何を実行したかに依存する。

   返り値は捨てる。
   暗黙の main はなく、トップレベルの式文は順に実行されるだけで、その値は使われない。 *)

(* グローバル環境を作る。組み込みの値と、その時点で宣言表にあるクラスのメソッドの値(§14.11)を置く *)
let start_program () =
  Hashtbl.reset instance_impls;
  Hashtbl.reset closed_cache;
  let globals = Hashtbl.create 512 in
  register_builtin_values globals;
  register_class_methods globals;
  { globals; locals = SMap.empty; dicts = DMap.empty; resume = None }

(* 単位 1 個の宣言を、前の単位までを実行したグローバル環境で実行する。
   値の参照は型検査が木に書いた参照先で引くので、単位をまたいでも名前は衝突しない *)
let exec_unit env decls = List.fold_left exec_decl env decls

(* 単位の並び(プレリュードが先頭)を順に実行する *)
let run_units ~sink units =
  let env = start_program () in
  ignore
    (Builtin.with_runtime ~sink (fun () ->
         ignore (List.fold_left exec_unit env units);
         unit))

let run ~sink decls = run_units ~sink [ decls ]

(* ## 14.14 本章の限界

   ### fiber の上の Stack_overflow

   ハンドラの本体は fiber の上で実行される。
   fiber のスタックはヒープ上で伸びるので、止まらない再帰は、
   通常のスタックの上で実行した場合より遅れて `Stack_overflow` になる。
   先にメモリを使い尽くして、`Out_of_memory` になることもある。
   そのため driver(第16章)は、`Stack_overflow` と `Out_of_memory` を同じ終了コード 3 で報告する。
   スタックの上限が既定値のときは、深い非末尾の再帰がどの深さでエラーになるかが、
   環境のメモリ量で変わる。
   そのため、末尾呼び出しでスタックが増えないことは、
   既定の上限でプログラムが最後まで動くことからは確かめられない。
   `test/tail_calls.t` は、`OCAMLRUNPARAM=l=100k` でスタックの上限を 102400 ワードに絞る。
   そのうえで、非末尾の再帰がスタックオーバーフローになる回数だけ繰り返しても、
   末尾呼び出しと末尾 `resume` が最後まで動くことを確かめる。

   ### 残している制限

   どの節にも一致しなかった操作を外側のハンドラへ回す処理(re-perform)を実装していないことは、
   残している制限に数えない。
   仕様はその規則を持たず(sample.kel:515)、
   第11章の検査(§11.23)が、どの節も選ばれないことのあるハンドラを型検査で拒否するからである。
   この検査は、各操作に、ガードがなく、引数のパターンが必ず一致する節を 1 つ以上要求する。
   同じハンドラの中では、選ばれなかった節から次の節へ進む。
   外側のハンドラへ回す機構と、それを実装しない理由(型付けができないこと)は、§14.9 に書いた。

   残している制限は次の 1 つである。

   - 前方参照の値を、定義より前に評価される位置で使うこと。
     パス 1c のシグネチャによって型検査には通るが、`let x = g(1)` の右辺のような、
     その場で評価される位置から、後ろで定義する `g` を呼ぶと、
     実行時にはまだ値がないので「未束縛の変数」の実行時エラーになる。
     前方参照を、名前を評価する時点で値を引く方法で実現しているために、この形が残る。
     誤った値を返して実行を続けるのではなく、実行時エラーで終了するので、許容している。
     インスタンス宣言より前の位置でそのインスタンスを使う形も、同じく実行時エラーにしている(§14.6)。

   値の名前については、elab が宣言時点の環境で解決した参照先を `resolved` に書き、
   評価器はその参照先で値を引く(§14.4)。
   そのため、同名の再束縛(`let` の後の同名の `let` や `extern`、
   クラスメソッドと同名のトップレベル束縛)でも、
   module の値の別名でも、`--prelude` で差し替えたプレリュードの module の中の名前でも、
   型検査と実行は同じ宣言を選ぶ(`test/resolved_names.t`)。

   ### 辞書のコスト

   辞書は、型検査が木に書いた証拠を評価して作る(§14.6)。
   辞書パラメータを含まない証拠の辞書は、穴ごとに 1 回だけ作る。
   辞書を受け取る値は、直前に受け取った辞書の並びと結果を記録する。
   そのため、同じ呼び出し箇所を繰り返し実行しても、辞書を作り直さない。
   制約付きの多相関数の再帰は、再帰のたびに辞書パラメータを `dicts` から引いて渡し、
   演算子の辞書からメソッドを選ぶので、その分だけ単相の関数より遅い。

   辞書のコストとは別に、本章の処理のうち、省いてもエラーにならず、
   気づかないまま動作が変わるものを最後に挙げる。

   1. 起動ごとの `inst` の採番。
      共有すると、入れ子のハンドラが、外側のハンドラ宛ての `Unwind` を自分宛てとして受け取る。
   2. resume しなかった場合と例外で脱出した場合の両方での `discontinue`。
      省くと資源が漏れる。
   3. 節本体の末尾の背骨にある `Resume` の `continue` を、try ブロックを抜けてから呼ぶこと。
      try ブロックの中で呼ぶと、perform を含むループが perform のたびにスタックを使う。
      ただし、引数の評価は try ブロックで囲む。
      囲まないと資源が漏れる。
   4. 辞書とセレクタのクラスの比較。
      省くと、辞書の渡し方を誤ったときに、エラーにならずに別のメソッドが呼ばれる。
   5. `let` による評価順序の固定。
      省くと、観測できる意味論が変わる。 *)

(* ## 14.15 対話的な実行

   対話的な実行(第16章)は、プレリュードを 1 回だけ実行し、その後は入力ごとに宣言を実行する。
   `start_session` は globals を作ってプレリュードを実行し、セッションを返す。
   `exec_input` は、1 つの入力の宣言を `with_runtime` の中で実行し、
   表示する値の並びを `show` に渡す。
   並びの要素は、名前、式か参照先、値の 3 つの組である。
   `show` も `with_runtime` の中で呼ぶ。
   表示のために呼んだ Show のインスタンスが実行時エラーになったときに、
   その入力の全体を取り消すためである。
   `with_runtime` を入力ごとに呼べるのは、継続が入力の境界をまたがないからである。
   `handle` は式で、トップレベルの `with` も入力の末尾で閉じる。
   `inst` はプロセス全体で共有する `new_oid` で採番するので、
   `with_runtime` を何度呼んでも衝突しない。

   実行時エラーになった入力は、入力の全体を取り消す。
   `exec_input` は、globals とインスタンス表への書き込みを `jreplace` で記録する。
   例外が起きたら、記録した書き込みを新しいものから順に元に戻し、
   環境を入力の前の状態に戻して、例外を再送出する。
   辞書のキャッシュ(`closed_cache`)は戻さない。
   失敗した入力の穴は後の入力から参照されないので、残っていても動作は変わらない。
   出力と、Ref や可変配列の内容の書き換えも戻さない。

   セッションを始めた後の入力で宣言したクラスには、
   `start_session` の `register_class_methods` がメソッドを選ぶ値(§14.11)を置いていない。
   そこで `DClass` を実行するときに、そのクラスのメソッドを選ぶ値を、`GMethod` のキーで置く。
   キーはクラスごとに別なので、先にある同名の値を上書きしない(§14.11)。 *)
type session = { mutable s_env : env }

(* 束縛パターンの変数の名前を、書いた順に返す *)
let rec pat_names ((_, p) : T.pat) =
  match p with
  | T.PVar x -> [ x ]
  | T.PAnnot (q, _) -> pat_names q
  | T.PRecord (fs, tail) -> List.concat_map (fun (_, q) -> pat_names q) fs @ Option.fold ~none:[] ~some:pat_names tail
  | T.PCtor (_, args) -> List.concat_map (fun (a : T.ctor_arg_pat) -> pat_names a.T.cap_pat) args
  | T.PVariant (_, q) -> pat_names q
  | T.PWildcard | T.PBool _ | T.PNumber _ | T.PText _ -> []

let start_session ?(print = false) ~sink prelude =
  let s = { s_env = start_program () } in
  ignore
    (Builtin.with_runtime ~print ~sink (fun () ->
         s.s_env <- exec_unit s.s_env prelude;
         unit));
  s

let exec_input ?(print = false) ?(show = fun _ -> ()) s ~sink decls =
  journaling := true;
  journal := [];
  let saved_env = s.s_env in
  let shown = ref [] in
  let step env ((_, d) as node : T.decl) =
    match d with
    | T.DClass c -> (
        match Decls.find_class (Type.intern c.T.cls_name) with
        | Some ci ->
            let cls_name = Type.name_of ci.Decls.ci_name in
            bind_globals env (List.map (fun ((m, _) as ms) -> (Tree.GMethod (cls_name ^ "." ^ m), method_selector ci ms)) ci.Decls.ci_methods)
        | None -> env)
    | T.DExp e ->
        (* 辞書パラメータを持つ式文は、宣言の位置で評価せず、辞書を受け取る値にする。
           評価するのは、値を表示する第16章 §16.6b である *)
        let v =
          match Tree.get_dict node with
          | Tree.DAbs ks -> VDictAbs { da_last = None; da_name = "_"; da_arity = List.length ks; da_fn = (fun ds -> eval (bind_dicts env ks ds) e) }
          | _ -> eval env e
        in
        shown := ("_", `Exp e, v) :: !shown;
        env
    | T.DLet ((_, b) as bnode) ->
        let env' = exec_decl env node in
        let bound =
          List.filter_map
            (fun x ->
              let g = Tree.GDecl (Tree.oid_of bnode, x) in
              Option.map (fun v -> (x, `Ref g, v)) (Hashtbl.find_opt env'.globals g))
            (pat_names b.T.lb_name)
        in
        shown := List.rev_append bound !shown;
        env'
    | T.DLetRec bs ->
        let env' = exec_decl env node in
        List.iter
          (fun ((_, b) as bnode : T.let_binding) ->
            match snd b.T.lb_name with
            | T.PVar x -> (
                let g = Tree.GDecl (Tree.oid_of bnode, x) in
                match Hashtbl.find_opt env'.globals g with Some v -> shown := (x, `Ref g, v) :: !shown | None -> ())
            | _ -> ())
          bs;
        env'
    | _ -> exec_decl env node
  in
  match
    Builtin.with_runtime ~print ~sink (fun () ->
        s.s_env <- List.fold_left step s.s_env decls;
        (* 結果の表示も with_runtime の中で行う。表示のために呼んだ Show のインスタンスが
           実行時エラーになったら、この入力の書き込みも取り消す *)
        show (List.rev !shown);
        unit)
  with
  | _ ->
      journaling := false;
      journal := []
  | exception ex ->
      List.iter (fun f -> f ()) !journal;
      journal := [];
      journaling := false;
      s.s_env <- saved_env;
      raise ex
