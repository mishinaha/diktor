(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第14章 評価器

   本章は実行系の中心で、木を歩いて値を作る。
   受け取るのは、第11章(elab.ml)が型と解決結果を書き込んだ木、
   第12章(value.ml)の値の表現とレコード演算、
   第13章(builtin.ml)のプリミティブと最も外側のハンドラである。
   第16章(driver.ml)へ渡すのは、正常に終了したか、どの例外で終わったかだけである。

   評価器の大半は素直な木の巡回である。
   込み入っている部分は 2 つある。
   エフェクトハンドラ(§14.10)と、型クラスの辞書(§14.6 と §14.7)である。
   前者は Keleut の意味論を OCaml 5 の `Effect.Deep` に写す部分で、
   後者は型検査が木に書いた証拠から辞書を作り、メソッドを選ぶ部分である。
   どちらも、誤って実装してもエラーにならず、気づきにくい形で壊れる。

   ## Keleut のハンドラと OCaml 5 の Effect.Deep の対応

   Diktor は Keleut のエフェクトを OCaml 5 の `Effect.Deep` にそのまま写す。
   対応は次のとおりである。

   | Keleut(sample.kel §9) | OCaml 5 の Effect.Deep |
   |---|---|
   | 深いハンドラ `handle { … }` | `match_with` 1 つ |
   | `perform op(args)` | `Effect.perform (Op (op, args))` |
   | `resume(e)` | `Effect.Deep.continue k v` |
   | resume を呼ばずに節を抜ける | `discontinue k (Unwind (inst, v))` |
   | `case return(x)` | `retc`(親のスタック上で走る) |
   | `case cancel` | `exnc` の中で節を走らせる |
   | 最も内側のハンドラが捕まえる | `effc` が `None` を返せば外側へ進む |
   | resume はアフィン(高々 1 回) | ワンショット継続(先に自前で検査する) |
   | resume の返り値の型が handle 式全体の型 | `continue` の型が `match_with` の型 |
   | cancel の LIFO の巻き戻し | fiber の入れ子から自動で決まる |

   表の最後の行のとおり、後始末の順序はハンドラの入れ子という既存の構造から決まる。
   そのため、評価器は後始末の順序を管理しなくてよい。

   ## 本章が守る 3 つの規約

   1. 末尾呼び出しの規約。
      `eval` の末尾位置(`Apply` のクロージャ本体、`Match` の節本体、ブロックの末尾式)を、
      OCaml の末尾呼び出しに保つ。
      とくに、`eval` の再帰を `try … with` で包まない。
      Keleut には while が無く、反復の手段は再帰だけなので、末尾呼び出しの最適化を失うと、
      普通のループがスタックを使い尽くす。
      例外は、操作節の本体(短い経路では `resume` の引数)と操作節のガードと cancel 節の本体である。
      前の 2 つは §14.10 の 3 つの経路を判定するために、cancel 節は中の例外を抑制するために、
      包みの中で評価する。
      そのため、これらの中の末尾位置にある関数呼び出しは末尾にならない。
      操作節の本体の末尾の背骨にある `resume` だけは、包みを抜けてから継続を末尾で発行する(§14.10)。

   2. 評価順序を let で固定する。
      OCaml は関数適用で引数を評価する順序を規定しておらず、現行のコンパイラは右から左に評価する。
      Keleut の仕様は左から右(sample.kel:277)なので、
      `apply (eval env f) (eval env arg)` と書くと順序が逆になる。
      値を 1 つずつ `let` で束縛して、評価順序を OCaml の未規定な評価順から切り離す。

   3. エラーの装飾は、driver の最も外側で 1 回だけ行う。
      途中で例外を捕まえて包み直すと、規約 1 が壊れる。
      さらに、例外はエフェクトの巻き戻しにも使われている(§14.10 の `Unwind`)ので、
      捕まえ損ねるとそのまま意味論が壊れる。

   ## 章の見取り図

   表(§14.1)、パターン照合(§14.2)、数値リテラル(§14.3)、`eval` の骨格(§14.4)、適用(§14.5)、
   辞書とメソッドの選択(§14.6)、構造的等価(§14.7)、束縛(§14.9)、ハンドラ(§14.10)、
   トップレベル(§14.11〜§14.14)の順に述べる。 *)
open Aux
open Syntax
open Value
module T = Tree.Tree

(* ## 14.1 実行時に引く表

   型クラスのメソッドをどのインスタンスで呼ぶかは、型検査が型から決め、
   証拠として木に書く(第5章 §5.1b)。
   評価器は証拠から辞書を作り(§14.6)、辞書が指す (クラス, 型構成子) でインスタンスの表を引く。
   実行時の値のタグは見ない。
   要る表は、利用者が宣言したインスタンスの `instance_impls` と、
   第13章の組み込みのメソッド表である。
   型構成子は第1章のインターン表の oid で、型の側と同じ番号を使う。
   辞書パラメータは局所環境 `locals` に名前で置くので、
   閉包が辞書を字句的に捕まえる仕組みを別に持たない。 *)

(* 利用者が宣言したインスタンスのメソッド。(クラス, 型構成子) → メソッド名 → 前提と
   メソッド自身の辞書を受け取って実装を返す関数。exec_decl の DInstance だけが jreplace で書く *)
let instance_impls : (oid * oid, (oid * (Value.t list -> Value.t)) list) Hashtbl.t = Hashtbl.create 32

(* 辞書パラメータの鍵(型変数の vid, クラスの oid)を局所環境の名前にする。
   利用者の識別子は英字か _ で始まるので、$ で始まる名前とは衝突しない *)
let dkey_name ((v, c) : Tree.dkey) = "$d" ^ string_of_int v ^ ":" ^ string_of_int c

let bind_dicts env ks ds = { env with locals = List.fold_left2 (fun l k d -> SMap.add (dkey_name k) d l) env.locals ks ds }

(* 辞書パラメータを含まない証拠の辞書は、穴ごとに 1 回だけ作って覚える *)
let closed_cache : (oid, Value.t) Hashtbl.t = Hashtbl.create 64

let rec closed_ev (e : Tree.evidence) =
  match e with
  | Tree.EvParam _ -> false
  | Tree.EvInst (_, _, subs) -> List.for_all closed_ev subs
  | Tree.EvRecord fs | Tree.EvVariant fs -> List.for_all (fun (_, e) -> closed_ev e) fs
  | Tree.EvHole h -> ( match h.Tree.h_sol with Some e -> closed_ev e | None -> false)

let dict_params_of node = match Tree.get_dict node with Tree.DAbs ks | Tree.DMethod (ks, _, _) -> ks | _ -> []

(* `cancel_log` は、cancel 節で抑制した例外の行き先である。
   仕様 sample.kel:585 は、cancel 節について次のように定めている。
   「cancel 節から外へは脱出できない。例外に相当するものが起きるとその cancel 節は打ち切るが、
   脱出は抑制してログに記録し、外側の後始末を続ける」。
   ライブラリが stderr に直接書かないよう、関数を 1 段はさみ、driver(第16章)がそれを差し替える。 *)

(* cancel 節の中の例外を記録する関数(sample.kel:585)。driver が差し替える *)
let cancel_log : (string -> unit) ref = ref (fun _ -> ())

(* ## 14.2 パターン照合

   `match_pat` は、照合に成功したら束縛を積んだ locals を `Some` で返し、失敗したら `None` を返す。
   失敗を例外にしないのは、照合の失敗が match の次の節へ進むための正常な制御で、
   エラーではないからである。

   細部で効いているのは次の 3 点である。

   - レコードは最左一致で照合する(Scoped Labels、第12章)。
     `record_take` が最も左の同名のラベルを 1 つ取り出して残りを返すので、
     同名のラベルを 2 つ持つ値から 2 回取ると、2 回目は隠れていたほうに当たる。
     ラベルが無いときに `record_take` が投げる `Runtime_error` は、ここでは照合の失敗なので、
     `exception` パターンで受けて `None` に変える。
     実行時エラーとして外へは出さない。
   - コンストラクタパターンは表を引くだけである。
     位置引数とラベル引数の混在や、省略されたフィールドの扱いは、
     elab が `field_to_arg` にまとめている(第5章(tree.ml)の `resolved`)。
     `None` は、そのフィールドにパターンが触れていないことを表す。
     ここで名前解決をやり直すと、elab と interp が同じ規則を二重に実装することになり、
     両者が食い違いうる。
   - 数値パターンは、字面ではなく値で比べる。
     リテラルの字面をその値の型で読み直してから比べるので、`0x1` と `1` は一致する。
     第10章(exhaust.ml)の重複検出も、字面を数値として読んでから比べる。

   `bind_pat_exn` は、反駁できないはずの位置(`let`、関数の引数、`return` 節)で使う。
   操作節の引数はここを通らず、フォールスルーする照合(`match_pat`)で扱い、
   一致しなければ次の節へ進む(§14.10)。
   `let`、`let rec`、`fn` の引数と `return` 節に書いた反駁可能なパターンは、
   `Exhaust.queue` で網羅性検査に掛かる。
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
            (* ラベルが無いのは照合の失敗であって実行時エラーではない *)
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
                  (* 省略されたフィールドは触らない *)
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

   `1` が `Int32`、`Int64`、`Float64` のどれなのかは、字面からは決まらない。
   決めるのは型検査で、既定化の結果がノードの型に書かれている。
   評価器は型を実行時に持ち回らず、elab の書き込んだ型を読むのはここだけである。
   ほかのノードでは `resolved`(解決結果)しか読まない。

   字面は字句解析のまま(`0x` 接頭辞やアンダースコアの区切りを含む)保持されており、
   OCaml の `Int32.of_string` はそれをそのまま解釈できる。
   範囲外の字面で起きる `Failure` は、`Runtime_error` に包み直す。
   包まないと、利用者のプログラムの誤りである範囲外のリテラルを、
   driver(第16章)の受け皿の最後の節が「内部エラー: 予期しない例外です」として報告する。
   終了コードは `Runtime_error` の場合と同じ 3 だが、利用者には処理系の誤りに見える。 *)

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

   本体は素直な木の巡回である。
   以下では、ノードごとの注意点だけを述べる。

   ### 評価順序

   `Apply`、`BinOp`、`RecordUpdate` は、規約 2 に従って `let` で左から右の順序に固定する。
   OCaml に任せると右から左になり、
   副作用のあるプログラム(perform を含む)の出力の順序が仕様と食い違う。

   `RecordExtend (rest, l, v)` だけは、value を先に、rest を後に評価する。
   仕様(sample.kel:278)が、`{l = e extends r}` では e を先に、r を最後に評価すると定めている。
   タプルの脱糖がこの規則に従うので、`(a, b, c)` は a、b、c の順に評価される。
   この順序は AST のフィールドの順序と逆なので、コードを目で追うときに間違えやすい。

   `Construct` は 2 つの順序を分ける。
   評価はソースの順、格納は宣言したフィールドの順である。
   `List.iteri` の副作用でソースの順に評価し、書き込み先は elab が作った `arg_to_field` の表で引く。

   ### ノードごとの要点

   - `Ident` は 3 段階で引く。
     locals(不変の Map)、elab が `resolved` に書いたトップレベルの実体(`RVar`)、
     引数のないコンストラクタ(`RCtor`)の順である。
     トップレベルの実体は globals(可変の Hashtbl)を実体の鍵(`Tree.gref`)で引く。
     globals は可変で、実体を呼び出し時に引くので、トップレベルの相互参照と前方参照が、
     追加のコードなしで通る(第12章の環境の二層構造)。
     同名の再束縛は、束縛ノードごとに別の鍵になるので、前の束縛を上書きしない(§14.13)。
     どれにも当たらなければ、型検査と評価器の解決が食い違っている。
     型検査が訪れなかった `Ident` を評価したか、
     型検査が局所と判断した名前が実行時の locals に無いかで、
     どちらも処理系の誤り(`bug`)にする。
   - `BinOp` は第7章(prims.ml)の表を引くだけである。
     `Neg` も同じく第7章の `neg_method` で `Neg.neg` を呼ぶ。
     `&&` と `||` だけは、短絡して右辺を評価しないことがあるので、型クラスにできない。
     `!=` は `Eq.eq` の否定として同じ表に入っている。
   - `Match` では、節のガードが偽なら次の節へ進む。
     `try_clauses` は末尾再帰で、節本体の `eval` も末尾位置にある(規約 1)。
     ハンドラの操作節も同じ規則で、
     パターンが一致しないときもガードが偽のときも次の節へ進む(§14.10)。
   - `Perform` は、elab が `resolved` に書いた完全な操作名の oid をそのまま使う。
     修飾なしで書いた操作名の解決(第11章 §11.20)は型検査で済んでおり、実行時に名前を探すことはない。
   - `Resume` は、継続を消費する前に引数を評価する。
     `resume(f())` の `f` が例外で脱出すれば、resume は未消費のまま節の例外の経路
     (§14.10 の discontinue)に乗る。
     順序を入れ替えると、消費済みの継続を捨てることになる。
     この分岐に来るのは、節本体の末尾の背骨の外にある `resume` だけである。
     背骨の上の `resume` は §14.10 の `eval_clause_tail` が処理し、その経路も `take_resume` で
     引数を先に評価する。
   - `Run` は、実行時には恒等写像である。
     `run h { … }` の `h` は型の上にしか存在せず、
     リージョンの安全性は第11章の剛定数とレベルが保証している。
     操作を持たないエフェクトラベル(`Heap`、`Blocking`)には、実行時の処理が何も無い。
     `Run` は、実行時に何もしないもののいちばん目立つ例である。
     `Blocking` を落とす組み込み関数 `pinned` も、実行時には渡された関数を呼ぶだけである(§14.11)。
     型で守り切れた性質を、実行時に検査し直すことはしない。 *)

(* 操作節の本体を末尾の背骨に沿って評価した結果(§14.10)。
   `Clause_resume v` は、背骨の末尾の `resume(v)` に着いたことを表す。
   継続はまだ再開しておらず、再開は呼び出し側が例外の捕捉を抜けてから行う *)
type clause_end = Clause_value of Value.t | Clause_resume of Value.t

let rec eval env ((_, e) as node : T.exp) : Value.t =
  match e with
  | T.Bool b -> VBool b
  | T.Text s -> VText s
  | T.Number n -> number_value node n (* 評価器が elab の型を読む唯一の場所(§14.3) *)
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
              | None -> runtime_error ("未束縛の変数: " ^ name))
          (* 裸の引数なしコンストラクタ *)
          | Some (Tree.RCtor (d, c, _)) -> VData { d_type = d; d_ctor = c; d_fields = [||] }
          | _ -> bug ("Ident が解決されていません: " ^ name)))
  | T.Lambda { l_params; l_body } -> VClosure { c_env = env; c_params = l_params; c_body = l_body }
  | T.Apply (f, arg) ->
      (* 左から右に評価する。OCaml の未規定の評価順に任せない(規約 2) *)
      let vf = eval env f in
      let va = eval env arg in
      apply vf va
  | T.Construct (_, args) -> (
      match Tree.get_resolved node with
      | Some (Tree.RCtor (d, c, arg_to_field)) ->
          let fields = Array.make (Array.length arg_to_field) unit in
          List.iteri
            (fun ai (a : T.ctor_arg) ->
              (* 評価はソースの順、格納は宣言したフィールドの順(resolved の対応表) *)
              fields.(arg_to_field.(ai)) <- eval env a.T.ca_exp)
            args;
          VData { d_type = d; d_ctor = c; d_fields = fields }
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
          (* 辞書はオペランドより先に作る。副作用は無く、後で作ると env が右辺の評価をまたいで生き残る *)
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
      (* value が先、rest が後(sample.kel:278。AST のフィールドの順序と逆) *)
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
      (* この分岐に来るのは、節本体の末尾の背骨の外にある resume だけである。
         背骨の上の resume は §14.10 の eval_clause_tail が処理する *)
      let r, v = take_resume env arg in
      Effect.Deep.continue r.r_k v
  | T.Run (_, body) -> eval env body (* 実行時は恒等。リージョンの安全性は型が保証する *)

(* ## 14.5 関数の適用

   関数は複数の引数を取って 1 つの値を返し、引数は 1 つのレコードに詰めて渡す。
   したがって適用は、引数レコードのフィールドを仮引数のパターンに順に束縛するだけである。

   引数の個数の不一致は、ここでは本来起きない。
   引数の個数は矢印型の一部であり、
   型検査が閉じた `_item` 行の単一化として検査しているからである(sample.kel:190-191)。
   個数の検査は保険として残してある。
   プリミティブを経由した呼び出しや内部の誤りで壊れた引数が来たときに、
   `List.fold_left2` の `Invalid_argument` のような無関係な例外ではなく、
   個数の不一致として報告するためである。

   束縛の土台を `c.c_env.locals`(定義時の環境)にすることで、静的スコープを実装している。
   呼び出し側の locals は一切混ざらない。 *)

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
   実行時の値のタグは見ない。
   辞書パラメータを持つ値(`VDictAbs`)には、使う位置の `DUse` の証拠を評価した辞書の列を渡す。
   メソッドの実体は `method_selector`(§14.12)が作る `VDictAbs` で、
   辞書を受け取ると、呼ばれた時点でインスタンスの表からメソッドを選ぶ関数を返す。
   選ぶ時点を呼び出しにするのは、インスタンス宣言より前の位置で辞書を作る形を、
   宣言の後に呼べば動かすためである(§14.13)。
   セレクタのクラスと辞書のクラスが食い違えば、辞書の渡し方の誤りなので `bug` にする。 *)

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
      match SMap.find_opt (dkey_name k) env.locals with Some d -> d | None -> bug ("辞書パラメータが束縛されていません: " ^ dkey_name k))
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
              (* 型検査はパス 1c でインスタンス表を揃えるので、宣言より前の位置の使用を通す。
                 実行は宣言の順に表へ書くので、その時点ではまだ実体が無い。黙って続けず止める *)
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
   行の型は最左一致で決まる一方、異なるラベルの間には順序が無い。
   そのため、値のフィールドのリストを前から突き合わせる比較は誤りである。
   型検査が組んだ `EvRecord` は、閉じた行の型のラベルごとに、
   そのフィールドの型の `Eq` の辞書を持つ。
   左辺と右辺からそのラベルの最も左のフィールドを取り出して消し、フィールドの辞書で比べる。
   最後に両辺が空になれば一致である。
   フィールドの型が名目的な型なら、その型のインスタンスの辞書で比べるので、
   利用者が宣言した `Eq` を無視して構造をのぞき込むことはない。
   ヴァリアントは、ラベルを比べ、同じなら行の中のそのラベルの辞書で積載値を比べる。
   `Float64` の比較は組み込みの `eq` に委ねるので、IEEE の意味論(NaN ≠ NaN)がそのまま出る。 *)

and eq_with d x y = Builtin.as_bool (apply (select_method ~cls:(Type.intern "Eq") d "eq" []) (VRecord [ (Type.l_item, x); (Type.l_item, y) ]))

(* 閉じたレコード型の構造的な Eq。型の行の順にラベルを取り、両辺から最も左の同名のフィールドを
   取り出して、そのフィールドの辞書で比べる。異なるラベルの間の物理的な順序は値によって違いうる *)
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

(* ## 14.9 let と let rec

   `eval_binding_value` は、引数リストが付いていれば、右辺を評価せずにクロージャを作る。
   `let f(x) = …` の右辺は関数の本体であって、束縛の時点で評価する式ではない。

   `let rec` は、クロージャの生成、環境の構築、`c_env` のバックパッチの 3 段階で束縛する。
   相互再帰する関数は、自分たちを含む環境を捕まえる必要がある。
   その環境はクロージャができあがるまで作れないので、循環を後から結ぶ。
   第12章のクロージャで `c_env` だけが mutable なのは、このバックパッチのためである。
   第12章には `resume` の `r_used` と `r_alive` という mutable なフィールドもあるが、
   これらは §14.10 のアフィン性と second-class の検査のためにある。

   右辺が関数でないときは実行時エラーにするが、この分岐には到達しない。
   `let rec x = x + 1` のように、型は付くのに実行すれば必ず落ちるプログラムは、
   elab が拒否するからである。

   トップレベルの `let rec`(§14.13)にバックパッチが要らないのは、
   globals が共有の可変な表で、実体の表引きが呼び出し時に起きるからである。 *)

and eval_binding_value_plain env ((_, b) : T.let_binding) =
  match b.T.lb_params with
  | Some ps -> VClosure { c_env = env; c_params = ps; c_body = b.T.lb_body }
  | None -> eval env b.T.lb_body

(* 辞書パラメータを持つ束縛は、辞書を受け取って束縛の値を評価する VDictAbs にする。
   値束縛の初期化式は、名前を使うたびに評価する(§14.5b) *)
and eval_binding_value env bnode =
  match dict_params_of bnode with
  | [] -> eval_binding_value_plain env bnode
  | ks -> VDictAbs { da_last = None; da_name = "let"; da_fn = (fun ds -> eval_binding_value_plain (bind_dicts env ks ds) bnode) }

and eval_binding env ((_, b) as bnode : T.let_binding) =
  let v = eval_binding_value env bnode in
  bind_pat_exn env.locals b.T.lb_name v

and eval_rec_bindings env (bs : T.let_binding list) =
  (* クロージャの生成 → 環境の構築 → c_env のバックパッチ。辞書パラメータを持つ束縛は、
     群の環境を捕まえて辞書を受け取るたびにクロージャを作る VDictAbs にし、バックパッチしない *)
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
                { da_last = None; da_name = name; da_fn = (fun ds -> VClosure { c_env = bind_dicts !genv ks ds; c_params = ps; c_body = body }) },
              None ))
      bs
  in
  let locals = List.fold_left (fun locals (n, v, _) -> SMap.add n v locals) env.locals closures in
  genv := { env with locals };
  List.iter (function _, _, Some c -> c.c_env <- { env with locals } | _ -> ()) closures;
  locals

(* ## 14.10 ハンドラ

   1 つの `handle` 式は、1 つの `Effect.Deep.match_with` になる。
   節の振り分けは、elab が `resolved` に書いたタグを読むだけで行う。
   タグは `ROp`、`RReturnClause`、`RCancelClause` の 3 種類である。
   操作名の解決はここでは行わない。

   ### 起動ごとの inst

   `inst` は、Handle ノードを評価するたびに `new_oid ()` で採番する。
   ハンドラの同一性は、書かれた場所ではなく、その起動ごとに決まる。
   AST のノードの id を流用すると、
   同じ handle 式が入れ子に起動する場面(再帰の中の handle や、`with_file` を 2 回呼んだ入れ子)で、
   内側のハンドラが外側宛ての `Unwind` を自分宛てと取り違えて飲み込む。
   取り違えると、handle 式が誤った値を返す。
   たとえば `#Err(boom)` を返すべきところで、`#Ok(#Err(boom))` を返す。

   ### Unwind のプロトコル

   `Unwind (inst, v)` は、例外の形をした通知である。
   resume されずに終わった節の値 `v` を、
   `inst` 番のハンドラの handle 式全体の値として届けることを依頼する。

   1. 節が resume を呼ばずに `v` を返す。
   2. `discontinue k (Unwind (inst, v))` で、捨てる継続の中にこの例外を送り込む。
   3. 中断された計算の断片が、内側から巻き戻る。
      途中のハンドラは `exnc` で自分宛てでない `Unwind` を受け取り、
      `cancel` 節を走らせてから再送出する。
   4. 最後に自分の `exnc` が `id = inst` を確かめて `v` を返す。これが handle 式の値になる。

   後始末が LIFO になるのは、この経路が fiber の入れ子をそのまま逆にたどるからである。
   評価器には、順序を管理するコードが無い。
   仕様(sample.kel:572-585)は defer 構文を持たず、後始末をハンドラの cancel 節に書くと定めている。
   実装では、その規則がこの 4 段階に対応する。

   ### 3 つの経路

   `effc` が返す関数は、節の評価がどう終わったかによって 3 つの経路に分かれる。

   | 節の終わり方 | 処理 | 理由 |
   |---|---|---|
   | resume した後に値 `v` を返した | `v` を返す | 継続は消費済みで、返り値が handle 式の値になる |
   | resume せずに値 `v` を返した | `discontinue k (Unwind (inst, v))` | 捨てた継続の中の cancel 節を走らせる |
   | 例外 `ex` で脱出した | resume していなければ `discontinue k ex` | 捨てた継続の中と自分の cancel 節を走らせる |

   2 行目で `v` を直接返すと、捨てた継続の中にあるハンドラの `cancel` 節が走らず、資源が漏れる。
   回帰テストは `test/eval.t` の effects.kel である。
   このテストは `with_res` を 2 つ重ね、外側の `try_` に継続を捨てさせる。
   出力は `cancel inner`、`cancel outer` の順になる。

   これとは別に、ハンドラの節が自分の継続を捨てたとき、
   そのハンドラ自身の `return` 節と `cancel` 節は走らない。
   評価器はその継続を `discontinue` で捨てるが、送り込んだ `Unwind` は、
   自分の `exnc` がそのまま handle 式の値として受け取る。
   これは意図した挙動である。
   ここで cancel 節を走らせると、`try_` が正常に `#Err` を返すときにも後始末が走ってしまう。
   資源を持つハンドラが自分で継続を捨てるなら、後始末はその節の中に書く。

   3 行目は、素朴な実装で書き忘れやすい分岐である。
   節の中で `???` に到達した場合も、実行時エラーが起きた場合も、外側の `Unwind` が通過した場合も、
   `discontinue` が要る。
   これを書き忘れると、捨てた継続の中の cancel 節も、自分の cancel 節も走らない。
   `effc` からの素の `raise` は親のスタック上を伝播するので、自分の `exnc` を通らない。
   回帰テストは `test/eval.t` の holecancel.kel で、
   節本体が `???` でも内側の cancel 節が走ることを確かめる。

   この規約は、§13.6 の最も外側のハンドラ(`with_runtime` の `Console.write`)にも当てはまる。

   ### 末尾 resume

   上の 3 つの経路を判定するには、節の評価を `match … with exception` で包む必要がある。
   この包みの内側で `continue` を発行すると、`continue` が `effc` の末尾式でなくなる。
   継続の発行が末尾でないと、perform のたびにスタックが伸びる。
   fiber のスタックは伸長できるので既定の上限では Stack_overflow になりにくいが、
   perform の回数に比例して空間を使い、大幅に遅くなる。
   Keleut は反復を再帰で書くので、perform を含むループは、
   節の末尾の `resume` が継続を末尾で発行することを前提にしている。

   そこで、節本体の末尾の背骨にある `Resume` では、継続を包みの内側で発行しない。
   背骨は、`eval` の末尾位置から `Handle` の内側を除いたもので、`Seq` の最後、
   `Let` と `LetRec` の続き、`Match` の節本体、`&&` と `||` の右辺、`Run` の本体である。
   `eval_clause_tail` は背骨をたどり、背骨の末尾の `Resume` に着いたら、
   引数を評価して検査を済ませ、継続を再開せずに `Clause_resume v` を返す。
   背骨から外れた部分は `eval` で評価し、`Clause_value v` を返す。
   `effc` は包みを抜けた後の値の枝で、`Clause_resume v` なら `continue k v` を末尾で発行する。
   `Clause_value v` なら、上の表の 1 行目か 2 行目の経路に進む。

   背骨は `Handle` と `Lambda` に入らない。
   内側の `handle` の本体にある `resume` は、内側のハンドラの枠の中から呼ばれるので末尾にならない。
   内側の `handle` の return 節と、閉包の本体には、その節の `resume` を書けない(§11.21、§11.24)。
   そのため、背骨の上の `Resume` は常にこの節の resume である。
   背骨の外の `Resume` は、`eval` の中で `continue` を発行し、その結果を値として返す。

   背骨に `Resume` の無い節は、背骨をたどらずに `eval` で評価する。
   `eval_handle` は、ハンドラを起動するときに各節の背骨を 1 回ずつ調べ(`spine_has_resume`)、
   結果を節と並べて持つ。
   調べる費用は背骨の大きさ(`Match` のすべての節を含む)に比例し、perform のたびには掛からない。
   resume しない節の本体から深く再帰する形では、背骨をたどる 1 段が再帰の 1 段ごとに
   スタックを使うので、この区別が無いと、同じスタックの上限で落ちる深さが浅くなる。
   この区別は節の単位なので、`match` の一方の腕で resume し、他方の腕で再帰する節では、
   再帰する腕も背骨をたどり、落ちる深さは浅いままである。

   節本体が構文上 `Resume` そのものである節は、さらに短い経路を通る。
   `case op(x) => resume(…)` の形の節は多く、プレリュードのハンドラ(`with_stdout`)もこの形である。
   この経路は `r_used` を引数の評価より先に `true` にするので、
   引数の中の入れ子の `resume` は、継続を再開する前にアフィン性の検査で落ちる。
   背骨をたどる経路では、引数の中の入れ子の `resume` は継続を再開し、
   その後で外側の `resume` がアフィン性の検査で落ちる。
   どちらも実行時エラーで終わるが、エラーの前に継続の出力が見えるかどうかが異なる。
   `test/eval.t` の perf.kel(10 万回の println)が短い経路の回帰テストで、
   `test/tail_calls.t` が、小さいスタック上限の下で両方の経路が空間を使わないことを確かめる。

   どちらの経路も、3 つの経路の規約を守る。
   `match … with exception` が覆うのは、節の評価(短い経路では引数の評価)だけである。
   その中で例外が起きたら、resume していなければ `discontinue` する。
   包まないと、`resume(???)` の形で、捨てた継続の cancel 節も自分の cancel 節も走らない。
   回帰テストは `test/eval.t` の tailresume.kel である。
   再開した計算から出てきた例外は、包みの外で発行した `continue` からそのまま `effc` の外へ出る。
   これは、継続を消費済みの節が例外を再送出する経路(上の表の 3 行目)と同じ結果である。

   `continue` は値の枝、つまり例外を捕まえる範囲(trap)を抜けた後にあり、末尾での発行が保たれる。
   OCaml は、値の場合の枝を trap の外に置いてコンパイルする。
   一方、`continue` を trap の内側に置くと、perform のたびにスタックが伸びる。

   ### アフィンな resume と second-class

   `r_used` はアフィン性(高々 1 回)を、`r_alive` は second-class(節の外へ持ち出さない)を、
   実行時に検査するための印である。
   OCaml も 2 度目の `continue` で `Continuation_already_resumed` を投げるが、
   それでは Keleut のエラーとして説明にならないので、先に自前で検査して日本語のメッセージを出す。
   second-class の検査は 2 段構えで、実行時の `r_alive` はその片方である。
   もう片方は、節本体のラムダ式や関数束縛の本体に、その節の `resume` があれば拒否する構文検査で、
   elab にある。

   ### cancel 節の実行文脈

   `run_cancel` は `exnc` の中、つまり巻き戻しの途中で走る。
   このとき有効なのは外側のハンドラだけで、
   いま巻き戻しを起こしているハンドラ自身はすでに外れている。
   `Effect.Deep.match_with` の `exnc` は、fiber を巻き戻した後に親のスタックで呼ばれるので、
   `run_cancel` の中で `Effect.perform` しても自分の `effc` には届かない。
   cancel 節から自分の操作を perform すると、外側にある同じエフェクトのハンドラに届く。
   これは、第11章 §11.24 が cancel 節を外側の行で型付けているのと同じ事実を、
   実行の側から見たものである。
   届いた先の節が resume せずに抜けると、`Unwind` が cancel 節を通過しようとする。
   `run_cancel` はそれを cancel 節の中の例外として抑制し(仕様 sample.kel §9 の抑制規則)、
   ログに記録するだけで外へは出さない。
   回帰テストは `test/eval.t` の cancelouter と cancelnores である。

   cancel 節の中の例外をすべて抑制してログに記録するのは、仕様(sample.kel:585)の規則である。
   既知の例外(`Runtime_error`、`Unwind`、`Sys_error`)は日本語のメッセージにし、
   それ以外の例外は `Printexc.to_string` で文字列にしてからログに渡す。

   `retc` と `run_cancel` が `cl_guard` を読まないのは、
   elab が return 節と cancel 節のガードを拒否するからである(§11.24)。

   ### 操作節の選択

   操作節はソースの順に試し、パターンが一致しないときもガードが偽のときも次の節へ進む。
   これは §14.2 の match とまったく同じ規則である。
   ガードは resume の無い環境で評価する(ガードから継続は見えない。§11.24)。
   すべての節が外れたときは、`discontinue` で実行時エラーにする。
   elab の総和性検査は、各操作について、
   ガードが無く、その節だけを持つ match が引数の並びについて網羅的になる節を 1 つ要求する(§11.24)。
   この検査を通っていれば、この分岐には到達しない。
   この分岐は防御のために残してある。
   素の raise にしないのは、3 つの経路の規約どおり、捨てた継続の cancel 節を走らせるためである。

   Diktor は、ハンドラの外への後送り(re-perform)を実装していない。
   仕様も、どの節にも一致しなかった操作を外側のハンドラへ回す規則を持たない(sample.kel:515)。
   機構としては実装できる。
   `effc` のハンドラ関数は fiber の外で走るので、そこから `Effect.perform` すれば、
   自分を飛ばして外側のハンドラに届く。
   実装しないのは型の都合である。
   handle の型付けは対象のエフェクト E を行から消すので(§11.24)、
   ガードが偽の `E.op` を外へ流すと、E を持たない行の文脈に操作が漏れ、型が実行と合わなくなる。
   仕様は関数型の行を書いたとおりに読み(sample.kel:475)、
   行にラベルを足して暗黙に合わせる一般の規則(サブエフェクティング)を持たない。
   例外の使用時の開き(sample.kel:476)は、閉じた行の関数を使う側の行へ広げるだけで、
   行からラベルを落とすことはない。
   そのため、E を消す型付けと、E の操作を外へ流す実行を両立させる手段がない。 *)

(* resume の引数を評価し、アフィン性と second-class の検査を済ませて、継続を消費済みにする。
   継続の再開は呼び出し側が行う。
   引数を先に評価するので、引数の評価中に起きた例外では、resume は未消費のまま
   節の例外の経路(discontinue)に乗る。
   順序を入れ替えると、消費済みの継続を捨てることになる *)
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

(* 操作節の本体を、末尾の背骨に沿って評価する(§14.10)。
   背骨は `eval` の末尾位置と同じで、`Seq` の最後、`Let` と `LetRec` の続き、
   `Match` の節本体、`&&` と `||` の右辺、`Run` の本体である。
   それ以外のノードは `eval` に渡して `Clause_value` にする。
   `Handle` と `Lambda` には入らないので、背骨の上の `Resume` は常にこの節の resume である *)
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

(* 節本体の末尾の背骨に `Resume` があるか。背骨の定義は `eval_clause_tail` と同じである *)
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
  (* inst は Handle ノードを評価するたびに採番する(入れ子に起動したハンドラが、
     外側宛ての Unwind を自分宛てと取り違えないため) *)
  let inst = new_oid () in
  let op_clauses =
    List.filter_map
      (fun (cl : T.clause) ->
        match Tree.get_resolved cl with
        | Some (Tree.ROp op) -> Some (op, (cl, spine_has_resume (snd cl).T.cl_body))
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
          (* return 節は親のスタック上で走る *)
          match ret_clause with
          | None -> v
          | Some (_, c) ->
              let pat = match clause_arg_pats c with [ p ] -> p | _ -> bug "return 節のパターン" in
              let locals = bind_pat_exn env.locals pat v in
              eval { env with locals; resume = None } c.T.cl_body);
      exnc =
        (fun ex ->
          match ex with
          (* 自分宛ての巻き戻し。保留していた節の値が handle 式の値になる *)
          | Unwind (id, v) when id = inst -> v
          | ex ->
              (* 外側による巻き戻し(または実行時エラー)の通過。cancel 節を実行してから再送出する *)
              run_cancel ();
              raise ex);
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Op (op, args) -> (
              match List.filter (fun (o, _) -> o = op) op_clauses with
              | [] -> None (* 自分の操作でなければ外側へ *)
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
                         次の節へ進む(§14.2 の match と同じ規則)。ガードから継続は見えない *)
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
                      (* 節の選択(引数の照合とガードの評価)も例外の捕捉の中で行う。ガードで
                         起きた例外も、ガードを通過する外側の Unwind も、3 つの経路の規約に
                         乗せる。素の raise は fiber に届かず、捨てた継続の cancel 節も
                         自分の cancel 節も走らない *)
                      | exception ex -> Effect.Deep.discontinue k ex
                      | None ->
                          (* すべての節が外れた。elab の総和性検査(§11.24)を通っていれば到達しない
                             防御の分岐である。素の raise ではなく discontinue にして、
                             捨てた継続の cancel 節を走らせる(3 つの経路の規約) *)
                          Effect.Deep.discontinue k
                            (Runtime_error ("handle のどの節にも一致しません: " ^ Type.display_of op ^ show args))
                      | Some (locals, c, tail) -> (
                          match snd c.T.cl_body with
                          | T.Resume arg -> (
                              (* 節本体が resume そのものの短い経路(§14.10)。exception 節が覆うのは
                                 引数の評価だけで、continue は値の枝(例外の捕捉を抜けた後)に
                                 あるので、末尾での発行が保たれる。引数が例外で脱出したときは、
                                 通常の経路と同じく discontinue して、捨てた継続の cancel 節を
                                 走らせる。r_used を先に true にしてあるので、引数の中の入れ子の
                                 resume はアフィン性の検査で先に落ちる。例外が起きた時点で k は
                                 未消費なので、discontinue は常に安全である *)
                              let r = { r_k = k; r_used = true; r_alive = true } in
                              match arg with
                              | None ->
                                  r.r_alive <- false;
                                  Effect.Deep.continue k unit
                              | Some e -> (
                                  match eval { env with locals; resume = Some r } e with
                                  | v ->
                                      r.r_alive <- false;
                                      Effect.Deep.continue k v
                                  | exception ex ->
                                      r.r_alive <- false;
                                      Effect.Deep.discontinue k ex))
                          | _ when not tail -> (
                              (* 背骨に resume の無い節は、背骨をたどらずに評価する *)
                              let r = { r_k = k; r_used = false; r_alive = true } in
                              match eval { env with locals; resume = Some r } c.T.cl_body with
                              | v ->
                                  r.r_alive <- false;
                                  if r.r_used then v else Effect.Deep.discontinue k (Unwind (inst, v))
                              | exception ex ->
                                  r.r_alive <- false;
                                  if r.r_used then raise ex else Effect.Deep.discontinue k ex)
                          | _ -> (
                              let r = { r_k = k; r_used = false; r_alive = true } in
                              match eval_clause_tail { env with locals; resume = Some r } c.T.cl_body with
                              | Clause_resume v ->
                                  (* 背骨の末尾の resume。continue は値の枝(例外の捕捉を
                                     抜けた後)にあるので、末尾で発行される *)
                                  r.r_alive <- false;
                                  Effect.Deep.continue k v
                              | Clause_value v ->
                                  r.r_alive <- false;
                                  (* resume していなければ継続を巻き戻し、
                                     自分の exnc で v を受け取り直す *)
                                  if r.r_used then v else Effect.Deep.discontinue k (Unwind (inst, v))
                              | exception ex ->
                                  (* 節が例外で脱出したときも、resume していなければ
                                     discontinue して、捨てた継続の中の cancel 節を走らせる。
                                     落とすと資源が漏れる *)
                                  r.r_alive <- false;
                                  if r.r_used then raise ex else Effect.Deep.discontinue k ex))))
          | _ -> None);
    }

(* ## 14.11 組み込み値

   `Ref` は OCaml の `ref` で、`Array` と `MutableArray` はどちらも OCaml の配列である。
   リージョンの安全性(`run h { … }` の外へ持ち出せないこと)は、
   第11章の剛定数とレベルが型で保証する。
   そのため、実行時には包みも検査も無い。
   §14.4 の `Run` が恒等写像であるのと同じ理由である。

   値の表現だけは 2 つに分けている。
   `VArray` が不変、`VMutArray` が可変で、中身はどちらも `Value.t array` である。
   分けているのは印字(§12.7)のためで、実行時の動作が違うからではない。
   どのインスタンスのメソッドで印字するかは型検査が型から決めるので(§14.6)、
   値のコンストラクタの違いは、組み込みの `show` が可変配列であることを表示に出すためだけに使う。
   `type instance[A: Show] Show[Array[_]]` と `type instance[H, A: Show] Show[MutableArray[_, _]]` は、
   どちらも宣言も使用もできる。
   前提がリージョンの型パラメータにも制約を付けた `[H: Show, A: Show]` の形は、
   宣言できても使う位置で型エラーになる。
   その理由は `run` の剛定数に制約が無いことである。

   `MutableArray.freeze` はコピーを作る。
   仕様 §10 が要求するのは、観測できる契約だけである。
   その契約とは、freeze の後に元の可変配列へ書き込んでも、取り出した配列は変わらないことである。
   コピーするかどうかは実装が選ぶ、と仕様は明記している。
   配列を共有したまま契約を守るには、線形性か copy-on-write が要る。
   Diktor はどちらも持たないので、素直にコピーする。
   要素が可変配列である入れ子は浅いコピーのままなので、リージョンの内側では要素の別名を観測できる。
   しかし、そうした配列は要素の型に `h` を持つので、リージョンの外へは出られない。

   一方、配列の範囲検査は実行時に行う。
   長さは型に載っていないので、型では守れない。
   負の長さの `MutableArray.new` も、同じ理由で実行時に拒否する。

   `Array.each` は、渡された関数を `apply` で呼ぶ。
   その関数の中で `perform` が起きても、エフェクトは外側のハンドラまで届く。
   OCaml のエフェクトは、間にある `Array.iter` のスタックフレームを越えて伝わるからである。
   組み込み関数をエフェクトが通り抜けられるようにするための特別な仕掛けは要らない。 *)

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
          (* 長さは型に載っていないので、ここは実行時に守る *)
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
  (* freeze はコピーを作る。仕様 §10 の「freeze の後に元の可変配列へ書き込んでも、
     取り出した配列は変わらない」を、配列を共有しない最も素直な形で満たす *)
  reg "MutableArray.freeze" (fun args ->
      match Builtin.arg1 args with
      | VMutArray a -> VArray (Array.copy a)
      | _ -> runtime_error "MutableArray ではありません");
  (* pinned は恒等関数として実装する。Diktor が Blocking について守る観測できる
     契約は、並列度を減らさないことと、キャンセルの配送点にならないことの 2 つである。
     Diktor はタスクを 1 つしか持たず、キャンセルの配送点も持たないので、
     恒等関数がどちらの契約も満たす。スケジューラを持たないので、
     専用のスレッドへの束縛も行わない。Blocking はトップレベルに残せる(仕様 §12)ので、
     pinned を通さないプログラムも実行できるが、ランタイムが受け取るものは何も無い *)
  reg "pinned" (fun args -> apply (Builtin.arg1 args) unit)

(* ## 14.12 クラスメソッドの識別子参照

   `eq(a, b)` や `show(x)` のようなメソッドの識別子参照のために、
   辞書を受け取ってメソッドを選ぶ値(`method_selector`)を globals に置く。
   メソッドを選ぶのは、globals に置いた時点ではなく、
   辞書を受け取った関数が呼ばれた時点である(§14.6)。
   そのため、メソッドを参照する関数をインスタンス宣言より前に定義しても、
   インスタンス宣言より後に呼べば、そのインスタンスが使われる。
   呼び出しの評価がインスタンス宣言より前になると、§14.6 の実行時エラーになる。

   実体は、メソッドの鍵 `GMethod Cls.m` の 1 個で置く。
   非修飾名 `map` と修飾名 `Functor.map` のどちらで書いても、
   elab が同じ実体を `resolved` に書く(第11章 §11.33)。
   非修飾名をどのクラスのメソッド(またはどのトップレベルの値)に結ぶかは、
   elab が決める(パス 1b の先勝ちの規則と、後に置いたトップレベルの let による覆い)。
   ここでの登録の順序は関係しない。
   クラスメソッドと同名のトップレベル束縛は、束縛ノードの鍵(`GDecl`)で別に置かれるので、
   ラッパを覆わない。

   下の実装が、走査の結果をクラス名でソートしてから登録するのは、念のためである。
   鍵はクラスごとに別なので順序は結果を変えないが、
   ハッシュ順に由来する非決定性を表の走査に残さない。 *)

(* クラスメソッドの実体。辞書の列を受け取り、クラスパラメータの位置の辞書とメソッド自身の
   辞書に分け、呼ばれた時点でメソッドを選ぶ関数を返す。クラスパラメータの位置は、
   スキーマの制約の正準順の中で求める *)
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

(* ## 14.13 宣言の実行

   トップレベルの `let` と `let rec` は、globals に直接置く。
   バックパッチが要らないのは、§14.9 で述べたとおりである。

   本章でインスタンス表(`instance_impls`)に書き込むのは、`type instance` の処理だけである。
   この処理では、同義語の表を引くことに注意している。
   第11章の `flatten_modules` は、型検査の前に module を平坦化し、
   `module BigInt { newtype BigInt … }` の型を `BigInt.BigInt` に改名する。
   インスタンスの頭に書かれた非修飾名をそのまま鍵にすると、宣言した実体が実行時に見つからない。
   そこで `Decls.resolve_con` に通して、elab と同じ名前にそろえる。
   同義語は module ごとのスコープを持つので、
   `exec_decl` の冒頭で宣言の出身 module を `Decls.current_module` に立ててから引く。
   これは elab の `with_decl_module` と同じ規律である。
   回帰テストは `test/verify_fixes.t` の modinst.kel である。
   組み込みのインスタンスと同じ `(cls, con)` を持つ宣言は、elab が宣言の時点で拒否するので、
   ここに来る宣言が組み込みの実体を差し替えることはない。

   `extern` は、実装が無ければ、呼ばれた時点で落ちる prim を登録する。
   宣言だけして呼ばないプログラムを通すためである。
   同名の extern どうしで嘘の型を再宣言することは、elab が拒否する(登録簿が効く範囲は §6.2)。

   `DLet` と `DExtern` の分岐は、束縛した値を、束縛ノードと名前の組の鍵(`GDecl`)で globals に置く。
   同名の束縛を再び宣言しても、束縛ノードが違うので鍵も違い、前の束縛は残る。
   それより前に作られた閉包は、elab が書いた前の束縛の鍵を引くので、定義した時点の実体を見る。

   `type`、`newtype`、`effect`、`type class` は、実行時には何もしない。
   値を作らない宣言で、必要な情報は第6章の表に入っている。
   `module` は、平坦化を通っていればここには来ない。 *)

(* globals とインスタンス表への書き込みの記録(§14.16)。journaling が真の間、
   書き込む前の中身を戻す閉包を journal に積む *)
let journaling = ref false

let journal : (unit -> unit) list ref = ref []

let jreplace t k v =
  (if !journaling then
     let old = Hashtbl.find_opt t k in
     journal := (fun () -> match old with Some o -> Hashtbl.replace t k o | None -> Hashtbl.remove t k) :: !journal);
  Hashtbl.replace t k v

(* トップレベルの束縛を、実体の鍵で globals に置く。鍵は束縛ノードごとに別なので、
   同名の再束縛も前の束縛を上書きしない *)
let bind_globals env names_values =
  List.iter (fun (g, v) -> jreplace env.globals g v) names_values;
  env

let exec_decl env ((_, d) as node : T.decl) =
  (* インスタンスの頭の resolve_con は宣言の出身の module と単位のスコープで引くので、
     Decls 側の current_module と current_unit を一時的に立てる *)
  Decls.with_decl_scope (Tree.oid_of node) @@ fun () ->
  match d with
  | T.DLet ((_, b) as bnode) ->
      let v = eval_binding_value env bnode in
      let bound = bind_pat_exn SMap.empty b.T.lb_name v in
      bind_globals env (List.map (fun (n, v) -> (Tree.GDecl (Tree.oid_of bnode, n), v)) (SMap.bindings bound))
  | T.DLetRec bs ->
      (* 群の閉包は globals を共有し、自己参照と相互参照は呼び出し時に実体の鍵で引くので、
         バックパッチは要らない(§14.9) *)
      List.iter
        (fun ((_, b) as bnode : T.let_binding) ->
          let x = match snd b.T.lb_name with T.PVar x -> x | _ -> runtime_error "let rec は名前束縛のみです" in
          jreplace env.globals (Tree.GDecl (Tree.oid_of bnode, x)) (eval_binding_value env bnode))
        bs;
      env
  | T.DExp e ->
      (* 辞書パラメータを持つ式文(制約付きで一般化した構文上の値)は評価しない *)
      (match Tree.get_dict node with Tree.DAbs _ -> () | _ -> ignore (eval env e));
      env
  | T.DInstance i ->
      let cls = Decls.resolve_class (Type.intern i.T.ins_class) in
      (* module の平坦化で作った同義語を通す(BigInt.BigInt など)。組み込みと同じ鍵の
         利用者の宣言は elab が拒否するので、ここに来る宣言は組み込みを差し替えない *)
      let con =
        match i.T.ins_args with
        | [ (_, T.EIdent (LongId comps)) ] -> Decls.resolve_con (Type.intern (String.concat "." comps))
        | [ (_, T.EApply ((_, T.EIdent (LongId comps)), _)) ] -> Decls.resolve_con (Type.intern (String.concat "." comps))
        | _ -> bug "インスタンス頭が解決できません"
      in
      (* 各メソッドは、前提の辞書とメソッド自身の辞書の列を受け取って実装を返す関数にする。
         受け取った辞書を前提の鍵とメソッドの鍵に束縛した環境で束縛を評価し、実装の型の辞書
         パラメータ(own)には adapter の証拠を渡す。前提もメソッド自身の制約も無いメソッドは、
         宣言の実行で 1 回だけ評価する *)
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
        (* 宣言の ABI で表を選ぶ。実装を引く鍵は修飾しない ex_prim で、
           globals に登録する鍵は宣言ノードの実体(GDecl と修飾された ex_name の組)である *)
        match Builtin.find_extern ~abi:ex.T.ex_abi ex.T.ex_prim with
        | Some f -> f
        (* 実装が無くても宣言は通し、呼ばれた時点で落とす。表を引いた鍵は ex_prim なので、
           修飾名と食い違うときは両方を見せる *)
        | None ->
            fun _ ->
              runtime_error
                ("未実装のプリミティブ: " ^ Type.display ex.T.ex_name
                ^ if ex.T.ex_name = ex.T.ex_prim then "" else "(実装名 " ^ ex.T.ex_prim ^ " が見つかりません)")
      in
      (* 制約付きの型パラメータを持つ extern は辞書を受け取って捨てる。実装は OCaml の関数で辞書を使わない *)
      let prim = VPrim { p_name = ex.T.ex_name; p_fn = impl } in
      let v =
        match Tree.get_dict node with
        | Tree.DAbs (_ :: _) -> VDictAbs { da_last = None; da_name = ex.T.ex_name; da_fn = (fun _ -> prim) }
        | _ -> prim
      in
      bind_globals env [ (Tree.GDecl (Tree.oid_of node, ex.T.ex_name), v) ]
  | T.DType _ | T.DNewtype _ | T.DEffect _ | T.DClass _ -> env
  | T.DModule _ -> runtime_error "module の評価は未実装です(M10)"

(* ## 14.14 run

   `run_units` は単位の列(先頭がプレリュード)を順に実行する。
   どの単位も同じ大域の環境の上で実行する。
   値の参照は型検査が木に書いた実体で引き、型やコンストラクタの綴りは単位ごとに別なので、
   別々の単位の同じ名前が実行時に混ざることは無い。
   `run` は単位 1 個の場合である。

   実行は全体を `Builtin.with_runtime`(第13章)の中で走らせる。
   `with_runtime` はランタイムが提供するエフェクトのハンドラで、
   `Console.write` を出力先へ送る。
   ここにも届かなかった操作は `Effect.Unhandled` になり、driver が操作名を含めて報告する。
   プログラムのいちばん外側にハンドラを置き、
   エフェクトを未処理として扱う場所をここ 1 か所に決めている。

   `start_program` は、インスタンス表 `instance_impls` と閉じた辞書の覚え書き `closed_cache` を空にする。
   同じプロセスで `run` を繰り返し呼ぶ場合(第16章の `eval_string`)に、
   前回の実行の痕跡を次の実行に残さないためである。
   痕跡が残ると、同じプログラムの結果が、それより前に何を実行したかに依存する。

   返り値は捨てる。
   暗黙の main は無く、トップレベルの式文は順に実行されるだけで、その値は誰も見ない。 *)

(* 大域の環境を作る。組み込みの値と、その時点で宣言表にあるクラスのメソッドのラッパを置く *)
let start_program () =
  Hashtbl.reset instance_impls;
  Hashtbl.reset closed_cache;
  let globals = Hashtbl.create 512 in
  register_builtin_values globals;
  register_class_methods globals;
  { globals; locals = SMap.empty; resume = None }

(* 単位 1 個の宣言を、前の単位までの大域の環境の上で実行する。
   値の参照は型検査が木に書いた実体で引くので、単位をまたいでも名前は衝突しない *)
let exec_unit env decls = List.fold_left exec_decl env decls

(* 単位の列(プレリュードが先頭)を順に実行する *)
let run_units ~sink units =
  let env = start_program () in
  ignore
    (Builtin.with_runtime ~sink (fun () ->
         ignore (List.fold_left exec_unit env units);
         unit))

let run ~sink decls = run_units ~sink [ decls ]

(* ## 14.15 本章の限界

   ### fiber の上の Stack_overflow

   ハンドラの本体は fiber の上で走る。
   fiber のスタックはヒープ上で伸びるので、暴走した再帰は、
   通常のスタックの上で走る場合より遅れて `Stack_overflow` として現れる。
   先にメモリを使い尽くし、`Out_of_memory` として現れることもある。
   そのため driver(第16章)は、`Stack_overflow` と `Out_of_memory` を同じ終了コード 3 で報告する。
   既定の上限の下では、深い非末尾再帰がどこで落ちるかは環境のメモリ量で変わる。
   そのため、末尾呼び出しが空間を使わないことは、既定の上限の下での完走では確かめられない。
   `test/tail_calls.t` は `OCAMLRUNPARAM=l=100k` でスタックの上限を 102400 語に絞り、
   末尾でない再帰が落ちる回数で、末尾呼び出しと末尾の `resume` が完走することを確かめる。

   ### 残している穴

   ハンドラの外への後送り(re-perform)は、残している穴に数えない。
   仕様は、どの節にも一致しなかった操作を外側のハンドラへ回す規則を持たず(sample.kel:515)、
   第11章の総和性の検査(§11.23)が、すべての節が外れうるハンドラを型検査で拒否するからである。
   同じハンドラの中の節どうしはフォールスルーする。
   後送りの機構と、それを実装しない型の理由は §14.10 にある。

   - 前方参照の値を、定義より前に評価される位置で使うこと。
     パス 1c の署名で型は通るが、`let x = g(1)` の右辺のような、
     即時に評価される位置から前方の `g` を呼ぶと、
     実行はまだ値を持たないので「未束縛の変数」で落ちる。
     この形は、前方参照を遅延束縛で通す設計の代価である。
     黙って誤った値を返すのではなく実行時エラーで止まるので、許容している。
     インスタンス宣言より前の位置でそのインスタンスを使う形も、同じく実行時エラーにしている(§14.7)。

   値の名前は、elab が宣言時点の環境で解決した実体を `resolved` に書き、
   評価器はその実体で引く(§14.4)。
   そのため、同名の再束縛(`let` の後の同名の `let` や `extern`、
   クラスメソッドと同名のトップレベル束縛)でも、
   module の値同義語でも、`--prelude` で差し替えたプレリュードの module の中の名前でも、
   型検査と実行は同じ実体を選ぶ(`test/resolved_names.t`)。

   ### 辞書の費用

   辞書は、型検査が木に書いた証拠を評価して作る(§14.6)。
   辞書パラメータを含まない証拠の辞書は穴ごとに 1 回だけ作り、
   辞書を受け取る値は直前に受け取った辞書の列と結果を覚えるので、
   同じ呼び出し地点を繰り返しても辞書を作り直さない。
   制約付きの多相関数の再帰は、再帰のたびに辞書を局所環境から引いて渡すので、
   単相の関数より遅い。
   辞書パラメータを名前の文字列で引くことがその費用の中心である。

   最後に、本章で外すと気づかれずに壊れるものを並べる。

   1. 起動ごとの `inst` の採番(共有すると、入れ子のハンドラが `Unwind` を横取りする)
   2. resume しなかった場合と例外で脱出した場合の両方での `discontinue`(落とすと資源が漏れる)
   3. 節本体の末尾の背骨にある `Resume` の `continue` を、包みを抜けてから発行すること
      (落とすと perform を含むループが perform のたびに空間を使う。
      ただし引数の評価は包む。包み忘れると資源が漏れる)
   4. 辞書とセレクタのクラスの比較(外すと、辞書の渡し方の誤りが黙って別のメソッドを呼ぶ)
   5. `let` による評価順序の固定(外すと観測できる意味論が変わる) *)

(* ## 14.16 対話的な実行

   対話的な実行(第16章)は、プレリュードを 1 回だけ実行し、その後は入力ごとに宣言を実行する。
   `start_session` は globals を作ってプレリュードを実行し、セッションを返す。
   `exec_input` は 1 入力分の宣言を `with_runtime` の中で実行し、表示する(名前、式か実体、値)の列を
   `show` に渡す。
   `show` も `with_runtime` の中で呼ぶ。
   表示が Show のインスタンスを呼んで実行時エラーになったら、その入力ごと取り消すためである。
   `with_runtime` を入力ごとに呼ぶのは、継続が入力の境界をまたがないからである。
   `handle` は式で、トップレベルの `with` も入力の末尾で閉じる。
   `inst` の採番は大域の `new_oid` なので、`with_runtime` を何度呼んでも衝突しない。

   実行時エラーで落ちた入力は、入力の単位で戻す。
   `exec_input` は、globals とインスタンス表への書き込みを `jreplace` で記録し、
   例外で落ちたら記録を逆順に戻し、環境を入力の前に戻して、例外を投げ直す。
   解決のキャッシュ 2 つは空にする(キャッシュなので、空にしても意味は変わらない)。
   出力と、Ref や可変配列の中身の書き換えは戻さない。

   後の入力で宣言したクラスには、
   `start_session` の `register_class_methods` がラッパを置いていない。
   そこで `DClass` を実行するときに、そのクラスのメソッドのラッパを `GMethod` の鍵で置く。
   鍵はクラスごとに別なので、先にある同名の値を覆わない(§14.12)。 *)
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
        (* 辞書パラメータを持つ式文は評価せず、辞書を受け取る値として表示する(<fn>) *)
        let v =
          match Tree.get_dict node with
          | Tree.DAbs ks -> VDictAbs { da_last = None; da_name = "_"; da_fn = (fun ds -> eval (bind_dicts env ks ds) e) }
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
        (* 結果の表示も実行時の中で行う。表示が呼ぶ Show のインスタンスが実行時エラーを
           出したら、この入力の書き込みと一緒に取り消す *)
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
