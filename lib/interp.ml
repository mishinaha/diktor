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
   エフェクトハンドラ(§14.10)と、型クラスの実行時ディスパッチ(§14.6 と §14.7)である。
   前者は Keleut の意味論を OCaml 5 の `Effect.Deep` に写す部分で、
   後者は elab が選んだのと同じインスタンスを、実行時にもう一度選ぶ部分である。
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
   ディスパッチ(§14.6〜§14.8)、束縛(§14.9)、ハンドラ(§14.10)、
   トップレベル(§14.11〜§14.14)の順に述べる。 *)
open Aux
open Syntax
open Value
module T = Tree.Tree

(* ## 14.1 実行時に引く 2 つの表

   Keleut の型クラスは辞書渡しをしない。
   呼び出し地点に辞書を通す代わりに、実行時に値のタグでインスタンスを引く。
   そのために要るのは、この `user_instances` と、第13章の組み込みのメソッド表だけである。

   引き方は `(クラス, 型構成子) → メソッド名 → 値` である。
   型構成子は第1章のインターン表の oid で、型の側と同じ番号を使う。 *)

(* 利用者が宣言したインスタンスのメソッドの実体。(クラス, 型構成子) → メソッド名 → 値 *)
let user_instances : (oid * oid, (oid * Value.t) list) Hashtbl.t = Hashtbl.create 32

(* dispatch の解決のキャッシュ。(クラス, 型構成子, メソッド) → 実装。
   見つからなかったこと(None。構造的導出へ進む)も覚える。
   user_instances に書き込むのは exec_decl の DInstance の 1 か所だけで、
   そこで必ずこの表を無効化する。
   書き込む箇所を 1 か所に保つことが、この表の正しさの前提である。
   無効化が漏れると、宣言の順序によって結果が変わる *)
let resolution_cache : (oid * oid * oid, (Value.t -> Value.t) option) Hashtbl.t = Hashtbl.create 64

(* dispatch_positions の結果のメモ。(クラス, メソッド) → 候補の位置。
   スキーマは宣言の後は変わらないので、無効化するのは run の初期化だけでよい *)
let positions_cache : (oid * oid, int list) Hashtbl.t = Hashtbl.create 64

(* `tycon_of_value` はディスパッチの入口で、値から名目的な型の名前を 1 つ取り出す。
   `VRecord` と `VVariant` が `None` になるのは、レコードとヴァリアントが構造的な型で名前を持たず、
   名目的なインスタンス表を引く鍵にならないからである。
   ここで `None` になった値は、§14.7 の構造的導出へ回る。
   `VClosure` と `VPrim` も、関数にはインスタンスが付かないので `None` になる。 *)

let tycon_of_value = function
  | VBool _ -> Some (Type.intern "Boolean")
  | VInt32 _ -> Some (Type.intern "Int32")
  | VInt64 _ -> Some (Type.intern "Int64")
  | VFloat64 _ -> Some (Type.intern "Float64")
  | VText _ -> Some (Type.intern "String")
  | VData d -> Some d.d_type
  | VRef _ -> Some (Type.intern "Ref")
  | VArray _ -> Some (Type.intern "Array")
  | VMutArray _ -> Some (Type.intern "MutableArray")
  | VRecord _ | VVariant _ | VClosure _ | VPrim _ -> None

(* `cancel_log` は、cancel 節で抑制した例外の行き先である。
   仕様 sample.kel:581 は、cancel 節について次のように定めている。
   「cancel 節から外へは脱出できない。例外に相当するものが起きるとその cancel 節は打ち切るが、
   脱出は抑制してログに記録し、外側の後始末を続ける」。
   ライブラリが stderr に直接書かないよう、関数を 1 段はさみ、driver(第16章)がそれを差し替える。 *)

(* cancel 節の中の例外を記録する関数(sample.kel:581)。driver が差し替える *)
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
   包まないと、OCaml の生の例外が driver の終了コードの規約(第16章)を素通りする。 *)

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

   - `Ident` は 4 段階で引く。
     locals(不変の Map)、globals(可変の Hashtbl)、
     module の平坦化で作った値同義語(globals に無かったときだけ)、
     引数のないコンストラクタの順である。
     globals は可変で、名前を呼び出し時に引くので、トップレベルの相互参照と前方参照が、
     追加のコードなしで通る(第12章の環境の二層構造)。
     同名の再束縛と、この呼び出し時の名前引きを両立させる仕組みは、§14.13 の版の複製である。
   - `BinOp` は第7章(prims.ml)の表を引くだけである。
     `&&` と `||` だけは、短絡して右辺を評価しないことがあるので、型クラスにできない。
     `!=` は `Eq.eq` の否定として同じ表に入っている。
   - `Match` では、節のガードが偽なら次の節へ進む。
     `try_clauses` は末尾再帰で、節本体の `eval` も末尾位置にある(規約 1)。
     ハンドラの操作節も同じ規則で、
     パターンが一致しないときもガードが偽のときも次の節へ進む(§14.10)。
   - `Perform` は、elab が `resolved` に書いた完全な操作名の oid をそのまま使う。
     修飾なしで書いた操作名の解決(行の最左優先)は型検査で済んでおり、実行時に名前を探すことはない。
   - `Resume` は、継続を消費する前に引数を評価する。
     節本体が `{ … ; resume(f()) }` のように `Resume` そのものでない形のとき、
     `f` が例外で脱出すれば、resume は未消費のまま節の例外の経路(§14.10 の discontinue)に乗る。
     順序を入れ替えると、消費済みの継続を捨てることになる。
     節本体が `resume(…)` そのもののときは §14.10 の末尾 resume 最適化に乗るが、
     その経路でも引数の評価は包んであり、例外なら discontinue する。
   - `Run` は、実行時には恒等写像である。
     `run h { … }` の `h` は型の上にしか存在せず、
     リージョンの安全性は第11章の剛定数とレベルが保証している。
     操作を持たないエフェクトラベル(`Heap`、`Blocking`、`Fs`)には、実行時の処理が何も無い。
     `Run` は、実行時に何もしないもののいちばん目立つ例である。
     `Blocking` を落とす組み込み関数 `pinned` も、実行時には渡された関数を呼ぶだけである(§14.11)。
     型で守り切れた性質を、実行時に検査し直すことはしない。 *)

let rec eval env ((_, e) as node : T.exp) : Value.t =
  match e with
  | T.Bool b -> VBool b
  | T.Text s -> VText s
  | T.Number n -> number_value node n (* 評価器が elab の型を読む唯一の場所(§14.3) *)
  | T.Hole -> runtime_error "??? に到達しました"
  | T.Ident li -> (
      let name = show_long_id li in
      match SMap.find_opt name env.locals with
      | Some v -> v
      | None -> (
          match Hashtbl.find_opt env.globals name with
          | Some v -> v
          | None -> (
              (* module スコープの値同義語。elab と同じく、見つからなかったときだけの
                 フォールバックで、引けるのはこの閉包が属する module の同義語だけ *)
              match
                Option.bind
                  (match env.mod_scope with
                  | Some m -> Hashtbl.find_opt Decls.module_val_synonyms (m, Type.intern name)
                  | None -> None)
                  (fun q -> Hashtbl.find_opt env.globals (Type.name_of q))
              with
              | Some v -> v
              | None -> (
                  (* 裸の引数なしコンストラクタ *)
                  match Tree.get_resolved node with
                  | Some (Tree.RCtor (d, c, _)) -> VData { d_type = d; d_ctor = c; d_fields = [||] }
                  | _ -> runtime_error ("未束縛の変数: " ^ name)))))
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
          (* 短絡評価(sample.kel:368) *)
          match op with
          | And -> if Builtin.as_bool (eval env l) then eval env r else VBool false
          | Or -> if Builtin.as_bool (eval env l) then VBool true else eval env r
          | _ -> bug "OpBool")
      | Prims.OpMethod (cls, m) ->
          let vl = eval env l in
          let vr = eval env r in
          dispatch cls m (VRecord [ (Type.l_item, vl); (Type.l_item, vr) ])
      | Prims.OpMethodNot (cls, m) ->
          let vl = eval env l in
          let vr = eval env r in
          VBool (not (Builtin.as_bool (dispatch cls m (VRecord [ (Type.l_item, vl); (Type.l_item, vr) ])))))
  | T.Not e -> VBool (not (Builtin.as_bool (eval env e)))
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
  | T.Resume arg -> (
      match env.resume with
      | None -> runtime_error "resume は操作節の中でのみ使えます"
      | Some r ->
          (* 引数を先に評価する。節本体が Resume そのものでない形なら、引数の評価中に
             起きた例外で、resume は未消費のまま節の例外の経路(discontinue)に乗る。
             節本体が Resume そのもののときは eval_handle の末尾 resume 最適化が
             処理するので、この分岐は走らない *)
          let v = match arg with Some e -> eval env e | None -> unit in
          if not r.r_alive then runtime_error "resume を節の外で呼び出しました(second-class)"
          else if r.r_used then runtime_error "resume は高々1回しか呼べません(アフィン)"
          else (
            r.r_used <- true;
            Effect.Deep.continue r.r_k v))
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
  | v -> runtime_error ("関数ではない値を適用しました: " ^ show v)

(* ## 14.6 ディスパッチに使う引数の位置

   辞書渡しをしない実装では、どの値のタグでインスタンスを選ぶかを、実行時に決めなければならない。
   引数を左から見て、最初にインスタンスを持つ値で決めるという素朴な方法は、誤りである。
   次の例がその反例になる。

   ```keleut
   type class Pick[A] { val pick: (Int32, A) => Int32 }
   type instance Pick[Int32]  { let pick(n, a) = a }
   type instance Pick[String] { let pick(n, a) = n }
   let s: String = ...    // 何か String の値
   pick(0, s)
   ```

   左から走査すると、第 1 引数の `Int32` に `Pick[Int32]` が当たり、実行時は `Pick[Int32]` を選ぶ。
   一方、elab はクラスパラメータ `A` の位置で解決するので、`Pick[String]` を選ぶ。
   型検査と実行が別のインスタンスを選ぶので、コヒーレンスが実行時に破れる。

   正しい規約は、クラスパラメータが頭に現れる引数の位置だけで選ぶことである。
   `dispatch_positions` は、メソッドのスキーマ(Generic の印が付いたもの)の引数レコードを走査し、
   型適用の背骨(`app_spine`)の頭がそのクラスパラメータである位置を集める。
   elab 側の `register_class` は、宣言の時点で、
   少なくとも 1 つの引数の頭にパラメータが現れることを要求する。
   `(List[A]) => …` のように、パラメータが引数の内側にしか現れないメソッドの宣言は拒否する。
   宣言を受理する側と実行する側が、まったく同じ述語を見ている。
   上の `Pick` の例の回帰テストは、`test/verify_fixes.t` の pick.kel である。

   位置が 1 つも取れなかったときは、すべての引数を走査する。
   ただし、この分岐には現状では到達しない。
   組み込みのクラス(Add、Sub、Mul、Div、Eq、Ord、Show)のスキーマは、
   どれも引数の頭がクラスパラメータそのものである。
   メソッドを持たない Integral と Fractional は、そもそも dispatch されない。
   利用者が宣言したクラスには、上の受理検査が同じ形を強制する。
   この分岐を残してあるのは、安全側の判断である。
   スキーマが想定外の形になったとき、候補を狭めるより広げるほうが、
   「インスタンスが見つかりません」で落ちにくい。 *)

(* メソッドのスキーマから、クラスパラメータが頭に現れる引数の位置を求める。
   ディスパッチはこの位置だけで行う(elab.ml の register_class と同じ規約)。
   これを守らないと、pick: (Int32, A) => Int32 が第 1 引数の Int32 で誤ってディスパッチし、
   elab の解決と食い違う *)
and dispatch_positions ci meth =
  let is_param t =
    match Type.repr (fst (Type.app_spine t)) with
    | Type.TVar r -> ( match !r with Type.Generic i -> i.Type.vid = ci.Decls.ci_param.Type.vid | _ -> false)
    | _ -> false
  in
  match List.assoc_opt meth ci.Decls.ci_methods with
  | Some scheme -> (
      match Type.repr scheme with
      | Type.TArrow (args, _, _) -> (
          match Type.repr args with
          | Type.TRecord row ->
              fst (Type.row_fields row)
              |> List.mapi (fun i (_, t) -> (i, t))
              |> List.filter_map (fun (i, t) -> if is_param t then Some i else None)
          | _ -> [])
      | _ -> [])
  | None -> []

(* ## 14.7 dispatch の探索順序とフォールバック

   候補の位置の値を左から見て、最初に実装が見つかった値でメソッドを決める。
   1 つの値について引く順序は、利用者が宣言したインスタンス、組み込みのメソッド表の順である。
   利用者の宣言が組み込みの鍵を奪えないことは、§14.13 で別に保証する。

   どこにも無ければ、構造的導出へ進む。
   Diktor が構造的に導出するのは `Eq` だけで、
   クラス宣言に付いた `derive structural` が、そのクラスの構造的導出を有効にする。
   仕様は構造的な型へのインスタンスについて「利用者には書かせない。コヒーレンスを守るため、
   組み込みの自動導出だけがインスタンスを与える」と定め(sample.kel:383)、
   導出が閉じた行にしか効かないことも定めている(sample.kel:391-395)。

   ここでは次の不変条件が効いている。
   elab 側(第8章(unify.ml))は、構造的導出を閉じた行のレコードとヴァリアントにしか適用しない。
   それ以外の型に `Eq` が要求されればインスタンス表を引き、無ければ型エラーにする。
   そのため、型検査を通ったプログラムでこの分岐に来る値は、
   レコードかヴァリアント(`tycon_of_value` が `None` を返す値)に限られ、
   実行時の選択が elab の判定と一致する。

   ただし、名目型の値がこの分岐に来る場合が 1 つだけある。
   利用者のインスタンスを、その宣言より前の位置で使う場合である。
   型検査はパス 1c でインスタンス表を揃えてから本体を見るので、宣言の順序を問わない。
   一方、実行は宣言の順に `user_instances` へ書くので、その時点ではまだ実体が無い。
   ここで名目型の値を黙って構造的等価に落とすと、同じ式が宣言の前と後で違う値を返す。
   そこで、elab の表にはインスタンスがあるのに実行の表には無い値を見つけたら、
   構造的導出へ進む前に実行時エラーにする(`test/verify_fixes.t` の instorder)。
   黙って誤った値を返すより、エラーで止めるほうを選ぶ点で、
   §14.15 の前方参照の値の扱いと同じ判断である。

   上の不変条件から、ここで「インスタンスが見つかりません」が出たら、誤りは実行時の側ではなく、
   型検査の側か表の登録の側にある。

   実行時ディスパッチが正しいのは、探索の方法によるのではなく、
   コヒーレンスが保証されているからである。
   そのため、探索の結果を覚えても意味は変わらない。
   結果を覚える表は 2 つある。
   `resolution_cache` は解決の結果(None も含む)を、`positions_cache` は候補の位置を覚える。
   無効化する箇所は 2 つだけである。
   `run` の冒頭の初期化と、`exec_decl` の `DInstance` の登録で、
   後者は `resolution_cache` を空にする。
   `user_instances` に書き込む箇所を 1 か所に保つことが、
   `resolution_cache` の正しさの前提である。 *)

and dispatch cls_name meth args =
  let cls_oid = Type.intern cls_name in
  let meth_oid = Type.intern meth in
  let vals = Builtin.arg_values args in
  let cand_vals =
    match Decls.find_class cls_oid with
    | Some ci -> (
        let ps =
          match Hashtbl.find_opt positions_cache (cls_oid, meth_oid) with
          | Some ps -> ps
          | None ->
              let ps = dispatch_positions ci meth in
              Hashtbl.replace positions_cache (cls_oid, meth_oid) ps;
              ps
        in
        match ps with
        | [] -> vals (* 位置が取れなければすべてを走査する(現状は到達しない安全側の保険) *)
        | ps -> List.filteri (fun i _ -> List.mem i ps) vals)
    | None -> vals
  in
  let find_impl v =
    match tycon_of_value v with
    | Some con -> (
        (* 解決の結果はキャッシュを通して引く。コヒーレンスが保証されていて、
           正しさが探索の方法に依らないので、結果を覚えても意味は変わらない *)
        match Hashtbl.find_opt resolution_cache (cls_oid, con, meth_oid) with
        | Some r -> r
        | None ->
            let r =
              match Hashtbl.find_opt user_instances (cls_oid, con) with
              | Some methods -> (
                  match List.assoc_opt meth_oid methods with Some f -> Some (fun args -> apply f args) | None -> None)
              | None -> Builtin.builtin_method cls_name (Type.name_of con) meth
            in
            Hashtbl.replace resolution_cache (cls_oid, con, meth_oid) r;
            r)
    | None -> None
  in
  match List.find_map find_impl cand_vals with
  | Some f -> f args
  | None -> (
      (* 名目型の値がここへ来るのは、その `(クラス, 型構成子)` の利用者のインスタンスが、
         宣言より前の位置で使われたときだけである。型検査はパス 1c で表を揃えるので
         この使用を通す。一方、実行は宣言の順に user_instances へ書くので、この時点では
         まだ実体が無い。黙って構造的等価へ落とすと、同じ式が宣言の前と後で違う値を
         返すので、実行時エラーにする(§14.15 の前方参照と同じ判断) *)
      (match List.find_map tycon_of_value cand_vals with
      | Some con when Decls.find_instance ~cls:cls_oid ~con <> None ->
          runtime_error
            (cls_name ^ "[" ^ Type.name_of con ^ "] のインスタンスは宣言より前の位置では使えません(実行はまだ実体を持ちません。インスタンス宣言を使用より前に置いてください)")
      | _ -> ());
      (* 構造的導出(Diktor は Eq だけを導出する)。コヒーレンスにより elab の選択と一致する *)
      let structural = match Decls.find_class cls_oid with Some ci -> ci.Decls.ci_derive_structural | None -> false in
      match (structural, meth, vals) with
      | true, "eq", [ a; b ] -> VBool (structural_eq a b)
      | _ ->
          runtime_error
            (cls_name ^ "." ^ meth ^ " のインスタンスが見つかりません: "
            ^ String.concat ", " (List.map show vals)))

(* ## 14.8 構造的等価

   `{p = 1, q = 2}` と `{q = 2, p = 1}` は同じ値である。
   行の型は最左一致で決まる一方、異なるラベルの間には順序が無い。
   そのため、値のフィールドのリストを前から突き合わせる比較は誤りである。
   正しい手順では、左辺のレコードのフィールドを順に取り、
   右辺のレコードから同名のフィールドのうち最も左のものを取り出して消していく。
   最後に右辺が空になれば一致である(右辺に余分なフィールドがあれば、ここで不一致になる)。

   フィールドの比較は、直接の再帰ではなく `value_eq`(つまり `dispatch Eq.eq`)に通す。
   フィールドに利用者定義の `Eq` を持つ newtype があるとき、
   宣言されたインスタンスを無視して構造をのぞき込まないためである。

   引数レコードに `_item` が 2 つ並ぶのは、Scoped Labels がラベルの重複を許すからである。
   ラベルの重複を許すことが、そのまま多引数の表現になっている。

   関数どうしの比較は、実行時エラーにする。
   Float64 の比較は `__float64_eq` に委ねるので、IEEE の意味論(NaN ≠ NaN)がそのまま出る。 *)

and value_eq a b = Builtin.as_bool (dispatch "Eq" "eq" (VRecord [ (Type.l_item, a); (Type.l_item, b) ]))

(* レコードは、左辺のフィールドを順に取り、
   右辺から同名のフィールドのうち最も左のものを取り出して消す。
   異なるラベルの間の物理的な順序は値によって違いうるので、単純な順序比較は誤りである *)
and structural_eq a b =
  match (a, b) with
  | VRecord fs1, VRecord _ ->
      let rec go fs1 rv =
        match fs1 with
        | [] -> record_fields rv = [] (* 右辺に余りがあれば不一致 *)
        | (l, x) :: rest -> (
            match record_take rv l with
            | y, rv' -> value_eq x y && go rest rv'
            | exception Runtime_error _ -> false)
      in
      go fs1 b
  | VVariant (l1, p1), VVariant (l2, p2) -> l1 = l2 && value_eq p1 p2
  | VData d1, VData d2 ->
      d1.d_type = d2.d_type && d1.d_ctor = d2.d_ctor
      && Array.length d1.d_fields = Array.length d2.d_fields
      && Array.for_all2 (fun x y -> value_eq x y) d1.d_fields d2.d_fields
  | (VClosure _ | VPrim _), _ | _, (VClosure _ | VPrim _) -> runtime_error "関数は比較できません"
  | _ -> value_eq a b

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
   globals が(同じ版を見る閉包の間では)共有の可変な表で、
   名前の解決が呼び出し時に起きるからである。 *)

and eval_binding_value env ((_, b) : T.let_binding) =
  match b.T.lb_params with
  | Some ps -> VClosure { c_env = env; c_params = ps; c_body = b.T.lb_body }
  | None -> eval env b.T.lb_body

and eval_binding env ((_, b) as bnode : T.let_binding) =
  let v = eval_binding_value env bnode in
  bind_pat_exn env.locals b.T.lb_name v

and eval_rec_bindings env (bs : T.let_binding list) =
  (* クロージャの生成 → 環境の構築 → c_env のバックパッチ *)
  let closures =
    List.map
      (fun ((_, b) : T.let_binding) ->
        let name = match snd b.T.lb_name with T.PVar x -> x | _ -> runtime_error "let rec は名前束縛のみです" in
        let c =
          match b.T.lb_params with
          | Some ps -> { c_env = env; c_params = ps; c_body = b.T.lb_body }
          | None -> (
              match snd b.T.lb_body with
              | T.Lambda { l_params; l_body } -> { c_env = env; c_params = l_params; c_body = l_body }
              | _ -> runtime_error "let rec の右辺は関数でなければなりません")
        in
        (name, c))
      bs
  in
  let locals = List.fold_left (fun locals (n, c) -> SMap.add n (VClosure c) locals) env.locals closures in
  List.iter (fun (_, c) -> c.c_env <- { env with locals }) closures;
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
   仕様(sample.kel:568-581)は defer 構文を持たず、後始末をハンドラの cancel 節に書くと定めている。
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

   ### 末尾 resume 最適化

   上の 3 つの経路を判定するには、節の評価を `match … with exception` で包む必要がある。
   この包みがあると、`continue` が `effc` の末尾式でなくなる。
   継続の発行が末尾でないと、perform のたびにスタックが伸びる。
   fiber のスタックは伸長できるので Stack_overflow にはならないが、
   perform の回数が増えるほど大幅に遅くなる。

   `case op(x) => resume(…)` の形の節は多く、プレリュードのハンドラ(`with_stdout`)もこの形である。
   そこで、節本体が構文上 `Resume` そのものであれば、
   節本体全体を包んで終わり方を判定する処理を省き、
   `Effect.Deep.continue k v` を末尾で発行する。
   `test/eval.t` の「10 万回の println」がこの経路の回帰テストで、
   最適化が外れると実行時間で気づける。
   この最適化は、性能の改善というより、実用上の必要条件である。

   この速い経路も、3 つの経路の規約を守る。
   `match … with exception` が覆うのは引数の評価だけである。
   引数が例外で脱出したら、通常の経路と同じく `discontinue` する。
   引数の評価を包まないと、`resume(???)` の形で、
   捨てた継続の cancel 節も自分の cancel 節も走らない。
   回帰テストは `test/eval.t` の tailresume.kel である。

   包むのが引数の評価だけなので、`continue` は値の枝、
   つまり例外を捕まえる範囲(trap)を抜けた後にあり、末尾での発行が保たれる。
   OCaml は、値の場合の枝を trap の外に置いてコンパイルする。
   引数の評価だけを包む形は、包まない形と実行時間もメモリも変わらない。
   一方、`continue` を trap の内側に置くと、大幅に遅くなる。

   ### アフィンな resume と second-class

   `r_used` はアフィン性(高々 1 回)を、`r_alive` は second-class(節の外へ持ち出さない)を、
   実行時に検査するための印である。
   OCaml も 2 度目の `continue` で `Continuation_already_resumed` を投げるが、
   それでは Keleut のエラーとして説明にならないので、先に自前で検査して日本語のメッセージを出す。
   second-class の検査は 2 段構えで、実行時の `r_alive` はその片方である。
   もう片方は、節本体のラムダの中に `resume` があれば拒否する構文検査で、elab にある。

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

   cancel 節の中の例外をすべて抑制してログに記録するのは、仕様(sample.kel:581)の規則である。
   既知の例外(`Runtime_error`、`Unwind`、`Sys_error`)は日本語のメッセージにし、
   それ以外の例外は `Printexc.to_string` で文字列にしてからログに渡す。

   `retc` と `run_cancel` が `cl_guard` を読まないのは、
   elab が return 節と cancel 節のガードを拒否するからである(§11.24)。

   ### 操作節の選択

   操作節はソースの順に試し、パターンが一致しないときもガードが偽のときも次の節へ進む。
   これは §14.2 の match とまったく同じ規則である。
   ガードは resume の無い環境で評価する(ガードから継続は見えない。§11.24)。
   すべての節が外れたときは、`discontinue` で実行時エラーにする。
   elab の総和性検査は、各操作について、ガードが無く反駁できない節を 1 つ要求する(§11.24)。
   この検査を通っていれば、この分岐には到達しない。
   この分岐は防御のために残してある。
   素の raise にしないのは、3 つの経路の規約どおり、捨てた継続の cancel 節を走らせるためである。

   Diktor は、ハンドラの外への後送り(re-perform)を実装していない。
   機構としては実装できる。
   `effc` のハンドラ関数は fiber の外で走るので、そこから `Effect.perform` すれば、
   自分を飛ばして外側のハンドラに届く。
   実装しないのは型の都合である。
   handle の型付けは対象のエフェクト E を行から消すので(§11.24)、
   ガードが偽の `E.op` を外へ流すと、E を持たない行の文脈に操作が漏れ、型が実行と合わなくなる。
   仕様は行の部分型付け(サブエフェクティング)を持たないので(sample.kel:473)、
   E を消す型付けと、E の操作を外へ流す実行を両立させる手段がない。 *)

and eval_handle env body clauses =
  (* inst は Handle ノードを評価するたびに採番する(入れ子に起動したハンドラが、
     外側宛ての Unwind を自分宛てと取り違えないため) *)
  let inst = new_oid () in
  let op_clauses =
    List.filter_map
      (fun (cl : T.clause) ->
        match Tree.get_resolved cl with Some (Tree.ROp op) -> Some (op, cl) | _ -> None)
      clauses
  in
  let ret_clause = List.find_opt (fun cl -> Tree.get_resolved cl = Some Tree.RReturnClause) clauses in
  let cancel_clause = List.find_opt (fun cl -> Tree.get_resolved cl = Some Tree.RCancelClause) clauses in
  let run_cancel () =
    match cancel_clause with
    | None -> ()
    | Some (_, c) -> (
        (* cancel 節の中の例外は抑制してログに記録する(sample.kel:581) *)
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
                        | (_, ((_, c) : T.clause)) :: rest -> (
                            match bind env.locals (clause_arg_pats c) fields with
                            | None -> select rest
                            | Some locals -> (
                                match c.T.cl_guard with
                                | None -> Some (locals, c)
                                | Some g ->
                                    if Builtin.as_bool (eval { env with locals; resume = None } g) then
                                      Some (locals, c)
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
                            (Runtime_error ("handle のどの節にも一致しません: " ^ Type.name_of op ^ show args))
                      | Some (locals, c) -> (
                          match snd c.T.cl_body with
                          | T.Resume arg -> (
                              (* 末尾 resume 最適化(§14.10)。exception 節が覆うのは
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
                          | _ -> (
                              let r = { r_k = k; r_used = false; r_alive = true } in
                              match eval { env with locals; resume = Some r } c.T.cl_body with
                              | v ->
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
   分けているのはディスパッチのタグ(§12.1 の表)と印字を別にするためで、
   実行時の動作が違うからではない。
   同じコンストラクタを共用すると、可変配列の値が `Array` のタグで表を引いてしまう。
   たとえば、前提つきのインスタンス `type instance[A: Show] Show[Array[_]]` は宣言できるので、
   タグを共用すると、可変配列の値がこのインスタンスに当たる。
   なお、`MutableArray` 側のインスタンスは、宣言できても使う位置で落ちる。
   その理由は `run` の剛定数に制約が無いことで、タグの区別とは関係がない。

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
  let reg n f = Hashtbl.replace globals n (VPrim { p_name = n; p_fn = f }) in
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
  (* par と par_map。逐次実装が並列実行と観測上同値である根拠は、スケジューラが
     無いことではなく、コールバックの行が @ {} に閉じていることにある。コールバックは
     Heap も Console も Async も起こせないので、実行順序を観測できない(§6.11b)。
     並列に実行した場合と違うのは 1 点だけで、コールバックが例外で脱出したとき、
     逐次実装では後続を評価しない(素の OCaml と同じ)。
     par_map の返り値は不変の Array[B] で、可変配列とは型が違う。
     決定性は型が守り、その根拠は次の 3 つである。可変配列は h を型に持つので、
     @ {} のコールバックからは触れない。入れ子の矢印で @ を省略すると @ {} と読むので、
     高階の位置でエフェクトを隠す形が書けない(test/annot_rows.t の launder)。
     ファイルを扱うプリミティブは @ Fs を持つ(test/fs_effect.t) *)
  reg "par_map" (fun args ->
      match Builtin.arg_values args with
      | [ VArray a; f ] ->
          (* 適用の順序は添字 0 から明示的に固定し、Array.map の適用順に任せない。
             par の左から右と同じく、逐次実装の意味論は順序も含めて固定する(規約 2) *)
          let n = Array.length a in
          if n = 0 then VArray [||]
          else (
            let out = Array.make n unit in
            for i = 0 to n - 1 do
              out.(i) <- apply f (VRecord [ (Type.l_item, a.(i)) ])
            done;
            VArray out)
      | _ -> runtime_error "par_map の引数が不正です");
  reg "par" (fun args ->
      match Builtin.arg_values args with
      | [ fa; fb ] ->
          (* 左から評価する。OCaml の未規定の評価順に任せない(規約 2) *)
          let va = apply fa unit in
          let vb = apply fb unit in
          VRecord [ (Type.l_item, va); (Type.l_item, vb) ]
      | _ -> runtime_error "par の引数が不正です");
  (* pinned は恒等関数として実装する。Diktor が Blocking について守る観測できる
     契約は、並列度を減らさないことと、キャンセルの配送点にならないことの 2 つである。
     Diktor はタスクを 1 つしか持たず(Async の操作はすぐに継続を再開する)、配送点は
     yield_ だけなので、恒等関数がどちらの契約も満たす。スケジューラを持たないので、
     専用のスレッドへの束縛も行わない。Blocking はトップレベルに残せる(仕様 §12)ので、
     pinned を通さないプログラムも実行できるが、ランタイムが受け取るものは何も無い *)
  reg "pinned" (fun args -> apply (Builtin.arg1 args) unit)

(* ## 14.12 クラスメソッドの識別子参照

   `eq(a, b)` や `show(x)` のようなメソッドの識別子参照のために、
   `dispatch` を呼ぶだけのラッパの prim を globals に置く。
   ラッパは呼ばれた時点で表を引くので、インスタンス宣言との前後関係を気にしなくてよい。

   登録する名前は、非修飾名と修飾名の両方である。
   `map` でも `Functor.map` でも引ける。
   同名のメソッドを持つクラスが 2 つあると、非修飾名をどちらのクラスが取るかで衝突する。
   この衝突は、宣言時に elab が拒否する(§11.33)。
   衝突を受理すると、型検査と実行が別のクラスを選びうる。
   elab の非修飾名の解決と、ここでの登録の順序が一致する保証がないからである。

   下の実装が、走査の結果をクラス名でソートしてから登録するのは、念のためである。
   クラスどうしの衝突は elab が拒否するので起きないが、
   ハッシュ順に由来する非決定性は観測に漏れうるので、表の走査に残さない。

   ただし、elab の拒否が守るのはクラスどうしの衝突だけである。
   クラスメソッドと同名のトップレベル束縛(プレリュードの `let` や `extern` を含む)は、
   この登録より後に globals に入り、ここで置いたラッパを覆う。
   このとき §14.13 の版の複製が働く。
   再束縛の時点で表が分かれ、それより前に作られた閉包は、古い表のラッパを見続ける。
   elab 側も同じ規則である。
   パス 1b と 1c の非修飾名の登録は先勝ちで、
   後から来た同名の束縛は既存の環境を上書きしない(第11章 §11.33、§11.36)。
   両者とも、最初にその名前を持った側が非修飾名の勝者になるので、
   どの呼び出し地点でも elab と実行が同じ実体を選ぶ。 *)

(* クラスメソッドの識別子参照は、dispatch を呼ぶラッパで処理する *)
let register_class_methods globals =
  Hashtbl.fold (fun _ ci acc -> ci :: acc) Decls.classes []
  |> List.sort (fun (a : Decls.class_info) b -> compare (Type.name_of a.Decls.ci_name) (Type.name_of b.Decls.ci_name))
  |> List.iter (fun (ci : Decls.class_info) ->
         let cls_name = Type.name_of ci.Decls.ci_name in
         List.iter
           (fun (m, _) ->
             let wrapper = VPrim { p_name = cls_name ^ "." ^ m; p_fn = (fun args -> dispatch cls_name m args) } in
             Hashtbl.replace globals m wrapper;
             Hashtbl.replace globals (cls_name ^ "." ^ m) wrapper)
           ci.Decls.ci_methods)

(* ## 14.13 宣言の実行

   トップレベルの `let` と `let rec` は、globals に直接置く。
   バックパッチが要らないのは、§14.9 で述べたとおりである。

   本章でインスタンス表(`user_instances`)に書き込むのは、`type instance` の処理だけである。
   この処理では、次の 2 点に注意している。

   1 つ目は、同義語の表を引くことである。
   第11章の `flatten_modules` は、型検査の前に module を平坦化し、
   `module BigInt { newtype BigInt … }` の型を `BigInt.BigInt` に改名する。
   インスタンスの頭に書かれた非修飾名をそのまま鍵にすると、宣言した実体が実行時に見つからない。
   そこで `Decls.resolve_con` に通して、elab と同じ名前にそろえる。
   同義語は module ごとのスコープを持つので、
   `exec_decl` の冒頭で宣言の出身 module を `Decls.current_module` に立ててから引く。
   これは elab の `with_decl_module` と同じ規律である。
   回帰テストは `test/verify_fixes.t` の modinst.kel である。

   2 つ目は、組み込みのインスタンスを差し替えないことである。
   利用者が `type instance Add[Int32]` を再宣言して実体を差し替えると、
   elab は組み込みの `Add[Int32]` で型検査するのに、実行時だけ利用者の実体が使われる。
   そこで、組み込みクラスの組み込みの鍵と同じ `(cls, con)` を持つ宣言は、
   受理したうえで実体を差し替えない。

   `extern` は、実装が無ければ、呼ばれた時点で落ちる prim を登録する。
   宣言だけして呼ばないプログラムを通すためである。
   同名の extern どうしで嘘の型を再宣言することは、elab が拒否する(登録簿が効く範囲は §6.2)。

   `DLet` と `DExtern` の分岐は、既存の globals と同名の束縛を、次の `bind_globals` で扱う。
   既存の globals には、先行する `let` や、組み込みクラスメソッドの修飾名が含まれる。
   トップレベルで同名の束縛を再び宣言したときに素の `Hashtbl.replace` で上書きすると、
   型検査と実行が別の実体を選びうる。

   `type`、`newtype`、`effect`、`type class` は、実行時には何もしない。
   値を作らない宣言で、必要な情報は第6章の表に入っている。
   `module` は、平坦化を通っていればここには来ない。 *)

(* トップレベル束縛の、呼び出し時の名前引きと宣言時の名前解決の整合。
   globals は前方参照のために呼び出し時に引くが、elab は宣言時点の環境で名前を解決する。
   同名の再束縛を同じ表への Hashtbl.replace にすると、
   それより前に定義した関数まで新しい実体を見てしまい、
   型検査と実行が別の実体を選ぶ(黙って別の値が返ることもある)。
   そこで、再束縛のときだけ表を複製し、以後の宣言は新しい表で評価する。
   既存の閉包は古い表を持ち続けるので、定義した時点の名前を見る。
   新しい名前は、生きているすべての版に追加する。
   パス 1c で署名を登録した前方参照は、古い閉包からも見えるべきだからである。
   複製は再束縛のときだけ走るので、再束縛の無いプログラムでは一度も起きない。
   その代わり、病的な入力では、再束縛 K 回と新しい名前 N 個に対して O(K × N) の時間とメモリを使う *)
let bind_globals versions env names_values =
  let env =
    if List.exists (fun (n, _) -> Hashtbl.mem env.globals n) names_values then (
      let t2 = Hashtbl.copy env.globals in
      versions := t2 :: !versions;
      { env with globals = t2 })
    else env
  in
  List.iter
    (fun (n, v) ->
      if Hashtbl.mem env.globals n then Hashtbl.replace env.globals n v
      else List.iter (fun t -> Hashtbl.replace t n v) !versions)
    names_values;
  env

let exec_decl versions env ((_, d) as node : T.decl) =
  (* 宣言の出身 module を環境に立てる。この宣言から作られる閉包が mod_scope を
     捕まえるので、実行時の非修飾名の解決が elab の current_module と同じスコープの
     規則になる。インスタンスの頭の resolve_con も同じスコープで引くので、
     Decls 側の current_module も一時的に立てる *)
  let env = { env with mod_scope = Hashtbl.find_opt Decls.decl_module (Tree.oid_of node) } in
  let saved = !Decls.current_module in
  Decls.current_module := env.mod_scope;
  Fun.protect ~finally:(fun () -> Decls.current_module := saved) @@ fun () ->
  match d with
  | T.DLet ((_, b) as bnode) ->
      let v = eval_binding_value env bnode in
      let bound = bind_pat_exn SMap.empty b.T.lb_name v in
      bind_globals versions env (SMap.bindings bound)
  | T.DLetRec bs ->
      (* 再束縛があるなら、本体を評価する前に表を差し替える。閉包が新しい表を
         捕まえないと、自己再帰が古い実体を呼ぶ *)
      let names =
        List.map
          (fun ((_, b) : T.let_binding) ->
            match snd b.T.lb_name with T.PVar x -> x | _ -> runtime_error "let rec は名前束縛のみです")
          bs
      in
      let env =
        if List.exists (fun n -> Hashtbl.mem env.globals n) names then (
          let t2 = Hashtbl.copy env.globals in
          versions := t2 :: !versions;
          { env with globals = t2 })
        else env
      in
      List.iter2
        (fun ((_, _) as bnode : T.let_binding) x ->
          let v = eval_binding_value env bnode in
          if Hashtbl.mem env.globals x then Hashtbl.replace env.globals x v
          else List.iter (fun t -> Hashtbl.replace t x v) !versions)
        bs names;
      env
  | T.DExp e ->
      ignore (eval env e);
      env
  | T.DInstance i ->
      let cls = Type.intern i.T.ins_class in
      (* module の平坦化で作った同義語を通す(BigInt.BigInt など)。
         組み込み(Add[Int32] など)と同じ鍵の利用者の宣言は、実体を差し替えない。
         elab は組み込みを使うので、実行時だけ差し替わるとコヒーレンスが破れる *)
      let con =
        match i.T.ins_args with
        | [ (_, T.EIdent (LongId comps)) ] -> Decls.resolve_con (Type.intern (String.concat "." comps))
        | [ (_, T.EApply ((_, T.EIdent (LongId comps)), _)) ] -> Decls.resolve_con (Type.intern (String.concat "." comps))
        | _ -> bug "インスタンス頭が解決できません"
      in
      if
        (match Decls.find_class cls with Some ci -> ci.Decls.ci_builtin | None -> false)
        && Decls.builtin_instance_exists cls con
      then env (* 組み込みインスタンスは差し替えない(elab と一致させる) *)
      else
      let methods =
        List.concat_map
          (fun ((_, d) : T.decl) ->
            match d with
            | T.DLet ((_, b) as bnode) -> (
                match snd b.T.lb_name with
                | T.PVar x -> [ (Type.intern x, eval_binding_value env bnode) ]
                | _ -> [])
            | T.DLetRec bs ->
                let locals = eval_rec_bindings env bs in
                List.filter_map
                  (fun ((_, b) : T.let_binding) ->
                    match snd b.T.lb_name with
                    | T.PVar x -> Some (Type.intern x, SMap.find x locals)
                    | _ -> None)
                  bs
            | _ -> [])
          i.T.ins_body
      in
      Hashtbl.replace user_instances (cls, con) methods;
      (* 解決のキャッシュを無効化する。宣言より前の呼び出しが覚えた None を残すと、
         この宣言が二度と見えない *)
      Hashtbl.reset resolution_cache;
      env
  | T.DExtern ex ->
      let impl =
        (* 宣言の ABI で表を選ぶ。実装を引く鍵は修飾しない ex_prim で、
           globals に登録する名前は修飾された ex_name のままにする *)
        match Builtin.find_extern ~abi:ex.T.ex_abi ex.T.ex_prim with
        | Some f -> f
        (* 実装が無くても宣言は通し、呼ばれた時点で落とす。表を引いた鍵は ex_prim なので、
           修飾名と食い違うときは両方を見せる *)
        | None ->
            fun _ ->
              runtime_error
                ("未実装のプリミティブ: " ^ ex.T.ex_name
                ^ if ex.T.ex_name = ex.T.ex_prim then "" else "(実装名 " ^ ex.T.ex_prim ^ " が見つかりません)")
      in
      bind_globals versions env [ (ex.T.ex_name, VPrim { p_name = ex.T.ex_name; p_fn = impl }) ]
  | T.DType _ | T.DNewtype _ | T.DEffect _ | T.DClass _ -> env
  | T.DModule _ -> runtime_error "module の評価は未実装です(M10)"

(* ## 14.14 run

   `run` は宣言を順に実行するだけだが、全体を `Builtin.with_runtime`(第13章)の中で走らせる。
   `with_runtime` はランタイムが提供するエフェクトのハンドラで、
   `Console.write` を出力先へ送り、`Async.yield_` と `Async.sleep` ではすぐに continue する。
   ここにも届かなかった操作は `Effect.Unhandled` になり、driver が操作名を含めて報告する。
   プログラムのいちばん外側にハンドラを置き、
   エフェクトを未処理として扱う場所をここ 1 か所に決めている。

   冒頭では、3 つの表 `user_instances`、`resolution_cache`、`positions_cache` を空にする。
   さらに、第13章のメモリ上のダミーファイルシステムを `Builtin.reset_fs` で初期化する。
   同じプロセスで `run` を繰り返し呼ぶ場合(第16章の `eval_string`)に、
   前回の実行の痕跡を次の実行に残さないためである。
   痕跡が残ると、同じプログラムの結果が、それより前に何を実行したかに依存する。

   返り値は捨てる。
   暗黙の main は無く、トップレベルの式文は順に実行されるだけで、その値は誰も見ない。 *)

let run ~sink decls =
  Hashtbl.reset user_instances;
  Hashtbl.reset resolution_cache;
  Hashtbl.reset positions_cache;
  Builtin.reset_fs ();
  let globals = Hashtbl.create 512 in
  register_builtin_values globals;
  register_class_methods globals;
  let env = { globals; locals = SMap.empty; resume = None; mod_scope = None } in
  let versions = ref [ globals ] in
  ignore
    (Builtin.with_runtime ~sink (fun () ->
         ignore (List.fold_left (exec_decl versions) env decls);
         unit))

(* ## 14.15 本章の限界

   ### fiber の上の Stack_overflow

   ハンドラの本体は fiber の上で走る。
   fiber のスタックはヒープ上で伸びるので、暴走した再帰は、
   通常のスタックの上で走る場合より遅れて `Stack_overflow` として現れる。
   先にメモリを使い尽くし、`Out_of_memory` として現れることもある。
   そのため driver(第16章)は、`Stack_overflow` と `Out_of_memory` を同じ終了コード 3 で報告する。
   同じ理由で、深い非末尾再帰の限界を評価器のテストで固定することには意味が無い。
   限界は環境のメモリ量で変わる。

   ### 残している穴

   - ハンドラの外への後送り(re-perform)。
     同じハンドラの中の節どうしはフォールスルーする(§14.10)が、
     すべての節が外れた操作を外側のハンドラへ流すことはできない。
     機構は `effc` から `Effect.perform` するだけで書けるが、
     handle が E を消すという型付け(§11.24)と両立しない(§14.10)。
   - 前方参照の値を、定義より前に評価される位置で使うこと。
     パス 1c の署名で型は通るが、`let x = g(1)` の右辺のような、
     即時に評価される位置から前方の `g` を呼ぶと、
     実行はまだ値を持たないので「未束縛の変数」で落ちる。
     この形は、前方参照を遅延束縛で通す設計の代価である。
     黙って誤った値を返すのではなく実行時エラーで止まるので、許容している。
     インスタンス宣言より前の位置でそのインスタンスを使う形も、同じく実行時エラーにしている(§14.7)。

   一方、同名の再束縛(`let` の後の同名の `let` や `extern`、
   クラスメソッドと同名のトップレベル束縛)では、
   §14.13 の版の複製と elab の先勝ちの登録(§11.33、§11.36)により、型検査と実行が同じ実体を選ぶ。
   module の値同義語についても、elab と評価器の選ぶ実体は一致する。
   elab は宣言時点の環境で、評価器は呼び出し時の globals で名前を引き、
   どちらも見つからなかったときだけ同義語へフォールバックする。
   module の中の値の名前が、利用者のプログラムのトップレベルの値の名前と同じだと、
   フォールバックが起きるかどうかが両者で食い違いうる。
   その衝突は、第11章の `flatten_modules` が平坦化の時点で拒否する。
   プレリュードや組み込みの名前は、
   利用者のプログラムより先に elab の環境にも評価器の globals にも入るので、
   どちらも同義語へフォールバックする前にその名前を見つける。

   ### 静的化への移行路

   Diktor は型クラスのメソッドを、値のタグで動的にディスパッチする。
   この設計は、静的なディスパッチへ段階的に移ることを妨げない。
   elab が呼び出し地点の `resolved` に選んだインスタンスを書けば、
   評価器は `dispatch` の表引きを省ける。
   動的ディスパッチをフォールバックとして残したまま、呼び出し地点ごとに移せる。
   `pure` のように返り値の型からしかインスタンスが決まらないメソッドには、この静的な注記が要る。
   Diktor はこの注記を持たないので、そうしたメソッドは宣言の時点で拒否する(§11.33)。
   表引きの費用は、§14.7 の解決のキャッシュで抑えている。

   最後に、本章で外すと気づかれずに壊れるものを並べる。

   1. 起動ごとの `inst` の採番(共有すると、入れ子のハンドラが `Unwind` を横取りする)
   2. resume しなかった場合と例外で脱出した場合の両方での `discontinue`(落とすと資源が漏れる)
   3. 節本体が `Resume` のときの末尾での `continue`(落とすと実用的な速度を失う。
      ただし引数の評価は包む。包み忘れると資源が漏れる)
   4. クラスパラメータの位置だけを使うディスパッチ(外すとコヒーレンスが破れる)
   5. `let` による評価順序の固定(外すと観測できる意味論が変わる) *)
