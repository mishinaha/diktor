(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第14章 — 評価器: OCaml 5 のエフェクトで Keleut のエフェクトを写す

   ここが実行系の核心です。第11章 (elab.ml) が型と解決結果を書き込んだ木、
   第12章 (value.ml) の値表現とレコード演算、第13章 (builtin.ml) の
   プリミティブと最外周ハンドラを受け取り、木を歩いて値を作ります。
   第16章 (driver.ml) へ渡すのは「正常終了か、どの例外か」だけです。

   評価器の大半は素直な木の巡回で、面白いのは 2 か所しかありません。
   **エフェクトハンドラ**(§14.10)と**型クラスの実行時ディスパッチ**(§14.6,
   §14.7)です。前者は Keleut の意味論を OCaml 5 の `Effect.Deep` に写す仕事、
   後者は「elab が選ぶはずのインスタンスを実行時にもう一度当てる」仕事で、
   どちらも**外して気づきにくい形で壊れる**部類の実装です。

   ## 対応表 — Keleut のハンドラと OCaml 5 の Effect.Deep

   計画 D2 の裁定は「Keleut のエフェクトを `Effect.Deep` にそのまま写す」でした。
   写せる根拠は下の対応表で、全項目が spike (doc/log/260829-1-spike/effect) で
   実機確認済みです。

   | Keleut (sample.kel §9) | OCaml 5 の Effect.Deep |
   |---|---|
   | 深いハンドラ `handle { … }` | `match_with` 1 枚 |
   | `perform op(args)` | `Effect.perform (Op (op, args))` |
   | `resume(e)` | `Effect.Deep.continue k v` |
   | resume を呼ばずに節を抜ける | `discontinue k (Unwind (inst, v))` |
   | `case return(x)` | `retc`(親スタック上で走る) |
   | `case cancel` | `exnc` の中で節を走らせる |
   | 最内のハンドラが捕まえる | `effc` が `None` を返せば外側へ |
   | resume はアフィン(高々 1 回) | ワンショット継続(先に自前で検査) |
   | resume の返り値 = handle 式全体の型 | `continue` の型 = `match_with` の型 |
   | cancel の LIFO 巻き戻し | fiber の入れ子から自動で出る |

   最後の行が D2 の一番の収穫です。後始末の順序を評価器が管理する必要はなく、
   「ハンドラの入れ子」という既にある構造から出てきます。

   ## この章が守る 3 つの規約

   1. **末尾呼び出し規約**(計画 §8.3)。`eval` の末尾位置(`Apply` のクロージャ本体、
      `Match` の節本体、ブロックの末尾式)を OCaml の末尾呼び出しに保ちます。
      とくに **`eval` の再帰を `try … with` で包まない**。Keleut に while は無く
      再帰が唯一の反復手段なので、TCO を失うと普通のループがスタックを尽くします。

      > 評価器の再帰を 1 枚の try で包むと、その言語からループが消える。

   2. **評価順序は let で固定する**。OCaml の関数適用の引数評価順は未規定で、
      現行のコンパイラは右から左です。Keleut の仕様は左から右(sample.kel:203)
      なので、`apply (eval env f) (eval env arg)` と書くと順序が逆になります。
      1 つずつ `let` で束縛して順序を言語仕様から切り離します。

   3. **エラー装飾は driver の最外周 1 回だけ**。途中で捕まえて包み直すと、
      規約 1 が壊れるうえ、例外がエフェクトの巻き戻しにも使われている
      (§14.10 の `Unwind`)ため、捕まえ損ねが意味論の破壊に直結します。

   ## 章の見取り図

   表 (§14.1) → パターン照合 (§14.2) → 数値リテラル (§14.3) →
   `eval` の骨格 (§14.4) → 適用 (§14.5) → ディスパッチ (§14.6-§14.8) →
   束縛 (§14.9) → **ハンドラ** (§14.10) → トップレベル (§14.11-§14.14)。 *)
open Aux
open Syntax
open Value
module T = Tree.Tree

(* ## 14.1 実行時に引く 2 つの表

   計画 D3 の裁定により、型クラスは**辞書渡しをしません**。呼び出し地点に
   辞書を通す代わりに、実行時に値のタグでインスタンスを引きます。そのために
   必要なのはこの `user_instances` 1 枚と、第13章の組み込みメソッド表だけです。

   引き方は `(クラス, 型構成子) → メソッド名 → 値`。型構成子は第1章の
   インターン表の oid で、型側と同じ番号を使います。 *)

(* ユーザ宣言インスタンスのメソッド実体: (クラス, 型構成子) → メソッド名 → 値 *)
let user_instances : (oid * oid, (oid * Value.t) list) Hashtbl.t = Hashtbl.create 32

(* dispatch の解決キャッシュ(D37 / H12)。(クラス, 型構成子, メソッド)→
   実装。None(見つからない = 構造的導出へ落ちる)も覚える。
   user_instances への書き込み点は exec_decl の DInstance の 1 か所だけで、
   そこで必ずこの表を無効化する。書き込み点を増やすときは 1 か所を保つ
   こと — 無効化漏れは「宣言順で結果が変わる」最悪の壊れ方をする *)
let resolution_cache : (oid * oid * oid, (Value.t -> Value.t) option) Hashtbl.t = Hashtbl.create 64

(* dispatch_positions のメモ((クラス, メソッド)→ 候補位置)。スキーマは
   宣言後は不変なので無効化は run のリセットだけでよい *)
let positions_cache : (oid * oid, int list) Hashtbl.t = Hashtbl.create 64

(* ここがディスパッチの入口です。値から「名目的な型の名前」を 1 つ取り出します。
   `VRecord` と `VVariant` が `None` なのは偶然ではありません。レコードと
   ヴァリアントは構造的な型で、名前を持たないので名目的なインスタンス表を引く
   鍵になりません。ここで `None` になった値は §14.7 の構造的導出へ回ります。
   `VClosure` / `VPrim` も `None` — 関数にインスタンスは付きません。 *)

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

(* cancel 節で握り潰した例外の行き先です(sample.kel:392 の「cancel 節は自身の行から
   抜け出せない。例外相当を投げても抑制されてログに回る」)。ライブラリが直接
   stderr を触らないよう 1 段はさみ、driver (第16章) が差し替えます。 *)

(* cancel 節内の例外の抑制ログ(sample.kel:392)。driver が差し替える *)
let cancel_log : (string -> unit) ref = ref (fun _ -> ())

(* ## 14.2 パターン照合 — 失敗は例外ではない

   `match_pat` は「成功したら束縛を積んだ locals を `Some` で、失敗したら `None`」
   を返します。**失敗を例外にしない**のが要点です。照合の失敗は match の次の節へ
   進むための正常な制御であって、エラーではありません。

   細部で効いているのは 3 つです。

   - **レコードは最左一致**(Scoped Labels、第12章)。`record_take` が最左の同名を
     1 つ取り出して残りを返すので、同名ラベルを 2 つ持つ値から 2 回取ると
     2 回目は隠れていた方に当たります。ラベルが無いときに `record_take` が投げる
     `Runtime_error` は、ここでは**照合の失敗**なので `exception` パターンで
     受けて `None` に変えます。実行時エラーとして外へ出してはいけません。
   - **コンストラクタパターンは表引きだけ**。位置引数とラベル引数の混在、
     省略されたフィールドの扱いは、elab が `field_to_arg` に畳んであります
     (第5章 (tree.ml) の `resolved`)。ここで名前解決をやり直すと、elab と interp が
     同じ規則を二重に実装してドリフトします。`None` は「そのフィールドは
     パターンで触れていない」の意味です。
   - **数値パターンは字面ではなく値で比べる**。リテラルの字面をその値の型で
     読み直してから比較するので、`0x1` と `1` は一致します(実装記録の乖離11。
     elab の重複検出も同じ正規化を使っています)。

   `bind_pat_exn` は反駁不可であるべき位置 — `let`、関数引数、`return` 節 —
   で使います。操作節の引数はここを通りません — D28 以降はフォールスルーの
   照合(`match_pat`)で、不一致は次の節へ落ちます(§14.10)。
   ここで落ちたら網羅性検査か elab の穴です。`let` / `let rec` / `fn` の
   引数と `return` 節の反駁可能パターンも `Exhaust.queue` に乗っています
   (260829-5 の課題台帳 V10 は配線済み — かつて本文は「まだ配線されて
   いない」と書いていましたが、コミット 3d78255 で塞がっていました)。 *)

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

(* ## 14.3 数値リテラル — 評価器が elab の型を読む唯一の場所

   `1` が `Int32` なのか `Int64` なのか `Float64` なのかは、字面からは決まりません。
   決めるのは型検査で、既定化 (defaulting、D8) の結果がノードの型に書かれています。
   評価器が elab の書き込みを読むのは**ここだけ**です(計画 §8.3)。ほかのノードは
   `resolved`(解決結果)しか読みません。

   > 型を実行時に持ち回らないための代償は、リテラル 1 か所の型読みだけで済む。

   字面は字句解析のまま(`0x` 接頭辞やアンダースコア区切りを含む)保持されており、
   OCaml の `Int32.of_string` がそれをそのまま解釈できます。範囲外は `Failure` を
   `Runtime_error` に包み直します。包み忘れると OCaml の生の例外が driver の
   終了コード規約(第16章)を素通りします — 敵対的検証の頑健性の項でまとめて
   塞いだ穴の 1 つです。 *)

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

(* ## 14.4 eval の骨格 — 順序を言語仕様から切り離す

   本体は素直な木の巡回です。ノードごとに注意点だけ書きます。

   ### 評価順序

   `Apply` / `BinOp` / `RecordUpdate` は `let` で左から右を固定します。OCaml に
   任せると右から左になるので、副作用のあるプログラム(perform を含む)の
   出力順が仕様と食い違います。書き味の問題ではなく、**観測できる意味論**です。

   `RecordExtend (rest, l, v)` だけは **value が先、rest が後**です。AST の
   フィールド順と逆なので目で追うと間違えます。仕様(sample.kel:203)が
   `{l = e extends r}` を「e を先、r を最後」と定めているためで、タプルの脱糖が
   この規則に乗ることで `(a, b, c)` が a → b → c の順に評価されます。

   `Construct` は 2 つの順序を分けます。**評価はソース順、格納は宣言フィールド順**。
   `List.iteri` の副作用でソース順に評価し、書き込み先は elab が作った
   `arg_to_field` 表で引きます。ラベル引数を宣言と違う順で書いたときに、
   評価順だけがソースに従います。

   ### ノードごとの要点

   - **`Ident` は 4 段引き**: locals(不変 Map)→ globals(可変 Hashtbl)→
     module 平坦化の値同義語(D39、globals に無かったときだけ)→
     引数なしコンストラクタ。globals が可変なので、トップレベルの相互参照と
     前方参照が追加コードなしで通ります(第12章の環境の二層構造)。同名の
     **再束縛**とこの遅延引きを両立させる仕組みは §14.13 の版複製です。
   - **`BinOp`** は第7章 (prims.ml) の表を引くだけです。`&&` と `||` だけは
     型クラスにできません — 短絡するので右辺を評価しないから(D9)。
     `!=` は `Eq.eq` の否定として同じ表に入っています。
   - **`Match`** のガードが偽なら**次の節へ落ちます**。`try_clauses` は末尾再帰で、
     節本体の `eval` も末尾位置にあります(規約 1)。ハンドラの操作節も同じ
     規則です — パターン不一致もガードの偽も次の節へ落ちます(§14.10、D28)。
   - **`Perform`** は elab が `resolved` に書いた**完全操作名**の oid をそのまま
     使います。非修飾名の解決(D22 と、それを精密化した実装記録の乖離3 —
     「行の最左優先」)は型検査で終わっており、実行時に名前で悩むことはありません。
   - **`Resume`** は引数を**先に**評価します。節本体が `{ … ; resume(f()) }` の
     ように `Resume` そのものでない形のとき、`f` が例外で脱出すれば resume は
     未消費のまま節の例外経路(§14.10 の discontinue)に乗ります。順序を
     入れ替えると、消費済みの継続を捨てることになります。節本体が
     `resume(…)` そのもののときは §14.10 の末尾 resume 最適化に乗りますが、
     その経路でも引数の評価は包んであり、例外なら discontinue します。
   - **`Run`** は実行時には恒等写像です。`run h { … }` の `h` は型だけの存在で、
     リージョン安全性は第11章の剛定数とレベルが保証済みです。操作を持たない
     エフェクトラベル(`Heap`、`Blocking`、`pinned`)が実行時 no-op という
     計画 §8.4 の統一規則の、一番目立つ現れがこれです。

     > 型で守り切れたものは、実行時に守り直さない。 *)

let rec eval env ((_, e) as node : T.exp) : Value.t =
  match e with
  | T.Bool b -> VBool b
  | T.Text s -> VText s
  | T.Number n -> number_value node n (* 唯一 elab の型を読む場所(計画 §8.3) *)
  | T.Hole -> runtime_error "??? に到達しました"
  | T.Ident li -> (
      let name = show_long_id li in
      match SMap.find_opt name env.locals with
      | Some v -> v
      | None -> (
          match Hashtbl.find_opt env.globals name with
          | Some v -> v
          | None -> (
              (* module スコープの値同義語(D39 / D43)。elab と同じく
                 見つからなかったときだけのフォールバックで、引けるのは
                 この閉包の出身 module の分だけ *)
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
      (* 左から右。OCaml の未規定評価順に任せない(計画 §8.3) *)
      let vf = eval env f in
      let va = eval env arg in
      apply vf va
  | T.Construct (_, args) -> (
      match Tree.get_resolved node with
      | Some (Tree.RCtor (d, c, arg_to_field)) ->
          let fields = Array.make (Array.length arg_to_field) unit in
          List.iteri
            (fun ai (a : T.ctor_arg) ->
              (* 評価はソース順、格納は宣言フィールド順(resolved の対応表) *)
              fields.(arg_to_field.(ai)) <- eval env a.T.ca_exp)
            args;
          VData { d_type = d; d_ctor = c; d_fields = fields }
      | _ -> bug "Construct が解決されていません")
  | T.Variant (s, payload) -> VVariant (Type.intern s, eval env payload)
  | T.BinOp (l, op, r) -> (
      match Prims.bin_op_sem op with
      | Prims.OpBool -> (
          (* 短絡(sample.kel:282) *)
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
                (* ガードが偽なら次の節へ落ちる *)
                | Some g -> if Builtin.as_bool (eval env2 g) then eval env2 c.T.cl_body else try_clauses rest
                | None -> eval env2 c.T.cl_body))
      in
      try_clauses clauses
  | T.RecordEmpty -> unit
  | T.RecordExtend (rest, l, v) ->
      (* value が先、rest が後(sample.kel:203。AST のフィールド順と逆。計画 §8.3) *)
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
          (* 引数を先に評価する: 節本体が Resume そのものでない形なら、引数評価中の例外で
             resume は未消費のまま節の例外経路(discontinue)に乗る。
             節本体が Resume そのもののときは下の末尾 resume 最適化に乗るので走らない *)
          let v = match arg with Some e -> eval env e | None -> unit in
          if not r.r_alive then runtime_error "resume を節の外で呼び出しました(second-class)"
          else if r.r_used then runtime_error "resume は高々1回しか呼べません(アフィン)"
          else (
            r.r_used <- true;
            Effect.Deep.continue r.r_k v))
  | T.Run (_, body) -> eval env body (* 実行時は恒等。型が保証する(計画 §8.4) *)

(* ## 14.5 適用 — arity 検査は閉じた行の実行時版

   関数は多引数で単値を返し、引数は 1 つのレコードに詰めて渡します(D5)。
   よって適用は「引数レコードのフィールドを仮引数パターンに順に束縛する」だけです。

   個数の不一致はここでは本来起きません。arity は矢印型の一部で、閉じた `_item`
   行の単一化として型検査が弾いているからです(sample.kel:125-126)。残してある
   のは、プリミティブ経由や内部バグで壊れた引数が来たときに `Array.for_all2` の
   `Invalid_argument` のような無関係な例外に化けさせないための保険です。

   束縛の土台が `c.c_env.locals`(定義時の環境)であることが静的スコープの実装です。
   呼び出し側の locals は一切混ざりません。 *)

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

(* ## 14.6 どの引数でディスパッチするか — 実際に踏んだ健全性のバグ

   辞書渡しをしない実装(D3)は、実行時に「どの値のタグでインスタンスを選ぶか」を
   決めなければなりません。素朴な答えは「引数を左から見て、最初にインスタンスを
   持つ値で決める」です。**これは誤りでした。**

   反例は 260829-2b の敵対的検証で実際に動かしたものです。

   ```keleut
   type class Pick[A] { val pick: (Int32, A) => Int32 }
   type instance Pick[Int32]  { let pick(n, a) = a }
   type instance Pick[String] { let pick(n, a) = n }
   let s: String = ...    // 何か String の値
   pick(0, s)
   ```

   左から走査すると第 1 引数の `Int32` に `Pick[Int32]` が当たり、実行時は
   `Pick[Int32]` を選びます。ところが elab はクラスパラメータ `A` の位置で
   解決するので `Pick[String]` を選びます。**型検査と実行が別のインスタンスを
   選ぶ**、つまりコヒーレンスが実行時に破れている状態です。

   正しい規約は「**クラスパラメータが頭に現れる引数位置だけで選ぶ**」。
   `dispatch_positions` はメソッドスキーマ(Generic マーク済み)の引数レコードを
   走り、型適用の背骨 (`app_spine`) の頭が当のクラスパラメータである位置を
   集めます。elab 側の `register_class` は、宣言時に「少なくとも 1 つの引数の
   頭にパラメータが現れること」を要求しており(`List[A]` のように内側へ埋もれた
   形は宣言を拒否)、**両側がまったく同じ述語を見ています**。

   > ディスパッチの規約は、宣言を受理する側と実行する側で同じ 1 つでなければならない。

   位置が 1 つも取れなかったときは全走査に落とします。ただし現状これは
   **到達しない**保険です。組み込みクラス (Add / Sub / Mul / Div / Eq / Ord / Show)
   のスキーマはどれも引数の頭がクラスパラメータそのもの、メソッドを持たない
   Integral / Fractional はそもそも dispatch されず、ユーザ宣言クラスは上の
   受理検査が同じ形を強制します。スキーマの形が将来想定外になったときに、
   選択肢が狭まるより広い方が「インスタンスが無い」で落ちにくい、という
   安全側の判断で残してあります。回帰テストは test/verify_fixes.t の
   pick.kel です。 *)

(* メソッドスキーマから「クラスパラメータが頭に現れる引数位置」を求める。
   ここだけでディスパッチする(elab.ml の register_class と同じ規約)。
   これを守らないと pick: (Int32, A) => Int32 が第1引数の Int32 で
   誤ってディスパッチし、elab の解決と食い違う(検証で実証) *)
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

(* ## 14.7 dispatch — 探索の順序とフォールバック

   候補位置の値を左から見て、最初に実装が見つかった値でメソッドを決めます。
   1 つの値について引く順序は **ユーザ宣言インスタンス → 組み込みメソッド表**
   です(ユーザ宣言が組み込みキーを奪えないことは §14.13 で別に保証します)。

   どこにも無ければ**構造的導出**へ落ちます。v0 が構造的に導出するのは `Eq` だけで
   (sample.kel:297 の「ユーザには書かせない。コヒーレンスを堅持するため、組み込みの
   自動導出のみが与える」。導出が閉じた行にしか効かないことは sample.kel:305-309)、
   クラス宣言に付いた `derive structural` が実体です。

   ここで効いている不変条件があります。elab 側(第8章 (unify.ml))は構造的導出を
   **閉じた行のレコードとヴァリアントにしか**適用しません。それ以外の型に `Eq` が
   要求されればインスタンス表を引き、無ければ型エラーです。だから実行時に
   この分岐へ来る値は、型検査を通った範囲ではレコードかヴァリアント
   — `tycon_of_value` が `None` を返した値 — に限られ、elab の判定と選択が一致します。
   例外が 1 つだけあります。ユーザインスタンスを**宣言より前の位置**で使う形です。
   型検査はパス 1c でインスタンス表を揃えてから本体を見るので宣言順を問いませんが、
   実行は宣言順に `user_instances` へ書くので、その時点では実体がありません。
   かつてはここで名目型の値が黙って構造的等価に落ち、同じ `Box(1) == Box(1)` が
   インスタンス宣言の前では `true`、後では `false` を返しました(M22 の検証で実測)。
   いまは elab の表にインスタンスがあるのに実行の表に無い値を見つけたら、
   構造的導出へ落ちる前に実行時エラーにします — 末尾の残穴の一覧が前方参照の値に
   ついて採っている「黙って誤るのではなく音を立てる」側の判断と同じです
   (`test/verify_fixes.t` の instorder)。

   逆に言えば、ここで「インスタンスが見つかりません」が出たら、それは実行時の
   問題ではなく**型検査側か表の登録側の穴の報告**です。実際、module の中で宣言した
   instance が実行時に見つからない欠陥は、この形で表に出ました(§14.13)。

   > 実行時ディスパッチが正しいのは、コヒーレンスが保証されているからであって、
   > 探索が賢いからではない。だから賢くしてよい — 正しさが探索に依らないと
   > 分かっているから、結果を覚えても意味は変わらない。

   その「覚える」が `resolution_cache`(解決の結果。None も含む)と
   `positions_cache`(候補位置)です(D37 / H12)。無効化点は 2 つだけ —
   `run` の冒頭のリセットと、`exec_decl` の `DInstance` 登録(そこで
   `resolution_cache` を空にする)。user_instances への書き込み点を
   1 か所に保つことが、この表の正しさの前提です。 *)

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
        | [] -> vals (* 位置が取れなければ全走査(現状は到達しない安全側の保険) *)
        | ps -> List.filteri (fun i _ -> List.mem i ps) vals)
    | None -> vals
  in
  let find_impl v =
    match tycon_of_value v with
    | Some con -> (
        (* 解決はキャッシュ越し(H12)。賢くしてよいのは、正しさが探索に
           依らない — コヒーレンスが保証されている — と分かっているから *)
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
      (* 名目型の値がここへ来るのは、その (クラス, 構成子) のユーザインスタンスが
         宣言より**前**の位置で使われたときだけ(型検査はパス 1c で表を揃えるので
         通す。実行は宣言順に user_instances へ書くので、まだ実体が無い)。
         黙って構造的等価へ落とすと同じ式が宣言の前後で違う答えを返す(M22 の
         検証で実測)ので、音を立てる側に倒す — §14 末尾の前方参照と同じ判断 *)
      (match List.find_map tycon_of_value cand_vals with
      | Some con when Decls.find_instance ~cls:cls_oid ~con <> None ->
          runtime_error
            (cls_name ^ "[" ^ Type.name_of con ^ "] のインスタンスは宣言より前の位置では使えません(実行はまだ実体を持ちません。インスタンス宣言を使用より前に置いてください)")
      | _ -> ());
      (* 構造的導出(v0 は Eq のみ、計画 §8.2)。コヒーレンスにより elab と一致 *)
      let structural = match Decls.find_class cls_oid with Some ci -> ci.Decls.ci_derive_structural | None -> false in
      match (structural, meth, vals) with
      | true, "eq", [ a; b ] -> VBool (structural_eq a b)
      | _ ->
          runtime_error
            (cls_name ^ "." ^ meth ^ " のインスタンスが見つかりません: "
            ^ String.concat ", " (List.map show vals)))

(* ## 14.8 構造的等価 — 物理順序で比べてはいけない

   `{p = 1, q = 2}` と `{q = 2, p = 1}` は同じ値です。行の型は最左一致で決まる
   一方、異なるラベルの間には順序がありません。よって値のフィールドリストを
   前から突き合わせる比較は**誤り**です。正しい手順は「左のフィールドを順に取り、
   右から**最左の同名**を取り出して消す」。最後に右が空になれば一致です
   (右に余分なフィールドがあればここで落ちます)。

   フィールドの比較を直接の再帰ではなく `value_eq`(= `dispatch Eq.eq`)に通すのも
   意図的です。フィールドにユーザ定義の `Eq` を持つ newtype があるとき、宣言された
   インスタンスを無視して構造をのぞき込んではいけません。

   引数レコードに `_item` が 2 つ並ぶのは Scoped Labels だからです(D5)。重複を
   許すと決めたことが、そのまま多引数の表現になっています。

   関数の比較は実行時エラー。Float は `__float64_eq` に落ちるので IEEE の意味論
   (NaN ≠ NaN)がそのまま出ます。 *)

and value_eq a b = Builtin.as_bool (dispatch "Eq" "eq" (VRecord [ (Type.l_item, a); (Type.l_item, b) ]))

(* レコードは「左のフィールドを順に、右から最左同名を取り出して消す」(計画 §8.2。
   異ラベル間の物理順序は違いうるので単純な順序比較は誤り) *)
and structural_eq a b =
  match (a, b) with
  | VRecord fs1, VRecord _ ->
      let rec go fs1 rv =
        match fs1 with
        | [] -> record_fields rv = [] (* 右に余りがあれば不一致 *)
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

(* ## 14.9 let と let rec — バックパッチが要る場所、要らない場所

   `eval_binding_value` は、引数リストが付いていれば右辺を**評価せずに**
   クロージャを作ります。`let f(x) = …` は関数定義であって、右辺の式ではありません。

   `let rec` は 3 手です。**クロージャ生成 → 環境構築 → `c_env` バックパッチ**。
   相互再帰する関数は「自分たちを含む環境」を捕まえる必要があり、その環境は
   クロージャが出来上がるまで作れないので、循環を後から結びます。第12章の
   クロージャで `c_env` だけが mutable なのは、この 3 行のためです(章の中で
   唯一の mutable ではありません。`resume` の `r_used` / `r_alive` は §14.10 の
   アフィン性と second-class のためのもので、別の話です)。

   右辺が関数でないときは実行時エラーですが、ここへは来ません。「型検査は通るのに
   実行時に必ず落ちる」`let rec x = x + 1` の類は elab が拒否するようになりました
   (260829-2b の健全性 9)。**必ず落ちるプログラムを実行時まで運ばない**のが方針です。

   トップレベルの `let rec` (§14.13) にバックパッチが要らないのは、globals が
   (同じ版を見る閉包の間では)共有の可変表で、名前解決が呼び出し時に
   起きるからです。 *)

and eval_binding_value env ((_, b) : T.let_binding) =
  match b.T.lb_params with
  | Some ps -> VClosure { c_env = env; c_params = ps; c_body = b.T.lb_body }
  | None -> eval env b.T.lb_body

and eval_binding env ((_, b) as bnode : T.let_binding) =
  let v = eval_binding_value env bnode in
  bind_pat_exn env.locals b.T.lb_name v

and eval_rec_bindings env (bs : T.let_binding list) =
  (* クロージャ生成 → 環境構築 → c_env バックパッチ(計画 §8.2) *)
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

(* ## 14.10 ハンドラ — この章の心臓

   1 つの `handle` 式は `Effect.Deep.match_with` 1 枚です。節の振り分けは elab が
   `resolved` に書いたタグ(`ROp` / `RReturnClause` / `RCancelClause`)を読むだけで、
   操作名の解決はここではやりません。

   ### 起動ごとの inst — ハンドラの同一性は「場所」ではなく「起動」

   `inst` は **Handle ノードを評価するたびに** `new_oid ()` で採番します。AST の
   ノード id を流用してはいけません。同じ handle 式が入れ子に活性化する場面
   — 再帰の中の handle、`with_file` を 2 回呼んだ入れ子 — で、内側が**外側宛の
   `Unwind` を自分宛と誤認して飲み込む**からです。spike の TEST 6 で、共有した
   場合に結果が `#Err(boom)` ではなく `#Ok(#Err(boom))` に化けることを実測しました。

   > ハンドラの同一性は、書かれた場所ではなく、その起動そのものである。

   ### Unwind が運ぶプロトコル

   `Unwind (inst, v)` は例外の形をした手紙です。中身は「resume されずに終わった
   節の値 `v` を、`inst` 番のハンドラの handle 式全体の値として届けてほしい」。

   1. 節が resume を呼ばずに `v` を返す。
   2. `discontinue k (Unwind (inst, v))` で、捨てる継続の中にこの例外を叩き込む。
   3. 中断されたフラグメントが内側から巻き戻る。途中のハンドラは `exnc` で
      「自分宛でない `Unwind`」を見て、`cancel` 節を走らせてから再送出する。
   4. 最後に自分の `exnc` が `id = inst` を見て `v` を返す。これが handle 式の値。

   後始末が LIFO になるのは、この経路が fiber の入れ子をそのまま逆にたどるからです。
   評価器に順序を管理するコードはありません(spike TEST 3 で `with_file` 2 枚重ねの
   close 順を確認済み)。仕様(sample.kel:379-392)が defer 構文を持たず「後始末は
   ハンドラの cancel 節」と決めたことが、実装ではこの 4 行に落ちます。

   ### 3 つの径路 — resume されない経路と例外経路

   `effc` が返す関数は、節の評価が**どう終わったか**で 3 つに分かれます。

   | 節の終わり方 | すること | 理由 |
   |---|---|---|
   | resume 済み、値 `v` | `v` を返す | 継続は消費済み。返り値が handle 式の値 |
   | 未 resume、値 `v` | `discontinue k (Unwind (inst, v))` | 捨てた継続の cancel |
   | 例外 `ex` で脱出 | `discontinue k ex`(未 resume なら) | 同上 + 自分の cancel |

   2 行目で `v` を直接返してはいけない理由は、捨てた継続の中のハンドラの
   `cancel` 節が走らず**資源が漏れる**からです。spike TEST 3 が実証です
   — `with_file` を 2 枚重ねて内側で継続を捨てると、内側 → 外側の順に
   `cancel` が走って `__close` が 2 回出ます。diktor 側の回帰テストは
   test/eval.t の effects.kel(`with_res` の 2 枚重ねで `cancel inner` →
   `cancel outer`)です。

   よく似た別の事実と混ぜないでください。**自分の**節が継続を捨てたとき、
   その**当のハンドラ自身**の `return` / `cancel` 節は走りません(spike TEST 14)。
   discontinue しても変わりません。これは穴ではなく、計画 §12 が「意図した挙動」
   として記録した裁定です — cancel を走らせると、`try_` が正常に `#Err` を返す
   ときにも後始末が走ってしまうからです。資源を持つハンドラが自分で継続を
   捨てるなら、後始末は節の中に書きます。

   3 行目は素朴に書くと必ず落とす分岐です。節の中で `???` に到達した、実行時エラーが
   起きた、外側の `Unwind` が通過した — どの場合も `discontinue` が要ります。
   落とすと 2 つ壊れます。(a) 捨てた継続の中の cancel が走らない。(b) `effc` から
   の素の `raise` は**親スタック上を伝播するので自分の `exnc` を素通りし**、
   自分の cancel すら走らない。spike の TEST 4b / 4c で両方を実測し、回帰テストは
   test/eval.t の holecancel.kel(節本体が `???` でも内側の cancel が走る)です。

   > 継続を捨てるときは、捨てたことを継続に知らせる。

   この 3 径路の規約は、§13.6 の最外周ハンドラ(`with_runtime` の
   `Console.write`)にも同じく効きます。

   ### 末尾 resume 最適化 — 性能ではなく実用条件

   上の 3 径路の判定は、節の評価を `match … with exception` で包むことを要求します。
   その 1 枚が `continue` を `effc` の末尾式でなくします。計測(計画 §8.4)では、
   継続の発行を末尾にしない実装は perform 100 万回で約 26 倍、1000 万回で約 300 倍
   遅くなりました(Stack_overflow はしません。fiber のスタックは伸びます)。

   `case op(x) => resume(…)` はプレリュードのハンドラのほぼ全部です。そこで
   **節本体が構文的に `Resume` そのものなら**、3 径路の判定ごと畳んで
   `Effect.Deep.continue k v` を末尾発行します。ゴールデン test/eval.t の
   「10 万回の println」がこの経路の回帰テストで、最適化が外れれば実行時間で
   気づけます。**最適化というより実用条件**で、M10 送りにしなかったのはそのためです。

   速い経路も 3 径路の規約を守ります。`match … with exception` が覆うのは
   **引数の評価だけ**で、`continue` は値の枝 — trap を抜けたあと — にあるので
   末尾発行のまま(OCaml は値ケースを trywith の外に下げます)。引数が例外で
   脱出したら通常経路と同じく `discontinue` します。かつてはこの経路だけ
   引数評価が包まれておらず、`resume(???)` の形で捨てた継続の cancel も自分の
   cancel も走りませんでした(実測)。マイクロベンチ(perform 1000 万回)で
   引数だけ包む形は現行と同時間・同メモリ、`continue` を trap の内側に置く形は
   約 120 倍遅いことを確認して、この形を選んでいます。

   ### アフィンな resume と second-class

   `r_used` はアフィン性(高々 1 回)、`r_alive` は second-class(節の外へ
   持ち出さない)の実行時側です。OCaml も 2 度目の `continue` で
   `Continuation_already_resumed` を投げますが、それでは Keleut のエラーとして
   説明にならないので、先に自前で弾いて日本語のメッセージを出します。
   `r_alive` は D19 の 2 段構えの片方で、もう片方 — 節本体のラムダの中に
   `resume` があれば拒否する構文検査 — は elab にあります。

   ### cancel 節の実行文脈

   `run_cancel` は `exnc` の中、つまり**巻き戻しの途中**で走ります。このとき
   有効なのは**外側のハンドラだけ**で、いま巻き戻しを起こしている当の
   ハンドラは既に外れています。`Effect.Deep.match_with` の `exnc` は fiber を
   巻き戻したあと**親のスタックで**呼ばれるので、`run_cancel` の中で
   `Effect.perform` しても自分の `effc` には届きません。cancel 節から自分の
   操作を perform すると、外側の同名エフェクトのハンドラに届きます —
   第11章 §11.24 が cancel 節を外側の行で型付けているのと同じ事実の
   実行側です(`test/eval.t` の cancelouter / cancelnores、D100)。
   届いた先が resume せずに抜けると `Unwind` が cancel 節を通過しようと
   しますが、それは cancel 節内の例外として抑制され、ログに回るだけで
   外へは出ません(仕様 sample.kel §9 の抑制規則)。

   かつてこの節は「当のハンドラも有効で、perform は同じハンドラに再入する
   (deep handler は discontinue のあとも再設置されるため)」と書いていました。
   実測で反証された誤りです。第11章 §11.24 は最初から正しく「自分の
   ハンドラが外れた文脈で走る」と書いていて、2 つの章が逆のことを言った
   まま突き合わせられていませんでした。誤った本文は issue を経由して仕様
   §9 にまで写り、2026-09-12 に仕様側を訂正しました。**仕様へ出す文面は
   実装の本文からではなく実測から起こす**、という教訓がここにあります。

   cancel 節の例外をすべて握り潰してログに回すのは仕様(sample.kel:392)です。
   OCaml の生の例外表現がそのままログに出ないよう、`Printexc.to_string` を通します。

   `retc` と `run_cancel` が `cl_guard` を読まないのは、elab が return 節と
   cancel 節のガードを拒否するからです (§11.24)。かつて elab はガードを受理して
   いて、ここが読まないぶん実行時に黙って消えていました。

   ### 操作節の選択は match と同じ(D28)

   操作節はソース順に試し、**パターン不一致もガードの偽も次の節へ落ちます**
   — §14.2 の match と完全に同じ規則です。ガードは resume 無しの環境で
   評価します(ガードから継続は見えません。§11.24)。全節が外れたときは
   `discontinue` で実行時エラーにしますが、elab の総和性検査(各操作に
   ガード無し・反駁不可の節を 1 つ要求する。§11.24)を通っていれば到達
   しない防御枝です — 消さないこと。素の raise にしないのは 3 径路の
   規約どおり、捨てた継続の cancel を走らせるためです。

   **ハンドラの外への後送り(re-perform)は v0 にはありません。** 機構は
   書けます — `effc` のハンドラ関数は fiber の外で走るので、そこから
   `Effect.perform` すれば自分を飛ばして外側に届きます(実測済み)。塞いで
   いるのは型です。handle の型付けは対象エフェクト E を**消す**と言い切る
   ので(§11.24)、ガード偽で E.op を外へ流すと E の無い行の文脈に操作が
   漏れ、型が嘘になります。部分ハンドラの型付け(サブエフェクティング)は
   仕様側の裁定待ちです。 *)

and eval_handle env body clauses =
  (* inst は Handle ノードの評価のたびに採番する(入れ子活性化が外側宛の Unwind を
     自分宛と誤認しないため。誤動作を spike で実測済み) *)
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
        (* cancel 節内の例外は抑制してログ(sample.kel:392) *)
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
          (* return 節は親スタック上で走る(計画 §8.4) *)
          match ret_clause with
          | None -> v
          | Some (_, c) ->
              let pat = match clause_arg_pats c with [ p ] -> p | _ -> bug "return 節のパターン" in
              let locals = bind_pat_exn env.locals pat v in
              eval { env with locals; resume = None } c.T.cl_body);
      exnc =
        (fun ex ->
          match ex with
          (* 自分宛の巻き戻し: 保留していた節の値が handle 式の値になる *)
          | Unwind (id, v) when id = inst -> v
          | ex ->
              (* 外側による巻き戻し(または実行時エラー)の通過: cancel 節を実行してから再送出 *)
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
                      (* 節を宣言順に試す。パターン不一致もガードの偽も次の節へ落ちる
                         (§14.2 の match と同じ規則、D28)。ガードから継続は見えない *)
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
                      (* 節の選択 — 引数の照合とガードの評価 — も trap の中(敵対的
                         検証の指摘)。ガードで起きた例外も、ガードを通過する外側の
                         Unwind も 3 径路の規約に乗せる。素の raise は fiber に
                         届かず、捨てた継続の cancel も自分の cancel も走らない *)
                      | exception ex -> Effect.Deep.discontinue k ex
                      | None ->
                          (* 全節が外れた。elab の総和性検査(§11.24)を通っていれば到達
                             しない防御枝 — 消さないこと。素の raise ではなく discontinue
                             (捨てた継続の cancel を走らせる。3 径路の規約) *)
                          Effect.Deep.discontinue k
                            (Runtime_error ("handle のどの節にも一致しません: " ^ Type.name_of op ^ show args))
                      | Some (locals, c) -> (
                          match snd c.T.cl_body with
                          | T.Resume arg -> (
                              (* 末尾 resume 最適化(計画 §8.4 の性能特性)。exception 節が
                                 覆うのは引数の評価だけで、continue は値の枝 — trap を抜けた
                                 あと — にあるので末尾発行のまま。引数が例外で脱出したときは
                                 通常経路と同じく discontinue する(捨てた継続の cancel を
                                 走らせるため)。r_used を先に true にしてあるので、引数の中の
                                 入れ子 resume はアフィン検査で先に落ち、例外の時点で k は
                                 必ず未消費 — discontinue は常に安全 *)
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
                                  (* 未 resume なら継続を巻き戻し、自分の exnc で v を拾い直す *)
                                  if r.r_used then v else Effect.Deep.discontinue k (Unwind (inst, v))
                              | exception ex ->
                                  (* 節が例外で脱出したときも必ず discontinue(捨てた継続の中の
                                     cancel を走らせる。落とすと資源が漏れることを spike で実測済み) *)
                                  r.r_alive <- false;
                                  if r.r_used then raise ex else Effect.Deep.discontinue k ex))))
          | _ -> None);
    }

(* ## 14.11 組み込み値 — Ref と配列は素の OCaml

   `Ref` は OCaml の `ref`、`Array` と `MutableArray` はどちらも OCaml の
   配列です。リージョン安全性(`run h { … }` の外へ持ち出せないこと)は
   第11章の剛定数とレベルが型で保証しているので、実行時には包みも検査も
   ありません。§14.4 の `Run` が恒等写像であることと同じ話の裏側です。

   値の表現だけは 2 つに分けました (D70)。`VArray` が不変、`VMutArray` が
   可変で、中身はどちらも `Value.t array` です。分けたのはディスパッチの
   タグ(§12.1 の表)と印字を別にするためで、実行時の動作が違うからでは
   ありません。同じコンストラクタを共用すると、可変配列の値が `Array` の
   タグで表に引かれます。これは将来の備えではなく、いま効いています —
   M22 の前提つきインスタンスで `type instance[A: Show] Show[Array[_]]` は
   宣言でき、実行時のディスパッチは現にこのタグで表を引きます(検証で実測)。
   共用していれば、可変配列の値がそのインスタンスに当たっていました。
   `MutableArray` 側のインスタンスは宣言できても使用点で落ちます(`run` の
   剛定数に制約が無いため)が、それはタグが正しいこととは別の理由です。

   `MutableArray.freeze` は**コピー**です (D69)。仕様 §10 が要求するのは
   「freeze 後に元の可変配列へ書いても、取り出した配列は変わらない」という
   観測可能な契約だけで、コピーするかどうかは実装戦略だと明記してあります。
   共有したまま契約を守るには線形性か copy-on-write が要り、どちらも v0 には
   無いので、素直にコピーします。要素が可変配列であるときの入れ子は浅い
   コピーのままで、リージョンの内側では要素の別名を観測できますが、
   そういう配列は要素の型に `h` を持つのでリージョンの外へ出られません。

   一方で配列の**範囲検査は実行時**です。長さは型に載っていないので、
   ここは型では守れません。負の長さの `MutableArray.new` も同じ理由で
   実行時に弾きます。

   `Array.each` が `apply` を呼ぶことには意味があります。渡された関数の中で
   `perform` が起きても、OCaml のエフェクトは間に挟まる `Array.iter` の
   スタックフレームを越えて外側のハンドラまで届きます。組み込み関数を
   「エフェクトを通す穴」にするための特別な仕掛けは要りません。 *)

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
          (* 長さは型に載っていないので、ここだけは実行時に守る *)
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
  (* freeze はコピー(D69)。仕様 §10 の「freeze 後に元の可変配列へ書いても
     取り出した配列は変わらない」を、共有しない最も素直な形で満たす *)
  reg "MutableArray.freeze" (fun args ->
      match Builtin.arg1 args with
      | VMutArray a -> VArray (Array.copy a)
      | _ -> runtime_error "MutableArray ではありません");
  (* par / par_map(H2 / D45)。逐次実装が並列実行と**観測同値**である根拠は
     スケジューラの不在ではなく、コールバックの行が @ {} に閉じている
     こと — Heap も Console も Async も起こせないので、実行順序が観測
     できない(§6.11b)。並列化したら変わる点が 1 つ: コールバックが
     例外で脱出したとき、逐次では後続が評価されない(素の OCaml と同じ)。
     par_map の返り値は不変の Array[B] で、可変配列とは型が違う(M24)。
     **正直な留保**: この「型が純粋を守る」前提には
     既知の破れが 2 つある(260829-5 台帳 V14 / V15)— 高階位置(newtype
     フィールド・effect 操作型)の省略 @ が使用毎に別インスタンス化されて
     エフェクトが洗浄される形と、ファイル prim が行なしで型付けされて
     いる形。どちらも仕様側の裁定待ち(M20)で、それまで観測同値の保証は
     この 2 つの穴を除いた範囲に留まる *)
  reg "par_map" (fun args ->
      match Builtin.arg_values args with
      | [ VArray a; f ] ->
          (* 適用順は添字 0 から明示で固定。Array.map の適用順に任せない
             (計画 §8.3 の規律。par の左→右と同じ — 逐次実装の意味論は
             順序込みで固定する) *)
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
          (* 評価順は左から。OCaml の未規定評価順に任せない(計画 §8.3) *)
          let va = apply fa unit in
          let vb = apply fb unit in
          VRecord [ (Type.l_item, va); (Type.l_item, vb) ]
      | _ -> runtime_error "par の引数が不正です");
  (* pinned は恒等(H11)。v0 が Blocking に負う観測可能な契約は「並列度を
     減少させない」と「キャンセル配送点ではない」の 2 つで、タスクが 1 つ
     (Async は no-op)・配送点が yield_ だけの v0 ではどちらも恒等実装が
     満たす。Blocking はトップレベルに残せる(仕様 §12、D88)ので、
     pinned を通さないプログラムも実行に届くが、ランタイムが受け取る
     ものは何も無い。スケジューラを持つ日に、専用スレッドへの束縛として
     ここを差し替える *)
  reg "pinned" (fun args -> apply (Builtin.arg1 args) unit)

(* ## 14.12 クラスメソッドの識別子参照

   `eq(a, b)` や `show(x)` のようなメソッドの**識別子参照**は、`dispatch` を
   呼ぶだけのラッパ prim を globals に置いて素通しにします。ラッパは呼ばれた
   時点で表を引くので、インスタンス宣言との前後関係を気にしなくて済みます。

   登録する名前は**非修飾と修飾の両方**です(実装記録の乖離12)。`map` でも
   `Functor.map` でも引けます。同名メソッドを持つクラスが 2 つあると非修飾名の
   勝者争いが起きますが、その衝突は**宣言時に elab が拒否します** (§11.33)。
   かつては受理していて、どちらが勝つかが「未規定」どころではありませんでした
   — elab の非修飾名解決は宣言順の後勝ち、こちらの登録は `Hashtbl.iter` の
   走査順(oid のハッシュ順)の後勝ちで、**型検査と実行が別のクラスを選び**、
   誤った実体を静かに呼ぶか、偽の「インスタンスが見つかりません」を出しました
   (実測。無関係な 1 行を足しただけで勝者が入れ替わることも確認)。

   下の実装が走査結果をクラス名でソートしてから登録するのは念のためです。
   **クラスどうし**の勝者争いは elab が拒否するので起きませんが、ハッシュ順
   という観測に漏れうる非決定性を、そもそも表の走査に残さないためです。

   ただし elab の拒否が守るのはクラスどうしの衝突**だけ**です。クラス
   メソッドと同名の**トップレベル束縛**(プレリュードの `let` / `extern` を
   含む)は、この登録より後に globals に入り、ここで置いたラッパを覆います。
   かつてはそれが同じ表への `Hashtbl.replace` だったので、**再束縛より前に
   定義済みの関数まで**新しい実体を見てしまい、elab(宣言時点で解決)と
   逆の勝者を選びました。いまは §14.13 の版複製が働きます — 再束縛の時点で
   表が分かれ、先に作られた閉包は古い表のラッパを見続けます。elab 側も
   同じ規則です: パス 1b / 1c の非修飾名登録は**先勝ち**で、後から来た
   同名束縛が既存の環境を上書きしません(第11章 §11.33 / §11.36)。両者が
   「最初にその名前を持った側が非修飾名の勝者」で揃うので、どの呼び出し
   地点でも elab と実行が同じ実体を選びます(260829-5 の課題台帳 V1、
   M15 で解消。module の値同義語が絡む残穴は §14.15)。 *)

(* クラスメソッドの識別子参照は dispatch へのラッパで素通しにする(計画 §8.5) *)
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

(* ## 14.13 宣言の実行 — インスタンス表に触る唯一の場所

   トップレベルの `let` / `let rec` は globals へ直に置きます。バックパッチが
   要らないのは §14.9 で述べたとおりです。

   `type instance` の処理には、敵対的検証で見つけた欠陥の修正が 2 つ入っています。

   **(1) 同義語表を引く。** module は型検査の前に平坦化されます(第11章の
   `flatten_modules`、実装記録の乖離5)。`module BigInt { newtype BigInt … }` の
   型は `BigInt.BigInt` に改名されます。
   インスタンス頭に書かれた非修飾名をそのまま鍵にすると、宣言した実体が
   実行時に見つかりません(検証の健全性 6)。`Decls.resolve_con` に通して
   elab と同じ名前へ寄せます。M16 から同義語は module スコープ(D43)なので、
   `exec_decl` の冒頭で宣言の出身 module を `Decls.current_module` に立てて
   から引きます — elab の `with_decl_module` と同じ規律です。回帰テストは
   test/verify_fixes.t の modinst.kel です。

   **(2) 組み込みインスタンスを差し替えない。** `type instance Add[Int32]` を
   ユーザが再宣言できてしまうと、elab は組み込みの `Add[Int32]` で型検査し、
   実行時だけユーザの実体が使われます。検証では `2 + 3` が `-1` になりました
   (健全性 5)。組み込みクラスの組み込みキーと同じ `(cls, con)` は、宣言を
   受理したうえで**実体を差し替えません**。

   > 実行時にだけ効く差し替えは、型検査が見ている世界との分裂である。

   `extern` は、実装が無ければ「呼ばれた時点で落ちる prim」を登録します。宣言だけ
   して呼ばないプログラムを通すためで、**同名の extern どうし**の嘘の型の
   再宣言は elab が拒否します(健全性 8。登録簿の射程は §6.2)。上の格言を
   この関数の `DLet` / `DExtern` 枝自身が守る仕組みが、次の `bind_globals`
   です — かつては素の `Hashtbl.replace` で、既存の globals(先行する `let`、
   組み込みクラスメソッドの修飾名)を黙って上書きし、トップレベルの同名
   再束縛で型検査と実行が別の実体を選べました(260829-5 課題台帳 V1)。
   `type` / `newtype` / `effect` / `type class` は実行時に何もしません
   — 値を作らない宣言で、必要な情報は第6章の表に入っています。`module` は
   平坦化を通っていれば到達しません。 *)

(* トップレベル束縛の早期/遅延の整合(V1)。globals は呼び出し時に引く
   (前方参照のため)が、elab は宣言時点の環境で名前を解決する。同名の
   再束縛を同じ表への Hashtbl.replace にすると、**先に定義済みの関数まで**
   新しい実体を見てしまい、型検査と実行が別の実体を選ぶ(黙って別の値が
   返る形まで実測 — 260829-5 台帳 V1)。そこで再束縛のときだけ表を複製し、
   以後の宣言は新しい表で評価する。既存の閉包は古い表を持ち続けるので
   定義時点の名前を見る。**新しい名前**の追加は生きている全版に入れる —
   前方参照(1c 署名つき)は古い閉包からも見えるべきものだから。
   複製は再束縛のときだけ走るので、通常のプログラムでは 1 度も起きない。
   代価は病的な入力にある: 再束縛 K 回 + 新名 N 個で O(K・N) の時間と
   メモリ(実測 8000+8000 で 11 秒・2.4 GB。260829-5 台帳 V13、M19) *)
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
  (* 宣言の出身 module を環境に立てる。この宣言から作られる閉包が
     mod_scope を捕まえ、実行時の非修飾名解決が elab の current_module と
     同じスコープ規則になる(D43)。インスタンス頭の resolve_con も同じ
     スコープで引くため、Decls 側の current_module も一時的に立てる *)
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
      (* 再束縛があるなら、本体を評価する前に表を差し替える — 閉包が新しい
         表を捕まえないと、自己再帰が古い実体を呼ぶ *)
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
      (* module 平坦化の同義語を通す(BigInt.BigInt 等。検証で発見)。
         組み込み(Add[Int32] 等)と同じキーのユーザ宣言は実体を差し替えない
         — elab は組み込みを使うので、実行時だけ差し替わるとコヒーレンスが破れる(検証で発見) *)
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
      (* 解決キャッシュの無効化(H12)。宣言より前の呼び出しが覚えた
         None を残すと、この宣言が二度と見えない *)
      Hashtbl.reset resolution_cache;
      env
  | T.DExtern ex ->
      let impl =
        (* 宣言の ABI で表を選ぶ(C4)。実装の鍵は非修飾の ex_prim(H14)。
           globals への登録名は修飾された ex_name のまま *)
        match Builtin.find_extern ~abi:ex.T.ex_abi ex.T.ex_prim with
        | Some f -> f
        (* 実装が無くても宣言は通す。落ちるのは呼ばれた時点。表を引いた鍵は
           ex_prim なので、修飾名と食い違うときは両方見せる(検証の指摘) *)
        | None ->
            fun _ ->
              runtime_error
                ("未実装のプリミティブ: " ^ ex.T.ex_name
                ^ if ex.T.ex_name = ex.T.ex_prim then "" else "(実装名 " ^ ex.T.ex_prim ^ " が見つかりません)")
      in
      bind_globals versions env [ (ex.T.ex_name, VPrim { p_name = ex.T.ex_name; p_fn = impl }) ]
  | T.DType _ | T.DNewtype _ | T.DEffect _ | T.DClass _ -> env
  | T.DModule _ -> runtime_error "module の評価は未実装です(M10)"

(* ## 14.14 run — 最外周に 1 枚だけ敷く

   `run` は宣言を順に実行するだけですが、全体を `Builtin.with_runtime`(第13章)
   の中で走らせます。これがランタイム提供エフェクトのハンドラで、
   `Console.write` を出力シンクへ、`Async.yield_` / `Async.sleep` を即 continue へ
   落とします。ここにも届かなかった操作は `Effect.Unhandled` として driver が
   操作名込みで報告します(計画 §8.4)。

   > プログラムの外側はハンドラである。エフェクトを「未処理」にする場所を 1 つ決める。

   冒頭の 3 つの `Hashtbl.reset` は、同じプロセスで `run` を繰り返すテストのため
   です(インスタンス表と、第13章のメモリ上ダミーファイルシステム)。前回の
   実行の痕跡が次の実行に漏れると、ゴールデンが実行順に依存し始めます。

   返り値は捨てます。暗黙の main はなく、トップレベルの式文は順に実行されるだけで、
   その値は誰も見ません(計画 §8.7)。 *)

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

(* ## 14.15 この章の限界と、次に足すもの

   ### fiber の上では Stack_overflow が遅れて来る

   ハンドラの本体は fiber の上で走ります。fiber のスタックはヒープ上で伸びるので、
   暴走した再帰が `Stack_overflow` として現れるのは通常のスタックより**遅い**
   — 先にメモリを食い、`Out_of_memory` として現れることもあります。だから
   driver (第16章) は `Stack_overflow` と `Out_of_memory` を同じ終了コード 3 に
   落としています。同じ理由で、深い非末尾再帰の「限界」を評価器のテストで
   固定するのは意味がありません(環境のメモリ量で変わるため)。

   ### 残している穴

   - **ハンドラの外への後送り(re-perform)**。同じハンドラの中の節どうしは
     フォールスルーします(§14.10、D28)が、全節が外れた操作を外側のハンドラへ
     流すことはできません。機構は 3 行で書けることを実測済みですが、handle が
     E を消すという型付け(§11.24)と両立せず、部分ハンドラの型は仕様側の
     裁定待ちです。
   - **前方参照の値を、定義より前に評価される位置で使う**こと。パス 1c の
     シグネチャで型は通りますが、`let x = g(1)` の右辺のような**即時に評価
     される位置**から前方の `g` を呼ぶと、実行はまだ値を持たず
     「未束縛の変数」で落ちます。かつてはこの分裂がもっと広く、同名の
     **再束縛**(`let` の後の同名 `let` / `extern`、クラスメソッドと同名の
     トップレベル束縛)でも型検査と実行が別の実体を選び、誤った値が黙って
     返る形まで実測されました(260829-5 の課題台帳 V1)。そちらは §14.13 の
     版複製と elab の先勝ち登録(§11.33 / §11.36)で塞ぎ、残ったこの形は
     **黙って誤る**のではなく実行時エラーで落ちる — 誤るなら見逃す側では
     なく音を立てる側、という点で許容しています(遅延束縛で前方参照を通す
     設計の代価)。インスタンス宣言より前の位置でそのインスタンスを使う形も
     同じ側に倒してあります(§14.7。M22 の検証で、`derive structural` を持つ
     `Eq` では黙って構造的等価に落ちていました)。ただし **module の値同義語が絡むと、この保証はまだ
     破れます**(260829-5 課題台帳 V12)。elab は宣言時点の環境+同義語
     フォールバック、評価器は呼び出し時の globals + 同義語フォールバックで
     名前を引くため、module 内の名前と同名のトップレベル束縛が両方いると、
     フォールバックの発火が両者で食い違い、型検査と実行が別の実体を
     選べます(実測)。M16 の同義語の module スコープ化(D43 の射程拡大)で
     塞ぐ予定です。

   ### 静的化への移行路

   D3 は動的ディスパッチを選びましたが、逃げ道は開けてあります。elab が呼び出し
   地点の `resolved` にインスタンスを注記すれば、`dispatch` の表引きを飛ばせます。
   **動的ディスパッチをフォールバックに残したまま**段階的に移行できるので、
   v1 で高階カインドが入り `pure` のような型からしか決まらないメソッドが
   必要になった時点で発動できます(計画 §8.5)。§14.7 の解決キャッシュが
   入ったので、焼き込みの動機は性能から HKT へ移りました(D37)。

   この章で外すと静かに壊れるものを、最後にもう一度並べておきます。

   1. 起動ごとの `inst` 採番(共有すると入れ子で `Unwind` を横取りする)
   2. 未 resume と例外脱出の両方での `discontinue`(落とすと資源が漏れる)
   3. 節本体が `Resume` のときの末尾 `continue`(落とすと実用速度を失う。
      ただし引数の評価は包む — 包み忘れると資源が漏れる)
   4. クラスパラメータ位置だけでのディスパッチ(外すとコヒーレンスが破れる)
   5. `let` による評価順序の固定(外すと観測できる意味論が変わる) *)
