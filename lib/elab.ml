(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第11章 — 型推論の本体

   ここが Keleut の型検査器です。第5章 (tree.ml) が用意した精緻化木を
   受け取り、節点ごとに型と解決結果を書き込みながら、第8章 (unify.ml) の
   単一化器を呼びます。名前と宣言の表は第6章 (decls.ml)、演算子と
   ランタイムエフェクトの表は第7章 (prims.ml)、網羅性の遅延キューは
   第10章 (exhaust.ml) から借ります。出ていくのは「型が書き込まれた木」で、
   第14章 (interp.ml) はそれをそのまま歩いて評価します。

   この章が一貫して守る 3 つの約束を先に置きます。

   - **eff は下向きに渡す。** 戻り値でエフェクト集合を持ち上げるのではなく、
     「いまここで許されているエフェクト行」を引数で配ります (MiniLang §11)。
     perform に出会ったら、その行に単一化を 1 回かけるだけで済みます。
   - **level は常に引数。** グローバル変数にしません。型エラーで大域脱出しても
     レベルが戻し損ねられることが原理的に起きません (計画 R9)。
     MiniLang が try/finally で守っていた不変条件を、引数渡しで消しています。
   - **推論の結果は木に書く。** elab_exp は型を返すと同時に set_ty し、
     コンストラクタ・操作・節の解決結果を set_resolved します。
     評価器が名前解決をもう一度やらずに済むのは、この書き込みのおかげです。

   ## 宣言処理のパス構成

   トップレベルは 1 回では片付きません。前方参照 (sample.kel:334 の
   `user_names` が後方の `println`(:347) を呼ぶ) と、宣言どうしの相互再帰を
   通すために、宣言列を 4 回なめます。

   | パス | 登録するもの | なぜ独立のパスか |
   |---|---|---|
   | 1a | エイリアスの表、newtype の**頭** (名前とカインド) | 型の本体を書く前に全構成子のカインドが引けている必要がある |
   | 1b | newtype の ctor、effect の操作、class のメソッド | 型の本体を書くのでカインド表が要る。宣言順に依存しない |
   | 1c | インスタンスの頭、**注釈が完全な** let の署名 | 頭の検査にクラス表が要る。署名は前方参照の材料 |
   | 2 | let / let rec / 式 / extern / インスタンス本体 | 宣言順に本体を推論し、順に型を印字する |

   1a〜1c が「表を埋める」パス、2 が「本体を推論する」パスです。
   1c の署名登録だけは半端な存在で、注釈が完全でない let は登録されず、
   宣言順に依存したままになります。その線をどこに引くかが後で問題になります
   (§11.36)。

   ## 主要関数の一覧

   | 関数 | 役目 |
   |---|---|
   | `elab_type` / `elab_eff` | 表層の型式 → 内部型 / エフェクト行。展開とカインド検査を含む |
   | `expand_alias` | エイリアスの透過展開。非再帰・部分適用禁止をここで守る |
   | `elab_pat` | パターン → 単相束縛を足した環境。期待型に対する検査 |
   | `is_value` | 値制限の構文判定 |
   | `elab_exp` / `elab_exp'` | 式 → 型。木に型を書き込む |
   | `elab_check` | 軽い検査モード。ラムダと引数レコードにだけ期待型を押し込む |
   | `resolve_perform` | 操作名 → (エフェクト, 操作, スキーマ)。非修飾は行の最左優先 |
   | `check_resume_static` | resume が第二級であることの構文検査 (D19) |
   | `elab_handle` | handle の節分類・対象エフェクト決定・型付け |
   | `elab_binding` / `elab_rec_bindings` | let / let rec。Rigid の生成と解放 |
   | `make_rigids` / `open_explicit_eff` / `release_rigids` | 注釈の skolem 化の 3 点セット |
   | `register_newtype` ほか `register_*` | パス 1 の宣言登録 |
   | `fully_effected` / `signature_of_binding` | パス 1c の前方参照シグネチャ |
   | `check_instance_bodies` | インスタンス本体の包摂検査 |
   | `process_decls` / `type_check_decls` / `type_check` | 入口 |
   | `flatten_modules` | module の平坦化 (D21) |

   長い章ですが、繰り返し出てくる形は多くありません。読みながら
   「レベルを上げる → 剛定数を作る → 出口で漏れを見る」という 3 行の型
   (§11.17 と §11.28) が何度現れるかを数えてみてください。 *)

open Aux
open Syntax
open Type
module T = Tree.Tree
module SMap = Map.Make (String)

(* ## 11.1 環境は 3 つのフィールドしかない

   環境は不変の Map を値渡しします (D10)。enter / leave のような破壊的な
   スコープ操作を持たないので、「戻し忘れ」というバグの種が構造的に
   存在しません。型エラーで大域脱出しても、呼び出し元が持っている env は
   汚れていません。

   フィールドは 3 つです。`values` は変数の型 (Generic を含む型がそのまま
   スキーマの役をします。型スキーマ専用のデータ型は D11 により持ちません)、
   `types` は型パラメータの束縛 (リージョン変数 `h` も同じ棚に載ります)、
   `resume_ty` は操作節の中だけ Some になる 2 つ組です。

   `resume_ty` が env の一部であることが、resume が第一級の値でないという
   設計 (D19) の実装上の表明です。resume は値ではないので `values` には
   入りません。§11.21 でこの選択の代償を見ます。

   警告は溜めてから印字します。`current_out` は「型エラーで打ち切られるまでに
   確定した出力行」で、driver がエラー時にもここまでの結果を印字するために
   参照します (第16章)。

   `closed_item_row` は引数リストを閉じた `_item` 行に畳むだけの補助ですが、
   Keleut の arity 検査はすべてこの**閉じた行**の単一化から出てきます (D5)。
   引数の個数が合わないという専用の検査はどこにもありません。 *)

type env = {
  values : ty SMap.t;
  types : ty SMap.t; (* 型パラメータ束縛(リージョン変数 h を含む) *)
  resume_ty : (ty * ty) option; (* (操作の返り値型, handle 式全体の型)。操作節の中でのみ Some(計画 §7.3) *)
}

let warnings : string list ref = ref []

let warn msg = warnings := !warnings @ [ msg ]

(* 型エラーで打ち切られるまでの出力行(driver がエラー時にも印字する) *)
let current_out : string list ref = ref []

let closed_item_row tys = List.fold_right (fun t acc -> TRowExtend (l_item, t, acc)) tys TRowEmpty

(* ## 11.2 数値リテラルの型 — 述語を制約集合に相乗りさせる

   `1` の型は何か。Keleut は Int32 / Int64 / Float64 の 3 つを持つので、
   即断できません。ここで取る手は D8 の裁定です。

   > 整数リテラルは、`Integral` という**予約されたクラス制約**を貼った
   > 新しい型変数にする。

   専用の「リテラル型」も、専用の遅延解決フェーズも作りません。第8章の
   `add_class` がすでに持っている「型変数に貼りついた制約集合」に相乗りする
   だけです。ただ乗りの効き目は `1 + x` で分かります。この式は
   `{Integral, Add}` という 2 つの制約が同じ変数に載った状態になり、
   単一化のたびに両方が伝播します。リテラル述語のために書いた追加コードは
   ゼロなのに、既定化とクラス解決の相互作用が最初から正しく振る舞います。

   接尾辞が付いていれば具体型に落ちます。v0 が実行できるのは 3 種だけなので、
   それ以外の幅は「名前は受理してエラーにする」形で拒否します (D13)。
   黙って別の幅に丸めるより、書けないと言うほうが親切です。

   `Integral` / `Fractional` の残骸は、宣言の終わりで `default_numerics` が
   Int32 / Float64 に落とします (第8章)。既定化が先に走るので、通常の型表示に
   これらの述語は現れません。 *)

let number_ty level (n : number) : ty =
  match n.n_suffix with
  | Some (NsInt 32) -> t_int32
  | Some (NsInt 64) -> t_int64
  | Some (NsFloat 64) -> t_float64
  | Some _ -> type_error ("数値接尾辞 " ^ Lexer.show_number n ^ " は v0 では未対応です(i32/i64/f64 を使ってください)")
  | None ->
      let v = new_var level in
      Unify.add_class v (if n.n_is_float then cls_fractional else cls_integral);
      v

(* v0 で名前だけ受理して実行できない数値型(D13) *)
let unsupported_numeric = [ "Int8"; "Int16"; "UInt8"; "UInt16"; "UInt32"; "UInt64"; "Float32" ]

(* ## 11.3 型式の精緻化 — 書かれた型を内部型へ

   `elab_type` は表層の型式を第1章の内部型に変換します。名前解決・エイリアス
   展開・カインド検査がここで同時に済みます。専用のカインド検査パスは
   ありません。「引数の個数が宣言のカインドと合うか」を見るだけで、
   それがカインド検査の全部です (MiniLang §5.2 と同じ割り切り)。

   名前の引き方には優先順位があります。

   1. `env.types` にある名前 — 型パラメータとリージョン変数。ここが最優先で、
      内側の `[A]` は外側の型構成子 `A` を隠します。
   2. 型エイリアス — あれば**その場で展開**します (§11.5)。
   3. 宣言表の型構成子 — カインドを引き、引数の個数を照合します。

   `Decls.resolve_con` を必ず通すのは module 平坦化 (§11.42) の同義語表を
   引くためです。`module Parser` の中で `Parser` と書いても、外から
   `Parser.Parser` と書いても同じ oid に行き着きます。

   `EApply` の頭が型パラメータのときだけは扱いが違い、`tapp` で適用を組み立て、
   カインドは使用時に `kind_of` と `drop_arrows` が決めます。これが高階カインド
   (`F[_]`) の実装のすべてです。**型レベルλを入れない**ので、`f a ~ List Int` は
   `f ~ List, a ~ Int` に構造分解でき、単一化は一階のままです。

   `unsupported_numeric` にある名前をここで弾いているのは、`Int8` を
   「未知の型」と言われるより「v0 では未対応」と言われたほうが読み手の
   時間を返せるからです。 *)

let rec elab_type env level ~expanding ((_, te) : T.type_exp) : ty =
  match te with
  | T.EIdent (LongId [ n ]) -> (
      match SMap.find_opt n env.types with
      | Some t -> t
      | None ->
          if List.mem n unsupported_numeric then type_error ("数値型 " ^ n ^ " は v0 では未対応です(Int32/Int64/Float64 を使ってください)")
          else
            let oid = Decls.resolve_con (intern n) in
            (match Hashtbl.find_opt Decls.aliases oid with
            | Some info -> expand_alias env level ~expanding info []
            | None ->
                if Hashtbl.mem Decls.con_kinds oid then (
                  match Decls.con_kind oid 0 with
                  | KStar -> TCon (oid, [])
                  | _ -> type_error ("型構成子 " ^ n ^ " には型引数が必要です"))
                else type_error ("未知の型: " ^ n)))
  | T.EIdent li ->
      (* 平坦化済み module の修飾型参照(Parser.Parser 等) *)
      let oid = Decls.resolve_con (intern (show_long_id li)) in
      if Hashtbl.mem Decls.con_kinds oid then (
        match Decls.con_kind oid 0 with
        | KStar -> TCon (oid, [])
        | _ -> type_error ("型構成子 " ^ show_long_id li ^ " には型引数が必要です"))
      else type_error ("未知の型: " ^ show_long_id li)
  | T.EApply ((_, T.EIdent (LongId comps)), args) when List.length comps > 1 ->
      let oid = Decls.resolve_con (intern (String.concat "." comps)) in
      if Hashtbl.mem Decls.con_kinds oid then (
        let k = Decls.con_kind oid (List.length args) in
        let rec arity k = match kind_repr k with KArrow (_, r) -> 1 + arity r | _ -> 0 in
        if arity k <> List.length args then type_error ("型構成子 " ^ String.concat "." comps ^ " の引数の個数が不正です")
        else TCon (oid, List.map (fun a -> elab_type env level ~expanding (check_no_hole a)) args))
      else type_error ("未知の型: " ^ String.concat "." comps)
  | T.EApply ((_, T.EIdent (LongId [ n ])), args) -> (
      match SMap.find_opt n env.types with
      | Some t ->
          (* HKT 変数への適用。カインドは使用時に kind_of / drop_arrows が確定する *)
          List.fold_left (fun acc a -> tapp acc (elab_type env level ~expanding a)) t (List.map (fun a -> check_no_hole a) args)
      | None -> (
          let oid = Decls.resolve_con (intern n) in
          match Hashtbl.find_opt Decls.aliases oid with
          | Some info -> expand_alias env level ~expanding info args
          | None ->
              if Hashtbl.mem Decls.con_kinds oid then (
                let k = Decls.con_kind oid (List.length args) in
                let rec arity k = match kind_repr k with KArrow (_, r) -> 1 + arity r | _ -> 0 in
                let expected = arity k in
                if expected <> List.length args then
                  type_error (Printf.sprintf "型構成子 %s の引数は %d 個必要です(%d 個与えられました)" n expected (List.length args))
                else TCon (oid, List.map (fun a -> elab_type env level ~expanding (check_no_hole a)) args))
              else type_error ("未知の型: " ^ n)))
  | T.EApply _ -> type_error "型適用の頭は型名でなければなりません"
(* ## 11.4 矢印・レコード行・ヴァリアント和

   矢印 `(A, B) => R @ E` は `TArrow (引数レコード, 返り値, エフェクト行)` に
   なります。引数は閉じた `_item` 行のレコードなので、`(A) => R` と
   `(A, B) => R` は行の長さが違うというだけで別の型になります。

   `@` を省いた矢印は**新しい行変数**を作ります (sample.kel:315-316)。
   これは「エフェクトは何でもよい」の意味で、`@ {}` と書いたときの
   「純粋」とは全く違います。この差はあとで前方参照の穴になります
   (§11.36)。

   `extends` の右は 2 通り受けます。行そのものと、レコード型です。後者は
   行を取り出して splice します。`{x: Int32 extends Point}` が書けるのは
   このためで、Point の行がその場に展開されます。

   ヴァリアント和 `#Even | #Odd | R` は各要素を行に落として `row_append` で
   連結します。ここで 1 つだけ規則を課しています。

   > 開いていてよいのは末尾の要素だけ。

   途中に開いた行が来ると、連結後にどのラベルがどの尾部に属するのかが
   決まりません。閉じた要素どうしの連結なら結果も閉じ、`report`
   (sample.kel:157-162) が `case _` なしで網羅と判定されます。ヴァリアント和が
   網羅性検査 (第10章) と噛み合うのは、この「閉じたまま連結できる」性質
   ちょうどそのものです。

   `EHole` (`_`) はインスタンス頭の `List[_]` 専用です。型式の一般の位置に
   穴を許すと部分適用と同じ問題に踏み込むので、ここで拒否します。 *)

  | T.EArrow (params, ret, eff_opt) ->
      let param_tys = List.map (elab_type env level ~expanding) params in
      let eff = match eff_opt with None -> new_row_var level | Some e -> elab_eff env level ~expanding e in
      TArrow (TRecord (closed_item_row param_tys), elab_type env level ~expanding ret, eff)
  | T.EBraceRow (elems, ext) ->
      let tail =
        match ext with
        | None -> TRowEmpty
        | Some t -> (
            let tt = elab_type env level ~expanding t in
            match repr tt with
            | TRecord row -> row (* {x: T extends Point}: レコード型の行を splice *)
            | t' ->
                if Unify.kind_of t' = KRow || same_kind (Unify.kind_of t') KRow then t'
                else type_error "extends の右は行かレコード型でなければなりません")
      in
      let row =
        List.fold_right
          (fun elem acc ->
            match elem with
            | T.BField (l, t) -> TRowExtend (intern l, elab_type env level ~expanding t, acc)
            | T.BLabel _ -> type_error "エフェクトラベルはこの位置(レコード型)では使えません")
          elems tail
      in
      TRecord row
  | T.EVariantCase (s, payload) ->
      let pty = match payload with None -> t_unit | Some t -> elab_type env level ~expanding t in
      TVariant (TRowExtend (intern s, pty, TRowEmpty))
  | T.EUnion ts ->
      (* 各要素を行に落として連結(計画 §7.3)。開いてよいのは末尾要素だけ *)
      let n = List.length ts in
      let rows =
        List.mapi
          (fun i t ->
            let is_last = i = n - 1 in
            match snd t with
            | T.EVariantCase (s, payload) ->
                let pty = match payload with None -> t_unit | Some t -> elab_type env level ~expanding t in
                TRowExtend (intern s, pty, TRowEmpty)
            | _ -> (
                let tt = elab_type env level ~expanding t in
                match repr tt with
                | TVariant row ->
                    let _, tail = row_fields row in
                    if (not is_last) && repr tail <> TRowEmpty then type_error "ヴァリアント和の途中の要素は閉じていなければなりません"
                    else row
                | t' ->
                    if same_kind (Unify.kind_of t') KRow then
                      if is_last then t' else type_error "ヴァリアント和の途中に行変数は置けません"
                    else type_error ("ヴァリアント和の要素になれない型です: " ^ Show.show t')))
          ts
      in
      let rec fold = function [] -> TRowEmpty | [ r ] -> r | r :: rest -> row_append r (fold rest) in
      TVariant (fold rows)
  | T.EHole -> type_error "_ はこの位置では使えません(インスタンス頭の List[_] 専用)"

(* ## 11.5 エイリアスは透過・非再帰・部分適用禁止

   型エイリアスは**透過**です。表に本体をしまっておき、使われるたびに
   その場で精緻化して展開します。展開後の型に「元はエイリアスだった」という
   痕跡は残りません。表示が `IoError | ParseError` ではなく展開後の行になるのは
   その代償で、これは承知の上です。

   透過にしたうえで、硬い規則を 2 つ課します。

   > **規則 1: エイリアスは再帰できない。**
   > **規則 2: エイリアスは部分適用できない。**

   規則 1 は `expanding` (展開中のエイリアス名の集合) を引数で持ち回って
   守ります。展開中の名前がもう一度現れたら、そこで打ち切ってエラーにします。
   透過な展開に再帰を許すと単に停止しません。

   規則 2 のほうが重要です。`type P[A] = (A, Int32)` を `P` 単体で
   書けるようにすると、それは実質的に**型レベルλ**です。型レベルλが入ると
   `f a ~ P Int` の解が一意でなくなり、単一化が unitary でなくなって主要型が
   失われます。だから引数の個数が合わないエイリアスはその場でエラーにします。
   MiniLang の見取り図が最初に置いた 2 つの規則 (型レベルλを入れない、
   部分適用できるシノニムを入れない) は、この 1 つの `List.length` 比較として
   実装されています。

   > 型シノニムの部分適用を許した瞬間、それは型レベルλになる。

   `check_no_hole` は、その規則の系です。引数位置に `_` が書けてしまうと
   「引数を捨てる型関数」を書いたのと同じことになるので、インスタンス頭
   以外では穴を拒否します。

   展開の環境は**閉じています**。エイリアス本体から見えるのは自分の型
   パラメータだけで、呼び出し側の `env.types` は引き継ぎません。展開が
   その場のスコープに依存すると、同じエイリアスが場所によって別の型に
   なってしまいます。

   `al_kind` が `EffectRow` のときだけ本体をエフェクト行として精緻化します。
   Keleut では行変数とエフェクト名が構文上同形なので、エイリアスの側に
   カインドの注記が要ります (§11.6)。 *)

and check_no_hole ((_, te) as t : T.type_exp) =
  match te with T.EHole -> type_error "_ はこの位置では使えません(インスタンス頭の List[_] 専用)" | _ -> t

and expand_alias env level ~expanding info args =
  if List.mem info.Decls.al_name expanding then
    type_error ("型エイリアス " ^ name_of info.Decls.al_name ^ " が再帰しています(エイリアスは非再帰)")
  else if List.length args <> List.length info.Decls.al_params then
    type_error
      (Printf.sprintf "型エイリアス %s の引数は %d 個必要です(%d 個与えられました。部分適用は禁止)" (name_of info.Decls.al_name)
         (List.length info.Decls.al_params) (List.length args))
  else
    let arg_tys = List.map (fun a -> elab_type env level ~expanding (check_no_hole a)) args in
    let types =
      List.fold_left2 (fun m tp t -> SMap.add tp.tp_name t m) SMap.empty info.Decls.al_params arg_tys
    in
    (* エイリアス本体は閉じている: 型パラメータだけが見える *)
    let env' = { env with types } in
    let expanding = info.Decls.al_name :: expanding in
    match info.Decls.al_kind with
    | Some "EffectRow" -> elab_eff env' level ~expanding info.Decls.al_body
    | _ -> elab_type env' level ~expanding info.Decls.al_body

(* ## 11.6 エフェクト行の精緻化 — 同形の構文をスコープで分ける

   Keleut では `@ E` (行変数) と `@ Print` (エフェクト名) が構文上まったく
   同じ形をしています。区別できるのは型検査器だけで、その判定がこの関数です。

   1. `env.types` にあり、カインドが行なら — 行変数。
   2. `EffectRow` と注記されたエイリアスなら — 展開して splice。
   3. effect 宣言表にあれば — `@ Print` は `@ {Print}` の略記なので、
      ラベル 1 つの閉じた行にする。

   ここで `same_kind` を使っているのは、arity 0 の型パラメータのカインドが
   宣言時には未定 (`KVar`) だからです (D7)。`[E]` と書いただけでは行なのか型なのか
   分からず、使用位置で決まります。構造比較で `KRow` かどうかを見ると、
   まだ `KVar` のままの行変数を取りこぼします。これは実際に踏んだ罠で、
   同じ取りこぼしが第8章の `rewrite_row` にもあり、`fst({x=1, _item=...})` が
   落ちていました (260829-2b の健全性 1)。

   > カインドは構造で比べず `same_kind` で比べる。まだ変数かもしれない。

   ラベルの引数は 1 つまでです (`Heap[h]` のように)。ラベルの引数欄が
   そのままエフェクトのパラメータで、パラメータを持たないエフェクトは
   そこに `Unit` を置きます。行変数の中置合成 (`{E1, Print}` の `E1`) は
   受けません。行の合成は末尾の `extends` だけ、と決めておくと、
   `row_append` の左辺が常に閉じているという不変条件が保てます。

   相互再帰の 3 関数を定義し終えたら、`~expanding` を空リストで閉じた
   同名の関数で覆います。以降の呼び出し側は展開中集合の存在を知りません。 *)

and elab_eff env level ~expanding ((_, te) as t : T.type_exp) : ty =
  match te with
  | T.EIdent (LongId [ n ]) when SMap.mem n env.types ->
      let tv = SMap.find n env.types in
      if same_kind (Unify.kind_of tv) KRow then tv else type_error ("行カインドではない型パラメータです: " ^ n)
  | T.EIdent (LongId [ n ]) when Hashtbl.mem Decls.aliases (intern n) ->
      let info = Hashtbl.find Decls.aliases (intern n) in
      if info.Decls.al_kind = Some "EffectRow" then expand_alias env level ~expanding info []
      else type_error ("エフェクト位置に Type エイリアス " ^ n ^ " は使えません(: EffectRow を付けてください)")
  | T.EIdent (LongId [ n ]) ->
      (* @ Print = @ {Print} の略記(計画 §7.6) *)
      if Hashtbl.mem Decls.effects (intern n) then TRowExtend (intern n, t_unit, TRowEmpty)
      else type_error ("未知のエフェクト: " ^ n)
  | T.EBraceRow (elems, ext) ->
      let tail =
        match ext with
        | None -> TRowEmpty
        | Some t -> (
            let tt = elab_eff env level ~expanding t in
            if same_kind (Unify.kind_of tt) KRow then tt else type_error "extends の右は行でなければなりません")
      in
      List.fold_right
        (fun elem acc ->
          match elem with
          | T.BLabel (LongId [ n ], []) -> (
              match Hashtbl.find_opt Decls.aliases (intern n) with
              | Some info when info.Decls.al_kind = Some "EffectRow" ->
                  row_append (expand_alias env level ~expanding info []) acc (* 行 splice(計画 §7.6) *)
              | Some _ -> type_error ("エフェクト行に Type エイリアス " ^ n ^ " は置けません(: EffectRow を付けてください)")
              | None ->
                  if SMap.mem n env.types then
                    (* {E1, Print} のような行変数の合成は未対応(末尾 extends のみ) *)
                    type_error ("行変数 " ^ n ^ " は extends の位置にのみ書けます")
                  else if Hashtbl.mem Decls.effects (intern n) then TRowExtend (intern n, t_unit, acc)
                  else type_error ("未知のエフェクト: " ^ n))
          | T.BLabel (LongId [ n ], args) ->
              if not (Hashtbl.mem Decls.effects (intern n)) then type_error ("未知のエフェクト: " ^ n)
              else
                TRowExtend
                  ( intern n,
                    (match args with
                    | [ a ] -> elab_type env level ~expanding a
                    | _ -> type_error "エフェクトラベルの引数は1個までです"),
                    acc )
          | T.BLabel (li, _) -> type_error ("モジュール修飾のエフェクトは未対応です(M10): " ^ show_long_id li)
          | T.BField (l, _) -> type_error ("エフェクト行にフィールド " ^ l ^ " は書けません"))
        elems tail
  | _ -> elab_type env level ~expanding t

let elab_type env level t = elab_type env level ~expanding:[] t

let elab_eff env level t = elab_eff env level ~expanding:[] t

(* ## 11.7 パターン — 期待型に対する検査、束縛は単相

   パターンは推論ではなく**検査**です。上から期待型 `expected` が降りてきて、
   パターンはそれを分解しながら変数を環境に足していきます。

   束縛される変数は必ず**単相**です。パターン変数を一般化しないことが
   ランク 1 多相の一部で、ここで一般化しようとすると `match` の各節が
   別々の型で使える不健全な体系になります。

   `seen` は同一パターン内の変数の重複を弾くためだけの可変リストです。
   環境の値そのものは不変 Map で、足しては引数として次へ渡していきます。
   例外はコンストラクタパターンでフィールドを走査するところだけで、そこは
   `Array.iteri` の都合で環境を ref に溜めています (§11.8)。

   検査モードにしておくと得なことが 2 つあります。第 1 に、リテラル
   パターンが `number_ty` を経由するので、`case 0 =>` が `Integral` 述語つきの
   変数として期待型と単一化され、整数の幅がスクルティニ側から決まります。
   第 2 に、レコードパターンで `rest` を書いたかどうかがそのまま行の開閉に
   なります。閉じた行はタプルの arity 検査そのもので、`(a, b)` が 3 要素の
   タプルに当たらないのは行の長さが合わないからです。専用の検査はありません。

   すべてのパターン節点に `set_ty` しているのは、評価器と網羅性検査が
   同じ型を後から引けるようにするためです。 *)

let rec elab_pat env level seen expected ((_, p) as node : T.pat) : env =
  let set t = Tree.set_ty node t in
  set expected;
  match p with
  | T.PWildcard -> env
  | T.PVar x ->
      if List.mem x !seen then type_error ("同じパターン内で変数 " ^ x ^ " が重複しています")
      else (
        seen := x :: !seen;
        { env with values = SMap.add x expected env.values })
  | T.PAnnot (sub, te) ->
      Unify.unify expected (elab_type env level te);
      elab_pat env level seen expected sub
  | T.PBool _ ->
      Unify.unify expected t_boolean;
      env
  | T.PText _ ->
      Unify.unify expected t_string;
      env
  | T.PNumber n ->
      Unify.unify expected (number_ty level n);
      env
  | T.PRecord (fields, rest) -> (
      let ftys = List.map (fun (l, _) -> (l, new_var level)) fields in
      match rest with
      | None ->
          (* 閉じた行(タプルの arity 検査) *)
          let row = List.fold_right (fun (l, t) acc -> TRowExtend (intern l, t, acc)) ftys TRowEmpty in
          Unify.unify expected (TRecord row);
          List.fold_left2 (fun env (_, sub) (_, t) -> elab_pat env level seen t sub) env fields ftys
      | Some rest_pat ->
          let tail = new_row_var level in
          let row = List.fold_right (fun (l, t) acc -> TRowExtend (intern l, t, acc)) ftys tail in
          Unify.unify expected (TRecord row);
          let env = List.fold_left2 (fun env (_, sub) (_, t) -> elab_pat env level seen t sub) env fields ftys in
          elab_pat env level seen (TRecord tail) rest_pat)
  | T.PVariant (str, sub) ->
      let tf = new_var level in
      let rest = new_row_var level in
      Unify.unify expected (TVariant (TRowExtend (intern str, tf, rest)));
      elab_pat env level seen tf sub
(* ## 11.8 コンストラクタパターン — 並べ替えを木に残す

   `Cons(head, tail)` のようなパターンは、宣言表からコンストラクタを引き、
   データ型のパラメータを新しい変数にして期待型と単一化し、フィールド型を
   `subst_params` で具体化してから部分パターンへ降りていきます。

   面倒なのはフィールドの指定方法が 2 通りあることです。位置引数と
   ラベル指定を混ぜて書けて、ラベル指定なら**欠落を許します** (書かなかった
   フィールドは `_` と同じ)。位置引数を使ったときだけ全フィールドが必要です。
   ラベル指定で欠落を許すのは、フィールドを増やしたときに既存のパターンを
   壊さないためです。

   その割り付け結果 (フィールド位置 → 実引数位置の配列) を `set_resolved` で
   木に書きます。**評価器と網羅性検査に同じ計算をさせない**ためです。
   ラベルの並べ替えを 3 箇所で実装すると、3 箇所がずれた瞬間に、型は通るのに
   値が入れ替わるという最悪の壊れ方をします。

   `dd_opaque` (`newtype T = ???`) の分解をここで拒むのが、表現の隠蔽の
   実装です。型としては使えますが、パターンで中身は覗けません。 *)

  | T.PCtor (li, args) -> (
      let (LongId comps) = li in
      let cname = List.nth comps (List.length comps - 1) in
      if not (cname.[0] >= 'A' && cname.[0] <= 'Z') then
        type_error ("未知のコンストラクタパターン: " ^ show_long_id li ^ "(操作節は handle の中でのみ使えます)")
      else
        match Hashtbl.find_opt Decls.ctor_owner (intern cname) with
        | None -> type_error ("未知のコンストラクタ: " ^ show_long_id li)
        | Some dname ->
            let ctor = intern cname in
            let dd = Hashtbl.find Decls.datas dname in
            if dd.Decls.dd_opaque then type_error ("newtype " ^ name_of dname ^ " の表現は ??? で隠されています")
            else
              let ct = List.find (fun c -> c.Decls.ct_name = ctor) dd.Decls.dd_ctors in
              let nfields = List.length ct.Decls.ct_fields in
              let field_to_arg = Array.make nfields None in
              let positional = List.filter (fun a -> a.T.cap_label = None) args in
              (* 位置引数があるときは全フィールドが必要。欠落の _ 補完はラベル指定パターンのみ(計画 §2.1) *)
              if positional <> [] && List.length args <> nfields then
                type_error
                  (Printf.sprintf "コンストラクタ %s のパターンは %d 個のフィールドを取ります(%d 個与えられました)" cname nfields
                     (List.length args));
              List.iteri
                (fun ai (a : T.ctor_arg_pat) ->
                  match a.T.cap_label with
                  | None ->
                      let rec first i =
                        if i >= nfields then type_error ("コンストラクタ " ^ cname ^ " のパターンの引数が多すぎます")
                        else if field_to_arg.(i) = None then i
                        else first (i + 1)
                      in
                      field_to_arg.(first 0) <- Some ai
                  | Some l ->
                      let lo = intern l in
                      let rec find i = function
                        | [] -> type_error ("コンストラクタ " ^ cname ^ " にフィールド " ^ l ^ " はありません")
                        | f :: rest -> if f.Decls.fi_label = Some lo then i else find (i + 1) rest
                      in
                      let i = find 0 ct.Decls.ct_fields in
                      if field_to_arg.(i) <> None then type_error ("フィールド " ^ l ^ " が二重に指定されています");
                      field_to_arg.(i) <- Some ai)
                args;
              Tree.set_resolved node (Tree.RCtorPat (dname, ctor, field_to_arg));
              let subst =
                List.map (fun (i : var_info) -> (i.vid, new_var ~kind:i.vkind ~classes:i.vcls level)) dd.Decls.dd_params
              in
              Unify.unify expected (TCon (dname, List.map snd subst));
              let env = ref env in
              Array.iteri
                (fun fi arg ->
                  match arg with
                  | Some ai ->
                      let f = List.nth ct.Decls.ct_fields fi in
                      env := elab_pat !env level seen (Unify.subst_params level subst f.Decls.fi_ty) (List.nth args ai).T.cap_pat
                  | None -> ())
                field_to_arg;
              !env)

(* ## 11.9 値制限 — 構文だけで決める

   `is_value` は純粋に**構文的な**判定です。式が値なら一般化してよい、と
   決めます。可変参照がある言語で一般化を無条件に許すと不健全になるので、
   どこかで線を引く必要があり、その線を構文で引くのが最も安上がりです。

   実装上のコツは MiniLang §9 と同じで、「値でないときはレベルを上げない」
   だけです。上げなければその束縛では一般化されません。専用のフラグも
   後処理もありません。

   ブロック (`Seq` や `Let` の連鎖) は**保守的に非値**としています。中身を
   見れば値と分かるブロックもありますが、見ないと決めておくほうが規則が
   短く、誤ったほうへ倒れません。値でないと言い過ぎても不健全にはならず、
   多相性が減るだけです。逆は不健全です。

   > 値制限は、迷ったら非値と言え。 *)

let rec is_value ((_, e) : T.exp) =
  match e with
  | T.Bool _ | T.Number _ | T.Text _ | T.Ident _ | T.Hole | T.Lambda _ | T.RecordEmpty -> true
  | T.Variant (_, v) -> is_value v
  | T.Construct (_, args) -> List.for_all (fun a -> is_value a.T.ca_exp) args
  | T.RecordExtend (r, _, v) -> is_value r && is_value v
  | T.RecordRestriction (r, _) -> is_value r
  | _ -> false

(* ## 11.10 式の精緻化 — 型を返しつつ木に書く

   `elab_exp` の仕事は 2 つです。式の型を返すことと、その型を節点に
   書き込むこと。後者があるので、第14章の評価器は型を引き直せますし、
   `--dump-ast` (第4章) は推論結果を目で確認できます。

   引数は `env` / `level` / `eff` の 3 つ。`eff` が「いまここで許されている
   エフェクト行」で、下向きにだけ流れます。この向きが効くのは perform の
   ところで、上向きに集めて回る実装なら必要になる合流と差分の計算が、
   単一化 1 回に置き換わります (§11.15)。

   以下、節ごとに規則を見ていきます。リテラルは即決、`Hole` は新しい変数で、
   実行時に落ちます。 *)

let rec elab_exp env level eff ((_, e) as node : T.exp) : ty =
  let t = elab_exp' env level eff node e in
  Tree.set_ty node t;
  t

and elab_exp' env level eff node e =
  ignore node;
  match e with
  | T.Bool _ -> t_boolean
  | T.Text _ -> t_string
  | T.Number n -> number_ty level n
(* ## 11.11 変数とラムダ

   変数参照は `instantiate` を呼ぶ主要な場所です。ほかにも呼ぶ場所はあります —
   演算子がクラスのメソッドスキーマを引くところ (§11.13)、perform と操作節が
   操作スキーマを引くところ (§11.15、§11.24)、インスタンス本体の包摂検査
   (§11.38)。ただし、どれも「**表から引いたスキーマの ∀ を剥がす**」という
   同じ用途です。∀ を剥がす操作がこの用途に閉じているので、型クラス制約と
   カインドが複製される場所も、スキーマを引いた直後だけだと分かります (第8章)。

   大文字で始まる名前が値環境に無ければ、引数ゼロのコンストラクタとして
   もう一度探します。`Nil` を `Nil()` と書かせないための小さな配慮です。

   ラムダの本体には**新しい行変数**を割り当てます。ラムダ式そのものは値なので、
   周囲の `eff` には何も足しません。関数を作ることは何のエフェクトも
   起こさない、という当たり前のことが、この 1 行で表現されています。
   起こるのは呼んだときで、それが次の節です。 *)

  | T.Ident li -> (
      let name = show_long_id li in
      match SMap.find_opt name env.values with
      | Some sch -> Unify.instantiate level sch
      | None -> (
          match li with
          | LongId comps when comps <> [] && String.length (List.nth comps (List.length comps - 1)) > 0 ->
              let last = List.nth comps (List.length comps - 1) in
              if last.[0] >= 'A' && last.[0] <= 'Z' then elab_construct env level node last []
              else type_error ("未束縛の変数: " ^ name)
          | _ -> type_error ("未束縛の変数: " ^ name)))
  | T.Hole -> new_var level
  | T.Lambda { l_params; l_body } ->
      let param_tys = List.map (fun _ -> new_var level) l_params in
      let seen = ref [] in
      let env2 = List.fold_left2 (fun env p t -> elab_pat env level seen t p) env l_params param_tys in
      let body_eff = new_row_var level in
      let tr = elab_exp env2 level body_eff l_body in
      TArrow (TRecord (closed_item_row param_tys), tr, body_eff)
(* ## 11.12 適用 — 軽い双方向化と、その必然性

   適用の型付けの骨格は 1 行です。関数の型を
   `TArrow (引数レコード, 返り値, eff)` と単一化する。ここで第 3 要素に
   **呼び出し側の** `eff` を渡すのが要点で、これで「この関数を呼ぶには
   このエフェクトが要る」が呼び出し文脈の行に流れ込みます
   (MiniLang:1319-1324。旧 Diktor はここを結んでいませんでした — 計画 §0.2 の
   既存バグ 4)。

   問題は残りの 2 行の**順番**です。素直に書けば、引数を先に推論してから
   関数型と単一化します。この実装はそうしません。

   1. 関数を推論する
   2. **先に** `TArrow (pvar, tr, eff)` と単一化して、関数型を分解する
   3. 引数を、その `pvar` を期待型として**検査**する (§11.19)

   なぜか。引数がラムダで、その本体が `perform` を含むときに差が出ます。
   非修飾の操作名の解決 (D22) は、その時点でのエフェクト行に**どのラベルが
   見えているか**を見ます。引数を先に推論すると、ラムダの行はまだ何も
   決まっていない新しい行変数で、ラベルが 1 つも見えません。解決が
   間に合わないのです。

   決定的な例が sample.kel:415-419 の `copy` です。

   ```
   let copy(src: String, dst: String): Unit @ Console = {
     with _ = with_file(src)
     with _ = with_file(dst)
     perform write(perform read())
   }
   ```

   `with` は「呼び出しの末尾に継続を足す」構文糖 (第3章) なので、これは
   `with_file(src, fn(_) => ...)` に脱糖されます。`with_file` の宣言は
   `body: () => A @ {File extends E}` なので、期待型を先に押し込めば、
   ラムダの行は `{File extends E}` に確定した状態で本体に入れます。すると
   `write` を解決するとき行に `File` が見えています。順番を入れ替えると、
   ここは「`write` は Console と File の両方にある」という曖昧さのエラーに
   なります。

   計画にはこの双方向化がありませんでした (乖離 2)。実装して初めて、
   D22 の解決規則が「引数の行が先に固まっていること」を暗黙の前提に
   していたと分かった箇所です。

   > 双方向化は多相のためだけの道具ではない。解決の順序を決める道具でもある。 *)

  | T.Apply (f, arg) ->
      let tf = elab_exp env level eff f in
      let tr = new_var level in
      let pvar = new_var level in
      (* 関数の行を呼び出し側の eff と単一化してから、引数を期待型で検査する(§11.12) *)
      Unify.unify tf (TArrow (pvar, tr, eff));
      elab_check env level eff arg pvar;
      tr
(* ## 11.13 演算子とレコードの 4 操作

   演算子は AST に `BinOp` として残し、意味は第7章の表から引きます (D9)。
   `+` はクラス `Add` のメソッド `add` の呼び出しと**同じ型付け**をします
   (`method_scheme` がクラス表からメソッドの型スキーマを引き、それを
   `(左辺, 右辺)` の行に対する矢印と単一化するだけ)。
   つまり演算子のためだけの推論規則はありません。`&&` と `||` だけは
   短絡なので両辺 Boolean の組み込み、`!=` は `Eq.eq` の否定 — この 2 つの
   例外が表の中に閉じているのが、ノードを残した理由です。エラーメッセージに
   演算子の見た目を保てるという実利もあります。

   レコードは 4 つの操作で尽きます。拡張・選択・制限・更新。更新
   (`{r with l = v}`) は「制限してから拡張」と同じ型付けで、**フィールドの型が
   変わってよい**のが特徴です。行に載っている古い型は捨てて、新しい型で
   拡張し直します。

   `RecordEmpty` の型が Unit なのは Keleut の設計です。Unit は空レコードで
   あって、専用の型ではありません。

   構造的ヴァリアント `#Foo(v)` は、ラベル 1 つと**新しい行変数**の行を作ります。
   尾部が開いているので、`#Foo(1)` はそのまま `#Foo | #Bar` の文脈にも渡せます。
   閉じるのは match の網羅性検査 (第10章) と型注釈です。 *)

  | T.BinOp (l, op, r) -> (
      let tl = elab_exp env level eff l in
      let tr = elab_exp env level eff r in
      match Prims.bin_op_sem op with
      | Prims.OpBool ->
          Unify.unify tl t_boolean;
          Unify.unify tr t_boolean;
          t_boolean
      | Prims.OpMethod (cls, m) | Prims.OpMethodNot (cls, m) ->
          let scheme = method_scheme cls m in
          let ret = new_var level in
          Unify.unify (Unify.instantiate level scheme) (TArrow (TRecord (closed_item_row [ tl; tr ]), ret, eff));
          ret)
  | T.Not e ->
      Unify.unify (elab_exp env level eff e) t_boolean;
      t_boolean
  | T.RecordEmpty -> t_unit
  | T.RecordExtend (rest, l, v) ->
      let tv = elab_exp env level eff v in
      let rest_row = new_row_var level in
      Unify.unify (elab_exp env level eff rest) (TRecord rest_row);
      TRecord (TRowExtend (intern l, tv, rest_row))
  | T.RecordSelection (r, l) ->
      let tf = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, tf, rest)));
      tf
  | T.RecordRestriction (r, l) ->
      let tf = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, tf, rest)));
      TRecord rest
  | T.RecordUpdate (r, l, v) ->
      (* 制限してから拡張と同じ型付け(計画 §7.3)。フィールド型は変わってよい *)
      let told = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, told, rest)));
      TRecord (TRowExtend (intern l, elab_exp env level eff v, rest))
  | T.Variant (s, v) -> TVariant (TRowExtend (intern s, elab_exp env level eff v, new_row_var level))
(* ## 11.14 ブロック・let・match・コンストラクタ

   ブロックは各文を同じ `eff` で推論し、末尾式の型を返します。文が無ければ
   Unit です。let と let rec は環境を足して本体へ進むだけで、面白いことは
   すべて `elab_binding` の側で起きます (§11.28)。

   match はスクルティニを推論し、各節のパターンをその型に対して検査し、
   ガードを Boolean と、本体を共通の結果型と単一化します。単一スクルティニ
   だけなのは、Keleut が後置 `v match {...}` しか持たないからです (D18)。
   タプルはレコードなので `(a, b) match` が多スクルティニと同じ表現力を
   与えます。

   網羅性検査はここでは**走らせません**。パターンの列と型を遅延キューに
   積むだけです。理由は順序にあります。`close_variant_rows` が Generic 化
   された行変数に単一化をかけると内部エラーになるので、検査は必ず
   一般化の**前**に流し切らなければなりません。drain する場所は 1 箇所では
   ありませんが、どれも一般化より前です — 束縛群 (`elab_binding` /
   `elab_rec_bindings`) では `generalize` の直前、トップレベル式 (`DExp`) では
   推論の直後 (§11.28、§11.40、計画 §7.2)。

   > 網羅性検査は一般化より前。あとで走らせると、閉じるべき行がもう凍っている。

   コンストラクタの適用は `elab_construct` に委ねます (§11.18)。 *)

  | T.Seq es ->
      let rec go = function
        | [] -> t_unit
        | [ last ] -> elab_exp env level eff last
        | s :: rest ->
            ignore (elab_exp env level eff s);
            go rest
      in
      go es
  | T.Let (b, body) ->
      let env2 = elab_binding env level eff b in
      elab_exp env2 level eff body
  | T.LetRec (bs, body) ->
      let env2 = elab_rec_bindings env level eff bs in
      elab_exp env2 level eff body
  | T.Match (scrut, clauses) ->
      let tscrut = elab_exp env level eff scrut in
      let tres = new_var level in
      List.iter
        (fun ((_, c) : T.clause) ->
          let seen = ref [] in
          let env2 = elab_pat env level seen tscrut c.T.cl_pat in
          (match c.T.cl_guard with
          | Some g -> Unify.unify (elab_exp env2 level eff g) t_boolean
          | None -> ());
          Unify.unify (elab_exp env2 level eff c.T.cl_body) tres)
        clauses;
      Exhaust.queue (List.map (fun ((_, c) : T.clause) -> (c.T.cl_pat, c.T.cl_guard <> None)) clauses) tscrut;
      tres
  | T.Construct (li, args) ->
      let (LongId comps) = li in
      elab_construct env level node
        (List.nth comps (List.length comps - 1))
        ~eff
        (List.map (fun (a : T.ctor_arg) -> (a.T.ca_label, a.T.ca_exp)) args)
(* ## 11.15 perform — 行に 1 回の単一化

   操作の呼び出しは 4 段です。名前を解決し (§11.20)、完全名を木に書き、
   引数を操作スキーマの引数行と単一化し、最後に

   ```
   unify eff (TRowExtend (エフェクト名, Unit, 新しい行変数))
   ```

   をします。この 1 行が「ここでこのエフェクトを起こしてよいか」の検査の
   全部です。`eff` が開いていればラベルが追加され、閉じていれば単一化が
   失敗して「ここでは実行できません」になります。エフェクト集合の包含
   判定も、差分の計算も、どこにも書いていません。行の単一化がそれを
   兼ねています。

   行に載るラベルは**エフェクト名**であって操作名ではありません。
   `perform write(...)` の行に立つのは `File` であって `write` ではない。
   ハンドラが捕まえる単位がエフェクトだからです。

   木に書き込む解決結果は完全名 `Effect.op` の oid です。評価器は名前解決を
   やり直さず、この oid でハンドラを探します (第14章)。 *)

  | T.Perform (li, arg) ->
      let eff_name, op, scheme = resolve_perform env eff li in
      Tree.set_resolved node (Tree.ROp (intern (name_of eff_name ^ "." ^ name_of op)));
      let args_row, op_ret =
        match repr (Unify.instantiate level scheme) with
        | TArrow (a, r, _) -> (a, r)
        | _ -> bug "操作スキーマが矢印型ではありません"
      in
      Unify.unify (elab_exp env level eff arg) args_row;
      (try Unify.unify eff (TRowExtend (eff_name, t_unit, new_row_var level))
       with Type_error msg -> type_error ("エフェクト " ^ name_of eff_name ^ " をここでは実行できません(" ^ msg ^ ")"));
      op_ret
(* ## 11.16 resume の在処 — 環境に置く継続

   `resume` の型付けは、`env.resume_ty` が Some のときだけ通ります。
   Some が入るのは操作節の中だけなので、「resume は操作節の中でしか
   書けない」が環境の形だけで保証されます。

   2 つ組の中身は (操作の返り値型, handle 式全体の型) です。つまり
   `resume(v)` は `v` を操作の返り値型と単一化し、**handle 式全体の型**を
   返します。深いハンドラの型付けそのもので、resume を呼ぶと残りの計算が
   同じハンドラの下で走り切り、最終結果が返ってくることを型が言っています。

   引数の省略は操作の返り値型が Unit のときだけ許します
   (sample.kel:356)。`Unit` と単一化するだけなので、規則は 1 行です。

   なぜ resume を値環境に入れず env のフィールドにしたのか。値として
   束縛できてしまうと、節を抜けたあとに呼べる継続が作れてしまい、
   自動巻き戻し (cancel) が成立しなくなるからです。第二級性の残りの穴は
   次の節で塞ぎます (§11.21)。 *)

  | T.Handle (body, clauses) -> elab_handle env level eff clauses body
  | T.Resume arg -> (
      match env.resume_ty with
      | None -> type_error "resume は操作節の中でのみ使えます"
      | Some (op_ret, tres) ->
          (match arg with
          | Some e -> Unify.unify (elab_exp env level eff e) op_ret
          | None ->
              (* 引数省略は操作の返り値型が Unit のときだけ(sample.kel:356) *)
              Unify.unify t_unit op_ret);
          tres)
(* ## 11.17 run — 「レベルを上げる、剛定数を作る、出口で漏れを見る」

   `run[h] { ... }` はスコープ付きの可変状態です。中で作った `Ref` を外に
   持ち出せないことを、ランク 2 多相を入れずに保証します。実装は 3 行で、
   **順番が全て**です。

   1. スコープに入る**前に**結果用の変数を作る (レベル L)
   2. レベルを上げてから剛定数 `h` を作る (レベル L+1) — これが領域の名前
   3. 本体を `{Heap[h] | eff}` の行で推論し、最後に結果変数と単一化する

   3 で `occurs_adjust` が走り、本体の型の中にレベル L+1 の剛定数が
   残っていれば脱出検査が発火します。1 と 2 の順序を入れ替えると結果変数の
   レベルが L+1 になり、剛定数が素通りします。

   MiniLang §17 が「同じ形が 3 回出てくる」と言っているのがこの 3 行です。
   runST、型注釈の skolem 化、そして (足すなら) 存在型の開封。この実装でも
   同じ形が 2 度目に現れます — §11.25 の `make_rigids` と §11.28 の
   `lvl = level + 1` がそれで、注釈の型パラメータを剛定数にして本体を検査し、
   スコープを出るところで Generic に変えています。名前が違うだけで、
   やっていることは run と同じです。

   > 柔らかい変数は寿命を縮められる。剛定数は縮められない。

   なぜ `Ref[h, A]` という型だけでは足りず、エフェクト行にも `Heap[h]` を
   置くのか。`run h { let r = Ref.new(0); fn() => Ref.get(r) }` が決定的です。
   返る関数の型に `h` は現れず、**エフェクト行にだけ**残ります。行を見ていな
   ければ、この関数は領域の外へ逃げます。

   ちなみに「入れ子の run で外側の Ref が読めない」のは仕様どおりです。
   敵対的検証はこれを誤動作として報告しましたが、Haskell の ST と同じ
   リージョン安全性で、変更していません (260829-2b)。 *)

  | T.Run (h, body) ->
      (* MiniLang:1530-1538。スコープに入る前に結果変数、level+1 で Rigid、本体を Heap[h] 行で推論 *)
      let result = new_var level in
      let heap = new_rigid (level + 1) in
      let env2 = { env with types = SMap.add h heap env.types } in
      let t = elab_exp env2 (level + 1) (TRowExtend (eff_heap, heap, eff)) body in
      Unify.unify result t;
      result

(* ## 11.18 コンストラクタの適用 — 式では全フィールド必須

   パターン側 (§11.8) と対になる処理です。違いは 2 つ。

   - 式では**全フィールドが必須**です。パターンでは欠落を `_` と読みますが、
     値を作るときに欠けたフィールドを黙って埋める意味はありません。
   - 割り付けの向きが逆です。パターンは「フィールド → 実引数」、式は
     「実引数 → フィールド」の配列を木に書きます。評価器が引数を評価した
     順のまま並べ替えられるようにするためです。

   引数を推論するときだけ `eff` が要ります。引数ゼロのコンストラクタは
   `elab_exp` の `Ident` 経路からも来るので、`eff` を省略可能引数に
   しています。引数があるのに `eff` が無いのは呼び出し側の誤りなので
   `bug` で落とします。型検査器の内部矛盾はユーザのエラーではありません。 *)

and elab_construct env level node cname ?eff args =
  let ctor = intern cname in
  match Hashtbl.find_opt Decls.ctor_owner ctor with
  | None -> type_error ("未知のコンストラクタ: " ^ cname)
  | Some dname ->
      let dd = Hashtbl.find Decls.datas dname in
      if dd.Decls.dd_opaque then type_error ("newtype " ^ name_of dname ^ " の表現は ??? で隠されています")
      else
        let ct = List.find (fun c -> c.Decls.ct_name = ctor) dd.Decls.dd_ctors in
        let nfields = List.length ct.Decls.ct_fields in
        let assigned = Array.make nfields false in
        let arg_to_field =
          Array.of_list
            (List.map
               (fun (label, _) ->
                 match label with
                 | None ->
                     let rec first i =
                       if i >= nfields then type_error ("コンストラクタ " ^ cname ^ " の引数が多すぎます")
                       else if assigned.(i) then first (i + 1)
                       else i
                     in
                     let i = first 0 in
                     assigned.(i) <- true;
                     i
                 | Some l ->
                     let lo = intern l in
                     let rec find i = function
                       | [] -> type_error ("コンストラクタ " ^ cname ^ " にフィールド " ^ l ^ " はありません")
                       | f :: rest -> if f.Decls.fi_label = Some lo then i else find (i + 1) rest
                     in
                     let i = find 0 ct.Decls.ct_fields in
                     if assigned.(i) then type_error ("フィールド " ^ l ^ " が二重に指定されています");
                     assigned.(i) <- true;
                     i)
               args)
        in
        if Array.exists not assigned then
          type_error ("コンストラクタ " ^ cname ^ " の引数が不足しています(式では全フィールド必須)");
        Tree.set_resolved node (Tree.RCtor (dname, ctor, arg_to_field));
        let subst =
          List.map (fun (i : var_info) -> (i.vid, new_var ~kind:i.vkind ~classes:i.vcls level)) dd.Decls.dd_params
        in
        List.iteri
          (fun ai (_, e) ->
            let f = List.nth ct.Decls.ct_fields arg_to_field.(ai) in
            let ety =
              match eff with
              | Some eff -> elab_exp env level eff e
              | None -> bug "elab_construct: 引数つきなのに eff がない"
            in
            Unify.unify ety (Unify.subst_params level subst f.Decls.fi_ty))
          args;
        TCon (dname, List.map snd subst)

(* ## 11.19 検査モード — 押し込むのは 2 種類だけ

   これが §11.12 で言った「軽い双方向化」の実体です。期待型を押し込むのは
   **ラムダと引数レコードだけ**で、それ以外は今までどおり型を合成してから
   単一化します。合わない形に出会ったら黙って `fallback` に落ちるので、
   検査モードが失敗して全体が落ちることはありません。

   ラムダの節は、期待型が矢印で、引数が閉じた `_item` 行で、個数が一致する
   ときだけ発火します。このとき本体は期待型の**エフェクト行 `eexp` で**
   推論されます。ここが肝で、これによりラムダ本体に入る前に行のラベルが
   確定します。

   レコード拡張の節が要るのは、呼び出しの引数リストが `_item` の
   `RecordExtend` の連なりに脱糖されているからです (第3章)。期待型の行から
   `rewrite_row` でフィールドを 1 つ取り出し、その型で値を検査し、残りを
   再帰的に検査する。この連鎖があって初めて、期待型が第 2 引数のラムダまで
   届きます。`rewrite_row` が失敗する (そのラベルが無い) 場合も
   `fallback` に落として、エラーは通常経路の単一化に語らせます。

   検査に成功した節点にも `set_ty` を忘れないこと。期待型が押し込まれた
   ノードは `elab_exp` を通らないので、ここで書かないと木に穴が空きます。 *)

and elab_check env level eff ((_, e) as node : T.exp) expected =
  let fallback () = Unify.unify (elab_exp env level eff node) expected in
  match (e, repr expected) with
  | T.Lambda { l_params; l_body }, TArrow (pexp, rexp, eexp) -> (
      match repr pexp with
      | TRecord prow ->
          let fields, tail = row_fields prow in
          if
            repr tail = TRowEmpty
            && List.length fields = List.length l_params
            && List.for_all (fun (l, _) -> l = l_item) fields
          then (
            let seen = ref [] in
            let env2 = List.fold_left2 (fun env p (_, t) -> elab_pat env level seen t p) env l_params fields in
            Tree.set_ty node expected;
            elab_check env2 level eexp l_body rexp)
          else fallback ()
      | _ -> fallback ())
  | T.RecordExtend (rest, l, v), TRecord row -> (
      match Unify.rewrite_row row (intern l) with
      | fty, rest_row ->
          Tree.set_ty node expected;
          elab_check env level eff v fty;
          elab_check env level eff rest (TRecord rest_row)
      | exception Type_error _ -> fallback ())
  | _ -> fallback ()

(* ## 11.20 操作名の解決 — 行の最左が勝つ

   Keleut は操作名の重複を許します。許さざるを得ません。仕様である
   sample.kel 自身が `Console.write`(:342) と `File.write`(:397) を両方
   宣言しているからです。したがって「操作名は大域一意」という素朴な裁定は
   最初から使えません (D22)。

   修飾されていれば話は簡単で、宣言表を直接引きます。問題は非修飾で
   候補が複数あるときです。MiniLang の `lookupOp` は候補の先頭を採りますが
   (:1261-1264)、それは宣言順に依存した誤解決になるので移植しません。

   計画は「現在の eff 行に明示的に現れているエフェクトを優先」としていました。
   実装してみると、これでは足りません。§11.12 の `copy` では行に `File` も
   `Console` も見えていて、`write` が両方に該当します。そこで規則を
   一段精密にしました (乖離 3)。

   > 行に現れる候補のうち、**最左**を採る。

   最左とは何か。Scoped Labels では最左のラベルが最初に一致し、実行時には
   最も内側のハンドラが最初に捕まえます。つまり行の最左は**最内ハンドラ**
   です。型検査の解決と実行時の捕捉が同じ順序を見ている、というのが
   この規則の正当化であって、単なる先勝ちの言い換えではありません。

   `copy` で `write` が `File.write` になるのは、`with_file` が積んだ `File` が
   `Console` より内側 = 行の左にいるからです。そして人間が読んだときの
   直感 — 直近に開いたファイルに書く — とも一致します。

   行に候補が 1 つも現れないときは諦めて、`File.write` のように修飾せよと
   案内します。推測しません。 *)

and resolve_perform env eff li =
  ignore env;
  match li with
  | LongId [ ename; op ] -> (
      let e = intern ename in
      match Decls.find_effect e with
      | None -> type_error ("未知のエフェクト: " ^ ename)
      | Some info -> (
          match List.assoc_opt (intern op) info.Decls.ef_ops with
          | Some scheme -> (e, intern op, scheme)
          | None -> type_error ("エフェクト " ^ ename ^ " に操作 " ^ op ^ " はありません")))
  | LongId [ op ] -> (
      let opo = intern op in
      match Decls.op_candidates opo with
      | [] -> type_error ("未知の操作: " ^ op)
      | [ e ] -> (e, opo, List.assoc opo (Option.get (Decls.find_effect e)).Decls.ef_ops)
      | many -> (
          (* 現在の eff 行に明示的に現れる候補のうち、最左(= 最内ハンドラ)を採る。
             Scoped Labels の最左一致と実行時の最内捕捉に一致する *)
          let labels = List.map fst (fst (row_fields eff)) in
          let pos e =
            let rec go i = function [] -> None | l :: tl -> if l = e then Some i else go (i + 1) tl in
            go 0 labels
          in
          let ranked = List.filter_map (fun e -> Option.map (fun i -> (i, e)) (pos e)) many in
          match List.sort compare ranked with
          | (_, e) :: _ -> (e, opo, List.assoc opo (Option.get (Decls.find_effect e)).Decls.ef_ops)
          | [] ->
              type_error
                ("操作 " ^ op ^ " は複数のエフェクト("
                ^ String.concat ", " (List.map name_of many)
                ^ ")に属します。" ^ name_of (List.hd many) ^ "." ^ op ^ " のように修飾してください")))
  | li -> type_error ("不正な操作名です: " ^ show_long_id li)

(* ## 11.21 resume の第二級性 — 構文だけでは守れない

   D19 は resume を専用の AST ノードにしました。名前ではないので変数に
   束縛できず、値として渡せません。それで第二級性が保証されるかというと、
   **されません**。

   ```
   case print(m) => { let f = fn() => resume(); f() }
   ```

   これは書けてしまいます。`resume` は値になっていませんが、それを含む
   クロージャが値になっており、節の外へ持ち出せます。「構文だけで
   second-class を保証」は成立しない、というのが検証で確定した事実です。

   そこで 2 段構えにします。

   1. **静的**: 節本体を走査し、ラムダの内側に現れた `Resume` をエラーにする
      (この関数、約 40 行)。
   2. **動的**: 実行時に継続の生死フラグを見る (第14章の `r_alive`)。

   走査の細部に 1 つ判断があります。内側の `Handle` に出会ったら、**本体は
   そのまま走査し、節には入りません**。内側のハンドラの節は、その節自身が
   検査を受けるときに自分の文脈で見られるからです。ここで節に入ってしまうと、
   内側の resume を外側の resume と取り違えます。

   静的検査が効いていると何が嬉しいのか。節を抜ける時点で継続の生死が
   確定するので、cancel による自動巻き戻しが成立します (sample.kel:353-356)。
   継続がどこかのクロージャに生き残っている可能性があると、巻き戻しの
   タイミングが決められません。 *)

and check_resume_static ?(in_lambda = false) ((_, e) : T.exp) =
  let go = check_resume_static ~in_lambda in
  match e with
  | T.Resume arg ->
      if in_lambda then type_error "resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)"
      else Option.iter go arg
  | T.Lambda { l_body; _ } -> check_resume_static ~in_lambda:true l_body
  | T.Handle (b, _) -> go b
  | T.Bool _ | T.Number _ | T.Text _ | T.Ident _ | T.Hole | T.RecordEmpty -> ()
  | T.Apply (f, a) ->
      go f;
      go a
  | T.Construct (_, args) -> List.iter (fun (a : T.ctor_arg) -> go a.T.ca_exp) args
  | T.Variant (_, v) -> go v
  | T.BinOp (l, _, r) ->
      go l;
      go r
  | T.Not v -> go v
  | T.Let ((_, b), rest) ->
      go b.T.lb_body;
      go rest
  | T.LetRec (bs, rest) ->
      List.iter (fun ((_, b) : T.let_binding) -> go b.T.lb_body) bs;
      go rest
  | T.Seq es -> List.iter go es
  | T.Match (scrut, cs) ->
      go scrut;
      List.iter
        (fun ((_, c) : T.clause) ->
          Option.iter go c.T.cl_guard;
          go c.T.cl_body)
        cs
  | T.RecordExtend (r, _, v) | T.RecordUpdate (r, _, v) ->
      go r;
      go v
  | T.RecordRestriction (r, _) | T.RecordSelection (r, _) -> go r
  | T.Perform (_, a) -> go a
  | T.Run (_, b) -> go b

(* ## 11.22 handle の節を 3 種類に分ける

   handle の節はエフェクト名ではなく**操作名**で書きます。パーサから見れば
   どれもコンストラクタパターンなので、意味づけはここで行います。

   | 節の形 | 種別 | 意味 |
   |---|---|---|
   | `case print(m) =>` | 操作節 | 小文字始まりの名前は操作。`Print.print` と修飾もできる |
   | `case return(x) =>` | return 節 | 本体が値を返し切ったときの後処理。1 つまで |
   | `case cancel =>` | cancel 節 | 巻き戻されたときの後始末。1 つまで |

   `return` と `cancel` は名前で特別扱いされる予約語ではなく、この分類器が
   見ているだけです。`cancel` は引数を取らない形しか受けません
   (`cancel(reason)` は将来拡張)。操作節は最低 1 つ必要です — 操作を 1 つも
   扱わない handle は、書き手が何かを間違えています。

   分類結果は `set_resolved` で木に書きます。評価器が節の種別を判定し直さない
   ためです (§11.8 と同じ方針)。 *)

and elab_handle env level eff clauses body =
  let classify ((_, c) as cnode : T.clause) =
    match snd c.T.cl_pat with
    | T.PVar "cancel" -> `Cancel cnode
    | T.PCtor (LongId comps, args) -> (
        match List.rev comps with
        | "cancel" :: _ ->
            if args <> [] then type_error "cancel(reason) は将来拡張です(v0 では case cancel のみ)" else `Cancel cnode
        | "return" :: _ -> (
            match args with
            | [ { T.cap_label = None; cap_pat } ] -> `Return (cap_pat, cnode)
            | _ -> type_error "return 節は case return(x) の形で書いてください")
        | op :: quals when op <> "" && op.[0] >= 'a' && op.[0] <= 'z' ->
            `Op (intern op, (match quals with [] -> None | _ -> Some (intern (String.concat "." (List.rev quals)))), args, cnode)
        | _ -> type_error ("handle の節は操作名 / return / cancel で始めてください: " ^ show_long_id (LongId comps)))
    | _ -> type_error "handle の節は操作名 / return / cancel で始めてください"
  in
  let classified = List.map classify clauses in
  let ops = List.filter_map (function `Op (op, q, args, cnode) -> Some (op, q, args, cnode) | _ -> None) classified in
  let rets = List.filter_map (function `Return (p, cnode) -> Some (p, cnode) | _ -> None) classified in
  let cancels = List.filter_map (function `Cancel cnode -> Some cnode | _ -> None) classified in
  (if List.length rets > 1 then type_error "return 節は1つまでです");
  (if List.length cancels > 1 then type_error "cancel 節は1つまでです");
  (if ops = [] then type_error "handle には少なくとも1つの操作節が必要です");
(* ## 11.23 対象エフェクトの決定

   節が操作名で書かれている以上、このハンドラがどのエフェクトを消すのかを
   決めなければなりません。1 つでも修飾があればそれを使い、全部が非修飾なら
   D22 の規則で絞ります。

   1. 全ての操作名を宣言しているエフェクトを集める (`holds_all`)
   2. そのうち、**自分の全操作がこの handle に書かれている**ものだけ残す
      (`covered`)
   3. ちょうど 1 つなら決まり。0 個なら網羅漏れ、2 個以上なら曖昧

   2 の条件があるので、`Console` と `File` のように操作名が重なるエフェクトが
   あっても、`read` と `write` の両方を書けば `File` に決まります。`write` 節
   だけを書いた handle は `Console` に決まります — `Console` の全操作は
   `write` 1 つなので、覆えている候補が `Console` だけになるからです。`File` を
   意図していたなら `File.write` と修飾するか、`read` 節も書いてください。
   逆に「操作が漏れています」と言われるのは、**どの候補も自分の全操作を
   覆えていない**ときです (2 操作を持つエフェクトの片方だけを書いた場合など)。

   修飾されたエフェクトが実在するかを、ここで確かめておくのを忘れないこと。
   検査を落とすと、後段の `Option.get` が `None` を掴んで OCaml の例外が
   そのまま外に出ます。型エラーとして報告されるべきものが処理系のクラッシュに
   なる典型で、敵対的検証で実際に見つかりました (260829-2b の頑健性)。

   > 表を引く前に、その名前が表にあることを確かめる。`Option.get` は検査ではない。

   対象が決まったら、逆向きの検査を 2 つ。対象の全操作が節にあるか、
   そして全ての節が対象に属するか。網羅を要求するのは、ハンドラが
   エフェクトを**消す**と型が言い切るためです。 *)

  (* D22: 対象エフェクトは「全節が属し全操作が網羅される」候補が一意であること *)
  let quals = List.filter_map (fun (_, q, _, _) -> q) ops in
  let op_names = List.map (fun (op, _, _, _) -> op) ops in
  let target =
    match List.sort_uniq compare quals with
    | [ e ] ->
        (* 修飾されたエフェクトが実在するか検査(未検査だと後段の Option.get で落ちる。検証で発見) *)
        if Decls.find_effect e = None then type_error ("未知のエフェクト: " ^ name_of e) else e
    | _ :: _ -> type_error "handle の節の修飾エフェクトが一致しません"
    | [] -> (
        let declares e op = List.mem_assoc op (Option.get (Decls.find_effect e)).Decls.ef_ops in
        let all_effects = List.sort_uniq compare (List.concat_map Decls.op_candidates op_names) in
        let holds_all = List.filter (fun e -> List.for_all (declares e) op_names) all_effects in
        let covered =
          List.filter
            (fun e -> List.for_all (fun (op, _) -> List.mem op op_names) (Option.get (Decls.find_effect e)).Decls.ef_ops)
            holds_all
        in
        match covered with
        | [ e ] -> e
        | [] -> (
            match holds_all with
            | e :: _ ->
                let missing =
                  List.filter
                    (fun (op, _) -> not (List.mem op op_names))
                    (Option.get (Decls.find_effect e)).Decls.ef_ops
                in
                type_error
                  ("ハンドラが操作を網羅していません: " ^ name_of e ^ " の "
                  ^ String.concat ", " (List.map (fun (op, _) -> name_of op) missing)
                  ^ " が漏れています")
            | [] -> type_error ("この操作の組を宣言するエフェクトがありません: " ^ String.concat ", " (List.map name_of op_names)))
        | es ->
            type_error
              ("handle の対象エフェクトが曖昧です(" ^ String.concat ", " (List.map name_of es)
             ^ ")。" ^ name_of (List.hd es) ^ "." ^ name_of (List.hd op_names) ^ " のように修飾してください"))
  in
  let target_info = Option.get (Decls.find_effect target) in
  (* 対象確定後の検査: 全操作の網羅と、全節の所属 *)
  List.iter
    (fun (op, _) ->
      if not (List.mem op op_names) then
        type_error ("ハンドラが操作を網羅していません: " ^ name_of target ^ " の " ^ name_of op ^ " が漏れています"))
    target_info.Decls.ef_ops;
  List.iter
    (fun (op, _, _, _) ->
      if not (List.mem_assoc op target_info.Decls.ef_ops) then
        type_error ("操作 " ^ name_of op ^ " はエフェクト " ^ name_of target ^ " に属しません"))
    ops;
(* ## 11.24 本体・return・cancel・操作節をどの行で推論するか

   型付けの形は MiniLang §11 のハンドラ規則と同じです。

   ```
     Γ ⊢ e : α ! {E | ε}
     Γ, x : α ⊢ r : R ! ε                        -- return 節
     Γ, x : A_op, resume : B_op -> R ⊢ b : R ! ε  -- 操作節
     ---------------------------------------------
     Γ ⊢ e handle { ... } : R ! ε
   ```

   注目すべきは**どの節をどの行で推論するか**です。本体だけが対象エフェクトを
   積んだ内側の行で、return 節・cancel 節・操作節はすべて**外側の** `eff` です。

   return 節と cancel 節が外側なのは、実装を読んで決めたのではなく、
   実行を見て決めました。この 2 つは自分のハンドラが外れた文脈で走ります。
   内側の行で型付けると、型が許したエフェクトを実行時には起こせないという
   食い違いが出ます。

   操作節が外側の行なのは深いハンドラだからです。節の本体は、ハンドラの
   外側と同じ文脈で走ります。

   節ごとの細部を 4 つ。

   - resume の型は「操作の返り値型 → handle 式全体の型」。これを
     `resume_ty` に入れて節本体を推論します (§11.16)。return 節と
     cancel 節では **None に戻します** — そこに継続は存在しません。
   - cancel 節の値は捨てられるので Unit と単一化します。
   - 操作節の引数はラベルで書けません。位置引数だけです。操作の引数は
     宣言の並びが意味を決めているので、並べ替えを許す理由がありません。
   - return 節と cancel 節に**ガードは書けません**。節の構文 (clause) は
     汎用なのでパーサは受けますが、ここで拒否します。この 2 つは 1 ハンドラに
     1 節まで (§11.23) なので、ガードが偽のときに落ちる先がありません。
     かつてはガードを Boolean と単一化だけして受理していました — すると
     第14章の `retc` / `run_cancel` はガードを一度も読まないので、型検査を
     通った条件式が実行時に黙って消えていました。`case return(x) if c => a` と
     書きたければ、節本体で `c` を match すれば同じことが書けます。

   `check_resume_static` を呼ぶのはここ、操作節に入る直前です (§11.21)。 *)

  (* 本体は対象エフェクトを積んだ行で推論 *)
  let body_ty = elab_exp env level (TRowExtend (target, t_unit, eff)) body in
  let tres = new_var level in
  (* return 節・cancel 節は外側の eff で推論(retc/exnc は自分のハンドラが外れた文脈で走る、計画 §7.3) *)
  (match rets with
  | [ (p, ((_, c) as cnode)) ] ->
      Tree.set_resolved cnode Tree.RReturnClause;
      if c.T.cl_guard <> None then type_error "return 節にガードは書けません";
      let seen = ref [] in
      let env2 = elab_pat { env with resume_ty = None } level seen body_ty p in
      Unify.unify (elab_exp env2 level eff c.T.cl_body) tres
  | _ -> Unify.unify body_ty tres);
  (match cancels with
  | [ ((_, c) as cnode) ] ->
      Tree.set_resolved cnode Tree.RCancelClause;
      if c.T.cl_guard <> None then type_error "cancel 節にガードは書けません";
      let env2 = { env with resume_ty = None } in
      (* cancel 節の値は捨てられる: Unit と単一化(計画 §7.3) *)
      Unify.unify (elab_exp env2 level eff c.T.cl_body) t_unit
  | _ -> ());
  (* 操作節 *)
  List.iter
    (fun (op, _, args, ((_, c) as cnode)) ->
      Tree.set_resolved cnode (Tree.ROp (intern (name_of target ^ "." ^ name_of op)));
      let scheme = List.assoc op target_info.Decls.ef_ops in
      let args_row, op_ret =
        match repr (Unify.instantiate level scheme) with
        | TArrow (a, r, _) -> (a, r)
        | _ -> bug "操作スキーマが矢印型ではありません"
      in
      let param_tys = match repr args_row with TRecord row -> List.map snd (fst (row_fields row)) | _ -> [] in
      if List.length args <> List.length param_tys then
        type_error
          (Printf.sprintf "操作 %s は %d 引数です(節には %d 個書かれています)" (name_of op) (List.length param_tys)
             (List.length args));
      List.iter (fun (a : T.ctor_arg_pat) -> if a.T.cap_label <> None then type_error "操作節の引数にラベルは書けません") args;
      let seen = ref [] in
      let env2 =
        List.fold_left2
          (fun env (a : T.ctor_arg_pat) t -> elab_pat env level seen t a.T.cap_pat)
          env args param_tys
      in
      (* 操作節では resume が使える。本体は外側の eff で推論(MiniLang:1499) *)
      let env2 = { env2 with resume_ty = Some (op_ret, tres) } in
      check_resume_static c.T.cl_body;
      (match c.T.cl_guard with Some g -> Unify.unify (elab_exp env2 level eff g) t_boolean | None -> ());
      Unify.unify (elab_exp env2 level eff c.T.cl_body) tres)
    ops;
  tres

and method_scheme cls m =
  match Decls.find_class (intern cls) with
  | Some ci -> (
      match List.assoc_opt m ci.Decls.ci_methods with
      | Some t -> t
      | None -> bug ("組み込みクラス " ^ cls ^ " にメソッド " ^ m ^ " がありません"))
  | None -> bug ("組み込みクラス " ^ cls ^ " が未登録です")

(* ## 11.25 束縛の下ごしらえ — 剛定数の一生

   `let f[A](x: A): A = ...` の `[A]` をどう扱うか。素朴に新しい型変数に
   すると、`fn x => x + 1` を `[A] (A) => A` と注釈しても通ってしまいます。
   注釈は「少なくともこれだけ多相か」を**要求**するものなので、それでは
   意味を成しません。

   正しくは skolem 化です。型パラメータを**剛定数** (Rigid) にして本体を
   検査します。剛定数は代入先になれないので、`A` を Int32 に決めようとした
   瞬間に単一化が落ちます。§11.17 で見た run の 3 行と同じ道具立てで、
   `make_rigids` が 2 番目の行 (剛定数を作る) を担当します。

   カインドは `F[_]` と書かれていればその場で確定し、`[A]` や `[E]` のように
   括弧が無ければ**カインド変数**にしておきます (D7)。Keleut では型パラメータが
   型なのか行なのかを字句で区別できず、使用位置 — `extends` の右か `@` の右か —
   でしか決まらないからです。未解決のまま残ったカインドは宣言の終わりで
   `KStar` に既定化します。

   剛定数の一生は 3 段です。

   1. `make_rigids` — 束縛のレベル + 1 で作る
   2. 本体の検査 — 代入されないことと、外へ漏れないことを単一化が見張る
   3. `release_rigids` — スコープを出たら Generic に書き換える (§11.27)

   この 3 段が閉じているので、注釈付きの束縛は「本体では硬く、環境では
   多相」という 2 つの顔を、型スキーマ用のデータ型を 1 つも持たずに
   実現できています。

   制約に書かれたクラス名は、剛定数を作るこの時点で検証します
   (`class_names_of`)。かつては intern するだけで、未知のクラスは使用点の
   `add_class` (§8.9) まで落ちませんでした。すると `let f[A: Bogus](x: A): A = x`
   という宣言が通り、`f : [A: Bogus] (A) => A` と印字されてから、呼んだ場所で
   ようやく「未知のクラス」になります。どこが悪いのかユーザに分からない
   エラーの出方だったので、入口に検査を寄せました。 *)

(* 型パラメータに書かれたクラス名を oid にする。宣言済みでなければその場で
   落とす。使用点(unify.ml add_class)まで持ち越すと「宣言は通ったのに
   呼ぶと落ちる」ことになり、しかも宣言の印字が先に出てしまう。
   文言は add_class と一字一句そろえる *)
and class_names_of tp =
  List.map
    (fun li ->
      let c = intern (show_long_id li) in
      if Decls.find_class c = None then type_error ("未知のクラス: " ^ show_long_id li);
      c)
    tp.tp_classes

and make_rigids level tparams =
  List.map
    (fun tp ->
      let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var () in
      let classes = class_names_of tp in
      let r = ref (Rigid { vid = new_oid (); vlevel = level; vkind = kind; vcls = classes }) in
      (tp.tp_name, TVar r, r))
    tparams

(* ## 11.26 明示的エフェクト注釈の開放

   計画が想定していなかった裁定です (乖離 1)。`@ Print` と書いたら
   ラベル 1 つの**閉じた**行になる、というのが仕様の字義です。ところが
   それでは sample.kel:357 が型付きません。

   ```
   println(msg) handle {
     case print(message) => resume(perform write(message))
   }
   ```

   `println : (String) => Unit @ Print` の本体は `perform print(...)` ですが、
   この handle の下で `println` を呼ぶと、行は `{Print}` ではなく
   `{Print, Console}` である必要があります。閉じたままではハンドラを通せません。

   そこで、**ラベルの付いた閉じた行の注釈だけ**を開きます。

   | 注釈 | 本体の検査で | 公開スキーマで |
   |---|---|---|
   | `@ Print` / `@ {A, B}` | 尾部に **Rigid** を足して開く | 尾部を **Generic** にして開く |
   | `@ {}` | 閉じたまま | 閉じたまま (純粋) |
   | `@` 省略 | 新しい行変数 (もともと開いている) | 一般化される |

   なぜ本体では Rigid なのか。開くだけなら未定変数でもよさそうですが、それだと
   本体が注釈に書いていないエフェクトを起こしたときに、尾部に勝手に足されて
   通ってしまいます。剛定数なら足せないので、注釈の約束が守られます。
   スコープを出るところで Generic に変えると、呼び出し側は好きな行を尾部に
   継ぎ足せます。

   > 尾部を開くと通しやすくなる。剛くしておくと嘘をつけなくなる。両方要る。

   `@ {}` を閉じたままにしてあるので、「純粋を強制したい」という意図は
   引き続き書けます (sample.kel:316)。なお仕様の字義と実装上の要請が
   食い違っている点は自覚しており、`@ Print` の意味論 (正確に Print だけか、
   Print を含むか) の明文化を親リポジトリへのフィードバック事項として
   記録してあります。 *)

and open_explicit_eff lvl eff =
  let fields, tail = row_fields eff in
  match repr tail with
  | TRowEmpty when fields <> [] ->
      let r = ref (Rigid { vid = new_oid (); vlevel = lvl; vkind = KRow; vcls = [] }) in
      (row_append eff (TVar r), [ ("", TVar r, r) ])
  | _ -> (eff, [])

(* ## 11.27 剛定数の解放

   束縛のスコープを出るとき、この束縛が作った剛定数を Generic に書き換えます。
   これが「注釈の一般化」で、書き換えは in-place です。木にはすでに
   `set_ty` 済みの型が入っていて、それと共有を切らないためです。

   安全性の根拠は、書き換える側ではなく検査する側にあります。剛定数が
   外へ漏れていれば、そこに至るまでの `unify` と `occurs_adjust` がすでに
   捕まえています (第8章)。ここまで来たということは漏れていないということで、
   だから無条件に Generic にしてよいのです。

   ついでにカインドの既定化もここで済ませます。`[E]` と書かれたきり
   どこにも使われなかった型パラメータのカインドは `KVar` のままなので、
   `KStar` に落とします (D7)。 *)

and release_rigids rigids =
  List.iter
    (fun (_, _, r) ->
      match !r with
      | Rigid i ->
          default_kind i.vkind (* 未解決カインドは KStar に既定化(D7) *);
          r := Generic i
      | _ -> ())
    rigids

(* ## 11.28 let 束縛 — 一般化の条件は 2 つだけ

   束縛の処理は、レベルを 1 つ上げ、型パラメータを剛定数にし、注釈を
   精緻化し、本体を推論し、注釈と単一化し、一般化して、剛定数を解放する。
   run と同じ 3 行の形が、ここでは注釈のために使われています。

   ### 一般化してよいのは、関数か構文的な値のとき

   ```
   let gen = is_fun || is_value b.T.lb_body
   ```

   この 1 行が値制限の全部です。そして、ここに**第 3 の条件を足したくなる**
   のが罠でした。「注釈が書いてあるなら書き手の意図を尊重して一般化しよう」
   は自然な発想で、実際にそう書かれていました。それは不健全でした。

   ```
   let slot: Ref[h, T] = Ref.new(...)
   ```

   注釈の中で省略された `@` は独立な新しい行変数を作ります。注釈付きを
   一般化条件に入れると、この束縛が一般化され、`run` が作った剛定数 `h` が
   Generic に化けます。結果として、リージョンの中の可変参照を外へ持ち出せます。
   実証済みの反例です (260829-2b の健全性 2)。

   > 注釈は「多相にしてよい」の証明ではない。値であることの証明だけが証明。

   同じ理由で、非値の束縛に型パラメータを書くことも拒否します。それは
   多相化の要求であり、値制限に真っ向から反します。

   ### 一般化しないときはレベルを上げない

   `lvl = if gen then level + 1 else level` の 1 行で済みます。上げなければ
   `generalize` は何も掴まないので、フラグも後処理も要りません。

   ### 注釈の精緻化は 1 回で済む

   計画は「本体検査用に Rigid で 1 回、環境登録用に Generic でもう 1 回、
   合わせて 2 回 elaborate するのが最短」と見積もっていました。実装は
   1 回です。`release_rigids` が剛定数を**その場で** Generic に書き換えるので、
   同じ型オブジェクトが 2 つの顔を順に持てるからです (§11.27)。
   木に `set_ty` 済みの型と共有が切れないという利点も付いてきます。

   返り値の注釈があれば本体の型と単一化し、失敗を「注釈された返り値型を
   満たしません」に言い換えます。値束縛でも同じことをします — こちらは
   注釈が書かれているときだけ「注釈された型を満たしません」に言い換えます。
   単一化を try で包んでエラーを注釈や宣言の側から語り直す箇所は、この 2 つの
   ほかに perform の行単一化 (§11.15) とインスタンス本体の包摂 (§11.38) が
   あり、合わせて 4 箇所です。

   ### 網羅性の drain はここ

   遅延キューを流すのは `generalize` の**直前**です (§11.14)。
   パターン束縛 (`let (a, b) = ...`) は単一ケースの match と同じ扱いで、
   単相に束縛し、網羅性のキューに載せます (乖離 7)。この経路には一般化が
   無いので、キューに積んだ直後にそのまま流します。 *)

and elab_binding env level eff ((_, b) as node : T.let_binding) : env =
  let is_fun = b.T.lb_params <> None in
  (* 値制限(計画 §7.2): 一般化してよいのは関数定義か値のみ。§11.28 を参照 *)
  let gen = is_fun || is_value b.T.lb_body in
  if (not gen) && b.T.lb_tparams <> [] then
    type_error "非値の束縛に型パラメータは付けられません(値制限。関数にするか値を束縛してください)";
  let lvl = if gen then level + 1 else level in
  let extra_rigids = ref [] in
  let rigids = make_rigids lvl b.T.lb_tparams in
  let env_ty = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types rigids } in
  let fn_ty =
    match b.T.lb_params with
    | Some params ->
        let seen = ref [] in
        let param_tys = List.map (fun _ -> new_var lvl) params in
        let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
        let fn_eff, eff_rigids =
          match b.T.lb_eff with Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e) | None -> (new_row_var lvl, [])
        in
        extra_rigids := eff_rigids @ !extra_rigids;
        let ret_ty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
        let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
        (try Unify.unify ret_ty body_ty
         with Type_error msg -> type_error ("注釈された返り値型を満たしません(" ^ msg ^ ")"));
        TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
    | None ->
        let vty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
        (* 値束縛は外側の eff で評価される *)
        let body_ty = elab_exp env_ty lvl eff b.T.lb_body in
        (try Unify.unify vty body_ty
         with Type_error msg when b.T.lb_ret <> None -> type_error ("注釈された型を満たしません(" ^ msg ^ ")"));
        vty
  in
  Tree.set_ty node fn_ty;
  let rigids = rigids @ !extra_rigids in
  (* 網羅性の遅延キューは generalize の直前に drain する(計画 §7.2) *)
  match snd b.T.lb_name with
  | T.PVar x ->
      List.iter warn (Exhaust.drain ());
      if gen then Unify.generalize level fn_ty;
      release_rigids rigids;
      { env with values = SMap.add x fn_ty env.values }
  | T.PWildcard ->
      List.iter warn (Exhaust.drain ());
      if gen then Unify.generalize level fn_ty;
      release_rigids rigids;
      env
  | _ ->
      (* パターン束縛は単相(単一ケース match と同じ扱い、計画 §6.4)。網羅性警告に乗せる *)
      release_rigids rigids;
      let seen = ref [] in
      let env' = elab_pat env level seen fn_ty b.T.lb_name in
      Exhaust.queue [ (b.T.lb_name, false) ] fn_ty;
      List.iter warn (Exhaust.drain ());
      env'

(* ## 11.29 let rec — 単相で括ってから一般化する

   手順は 4 つ。名前を**単相の**新しい変数で先に束縛する、本体を推論する、
   その変数と単一化する、最後に一般化する。この順序なので再帰呼び出しは
   単相で、**多相再帰はできません**。多相再帰には型注釈が要り、そこまで
   踏み込むと推論が決定不能に近づきます。

   右辺は関数でなければなりません。これは型の都合ではなく評価器の都合です。
   非関数の右辺 (`let rec x = x + 1`) を許すと、型検査は通るのに実行時に
   必ず落ちます。型が通って必ず落ちるものは、型で落とすべきです
   (260829-2b の健全性 9)。

   束縛の名前をパターンにできないのも同じ理由です。相互再帰の前方参照は
   名前が要ります。

   一般化するのは全ての右辺を推論し終えてからで、束縛群として一括です。
   片方だけ先に一般化すると、相互再帰の相手が見ている変数がすでに凍って
   いて単一化に失敗します。 *)

and elab_rec_bindings env level eff bs : env =
  (* 事前割り当ての単相変数で束縛 → 本体推論 → unify → 一般化(既存バグ 0.2-5 の修正)。多相再帰不可 *)
  let lvl = level + 1 in
  let names =
    List.map
      (fun (_, b) ->
        (* let rec の右辺は関数でなければならない(評価器が構造上そう要求する。
           非関数を許すと型検査を通って実行時に必ず落ちる。検証で発見) *)
        (match (b.T.lb_params, snd b.T.lb_body) with
        | None, T.Lambda _ | Some _, _ -> ()
        | None, _ -> type_error "let rec の右辺は関数でなければなりません");
        match snd b.T.lb_name with
        | T.PVar x -> (x, new_var lvl)
        | _ -> type_error "let rec の束縛はパターンにできません")
      bs
  in
  let env_rec = { env with values = List.fold_left (fun m (x, t) -> SMap.add x t m) env.values names } in
  List.iter2
    (fun ((_, b) as bnode) (_, pre) ->
      let rigids = make_rigids lvl b.T.lb_tparams in
      let env_ty = { env_rec with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env_rec.types rigids } in
      let extra_rigids = ref [] in
      let fn_ty =
        match b.T.lb_params with
        | Some params ->
            let seen = ref [] in
            let param_tys = List.map (fun _ -> new_var lvl) params in
            let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
            let fn_eff, eff_rigids =
              match b.T.lb_eff with
              | Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e)
              | None -> (new_row_var lvl, [])
            in
            extra_rigids := eff_rigids;
            let ret_ty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
            let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
            Unify.unify ret_ty body_ty;
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None ->
            let vty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
            Unify.unify vty (elab_exp env_ty lvl eff b.T.lb_body);
            vty
      in
      Unify.unify pre fn_ty;
      Tree.set_ty bnode fn_ty;
      release_rigids (rigids @ !extra_rigids))
    bs names;
  List.iter warn (Exhaust.drain ());
  List.iter (fun (_, t) -> Unify.generalize level t) names;
  { env with values = List.fold_left (fun m (x, t) -> SMap.add x t m) env.values names }

(* ## 11.30 宣言の入口 — トップレベルで許されるエフェクト

   トップレベルの初期エフェクト行は、ランタイムが提供する**閉じた**行です。
   いまは `{Console, Async}` の 2 つ (第7章に定義が 1 箇所だけあります)。

   閉じているので、`perform print(...)` をトップレベルに書くと
   「エフェクト Print をここでは実行できません」になります。正しい挙動です。
   Print はユーザが宣言したエフェクトで、ハンドラを書かない限り誰も
   解釈しません。

   `Async` が入っているのは、sample.kel:529 の `crunch` が
   `@ Async` を持ったままトップレベルから呼ばれるからです。`yield_` は
   型検査を通り、実行時には何もしない — この約束をランタイム側の提供
   エフェクトとして表現しています。

   初期の値環境は第6章の組み込み表から作ります。 *)

let toplevel_eff () =
  List.fold_right (fun n acc -> TRowExtend (intern n, t_unit, acc)) Prims.runtime_effects TRowEmpty

let initial_env () =
  {
    values = List.fold_left (fun m (n, t) -> SMap.add n t m) SMap.empty (Decls.builtin_values ());
    types = SMap.empty;
    resume_ty = None;
  }

(* ## 11.31 newtype の登録

   データ宣言は型言語を変えません。名目的な `TCon` が 1 つ増え、宣言表に
   コンストラクタとフィールド型が載るだけです。

   フィールド型の中の型パラメータは **Generic** で束縛します。つまり
   宣言表に置かれるのはスキーマで、使うたびに `subst_params` で具体化します
   (§11.8、§11.18)。組み込みメソッドのスキーマとまったく同じ形なので、
   使う側のコードが 1 本で済みます。

   パラメータのカインドは `*` か、`F[_]` と明示されたものだけです。ここで
   カインド変数を許さないのは、データ宣言のカインドが後から推論で決まると、
   1a パスで登録した頭のカインドと食い違うからです。

   `newtype T = ???` (`NtHole`) は表現を隠します。コンストラクタを持たない
   不透明なデータ型として登録され、構築も分解もできません。

   フィールド型の精緻化をこの登録時に済ませているので、パス 2 で newtype に
   出会っても何もすることがありません。未知の型を書けばこの時点でエラーです。 *)

let register_newtype env (n : T.newtype') =
  let params =
    List.map
      (fun tp ->
        (* newtype パラメータのカインドは * か、F[_] 明示のみ(v0) *)
        let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else KStar in
        let classes = List.map (fun li -> intern (show_long_id li)) tp.tp_classes in
        { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes })
      n.T.nt_params
  in
  let types =
    List.fold_left2
      (fun m (tp : type_param) i -> SMap.add tp.tp_name (TVar (ref (Generic i))) m)
      env.types n.T.nt_params params
  in
  let env' = { env with types } in
  match n.T.nt_rhs with
  | T.NtHole ->
      Decls.add_data { Decls.dd_name = intern n.T.nt_name; dd_params = params; dd_ctors = []; dd_opaque = true }
  | T.NtCtors ctors ->
      let ctors =
        List.map
          (fun (c : T.ctor_decl) ->
            {
              Decls.ct_name = intern c.T.cd_name;
              ct_fields =
                List.map
                  (fun (f : T.field_decl) ->
                    let ty = elab_type env' 1 f.T.fd_ty in
                    (* 省略された @ など、束縛されなかった変数はスキーマでは Generic にする *)
                    Unify.generalize 0 ty;
                    { Decls.fi_label = Option.map intern f.T.fd_label; fi_ty = ty })
                  c.T.cd_fields;
            })
          ctors
      in
      Decls.add_data { Decls.dd_name = intern n.T.nt_name; dd_params = params; dd_ctors = ctors; dd_opaque = false }

(* ## 11.32 effect の登録

   エフェクト宣言は操作名から矢印スキーマへの表です。操作の型が矢印で
   なければならないのは、`perform` が引数と返り値を必要とするからです。

   effect 宣言に型パラメータは書けません (sample.kel §9)。エフェクトの
   パラメータはラベルの引数欄として行に載る仕組みで、`Heap[h]` のように
   組み込み側が使っています。ユーザ宣言のエフェクトにこれを開放すると、
   操作の型が真に多相になり、ハンドラの節が多相な継続を受け取ることになって
   ランク 2 に踏み込みます。ランク 1 で取れる最大限がこの形です。

   同一エフェクト内での操作名の重複は拒否します。**別の**エフェクトとの
   重複は許します — それが D22 の前提です (§11.20)。 *)

let register_effect env (e : T.effect') =
  if e.T.ef_params <> [] then type_error "effect 宣言に型パラメータは書けません(sample.kel §9)";
  let ops =
    List.map
      (fun (op, te) ->
        match snd te with
        | T.EArrow _ ->
            let ty = elab_type env 1 te in
            Unify.generalize 0 ty;
            (intern op, ty)
        | _ -> type_error ("操作 " ^ op ^ " の型は矢印型でなければなりません"))
      e.T.ef_ops
  in
  (* 同一 effect 内の重複 op は拒否 *)
  let rec dup = function
    | [] -> ()
    | (op, _) :: rest -> if List.mem_assoc op rest then type_error ("操作 " ^ name_of op ^ " が二重に宣言されています") else dup rest
  in
  dup ops;
  Decls.add_effect { Decls.ef_name = intern e.T.ef_name; ef_ops = ops }

let binding_name (b : T.let_binding') = match snd b.T.lb_name with T.PVar x -> Some x | _ -> None

(* ## 11.33 type class の登録 — と、パラメータは頭に現れよという条件

   クラスのパラメータは 1 つだけです (D11)。多引数クラスは仕様が明示的に
   排除しており (sample.kel:275)、それを受けて型スキーマ用のデータ型も
   制約ストアも持たずに済んでいます。Generic マークだけで多相が表せるのは
   この裁定のおかげです。

   メソッドの型は、**クラスパラメータとメソッド固有の型パラメータの両方**を
   Generic 化したスキーマとして表に置きます。`val map[A, B, E]:` のように
   メソッドが自分の型パラメータを持てるので、2 種類を同じスキーマの中で
   Generic にする必要があります。クラスパラメータのほうには `vcls` として
   クラス名が貼ってあり、これが後で「この変数はこのクラスのインスタンスで
   なければならない」という制約になります。メソッドの型パラメータに書かれた
   **制約のクラス名の検証**だけは、ここでは行わずパス 1b の後に回してあります
   (§11.39)。クラスどうしの宣言順に依存させないためです。

   `Integral` と `Fractional` はユーザ宣言できません。リテラル述語のために
   予約された名前です (D8、§11.2)。どの名前が予約かの表は第6章
   (`Decls.reserved_predicate`) が持ち、ここはそれを引くだけです。
   インスタンス宣言側の入口にも同じ表の検査があります (§6.12)。

   ### クラスパラメータが引数の頭に現れること

   v0 の硬い制約です。

   > メソッドの引数の**どれか 1 つ**で、クラスパラメータが型の**頭**に
   > 現れていなければ、そのメソッドは宣言できない。

   理由は実行時にあります。型クラスのディスパッチは辞書渡しではなく、
   値のタグを見る動的ディスパッチです (D3、第14章)。実行時に見えるのは
   値の頭のコンストラクタだけなので、`(List[A]) => ...` のようにパラメータが
   引数の内側に埋もれていると、`A` のインスタンスを選べません。
   「頭に現れる」は「その引数でタグディスパッチできる」の言い換えです。

   最初はこの条件を「引数のどこかに現れる」と緩く書いていました。それだと
   `(Int32, A) => Int32` のようなメソッドが宣言でき、実行時に第 1 引数の
   Int32 で誤ってディスパッチします (260829-2b の健全性 4)。条件を
   「頭に現れる」に強めたのと同時に、実行時のディスパッチ側も
   「パラメータが頭に現れる引数位置」だけを見るように直しました。
   静的な宣言条件と動的な選択規則が同じ述語を見ている、というのがこの
   修正の要点です。

   代償として `pure : (A) => F[A]` の類は宣言できません。返り値の位置に
   しかパラメータが現れないからです。仕様が Monad / Applicative を
   プレリュードに置かないと明言しているので (sample.kel:329-333)、
   v0 ではこの制約と衝突しません。

   組み込みと同名のクラスをユーザが宣言したときは、**組み込みに無いメソッドを
   足していないか**だけを照合して受理し、実体は組み込みを使います (乖離 4)。
   照合は一方向で、部分集合は許します — 組み込み `Ord` の 4 メソッドのうち
   `lt` だけを書いた宣言もそのまま通ります。sample.kel 自身がプレリュード
   相当の宣言を含んでいるための運用上の裁定です。

   ### 非修飾名の所有者は高々 1 クラス

   もうひとつ、ここで守る不変条件があります。同名メソッドを持つクラスが
   2 つあると、elab の非修飾名解決 (パス 1b の `SMap.add`) は宣言順の後勝ち、
   第14章の登録 (`register_class_methods`) はハッシュ順の後勝ちで、
   **型検査と実行が別のクラスを選び**ます。型検査が選んだ実体と違う実装が
   静かに走るか、偽の「インスタンスが見つかりません」が出るか — どちらも
   実測しました。§14.6 の教訓『ディスパッチの規約は、宣言を受理する側と
   実行する側で同じ 1 つでなければならない』の言い換えとして、衝突そのものを
   宣言時に拒否します。どちらかに「後勝ち」の規則を与える案は、同じ順序規則を
   2 か所に実装することになるので採りません。検査は既存クラス全走査ですが、
   不変条件が帰納的に保たれるので衝突相手は高々 1 つ、エラー文言も決定的です。
   v1 で「曖昧なら型で絞る」方式に進むなら、この拒否は緩められます。 *)

let register_class env (c : T.class_decl') =
  let cls = intern c.T.cls_name in
  (if Decls.reserved_predicate cls then
     type_error (c.T.cls_name ^ " は予約されたリテラル述語です(ユーザ宣言不可、D8)"));
  let param =
    match c.T.cls_params with
    | [ p ] -> p
    | _ -> type_error "type class のパラメータは1個です(多パラメータ型クラスは意図的に排除、sample.kel:275)"
  in
  let param_kind = if param.tp_arity > 0 then k_arrow param.tp_arity else KStar in
  (if param.tp_classes <> [] then type_error "クラスパラメータに制約は書けません(スーパークラスは v1)");
  let pinfo = { vid = new_oid (); vlevel = 0; vkind = param_kind; vcls = [ cls ] } in
  let pvar = TVar (ref (Generic pinfo)) in
  List.iter
    (fun d -> if d <> "structural" then type_error ("未知の導出規則: " ^ d ^ "(v0 は derive structural のみ)"))
    c.T.cls_derives;
  let methods =
    List.map
      (fun (v : T.class_val) ->
        let mt_params =
          List.map
            (fun tp ->
              (* カインドは使用位置から推論し、宣言終了時に KStar へ既定化(D7) *)
              let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var () in
              let classes = List.map (fun li -> intern (show_long_id li)) tp.tp_classes in
              (tp.tp_name, TVar (ref (Generic { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes }))))
            v.T.cv_tparams
        in
        let types = List.fold_left (fun m (n, t) -> SMap.add n t m) (SMap.add param.tp_name pvar env.types) mt_params in
        let ty = elab_type { env with types } 1 v.T.cv_ty in
        Unify.generalize 0 ty;
        List.iter (fun (_, t) -> match repr t with TVar r -> default_kind (Unify.var_info_of r).vkind | _ -> ()) mt_params;
        (* v0 制約: クラスパラメータが少なくとも1つの引数の「頭」に現れること(計画 §7.4)。
           実行時ディスパッチ(tycon_of_value)は値の頭のコンストラクタしか見えないので、
           List[A] のようにパラメータが引数の内側に埋もれた形は選べない。
           「頭に現れる」= その引数でタグディスパッチできることを保証する *)
        let head_is_param t =
          match repr (fst (app_spine t)) with TVar r -> ( match !r with Generic i -> i.vid = pinfo.vid | _ -> false) | _ -> false
        in
        (match repr ty with
        | TArrow (args, _, _) -> (
            match repr args with
            | TRecord row when List.exists (fun (_, t) -> head_is_param t) (fst (row_fields row)) -> ()
            | _ ->
                type_error
                  ("メソッド " ^ v.T.cv_name ^ " はクラスパラメータが引数の頭に現れないため v0 では宣言できません(実行時タグディスパッチの前提、§7.4)"))
        | _ -> type_error ("メソッド " ^ v.T.cv_name ^ " の型は矢印型でなければなりません"));
        (v.T.cv_name, ty))
      c.T.cls_vals
  in
  (* 非修飾名の所有者は高々 1 クラス、という不変条件をここで守る。破れると
     elab(宣言順の後勝ち)と interp(ハッシュ順の後勝ち)が別のクラスを選び、
     誤った実体を呼ぶか、偽の「インスタンスが見つかりません」を出す(実測)。
     組み込みと同名のクラス再宣言は同一 oid なので素通しになる(乖離 4)。
     不変条件が帰納的に保たれるので候補は高々 1 つで、文言も決定的 *)
  List.iter
    (fun (m, _) ->
      Hashtbl.iter
        (fun _ (other : Decls.class_info) ->
          if other.Decls.ci_name <> cls && List.mem_assoc m other.Decls.ci_methods then
            type_error
              ("メソッド名 " ^ m ^ " は型クラス " ^ name_of other.Decls.ci_name
             ^ " が既に宣言しています(非修飾名が衝突するため、v0 では同名メソッドを複数のクラスに宣言できません)"))
        Decls.classes)
    methods;
  match
    Decls.add_class_decl
      {
        Decls.ci_name = cls;
        ci_param = pinfo;
        ci_param_kind = param_kind;
        ci_derive_structural = List.mem "structural" c.T.cls_derives;
        ci_builtin = false;
        ci_methods = methods;
      }
  with
  | `Added -> methods
  | `Builtin prev ->
      (* 組み込みと同名: 組み込みに無いメソッドを足していないかだけ照合し(部分集合は許す)、
         実体は組み込みを使う *)
      List.iter
        (fun (m, _) ->
          if not (List.mem_assoc m prev.Decls.ci_methods) then
            type_error ("組み込みクラス " ^ c.T.cls_name ^ " に無いメソッド " ^ m ^ " は宣言できません"))
        methods;
      prev.Decls.ci_methods

(* ## 11.34 インスタンスの頭 — キーは名前 1 つ

   インスタンスの頭は `Int32` か `List[_]` の形しか受けません。`_` は穴で、
   引数の**個数**だけを伝えます。`List[Int32]` のような具体的な頭は書けません。

   そのおかげでインスタンス表のキーが (クラス, 型構成子) の 2 つ組で済み、
   探索が表引き 1 回になります。`Functor[List[_]]` の `_` はカインド検査に
   だけ使われ、キーには入りません。重なり合うインスタンスも、インスタンスの
   前提の解決も存在しないので、コヒーレンスは「同じキーを 2 度登録したら
   エラー」の 1 行で保証できます (sample.kel:276)。

   頭のカインドはクラスパラメータのカインドと一致していなければなりません。
   `Functor` は `[_] Type` のクラスなので、`Functor[Int32]` はここで落ちます。 *)

let instance_head (i : T.instance_decl') =
  let cls = intern i.T.ins_class in
  let head =
    match i.T.ins_args with
    | [ h ] -> h
    | _ -> type_error "type instance の型引数は1個です(D11)"
  in
  let con, holes =
    match snd head with
    | T.EIdent (LongId [ n ]) -> (Decls.resolve_con (intern n), 0)
    | T.EApply ((_, T.EIdent (LongId [ n ])), args) ->
        List.iter (fun (a : T.type_exp) -> match snd a with T.EHole -> () | _ -> type_error "インスタンス頭の型引数は _ だけです(List[_] の形)") args;
        (Decls.resolve_con (intern n), List.length args)
    | _ -> type_error "インスタンス頭は 型構成子 か 型構成子[_, ...] の形で書いてください"
  in
  (cls, con, holes)

(* ## 11.35 インスタンスの登録 — 網羅と過剰の両方を見る

   パス 1c ではインスタンスの**頭とメソッド名**だけを登録し、本体の検査は
   パス 2 に回します (§11.38)。本体の推論には値環境が揃っている必要が
   あるからです。

   ここで見るのは 2 方向の照合です。宣言していないメソッドを書いていないか
   (過剰)、クラスの全メソッドを書いたか (網羅)。片方だけでは足りません。
   過剰を許すと綴り間違いが黙って無視され、網羅を許さないと実行時に
   メソッドが見つかりません。

   インスタンス本体に書けるのは let と let rec だけです。`Functor[List[_]]` の
   `map` は自分自身を再帰呼び出しするので、let rec が要ります
   (sample.kel:321-324)。 *)

let register_instance (i : T.instance_decl') =
  let cls, con, holes = instance_head i in
  let ci = match Decls.find_class cls with Some ci -> ci | None -> type_error ("未知のクラス: " ^ i.T.ins_class) in
  if not (Hashtbl.mem Decls.con_kinds con) then type_error ("未知の型構成子: " ^ name_of con);
  if not (same_kind ci.Decls.ci_param_kind (Decls.con_kind con holes)) then
    type_error
      ("インスタンス頭 " ^ name_of con ^ " のカインドがクラス " ^ i.T.ins_class ^ " のパラメータと一致しません");
  let methods =
    List.concat_map
      (fun ((_, d) : T.decl) ->
        let name_of_b ((_, b) as bnode : T.let_binding) =
          match binding_name b with
          | Some x -> (intern x, bnode)
          | None -> type_error "インスタンス本体の let は名前束縛でなければなりません"
        in
        match d with
        | T.DLet bnode -> [ name_of_b bnode ]
        | T.DLetRec bs -> List.map name_of_b bs
        | _ -> type_error "インスタンス本体には let(と let rec)だけが書けます")
      i.T.ins_body
  in
  (* メソッドの網羅と過剰 *)
  List.iter
    (fun (m, _) ->
      if not (List.exists (fun (m2, _) -> intern m2 = m) ci.Decls.ci_methods) then
        type_error ("クラス " ^ i.T.ins_class ^ " にメソッド " ^ name_of m ^ " はありません"))
    methods;
  List.iter
    (fun (m, _) ->
      if not (List.mem_assoc (intern m) methods) then
        type_error ("インスタンスがメソッドを網羅していません: " ^ m ^ " が漏れています"))
    ci.Decls.ci_methods;
  Decls.add_instance ~builtin:false ~methods ~cls ~con []

(* ## 11.36 前方参照は、全ての矢印に注釈があるときだけ

   パス 1c で登録する「注釈が完全な let の署名」は、前方参照を通すための
   仕掛けです。sample.kel:334 の `user_names` が、後ろで定義される
   `println`(:347) を呼べるのはこれのおかげです。

   問題は「完全」の定義でした。計画は「引数と返り値に型注釈があること」と
   書いていました。それでは穴が空きます。

   省略された `@` は**新しい行変数**を作ります (§11.4)。本体を推論するときは
   その行変数が呼び出し側の `eff` と結ばれて縛られますが、本体を見ずに
   署名だけを作ると、行変数は何にも縛られないまま一般化されます。すると
   その関数は「どんなエフェクトでも起こしてよい」ことになり、
   **宣言順によってエフェクト検査が抜けます** — 前方参照された呼び出しは
   通り、同じ呼び出しを定義の後ろに書くと落ちる。実証済みの穴です
   (260829-2b の健全性 3)。

   そこで条件を厳しくします。

   > 前方参照シグネチャに使ってよいのは、**注釈中の全ての矢印に `@` が
   > 明示されている**ものだけ。

   `fully_effected` はその再帰的な判定です。引数の型の中に埋まった矢印も、
   返り値の型の中の矢印も、行の中のラベル引数も見ます。1 つでも省略が
   あれば署名を作らず、その let は宣言順に依存したままになります。
   通せるものを減らしてでも、通してはいけないものを通さないほうを選びました。

   > 本体を見ずに型を信じるなら、その型に省略があってはならない。 *)

let rec fully_effected ((_, te) : T.type_exp) =
  match te with
  | T.EArrow (params, ret, eff) -> eff <> None && List.for_all fully_effected params && fully_effected ret
  | T.EApply (f, args) -> fully_effected f && List.for_all fully_effected args
  | T.EBraceRow (elems, ext) ->
      List.for_all
        (function T.BField (_, t) -> fully_effected t | T.BLabel (_, ts) -> List.for_all fully_effected ts)
        elems
      && (match ext with Some t -> fully_effected t | None -> true)
  | T.EVariantCase (_, Some t) -> fully_effected t
  | T.EUnion ts -> List.for_all fully_effected ts
  | T.EVariantCase (_, None) | T.EIdent _ | T.EHole -> true

(* ## 11.37 署名の構築 — 失敗したら黙って諦める

   条件を満たした束縛について、本体を見ずに型を組み立てます。型パラメータを
   剛定数にし、注釈を精緻化し、一般化し、解放する。§11.25 の 3 段そのままです。

   関数束縛では引数パターンが全て `PAnnot` (注釈付き) であることも要求します。
   注釈のない引数があれば、その型は本体からしか分かりません。

   例外を握り潰して `None` を返しているのが目を引きますが、これは意図的です。
   このパスの目的は署名を**登録できるものは登録する**ことであり、エラーを
   報告することではありません。ここで落ちる型注釈は、パス 2 で本体を
   推論するときにもう一度精緻化され、そのとき正しい文脈で正しいエラーに
   なります。1c で早まって報告すると、エラーの出る位置が宣言順に依存します。 *)

let signature_of_binding env (b : T.let_binding') : ty option =
  let params_annotated =
    match b.T.lb_params with
    | None -> true
    | Some ps -> List.for_all (fun (_, p) -> match p with T.PAnnot _ -> true | _ -> false) ps
  in
  let param_tes = match b.T.lb_params with None -> [] | Some ps -> List.filter_map (fun (_, p) -> match p with T.PAnnot (_, te) -> Some te | _ -> None) ps in
  let full =
    params_annotated && b.T.lb_ret <> None
    (* 関数束縛は自身の eff 行も明示されていること *)
    && (match b.T.lb_params with Some _ -> b.T.lb_eff <> None | None -> true)
    && List.for_all fully_effected param_tes
    && (match b.T.lb_ret with Some t -> fully_effected t | None -> false)
  in
  if not full then None
  else
    try
      let lvl = 1 in
      let rigids = make_rigids lvl b.T.lb_tparams in
      let env_ty = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types rigids } in
      let ty =
        match b.T.lb_params with
        | Some ps ->
            let param_tys =
              List.map
                (fun (_, p) -> match p with T.PAnnot (_, te) -> elab_type env_ty lvl te | _ -> assert false)
                ps
            in
            let fn_eff, eff_rigids =
              match b.T.lb_eff with
              | Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e)
              | None -> (new_row_var lvl, [])
            in
            let ret_ty = match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> assert false in
            release_rigids eff_rigids;
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None -> ( match b.T.lb_ret with Some t -> elab_type env_ty lvl t | None -> assert false)
      in
      Unify.generalize 0 ty;
      release_rigids rigids;
      Some ty
    with Type_error _ | NotImplemented _ -> None

(* ## 11.38 インスタンス本体の検査 — instantiate と skolemize の非対称

   インスタンスのメソッド本体が、クラス宣言の型を満たしているかを見ます。
   期待型は「クラス宣言のメソッド型に、インスタンスの頭型を代入したもの」です。
   `Functor` の `map : (F[A], (A) => B @ E) => F[B] @ E` に `F := List` を
   代入すると `(List[A], (A) => B @ E) => List[B] @ E` になります。
   代入は `map_generics_with` にメモを 1 つ仕込むだけで、`tapp` の正規化が
   `F[A]` を `List[A]` に畳んでくれます (第1章)。

   検査は**包摂**です。単一化ではありません。向きが 2 つあることに注意して
   ください。

   | 側 | 操作 | 意図 |
   |---|---|---|
   | 推論された型 | `instantiate` | 「どんな型にでもなれる」— 柔らかい変数にする |
   | 期待型 | `skolemize` | 「どの型でも通らねばならない」— 剛定数にする |

   そのうえで単一化します。推論型のほうが期待型より**多相であれば**通り、
   足りなければ剛定数に具体型を代入しようとして落ちる。これが
   「実装は宣言と同じか、それより一般的であること」の検査です。
   両方 instantiate すると、たまたま一致する具体型があるだけで通ってしまい、
   両方 skolemize すると何も通りません。

   > 与えるほうは柔らかく、要求するほうは硬く。逆にすると検査が意味を失う。

   本体は普通の `elab_binding` / `elab_rec_bindings` で推論します。だから
   注釈付きのメソッドも let rec のメソッドも同じ経路で通ります
   (sample.kel:321-324)。 *)

let check_instance_bodies env (i : T.instance_decl') =
  let cls, con, _holes = instance_head i in
  let ci = match Decls.find_class cls with Some ci -> ci | None -> bug "instance: class 未登録" in
  let head_ty = TCon (con, []) in
  let expected_of mname =
    match List.assoc_opt mname ci.Decls.ci_methods with
    | Some scheme ->
        let memo = Hashtbl.create 8 in
        Hashtbl.add memo ci.Decls.ci_param.vid head_ty;
        Unify.map_generics_with memo (fun info -> TVar (ref (Generic info))) scheme
    | None -> bug "instance: メソッドスキーマ未登録"
  in
  let subsume mname inferred =
    let lvl = 1 in
    let skol = Unify.skolemize lvl (expected_of mname) in
    try Unify.unify (Unify.instantiate lvl inferred) skol
    with Type_error msg ->
      type_error ("インスタンスメソッド " ^ mname ^ " がクラス宣言の型を満たしません(" ^ msg ^ ")")
  in
  List.iter
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DLet ((_, b) as bnode) ->
          let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
          let env2 = elab_binding env 0 (new_row_var 0) bnode in
          subsume mname (SMap.find mname env2.values)
      | T.DLetRec bs ->
          let env2 = elab_rec_bindings env 0 (new_row_var 0) bs in
          List.iter
            (fun ((_, b) : T.let_binding) ->
              let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
              subsume mname (SMap.find mname env2.values))
            bs
      | _ -> type_error "インスタンス本体には let だけが書けます")
    i.T.ins_body

(* ## 11.39 宣言列を 4 回なめる

   章の冒頭に置いた表の実装です。ここで順序の理由をもう一度、コードに即して。

   **1a — エイリアスと newtype の頭。** 型の本体を精緻化するには、その中に
   出てくる全ての型構成子のカインドが引けなければなりません。だから名前と
   カインドだけを先に登録します。プレリュードが持っている名前をユーザが
   再宣言したときは、プレリュード側を残します (乖離 4)。

   **1b — コンストラクタ・操作・メソッド。** ここで初めて型の本体を書きます。
   1a が終わっているので、宣言の順序に依存しません。newtype どうしが
   互いを参照しても、effect が後ろの newtype を使っても通ります。
   クラスのメソッドは、非修飾名 (`map`) と修飾名 (`Functor.map`) の
   **両方**で値環境に登録します (乖離 12)。どちらでも書けるという仕様を、
   環境に 2 つ入れるという最も安い方法で実現しています。
   1b の後始末として、クラスメソッドの型パラメータ制約に未知のクラスが
   無いかだけを見る小さな検証ループが 1 つ走ります。表には何も登録しません。
   1b の中 (`register_class`) で検査すると、後ろで宣言されるクラスを制約に
   書いた形が落ちてしまうので、クラス表が出揃うのを待つのです。

   **1c — インスタンスの頭と前方参照シグネチャ。** 頭のカインド検査に
   クラス表が要るので 1b の後。署名の登録はここが最後のチャンスです
   (§11.36、§11.37)。

   **2 — 本体。** 宣言順に推論し、束縛ごとに型を印字します。印字の前に
   `default_numerics` を呼ぶのを忘れないこと。述語つきの弱い変数が残った
   まま表示すると、ユーザには意味のない内部の述語が見えます (D8)。

   プレリュードも同じ `process_decls` を通します。違いは `emit` を
   捨てることだけです。 *)

let process_decls env ~emit decls =
  let eff0 = toplevel_eff () in
  (* パス1a: 型エイリアスの登録と newtype の頭(カインド) *)
  List.iter
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DType t ->
          Decls.add_alias
            { Decls.al_name = intern t.T.ta_name; al_params = t.T.ta_params; al_kind = t.T.ta_kind; al_body = t.T.ta_body }
      | T.DNewtype n ->
          if not (Decls.prelude_owned "data" (intern n.T.nt_name)) || !Decls.in_prelude then
            Hashtbl.replace Decls.con_kinds (intern n.T.nt_name) (k_arrow (List.length n.T.nt_params))
      | _ -> ())
    decls;
  (* パス1b: newtype のコンストラクタ・effect・type class の登録(相互再帰・前方参照可) *)
  let env =
    List.fold_left
      (fun env ((_, d) : T.decl) ->
        match d with
        | T.DNewtype n ->
            register_newtype env n;
            env
        | T.DEffect e ->
            register_effect env e;
            env
        | T.DClass c ->
            let methods = register_class env c in
            {
              env with
              values =
                List.fold_left
                  (fun m (mn, ty) -> SMap.add mn ty (SMap.add (c.T.cls_name ^ "." ^ mn) ty m))
                  env.values methods;
            }
        | _ -> env)
      env decls
  in
  (* 1b の後始末: クラスメソッドの型パラメータ制約に未知のクラスが無いか。
     register_class は 1b で宣言順に走るので、そこで検査すると後方のクラスを
     制約に書いた形が落ちる。クラス表が出揃ったここで見れば宣言順に依存しない *)
  List.iter
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DClass c ->
          List.iter (fun (v : T.class_val) -> List.iter (fun tp -> ignore (class_names_of tp)) v.T.cv_tparams) c.T.cls_vals
      | _ -> ())
    decls;
  (* パス1c: インスタンス頭の登録と、注釈が完全な let の署名登録 *)
  let env =
    List.fold_left
      (fun env ((_, d) : T.decl) ->
        match d with
        | T.DInstance i ->
            register_instance i;
            env
        | T.DLet (_, b) -> (
            match (binding_name b, signature_of_binding env b) with
            | Some x, Some ty -> { env with values = SMap.add x ty env.values }
            | _ -> env)
        | T.DLetRec bs ->
            List.fold_left
              (fun env ((_, b) : T.let_binding) ->
                match (binding_name b, signature_of_binding env b) with
                | Some x, Some ty -> { env with values = SMap.add x ty env.values }
                | _ -> env)
              env bs
        | _ -> env)
      env decls
  in
  (* パス2: 本体の推論(宣言順) *)
  let show_binding env ((_, b) : T.let_binding) =
    match binding_name b with Some x -> emit (x ^ " : " ^ Show.show (SMap.find x env.values)) | None -> ()
  in
(* ## 11.40 パス 2 の 1 歩 — 宣言ごとに何が起きるか

   `step` は宣言 1 つを処理して新しい環境を返します。宣言の種類ごとの
   仕事は次のとおりです。

   - `DType` — パス 1a で表に入っているので、ここでは**検査のためだけに**
     本体を精緻化して結果を捨てます。未知の型・再帰・部分適用が
     この時点で報告されます。使われないエイリアスの誤りが黙って残らないように。
   - `DLet` / `DLetRec` — 本体を推論し、既定化してから型を印字。
   - `DExp` — 式を推論し、網羅性の警告を流してから型を印字。
   - `DExtern` — 署名だけを登録します。実装は第13章の表にあります。
     引数パターン・エフェクト注釈・返り値注釈の扱いは束縛と同じで、
     本体が無いぶん短いだけです。同じ名前を 2 度 extern できないのは、
     嘘の型を後から被せられるからです (260829-2b の健全性 8)。
   - `DNewtype` / `DEffect` / `DClass` — パス 1 で済んでいます。
   - `DInstance` — 本体を検査します (§11.38)。
   - `DModule` — ここには来ません。平坦化で消えているはずです (§11.42)。

   警告はこの宣言で新しく増えたぶんだけを印字します。宣言と警告の対応が
   崩れないように、処理の前後で個数を覚えておく方式です。 *)

  let step env ((_, d) : T.decl) =
    let wbefore = List.length !warnings in
    let env' =
      match d with
      | T.DType t ->
          (* 実在検査(未知の型・再帰・部分適用)をここで走らせる。結果は捨てる *)
          let info = Hashtbl.find Decls.aliases (intern t.T.ta_name) in
          let lvl = 1 in
          let rigids = make_rigids lvl info.Decls.al_params in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          ignore
            (match info.Decls.al_kind with
            | Some "EffectRow" -> elab_eff env_ty lvl info.Decls.al_body
            | _ -> elab_type env_ty lvl info.Decls.al_body);
          release_rigids rigids;
          env
      | T.DLet b ->
          let env' = elab_binding env 0 eff0 b in
          Unify.default_numerics () (* 表示前に述語つき弱変数を既定化する(D8) *);
          show_binding env' b;
          env'
      | T.DLetRec bs ->
          let env' = elab_rec_bindings env 0 eff0 bs in
          Unify.default_numerics ();
          List.iter (show_binding env') bs;
          env'
      | T.DExp e ->
          let t = elab_exp env 0 eff0 e in
          List.iter warn (Exhaust.drain ());
          Unify.default_numerics ();
          emit ("_ : " ^ Show.show t);
          env
      | T.DExtern ex ->
          (* extern 宣言は署名のみ(実装は builtin.ml の表)。重複・プレリュード保護 *)
          Decls.add_extern ex.T.ex_name;
          let lvl = 1 in
          let rigids = make_rigids lvl ex.T.ex_tparams in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          let seen = ref [] in
          let param_tys = List.map (fun _ -> new_var lvl) ex.T.ex_params in
          ignore (List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty ex.T.ex_params param_tys);
          let fn_eff, eff_rigids =
            match ex.T.ex_eff with Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e) | None -> (new_row_var lvl, [])
          in
          let ret_ty = match ex.T.ex_ret with Some t -> elab_type env_ty lvl t | None -> new_var lvl in
          let ty = TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff) in
          Unify.generalize 0 ty;
          release_rigids (rigids @ eff_rigids);
          emit (ex.T.ex_name ^ " : " ^ Show.show ty);
          { env with values = SMap.add ex.T.ex_name ty env.values }
      | T.DNewtype _ -> env (* パス1で登録済み。フィールド型の検査も登録時に済んでいる *)
      | T.DEffect _ -> env (* パス1で登録済み *)
      | T.DClass _ -> env (* パス1で登録済み *)
      | T.DInstance i ->
          check_instance_bodies env i;
          env
      | T.DModule _ -> noimpl "module(M10)"
    in
    Unify.default_numerics ();
    List.iteri (fun i w -> if i >= wbefore then emit ("⚠ " ^ w)) !warnings;
    env'
  in
  List.fold_left step env decls

(* ## 11.41 入口 — プレリュードを先に、フラグは必ず戻す

   プレリュード (第15章) を先に処理してから、ユーザの宣言列を処理します。
   プレリュードの出力は捨て、環境だけを引き継ぎます。

   `Decls.in_prelude` を `Fun.protect` で囲んでいるのが小さな要点です。
   プレリュードの処理中に型エラーが飛んでもフラグが立ちっぱなしにならない
   ようにするためで、立ちっぱなしになると、以降のユーザ宣言が
   プレリュード扱いされて再宣言の保護をすり抜けます。

   > 大域フラグを立てたら、例外の通り道に必ず戻す場所を置く。 *)

let type_check_decls ?(prelude = []) decls =
  warnings := [];
  Unify.reset ();
  Exhaust.reset ();
  let out = current_out in
  out := [];
  let emit s = out := !out @ [ s ] in
  let env0 = initial_env () in
  Decls.in_prelude := true;
  let env =
    Fun.protect
      ~finally:(fun () -> Decls.in_prelude := false)
      (fun () -> process_decls env0 ~emit:(fun _ -> ()) prelude)
  in
  let _env = process_decls env ~emit decls in
  !out

(* ## 11.42 module の平坦化 — 改名と同義語表

   v0 の module は名前空間ではなく**改名規則**です (D21)。宣言列を精緻化に
   渡す前に平坦化し、以降のパスは module を知りません。

   - `newtype` / `type` は `M.名前` に改名して登録し、第6章の同義語表に
     「非修飾名 → 修飾名」を張ります。この 1 本の表で、module の内側からの
     非修飾参照と、外側からのコンパニオン型参照 (sample.kel:580) の両方が
     通ります。§11.3 が名前を引くたびに `Decls.resolve_con` を通していたのは
     この表のためです。
   - `let` も `M.名前` に改名します。ただし module 内の相互参照は v0 では
     通りません (改名後の名前で書かれていないため)。sample.kel は使っていません。
   - `instance` はそのまま大域に出します。インスタンスは常に大域可視で、
     import で見え方が変わるものではありません (sample.kel:576)。
   - `pub` は受理するだけで検査しません。

   同義語表は実行時にも要ります。module の中の instance が実行時に
   見つからなかったのは、評価器が同義語表を引いていなかったからでした
   (260829-2b の健全性 6)。**型検査が使う名前解決の経路は、評価器も
   同じものを通らなければなりません。**

   入れ子の module と、module 内の effect / class / 式は未対応です。
   受理してから落ちるのではなく、平坦化の時点で型エラーとして報告します。 *)

let flatten_modules (decls : T.decl list) : T.decl list =
  List.concat_map
    (fun ((_, d) as node : T.decl) ->
      match d with
      | T.DModule (_, mname, body) ->
          List.concat_map
            (fun ((bdata, bd) as bnode : T.decl) ->
              match bd with
              | T.DNewtype n ->
                  let qual = mname ^ "." ^ n.T.nt_name in
                  Hashtbl.replace Decls.con_synonyms (intern n.T.nt_name) (intern qual);
                  [ (bdata, T.DNewtype { n with T.nt_name = qual }) ]
              | T.DType t ->
                  let qual = mname ^ "." ^ t.T.ta_name in
                  Hashtbl.replace Decls.con_synonyms (intern t.T.ta_name) (intern qual);
                  [ (bdata, T.DType { t with T.ta_name = qual }) ]
              | T.DLet ((bd2, b) as _bnode2) -> (
                  match snd b.T.lb_name with
                  | T.PVar x -> [ (bdata, T.DLet (bd2, { b with T.lb_name = (fst b.T.lb_name, T.PVar (mname ^ "." ^ x)) })) ]
                  | _ -> type_error ("module 内の let はパターン束縛にできません: module " ^ mname))
              | T.DLetRec bs ->
                  [
                    ( bdata,
                      T.DLetRec
                        (List.map
                           (fun ((bd2, b) : T.let_binding) ->
                             match snd b.T.lb_name with
                             | T.PVar x -> ((bd2, { b with T.lb_name = (fst b.T.lb_name, T.PVar (mname ^ "." ^ x)) }) : T.let_binding)
                             | _ -> type_error "module 内の let rec はパターン束縛にできません")
                           bs) );
                  ]
              | T.DInstance _ -> [ bnode ]
              | T.DExtern ex -> [ (bdata, T.DExtern { ex with T.ex_name = mname ^ "." ^ ex.T.ex_name }) ]
              | T.DModule _ -> type_error "module の入れ子は未対応です(M10)"
              | T.DEffect _ | T.DClass _ | T.DExp _ -> type_error ("module 内では未対応の宣言です: module " ^ mname))
            body
      | _ -> [ node ])
    decls

(* ## 11.43 最初の 1 つで打ち切る

   型エラーは最初の 1 つで打ち切ります。ただし、そこまでに確定した出力行は
   返します。エラー回復を実装していないので、2 つ目以降のエラーは 1 つ目の
   影響を受けた嘘になりがちで、それを並べても読み手の役に立たないからです。
   ここまでの型が見えれば、どこまで通ってどこで止まったかが分かります。

   例外を型付きの返り値に変えるのはこの 1 箇所です。以降 — 終了コードの
   規約と印字 — は第16章 (driver.ml) の仕事です。

   ## この章が守っている不変条件

   最後に、読み返すときの手がかりとして 5 つ挙げておきます。

   1. **`eff` は下向き、`level` は引数。** どちらも大域状態にしない。
      レベルの戻し忘れという古典的なバグが原理的に起きない。
   2. **一般化してよいのは関数か構文的な値のときだけ。** 注釈は理由に
      ならない (§11.28)。
   3. **網羅性検査は一般化より前に流し切る。** 一般化のあとでは、閉じる
      べき行がもう凍っている (§11.14)。
   4. **剛定数は作ったスコープの中でだけ硬い。** 出口で Generic に変える
      前に、漏れは `unify` が捕まえている (§11.27)。
   5. **解決した名前は木に書く。** コンストラクタの並べ替え、操作の完全名、
      節の種別。評価器に同じ計算をさせない (§11.8、§11.18、§11.22)。

   次の第12章からは実行時の話に移ります。この章が木に書き込んだ型と
   解決結果を、第14章の評価器がそのまま読みます。 *)

let type_check ?(prelude = []) decls =
  current_out := [];
  try (type_check_decls ~prelude decls, None) with
  | Type_error msg -> (!current_out, Some ("! 型エラー: " ^ msg))
  | Syntax_error msg -> (!current_out, Some ("! 構文エラー: " ^ msg))
