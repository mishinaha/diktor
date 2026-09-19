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

   トップレベルは 1 回では片付きません。前方参照 (sample.kel:399 の
   `user_names` が後方の `println`(:440) を呼ぶ) と、宣言どうしの相互再帰を
   通すために、宣言列を 4 回なめます。

   | パス | 登録するもの | なぜ独立のパスか |
   |---|---|---|
   | 1a | エイリアスの表、newtype の**頭** (名前とカインド) | 型の本体を書く前に全構成子のカインドが引けている必要がある |
   | 1a′ | (登録しない) newtype の本体の投機 | パラメータのカインドを宣言順に依存せず決めるため |
   | 1b | newtype の ctor、effect の操作、class のメソッド | 型の本体を書くのでカインド表が要る。宣言順に依存しない(残る例外は §11.31 の末尾 — 投機が届かない形へ要素なしの波括弧を渡したとき) |
   | 1c | インスタンスの頭、**注釈が完全な** let の署名 | 頭の検査にクラス表が要る。署名は前方参照の材料 |
   | 2 | let / let rec / 式 / extern / インスタンス本体 | 宣言順に本体を推論し、順に型を印字する |

   1a〜1c が「表を埋める」パス、2 が「本体を推論する」パスです。表の 1a′ は
   独立のパスではなく 1a の後始末で、表には何も登録しません(§11.39)。
   同じ形の後始末は 1b の後にも 2 つ走ります。
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
   | `at_node` | 位置なしの型エラーに最内ノードの span を貼る (E1 / D53) |
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

let warnings_count = ref 0

(* 先頭に積み、読む側が向きを戻す(M19 検証 — 末尾 @ は警告数の二乗。
   G3b が Exhaust.queue から取り除いたのと同じ形がここに残っていた) *)
let warn msg =
  warnings := msg :: !warnings;
  incr warnings_count

(* 出力の 1 行。種別を値で持つ(D54)。⚠ の前置などの整形は第16章の責任で、
   表示文字列を覗いて種別を当てる(かつての先頭バイト比較)ことはしない *)
type out_line = Binding of string | Warning of string

(* 型エラーで打ち切られるまでの出力行(driver がエラー時にも印字する) *)
let current_out : out_line list ref = ref []

let closed_item_row tys = List.fold_right (fun t acc -> TRowExtend (l_item, t, acc)) tys TRowEmpty

(* 位置なしの Type_error に、投げた**最内**ノードの span を貼る(E1 / D53)。
   位置つきの Type_error_at は素通りするので、外側の at_node は上書きしない。
   大域の「最後に訪れたノード」は持たない — eff は下向き・level は引数、
   という本章の「大域状態にしない」不変条件を診断でも守るため *)
let at_node node f =
  try f () with
  | Type_error msg -> raise (Type_error_at (Tree.loc_of node, msg))
  | NotImplemented feat -> raise (NotImplemented_at (Tree.loc_of node, feat))

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
  (* 浮動小数の本体に整数接尾辞(1.i32 / 1e3i64)は拒否する。受理すると
     実行時の Int32.of_string が本体を読めず、型検査を通ったリテラルが
     必ず落ちる(D25 で 1. が読めるようになった副作用。検証で実測) *)
  | Some (NsInt _ | NsUInt _) when n.n_is_float ->
      type_error ("数値リテラル " ^ Lexer.show_number n ^ " は浮動小数の本体に整数接尾辞が付いています")
  | Some (NsInt 32) -> t_int32
  | Some (NsInt 64) -> t_int64
  | Some (NsFloat 64) -> t_float64
  | Some _ -> noimpl ("数値接尾辞 " ^ Lexer.show_number n ^ "(v0 は i32/i64/f64 のみ)")
  | None ->
      let v = new_var level in
      Unify.add_class v (if n.n_is_float then cls_fractional else cls_integral);
      v

(* v0 で名前だけ受理して実行できない数値型(D13) *)
let unsupported_numeric = [ "Int8"; "Int16"; "UInt8"; "UInt16"; "UInt32"; "UInt64"; "Float32" ]

(* 未束縛の変数の診断。module スコープで解決済みなのに環境に届かない
   (前方の module 名)ときは素の文言、スコープ外に候補があるときだけ
   修飾名を案内する(D39 / D43) *)
let unbound_value name scoped =
  match scoped with
  | Some _ -> type_error ("未束縛の変数: " ^ name)
  | None -> (
      (* 候補に挙げるのは pub の名前だけ。非 pub を案内すると、その通りに
         書いても可視性エラーになる — 従っても直らない助言になる(M16 検証) *)
      let pub_only qs =
        List.filter
          (fun q -> match Hashtbl.find_opt Decls.value_visibility q with Some v -> v.Decls.vis_pub | None -> true)
          qs
      in
      match pub_only (Decls.val_synonym_candidates (intern name)) with
      | [] -> type_error ("未束縛の変数: " ^ name)
      | qs ->
          type_error ("未束縛の変数: " ^ name ^ "(" ^ String.concat " か " (List.map name_of qs) ^ " と修飾してください)"))

(* 構文的に反駁不能なパターンか。関数引数・return 節の網羅性検査
   (M19 / V10)で、確実に警告の出ない形を queue に積まないための
   節約。判定を厳しくしすぎても安全側(queue が正しく判定する) *)
let rec irrefutable_pat ((_, p) : T.pat) =
  match p with
  | T.PVar _ | T.PWildcard -> true
  | T.PAnnot (q, _) -> irrefutable_pat q
  | T.PRecord (fields, rest) ->
      List.for_all (fun (_, q) -> irrefutable_pat q) fields
      && (match rest with None -> true | Some rp -> irrefutable_pat rp)
  | T.PCtor _ | T.PVariant _ | T.PBool _ | T.PNumber _ | T.PText _ -> false

(* pub で @ を省略した宣言の本体行(Rigid)の vid。perform がこの行と
   衝突したとき、単一化の一般文言ではなく pub の規則を名指しで案内する
   ため(H6 / D44) *)
let pub_pure_rows : (oid, unit) Hashtbl.t = Hashtbl.create 8

(* 行の単一化に由来する失敗かどうか(エラー文言の言い換えの門番。M26 の B6)。
   引数の型不一致まで §9 の行の話にしないための判定。pub の言い換え
   (§11.12)と入れ子の省略 @ の言い換え(§11.12 / §11.18)が共用する *)
let row_failure msg =
  let has sub s =
    let n = String.length sub and m = String.length s in
    let rec go i = i + n <= m && (String.sub s i n = sub || go (i + 1)) in
    go 0
  in
  has "行型ではありません" msg || has "スコープ付きの型" msg || has "ラベル " msg || has "は注釈で固定された行変数" msg

(* 「@ を省略した let の、本体が純粋だと**判明した**行」を公開のときに
   行変数へ開き直す(D76。仕様 §9 の表「let は推論する。純粋な本体なら
   行変数として一般化され、どこからでも呼べる」)。行が空に固まるのは、
   本体が @ {} の関数(入れ子の省略 @ を含む)を呼んだときだけ — 何も
   呼ばなければ行変数のまま残るので、この後処理が要るのはその場合に限る。
   純粋な関数にどんな行を名乗らせても、起こすエフェクトが増えるわけでは
   ないので健全(open_explicit_eff がラベル付きの行にやることの、空行版)。
   注釈で @ {} と**書いた**ときは開かない — 呼び出し側にも純粋を要求する
   意図をそのまま残す(仕様 §9「@ {} だけは両方向に効く」)。
   矢印そのものを組み直すので、Tree.set_ty より**前**に呼ぶこと *)
let reopen_pure_row level ty =
  match repr ty with TArrow (a, r, e) when repr e = TRowEmpty -> TArrow (a, r, new_row_var level) | _ -> ty

(* 最外の @ が書かれているか(D76 のガード)。関数束縛は lb_eff、値束縛は
   注釈の頭が矢印リテラルならその @。頭が矢印リテラルでない注釈(型エイリアス
   等)は展開先の矢印が入れ子として読まれる(D75 — 省略は @ {}、@ {} は両方向)
   ので「書かれている」側に倒し、開き直さない。1c の署名(§11.37)も同じ閉じた
   行を作るので、宣言順に依存しない(M26 の検証で見つかった食い違い) *)
let outer_eff_written (b : T.let_binding') =
  match b.T.lb_params with
  | Some _ -> b.T.lb_eff <> None
  | None -> ( match b.T.lb_ret with Some (_, T.EArrow (_, _, eff)) -> eff <> None | Some _ -> true | None -> false)

(* 注釈中の全ての矢印に @ が明示されているか(§11.36 の判定。パス 1c の
   前方参照シグネチャと、pub の完全注釈検査(D44)が共用する) *)
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

(* pub の完全注釈検査(H6 / D44)。引数・返り値の注釈があるだけでなく、
   注釈の**中の**矢印にも @ が要る。M26 より前の理由は「中の矢印の省略 @ は
   推論任せの行になるので、公開 API のエフェクト行が実装で決まる」だった
   (M16 検証で、同じ pub 署名・同じ表示型のまま本体の変更だけで呼び出し側が
   壊れる形を実測)。いまは省略の意味が @ {} に確定している(D75)ので健全性の
   問題は消えたが、規則は仕様 §13(sample.kel:729-732)が可読性の理由で
   残した — 公開 API では純粋を意図したのか書き忘れたのかを読み手が
   区別できなければならない。pub newtype のフィールド(§11.31)も同じ。

   値束縛(引数リストを持たない `let`)の注釈の**頭**の矢印は、この
   「中の矢印」に入りません。頭は束縛の最外だからです(D116 / P9)。
   仕様 §13 は入れ子の矢印の `@` も省略できないと書き、最外の省略には
   別の意味 — 本体は純粋、公開される型は行多相 — を与えています。
   `fully_effected_value_head` は `fully_effected` とその 1 点だけで
   分かれます。頭が矢印リテラルなら引数と返り値だけを検査し、頭の `@` の
   有無は問いません。頭が矢印でない注釈(型エイリアス等)には最外の矢印が
   無いので、そのまま `fully_effected` に渡します。関数束縛の `lb_ret` は
   返り値の型 = 入れ子なので、従来どおり全ての矢印に `@` が要ります *)
let fully_effected_value_head ((_, te) as t : T.type_exp) =
  match te with
  | T.EArrow (params, ret, _) -> List.for_all fully_effected params && fully_effected ret
  | _ -> fully_effected t

let check_pub_annots ~params ~ret =
  (match params with
  | Some ps ->
      List.iter
        (fun ((_, p) : T.pat) ->
          match p with
          | T.PAnnot (_, te) ->
              if not (fully_effected te) then
                type_error "pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)"
          | _ -> type_error "pub な宣言には完全な型注釈が必要です(引数に型注釈がありません)")
        ps
  | None -> ());
  match ret with
  | None -> type_error "pub な宣言には完全な型注釈が必要です(返り値の型注釈がありません)"
  | Some te ->
      let ok = match params with None -> fully_effected_value_head te | Some _ -> fully_effected te in
      if not ok then type_error "pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)"

(* ## 11.3 型式の精緻化 — 書かれた型を内部型へ

   `elab_type` は表層の型式を第1章の内部型に変換します。名前解決・エイリアス
   展開・カインド検査がここで同時に済みます。専用のカインド検査パスは
   ありません。かつては「引数の個数が宣言のカインドと合うか」を見るだけで、
   中身は `elab_type` に丸投げしていました (MiniLang §5.2 と同じ割り切り)。
   M23 (D82) からは型構成子の適用で、**宣言されたパラメータのカインドに
   合わせて引数を読み分け、読んだ結果のカインドを照合します**
   (`elab_con_args`)。行カインドのパラメータの位置ではエフェクト行として
   読むので、`Callback[{}]` の `{}` は空行、`Callback[{Print}]` は 1 ラベルの
   閉じた行、`Callback[{Print extends E}]` は開いた行です。それ以外の位置では
   型として読み、`{}` は Unit です。`Box[E]` に行変数を渡す形は、使用点で
   `bind` が内部名を並べて落とすのではなく、宣言のその場で
   「Type を期待しましたが ς1 は Row です」と落ちます(`test/kinds.t` の kinderr)。
   この読み分けを仕様 §6 の条文にしたのが M29 (D123) です。認めないと
   `pub let mk(): Callback[{}]` が書けません — 仕様 §13 が `pub` の型注釈を
   完全に書けと要求するので、`Callback[{}]` と書く手段が無ければ `Callback` を
   公開 API に出す道が閉じます。同じ `{}` が `Callback[{}]` では空行、
   `Box[{}]` では Unit になる非対称は印字では見分けが付かず、値を入れて初めて
   見えます(`test/kinds.t` の rowarg)。

   読み分けの判定は `kind_repr` の構造マッチで、照合は `same_kind` です。
   §1.6 の格言「カインドを直接パターンで見ている箇所は、それだけでバグ候補」に
   あえて逆らう場所で(`elab_type` の中ではここだけ。同じ理由で `same_kind` を
   避ける兄弟が第6章 §6.6 の `kind_equiv` にあります)、理由は `same_kind` が
   `KVar` を張ることにあります — 判定に使うと、未確定のパラメータが全部
   `Row` に固定されます。
   照合の側が張るのはむしろ望ましく、パス 1b の中(相互再帰する newtype が
   互いを参照する形)ではこれがカインドの伝播路として働きます。
   M29 (D127) から 3 つ目の兄弟が §11.6 の `elab_eff` の最後の枝にできました。
   ここの限定はそのまま読めます — 最後の枝は `elab_eff` の中にあって、
   `elab_type` の外だからです。

   名前の引き方には優先順位があります。

   1. `env.types` にある名前 — 型パラメータとリージョン変数。ここが最優先で、
      内側の `[A]` は外側の型構成子 `A` を隠します。
   2. 型エイリアス — あれば**その場で展開**します (§11.5)。
   3. 宣言表の型構成子 — カインドを引き、引数の個数を照合し、パラメータの
      カインドで引数を読み分けて照合します。

   `Decls.resolve_con` を必ず通すのは module 平坦化 (§11.42) の同義語表を
   引くためです。`module Parser` の中で `Parser` と書いても、外から
   `Parser.Parser` と書いても同じ oid に行き着きます。

   `EApply` の頭が型パラメータのときだけは扱いが違い、`tapp` で適用を組み立て、
   カインドは使用時に `kind_of` と `drop_arrows` が決めます。これが高階カインド
   (`F[_]`) の実装のほぼすべてです。**型レベルλを入れない**ので、`f a ~ List Int` は
   `f ~ List, a ~ Int` に構造分解でき、単一化は一階のままです。
   残りの 1 つが定義域の照合で、M28 (D86) で足しました。`TCon` の適用は
   宣言表のカインドと照合しますが、`TApp` の適用は頭のカインド(`kind_of` が
   張った `KArrow` の左)と照合します — `drop_arrows` は定義域を捨てるので、
   ここでしか見られません。`let f[F[_], E](x: F[E], g: () => Unit @ E)` は
   `F[E]` が `E` を Type に確定させ、次の `@ E` で落ちます。診断の位置が
   2 番目の使用点になるのは、`F[E]` の時点では `E` のカインドがまだ未定で
   照合が通ってしまうからです(`test/kinds.t` の hkt)。かつては `F[E]` に
   行を渡しても何も起きず、`(F[R1], () => {}) => Int32` と型付いていました。

   `unsupported_numeric` にある名前をここで弾いているのは、`Int8` を
   「未知の型」と言われるより「v0 では未対応」と言われたほうが読み手の
   時間を返せるからです。

   M29 (D131) からは、**値の型の位置で読んだ結果のカインドも照合します**。
   値の型の位置とは、矢印の引数と返り値・レコードのフィールド・タプルの
   要素・ヴァリアントの積載、そして引数と返り値と値束縛の注釈です。
   照合は `elab_value_type`(注釈の側の入口は `elab_value_type_outer`)が
   `elab_type` の結果に掛け、合わなければ `check_value_kind` が
   「… の型のカインドが Type ではありません: <型> :: <カインド>」と落とします。
   かつてこの照合は newtype のフィールドの**最外**にしかなく (D83)、
   `newtype Bad2[E] = Bad2((E, Int32), () => Unit @ E)` のように 1 段でも
   包めば、行カインドの型パラメータや `EffectRow` エイリアスが値の型のまま
   宣言表に入りました(台帳 V17 / V20)。値の位置に行が座った型は値を作る
   手段が無いので、診断は使用点まで遅れ、使用点が無ければ出ませんでした。

   照合が `same_kind` なのは D83 と同じ理由です。裸のパラメータ 1 個の位置
   (`let f[A](x: A)`)では `A` のカインドがまだ `KVar` なので、照合が
   「値の位置に現れた ⇒ `Type`」という**推論**として働きます。この副作用が
   診断の位置を決めます — 同じパラメータを行と値の両方で使う宣言では、
   先に読んだ側がカインドを決め、二番目の使用点で落ちます (§11.4)。
   判定(`kind_repr` の構造マッチ)と照合(`same_kind`)の使い分けは
   `elab_con_args` と同じで、読み分けの側に `same_kind` を使わないのは
   未確定のパラメータを固定しないためです。

   名詞句は位置ごとに違い、`check_value_kind` の引数として渡ります。D83 が
   コンストラクタ名を添えた文面もこの補助関数を呼ぶので、newtype の
   フィールドの最外だけは「コンストラクタ X のフィールドの型」のまま
   残ります (§11.31)。`test/kinds.t` の valkind / annotkind / rowval /
   hktval と、D83 から動いていない fieldkind / fieldalias を合わせて、
   8 種類の名詞句と落ちる位置が固定してあります。 *)

(* 値の型の位置のカインド照合(D131)。what は「… の型」で終わる名詞句で、
   文面は D83 が newtype のフィールドに与えていたものをそのまま一般化した。
   カインドの併記を落とす枝があるのは、未確定の KVar が ?k997 の形で
   漏れると番号がプレリュードの行数で動くため — 照合が same_kind の
   ここでは KVar は張られて通るので届かないが、同じ文面を構造マッチで
   判定する側(エフェクト位置)と 1 か所に揃えておく *)
let kind_error what ~expected ty =
  let k = kind_repr (Unify.kind_of ty) in
  let annot = match k with KVar _ -> "" | _ -> " :: " ^ show_kind k in
  type_error (what ^ "のカインドが " ^ expected ^ " ではありません: " ^ Show.show ty ^ annot)

let check_value_kind what ty = if not (same_kind (Unify.kind_of ty) KStar) then kind_error what ~expected:"Type" ty

(* newtype の本体の投機(D132、§11.31)の最中だけ真。型引数の読み分け
   (elab_con_args)がこれを見て、型としても行としても読める字面を飛ばす *)
let speculating = ref false

let rec elab_type env level ~expanding ?(outer = false) (((_, te) as t) : T.type_exp) : ty =
  (* 内部再帰にも at_node を掛ける(検証の指摘)。入口だけ包むと、入れ子の
     注釈のどこで落ちても注釈全体の先頭がアンカーになってしまう *)
  at_node t @@ fun () ->
  match te with
  | T.EIdent (LongId [ n ]) -> (
      match SMap.find_opt n env.types with
      | Some t -> t
      | None ->
          if List.mem n unsupported_numeric then noimpl ("数値型 " ^ n ^ "(v0 は Int32/Int64/Float64 のみ)")
          else
            let oid = Decls.resolve_con (intern n) in
            Decls.check_con_visible oid;
            (match Hashtbl.find_opt Decls.aliases oid with
            | Some info -> expand_alias env level ~expanding info []
            | None ->
                if Hashtbl.mem Decls.con_kinds oid then (
                  match Decls.con_kind oid 0 with
                  | KStar -> TCon (oid, [])
                  | _ -> type_error ("型構成子 " ^ n ^ " には型引数が必要です"))
                else
                  (* スコープ外の module 内部型なら候補を添える(D39 / D43)。
                     案内するのは pub の型だけ — 非 pub は従っても直らない *)
                  match
                    List.filter
                      (fun q -> match Hashtbl.find_opt Decls.con_visibility q with Some v -> v.Decls.vis_pub | None -> true)
                      (Decls.con_synonym_candidates oid)
                  with
                  | _ :: _ as cands ->
                      type_error
                        ("未知の型: " ^ n ^ "(" ^ String.concat " か " (List.map name_of cands) ^ " と修飾してください)")
                  | _ -> type_error ("未知の型: " ^ n)))
  | T.EIdent li -> (
      (* 平坦化済み module の修飾型参照(Parser.Parser 等)。修飾名でも
         エイリアスは引ける(M.A の形。M16 で発見した抜け) *)
      let oid = Decls.resolve_con (intern (show_long_id li)) in
      Decls.check_con_visible oid;
      match Hashtbl.find_opt Decls.aliases oid with
      | Some info -> expand_alias env level ~expanding info []
      | None ->
          if Hashtbl.mem Decls.con_kinds oid then (
            match Decls.con_kind oid 0 with
            | KStar -> TCon (oid, [])
            | _ -> type_error ("型構成子 " ^ show_long_id li ^ " には型引数が必要です"))
          else type_error ("未知の型: " ^ show_long_id li))
  | T.EApply ((_, T.EIdent (LongId comps)), args) when List.length comps > 1 -> (
      let oid = Decls.resolve_con (intern (String.concat "." comps)) in
      Decls.check_con_visible oid;
      match Hashtbl.find_opt Decls.aliases oid with
      | Some info -> expand_alias env level ~expanding info args
      | None ->
          if Hashtbl.mem Decls.con_kinds oid then (
            let k = Decls.con_kind oid (List.length args) in
            let rec arity k = match kind_repr k with KArrow (_, r) -> 1 + arity r | _ -> 0 in
            if arity k <> List.length args then type_error ("型構成子 " ^ String.concat "." comps ^ " の引数の個数が不正です")
            else TCon (oid, elab_con_args env level ~expanding (String.concat "." comps) k args))
          else type_error ("未知の型: " ^ String.concat "." comps))
  | T.EApply ((_, T.EIdent (LongId [ n ])), args) -> (
      match SMap.find_opt n env.types with
      | Some t ->
          (* HKT 変数への適用。カインドは使用時に kind_of / drop_arrows が確定する。
             定義域の照合はここでしか書けない — drop_arrows は定義域を捨てる(D86)。
             acc は畳む前の頭、acc' は tapp の結果(頭が TCon なら畳まれる — §1.7)。
             kind_of acc' を先に呼ぶのは、頭がまだ KVar のとき drop_arrows に
             KArrow(新, 新)を張らせるためで、そのあと kind_of acc を見ると
             定義域が取り出せる *)
          List.fold_left
            (fun acc a ->
              let at = elab_type env level ~expanding a in
              let acc' = tapp acc at in
              ignore (Unify.kind_of acc');
              (match kind_repr (Unify.kind_of acc) with
              | KArrow (d, _) ->
                  if not (same_kind d (Unify.kind_of at)) then
                    type_error
                      ("型引数のカインドが一致しません: " ^ show_kind d ^ " を期待しましたが " ^ Show.show at ^ " は "
                     ^ show_kind (Unify.kind_of at) ^ " です")
              | _ -> ());
              acc')
            t
            (List.map (fun a -> check_no_hole a) args)
      | None -> (
          let oid = Decls.resolve_con (intern n) in
          Decls.check_con_visible oid;
          match Hashtbl.find_opt Decls.aliases oid with
          | Some info -> expand_alias env level ~expanding info args
          | None ->
              if Hashtbl.mem Decls.con_kinds oid then (
                let k = Decls.con_kind oid (List.length args) in
                let rec arity k = match kind_repr k with KArrow (_, r) -> 1 + arity r | _ -> 0 in
                let expected = arity k in
                if expected <> List.length args then
                  type_error (Printf.sprintf "型構成子 %s の引数は %d 個必要です(%d 個与えられました)" n expected (List.length args))
                else TCon (oid, elab_con_args env level ~expanding n k args))
              else type_error ("未知の型: " ^ n)))
  | T.EApply _ -> type_error "型適用の頭は型名でなければなりません"
(* ## 11.4 矢印・レコード行・ヴァリアント和

   矢印 `(A, B) => R @ E` は `TArrow (引数レコード, 返り値, エフェクト行)` に
   なります。引数は閉じた `_item` 行のレコードなので、`(A) => R` と
   `(A, B) => R` は行の長さが違うというだけで別の型になります。

   `@` を省いた矢印の読み方は、矢印の**位置**で決まります(仕様 §9、
   sample.kel:413-438、M26 / D75)。

   | 矢印の位置 | 書いたラベル付き行 | `@ {}` | `@` 省略 |
   |---|---|---|---|
   | 束縛の**最外**(`let` / `pub let` / `extern` / クラスメソッド) | 本体には上限、公開は行変数で開く(§11.26。クラスメソッドは M26 の検証まで開いておらず、§11.33 で直した) | 閉じたまま(両方向) | `let` = 推論、`pub let` = 純粋(D44)、メソッド = 実装純粋・公開行多相、`extern` = 行変数 |
   | **入れ子**(引数の型・返り値の中・newtype のフィールド・effect の操作型の引数・エイリアスの展開先) | 書いたとおり閉じたまま(開かない) | 閉じたまま | **`@ {}`(純粋)** |

   最外の矢印は `elab_binding` が `TArrow` を手で組み立てるので、ここには
   来ません。ここに来る矢印は原則すべて入れ子で、例外は `elab_type_outer` から
   入る 2 か所(クラスメソッドの型と、引数リストを持たない値束縛の注釈の頭)
   だけです。だから `EArrow` の省略 `@` は `outer` が真のときだけ新しい行変数に
   なり、それ以外は閉じた空行 `TRowEmpty` になります。

   かつては位置を見ず、省略はいつも新しい行変数でした。newtype のフィールドに
   `() => Int32` と書けば「何でも起こせる閉包」の意味になり、エフェクトつきの
   閉包を純粋として取り出せました(台帳 V14。`test/annot_rows.t` の launder)。
   計画 260829-4 の I8 は逆に「入れ子のラベル付き行も開こう」と提案していましたが、
   仕様は「入れ子は書いたとおり、省略は `@ {}`」と裁定しました。行を通したいなら
   `newtype Callback[E] = Callback(() => Unit @ E)` のように行変数を型パラメータに
   取ります(M23 がその手段を先に入れています)。

   `extends` の右は 2 通り受けます。行そのものと、レコード型です。後者は
   行を取り出して splice します。`{x: Int32 extends Point}` が書けるのは
   このためで、Point の行がその場に展開されます。

   この 3 つの構文は、どれも**値の型の位置**を持ちます (D131、§11.3)。
   そこで読んだ型のカインドが `Type` でなければ、その位置で落とします。

   | 構文 | 値の型の位置 | 位置ではない部分 |
   |---|---|---|
   | 矢印 `(A, B) => R @ E` | 引数 `A` `B` と返り値 `R` | `@` の右の行 `E` |
   | レコード行 `{a: A}` | 各フィールドの型(`_item` ラベルはタプルの要素) | `extends` の右 |
   | ヴァリアント `#Tag(T)` | 積載 `T` | 和の要素そのもの(行かヴァリアント) |

   落ちる位置は読む順で決まります。レコードとタプルの要素は
   `List.fold_right` で**右から**読むので、`(() => Unit @ E, E)` では第 2 要素の
   `E` が先に `Type` を決め、第 1 要素の `@ E` が「行カインドではない型
   パラメータです」で落ちます(`test/kinds.t` の rowval3)。コンストラクタの
   フィールドは左から読むので (§11.31)、同じ形を `newtype Bad2[E] =
   Bad2((E, Int32), () => Unit @ E)` と書けば落ちるのは第 2 フィールドです。
   どちらも宣言の時点で落ちるという結論は同じで、位置だけが違います。
   読む順を左からに揃えるには行の構築順を変えることになるので、
   ここでは触っていません。

   ヴァリアント和 `#Even | #Odd | R` は各要素を行に落として `row_append` で
   連結します。ここで 1 つだけ規則を課しています。

   > 開いていてよいのは末尾の要素だけ。

   途中に開いた行が来ると、連結後にどのラベルがどの尾部に属するのかが
   決まりません。閉じた要素どうしの連結なら結果も閉じ、`report`
   (sample.kel:193-198) が `case _` なしで網羅と判定されます。ヴァリアント和が
   網羅性検査 (第10章) と噛み合うのは、この「閉じたまま連結できる」性質
   ちょうどそのものです。

   `EHole` (`_`) はインスタンス頭の `List[_]` 専用です。型式の一般の位置に
   穴を許すと部分適用と同じ問題に踏み込むので、ここで拒否します。 *)

  | T.EArrow (params, ret, eff_opt) ->
      let param_tys = List.map (fun p -> elab_value_type env level ~expanding "矢印の引数の型" p) params in
      (* 仕様 §9(改訂): 省略された @ の読み方は矢印の**位置**で決まる(D75)。
         入れ子の矢印(最外以外の全て — 引数の型・返り値の中・newtype の
         フィールド・effect の操作型・型エイリアスが展開する矢印)の省略は
         @ {}(純粋)。最外(outer = true。クラスメソッドの型と、引数リストを
         持たない値束縛の注釈の頭)だけが従来どおり新しい行変数になる。
         再帰はすべて outer を省く = false で降りる *)
      let eff =
        match eff_opt with
        | Some e -> elab_eff env level ~expanding e
        | None -> if outer then new_row_var level else TRowEmpty
      in
      TArrow (TRecord (closed_item_row param_tys), elab_value_type env level ~expanding "矢印の返り値の型" ret, eff)
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
            | T.BField (l, t) ->
                let what = if l = "_item" then "タプルの要素の型" else "レコードのフィールド " ^ l ^ " の型" in
                TRowExtend (intern l, elab_value_type env level ~expanding what t, acc)
            | T.BLabel _ -> type_error "エフェクトラベルはこの位置(レコード型)では使えません")
          elems tail
      in
      TRecord row
  | T.EVariantCase (s, payload) ->
      let pty =
        match payload with None -> t_unit | Some t -> elab_value_type env level ~expanding ("ヴァリアント #" ^ s ^ " の積載の型") t
      in
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
                let pty =
                  match payload with
                  | None -> t_unit
                  | Some t -> elab_value_type env level ~expanding ("ヴァリアント #" ^ s ^ " の積載の型") t
                in
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

(* ## 11.5 エイリアスは透過・非再帰・部分適用禁止・制約は言及時

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

   第 3 の規則が M17 (D51) で加わりました。

   > **規則 3: パラメータ制約は言及時に課す。**

   第 4 の規則は M26 (D75) です。

   > **規則 4: エイリアスが展開する矢印は常に入れ子として読む。**

   `type Thunk = () => Unit` の省略 `@` は、`Thunk` を最外に書いても `@ {}` です
   (仕様 §9 が「型エイリアスが展開する矢印」を入れ子側に挙げています)。
   `expand_alias` の本体精緻化は `outer` を渡さないので、これは自動的に
   そうなります(`test/annot_rows.t` の alias)。

   書かれた行にも同じ規則が掛かります。`type F[A] = (A) => Int32 @ Print` を
   束縛の最外の位置に書いても、`{Print}` は閉じたまま残って開きません
   (D121 / P27)。開かせたいときは矢印をリテラルで書きます。`outer` を渡さない
   だけでは足りない場所が型クラスのメソッドの登録にあり、そちらは展開後の型が
   矢印かどうかだけを見て開いていたので、注釈の頭が矢印リテラルのときに限るよう
   直しました(§11.33。`test/annot_rows.t` の clsalias3 / clslit)。

   `type P[A: Show] = (A, A)` の `Show` は `P[X]` と**書いた時点**で `X` に
   要求されます。エイリアスは透過で構築点を持たないので、制約を効かせ
   られる場所は言及時しかありません(newtype の制約が値の構築時に効くのと
   対照的に、より早い時点になります)。かつては tp_classes が黙って無視され、
   同じ構文を書いても何も起きませんでした。

   第 5 の規則は M28 (D84) で、規則 3 と対になります。

   > **規則 5: 引数はパラメータのカインドに合わせて読む。**

   エイリアスに構築点が無いことの帰結がもう 1 つあります。newtype なら
   `Callback[{Print}]` の `{Print}` を行として読むための情報は宣言表の
   `dd_params` にありますが、透過なエイリアスは展開後に痕跡を残さないので、
   パラメータのカインドだけは表(`al_kinds`、第6章 §6.5)に残しておかないと
   使用点で読み分けられません。カインドは 1b の後始末が本体を一度投機的に
   精緻化して決めます(§11.39)。読み分けと照合の規則は `elab_con_args` と
   同じで、`type Cb[E] = Callback[E]` に `Cb[{Print}]` と書けるようになりました
   (`test/kinds.t` の alias)。かつては引数を全部型として読んでいたので、
   行変数を渡す形だけが通り、具体的な行は「エフェクトラベルはこの位置
   (レコード型)では使えません」で落ちていました。

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

(* 値の型の位置で読んだ型のカインドが Type であることを見る(D131)。
   矢印の引数と返り値、レコードのフィールド(タプルの要素を含む)、
   ヴァリアントの積載、そして外側からは引数と返り値の注釈がこれを通る。
   見ないと、行カインドの型パラメータや EffectRow エイリアスが値の型として
   表に入り、使用点まで診断が遅れて内部名になる(台帳 V17 / V20)。
   判定に same_kind を使うのは §11.31 のフィールド検査と同じ理由で、
   裸のパラメータ 1 個の位置では「値の位置に現れた ⇒ Type」という推論として
   働く。at_node を部分式に掛け直すのは、注釈全体の先頭ではなく
   カインドが合わなかった位置を指すため *)
and elab_value_type env level ~expanding what t =
  let ty = elab_type env level ~expanding t in
  at_node t (fun () -> check_value_kind what ty);
  ty

(* 型引数を宣言されたパラメータのカインドに合わせて読む(D82、仕様 §6)。
   Row のパラメータなら elab_eff、そうでなければ elab_type。
   読み終えたらカインドを照合する — 不一致はここで落とす方が、
   subst_params 越しに使用点で bind が落とすより早く読みやすい。
   読み分けの判定は kind_repr の構造マッチで行い、same_kind は使わない
   — same_kind は KVar を張るので、判定に使うと未確定のパラメータを
   全部 Row に固定してしまう(§1.6 の格言にあえて逆らう。同じ理由の
   兄弟が §6.6 の kind_equiv)。
   照合の側は same_kind でよく、パス 1b ではこれがカインドの伝播路になる。
   elab_eff を ~check_row:false で呼ぶのは、行にならなかったことを
   このすぐ下の照合が構成子名と引数の位置つきで言うから(D127)。
   抑制しないと、より一般的な「エフェクト位置の型のカインドが Row では
   ありません」が先に出て、どの引数かが位置からしか読めなくなる *)
and elab_con_args env level ~expanding cname k args =
  let rec go k i = function
    | [] -> []
    | a :: rest ->
        let pk, kr = match kind_repr k with KArrow (a', r) -> (a', r) | _ -> (new_kind_var (), KStar) in
        let a = check_no_hole a in
        (* 投機の間は、カインドが未確定のパラメータへ渡した要素なしの波括弧
           ({} と {extends R})を読まずに飛ばす(M29 の検証)。この 2 形だけが
           型としても行としても読めるので、型として読んで照合すると相手の
           パラメータを Type に張ってしまい、1b が宣言順に読めば Row と
           決まったはずの宣言を落とす。飛ばしても失うものは無い —
           1b がもう一度、相手のカインドが決まった状態で読む *)
        let ambiguous =
          !speculating && match (kind_repr pk, snd a) with KVar _, T.EBraceRow ([], _) -> true | _ -> false
        in
        let t =
          if ambiguous then t_unit
          else
            match kind_repr pk with KRow -> elab_eff ~check_row:false env level ~expanding a | _ -> elab_type env level ~expanding a
        in
        if (not ambiguous) && not (same_kind pk (Unify.kind_of t)) then
          type_error
            (Printf.sprintf "型構成子 %s の第%d引数のカインドが一致しません: %s を期待しましたが %s は %s です" cname (i + 1)
               (show_kind pk) (Show.show t) (show_kind (Unify.kind_of t)));
        t :: go kr (i + 1) rest
  in
  go k 0 args

and check_no_hole ((_, te) as t : T.type_exp) =
  match te with T.EHole -> type_error "_ はこの位置では使えません(インスタンス頭の List[_] 専用)" | _ -> t

(* 「未知のエフェクト」の言い分け(D85)。名前が型として登録されていれば
   綴りの誤りではなく位置の誤りなので、そう言う。resolve_con は module の
   同義語を辿るので、スコープ外の内部型名にもこちらの文言が出うるが、
   受理・拒否は変わらない *)
and unknown_effect n =
  if Hashtbl.mem Decls.con_kinds (Decls.resolve_con (intern n)) then
    "型 " ^ n ^ " はエフェクトではありません(ここにはエフェクト行が要ります)"
  else "未知のエフェクト: " ^ n

(* エイリアスが開いた行に展開されたときの splice(M28 の検証で見つかった
   Panic の修正)。row_append は左が閉じていることを要求するので、展開結果の
   閉じた前置部分をなぞり、残りの要素(acc)を行変数の手前に差し込む —
   {W[E], Console} は {Print, Console extends E} になる。acc も開いていたら
   行変数が 2 つになるので型エラー。かつては acc が空でないと row_append の
   bug に落ちていた *)
and splice_row alias_name expanded acc =
  let rec closed r = match repr r with TRowExtend (_, _, rest) -> closed rest | TRowEmpty -> true | _ -> false in
  let rec go r =
    match repr r with
    | TRowExtend (n, a, rest) -> TRowExtend (n, a, go rest)
    | TRowEmpty -> acc
    | tail ->
        if closed acc then row_append acc tail
        else
          type_error
            ("エイリアス " ^ alias_name ^ " は開いた行に展開されるので、extends や別の開いた行と同じ行には置けません(行変数は 1 つまで)")
  in
  go expanded

and expand_alias env level ~expanding info args =
  if List.mem info.Decls.al_name expanding then
    type_error ("型エイリアス " ^ name_of info.Decls.al_name ^ " が再帰しています(エイリアスは非再帰)")
  else if List.length args <> List.length info.Decls.al_params then
    type_error
      (Printf.sprintf "型エイリアス %s の引数は %d 個必要です(%d 個与えられました。部分適用は禁止)" (name_of info.Decls.al_name)
         (List.length info.Decls.al_params) (List.length args))
  else
    (* 引数は**使用スコープ**で精緻化する(呼び出し側の module のまま)。
       読み分けは表のカインド(al_kinds、D84)で決める — 規則は elab_con_args と
       同じ(判定は kind_repr の構造マッチ、照合は same_kind)。al_kinds は
       構築点で al_params と同じ長さに作られるので、食い違いは処理系の欠陥 *)
    if List.length info.Decls.al_kinds <> List.length info.Decls.al_params then
      bug ("expand_alias: " ^ name_of info.Decls.al_name ^ " の al_kinds の長さが al_params と違います");
    let arg_tys =
      List.map2
        (fun a pk ->
          let a = check_no_hole a in
          let t =
            match kind_repr pk with
            | KRow -> elab_eff ~check_row:false env level ~expanding a
            | _ -> elab_type env level ~expanding a
          in
          if not (same_kind pk (Unify.kind_of t)) then
            type_error
              ("型エイリアス " ^ name_of info.Decls.al_name ^ " の型引数のカインドが一致しません: " ^ show_kind pk
             ^ " を期待しましたが " ^ Show.show t ^ " は " ^ show_kind (Unify.kind_of t) ^ " です");
          t)
        args info.Decls.al_kinds
    in
    (* パラメータ制約は展開時 = **型を書いた時点**で課す(M17 / D51)。
       エイリアスは透過で、展開後の型に制約の痕跡が残らない — だから
       その場で見るしかない。newtype より**早い**時点になる(newtype の
       制約は値の構築時に効く。Box[NoShow] は型として書けるが Box(v) で
       落ちる — エイリアスに構築点は無いので言及時しかない)。かつては
       tp_classes を一切見ず、type P[A: Show] = (A, A) に非 Show の型が
       黙って通った(実測) *)
    List.iter2
      (fun (tp : type_param) t -> List.iter (fun li -> Unify.add_class t (intern (show_long_id li))) tp.tp_classes)
      info.Decls.al_params arg_tys;
    let types =
      List.fold_left2 (fun m tp t -> SMap.add tp.tp_name t m) SMap.empty info.Decls.al_params arg_tys
    in
    (* エイリアス本体は閉じている: 型パラメータだけが見える *)
    let env' = { env with types } in
    let expanding = info.Decls.al_name :: expanding in
    (* 本体は**宣言スコープ**で展開する(D43)。module 内のエイリアスが
       内部型を指しているとき、外から使っても壊れないように *)
    let saved = !Decls.current_module in
    Decls.current_module := info.Decls.al_module;
    Fun.protect
      ~finally:(fun () -> Decls.current_module := saved)
      (fun () ->
        match info.Decls.al_kind with
        | Some "EffectRow" -> elab_eff env' level ~expanding info.Decls.al_body
        | _ -> elab_type env' level ~expanding info.Decls.al_body)

(* ## 11.6 エフェクト行の精緻化 — 同形の構文をスコープで分ける

   Keleut では `@ E` (行変数) と `@ Print` (エフェクト名) が構文上まったく
   同じ形をしています。区別できるのは型検査器だけで、その判定がこの関数です。

   1. `env.types` にあり、カインドが行なら — 行変数。
   2. `EffectRow` と注記されたエイリアスなら — 展開して splice。引数が
      あってもなくても、エイリアスは effect 宣言表より先に見ます
      (M28 / D85)。
   3. effect 宣言表にあれば — `@ Print` は `@ {Print}` の略記なので、
      ラベル 1 つの閉じた行にする。

   ここで `same_kind` を使っているのは、arity 0 の型パラメータのカインドが
   宣言時には未定 (`KVar`) だからです (D7)。`[E]` と書いただけでは行なのか型なのか
   分からず、使用位置で決まります。構造比較で `KRow` かどうかを見ると、
   まだ `KVar` のままの行変数を取りこぼします。これは実際に踏んだ罠で、
   同じ取りこぼしが第8章の `rewrite_row` にもあり、`fst({x=1, _item=...})` が
   落ちていました (260829-2b の健全性 1)。

   > カインドは構造で比べず `same_kind` で比べる。まだ変数かもしれない。

   この格言には例外が 3 つあります。§11.3 の `elab_con_args` の読み分け、
   第6章 §6.6 の `kind_equiv`、そして下に書く**最後の枝の照合** (D127) です。
   どれも `same_kind` に張られては困る位置で、なぜここでは構造で比べてよいかを
   その場に書いてあることだけが歯止めです。

   ラベルの引数は 1 つまでです (`Heap[h]` のように)。ラベルの引数欄が
   そのままエフェクトのパラメータで、パラメータを持たないエフェクトは
   そこに `Unit` を置きます。行変数の中置合成 (`{E1, Print}` の `E1`) は
   受けません。行の合成は末尾の `extends` だけ、と決めておくと、
   `row_append` の左辺が常に閉じているという不変条件が保てます。例外は
   開いた行に展開されるエイリアスの splice で、これは `splice_row` が展開結果の
   閉じた前置部分に残りの要素を差し込む形で同じ不変条件を守ります
   (`{W[E], Console}` は `{Print, Console extends E}`。M28 の検証で見つけた
   Panic の修正 — `test/kinds.t` の splice2)。行変数が 2 つになる形
   (`{W[E] extends E2}`)は型エラーです。

   `Heap[h]`(ラベルの引数)と `WithPrint[E]`(パラメータつき EffectRow
   エイリアスの適用)は構文上同形です。取り違えないのは、型名・エフェクト名・
   エイリアス名が `claim_type_name` の 1 つの名前空間に載っているからで、
   名前を引けばどちらかは決まります。かつては引数つきの要素がエフェクト表
   しか見ず、`{Fs, WithPrint[E]}` が「未知のエフェクト: WithPrint」で落ちて
   いました(M17 の記録。M28 / D85 で閉じました — `test/kinds.t` の splice)。
   同じ改稿で「未知のエフェクト」を言い分けるようにしました。名前が型として
   登録されているなら綴りの誤りではなく位置の誤りなので、`Callback[Int32]` は
   「型 Int32 はエフェクトではありません」と言います(`unknown_effect`)。

   上の枝のどれにも当たらなかったものが**最後の枝**に落ちます。ここへ通る道は
   3 つです。文法(`eff` / `eff_name`)が通す module 修飾の名前 (`M.T` / `M.W`) と、
   エフェクト名でない頭への適用 (`W[E]` / `MutableArray[Int32, Int32]`)。
   そして 3 つ目が `{… extends <ty>}` の右です — 文法の `extends` は `eff` では
   なく **`ty`** を取り(`parser.mly` の `lbrace EXTENDS ty RBRACE`)、
   `EBraceRow` の枝がその `ty` をそのまま `elab_eff` へ再帰で渡すので、
   `@ {extends #Tag}` のように `eff` では書けない型式もここへ届きます。
   EffectRow エイリアスの適用はここを通って正しく行になるので、
   枝ごと落とすわけにはいきません。そこで M29 (D127) からは、`elab_type` で
   読んだ結果のカインドを照合し、行でなければ
   「エフェクト位置の型のカインドが Row ではありません: <型> :: <カインド>」と
   落とします。文面は §11.3 の値の型の位置と同じ `kind_error` から出します。
   かつては無条件に `elab_type` へ落ちるだけで、
   `let f(x: Int32): Int32 @ MutableArray[Int32, Int32] = x` が
   `@ {extends MutableArray[Int32, Int32]}` と型付いていました(台帳 V19)。
   尾部に座った Type の型は誰とも単一化しないので、その関数は宣言できても
   呼べません。同じ穴が module 修飾の型名 (`@ M.T`) と EffectRow エイリアスの
   本体 (`type W: EffectRow = MutableArray[Int32, Int32]`) にもあり、
   あわせて閉じました(`test/kinds.t` の effkind 〜 effkind5)。

   3 つ目の道の副作用として、`EBraceRow` の枝が持っていた検査
   「extends の右は行でなければなりません」は**到達不能**になりました。
   最後の枝を通ったものは新しい照合を先に抜けるのでカインドが必ず `Row` で、
   ほかの枝が返すのも行だからです。`@ {extends #Tag}` の診断はこの改稿で
   「extends の右は行でなければなりません」から
   「エフェクト位置の型のカインドが Row ではありません: #Tag :: Type」へ
   変わりました(M29 の検証で実測)。枝は安全網として残してあります。

   この照合だけは `kind_repr` の構造マッチで、`same_kind` を使いません。
   **エフェクト位置では推論をさせない**、というのが理由です。裸の型パラメータは
   1 番目の枝が受け、そこは `same_kind` で「まだ `KVar` の行変数かもしれない」を
   拾います。最後の枝にも、カインドが未確定のまま届くものはあります。経路は
   2 つで、1 つは arity 0 の束縛子への適用
   (`let f[F, E](x: Int32): Int32 @ F[E]`) — `drop_arrows` が
   `KArrow (KVar, KVar)` を張った結果の新しい `KVar` です。もう 1 つは
   パラメータのカインドがまだ推論されていない型エイリアスの適用で、
   こちらは `TVar` が返ります。エイリアスのカインド推論(D84)は 1b の後始末に
   走るので、1b の newtype の本体から見ると `al_kinds` は `KVar` のままです
   (`type Id[A] = A` と `newtype N[X] = MkN(() => Unit @ Id[X])` を並べると、
   展開結果の `A` が `KVar` のカインドで最後の枝へ返ります)。
   つまり構造で比べる根拠は「この枝に未確定のカインドは来ない」ではありません。
   **来るからこそ**構造で比べます — ここで `same_kind` を呼べば、それは検査では
   なく `Row` への既定化になります。`F[E]` なら `F` のカインドが
   「Type を取って Row を返す」に固定され、そんなカインドの型構成子は言語に
   無いので、宣言できても呼べない `f` がまた 1 つ残ります。カインドが未確定の
   ときは `:: <カインド>` の併記を落とします。内部の連番が漏れると、番号が
   プレリュードの行数で動いて診断が再現しなくなるからです (§11.3 の
   `kind_error`)。

   照合は `?check_row` で切れます。切るのは D82 の型引数の読み分けの 2 か所
   (`elab_con_args` と `expand_alias`) だけで、そこは呼び出し側が
   「型構成子 Callback の第1引数のカインドが一致しません」と構成子名と引数の
   位置を添えて言うからです(`test/kinds.t` の nest2)。既定が `true` なので、
   将来の新しい呼び出し側は照合つきになります。この結果、**エフェクト位置に
   名前や適用形を書いて、読んだ結果が行にならなかったとき**の言い分けが 3 つに
   分かれました — 綴りの誤り(`未知のエフェクト: Nope`)、位置の誤り
   (`型 Int32 はエフェクトではありません`)、読んだ結果のカインドが行でない
   (`エフェクト位置の型のカインドが Row ではありません`)。1 つの文言に
   揃えるとどれかが嘘になるので、`test/kinds.t` が 3 つを並べて固定しています。
   エフェクト位置で落ちる診断がこの 3 つで尽きるわけではありません。行カインド
   でない型パラメータ(`@ h`)と Type エイリアス(`@ P`)は、名前を引いた時点で
   手前の枝が「行カインドではない型パラメータです: h」
   「エフェクト位置に Type エイリアス P は使えません(: EffectRow を付けて
   ください)」と別の文言で先に落とします(`test/kinds.t` の regionkind /
   classrow)。

   相互再帰の 3 関数を定義し終えたら、`~expanding` を空リストで閉じた
   同名の関数で覆います。以降の呼び出し側は展開中集合の存在を知りません。 *)

and elab_eff ?(check_row = true) env level ~expanding ((_, te) as t : T.type_exp) : ty =
  at_node t @@ fun () ->
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
      else type_error (unknown_effect n)
  | T.EApply ((_, T.EIdent (LongId [ n ])), args) when Hashtbl.mem Decls.effects (intern n) ->
      (* @ Heap[h] = @ {Heap[h]} の略記。文法(eff_name)は受けるのに枝が
         無く、ブレース無しの引数付きラベルだけ「未知の型: Heap」に落ちて
         いた(M18 検証)。sample.kel:410 の略記則に引数の例外は無い *)
      TRowExtend
        ( intern n,
          (match args with
          | [ a ] -> elab_type env level ~expanding a
          | _ -> type_error "エフェクトラベルの引数は1個までです"),
          TRowEmpty )
  | T.EBraceRow (elems, ext) ->
      let tail =
        match ext with
        | None -> TRowEmpty
        | Some t -> (
            (* extends の右は文法(parser.mly)が eff ではなく ty を取るので、
               ここから elab_eff へ再帰で読む = 最後の枝への 3 つ目の入口。
               下の検査は D127 の照合が先に落とすので到達不能になったが、
               安全網として残す(§11.6) *)
            let tt = elab_eff env level ~expanding t in
            if same_kind (Unify.kind_of tt) KRow then tt else type_error "extends の右は行でなければなりません")
      in
      List.fold_right
        (fun elem acc ->
          match elem with
          | T.BLabel (LongId [ n ], args) -> (
              (* エイリアスを先に見る。引数の有無で経路を分けない — エフェクト名と
                 型名は同じ名前空間(claim_type_name)なので、Heap[h](ラベルの引数)と
                 WithPrint[E](エイリアスの適用)を取り違えない(D85)。かつては
                 引数つきの枝がエフェクト表しか見ず、{Fs, WithPrint[E]} が
                 「未知のエフェクト: WithPrint」で落ちていた(M17 の記録) *)
              match Hashtbl.find_opt Decls.aliases (intern n) with
              | Some info when info.Decls.al_kind = Some "EffectRow" ->
                  splice_row n (expand_alias env level ~expanding info args) acc (* 行 splice(計画 §7.6) *)
              | Some _ -> type_error ("エフェクト行に Type エイリアス " ^ n ^ " は置けません(: EffectRow を付けてください)")
              | None ->
                  if args = [] && SMap.mem n env.types then
                    (* {E1, Print} のような行変数の合成は未対応(末尾 extends のみ)。
                       引数つきのときに env.types を見ないのも従来どおり — 型パラメータ
                       への適用は行の要素になれない *)
                    type_error ("行変数 " ^ n ^ " は extends の位置にのみ書けます")
                  else if Hashtbl.mem Decls.effects (intern n) then
                    TRowExtend
                      ( intern n,
                        (match args with
                        | [] -> t_unit
                        | [ a ] -> elab_type env level ~expanding a
                        | _ -> type_error "エフェクトラベルの引数は1個までです"),
                        acc )
                  else type_error (unknown_effect n))
          | T.BLabel (li, _) -> noimpl ("モジュール修飾のエフェクト(M10): " ^ show_long_id li)
          | T.BField (l, _) -> type_error ("エフェクト行にフィールド " ^ l ^ " は書けません"))
        elems tail
  | _ ->
      (* 最後の枝(D127)。ここへ通るのは module 修飾の名前、エフェクト名でない
         頭への適用、そして {… extends <ty>} の右の 3 つ。EffectRow エイリアスの
         適用(W[E] / M.W)はここを通って正しく行になるので、落とすのではなく
         読んだ結果のカインドを照合する。判定は kind_repr の構造マッチで、
         same_kind は使わない — カインドが未確定のまま届く経路があり(F[E] と
         カインド未推論のエイリアスの適用)、same_kind で見ると検査ではなく
         Row への既定化になる(§11.6) *)
      let ty = elab_type env level ~expanding t in
      if check_row && kind_repr (Unify.kind_of ty) <> KRow then kind_error "エフェクト位置の型" ~expected:"Row" ty;
      ty

(* 束縛の**最外**の矢印が注釈としてそのまま書かれている位置(型クラスの
   メソッドの型と、引数リストを持たない値束縛の注釈)専用の入口。ここだけ
   省略 @ が従来どおり新しい行変数になる(仕様 §9 の表の「let は推論」
   「型クラスのメソッドは実装純粋 + 公開行多相」は一般化と包摂が担う)。
   ~outer:true を渡すのはこの 1 か所だけ *)
let elab_type_outer env level t = at_node t (fun () -> elab_type env level ~expanding:[] ~outer:true t)

let elab_type env level t = at_node t (fun () -> elab_type env level ~expanding:[] t)

(* 注釈の位置(引数・返り値・値束縛の頭)も値の型の位置なので同じ照合を通す
   (D131)。通さないと EffectRow エイリアスを書いた注釈が束縛の
   単一化まで生き延び、「カインドが一致しません: _A :: Type と {Print}」と
   内部名で落ちる *)
let elab_value_type env level what t = at_node t (fun () -> elab_value_type env level ~expanding:[] what t)

let elab_value_type_outer env level what t =
  let ty = elab_type_outer env level t in
  at_node t (fun () -> check_value_kind what ty);
  ty

let elab_eff env level t = at_node t (fun () -> elab_eff env level ~expanding:[] t)

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

   `PAnnot` が読む注釈は値の型の位置なので、`elab_value_type` を通して
   カインドを `Type` と照合します (D131、§11.3)。引数の注釈はこの経路で
   読まれるため、`let f(x: P)` に `EffectRow` エイリアスを書いた形は
   期待型との単一化まで進まず、注釈のその場で落ちます
   (`test/kinds.t` の annotkind)。

   すべてのパターン節点に `set_ty` しているのは、評価器と網羅性検査が
   同じ型を後から引けるようにするためです。 *)

let rec elab_pat env level seen expected ((_, p) as node : T.pat) : env =
  Tree.set_ty node expected;
  at_node node @@ fun () ->
  match p with
  | T.PWildcard -> env
  | T.PVar x ->
      if List.mem x !seen then type_error ("同じパターン内で変数 " ^ x ^ " が重複しています")
      else (
        seen := x :: !seen;
        { env with values = SMap.add x expected env.values })
  | T.PAnnot (sub, te) ->
      Unify.unify expected (elab_value_type env level "型注釈" te);
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
            Decls.check_ctor_visible ctor dname;
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
                List.map (fun (i : var_info) -> (i.vid, Unify.new_class_var ~kind:i.vkind ~classes:i.vcls level)) dd.Decls.dd_params
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
  let t = at_node node (fun () -> elab_exp' env level eff node e) in
  Tree.set_ty node t;
  t

and elab_exp' env level eff node e =
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
      | Some sch ->
          (* 修飾名で module の値に触るときの可視性検査(D41)。module 名と
             クラス名の衝突は平坦化が拒否する(§11.42)ので、可視性台帳に
             載っている名前は必ず module の値 — 綴りによる免除は要らない
             (かつて綴りで免除しており、同名クラスを 1 行宣言するだけで
             任意の非 pub 値が外から呼べた — M16 検証) *)
          Decls.check_value_visible (intern name);
          Unify.instantiate level sch
      | None -> (
          (* 環境に無かったときだけ、module スコープの値同義語を引く
             (D39 / D43)。フォールバック専用なので、局所束縛による遮蔽が
             自動で効く。スコープの外では解決せず、候補列(診断専用)で
             修飾名を案内する — 素の「未束縛の変数」では、module の同名
             let が原因だと読み手に辿れない(M15 検証) *)
          let scoped =
            match !Decls.current_module with
            | Some m -> Hashtbl.find_opt Decls.module_val_synonyms (m, intern name)
            | None -> None
          in
          match Option.bind scoped (fun q -> SMap.find_opt (name_of q) env.values) with
          | Some sch -> Unify.instantiate level sch
          | None -> (
              match li with
              | LongId comps when comps <> [] && String.length (List.nth comps (List.length comps - 1)) > 0 ->
                  let last = List.nth comps (List.length comps - 1) in
                  if last.[0] >= 'A' && last.[0] <= 'Z' then elab_construct env level node last []
                  else unbound_value name scoped
              | _ -> unbound_value name scoped)))
  | T.Hole -> new_var level
  | T.Lambda { l_params; l_body } ->
      let param_tys = List.map (fun _ -> new_var level) l_params in
      let seen = ref [] in
      let env2 = List.fold_left2 (fun env p t -> elab_pat env level seen t p) env l_params param_tys in
      let body_eff = new_row_var level in
      let tr = elab_exp env2 level body_eff l_body in
      (* 反駁可能な引数パターンは網羅性検査へ(M19 / V10。let のパターン
         束縛と同じ扱い — かつては型検査を通って実行時に「パターンに値が
         一致しません」で落ちた) *)
      List.iter2 (fun p t -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) l_params param_tys;
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

   決定的な例が sample.kel:540-545 の `copy` です。

   ```
   let copy(src: String, dst: String): Unit @ {Console, Fs} = {
     with _ = with_file(src)
     let text = perform read()                   // File は src のものが最左
     with _ = with_file(dst)
     perform write(text)                         // File は dst のものが最左
   }
   ```

   `with` は「呼び出しの末尾に継続を足す」構文糖 (第3章) なので、これは
   `with_file(src, fn(_) => ...)` に脱糖されます。`with_file` の宣言は
   `body: () => A @ {File, Fs extends E}` なので、期待型を先に押し込めば、
   ラムダの行は `{File, Fs extends E}` に確定した状態で本体に入れます。すると
   `write` を解決するとき行に `File` が見えています。順番を入れ替えると、
   ここは「`write` は Console と File の両方にある」という曖昧さのエラーに
   なります。

   計画にはこの双方向化がありませんでした (乖離 2)。実装して初めて、
   D22 の解決規則が「引数の行が先に固まっていること」を暗黙の前提に
   していたと分かった箇所です。

   > 双方向化は多相のためだけの道具ではない。解決の順序を決める道具でもある。

   単一化が行の不一致で落ちたときの文言は 3 段に言い換えます (M26 の B6)。
   `pub` の `@` 省略の Rigid 行と衝突した形は pub の規則を名指しし(M16)、
   呼び出し先の行が空 = 純粋な関数を空でない行の下から呼ぶ形と、この位置の
   行が空 = 高階の引数の行が `@ {}` である形は、仕様 §9 の「入れ子の矢印の
   `@` 省略は `@ {}`」を案内します(M26)。言い換えるのは行由来の失敗だけで、
   その門番が `row_failure` です — 引数の型不一致まで行の話にしてはいけません。
   `callee_pure` を単一化の**前**に取るのは、単一化が失敗しても呼び出し先の
   行が書き換わっていることがあるからです。 *)

  | T.Apply (f, arg) ->
      let tf = elab_exp env level eff f in
      (* 単一化の**前**に呼び出し先の行を覚えておく(あとでは書き換わる)。
         空行の関数を空でない行から呼ぶ失敗は仕様 §9 の規則そのものなので、
         一般文言のかわりに規則を案内する(M26 の B6) *)
      let callee_pure = match repr tf with TArrow (_, _, e) -> repr e = TRowEmpty | _ -> false in
      let tr = new_var level in
      let pvar = new_var level in
      (* 関数の行を呼び出し側の eff と単一化してから、引数を期待型で検査する(§11.12) *)
      (try Unify.unify tf (TArrow (pvar, tr, eff))
       with Type_error msg ->
         (* pub の @ 省略 = 純粋(D44)。エフェクトつき関数の**呼び出し**が
            Rigid 行と衝突する経路は perform より普通に踏むのに、一般文言
            「行型ではありません: ς1」では原因に到達できない(M16 検証)。
            perform 側(§11.15)と同じ翻訳をここにも置く。ただし翻訳するのは
            行由来の失敗だけ — 引数の型不一致まで pub の話にしない *)
         let pub_pure =
           let _, tail = row_fields eff in
           match repr tail with
           | TVar r -> ( match !r with Rigid i -> Hashtbl.mem pub_pure_rows i.vid | _ -> false)
           | _ -> false
         in
         if pub_pure && row_failure msg then
           type_error ("pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: " ^ msg ^ ")")
         else if row_failure msg && callee_pure then
           type_error
             (msg
            ^ "(呼び出し先の行は空 = 純粋です。行の部分型付けが無いので、空でない行の下からは呼べません。入れ子の矢印の @ 省略は @ {} と読みます — 行を通すなら行変数を型パラメータに取ってください。§9)")
         else if row_failure msg && repr eff = TRowEmpty then
           type_error
             (msg
            ^ "(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)")
         else type_error msg);
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
      let eff_name, op, scheme = resolve_perform eff li in
      Tree.set_resolved node (Tree.ROp (intern (name_of eff_name ^ "." ^ name_of op)));
      let args_row, op_ret =
        match repr (Unify.instantiate level scheme) with
        | TArrow (a, r, _) -> (a, r)
        | _ -> bug "操作スキーマが矢印型ではありません"
      in
      Unify.unify (elab_exp env level eff arg) args_row;
      (try Unify.unify eff (TRowExtend (eff_name, t_unit, new_row_var level))
       with Type_error msg ->
         (* pub の @ 省略 = 純粋(D44)。その Rigid 行と衝突したときだけ、
            規則を名指しで案内する(一般文言「行型ではありません: ς1」は
            原因と結びつかない) *)
         let pub_pure =
           let _, tail = row_fields eff in
           match repr tail with
           | TVar r -> ( match !r with Rigid i -> Hashtbl.mem pub_pure_rows i.vid | _ -> false)
           | _ -> false
         in
         if pub_pure then type_error "pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください)"
         else type_error ("エフェクト " ^ name_of eff_name ^ " をここでは実行できません(" ^ msg ^ ")"));
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
   (sample.kel:470)。`Unit` と単一化するだけなので、規則は 1 行です。

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
              (* 引数省略は操作の返り値型が Unit のときだけ(sample.kel:470) *)
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

   `h` のカインドは `Type` です (M29 / D130、仕様 §10)。`new_rigid` を既定の
   カインドで呼んでいるからで、リージョン専用のカインドは持ちません。帰結は
   2 つあります。行の位置に書いた `@ h` は「行カインドではない型パラメータ
   です: h」で落ち、値の型の位置に書いた `(h) => Int32` は**通ります** —
   値の型の位置が要求するのはカインド `Type` だからです (D131、§11.3。
   `test/kinds.t` の regionkind / regionkind2)。Region のカインドを分けな
   かったのは、得られるものが「値の型の位置に `h` と書けなくなる」だけで、
   代償が第1章のカインド定義・`same_kind` と `kind_of`・宣言表・`show_kind`・
   組み込みスキーマの書き換えだからです。`h` の値を作る手段はどこにも無いので、
   書けてしまう型に値は住めず、健全性は破れません (台帳 V21)。

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
   `bug` で落とします。型検査器の内部矛盾はユーザのエラーではありません。

   コンストラクタの引数の単一化が行の不一致で落ちたときは、newtype の
   フィールドの矢印の規則(書いたとおりに読み、省略は `@ {}` — 仕様 §9)を
   添えます (M26 の B6)。エフェクトつきの閉包を newtype に入れて純粋として
   取り出す形(台帳 V14)はまさにここで落ちるので、この言い換えがいちばん
   効きます。門番は §11.12 と同じ `row_failure` です。 *)

and elab_construct env level node cname ?eff args =
  let ctor = intern cname in
  match Hashtbl.find_opt Decls.ctor_owner ctor with
  | None -> type_error ("未知のコンストラクタ: " ^ cname)
  | Some dname ->
      (* コンストラクタの可視性は所属 newtype の pub に従う(D42) *)
      Decls.check_ctor_visible ctor dname;
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
          List.map (fun (i : var_info) -> (i.vid, Unify.new_class_var ~kind:i.vkind ~classes:i.vcls level)) dd.Decls.dd_params
        in
        List.iteri
          (fun ai (_, e) ->
            let f = List.nth ct.Decls.ct_fields arg_to_field.(ai) in
            let ety =
              match eff with
              | Some eff -> elab_exp env level eff e
              | None -> bug "elab_construct: 引数つきなのに eff がない"
            in
            let fty = Unify.subst_params level subst f.Decls.fi_ty in
            (* V14 の形(エフェクトつきの閉包を newtype に入れる)はここで落ちる
               ので、行由来の失敗だけ §9 の規則で言い換える(M26 の B6) *)
            try Unify.unify ety fty
            with Type_error msg when row_failure msg ->
              type_error
                (msg ^ "(コンストラクタ " ^ cname
               ^ " のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)"))
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
  at_node node @@ fun () ->
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
            elab_check env2 level eexp l_body rexp;
            (* 検査モードのラムダも引数パターンを網羅性検査へ(V10 の
               続き — M19 検証。注釈のある高階関数の引数位置はこちらへ
               流れるので、推論側だけに積むと最も普通のラムダが素通り
               した)。本体の後に積むのは、本体中の let の drain に
               食われて行が早期に閉じないため *)
            List.iter2 (fun p (_, t) -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) l_params fields)
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
   sample.kel 自身が `Console.write`(:407) と `File.write`(:514) を両方
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

   最左とは何か。**行が handle の入れ子から推論で組み立てられる限り**、
   最左は最内ハンドラです — §11.24 が本体の行を
   TRowExtend(label, …, outer) と積むので、内側のハンドラのラベルほど
   左に来ます。Scoped Labels の最左一致とも実行時の最内捕捉とも一致し、
   これがこの規則の正当化です。

   ただし**注釈が行を明示的に書いたときの最左は、書かれた順序**であって
   入れ子順ではありません(M20 / I3 で本文を訂正)。同名の操作を持つ
   E1 / E2 について `@ {E1, E2}` の関数の `perform op` は、E2 のハンドラが
   内側にいても E1 に解決されます(型は test/typecheck_m6.t の
   leftmost.kel、実行との一致は test/eval.t の leftmostrun.kel)。
   なお「推論された行の最左 = 最内」も正確には**その式に至る文の並びが
   handle の入れ子と同順である限り**の話です — 行は本体の推論が触れた順に
   伸びるからです。それでも静的解決と実行時捕捉は食い違いません —
   perform は解決済みの完全名 oid を運ぶので、E2 のハンドラが E1.op を
   捕まえることはない(素通りして E1 のハンドラに届く)からです。
   挙動は健全で、かつて誤っていたのはこの節の説明でした。

   `copy` で `write` が `File.write` になるのは、`with_file` が積んだ `File` が
   `Console` より内側 = 行の左にいるからです。そして人間が読んだときの
   直感 — 直近に開いたファイルに書く — とも一致します。

   規則は **2 段**です (D99)。1 段目: 操作名を宣言しているエフェクトが
   **1 つ**なら、行に現れているかを問わずそれに解決します。候補が 1 つなら
   推測する余地が無く、ここで行を要求すると注釈の無い `let` の中の perform
   (行は新しい変数なので候補は 1 つも現れない)が全部修飾を要求される
   ことになります。2 段目: 候補が **2 つ以上**のときだけ、上の「行の最左」を
   見ます。仕様 §9 は当初 2 段目だけを書いていて、diktor の issue 本文が
   `[ e ]` の近道を数え落としたのが原因でした(2026-09-12 に仕様側を訂正。
   `test/typecheck_m6.t` の onecand / twocand が両段を固定しています)。

   2 段目で行に候補が 1 つも現れないときは諦めて、`File.write` のように
   修飾せよと案内します。推測しません。なお行の**並び**は解決にだけ使い、
   型の等価性には使いません — 順序違いの行は単一化します
   (`test/typecheck_m6.t` の roworder)。 *)

and resolve_perform eff li =
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
          (* 現在の eff 行に明示的に現れる候補のうち、最左を採る。推論された
             行では最左 = 最内ハンドラ。注釈された行では書かれた順(§11.20) *)
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
   確定するので、cancel による自動巻き戻しが成立します (sample.kel:467-470)。
   継続がどこかのクロージャに生き残っている可能性があると、巻き戻しの
   タイミングが決められません。 *)

and check_resume_static ?(in_lambda = false) (((_, e) as node) : T.exp) =
  at_node node @@ fun () ->
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

   **操作節だけは同じ操作に複数書けます**(絞り込みパターンやガードで場合を
   分け、実行時は match と同じフォールスルーで選ぶ。D28)。return / cancel は
   1 つまでです。総和的な節(ガード無し・反駁不可)より後ろに同じ操作の節を
   書くと到達しないので、警告を出します (§11.24)。

   分類結果は `set_resolved` で木に書きます。評価器が節の種別を判定し直さない
   ためです (§11.8 と同じ方針)。 *)

and elab_handle env level eff clauses body =
  let classify ((_, c) as cnode : T.clause) =
    match snd c.T.cl_pat with
    | T.PVar "cancel" -> `Cancel cnode
    | T.PCtor (LongId comps, args) -> (
        match List.rev comps with
        | "cancel" :: _ ->
            if args <> [] then noimpl "cancel(reason)(v0 は case cancel のみ)" else `Cancel cnode
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
   あっても、`read` と `write` の両方を書けば `File` に決まります。
   `write` 節だけを書いた handle は、かつては `Console` に決まりました —
   `Console` の全操作は `write` 1 つで、覆えている候補が `Console` だけに
   なるからです。M20 (I4 / D63) からプレリュード所有の `Console` / `Async` は
   ハンドル禁止で候補からも外れるため、この形は「File の read が漏れて
   います」に落ちます — File のつもりの取り違えがそのまま診断になります。
   `Fs` は M27 で同じ名簿に入りました (D88) が、操作を持たないので候補には
   そもそも現れず、修飾して名指ししたときだけ禁止の診断に届きます (D90)。
   `File` を意図していたなら `File.write` と修飾するか、`read` 節も
   書いてください。
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
  (* ランタイム提供エフェクトはハンドルさせない(M20 / I4 / D63)。仕様
     sample.kel:462 が Console / Async / Fs の 3 つを名指しで定めた(Async は
     :641 にも「スケジューラは書かせない」。Console はかつて提案中で、
     2026-09-12 の改訂で明文化)。許すと出力が黙って消える恒等ハンドラが書け、
     File.write のつもりの case write(s) が Console を消す事故も起きる。
     判定はランタイム行に名前があり**かつ**プレリュード所有であること —
     --no-prelude でユーザが自分の effect Console / Fs を宣言した場合は禁止
     しない。修飾節ではこの判定が「操作 X はエフェクト Y に属しません」より
     **先**に走る。Heap / Blocking で禁止が出ないのは名簿に入れていないからで、
     入れると case Blocking.nope() の診断がこちらにすり替わる(第7章 §7.3)。
     Fs は操作を持たないので非修飾では候補に挙がらず、修飾したときだけ
     ここに届く(名簿に入れた理由は D88、文言は D90) *)
  let runtime_provided e = List.mem (name_of e) Prims.runtime_effects && Decls.prelude_owned "effect" e in
  let runtime_msg e =
    match name_of e with
    | "Console" ->
        "エフェクト Console はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:407, :462)。出力先を変えたいときは Print をハンドルしてください(プレリュードの with_stdout が Print を Console へ翻訳します)"
    | "Fs" ->
        "エフェクト Fs はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:408, :462)。ファイル操作を差し替えたいときは File のような自前のエフェクトをハンドルしてください(仕様 sample.kel:524 の with_file が見本)"
    | n -> "エフェクト " ^ n ^ " はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:641。スケジューラは書けません)"
  in
  let target =
    match List.sort_uniq compare quals with
    | [ e ] ->
        (* 修飾されたエフェクトが実在するか検査(未検査だと後段の Option.get で落ちる。検証で発見) *)
        if Decls.find_effect e = None then type_error ("未知のエフェクト: " ^ name_of e)
        else if runtime_provided e then type_error (runtime_msg e)
        else e
    | _ :: _ -> type_error "handle の節の修飾エフェクトが一致しません"
    | [] -> (
        let declares e op = List.mem_assoc op (Option.get (Decls.find_effect e)).Decls.ef_ops in
        let candidates = List.sort_uniq compare (List.concat_map Decls.op_candidates op_names) in
        (* ランタイム提供エフェクトを候補から外す。case write(s) 1 本の
           handle は Console ではなく「File の read が漏れています」に
           落ち、意図の取り違えがそのまま診断になる。候補が全部
           ランタイム提供だったときだけ、その旨を名指しで言う *)
        let all_effects = List.filter (fun e -> not (runtime_provided e)) candidates in
        (if all_effects = [] && candidates <> [] then type_error (runtime_msg (List.hd candidates)));
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
  (* 総和性(D29): 各操作に「ガードが無く全引数パターンが反駁不可」な節が
     1 つ以上要る。実行時の節選択は match と同じフォールスルー(第14章)だが、
     ハンドラの外への後送り(re-perform)は無いので、全節が外れうる形は
     ここで拒否する — 260829-2b 健全性 9 と同じ「実行時に必ず取りこぼしうる
     プログラムを型検査で通さない」方針 *)
  (* 反駁不能判定は §11 冒頭の irrefutable_pat と共用(M19 検証 —
     同じ判定が 2 本あった) *)
  let total (_, _, args, ((_, c) : T.clause)) =
    c.T.cl_guard = None && List.for_all (fun (a : T.ctor_arg_pat) -> irrefutable_pat a.T.cap_pat) args
  in
  List.iter
    (fun (op, _) ->
      if not (List.exists (fun ((o, _, _, _) as cl) -> o = op && total cl) ops) then
        type_error
          ("操作 " ^ name_of op
         ^ " の節が取りこぼします(ガードや絞り込みパターンだけの節は v0 では後送りできません)。変数パターンでガードの無い case "
         ^ name_of op ^ "(...) を最後に置いてください"))
    target_info.Decls.ef_ops;
  (* 到達不能な操作節の警告(B8): 総和的な節より後ろの同一操作の節は
     走らない。この検出は match の useful 判定(第10章)より**弱い** —
     絞り込み節の集まりで網羅済みでも警告は出ない(M19 / V9 の裁定:
     Exhaust への接続は操作節から合成 match ノードを作る必要があり、
     B2 で却下した経緯のとおり見送り。総和性検査が健全性を守っている
     ので、弱いのは警告の網羅性だけ) *)
  let rec dead_scan seen_total = function
    | [] -> ()
    | ((o, _, _, _) as cl) :: rest ->
        if List.mem o seen_total then
          warn ("操作 " ^ name_of o ^ " の節は到達しません(前の節が既に取りこぼしません)");
        dead_scan (if total cl && not (List.mem o seen_total) then o :: seen_total else seen_total) rest
  in
  dead_scan [] ops;
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
   食い違いが出ます。第14章 §14.10 も同じ事実を書いています — かつて
   あちらは「当のハンドラも有効で再入する」と逆のことを書いていて、
   その誤りが仕様 §9 にまで写りました(D100、2026-09-12 に訂正)。

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
   - 操作節のガードは受理しますが、**`resume` 抜き**で推論します。第14章は
     ガードを resume 無しの環境で評価するので、ここで resume を許すと
     「型は付くのに実行時に落ちる」ことになります(§11.21 の構文検査は
     本体しか歩かないため、ガードが唯一の抜け道でした)。
   - 操作節には**総和性検査**があります(D29。上の網羅検査の直後)。各操作に
     「ガードが無く全引数パターンが反駁不可」な節が 1 つ以上要ります。
     実行時の節選択はフォールスルーですが後送り(re-perform)は無いので、
     全節が外れうる形はここで拒否します。総和的な節より後ろの同じ操作の
     節には到達不能警告を出します(--strict-exhaustive でエラー化)。

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
      Unify.unify (elab_exp env2 level eff c.T.cl_body) tres;
      (* return 節の反駁可能パターンも網羅性検査へ(M19 / V10)。本体の
         **後**に積む — 先に積むと節本体中の let の drain に食われて行が
         早期に閉じる(M19 検証で実測) *)
      if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] body_ty
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
      (* ガードは resume 無しで推論する。第14章はガードを resume = None で
         評価するので、ここで Some にすると「型は付くのに実行時に落ちる」
         迂回路になる(敵対的検証で実測。§11.21 の静的検査も本体しか
         歩かないため、ガードが唯一の抜け道だった) *)
      (match c.T.cl_guard with
      | Some g -> Unify.unify (elab_exp { env2 with resume_ty = None } level eff g) t_boolean
      | None -> ());
      (* 操作節では resume が使える。本体は外側の eff で推論(MiniLang:1499) *)
      let env2 = { env2 with resume_ty = Some (op_ret, tres) } in
      check_resume_static c.T.cl_body;
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
      (* 予約述語は制約にも書けない(D8 の 3 つ目の入口)。書けると
         [A: Integral] の A が既定化の対象に見え、数値リテラルが解決
         されないまま実行に到達する(敵対的検証で実測) *)
      if Decls.reserved_predicate c then
        type_error (show_long_id li ^ " は予約されたリテラル述語です(制約には書けません、D8)");
      c)
    tp.tp_classes

and make_rigids ?kinds level tparams =
  (* kinds は型エイリアスの表のセル(al_kinds、D84)。長さが合わないときは
     黙って作り直す — 構築点で必ず一致するので、ここは保険 *)
  let kinds =
    match kinds with
    | Some ks when List.length ks = List.length tparams -> ks
    | _ -> List.map (fun (tp : type_param) -> if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var ()) tparams
  in
  List.map2
    (fun tp kind ->
      let classes = class_names_of tp in
      let r = new_rigid_ref ~kind ~classes level in
      (tp.tp_name, TVar r, r))
    tparams kinds

(* ## 11.26 明示的エフェクト注釈の開放

   計画が想定していなかった裁定です (乖離 1)。`@ Print` と書いたら
   ラベル 1 つの**閉じた**行になる、というのが仕様の字義です。ところが
   それでは sample.kel:471 が型付きません。

   ```
   println(msg) handle {
     case print(message) => resume(perform write(message))
   }
   ```

   `println : (String) => Unit @ Print` の本体は `perform print(...)` ですが、
   この handle の下で `println` を呼ぶと、行は `{Print}` ではなく
   `{Print, Console}` である必要があります。閉じたままではハンドラを通せません。

   そこで、**最外の**ラベルの付いた閉じた行の注釈だけを開きます。
   位置で決まる、というのが要点です(仕様 §9、sample.kel:413-438)。

   | 位置と注釈 | 本体の検査で | 公開スキーマで |
   |---|---|---|
   | 最外 `@ Print` / `@ {A, B}` | 尾部に **Rigid** を足して開く(本体の上限) | 尾部を **Generic** にして開く |
   | 最外 `@ {}` | 閉じたまま | 閉じたまま (純粋。両方向に効く) |
   | 最外 `@` 省略(`let`) | 新しい行変数 (もともと開いている) | 一般化される。本体が空に固まっていれば開き直す (D76) |
   | 最外 `@` 省略 (**pub**) | **Rigid の行**(perform を拒む = 純粋) | **Generic** にして開く (D44) |
   | 入れ子の `@ Print` / `@ {A, B}` | 書いたとおり閉じたまま | 開かない |
   | 入れ子の `@` 省略 | `@ {}` と同じ(純粋) | 閉じたまま (D75) |

   4 行目は M16 (H6) の追加です。当時の仕様の字義は「省略 = `@ {}`」で、
   閉じた空行にすると sample.kel 自身が落ちました(`Db.query` が
   `handle_request` から呼べない — 実測)。そこで乖離 1 のこの表を規則に
   昇格し (D23-a / D44)、空の行にも同じ非対称 — 本体には剛く、公開には
   寛く — を適用しました。この読みの下では `pub let f(): Unit`(省略)と
   `pub let f(): Unit @ {}`(明示)が別の型になります。**2026-09-12 の改訂で
   仕様がこの読みを採用しました**(sample.kel:729-732「推論に任せず、本体は
   純粋でなければならず、公開される型は行多相と読む」)。提案が通った形です。
   後ろの 2 行(入れ子)は M26 の追加で、§11.4 の表と同じ規則です。

   既知の制限が 1 つあります(H6 のリスク (b) の実現)。pub の @ 省略の
   本体が、**一般化されていないトップレベル束縛**(パターン束縛や非値の
   束縛)を呼ぶと、その束縛の単相な行変数を Rigid に結ぼうとして落ちます —
   本体が純粋でもです。診断は pub の規則を名指しして元の報告を添えるので、
   直し方(束縛を関数として宣言し直すか、@ を明示する)には辿り着けます。
   なお Rigid の行から `@ {}` の関数を呼ぶことも(通常の行と同じく)
   できません — 行の部分型付けを持たない設計(§11.26 冒頭)の一貫した
   帰結です。

   なぜ本体では Rigid なのか。開くだけなら未定変数でもよさそうですが、それだと
   本体が注釈に書いていないエフェクトを起こしたときに、尾部に勝手に足されて
   通ってしまいます。剛定数なら足せないので、注釈の約束が守られます。
   スコープを出るところで Generic に変えると、呼び出し側は好きな行を尾部に
   継ぎ足せます。

   > 尾部を開くと通しやすくなる。剛くしておくと嘘をつけなくなる。両方要る。

   `@ {}` を閉じたままにしてあるので、「純粋を強制したい」という意図は
   引き続き書けます (sample.kel:433-438)。`@ Print` の意味論(最外なら
   「Print を含む上限」、入れ子なら「正確に Print だけ」)も仕様が同じ箇所で
   明文化しました。

   空の行も開く、ただし書かれた `@ {}` は開かない — これが D76 です。
   `@` を省略した `let` の行は最初は行変数ですが、本体が `@ {}` の関数
   (入れ子の省略 `@` を含む)を呼ぶと単一化で空に固まります。D75 の下では
   これが普通に起き、`count_if` の類が「エフェクトのある文脈から呼べない
   関数」になってしまいます。そこで `reopen_pure_row` が、公開の直前に
   空に固まった最外の行を新しい行変数に組み直します。ガードは 3 つで、
   どれも実測で必要性を確かめました — 値制限(一般化しない束縛の行を開くと
   `run` の剛定数が漏れる経路に乗る)、明示の `@`(`let k: (Int32) => Int32 @ {}` を
   開くと「両方向に効く」約束が破れる — ガードを入れ忘れた版で `k(1)` が
   `@ Console` の文脈から通った)、`pub`(D44 の Rigid 経路が別にあるので、
   開き直しの対象から外す。Rigid の行は空に固まらないのでこのガードが
   発火する形は現状無く、保険である)。頭が型エイリアスの値束縛も開きません —
   展開先の矢印は入れ子(D75)なので、省略は `@ {}`、書かれた `@ {}` は両方向で、
   1c の署名(§11.37)と同じ閉じた行を公開します(M26 の検証で、パス 2 だけが
   開いて宣言順に依存する食い違いが見つかった)。健全性の根拠は、行が空に
   固まったということが本体の起こすエフェクトが無いことの証明だからです
   (`test/annot_rows.t` の val1 / val2 / rec2 / alval)。 *)

and open_explicit_eff lvl eff =
  let fields, tail = row_fields eff in
  match repr tail with
  | TRowEmpty when fields <> [] ->
      let r = new_rigid_ref ~kind:KRow lvl in
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

   注釈付きを一般化条件に入れると、この束縛が一般化され、`run` が作った
   剛定数 `h` が Generic に化けます。結果として、リージョンの中の可変参照を
   外へ持ち出せます。実証済みの反例です (260829-2b の健全性 2。
   `test/verify_fixes.t` の vr)。

   > 注釈は「多相にしてよい」の証明ではない。値であることの証明だけが証明。

   同じ理由で、非値の束縛に型パラメータを書くことも拒否します。それは
   多相化の要求であり、値制限に真っ向から反します。

   > 本体が純粋であることは「行多相にしてよい」の証明である。

   対になる格言です(M26 / D76、§11.26)。前者は型の多相、後者は行の多相で、
   値制限が掛かるのは前者だけ — 行を開き直すのも一般化する束縛に限る
   のは、そのためです。なお上の `Ref[h, T]` の例で「注釈の中で省略された
   `@` は独立な新しい行変数を作る」と書いていたのは M26 より前の読みで、
   いまは入れ子の省略 `@` は `@ {}` です。反例が反例であることは変わりません
   — 注釈があるだけで一般化すると `h` が Generic に化ける点は同じです。

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
   満たしません」に言い換えます。値束縛でも同じことをします — どちらも
   **注釈が書かれているときだけ**のガードつきです (E6。かつて関数束縛側は
   ガード無しで、注釈のない相手に注釈の話をする形が理屈の上では残って
   いました)。単一化を try で包んでエラーを注釈や宣言の側から語り直す箇所は、
   この 2 つのほかに perform の行単一化 (§11.15) とインスタンス本体の包摂
   (§11.38) があり、合わせて 4 箇所です。いずれも包むのは `Unify.unify`
   だけなので、`Type_error_at` を見る義務はありません (D55)。

   ### 網羅性の drain はここ

   遅延キューを流すのは `generalize` の**直前**です (§11.14)。
   パターン束縛 (`let (a, b) = ...`) は単一ケースの match と同じ扱いで、
   単相に束縛し、網羅性のキューに載せます (乖離 7)。この経路には一般化が
   無いので、キューに積んだ直後にそのまま流します。 *)

and elab_binding env level eff ((_, b) as node : T.let_binding) : env =
  at_node node @@ fun () ->
  (* pub の完全注釈検査(H6 / D44)。注釈が無ければ「@ 省略 = 純粋」の
     約束も立てられない — 検査は冒頭、本体を見る前に *)
  (if b.T.lb_pub then check_pub_annots ~params:b.T.lb_params ~ret:b.T.lb_ret);
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
          match b.T.lb_eff with
          | Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e)
          | None when b.T.lb_pub ->
              (* pub の @ 省略 = 純粋(D44 / D23-a)。仕様の字義は @ {} だが、
                 閉じた空行にすると sample.kel 自身が落ちる(Db.query が
                 handle_request から呼べない — 実測)。本体には Rigid を
                 見せて perform を拒み、公開スキーマでは Generic に解放して
                 どんな行の文脈からも呼べるようにする — open_explicit_eff が
                 空でない行にやることを、空の行にもやる形 *)
              let r = new_rigid_ref ~kind:KRow lvl in
              (match !r with Rigid i -> Hashtbl.replace pub_pure_rows i.vid () | _ -> ());
              (TVar r, [ ("", TVar r, r) ])
          | None -> (new_row_var lvl, [])
        in
        extra_rigids := eff_rigids @ !extra_rigids;
        let ret_ty = match b.T.lb_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> new_var lvl in
        let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
        (* 言い換えは注釈が書かれているときだけ(値束縛側と同じガード。E6)。
           lb_ret = None のここで落ちる経路は現状無いが、あれば注釈の話を
           していない相手に注釈の話をすることになる *)
        (try Unify.unify ret_ty body_ty
         with Type_error msg when b.T.lb_ret <> None -> type_error ("注釈された返り値型を満たしません(" ^ msg ^ ")"));
        List.iter2 (fun p t -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) params param_tys;
        TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
    | None ->
        (* 値束縛の注釈の**頭**の矢印は束縛の最外(D116 / P9)。ラベル付きの
           閉じた行を書いたときは関数束縛と同じく、本体には Rigid を足して
           開き、公開スキーマでは Generic にする(§11.26 の表の 1 行目)。
           書かれた @ {} と省略された @ は触らない。読みは
           elab_value_type_outer を通す — D131 のカインド照合を先に掛けてから、
           その結果の型に行の開き方を掛ける *)
        let vty =
          match b.T.lb_ret with
          | None -> new_var lvl
          | Some t -> (
              let ty = elab_value_type_outer env_ty lvl "型注釈" t in
              match (snd t, repr ty) with
              | T.EArrow (_, _, Some _), TArrow (a, r, e) ->
                  let e', eff_rigids = open_explicit_eff lvl e in
                  extra_rigids := eff_rigids @ !extra_rigids;
                  TArrow (a, r, e')
              | T.EArrow (_, _, None), TArrow (a, r, _) when b.T.lb_pub ->
                  (* pub の省略 @ は「本体は純粋、公開は行多相」(D44 / 仕様
                     §13。関数束縛の lb_eff = None と同じ扱い) *)
                  let rr = new_rigid_ref ~kind:KRow lvl in
                  (match !rr with Rigid i -> Hashtbl.replace pub_pure_rows i.vid () | _ -> ());
                  extra_rigids := ("", TVar rr, rr) :: !extra_rigids;
                  TArrow (a, r, TVar rr)
              | _ -> ty)
        in
        (* 値束縛は外側の eff で評価される *)
        let body_ty = elab_exp env_ty lvl eff b.T.lb_body in
        (try Unify.unify vty body_ty
         with Type_error msg when b.T.lb_ret <> None ->
           (* pub の省略 @ の値束縛では、失敗の原因は本体が純粋でないこと
              (D116)。関数束縛(§11.12)と同じ言い換えをここでも置く *)
           if b.T.lb_pub && (not (outer_eff_written b)) && row_failure msg then
             type_error ("pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: " ^ msg ^ ")")
           else type_error ("注釈された型を満たしません(" ^ msg ^ ")"));
        vty
  in
  (* @ 省略の let の行が本体で空に固まったら、公開のときに開き直す
     (D76 / §11.28)。明示の @ と pub(Rigid 経路)は対象外。値束縛は注釈の
     **頭**の矢印リテラルに @ が書かれていないときだけ — let k: (Int32) => Int32 @ {}
     の @ {} を開くと「両方向に効く」という約束が破れる(実測)。頭がエイリアス
     なら展開先は入れ子なので開かない(outer_eff_written) *)
  let fn_ty = if gen && (not (outer_eff_written b)) && not b.T.lb_pub then reopen_pure_row lvl fn_ty else fn_ty in
  Tree.set_ty node fn_ty;
  let rigids = rigids @ !extra_rigids in
  (* 網羅性の遅延キューは generalize の直前に drain する(計画 §7.2) *)
  match snd b.T.lb_name with
  | T.PVar x ->
      List.iter warn (Exhaust.drain ());
      if gen then (
        (* 一般化の直前に曖昧性を見る(M17 / D48)。generalize より前で
           なければならない — 後では Unbound が Generic に変わって判定
           できない *)
        Unify.check_ambiguity ~all:false ~level [ fn_ty ];
        Unify.generalize level fn_ty);
      release_rigids rigids;
      { env with values = SMap.add x fn_ty env.values }
  | T.PWildcard ->
      List.iter warn (Exhaust.drain ());
      if gen then (
        Unify.check_ambiguity ~all:false ~level [ fn_ty ];
        Unify.generalize level fn_ty);
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
  (* pub の @ 省略の Rigid 行は**群で 1 本**を共有する(H6 / D44)。束縛ごとに
     別の Rigid を作ると、相互再帰の呼び出しが 2 本の Rigid を単一化しようと
     して「スコープ付きの型が一致しません: R1 と ς1」で落ちる(M16 検証 —
     pub を外せば通る意味論的に同一の宣言が落ちる退行だった)。群は一緒に
     純粋なので同じ行でよい。解放も群の終わりに 1 度 *)
  let shared_pub_row = ref None in
  let rec_arg_queue = ref [] in
  let pub_pure_row lvl =
    match !shared_pub_row with
    | Some (t, r) -> (t, [ ("", t, r) ])
    | None ->
        let r = new_rigid_ref ~kind:KRow lvl in
        (match !r with Rigid i -> Hashtbl.replace pub_pure_rows i.vid () | _ -> ());
        shared_pub_row := Some (TVar r, r);
        (TVar r, [ ("", TVar r, r) ])
  in
  List.iter2
    (fun ((_, b) as bnode) (_, pre) ->
      at_node bnode @@ fun () ->
      (* pub の完全注釈検査と「@ 省略 = 純粋」は let(§11.28)と同じ規則
         (H6 / D44) *)
      (if b.T.lb_pub then check_pub_annots ~params:b.T.lb_params ~ret:b.T.lb_ret);
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
              | None when b.T.lb_pub ->
                  (* 共有 Rigid は群の終わりに解放するので、束縛ごとの
                     解放リストには入れない *)
                  (fst (pub_pure_row lvl), [])
              | None -> (new_row_var lvl, [])
            in
            extra_rigids := eff_rigids;
            let ret_ty = match b.T.lb_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> new_var lvl in
            let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
            Unify.unify ret_ty body_ty;
            (* 引数パターンの検査エントリは**群の全本体の後**に積む(下)。
               ここで積むと、後続束縛の本体中の let の drain に食われて
               行が早期に閉じ、受理されていたプログラムが型エラーになる
               (M19 検証で実測) *)
            rec_arg_queue := (params, param_tys) :: !rec_arg_queue;
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None ->
            (* 値束縛の注釈の頭の矢印は最外(D116。§11.28 と同じ)。読みは
               D131 のカインド照合を通してから。pub の枝は入れない —
               群が共有の Rigid 行を持つ設計と噛み合わないため(§11.29) *)
            let vty =
              match b.T.lb_ret with
              | None -> new_var lvl
              | Some t -> (
                  let ty = elab_value_type_outer env_ty lvl "型注釈" t in
                  match (snd t, repr ty) with
                  | T.EArrow (_, _, Some _), TArrow (a, r, e) ->
                      let e', eff_rigids = open_explicit_eff lvl e in
                      extra_rigids := eff_rigids @ !extra_rigids;
                      TArrow (a, r, e')
                  | _ -> ty)
            in
            Unify.unify vty (elab_exp env_ty lvl eff b.T.lb_body);
            vty
      in
      Unify.unify pre fn_ty;
      Tree.set_ty bnode fn_ty;
      release_rigids (rigids @ !extra_rigids))
    bs names;
  (match !shared_pub_row with Some (t, r) -> release_rigids [ ("", t, r) ] | None -> ());
  (* @ 省略の let rec も、本体が純粋だと判明したら公開の行を開き直す
     (D76。§11.28 と同じ規則。群のうち @ を書いた束縛と pub は対象外)。
     本体の再帰呼び出しが見ていた pre は古い矢印のまま — 本体は既に {} で
     検査し終えており、単相再帰の具体化が {} だっただけなので食い違わない *)
  let names =
    List.map2
      (fun (((_, b) as bnode) : T.let_binding) (x, t) ->
        if (not (outer_eff_written b)) && not b.T.lb_pub then (
          let t' = reopen_pure_row lvl t in
          if t' != t then Tree.set_ty bnode t';
          (x, t'))
        else (x, t))
      bs names
  in
  List.iter
    (fun (params, param_tys) ->
      List.iter2 (fun p t -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) params param_tys)
    (List.rev !rec_arg_queue);
  List.iter warn (Exhaust.drain ());
  (* 群として一括で曖昧性を見る(M17 / D48)。相互再帰の制約は群の
     どれかの型から到達できればよい *)
  Unify.check_ambiguity ~all:false ~level (List.map snd names);
  List.iter (fun (_, t) -> Unify.generalize level t) names;
  { env with values = List.fold_left (fun m (x, t) -> SMap.add x t m) env.values names }

(* ## 11.30 宣言の入口 — トップレベルで許されるエフェクト

   トップレベルの初期エフェクト行は、ランタイムが提供する**閉じた**行です。
   `{Console, Async, Fs, Blocking}` の 4 つで、名簿は第7章の
   `toplevel_effects` にあります (D88)。それぞれがそこにいる理由は違います。

   - `Console` — 出力の最終目的地。ランタイムが実装を持ち、ユーザは
     ハンドルできません (§11.23)。
   - `Async` — sample.kel:689 の `crunch` が `@ Async` を持ったまま
     トップレベルから呼ばれるからです。`yield_` は型検査を通り、実行時には
     何もしない — この約束をランタイム側の提供エフェクトとして表現しています。
   - `Fs` — ファイルプリミティブ 4 本が `@ Fs` を課す(M27 / D87)ので、
     トップレベルから `__open` を呼べるためにここにいます。操作は持ちません。
   - `Blocking` — 操作を持たないので、残っていても誰も何も起こせません。
     締め出す仕事は `pinned` に任せてよい、というのが仕様 §12 の判断です。
     ハンドル禁止の名簿 (`runtime_effects`) には入りません — 操作が無いので
     禁じる場面が無く、入れると診断が変わります (第7章 §7.3)。

   4 つのうち `--no-prelude` でも行に残るのは `Blocking` だけです。他の 3 つは
   プレリュードが宣言する名前で、所有のガード(下の `toplevel_eff`)は
   ユーザが同名を宣言しても行に載せません — `Fs` は `Console` と同じ側です。
   だから `--no-prelude` の世界では、自前の `effect Fs = {}` と自前の `@ Fs` の
   `extern` を書いてもトップレベルから呼ぶ手段がありません(`test/fs_effect.t`
   の npfs)。`--prelude` で `Fs` を宣言する差し替えなら所有になり、載ります
   (同 withpre)。これは M27 の検証で確かめた非対称で、根は宣言の場所の違い
   (`Blocking` は §6.12 の組み込み登録、`Fs` は第15章)にあります。

   閉じているので、`perform print(...)` をトップレベルに書くと
   「エフェクト Print をここでは実行できません」になります。正しい挙動です。
   Print はユーザが宣言したエフェクトで、ハンドラを書かない限り誰も
   解釈しません。

   初期の値環境は第6章の組み込み表から作ります。 *)

let toplevel_eff () =
  (* ランタイム行に載せるのは名簿 toplevel_effects のうち**プレリュード所有**
     のものだけ(M20 検証)。名前だけで張ると、--no-prelude やプレリュード
     差し替えの世界でユーザが自分の effect Console を宣言したとき、型は
     ユーザの署名・実行はランタイムの実装という食い違いが起きた(実測:
     型検査を通って実行時に落ちる)。所有でなければその名前は行に載らない
     — perform write は
     「ここでは実行できません」で静的に落ちる。
     Blocking がこのガードを通るのは、§6.12 の register_builtins が
     in_prelude を立てた下で add_effect するから(reset でも同じ経路)。
     register_ref_array の呼び出しがその外へ動くと Blocking は黙って
     トップレベル行から落ちる — test/blocking_top.t の btop が観測点 *)
  List.fold_right
    (fun n acc -> if Decls.prelude_owned "effect" (intern n) then TRowExtend (intern n, t_unit, acc) else acc)
    Prims.toplevel_effects TRowEmpty

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

   パラメータのカインドは本体での使われ方から推論します(仕様 §6、M23 / D80)。
   `newtype Callback[E] = Callback(() => Unit @ E)` の `E` は矢印の `@` に
   現れるので行カインドに決まり、使われ方が無ければ `Type` に既定化されます。
   かつてはここを `KStar` 決め打ちにしていて、その理由を「後から推論で決まると
   1a で登録した頭のカインドと食い違うから」と書いていました。食い違うのは
   頭と本体で**別のセル**を作っていたからで、同じセルを共有すれば食い違いません。
   1a が頭にパラメータごとのカインド変数を積み、1b の `register_newtype` が
   それを剥がして `dd_params` の `vkind` に据える — 本体の精緻化がそのセルを
   `same_kind` で張れば頭にも反映されます。プレリュード所有名の再宣言では 1a が
   頭を差し替えないので、剥がすのはプレリュードが決めたカインドになり、
   ユーザ側はそれを引き継ぎます(別セルを作ると `data_match` の照合で
   `KVar` と `KStar` が食い違う)。

   ここで言う「使われ方」は自分の宣言の本体に限らず、**宣言群の中の型の本体
   すべて**が材料です(M29 / D129)。頭と本体がいま見たとおり 1 つのセルを
   共有し、既定化が 1b の後始末まで遅れる(次の段)ことの帰結で、自分の本体では
   `Int32` しか使っていないパラメータでも、同じ宣言群の別の宣言がそれを行として
   使えば行カインドになります(`test/kinds.t` の phantomrow / phantomtype)。
   宣言を 1 つ消すとカインドが変わる、という脆さもここから来ます。

   既定化は宣言ごとではなく、**1b の後始末**で宣言群の全部が終わってから行います
   (D81、§11.39)。`same_kind` は未解決のカインド変数どうしを片方に張るので、
   先に処理した newtype を宣言ごとに既定化すると、まだ本体を読んでいない相手の
   カインドまで `KStar` に固定してしまい、相互参照する newtype が宣言順に
   依存します(`test/kinds.t` の mutual / mutual2)。`register_newtype` を呼ぶ者は
   既定化の責任を負う、と覚えておいてください。

   宣言順に依存する形が 1 つだけ残っていました。行カインドのパラメータへ
   **具体的な行**を前方参照つきで渡す形 — `newtype A[X] = MkA(B[{Print extends X}])`
   を `B` より前に置く形 — です。相手の `B` がまだ 1b を通っていないと
   パラメータのカインドは `KVar` のままなので、§11.3 の読み分けは `{…}` を型と
   して読み、「エフェクトラベルはこの位置(レコード型)では使えません」で落ちて
   いました。行変数を渡す形(`B[X]`)が順序に依存しないのと対照的です —
   こちらは `KVar` のまま読んでも行変数がそのまま返り、あとから `same_kind` で
   張られるからです。M23 で行を渡せるようになったことの代償でした。

   M29 (D132) はこれを**投機**で閉じました。パス 1a の直後に宣言列をもう一度
   なめ、newtype の本体を一度だけ読んでパラメータのカインドを決めてから 1b に
   入ります(`speculate_newtype`、§11.39)。1b に着いたときには `B` のパラメータが
   もう行だと分かっているので、読み分けは `{…}` を行として読みます。
   `test/kinds.t` の fwdrow が両方の宣言順を、fwdrow3 と fwdrowmod / fwdrowmod2 が
   連鎖と module の中を固定しています。投機は宣言順に 1 周するだけですが、連鎖にも
   届きます — `same_kind` はカインドのセルどうしを**張る**ので、連鎖の末端で
   行が決まれば手前まで一度に伝わるからです。

   M28 がこの案を見送ったときの理由は 2 つで、どちらも実測で消えました。
   第一は、newtype の本体が構築子の登録という副作用を持つこと。投機を
   `elab_type` の呼び出しだけに絞れば消えます。`Decls.add_data` も
   `Unify.generalize` も `pub` の完全注釈検査も呼ばないので、残る副作用は
   `elab_type` がカインドのセルに張る単一化だけで、それが投機の目的そのものです。
   第二は、失敗した投機がパラメータのカインドに張りを残すこと。名指しされた形を
   実際に走らせると、`A` の投機は `B[{Print extends X}]` を型として読み、
   `extends` の右が行かレコード型でなければならないので `same_kind` が
   **`X` を `Row` に張ります**。`Type` ではありません。そのあと `BLabel` の枝が
   落ちて投機は診断を捨てるので、失敗した投機がここで残す張りは正しい答えに
   なっています。台帳 V18 はこれで閉じました。

   投機には手当てが 2 つ要ります。どちらも同じ根から出ます — effect の操作の
   登録は 1b なので、**投機の時点ではユーザが宣言したエフェクトラベルが
   すべて未知**です。`() => Unit @ {Log}` のような普通のフィールドが、投機の
   中では「未知のエフェクト: Log」で落ちます。

   1 つ目は、例外をフィールドごとに握り潰すことです。本体全体を 1 つの `try` に
   包むと、フィールドが 1 個落ちただけで同じ newtype の残りのフィールドが読まれず、
   パラメータのカインドが `KVar` のまま 1b に入ります。そこへ別の宣言が `B[{}]` を
   渡すと `elab_con_args` の照合が相手のパラメータを `Type` に張り、`B` 自身が
   「行カインドではない型パラメータです: E」で落ちます — `B` を**先に**宣言して
   いれば投機を入れる前は通っていた形で、M29 の検証が退行として見つけました
   (`test/kinds.t` の specfield / specfield2)。

   2 つ目は、**投機の間だけ**、カインドが未確定のパラメータへ渡した要素なしの
   波括弧 — `{}` と `{extends R}` の 2 形 — を読まずに飛ばすことです。
   1 つのフィールドの中で先にラベルへ当たる形はフィールドごとの `try` では
   救えません。タプルやレコードの要素は右から読むので、
   `MkB((() => Unit @ E, () => Unit @ {Log}))` は右端の `{Log}` で落ちて `E` に
   届かないからです。飛ばす対象をこの 2 形に限るのは、型としても行としても
   読めるのがこれだけだからです — ラベルが 1 つでもあれば型として読むほうが
   失敗し、張りは残りません。飛ばして失うものもありません。1b が相手のカインドの
   決まった状態で同じ字面をもう一度読みます
   (`test/kinds.t` の specinner / specinner2)。

   この 2 つで、台帳 V22 が挙げた主たる形 —
   `newtype A[X] = MkA(B[{}], () => Unit @ X)` を `B` より前に置く形 — も
   通るようになりました(`test/kinds.t` の specunit)。残るのは、**相手の投機が
   そのパラメータのカインドを決められず、かつ型引数が要素なしの波括弧**の
   ときだけです。飛ばすのは投機の間だけなので、相手のカインドが `KVar` のまま
   1b に入ると、そこで `{}` が空レコードとして読むのに**成功**してしまい、
   `elab_con_args` の照合が相手のパラメータを `Type` に張ります
   (`test/kinds.t` の specunit2)。

   型引数にラベルを 1 つでも書けばどちらの順でも通る、とは言えません。投機が
   相手のパラメータに届かない形では、`B[{Log extends X}]` と書いても宣言順に
   依存します(`test/kinds.t` の speclab / speclab2)。ラベルの有無が決めるのは
   失敗した読みが張りを残すかどうかだけで、相手のカインドが決まるかどうかは
   別の話だからです。残りを閉じるには投機の中だけ `elab_con_args` の
   `same_kind` を止める必要があり、投機を「張らない読み」にする設計変更に
   なるので M29 では触っていません(台帳 V22)。

   `newtype T = ???` (`NtHole`) は表現を隠します。コンストラクタを持たない
   不透明なデータ型として登録され、構築も分解もできません。

   フィールド型の精緻化をこの登録時に済ませているので、パス 2 で newtype に
   出会っても何もすることがありません。未知の型を書けばこの時点でエラーです。
   `pub newtype` のフィールドには完全な型注釈を要求します(仕様 §13、M26)。
   入れ子の矢印の `@` 省略の意味は `@ {}` に決まっていますが、公開 API では
   純粋を意図したのか書き忘れたのかを読み手が区別できなければならない、
   というのが仕様の理由で、`let` の `check_pub_annots` と同じ `fully_effected` で
   見ます(`test/pub.t` の pubnt)。sample.kel の `Parser` が `@ {}` を明示している
   のはそのためです。

   フィールドの型のカインドが `Type` であることもここで見ます (D83)。
   見ないと、行カインドのパラメータや EffectRow エイリアスがそのまま値の型に
   なり、構築点まで落ちません — `newtype Bad[E] = Bad(() => Unit @ E, E)` は
   第 1 フィールドで `E` が行に決まり、第 2 フィールドで落ちます。
   判定に `same_kind` を使うのは意図的で、裸のパラメータ 1 個のフィールド
   (`newtype Id[A] = Id(A)`)では `A` のカインドがまだ未解決なので、
   「値の位置に現れた ⇒ `Type`」という推論として働きます
   (`test/kinds.t` の fieldkind)。

   M29 (D131) からは、これは**値の型の位置の一般検査の 1 事例**です。
   照合そのものは §11.3 の `check_value_kind` に移し、ここに残したのは
   名詞句にコンストラクタ名を添える枝だけです。フィールドの最外で
   カインドが合わない形の文面が「コンストラクタ X のフィールドの型の
   カインドが Type ではありません」のまま変わらないのはそのためで、
   どのフィールドかを名指しできるのはこの位置だけです
   (`test/kinds.t` の fieldkind / fieldalias)。

   フィールドの**内側**に包んだ形は、§11.3 の照合が包んだ位置ごとに
   落とします。`newtype Bad2[E] = Bad2((E, Int32), () => Unit @ E)` は
   第 1 フィールドのタプルで `E` が `Type` に決まり、第 2 フィールドの
   `@ E` で落ちます。`newtype Bad3[E] = Bad3(() => Unit @ E, {a: E})` は
   逆順なので、レコードのフィールド `a` の側が「レコードのフィールド a の型の
   カインドが Type ではありません: R1 :: Row」で落ちます。かつてはどちらも
   exit 0 で、行カインドのパラメータを値の型に持つスキーマが宣言表に
   入っていました(台帳 V17 と V20 はこれで閉じました。`test/kinds.t` の
   rowval / rowval2 / rowval3 / hktval)。 *)

(* 1a が頭に積んだカインドのセルをそのまま剥がして、パラメータの型環境を
   作る(D80)。頭と本体で別のセルを作ると、本体で決まったカインドが頭に
   反映されない。プレリュード所有名の再宣言では 1a が頭を差し替えないので、
   ここで剥がすのはプレリュードが決めたカインド — ユーザ側はそれを引き継ぐ
   (別セルを作ると data_match の kind_equiv で KVar と KStar が食い違う)。
   register_newtype と 1a の後の投機(D132)が同じセルを共有するための共通部 *)
let newtype_param_env env (n : T.newtype') =
  let head_kinds =
    let k = Decls.con_kind (intern n.T.nt_name) (List.length n.T.nt_params) in
    let rec peel k n =
      if n = 0 then []
      else match kind_repr k with KArrow (a, r) -> a :: peel r (n - 1) | _ -> List.init n (fun _ -> new_kind_var ())
    in
    peel k (List.length n.T.nt_params)
  in
  let params =
    List.map2
      (fun (tp : type_param) hk ->
        let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else hk in
        let classes = List.map (fun li -> intern (show_long_id li)) tp.tp_classes in
        { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes })
      n.T.nt_params head_kinds
  in
  let types =
    List.fold_left2
      (fun m (tp : type_param) i -> SMap.add tp.tp_name (TVar (ref (Generic i))) m)
      env.types n.T.nt_params params
  in
  (params, { env with types })

(* newtype の本体を 1b より前に一度**投機的に**読み、パラメータのカインドだけを
   決める(D132)。型エイリアスの投機(D84、§11.39)と同じ道具で、違いは
   構築子を登録しないことだけ — 登録も pub の注釈検査も generalize もせず、
   elab_type の副作用であるカインドの張りだけを残す。診断は捨てる(D55 の
   分類 (a) の 4 つだけを捕まえ、Panic は捕まえない)。
   これが要るのは、行カインドのパラメータへ**具体的な行**を前方参照つきで
   渡す形(`newtype A[X] = MkA(B[{Print extends X}])` が `B` より前)で、
   1b が B のパラメータのカインドをまだ知らないと §11.3 の読み分けが
   `{…}` を型として読むからです(台帳 V18、`test/kinds.t` の fwdrow) *)
let speculate_newtype env (n : T.newtype') =
  match n.T.nt_rhs with
  | T.NtHole -> ()
  | T.NtCtors ctors ->
      let _, env' = newtype_param_env env n in
      (* 例外はフィールドごとに握り潰す。effect の操作の登録は 1b なので、
         投機の時点ではユーザ宣言のエフェクトラベルがすべて未知で、
         () => Unit @ {Log} のような普通のフィールドが落ちる。本体全体を
         1 つの try で包むと、そこで後続のフィールドの張りまで失う *)
      let speculate (f : T.field_decl) =
        try ignore (elab_type env' 1 f.T.fd_ty)
        with Type_error _ | Type_error_at _ | NotImplemented _ | NotImplemented_at _ -> ()
      in
      speculating := true;
      Fun.protect
        ~finally:(fun () -> speculating := false)
        (fun () -> List.iter (fun (c : T.ctor_decl) -> List.iter speculate c.T.cd_fields) ctors)

let register_newtype env (n : T.newtype') =
  (* newtype パラメータのカインドは本体での使われ方から推論する(D80)。
     F[_] と書いてあればその場で確定。既定化は 1b の後始末(D81) *)
  let params, env' = newtype_param_env env n in
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
                    (* pub の完全注釈検査(D44 / 仕様 §13)はフィールドの矢印にも及ぶ。
                       省略の意味は @ {} に決まっているが、公開 API では
                       「純粋を意図したのか書き忘れたのか」を読み手が
                       区別できなければならない(sample.kel:729-732。D78) *)
                    (if n.T.nt_pub && not (fully_effected f.T.fd_ty) then
                       type_error "pub な newtype のフィールドには完全な型注釈が必要です(注釈の中の矢印に @ がありません)");
                    let ty = elab_type env' 1 f.T.fd_ty in
                    (* フィールドの型はカインド Type(D83)。値の型の位置の
                       一般検査(D131、§11.3)の 1 事例なので、照合そのものは
                       check_value_kind に任せ、ここは名詞句にコンストラクタ名を
                       添えるだけ。フィールドの**最外**を見る枝はこちらに残す —
                       どのフィールドかを名指しできるのはここだけで、内側に
                       包んだ形は elab_value_type が位置ごとに落とす *)
                    at_node f.T.fd_ty (fun () -> check_value_kind ("コンストラクタ " ^ c.T.cd_name ^ " のフィールドの型") ty);
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

   操作型の引数に現れる矢印は入れ子として読みます(仕様 §9、M26 / D75)。
   `spawn: (() => Unit @ Async) => Unit` の `@ Async` が暗黙に多相化しないのは
   仕様の規則であって実装の都合ではありません(`test/annot_rows.t` の opsig /
   opsig2)。操作型の**頭**の矢印の省略 `@` も `TRowEmpty` になりますが、
   `perform` も `handle` も操作スキーマの行を捨てるので観測されません。

   同一エフェクト内での操作名の重複は拒否します。**別の**エフェクトとの
   重複は許します — それが D22 の前提です (§11.20)。 *)

let register_effect env (e : T.effect') =
  if e.T.ef_params <> [] then type_error "effect 宣言に型パラメータは書けません(sample.kel §9)";
  (* return / cancel は handle 節の分類(§11.22)が名前で横取りするため、
     操作名としては宣言できない(D68)。受理すると、その操作を含む effect は
     修飾しても書きようがなくハンドルできない(敵対的検証 V4 で実測) *)
  List.iter
    (fun (op, _) ->
      if op = "return" || op = "cancel" then
        type_error ("操作名 " ^ op ^ " は予約されています(handle の " ^ op ^ " 節と衝突するため宣言できません)");
      (* 節の分類器(§11.22)が操作節として読むのは英小文字始まりだけ。
         _ 始まりを受理すると、ハンドルできない effect になる(検証の指摘) *)
      if String.length op = 0 || not (op.[0] >= 'a' && op.[0] <= 'z') then
        type_error ("操作名 " ^ op ^ " は英小文字で始めてください(handle の節が操作名として読めません)"))
    e.T.ef_ops;
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
   排除しており (sample.kel:318)、それを受けて型スキーマ用のデータ型も
   制約ストアも持たずに済んでいます。Generic マークだけで多相が表せるのは
   この裁定のおかげです。

   個数だけでなく**カインド**も決まっています。`tp_arity` が 0 なら `KStar`、
   `F[_]` なら `[_] Type`(一般に `tp_arity` 個の `Type` を取って `Type` を
   返す形)で、newtype の束縛子と違ってクラスのパラメータだけは
   `KVar` を経由しません (§1.12)。EffectRow のパラメータが取れないのはこの
   固定の帰結で、理由は §11.34 のキーにあります — インスタンスの選択は
   型構成子のタグ 1 つで決まるので、ラベルの集合でしかない行は選択の鍵に
   なりません。仕様 §8 がこれを定めています (M29 / D125)。
   逃げ道は用意してあります。**メソッドの型パラメータ**のほうは `KVar` を
   作るので行カインドになれ、`val run_[E]: (A, () => Unit @ E) => Unit @ E` は
   通ります。エフェクトで量化したいクラスは、クラスのパラメータではなく
   こちらに行変数を取ります(仕様 §8 の `Functor` の `map` が見本。
   `test/kinds.t` の classrow / classrow2 / classrowok)。これを書かずに
   「クラスのパラメータは `KStar` 固定」とだけ言うと、エフェクト多相な
   クラスが一切書けないという誤読になります。

   メソッドの型は、**クラスパラメータとメソッド固有の型パラメータの両方**を
   Generic 化したスキーマとして表に置きます。`val map[A, B, E]:` のように
   メソッドが自分の型パラメータを持てるので、2 種類を同じスキーマの中で
   Generic にする必要があります。クラスパラメータのほうには `vcls` として
   クラス名が貼ってあり、これが後で「この変数はこのクラスのインスタンスで
   なければならない」という制約になります。メソッドの型パラメータに書かれた
   **制約のクラス名の検証**だけは、ここでは行わずパス 1b の後に回してあります
   (§11.39)。クラスどうしの宣言順に依存させないためです。

   ### 最外の行を開くのは、注釈の頭が矢印リテラルのときだけ

   メソッドの注釈の最外にラベル付きの行を書いたときは、その行を開きます
   (D44 と同じ Rigid → Generic)。仕様 §9 の表が型クラスのメソッドを最外の
   4 種に数えているからで、開かないと `val f: (T) => Int32 @ Console` の
   メソッドがどの文脈からも呼べなくなります。

   開くのは、注釈の**頭が矢印リテラル**のときに限ります (D121 / P27)。
   頭が型エイリアスなら、展開先の矢印は入れ子です (§11.5 の規則 4)。
   入れ子の矢印に書いた行は閉じたまま読むので、ここで開くと
   `type F[A] = (A) => Int32 @ Print` が値束縛では閉じ、クラスメソッドでは
   開く、という二枚舌になります。M30 より前は `elab_type_outer` の**結果**が
   矢印かどうかだけを見ていたので、実際にそうなっていました
   (`test/annot_rows.t` の clsalias3 / clslit が、直した後の読みを固定します)。

   判定は表層の構文 `cv_ty` を見ます。値束縛の `outer_eff_written` (§11.28) と
   同じ規律で、そちらは `lb_ret` を見ます。同じ問いに答える判定が 2 か所に
   分かれているので、どちらかを直すときは両方を見てください。脱糖が変われば
   黙って効かなくなる種類の判定なので、見張り役は cram のほうに置いてあります。

   エイリアスで書いたメソッドは、ラベル付きの行を持つと呼びにくくなります。
   公開される型が閉じた `{Print}` なので、呼び出し側は `@` を省略して行を
   推論させるか (clsalias3ok)、メソッドの型を矢印リテラルで書き直すか (clslit)
   のどちらかになります。値束縛 (alval4) と同じ帰結で、仕様が定めた読みから
   素直に出てきます。

   `Integral` と `Fractional` はユーザ宣言できません。リテラル述語のために
   予約された名前です (D8、§11.2)。どの名前が予約かの表は第6章
   (`Decls.reserved_predicate`) が持ち、ここはそれを引くだけです。
   インスタンス宣言側の入口にも同じ表の検査があります (§6.12)。

   ### スーパークラスは持たない

   クラスパラメータへの制約 `type class Ord[A: Eq]` は拒否します。かつては
   「v1 で入れる」含みの文言で据え置いていましたが、仕様 §8 が 2026-09-12 の
   改訂で**入れない**と確定しました (D98)。理由は仕様の言い回しどおり、
   制約の含意を持たないほうが、署名に書いた制約だけで解決が決まって
   単純だからです。`Ord` は `Eq` を含意しないので、両方が要る場面では
   `[A: Eq + Ord]` と並べて書きます — 診断もそう案内します
   (`test/classes.t` の super / ordeq / ordeq2)。含意が無いことは、
   `[A: Ord]` だけで `==` を使うと「Eq のインスタンスではありません」と
   落ちることで観測できます。

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
   プレリュードに置かないと明言しているので (sample.kel:394-398)、
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
   v1 で「曖昧なら型で絞る」方式に進むなら、この拒否は緩められます。

   この検査の射程は**クラスどうし**の衝突までです。クラスメソッドと同名の
   トップレベル `let` / `extern` との衝突は拒否せず、**先勝ち**で解決します
   — 非修飾名の勝者は「最初にその名前を持った側」。プレリュードの `echo` が
   いる状態でユーザクラスが `echo` メソッドを宣言しても、非修飾の `echo` は
   プレリュードのまま(メソッドは `Cls.echo` と修飾すれば呼べます)。逆に
   クラスの後の同名 `let` は、パス 2 の逐次束縛で let 以降のコードにだけ
   見えます。この規則を選んだのは実行時と一致させるためです — 実行時は
   起動時に置いたメソッドのラッパを later な束縛が**版複製**(§14.13)で
   覆うので、再束縛より前に作られた閉包は元の実体を見続けます。elab が
   後勝ちだと、前方参照する関数だけ型検査と実行が別の実体を選びました
   (260829-5 課題台帳 V1。M15 検証で echo / println / __string_length の
   乗っ取りとして実測し、1b / 1c の先勝ち化で塞いだ形)。 *)

(* v0 の宣言条件(クラスパラメータは引数の頭に現れよ、§11.33)は
   MiniLang の Read のような「返り値からしか決まらない」クラスを閉め出す。
   だから曖昧性検査(D48)のテストは同じ型を持つ普通の多相 let
   — let read_[A: Show](s: String): A = ??? — で代用している *)
let register_class env (c : T.class_decl') =
  let cls = intern c.T.cls_name in
  (if Decls.reserved_predicate cls then
     type_error (c.T.cls_name ^ " は予約されたリテラル述語です(ユーザ宣言不可、D8)"));
  let param =
    match c.T.cls_params with
    | [ p ] -> p
    | _ -> type_error "type class のパラメータは1個です(多パラメータ型クラスは意図的に排除、sample.kel:318)"
  in
  let param_kind = if param.tp_arity > 0 then k_arrow param.tp_arity else KStar in
  (if param.tp_classes <> [] then
     type_error
       "クラスパラメータに制約は書けません(スーパークラスは入れない裁定です。両方が要るときは [A: Eq + Ord] のように並べて書いてください)");
  let pinfo = { vid = new_oid (); vlevel = 0; vkind = param_kind; vcls = [ cls ] } in
  let pvar = TVar (ref (Generic pinfo)) in
  List.iter
    (fun d -> if d <> "structural" then type_error ("未知の導出規則: " ^ d ^ "(v0 は derive structural のみ)"))
    c.T.cls_derives;
  (* derive structural はユーザの新クラスには書けない(sample.kel:340
     「ユーザには書かせない。コヒーレンスを堅持するため、組み込みの
     自動導出のみが与える」)。受理すると elab は任意のクラスで閉じた行に
     構造的導出を認めるのに、実行時の構造的フォールバック(§14.7)は
     Eq.eq 決め打ちなので、型検査を通ったプログラムが必ず実行時に落ちる
     (M15 検証)。プレリュード所有クラスの再宣言(D35)は照合対象なので
     ここでは弾かない — 集合の一致は add_class_decl が見る。
     カインド検査より**先**に置く: 逆順だと、新クラスに「カインドを直せ」
     という直しようのない案内が出る(直すと今度はこちらに当たる — M17 検証) *)
  (if List.mem "structural" c.T.cls_derives && (not !Decls.in_prelude) && not (Hashtbl.mem Decls.classes cls) then
     type_error "derive structural はユーザ宣言のクラスには書けません(構造的な型へのインスタンスは組み込みの自動導出のみが与えます)");
  (* derive structural のカインド検査(M17 / D9)。かつて仕様は TODO
     「Functor のように導出が不可能なクラスをカインドで弾けるか要確認」を
     置いていて、この検査がその回答だった。改訂後の仕様 sample.kel:354-356 は
     TODO を本文に昇格させ「カインドで弾けるので宣言の時点でエラーにする」と
     定めた。構造的導出はレコード・ヴァリアントに配る規則なので
     Type のクラスにしか意味が無い。上の全面拒否があるので、ここが単独で
     効くのは組み込みと同名のクラスの再宣言だけ *)
  (if List.mem "structural" c.T.cls_derives && not (same_kind param_kind KStar) then
     type_error
       ("derive structural は Type のクラスにしか付けられません(" ^ c.T.cls_name ^ " のパラメータは "
      ^ show_kind param_kind ^ " です)"));
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
        let ty = elab_type_outer { env with types } 1 v.T.cv_ty in
        (* 最外のラベル付き行は開く(D44 と同じ Rigid → Generic。仕様 §9 の表は
           型クラスのメソッドも最外に含める — sample.kel:415-421)。M26 の検証
           まで let / extern にしか掛かっておらず、val f: (T) => Int32 @ Console
           のメソッドがどの文脈からも呼べなかった(計画 B0 の表の見落とし)。
           開くのは注釈の頭が**矢印リテラル**のときだけ(D121 / P27)。頭が
           型エイリアスなら、展開先の矢印は入れ子なので書いた行をそのまま
           閉じたまま読む(§11.5 の規則 4)。値束縛の outer_eff_written
           (§11.28)と同じ「構文を見る」判定を、こちらは cv_ty に対して
           行っている — どちらかを直すときは両方を見ること *)
        let ty, eff_rigids =
          match (snd v.T.cv_ty, repr ty) with
          | T.EArrow _, TArrow (a, r, e) ->
              let e', rig = open_explicit_eff 1 e in
              (TArrow (a, r, e'), rig)
          | _ -> (ty, [])
        in
        Unify.generalize 0 ty;
        release_rigids eff_rigids;
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
  (* 同一クラス内の重複メソッドを拒否(register_effect の dup ops と同じ)。
     素通りすると elab の非修飾名解決は最後の宣言で型付け、インスタンス
     本体の照合は最初の宣言を見るので、型検査を通ったプログラムが実行時に
     型・アリティ崩壊する(敵対的検証で実測) *)
  let rec dup = function
    | [] -> ()
    | (m, _) :: rest -> if List.mem_assoc m rest then type_error ("メソッド " ^ m ^ " が二重に宣言されています") else dup rest
  in
  dup methods;
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
      (* 組み込みと同名: 構造照合は第6章の add_class_decl が済ませている
         (D35)。実体は組み込みを使う *)
      prev.Decls.ci_methods

(* ## 11.34 インスタンスの頭 — キーは名前 1 つ、穴は位置

   インスタンスの頭は `Int32` か `List[_]` の形しか受けません。`List[Int32]` の
   ような具体的な頭は書けません。`_` は**位置**です。前提つきインスタンス
   (仕様 §8、M22 / D93) の束縛子は、この位置へ左から順に対応します。

   > 穴は位置であり、束縛子が左から順にそれを埋める。埋まらなかった穴は
   > カインドの矢印として残る。

   同じ `List[_]` が `Functor[List[_]]` では「未適用の `List`」(束縛子 0 個、
   カインド `[_] Type`)を、`type instance[A: Eq] Eq[List[_]]` では「`List[A]`」
   (束縛子 1 個、カインド `Type`)を意味します。頭のカインドは「束縛子の個数
   だけ適用した後」のカインドで、2 つの例はこの 1 つの規則の両端です。
   束縛子の個数は `_` の個数を超えられません。

   `_` の個数そのものは、型構成子のアリティと一致していなければなりません
   (D96)。かつてここを見ておらず、`Functor[List[_, _, _]]` も穴なしの
   `Functor[List]` も受理していました (`holes` は `con_kind` のフォールバック
   引数にしか使われず、表に載っていれば捨てられていた)。

   キーは従来どおり (クラス, 型構成子の頭) の 2 つ組で、**前提はキーに
   入りません**。探索は表引き 1 回のままです。重なり合うインスタンスは
   存在しないので、コヒーレンスは「同じキーを 2 度登録したらエラー」の
   1 行で保証できます (sample.kel:319)。組み込みキーだけは
   1 度目のユーザ宣言が「受理するが採用しない」(乖離 4、§6.9)なので、
   エラーになるのは 2 度目からです — この数え方が第6章の
   `builtin_redecls` 表にあります。

   頭のカインドはクラスパラメータのカインドと一致していなければなりません。
   `Functor` は `[_] Type` のクラスなので、`Functor[Int32]` はここで落ちます。
   束縛子つきなら、束縛子のカインドも頭の構成子がその位置に要求するものと
   一致していなければなりません (D97。`[F[_]: C]` を `List[_]` の穴には
   置けない)。

   行カインドのパラメータを持つ型も、この照合でここに掛かります。M23 (D80) から
   `newtype Callback[E]` の頭のカインドは `EffectRow -> Type` なので、
   `Functor[F[_]]` が要求する `Type -> Type` と合わず、
   `type instance Functor[Callback[_]]` は宣言の時点で落ちます
   (`test/kinds.t` の nofunctor)。仕様 §8 はこれを、`derive structural` を
   Type のクラスに限る規則と並べて、同じカインドの規律から出る帰結として
   書いています (M29 / D126) — 利用者から見えるのは「`Callback` を `Functor` に
   できない」という制限だけなので、それが言語の規則なのか実装の都合なのかは
   仕様の側に書いてないと区別が付きません。 *)

let instance_head (i : T.instance_decl') =
  let cls = intern i.T.ins_class in
  let head =
    match i.T.ins_args with
    | [ h ] -> h
    | _ -> type_error "type instance の型引数は1個です(D11)"
  in
  let con, holes =
    (* 修飾名 M.T も受ける(M16 検証 — 受けないと、外から module の pub 型に
       インスタンスを書く正規の手段が 1 つも無い)。可視性検査も型注釈と
       同じに通す — 通さないと、名前で触れることすら許されない非 pub 型に
       外からインスタンスが付けられ、module 自身のコヒーレンス枠まで
       横取りされる(同検証。型名を oid に落とす経路は全部同じ検査を通る) *)
    match snd head with
    | T.EIdent (LongId comps) -> (Decls.resolve_con (intern (String.concat "." comps)), 0)
    | T.EApply ((_, T.EIdent (LongId comps)), args) ->
        List.iter (fun (a : T.type_exp) -> match snd a with T.EHole -> () | _ -> type_error "インスタンス頭の型引数は _ だけです(List[_] の形)") args;
        (Decls.resolve_con (intern (String.concat "." comps)), List.length args)
    | _ -> type_error "インスタンス頭は 型構成子 か 型構成子[_, ...] の形で書いてください"
  in
  Decls.check_con_visible con;
  (* 頭の _ の個数は構成子のアリティと一致していなければならない(D96)。
     これを見ないと Functor[List[_, _, _]] が通る(改訂前の実測) *)
  let rec kind_arity k = match kind_repr k with KArrow (_, r) -> 1 + kind_arity r | _ -> 0 in
  let arity = kind_arity (Decls.con_kind con holes) in
  if holes <> arity then
    type_error
      ("インスタンス頭 " ^ name_of con ^ " は型引数を " ^ string_of_int arity ^ " 個取りますが、_ が "
     ^ string_of_int holes ^ " 個書かれています");
  (* 前提の束縛子は頭の _ へ左から順に対応する(D93)。余った _ は未適用のまま
     残り、カインドの矢印になる(Functor[List[_]] が束縛子 0 個で通る形) *)
  let np = List.length i.T.ins_tparams in
  if np > holes then
    type_error
      ("インスタンスの型パラメータが " ^ string_of_int np ^ " 個ありますが、頭 " ^ name_of con ^ " の _ は "
     ^ string_of_int holes ^ " 個です");
  (cls, con, holes)

(* ## 11.35 インスタンスの登録 — 網羅と過剰の両方を見る

   パス 1c ではインスタンスの**頭とメソッド名**と、束縛子から組んだ**前提**
   だけを登録し、本体の検査はパス 2 に回します (§11.38)。本体の推論には
   値環境が揃っている必要があるからです。前提は `class_names_of` を通して
   `(引数位置, クラス)` の組にするので、未知クラス・予約述語の拒否が
   束縛子の位置でも無料で効きます (`test/premise.t` の pr8 / pr9)。
   第8章 §8.4 の `TCon` 枝は、この表に値が入って初めて実際の前提で走ります。

   ここで見るのは 2 方向の照合です。宣言していないメソッドを書いていないか
   (過剰)、クラスの全メソッドを書いたか (網羅)。片方だけでは足りません。
   過剰を許すと綴り間違いが黙って無視され、網羅を許さないと実行時に
   メソッドが見つかりません。

   インスタンス本体に書けるのは let と let rec だけです。`Functor[List[_]]` の
   `map` は自分自身を再帰呼び出しするので、let rec が要ります
   (sample.kel:386-389)。 *)

let register_instance (i : T.instance_decl') =
  let cls, con, holes = instance_head i in
  (* 予約述語は頭を見た時点で拒否する。add_instance にも同じ検査があるが、
     そちらは未知構成子・カインド・網羅の検査の後ろなので、頭の書き方
     次第で D8 でない理由が先に出てしまう(検証の指摘) *)
  (if Decls.reserved_predicate cls then
     type_error (i.T.ins_class ^ " は予約されたリテラル述語です(インスタンスは宣言できません、D8)"));
  let ci = match Decls.find_class cls with Some ci -> ci | None -> type_error ("未知のクラス: " ^ i.T.ins_class) in
  if not (Hashtbl.mem Decls.con_kinds con) then type_error ("未知の型構成子: " ^ name_of con);
  (* 頭のカインドは「束縛子の個数だけ適用した後」のカインド(D93)。
     同時に、束縛子のカインドが頭の構成子がその位置に要求するものと
     一致することを見る([F[_]: C] を List[_] の穴に置けない — D97) *)
  let rec head_kind k tps =
    match tps with
    | [] -> k
    | tp :: rest -> (
        match kind_repr k with
        | KArrow (a, r) ->
            let kb = if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var () in
            if not (same_kind a kb) then
              type_error
                ("インスタンスの型パラメータ " ^ tp.tp_name ^ " のカインドが頭 " ^ name_of con ^ " の引数と一致しません");
            head_kind r rest
        | _ -> bug "instance: 束縛子が頭のアリティを超えています(D96 の検査が先に落とすはず)")
  in
  if not (same_kind ci.Decls.ci_param_kind (head_kind (Decls.con_kind con holes) i.T.ins_tparams)) then
    type_error
      ("インスタンス頭 " ^ name_of con ^ " のカインドがクラス " ^ i.T.ins_class ^ " のパラメータと一致しません");
  (* 前提は (引数位置, クラス)。束縛子 i は頭の引数位置 i に対応するので恒等写像。
     class_names_of を通すので未知クラス・予約述語の拒否が束縛子の位置でも効く *)
  let premises =
    List.concat (List.mapi (fun i tp -> List.map (fun c -> (i, c)) (class_names_of tp)) i.T.ins_tparams)
  in
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
  Decls.add_instance ~builtin:false ~methods ~cls ~con premises

(* ## 11.36 前方参照は、頭の矢印に注釈があるときだけ

   パス 1c で登録する「注釈が完全な let の署名」は、前方参照を通すための
   仕掛けです。sample.kel:399 の `user_names` が、後ろで定義される
   `println`(:440) を呼べるのはこれのおかげです。

   問題は「完全」の定義でした。計画は「引数と返り値に型注釈があること」と
   書いていました。それでは穴が空きました — M26 より前の話です。

   かつて省略された `@` は**新しい行変数**を作りました。本体を推論するときは
   その行変数が呼び出し側の `eff` と結ばれて縛られますが、本体を見ずに
   署名だけを作ると、行変数は何にも縛られないまま一般化されます。すると
   その関数は「どんなエフェクトでも起こしてよい」ことになり、
   **宣言順によってエフェクト検査が抜けます** — 前方参照された呼び出しは
   通り、同じ呼び出しを定義の後ろに書くと落ちる。実証済みの穴です
   (260829-2b の健全性 3)。そこで条件を「注釈中の全ての矢印に `@` が明示
   されていること」まで厳しくしていました。

   仕様 §9 の改訂 (M26 / D75) がこの反例を無効にしました。入れ子の省略 `@` は
   `@ {}` に**確定**するので、本体を見なくても署名に決まっていないものが
   ありません。残る自由度は束縛自身の行だけです。そこで条件を緩めます (M26 の B7)。

   > 前方参照シグネチャに使ってよいのは、**注釈の頭の矢印に `@` が
   > 明示されている**ものだけ。関数束縛は自身の `@`(または `pub`)、
   > 値束縛は注釈の頭が矢印ならその `@`。

   `head_effected` がその判定です。`let helper[E](f: () => Unit @ E, g: (Int32) => Int32): Int32 @ {Console extends E}`
   は `g` の `@` が省略されていても署名になります(`test/typecheck_m6.t` の fwdsig。
   M26 より前は「未束縛の変数: helper」で、省略 1 つで宣言順に依存する — §11.36 が
   避けたかった形が逆向きに残っていました)。`fully_effected` は pub の完全注釈検査
   (D44、§11.31)がまだ使います。

   > 本体を見ずに型を信じるなら、その型に決まっていないものがあってはならない。
   > 省略は決まっている。

   もうひとつの規則が**先勝ち**です。署名は「環境にまだ無い名前」しか
   登録しません。同名の let が 2 本あれば 1 本目の署名だけが前方参照に
   使われ、プレリュード束縛やクラスメソッドと同名の let は署名を
   登録しません(その名前の前方参照は既存の実体の型で検査されます)。
   後勝ちにすると、実行時の版複製(§14.13)が前方参照する関数に見せる
   実体 —「最初にその名前を持った側」— と逆になり、同名 let 2 本 +
   前方参照で型検査を通ったプログラムが黙って別の型の値を返しました
   (M15 検証で実測)。 *)

(* ## 11.37 署名の構築 — 失敗したら黙って諦める

   条件を満たした束縛について、本体を見ずに型を組み立てます。型パラメータを
   剛定数にし、注釈を精緻化し、一般化し、解放する。§11.25 の 3 段そのままです。

   関数束縛では引数パターンが全て `PAnnot` (注釈付き) であることも要求します。
   注釈のない引数があれば、その型は本体からしか分かりません。

   例外を握り潰して `None` を返しているのが目を引きますが、これは意図的です。
   このパスの目的は署名を**登録できるものは登録する**ことであり、エラーを
   報告することではありません。ここで落ちる型注釈は、パス 2 で本体を
   推論するときにもう一度精緻化され、そのとき正しい文脈で正しいエラーに
   なります。1c で早まって報告すると、エラーの出る位置が宣言順に依存します。

   握り潰す節には `Type_error_at` も必ず並べます(D55)。位置つきの
   ほうだけ素通りさせると、1c が「黙って諦める」はずの注釈エラーをその場で
   報告してしまい、まさに避けたかった宣言順依存が位置つきで復活します。
   この形の回帰は test/errloc.t の sig.kel が見張っています。 *)

let signature_of_binding env (b : T.let_binding') : ty option =
  let params_annotated =
    match b.T.lb_params with
    | None -> true
    | Some ps -> List.for_all (fun (_, p) -> match p with T.PAnnot _ -> true | _ -> false) ps
  in
  (* 注釈の**頭**の矢印にだけ @ を要求する(仕様 §9 改訂、M26 の B7)。
     健全性 3 の穴は「省略 @ が独立な行変数になり無制約に一般化される」
     ことだったが、入れ子の省略 @ は @ {} に確定した(D75)ので自由度が無い。
     残る自由度は束縛自身の行だけ — 関数束縛は lb_eff(または pub。省略の
     意味が「純粋」に確定する D44 ので署名を作ってよい)、値束縛は注釈の頭が
     矢印ならその @ *)
  let head_effected ((_, te) : T.type_exp) = match te with T.EArrow (_, _, eff) -> eff <> None | _ -> true in
  let full =
    params_annotated && b.T.lb_ret <> None
    && (match b.T.lb_params with
       | Some _ -> b.T.lb_eff <> None || b.T.lb_pub
       | None -> ( match b.T.lb_ret with Some t -> head_effected t || b.T.lb_pub | None -> false))
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
                (fun (_, p) -> match p with T.PAnnot (_, te) -> elab_value_type env_ty lvl "型注釈" te | _ -> assert false)
                ps
            in
            let fn_eff, eff_rigids =
              match b.T.lb_eff with
              | Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e)
              | None ->
                  (* ここに来るのは pub のみ(full の条件)。本体側と同じ
                     Rigid → Generic(D44) *)
                  let r = new_rigid_ref ~kind:KRow lvl in
                  (TVar r, [ ("", TVar r, r) ])
            in
            let ret_ty = match b.T.lb_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> assert false in
            release_rigids eff_rigids;
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None -> (
            (* 1c の署名もパス 2 と同じ読み(D116)。開かないと前方参照の
               有無で値束縛の行の開き方が変わる。読みは D131 の照合を通す *)
            match b.T.lb_ret with
            | Some t -> (
                let ty = elab_value_type_outer env_ty lvl "型注釈" t in
                match (snd t, repr ty) with
                | T.EArrow (_, _, Some _), TArrow (a, r, e) ->
                    let e', eff_rigids = open_explicit_eff lvl e in
                    release_rigids eff_rigids;
                    TArrow (a, r, e')
                | T.EArrow (_, _, None), TArrow (a, r, _) when b.T.lb_pub ->
                    (* pub の省略 @ は公開の側で行多相(D44 / D116)。1c は
                       本体を見ないので Generic を直に置く *)
                    TArrow (a, r, new_row_var lvl)
                | _ -> ty)
            | None -> assert false)
      in
      Unify.generalize 0 ty;
      release_rigids rigids;
      Some ty
    with Type_error _ | Type_error_at _ | NotImplemented _ | NotImplemented_at _ -> None

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

   行だけは第 3 の扱いを受けます (M26 / D77)。表に 1 行足すなら
   「最外の行 | 実装が空なら単一化しない | 純粋ならどの行でも名乗れる」です。
   引数と返り値を先に単一化し、**そのあとで**実装の最外の行を見ます —
   メソッドの引数に `@` を省略した矢印があると、引数の単一化で実装の行が
   `{}` に固まる(D75)ので、順序が意味を持ちます。固まった行は「本体が
   何も起こさない」ことの証明で、空行は行の最小元なので、そこからの一般化は
   嘘になりません。仕様 §9 の「型クラスのメソッドは実装が純粋で、公開される
   型は行多相」を包摂の側で実現する形で、これが無いと `val fmap2[X, Y]:
   (F[X], (X) => Y) => F[Y]` のように引数の矢印の `@` を省略したメソッドが
   「宣言できるのに実装できない」ものになります(`test/classes.t` の clsrow)。
   実装が純粋でなければ従来どおり落ちます(clsimpure)。

   前提つきインスタンス (M22 / D93) では頭型が**部分適用形**になります。
   `type instance[A: Eq] Eq[List[_]]` の頭型は `List[A]` で、`A` は
   `make_rigids` が作る剛定数です。剛定数の `vcls` に前提 `Eq` が載って
   いるのが要点で、これが無いと包摂が本体の推論結果(`Eq` 制約つきの弱変数)
   をこの剛定数へ束縛しようとした瞬間に §8.4 の `Rigid` 枝で落ち、正しい実装が
   「`[A: Eq]` のように制約を書いてください」と拒否されます。**前提を載せる
   先はここ**です。`skolemize` は `Generic` しか写さないので頭の `Rigid` は
   そのまま残り、期待型の側に前提が硬いまま載ります — 上の表に「頭の束縛子」
   の行を足すなら「`Rigid` のまま。前提は宣言の側の要求」です。`expected_of`
   と `subsume` は 1 文字も変えていません。`tapp` の正規化が `F[A]` を
   `List[A]` に畳んでくれるからです。束縛子の名前は本体の型スコープにも
   入るので、メソッドに `xs: List[A]` と注釈を書けます (D94。メソッド自身の
   型パラメータが同名なら内側が勝ちます)。

   本体は普通の `elab_binding` / `elab_rec_bindings` で推論します。だから
   注釈付きのメソッドも let rec のメソッドも同じ経路で通ります
   (sample.kel:386-389)。 *)

let check_instance_bodies env (i : T.instance_decl') =
  let cls, con, _holes = instance_head i in
  let ci = match Decls.find_class cls with Some ci -> ci | None -> bug "instance: class 未登録" in
  (* 前提つきインスタンスの頭型は部分適用形。束縛子を剛定数にして
     vcls に前提を載せる(D93)。束縛子 0 個なら従来どおり TCon (con, [])。
     束縛子の名前は本体の型スコープに入る(D94) *)
  let head_rigids = make_rigids 1 i.T.ins_tparams in
  let head_ty = TCon (con, List.map (fun (_, t, _) -> t) head_rigids) in
  let env = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types head_rigids } in
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
    let inf = Unify.instantiate lvl inferred in
    try
      (* 最外の行だけ最後に見る(仕様 §9 の「型クラスのメソッド = 実装は純粋、
         公開は行多相」— D77)。引数と返り値を先に合わせたあと、実装の行が
         空 = 純粋なら、宣言の行(剛定数)と単一化せずに受理する — 純粋な
         実装はどの行の下からでも呼べるので、公開の行多相を名乗ってよい。
         pub の @ 省略(D44)が Rigid → Generic でやっている非対称を、
         推論された空行に対して行う形。メソッドの引数に @ を省略した
         矢印があると実装の行は必ず {} に固まる(D75)ので、この抜け道が
         無いと宣言できるのに実装できないメソッドが生まれる(実測) *)
      match (repr inf, repr skol) with
      | TArrow (ia, ir, ie), TArrow (sa, sr, se) ->
          Unify.unify ia sa;
          Unify.unify ir sr;
          if repr ie = TRowEmpty then () else Unify.unify ie se
      | _ -> Unify.unify inf skol
    with Type_error msg ->
      type_error ("インスタンスメソッド " ^ mname ^ " がクラス宣言の型を満たしません(" ^ msg ^ ")")
  in
  List.iter
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DLet ((_, b) as bnode) ->
          let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
          let env2 = elab_binding env 0 (new_row_var 0) bnode in
          (* 包摂エラーは当該メソッドの束縛を指す(検証の指摘。宣言先頭だと
             複数メソッドのどれが悪いか位置から読めない) *)
          at_node bnode (fun () -> subsume mname (SMap.find mname env2.values))
      | T.DLetRec bs ->
          let env2 = elab_rec_bindings env 0 (new_row_var 0) bs in
          List.iter
            (fun (((_, b) as bnode) : T.let_binding) ->
              let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
              at_node bnode (fun () -> subsume mname (SMap.find mname env2.values)))
            bs
      | _ -> type_error "インスタンス本体には let だけが書けます")
    i.T.ins_body;
  release_rigids head_rigids

(* ## 11.39 宣言列を 4 回なめる

   章の冒頭に置いた表の実装です。ここで順序の理由をもう一度、コードに即して。

   **1a — エイリアスと newtype の頭。** 型の本体を精緻化するには、その中に
   出てくる全ての型構成子のカインドが引けなければなりません。だから名前と
   カインドだけを先に登録します。プレリュードが持っている名前をユーザが
   再宣言したときは、プレリュード側を残します (乖離 4)。

   **1a の後始末 — newtype の本体の投機。** 1a が終わった直後に、宣言列を
   もう一度なめて newtype の本体を一度**投機的に**精緻化します(M29 / D132)。
   目的はパラメータのカインドを宣言順に依存せず決めることだけで、
   `speculate_newtype` はフィールドの型を `elab_type` に渡すほかは何もしません。
   走っている間だけ `speculating` を立て、§11.3 の読み分けがそれを見て、型としても
   行としても読める字面 — 要素なしの波括弧 — を飛ばします(§11.31 の末尾)。
   下にあるエイリアスの投機(D84)と道具は同じですが、違いが 2 つあります。
   1 つは構築子を登録しないこと — `Decls.add_data` も `Unify.generalize` も
   `pub` の完全注釈検査も呼ばないので、残る副作用は `elab_type` がカインドの
   セルに張る単一化だけです。もう 1 つは走る位置で、エイリアスの投機が 1b の
   **後**に来るのに対し、newtype の投機は 1b の**前**に置きます。1b の読み分けが
   相手のパラメータのカインドを見る以上、間に合わせるにはそれより前でなければ
   ならないからです(§11.31 の末尾)。診断を捨てるのも、捕まえる例外が D55 の
   分類 (a) の 4 つだけなのも、エイリアスの投機と同じです。握り潰す単位だけは
   違って、newtype のほうは**フィールドごと**です — エイリアスは本体が 1 つ
   なので差が出ませんが、newtype で本体全体を 1 つの `try` に包むと、投機の
   時点では必ず未知であるエフェクトラベルを含むフィールドが、後続のフィールドの
   張りまで道連れにします(§11.31 の末尾)。
   このループも `with_decl_module` で包みます。module 内の newtype の
   フィールド型は module の内部型を非修飾で参照するので、包み忘れたパスだけが
   「未知の型」になります(§10 特記の落とし穴)。これを見張るのは
   `test/kinds.t` の fwdrowmod2 — module の中の深さ 2 の連鎖です。fwdrowmod は
   内部型を参照しない `B6` の投機だけで通るので、包みを外しても緑のままでした
   (M29 の検証)。
   投機と既定化は、newtype の投機(1a の後)、1b、エイリアスの投機
   (1b の後始末の 1 周目)、既定化(2 周目)の順に並びます。

   **1b — コンストラクタ・操作・メソッド。** ここで初めて型の本体を書きます。
   1a とその後始末が終わっているので、原則として宣言の順序に依存しません
   (残る例外は §11.31 の末尾 — 投機が届かない形へ要素なしの波括弧を渡したとき)。
   newtype どうしが互いを参照しても、effect が後ろの newtype を使っても通ります。
   クラスのメソッドは、非修飾名 (`map`) と修飾名 (`Functor.map`) の
   **両方**で値環境に登録します (乖離 12)。どちらでも書けるという仕様を、
   環境に 2 つ入れるという最も安い方法で実現しています。
   1b の後始末として、宣言列をもう一度なめる小さなループが 2 つ走ります。
   仕事は 3 つ。クラスメソッド・newtype・型エイリアスの型パラメータ制約に
   未知のクラスが無いかを見ること(1b の中で検査すると、後ろで宣言されるクラスを制約に書いた
   形が落ちてしまうので、クラス表が出揃うのを待つ)、型エイリアスの本体を
   一度**投機的に**精緻化してパラメータのカインドを推論すること(M28 / D84)、
   そして newtype とエイリアスのパラメータのカインドを既定化すること(D81)。
   投機と呼ぶのは、診断を捨てるからです — 本物の検査(未知の型・再帰・
   部分適用)はパス 2 が同じ本体でやり直すので、ここで落としてしまうと
   §11.43 の「最初の 1 つ」がどのエラーになるかが変わります。捕まえる例外は
   D55 の分類 (a) の 4 つだけで、`Panic` は捕まえません。
   既定化が 2 つ目のループに来るのは、宣言ごとに落とすと
   相互参照する newtype の間で早すぎる時点に `KStar` が固定されるからで
   (§11.31)、投機より後に置くのは、newtype のパラメータのカインドがエイリアス
   経由で決まる形(`newtype A[X] = MkA(Cb[X])` と `type Cb[E] = Callback[E]`)で
   投機が届く前に `X` を固定しないためです。表に新しく登録するものは
   ありません — 既定化は表のセルを書き換えるだけです。
   既定化がパス 2 より前に済むので、**値の本体と使用点はカインドの材料に
   なりません**(M29 / D129)。宣言群を読み終えた時点のカインドがそのまま残り、
   `let f[E](x: Ph[E], c: Callback[E])` のような使用点が `Ph` のパラメータを
   後から行に変えることはありません — この形で落ちるのは `let` 自身の `E` の
   ほうで、`Ph[E]` が先に `E` を `Type` に決めます。既定化の直後に、
   行カインドになったパラメータに型クラスの制約が書かれていないかも見ます
   (`check_row_constraints`、M28)。型クラスは Type のクラスなので行には
   要求できず、かつてエイリアスでは全使用点で落ち、newtype では構築点が
   行を見ないので黙って素通りしていました(260829-5 の M17「記録のみ」の 2 件目)。

   **1c — インスタンスの頭と前方参照シグネチャ。** 頭のカインド検査に
   クラス表が要るので 1b の後。署名の登録はここが最後のチャンスです
   (§11.36、§11.37)。

   **2 — 本体。** 宣言順に推論し、束縛ごとに型を印字します。印字の前に
   `default_numerics` を呼ぶのを忘れないこと。述語つきの弱い変数が残った
   まま表示すると、ユーザには意味のない内部の述語が見えます (D8)。

   プレリュードも同じ `process_decls` を通します。違いは `emit` を
   捨てることだけです。 *)

(* コンパニオン型の大域同義語の登録(D43 / sample.kel:746)。平坦化では
   なくパス 1a で行う — プレリュードの宣言表はユーザ平坦化の時点では
   まだ空なので、既存名との照合がここでないと効かない(M16 検証:
   module List { pub newtype List } がプレリュード自身の型検査を壊した) *)
let register_companion tyname =
  match !Decls.current_module with
  | Some m when tyname = m ^ "." ^ m ->
      if
        Hashtbl.mem Decls.con_kinds (intern m)
        || Hashtbl.mem Decls.aliases (intern m)
        || Hashtbl.mem Decls.reserved_type_names (intern m)
      then
        type_error
          ("module " ^ m ^ " のコンパニオン型 " ^ m ^ " は既存の型 " ^ m
         ^ " と同名です(module 内の型とトップレベルの型は同名にできません)")
      else Decls.add_con_synonym (intern m) (intern tyname)
  | _ -> ()

(* 宣言の出身 module を current_module に立てて処理する。4 パスの**全部**を
   包むこと(§10 特記の落とし穴): 1b の newtype フィールド型や 1c の
   signature_of_binding も module 内の型を非修飾で参照するので、包み忘れた
   パスだけ「未知の型」になる。§11.41 の in_prelude と同じ Fun.protect 規律 *)
let with_decl_module node f =
  let saved = !Decls.current_module in
  Decls.current_module := Hashtbl.find_opt Decls.decl_module (Tree.oid_of node);
  Fun.protect ~finally:(fun () -> Decls.current_module := saved) f

(* 行カインドのパラメータに型クラスの制約は書けない(M28。260829-5 の M17
   「記録のみ」の 2 件目)。型クラスは Type のクラスなので、行に要求しても
   満たす手段が無い — かつてエイリアスでは全使用点で「クラス Show は Type の
   クラスですが…」と落ち、newtype では構築点が行を見ないので黙って素通り
   していた。カインドが決まった後(1b の後始末の 2 周目)に宣言の位置で見る *)
let check_row_constraints (tparams : type_param list) (kinds : kind list) =
  if List.length tparams = List.length kinds then
    List.iter2
      (fun (tp : type_param) k ->
        match kind_repr k with
        | KRow when tp.tp_classes <> [] ->
            type_error
              ("型パラメータ " ^ tp.tp_name ^ " は行カインドなので、型クラス "
              ^ String.concat ", " (List.map show_long_id tp.tp_classes)
              ^ " の制約は書けません(型クラスは Type のクラス)")
        | _ -> ())
      tparams kinds

let process_decls env ~emit decls =
  let eff0 = toplevel_eff () in
  (* パス1a: 型エイリアスの登録と newtype の頭(カインド) *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with
      | T.DType t ->
          register_companion t.T.ta_name;
          Decls.add_alias
            {
              Decls.al_name = intern t.T.ta_name;
              al_params = t.T.ta_params;
              (* パラメータのカインドのセル(D84)。F[_] と書いてあればその場で
                 確定、それ以外は 1b の後始末が本体から推論する *)
              al_kinds =
                List.map
                  (fun (tp : type_param) -> if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var ())
                  t.T.ta_params;
              al_kind = t.T.ta_kind;
              al_body = t.T.ta_body;
              al_module = !Decls.current_module;
            }
      | T.DNewtype n ->
          (* 名前空間の主張はここ(宣言順)で行う。add_data は 1b、add_effect
             も 1b なので、種別交差の検出を各 add に任せると 1a の add_alias が
             常に先回りし、後に書かれたエイリアスが先に書かれた newtype を
             「既に宣言されています」と逆向きに咎める(M15 検証の後始末) *)
          Decls.claim_type_name "newtype" (intern n.T.nt_name);
          register_companion n.T.nt_name;
          if not (Decls.prelude_owned "data" (intern n.T.nt_name)) || !Decls.in_prelude then
            (* 頭のカインドはパラメータごとにカインド変数を積む(D80)。1b の
               register_newtype がこのセルを剥がして dd_params の vkind に据える
               ので、本体で決まったカインドがそのまま頭に反映される *)
            Hashtbl.replace Decls.con_kinds (intern n.T.nt_name)
              (List.fold_right
                 (fun (tp : type_param) acc -> KArrow ((if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var ()), acc))
                 n.T.nt_params KStar)
      | T.DEffect e -> Decls.claim_type_name "effect" (intern e.T.ef_name)
      | _ -> ())
    decls;
  (* パス1a の後始末: newtype の本体の投機(D132)。宣言順に依存せずに
     パラメータのカインドを決めるために、登録の前に本体を一度読んで捨てる *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with T.DNewtype n -> speculate_newtype env n | _ -> ())
    decls;
  (* パス1b: newtype のコンストラクタ・effect・type class の登録(相互再帰・前方参照可) *)
  let env =
    List.fold_left
      (fun env ((_, d) as node : T.decl) ->
        at_node node @@ fun () ->
        with_decl_module node @@ fun () ->
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
                (* 非修飾名は先勝ち(既存の束縛は上書きしない)。実行時は
                   register_class_methods のラッパをプレリュードの let / extern の
                   再束縛が版複製で覆うので、非修飾名の勝者は先にいた方 —
                   elab も同じ側を選ばないと、型検査と実行が別の実体を選ぶ
                   (M15 検証で echo / println / __string_length の乗っ取りを実測)。
                   修飾名 Cls.m はクラスの所有なので常に登録する *)
                List.fold_left
                  (fun m (mn, ty) ->
                    let m = SMap.add (c.T.cls_name ^ "." ^ mn) ty m in
                    if SMap.mem mn m then m else SMap.add mn ty m)
                  env.values methods;
            }
        | _ -> env)
      env decls
  in
  (* 1b の後始末: クラスメソッドと newtype の型パラメータ制約に未知の
     クラス・予約述語が無いか。register_class / register_newtype は 1b で
     宣言順に走るので、そこで検査すると後方のクラスを制約に書いた形が
     落ちる。クラス表が出揃ったここで見れば宣言順に依存しない *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with
      | T.DClass c ->
          List.iter (fun (v : T.class_val) -> List.iter (fun tp -> ignore (class_names_of tp)) v.T.cv_tparams) c.T.cls_vals
      | T.DNewtype n -> List.iter (fun tp -> ignore (class_names_of tp)) n.T.nt_params
      (* DType もここで見る。プレリュード所有名の再宣言は add_alias が黙って
         捨てる(乖離 4)ので、パス 2 の make_rigids には AST が届かない —
         AST 側で検査しないと type Unit[A: Bogus] = A が素通りする(検証) *)
      | T.DType t -> (
          List.iter (fun tp -> ignore (class_names_of tp)) t.T.ta_params;
          (* エイリアス本体のカインド推論(D84)。ここで一度**投機的に**本体を
             精緻化し、パラメータのカインドだけを決めて結果は捨てる。パス 2 の
             実在検査より前にやらないと、エイリアスを先に使う宣言があったときに
             カインドが宣言順で変わる。診断は出さない — 本物の検査はパス 2 が
             同じ本体でやり直す(D55 の (a)。捕まえるのは握り潰す節の 4 つだけで、
             Panic は絶対に捕まえない)。本体が途中で落ちる宣言では、落ちた先の
             使われ方が推論に届かず Type に既定化されるが、そのプログラムは
             どのみちパス 2 で同じ箇所が落ちる。プレリュード所有名の再宣言は
             表にプレリュードの本体が残っているので、読むのもそちら *)
          match Hashtbl.find_opt Decls.aliases (intern t.T.ta_name) with
          | None -> ()
          | Some info -> (
              try
                let rigids = make_rigids ~kinds:info.Decls.al_kinds 1 info.Decls.al_params in
                let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
                ignore
                  (match info.Decls.al_kind with
                  | Some "EffectRow" -> elab_eff env_ty 1 info.Decls.al_body
                  | _ -> elab_type env_ty 1 info.Decls.al_body)
              with Type_error _ | Type_error_at _ | NotImplemented _ | NotImplemented_at _ -> ()))
      | _ -> ())
    decls;
  (* 1b の後始末の 2 周目: カインドの既定化。1b が全部終わってから落とす
     (D81)。宣言ごとに落とすと、相互参照する newtype の間でカインド変数が
     早すぎる時点で KStar に固定される(same_kind は未解決どうしを片方に張る)。
     エイリアスの投機(1 周目)より後に置くのは、newtype のパラメータのカインドが
     エイリアス経由で決まる形(newtype A[X] = MkA(Cb[X]) と type Cb[E] = Callback[E])
     で、投機が届く前に X を固定しないため。頭と dd_params の両方を落とすのは
     念のため — セルを共有しているので通常はどちらか一方で足りる *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with
      | T.DNewtype n -> (
          default_kind (Decls.con_kind (intern n.T.nt_name) (List.length n.T.nt_params));
          match Hashtbl.find_opt Decls.datas (intern n.T.nt_name) with
          | Some dd ->
              List.iter (fun (i : var_info) -> default_kind i.vkind) dd.Decls.dd_params;
              check_row_constraints n.T.nt_params (List.map (fun (i : var_info) -> i.vkind) dd.Decls.dd_params)
          | None -> ())
      | T.DType t -> (
          match Hashtbl.find_opt Decls.aliases (intern t.T.ta_name) with
          | Some info ->
              List.iter default_kind info.Decls.al_kinds;
              check_row_constraints t.T.ta_params info.Decls.al_kinds
          | None -> ())
      | _ -> ())
    decls;
  (* パス1c: インスタンス頭の登録と、注釈が完全な let の署名登録 *)
  let env =
    List.fold_left
      (fun env ((_, d) as node : T.decl) ->
        at_node node @@ fun () ->
        with_decl_module node @@ fun () ->
        match d with
        | T.DInstance i ->
            register_instance i;
            env
        | T.DLet (_, b) -> (
            (* 先勝ち: 既に環境にいる名前(先行する 1c 署名・クラスメソッド・
               プレリュード束縛)は上書きしない。実行時の版複製(§14.13)は
               再束縛より前に作られた閉包に古い実体を見せるので、前方参照の
               勝者も「最初にその名前を持った側」— 後勝ちにすると、前方参照
               する関数だけ型検査と実行が別の実体を選ぶ(M15 検証で、同名
               let 2 本 + 前方参照が黙って別の型の値を返す形まで実測) *)
            match (binding_name b, signature_of_binding env b) with
            | Some x, Some ty when not (SMap.mem x env.values) -> { env with values = SMap.add x ty env.values }
            | _ -> env)
        | T.DLetRec bs ->
            List.fold_left
              (fun env ((_, b) : T.let_binding) ->
                match (binding_name b, signature_of_binding env b) with
                | Some x, Some ty when not (SMap.mem x env.values) -> { env with values = SMap.add x ty env.values }
                | _ -> env)
              env bs
        | _ -> env)
      env decls
  in
  (* パス2: 本体の推論(宣言順) *)
  let show_binding env ((_, b) : T.let_binding) =
    match binding_name b with Some x -> emit (Binding (x ^ " : " ^ Show.show (SMap.find x env.values))) | None -> ()
  in
(* ## 11.40 パス 2 の 1 歩 — 宣言ごとに何が起きるか

   `step` は宣言 1 つを処理して新しい環境を返します。宣言の種類ごとの
   仕事は次のとおりです。

   `DLet` / `DLetRec` / `DExp` / `DInstance` では、既定化の直前に宣言終端の
   曖昧性検査 (M17 / D48) を回します — 宣言の型から到達できない制約は
   もう誰にも決められないからです。`DExp` も対象なので、**文の位置に
   捨てられた式の制約も曖昧として落ちます**。seq を let に脱糖する
   MiniLang では値が一般化されて通る形なので、ここは MiniLang より
   厳しくなっています。`DType` / `DNewtype` / `DEffect` / `DClass` /
   `DExtern` では回しません — 宣言の型に相当するものが無く、空の到達
   集合で掃くと偽陽性になります。

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

  let step env ((_, d) as node : T.decl) =
    let wbefore = !warnings_count in
    let env' =
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      let env' =
        match d with
      | T.DType t ->
          (* 実在検査(未知の型・再帰・部分適用)をここで走らせる。結果は捨てる *)
          let info = Hashtbl.find Decls.aliases (intern t.T.ta_name) in
          let lvl = 1 in
          let rigids = make_rigids ~kinds:info.Decls.al_kinds lvl info.Decls.al_params in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          ignore
            (match info.Decls.al_kind with
            | Some "EffectRow" -> elab_eff env_ty lvl info.Decls.al_body
            | _ -> elab_type env_ty lvl info.Decls.al_body);
          release_rigids rigids;
          env
      | T.DLet b ->
          let env' = elab_binding env 0 eff0 b in
          (* 宣言の終端の曖昧性検査(M17 / D48。all=true — 宣言の型から
             到達できない制約は誰にも決められない)。既定化の直前 —
             逆順だと述語つき変数が先に消え、免除の判定が要らなくなる
             代わりに Eq / Show だけが乗った変数の検出が遅れる *)
          Unify.check_ambiguity ~all:true ~level:0 [ Tree.get_ty b ];
          Unify.default_numerics () (* 表示前に述語つき弱変数を既定化する(D8) *);
          show_binding env' b;
          env'
      | T.DLetRec bs ->
          let env' = elab_rec_bindings env 0 eff0 bs in
          Unify.check_ambiguity ~all:true ~level:0 (List.map Tree.get_ty bs);
          Unify.default_numerics ();
          List.iter (show_binding env') bs;
          env'
      | T.DExp e ->
          let t = elab_exp env 0 eff0 e in
          List.iter warn (Exhaust.drain ());
          (* 文の位置の式も検査対象 — 捨てられる値の制約は誰にも決まらない。
             MiniLang(seq を let に脱糖)より厳しくなる点で、本文に明記 *)
          Unify.check_ambiguity ~all:true ~level:0 [ t ];
          Unify.default_numerics ();
          emit (Binding ("_ : " ^ Show.show t));
          env
      | T.DExtern ex ->
          (* extern 宣言は署名のみ(実装は builtin.ml の表)。重複・プレリュード保護 *)
          if ex.T.ex_abi <> "prim" && ex.T.ex_abi <> "C" then
            type_error ("未知の extern リンケージ: " ^ ex.T.ex_abi ^ "(prim か C を指定してください)");
          (* pub の完全注釈検査(H6 / D44)。let 側 §11.28 と同じ規則 *)
          (if ex.T.ex_pub then check_pub_annots ~params:(Some ex.T.ex_params) ~ret:ex.T.ex_ret);
          (* プレリュード保護は実装名(非修飾)、二重宣言検査は修飾名で(H14 と
             その検証の帰結。§6.2) *)
          Decls.add_extern ~prim:ex.T.ex_prim ex.T.ex_name;
          let lvl = 1 in
          let rigids = make_rigids lvl ex.T.ex_tparams in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          let seen = ref [] in
          let param_tys = List.map (fun _ -> new_var lvl) ex.T.ex_params in
          ignore (List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty ex.T.ex_params param_tys);
          let fn_eff, eff_rigids =
            match ex.T.ex_eff with Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e) | None -> (new_row_var lvl, [])
          in
          let ret_ty = match ex.T.ex_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> new_var lvl in
          (* C 既知名は型契約を照合する(第6章 §6.2b)。行は照合しない —
             @ Blocking を付けるかはバインディング作者の判断(sample.kel:711) *)
          (if ex.T.ex_abi = "C" then
             match Decls.c_known_signature ex.T.ex_prim with
             | None -> ()
             | Some (arg_cons, ret_con, rendered) ->
                 let same_con c t = match repr t with TCon (c', []) -> c' = c | _ -> false in
                 let ok =
                   List.length param_tys = List.length arg_cons
                   && List.for_all2 (fun t c -> same_con c t) param_tys arg_cons
                   && same_con ret_con ret_ty
                 in
                 if not ok then
                   type_error ("extern \"C\" の既知名 " ^ ex.T.ex_prim ^ " の型は " ^ rendered ^ " でなければなりません"));
          let ty = TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff) in
          Unify.generalize 0 ty;
          release_rigids (rigids @ eff_rigids);
          emit (Binding (ex.T.ex_name ^ " : " ^ Show.show ty));
          { env with values = SMap.add ex.T.ex_name ty env.values }
      | T.DNewtype _ -> env (* パス1で登録済み。フィールド型の検査も登録時に済んでいる *)
      | T.DEffect _ -> env (* パス1で登録済み *)
      | T.DClass _ -> env (* パス1で登録済み *)
      | T.DInstance i ->
          check_instance_bodies env i;
          (* インスタンス本体にも宣言終端の掃き出しを掛ける(M17 検証 —
             値制限で一般化されない本体 let は all=false 検査(gen ガード)を
             通らず、曖昧な制約が台帳ごと捨てられていた)。到達集合は
             各メソッド束縛の型 *)
          Unify.check_ambiguity ~all:true ~level:0
            (List.concat_map
               (fun ((_, d) : T.decl) ->
                 match d with
                 | T.DLet b -> [ Tree.get_ty b ]
                 | T.DLetRec bs -> List.map Tree.get_ty bs
                 | _ -> [])
               i.T.ins_body);
          env
      | T.DModule _ ->
          (* 平坦化を通っていれば到達しない。来たら不変条件違反 = 処理系の欠陥 *)
          bug "module が平坦化されていません(flatten_modules を先に呼んでください)"
      in
      (* 既定化も宣言の包みの中で走らせる(検証の指摘)。DInstance の本体で
         作られた数値リテラルの述語は、ここで初めて落ちることがある —
         包みの外だと位置なしの型エラーに戻ってしまう *)
      Unify.default_numerics ();
      env'
    in
    (* この宣言で増えた分だけを拾う。warnings は逆順に積んであるので
       先頭 n 個を反転して出す — 全体を数え直す O(総警告数) の走査を
       宣言ごとに繰り返さない(M19 検証) *)
    let fresh = !warnings_count - wbefore in
    let rec take n l = if n = 0 then [] else match l with [] -> [] | x :: tl -> x :: take (n - 1) tl in
    List.iter (fun w -> emit (Warning w)) (List.rev (take fresh !warnings));
    env'
  in
  (* パス 1 で溜まった制約つき変数(インスタンス頭・署名の instantiate)は
     宣言ごとの曖昧性判定に関係しない — 台帳だけを空にしてから畳み込む *)
  Unify.reset ();
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
  warnings_count := 0;
  Unify.reset ();
  Exhaust.reset ();
  Hashtbl.reset pub_pure_rows;
  let out = current_out in
  out := [];
  (* 先頭に積んで最後に反転(末尾 @ 連結は宣言数の二乗になる — 検証で実測) *)
  let emit s = out := s :: !out in
  let env0 = initial_env () in
  Decls.in_prelude := true;
  let env =
    Fun.protect
      ~finally:(fun () -> Decls.in_prelude := false)
      (fun () -> process_decls env0 ~emit:(fun _ -> ()) prelude)
  in
  let _env = process_decls env ~emit decls in
  List.rev !out

(* ## 11.42 module の平坦化 — 改名・スコープつき同義語・可視性台帳

   v0 の module は名前空間ではなく**改名規則**です (D21)。宣言列を精緻化に
   渡す前に平坦化し、以降のパスは module を知りません — ただし M16 からは
   各宣言の**出身 module** が `Decls.decl_module` に記録され、4 パスが
   `with_decl_module` で `current_module` を立てて処理します。走査も改名も
   しないので、束縛子の見落としによる誤改名というクラスのバグは原理的に
   起きません。

   - `newtype` / `type` は `M.名前` に改名して登録し、module スコープの
     同義語 `(M, 非修飾名) → M.名前` を張ります (D43)。大域に張るのは
     **コンパニオン**(module 名と同名の型。sample.kel:746)だけです。
     かつて同義語は大域 1 枚で、`module M { newtype List[A] = … }` と
     書くだけでプレリュード自身の型検査が壊れました(M15 検証)。
   - `let` も `M.名前` に改名し、module スコープの値同義語を張ります
     (D39 / D43)。module 内の相互参照と let rec の自己再帰はフォール
     バック(環境に無かったときだけスコープの同義語を引く)で通ります。
     **module 内の値名がトップレベルの値名と同名になることは禁止**です —
     elab は宣言時点、評価器は呼び出し時点の環境を見るため、同名を許すと
     フォールバックの発火が両者で食い違い、黙って別の実体を選びます
     (M15 検証 V12。禁止が両解決器の一致の前提)。
   - `pub` は可視性台帳(第6章 `value_visibility` / `con_visibility`)へ
     写します。検査は使用点(§11.3 / §11.11 / §11.8)で、境界は module
     だけです (D41)。コンストラクタは所属 newtype の pub に従います (D42)。
   - `instance` はそのまま大域に出します。インスタンスは常に大域可視で、
     import で見え方が変わるものではありません (sample.kel:741)。
   - `extern` は `ex_name` を `M.f` に修飾しますが、**実装名 `ex_prim` は
     元のまま**です (第1章)。実装は処理系側の表にあり、module はその表を
     切り分けません。第6章の登録簿は、プレリュード保護を `ex_prim` で、
     二重宣言検査を修飾名で見ます (§6.2) — 修飾名だけを鍵にすると保護が
     module の中から迂回でき、実装名だけを鍵にすると別々の module が同じ
     C シンボルを包めなくなります (どちらも実測)。

   同義語表は実行時にも要ります。module の中の instance が実行時に
   見つからなかったのは、評価器が同義語表を引いていなかったからでした
   (260829-2b の健全性 6)。**型検査が使う名前解決の経路は、評価器も
   同じものを通らなければなりません。** 評価器側の `current_module` 相当は
   環境の `mod_scope` で、module 生まれの閉包が出身を持ち歩きます(§14.13)。

   入れ子の module と、module 内の effect / class / 式は未対応です。
   受理してから落ちるのではなく、平坦化の時点で報告します — 種別は
   **未実装**(終了コード 4)です。module 内 let のパターン束縛だけは
   「未対応」ではなく仕様上の制限なので型エラー(終了コード 1)にして
   あります。 *)

let flatten_modules (decls : T.decl list) : T.decl list =
  (* トップレベル(module の外)の値名を先に集める。module 内の値名が
     これと同名になるのを禁止するため(D43 の値側。§6.4 の理由 —
     禁止しないと、宣言順と呼び出し時刻の組み合わせで elab と評価器の
     フォールバックの発火が食い違い、黙って別の実体を選ぶ。M15 検証 V12)。
     パターン束縛の束縛子も全部拾う — binding_name(PVar だけ)で集めると
     let (a, b) = … の a がすり抜けて V12 がそのまま再現する(M16 検証) *)
  let toplevel_vals = Hashtbl.create 32 in
  let rec pat_names ((_, p) : T.pat) =
    match p with
    | T.PVar x -> Hashtbl.replace toplevel_vals x ()
    | T.PAnnot (q, _) -> pat_names q
    | T.PRecord (fs, tail) ->
        List.iter (fun (_, q) -> pat_names q) fs;
        Option.iter pat_names tail
    | T.PCtor (_, args) -> List.iter (fun a -> pat_names a.T.cap_pat) args
    | T.PVariant (_, q) -> pat_names q
    | T.PWildcard | T.PBool _ | T.PNumber _ | T.PText _ -> ()
  in
  (* トップレベルの型名と、クラスのメソッド名も集める。コンパニオン型の
     大域同義語が既存の型名を黙って乗っ取る形(M16 検証 — module Foo を
     1 行足すだけで newtype Foo の名目型が破れる)と、module 名がクラス名と
     同じときに修飾名 M.f がクラスメソッドの修飾名と衝突して可視性検査を
     すり抜ける形(同)を、どちらも平坦化の時点で拒否するため *)
  let toplevel_types = Hashtbl.create 16 in
  let class_methods : (string, string list) Hashtbl.t = Hashtbl.create 16 in
  Hashtbl.iter
    (fun cname (ci : Decls.class_info) -> Hashtbl.replace class_methods (Type.name_of cname) (List.map fst ci.Decls.ci_methods))
    Decls.classes;
  List.iter
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DLet (_, b) -> pat_names b.T.lb_name
      | T.DLetRec bs -> List.iter (fun ((_, b) : T.let_binding) -> pat_names b.T.lb_name) bs
      | T.DExtern ex -> Hashtbl.replace toplevel_vals ex.T.ex_name ()
      | T.DNewtype n -> Hashtbl.replace toplevel_types n.T.nt_name ()
      | T.DType t -> Hashtbl.replace toplevel_types t.T.ta_name ()
      | T.DEffect e -> Hashtbl.replace toplevel_types e.T.ef_name ()
      | T.DClass c -> Hashtbl.replace class_methods c.T.cls_name (List.map (fun (v : T.class_val) -> v.T.cv_name) c.T.cls_vals)
      | _ -> ())
    decls;
  List.concat_map
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      match d with
      | T.DModule (_, mname, body) ->
          List.concat_map
            (fun ((bdata, bd) as bnode : T.decl) ->
              at_node bnode @@ fun () ->
              let claim_val x =
                if Hashtbl.mem toplevel_vals x then
                  type_error
                    ("module " ^ mname ^ " の " ^ x ^ " はトップレベルの " ^ x
                   ^ " と同名です(module 内の名前とトップレベル名は同名にできません)")
                else if match Hashtbl.find_opt class_methods mname with Some ms -> List.mem x ms | None -> false then
                  (* 修飾名 M.x が クラス M のメソッド x の修飾名と同綴りに
                     なり、値環境で区別できない(M16 検証 — かつては綴りの
                     一致だけで可視性検査を免除しており、同名クラスを 1 行
                     宣言するだけで任意の非 pub 値が外から呼べた) *)
                  type_error
                    ("module " ^ mname ^ " の " ^ x ^ " は型クラス " ^ mname ^ " のメソッド " ^ x
                   ^ " と修飾名が衝突します(module か メソッドを改名してください)")
                else Decls.(Hashtbl.replace module_val_synonyms (mname, intern x) (intern (mname ^ "." ^ x)));
                Decls.add_val_synonym (intern x) (intern (mname ^ "." ^ x))
              in
              let claim_con name pub =
                let qual = mname ^ "." ^ name in
                Decls.(Hashtbl.replace module_con_synonyms (mname, intern name) (intern qual));
                Decls.add_con_hint (intern name) (intern qual);
                (* コンパニオン(module 名と同名の型)とトップレベル型名の
                   衝突はここで拒否する — 黙って許すと module Foo を 1 行
                   足すだけでトップレベルの型 Foo が乗っ取られ、名目型の
                   抽象が破れる(M16 検証。D22 / D39 が否定した黙った
                   後勝ちの型側再発)。プレリュード名との衝突検査と大域
                   同義語の登録はパス 1a(§11.39)— プレリュードの宣言表は
                   平坦化の時点ではまだ空だから。可視性は pub の写し
                   (D41-D42) *)
                if name = mname && (Hashtbl.mem toplevel_types name || Hashtbl.mem Decls.reserved_type_names (intern name))
                then
                  type_error
                    ("module " ^ mname ^ " のコンパニオン型 " ^ name ^ " は既存の型 " ^ name
                   ^ " と同名です(module 内の型とトップレベルの型は同名にできません)");
                Hashtbl.replace Decls.con_visibility (intern qual) { Decls.vis_module = mname; vis_pub = pub };
                qual
              in
              let record_module (data, d') =
                Hashtbl.replace Decls.decl_module (Tree.oid_of (data, d')) mname;
                (data, d')
              in
              let vis x pub =
                Hashtbl.replace Decls.value_visibility (intern (mname ^ "." ^ x)) { Decls.vis_module = mname; vis_pub = pub }
              in
              match bd with
              | T.DNewtype n ->
                  let qual = claim_con n.T.nt_name n.T.nt_pub in
                  [ record_module (bdata, T.DNewtype { n with T.nt_name = qual }) ]
              | T.DType t ->
                  let qual = claim_con t.T.ta_name t.T.ta_pub in
                  [ record_module (bdata, T.DType { t with T.ta_name = qual }) ]
              | T.DLet ((bd2, b) as _bnode2) -> (
                  match snd b.T.lb_name with
                  | T.PVar x ->
                      claim_val x;
                      vis x b.T.lb_pub;
                      [ record_module (bdata, T.DLet (bd2, { b with T.lb_name = (fst b.T.lb_name, T.PVar (mname ^ "." ^ x)) })) ]
                  | _ -> type_error ("module 内の let はパターン束縛にできません: module " ^ mname))
              | T.DLetRec bs ->
                  [
                    record_module
                      ( bdata,
                        T.DLetRec
                          (List.map
                             (fun ((bd2, b) : T.let_binding) ->
                               match snd b.T.lb_name with
                               | T.PVar x ->
                                   claim_val x;
                                   vis x b.T.lb_pub;
                                   ((bd2, { b with T.lb_name = (fst b.T.lb_name, T.PVar (mname ^ "." ^ x)) }) : T.let_binding)
                               | _ -> type_error "module 内の let rec はパターン束縛にできません")
                             bs) );
                  ]
              | T.DInstance _ -> [ record_module (bdata, bd) ]
              | T.DExtern ex ->
                  claim_val ex.T.ex_name;
                  vis ex.T.ex_name ex.T.ex_pub;
                  [ record_module (bdata, T.DExtern { ex with T.ex_name = mname ^ "." ^ ex.T.ex_name }) ]
              | T.DModule _ -> noimpl "module の入れ子(M10)"
              | T.DEffect _ -> noimpl ("module 内の effect 宣言(M10): module " ^ mname)
              | T.DClass _ -> noimpl ("module 内の type class 宣言(M10): module " ^ mname)
              | T.DExp _ -> noimpl ("module 内の式文(M10): module " ^ mname))
            body
      | _ -> [ node ])
    decls

(* ## 11.43 最初の 1 つで打ち切る

   型エラーは最初の 1 つで打ち切ります。ただし、そこまでに確定した出力行は
   返します。エラー回復を実装していないので、2 つ目以降のエラーは 1 つ目の
   影響を受けた嘘になりがちで、それを並べても読み手の役に立たないからです。
   ここまでの型が見えれば、どこまで通ってどこで止まったかが分かります。

   位置のアンカー規則(D53): 型エラーの位置は「そのエラーを投げた
   **最内**の精緻化ノード」の開始位置です。`at_node` は位置なしの
   `Type_error` にだけ span を貼り、位置つきの `Type_error_at` を素通り
   させる — この 1 本の規則で、外側の包みが内側の位置を上書きしません。
   包んであるのは elab_exp / elab_check / elab_pat / elab_type / elab_eff /
   elab_binding / elab_rec_bindings / check_resume_static、そして
   process_decls の 4 パスと flatten_modules の宣言単位です。宣言単位の
   包みが最後の受けなので、どのエラーにも最低限「その宣言の先頭」が付きます。

   例外を型付きの返り値に変えるのはこの 1 箇所です。受けるのは
   `Type_error` / `Type_error_at`(終了コード 1)と `NotImplemented`
   (終了コード 4、G6)の 2 系統だけ — `Syntax_error` の節はかつてありましたが到達不能でした。
   raise 元は parser.mly に限られ、第16章の `parse_with` が全部
   `Parse_error` に包み直してから型検査に入るからです。防御的に節を足し
   直したくなったら、この段落がその根拠の記録です(E12)。診断は `error`
   レコード(位置・種別語・終了コード・本文)として返し、以降 — 整形と
   印字 — は第16章 (driver.ml) の仕事です。

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

(* 診断 1 本。位置・種別語・終了コード・本文を値で持つ(D54 / G6)。
   表示の整形は第16章の責任。e_loc は E1(位置の配線)が埋める *)
type error = { e_loc : Location.span option; e_word : string; e_exit : int; e_msg : string }

let type_check ?(prelude = []) decls =
  current_out := [];
  try (type_check_decls ~prelude decls, None) with
  | Type_error_at (loc, msg) -> (List.rev !current_out, Some { e_loc = Some loc; e_word = "型エラー"; e_exit = 1; e_msg = msg })
  | Type_error msg -> (List.rev !current_out, Some { e_loc = None; e_word = "型エラー"; e_exit = 1; e_msg = msg })
  (* Syntax_error の節は置かない — raise 元は parser.mly だけで、第16章の
     parse_with が全部 Parse_error に包み直してから型検査に入る。届く例外は
     Type_error(と、未実装の NotImplemented)の 2 系統だけ(E12) *)
  | NotImplemented_at (loc, feat) -> (List.rev !current_out, Some { e_loc = Some loc; e_word = "未実装"; e_exit = 4; e_msg = feat })
  | NotImplemented feat -> (List.rev !current_out, Some { e_loc = None; e_word = "未実装"; e_exit = 4; e_msg = feat })
