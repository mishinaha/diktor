(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第8章 — 単一化

   ここが推論器の心臓部です。第11章 (elab.ml) が構文から読み取る要求は、
   最終的にすべて「この型とこの型を等しくせよ」という 1 つの命令に落ちます。
   その命令を実行するのが本章の `unify` で、周りにあるのは
   その 1 つの命令を安全に実行するための前後処理だけです。

   材料は 2 つしかありません。第1章 (syntax.ml) が用意した型・カインド・行の
   表現と、第6章 (decls.ml) が持つ宣言表・クラス表・インスタンス表です。
   逆に本章が外へ渡すものは、主なものだけでもこれだけあります。

   | 渡すもの | 受け取る章 |
   |---|---|
   | `unify` / `add_class` | 第11章 (elab.ml) の全規則、第10章 (exhaust.ml) の 1 か所 |
   | `generalize` / `default_numerics` / `check_ambiguity` / `reset` | 第11章 — let と宣言の終端 |
   | `instantiate` / `skolemize` | 第11章 — 変数参照と、インスタンス本体の包摂検査 |
   | `subst_params` | 第10章・第11章 — コンストラクタのフィールドの展開 |
   | `rewrite_row` | 第11章 — フィールドアクセスの規則 |
   | `kind_of` / `var_info_of` / `map_generics_with` | 第11章 — 型の小道具 |
   | `is_predicate` / `show_ref` | 第9章 (show.ml) — 制約の印字と循環回避の穴 |

   `bind` も外からは見えますが、実際に呼ぶのは本章の `unify` /
   `generalize` / `default_numerics` だけです。外向けの道具ではないので
   §8.5 で内部手続きとして扱います。第10章が `unify` を使うのは
   構造的ヴァリアントの行を閉じる 1 か所だけで、あとはすべて読むだけです。

   お手本は MiniLang §5 (単一化)、MiniLang §6 (行の単一化 — Scoped Labels)、
   MiniLang §7 (一般化・インスタンス化・skolem 化) です。この 3 節を 1 ファイルに
   まとめたもの、と思って読んでください。ただし Keleut に合わせた差分が
   いくつかあり、それが本章の見どころでもあります。

   | 差分 | 中身 | 由来 |
   |---|---|---|
   | 矢印が 3 要素 | `TArrow` = 引数の閉じた `_item` 行・返り値・エフェクト行 | D5 |
   | カインド変数 | `KVar` があるので比較は必ず `same_kind` | D7 |
   | 予約述語 | `Integral` / `Fractional` が制約集合に相乗りする | D8 |
   | `Rigid` が 2 役 | `run` のリージョン変数と、注釈の skolem 定数 | D6 |
   | 多引数クラス無し | Tier 1 一式を実装しない。型スキーマ用の型も持たない | D11 |
   | レベルは引数 | 可変グローバル `currentLevel` を置かない | R9 |

   最後の 1 行は地味ですが効きます。MiniLang はレベルを可変グローバルに
   持っており、`generalize` と `instantiate` が暗黙にそれを読みます。
   Keleut 版は全部引数で渡すので、宣言をまたいで level が汚れる事故が
   構造的に起きません。そのぶん呼び出し側が level を意識する義務を負います。 *)

open Aux
open Syntax
open Type

(* ## 8.1 カインド計算 — 専用パスを持たない

   MiniLang §5.2 の `kindOf` は 7 行で、これがカインド検査の全部でした。
   型構成子は宣言表からカインドを引き、適用された引数の数だけ矢印を落とす。
   それだけです。カインド専用の走査パスは最後まで登場しません。
   Keleut でも専用のパスはありませんが、分担が 1 つ増えました (M23 / D82)。
   `kind_of` / `drop_arrows` は**結果の**カインドしか見ず、矢印の**定義域**
   — 型引数が宣言のパラメータのカインドと合うか — は精緻化の側が見ます。
   型構成子の適用では宣言表のカインドから (第11章 §11.3 の `elab_con_args`)、
   高階カインドの型変数への適用 `F[A]` では頭のカインドから (M28 / D86)。
   どちらも引数を読んだその場で照合します。

   Keleut では `drop_arrows` に `KVar` のケースが 1 つ増えます。理由は
   第1章 (syntax.ml) の裁定 D7 にあります。Keleut の型パラメータ束縛子は
   `[A]` も `[R]` も `[E]` も字句がまったく同じで、型なのか行なのかは
   **使われた位置**からしか分かりません。`F[_]` のように `[_]` が書いてある
   ときだけ、その場で `KArrow` が確定します。

   したがって「型引数を適用してみたら、その頭のカインドがまだ未知だった」
   という状況がごく普通に起きます。そこで `KVar` に出会ったら、その場で
   `KArrow (新しいカインド変数, 新しいカインド変数)` を張って先へ進みます。
   これが本実装の「カインド推論」の全部です。張った定義域を引数と照合する
   のは、上に書いたとおり精緻化の側の仕事です — `drop_arrows` は左を捨てて
   右だけを返します。未解決のまま残った `KVar` は
   宣言の終わりに `KStar` へ既定化されます (第1章の `default_kind`)。

   `var_info_of` は 4 状態 (`Unbound` / `Generic` / `Rigid` / `Link`) から
   `var_info` を取り出す小道具です。`Link` に当たったらバグ扱いにしています。
   `repr` を通した後の `TVar` は `Link` でない、という不変条件を
   ここで 1 度だけ主張しておくためです。

   > `repr` してから match する。本章の全関数の鉄則です。 *)

let rec drop_arrows k n =
  if n = 0 then k
  else
    match kind_repr k with
    | KArrow (_, r) -> drop_arrows r (n - 1)
    | KVar r ->
        (* 使用位置からカインドを確定させる(D7) *)
        let res = new_kind_var () in
        r.k_link <- Some (KArrow (new_kind_var (), res));
        drop_arrows res (n - 1)
    | KStar | KRow -> type_error "型構成子ではない型に型引数が適用されています"

let var_info_of r = match !r with Unbound i | Generic i | Rigid i -> i | Link _ -> bug "var_info_of: Link"

let rec kind_of t =
  match repr t with
  | TRowEmpty | TRowExtend _ -> KRow
  | TVar r -> (var_info_of r).vkind
  | TCon (n, args) -> drop_arrows (Decls.con_kind n (List.length args)) (List.length args)
  | TApp (f, _) -> drop_arrows (kind_of f) 1
  | TArrow _ | TRecord _ | TVariant _ -> KStar

(* ## 8.2 型を見せる窓を後から開ける

   本章のエラーメッセージは型を印字したがりますが、印字を担う第9章 (show.ml)
   のほうも、制約を印字するときに本章の `is_predicate` を呼びます。
   つまり相互参照です。OCaml のモジュールは循環できないので、
   ここでは `ref` に穴を開けておき、show.ml の末尾が起動時に埋めます。

   埋まる前に呼ばれても `<型>` と出るだけで落ちません。裏を返せば、
   型エラーの本文が `<型>` だらけになったら、それは show.ml の
   トップレベル初期化が走っていない (リンクから外れた) 証拠です。 *)

let show_ref : (ty -> string) ref = ref (fun _ -> "<型>") (* Show が後から差し込む(循環回避) *)

let show t = !show_ref t

let show2_ref : (ty -> ty -> string) ref = ref (fun _ _ -> "<型>")

let show2 a b = !show2_ref a b

(* ## 8.3 occurs check・レベル調整・脱出検査

   型変数 `tv` に型 `t` を代入する前に、`t` を 1 度だけ走査して
   3 つのことを同時に行います。MiniLang §5.1 と同じ 3 点セットです。

   - **occurs check**: `t` の中に `tv` 自身が出てきたら無限型なのでエラー。
   - **レベル調整**: `t` の中の未定変数のレベルを `tv` のレベルまで下げる。
   - **脱出検査**: `t` の中に `tv` より深いレベルの**剛定数**があればエラー。

   レベル調整を忘れると不健全になります。内側の let で作られた深いレベルの
   変数が、外側の浅いレベルの変数と単一化されたなら、それはもう
   「内側だけの持ち物」ではありません。代入は変数の寿命を伸ばすので、
   レベル (= 寿命の上限) は常に min を取ります。

   そして剛定数はレベルを下げられません。剛定数の存在意義そのものが
   「このスコープの外では意味を持たない」という宣言だからです。
   下げてしまえば宣言を破ることになるので、下げる代わりにエラーにします。

   > 柔らかい変数は寿命を縮められる。剛定数は縮められない。

   Keleut では `Rigid` が 2 役を兼ねます (D6)。`run h { ... }` が導入する
   リージョン変数 `h` と、`let f[A](...)` の注釈を検査するときの `A` です。
   役は違っても守りたい性質は同一 — 「与えたスコープの外へ漏らさない」 —
   なので、この 1 ケースが両方をまとめて守ります。MiniLang §17 が
   「同じ形が 3 回出てくる」と書いているのは、この形のことです。

   1. レベルを上げる
   2. 剛定数を作る
   3. 出口で浅いレベルへ漏れていないかを見る

   `Generic` に当たったら `type_error` ではなく `bug` にしている点にも
   意味があります。`Generic` は一般化済みのスキーマの中にしか居ないはずで、
   単一化に流れてきたなら、それは第11章 (elab.ml) が `instantiate` を
   忘れたということ — ユーザの型エラーではなく実装のバグです。 *)

let rec occurs_adjust tv lvl t =
  match repr t with
  | TVar v ->
      if v == tv then type_error "occurs check に失敗しました(無限型が発生します)";
      (match !v with
      | Unbound i -> if i.vlevel > lvl then v := Unbound { i with vlevel = lvl }
      | Rigid i ->
          (* 剛定数はレベルを下げられない。下げる代わりにエラーにする *)
          if i.vlevel > lvl then type_error ("スコープ付きの型 " ^ show (TVar v) ^ " がスコープの外に漏れています")
      | Generic _ -> bug "単一化中に Generic 変数が現れました"
      | Link _ -> ())
  | TCon (_, args) -> List.iter (occurs_adjust tv lvl) args
  | TApp (f, a) ->
      occurs_adjust tv lvl f;
      occurs_adjust tv lvl a
  | TArrow (p, r, e) ->
      occurs_adjust tv lvl p;
      occurs_adjust tv lvl r;
      occurs_adjust tv lvl e
  | TRecord row | TVariant row -> occurs_adjust tv lvl row
  | TRowEmpty -> ()
  | TRowExtend (_, f, rest) ->
      occurs_adjust tv lvl f;
      occurs_adjust tv lvl rest

(* ## 8.4 クラス制約の伝播 — これが型クラスの実装本体

   Keleut の型クラス (D3, D11) は、辞書渡しも修飾型も持ちません。
   制約は**型変数そのものに貼りつく**フィールド (`vcls`) で、
   文脈簡約は単一化の途中で即座に、決定的に終わります。
   `add_class t c` は「型 `t` はクラス `c` のインスタンスでなければならない」
   という要求を `t` の形で場合分けして解消する関数です。

   最初にカインドを見ます。ここで `=` ではなく `same_kind` を使うのが
   Keleut 版の肝で、理由は §8.6 で詳述します。

   | `t` の形 | すること |
   |---|---|
   | `Unbound` | 制約集合に合併する。台帳にも載せる |
   | `Rigid` / `Generic` | 宣言に無い制約はエラー (直しようを案内する) |
   | `TCon` | インスタンス表を引き、前提 (`ii_premises`) を引数へ伝播 (M22 から実際に走る) |
   | `TRecord` / `TVariant` | 構造的導出が有効なら、閉じた行の各フィールドへ |
   | `TApp` | 貼れない。エラー |

   `Generic` の行は M17 (D51) で増えました。宣言スキーマの位置(newtype の
   フィールド型・クラスメソッド型)で制約つきエイリアスを展開すると、
   パラメータの Generic マークに制約の要求が届きます。規則は Rigid と
   同じです — 宣言済みの制約に含まれていれば満たされ、無ければ
   `[A: Show]` と書けと案内します。

   `Rigid` のケースが 2 通りのメッセージに分かれているのは親切ではなく
   必然です。予約述語 `Integral` はユーザが宣言できないクラス (D8) なので、
   `let f[A: Add](x: A) = x + 1` に対して「A は Integral のインスタンスでは
   ありません」と言っても、ユーザには直す手段がありません。
   だから「`0i32` のように接尾辞を付けるか具体型を使ってください」と
   出口を示します。逆に普通のクラスなら `[A: Add]` と書けばよいので、
   そう案内します。エラーメッセージは、直し方が書けないなら書き直すべきです。

   例に `[A: Add]` が付いているのは偶然ではありません。制約を外した
   `let f[A](x: A) = x + 1` では、`+` のスキーマが運ぶ `Add` のほうが
   先に剛定数へ当たり、「型パラメータ ς1 は Add のインスタンスでは
   ありません。[A: Add] のように制約を書いてください」という
   **普通のクラス側**の分岐で落ちます。予約述語の分岐まで来させるには、
   先に `Add` を満たしておく必要があるわけです。注釈経由でよければ
   `let f[A](x: A): A = 1` でも同じ分岐に着きます。

   構造的導出のケース (sample.kel:391-395) は Keleut 固有です。
   `* -> *` のクラスがこの枝に到達し得ないのは、第11章が宣言時に
   カインドで弾いているからです (M17 / D9)。
   `Eq` のようにクラス宣言に `derive structural` が付いていれば、
   レコードやヴァリアントを分解して各フィールドに同じ制約を配ります。
   ただし**行が閉じているときだけ**です。`{x: Int32 extends R}` の `R` に
   何が入るか分からない以上、比較できると約束することはできません。
   点ごとの行制約 `[R: Eq]` を入れれば可能ですが、カインドと制約解決の
   両方に手が入るので採りません — 仕様がそう決めています。

   `TCon` の枝は M22 (前提つきインスタンス、D93) まで一度も実際の前提で
   走っていませんでした — 第6章 §6.9 の器に値が入るのが M22 だからです。
   `Eq[List[_]]` の前提 `A: Eq` は `(0, Eq)` として表に載り、`List[Opaque]` に
   `Eq` を要求すると `Opaque` に `Eq` が伝播して「Opaque は Eq のインスタンスでは
   ありません」で落ちます (`test/premise.t` の pr2 / pr3)。枝の中の
   `if i < List.length args` は到達不能な保険です — 冒頭のカインド照合が
   先に落とすので、前提が位置 `i` を持つなら `args` は必ず `i + 1` 個以上あります。

   `TApp` に制約を貼れないのは、修飾型を持たない設計の正直な代償です。
   Haskell なら `Show (f a)` として解決を遅延できますが、本実装の制約は
   「型変数」か「具体型の頭」にしか貼れません。MiniLang §5.3 と同じ限界で、
   ここを越えたければ制約を持ち回る仕組み一式が必要になります。

   ### 台帳 class_vars

   制約が乗った変数を記録しておきます(MiniLang の `classVars` と同じ)。
   台帳は 2 つの仕事を兼ねます — 予約述語つきの弱変数を宣言の終わりに
   既定値へ落とす掃除 (§8.9 の `default_numerics`) と、型から到達できない
   制約つき変数を報告する曖昧性検査 (§8.9 の `check_ambiguity`、M17 / D48)。
   同じ台帳に両方が乗るのは、どちらも「一般化・宣言の終わりまで
   決まらなかった制約つき変数」を相手にする仕事だからです(既定化は
   掃き出すだけで到達判定をしません — 到達を見るのは曖昧性検査だけ)。
   かつては予約述語つきだけを控えて掃除にしか使わず、曖昧性検査は
   「残っている穴の 1 つ」(第1章 §1.4)でした。 *)

let is_predicate c = c = cls_integral || c = cls_fractional

(* 制約つき変数の台帳(宣言終了時の default_numerics が掃き、
   check_ambiguity が到達不能な制約を報告する) *)
let class_vars : tvar ref list ref = ref []

(* 制約つきの新変数は必ずここで作る — 作った時点で台帳に載せる。D48 の
   「制約つき変数すべてを控える」は作成経路が 1 本でないと嘘になる
   (M17 検証: コンストラクタ具体化の経路 — subst_params と第11章の
   dd_params 直接展開 — が台帳をすり抜け、Empty のようなコンストラクタ
   由来の制約だけ曖昧性検査を素通りしていた) *)
let new_class_var ~kind ~classes level =
  let v = new_var ~kind ~classes level in
  (match v with TVar r when classes <> [] -> class_vars := r :: !class_vars | _ -> ());
  v

let rec add_class t c =
  let ci =
    match Decls.find_class c with Some ci -> ci | None -> type_error ("未知のクラス: " ^ name_of c)
  in
  if not (same_kind ci.ci_param_kind (kind_of t)) then
    type_error
      ("クラス " ^ name_of c ^ " は " ^ show_kind ci.ci_param_kind ^ " のクラスですが、" ^ show t ^ " に要求されました");
  match repr t with
  | TVar v -> (
      match !v with
      | Unbound i ->
          if not (List.mem c i.vcls) then (
            v := Unbound { i with vcls = c :: i.vcls };
            class_vars := v :: !class_vars)
      | Rigid i | Generic i ->
          (* Generic に届くのは宣言スキーマの位置(newtype フィールド・
             クラスメソッド型)で制約つきエイリアスを展開したとき(D51 で
             到達可能になった。M17 検証)。Rigid と同じ規則 — 宣言済みの
             制約に含まれていれば満たされ、無ければ制約を書けと案内する *)
          if not (List.mem c i.vcls) then
            if is_predicate c then
              type_error "型パラメータに数値リテラルは使えません。0i32 のように接尾辞を付けるか具体型を使ってください"
            else
              type_error
                ("型パラメータ " ^ show (TVar v) ^ " は " ^ name_of c ^ " のインスタンスではありません。[A: " ^ name_of c
               ^ "] のように制約を書いてください")
      | _ -> type_error (show t ^ " に " ^ name_of c ^ " 制約を付けられません"))
  | TCon (n, args) -> (
      match Decls.find_instance ~cls:c ~con:n with
      | Some { ii_premises; _ } ->
          List.iter (fun (i, c2) -> if i < List.length args then add_class (List.nth args i) c2) ii_premises
      | None -> type_error (name_of n ^ " は " ^ name_of c ^ " のインスタンスではありません"))
  | (TRecord row | TVariant row) when ci.ci_derive_structural ->
      (* 閉じた行への構造的導出(sample.kel:391-395)。開いた行は不可 *)
      let fields, tail = row_fields row in
      (match repr tail with
      | TRowEmpty -> List.iter (fun (_, f) -> add_class f c) fields
      | _ -> type_error ("行変数を含む型 " ^ show t ^ " に " ^ name_of c ^ " の構造的導出は適用できません(行が閉じていません)"))
  | TApp _ -> type_error ("制約 " ^ name_of c ^ " を " ^ show t ^ " に付けられません(頭が型変数の適用には制約を貼れません)")
  | other -> type_error (show other ^ " は " ^ name_of c ^ " のインスタンスではありません")

(* ## 8.5 代入 — 順序が意味を持つ 4 手

   代入先になれるのは `Unbound` だけです。`Rigid` も `Generic` も `Link` も
   ここには来ません (来たら実装のバグなので `bug`)。手順は 4 つで、
   **この順番でなければ正しく働きません**。

   1. カインドが一致するか (`same_kind`。合わせて `KVar` を解決する)
   2. `occurs_adjust` — occurs check・レベル調整・脱出検査
   3. 貼りついていた制約を代入先へ伝播 (`add_class`)
   4. `Link` を張る

   2 を 4 より先にやる理由がいちばん重要です。`v := Link t` を先に実行すると、
   以降 `repr (TVar v)` は `t` を返すようになり、`t` の中に `v` が
   含まれていても `occurs_adjust` は `v` を見つけられません。
   occurs check が静かに空振りし、無限型がそのまま通ります。

   3 を 4 より先にやるのは同値性の話ではなく、失敗したときの後始末の話です。
   制約の伝播が `type_error` で落ちたとき、まだ `Link` を張っていなければ
   `v` は未定変数のまま残り、型の状態が中途半端になりません。

   `unbound_var` は `repr` を**呼びません**。呼び出し側の `unify` が
   すでに `repr` 済みの型を渡す、という約束の上に成り立っています。 *)

let bind v t =
  match !v with
  | Unbound { vlevel; vkind; vcls; _ } ->
      if not (same_kind vkind (kind_of t)) then
        type_error ("カインドが一致しません: " ^ show (TVar v) ^ " :: " ^ show_kind vkind ^ " と " ^ show t);
      occurs_adjust v vlevel t;
      List.iter (fun c -> add_class t c) vcls;
      v := Link t
  | _ -> bug "束縛できない変数への bind"

let unbound_var t = match t with TVar ({ contents = Unbound _ } as r) -> Some r | _ -> None

(* ## 8.6 行の書き換え — Scoped Labels と最左一致

   採用するのは Daan Leijen の *Extensible Records with Scoped Labels* (2005)
   です。通常の行型システムは「同じラベルを 2 度含んではいけない」という
   lacks 制約 (`ρ \ x`) を課します。正しいのですが、制約を型に持ち回る
   必要があり、実装量が増えます。

   Scoped Labels の発想は逆で、**重複を許す**。その代わり

   - `r.x` は**最も左の** `x` を取り出す
   - `{x = e | 残り}` は無条件で追加できる (前の `x` は隠れる)
   - `r \ x` は最も左の `x` を消し、隠れていた `x` を復活させる

   と定めます。ラベルがレキシカルスコープのように積み重なるわけです。

   Keleut ではこの「最左一致」が 3 つの場所で同じ意味を持ちます。
   レコードでは**手前のフィールドが勝ち**、エフェクト行では
   **最も左のラベルが選ばれ**、`run` の入れ子では**内側のヒープが優先**
   されます。さらに実装記録の乖離 3 — 操作名の非修飾解決 (D22) を
   「行の最左優先」に精密化した件 — も同じ原理です。sample.kel:620 の
   `copy` の中で `write` が File と Console の両方に該当したとき、
   最左を採れば、handle の入れ子から推論で組み立てられた行では最内の
   ハンドラと一致します。ただし注釈で行を明示したときの最左は**書かれた
   順序**で、実行時の入れ子順とは食い違いえます (M20 / I3、第11章 §11.20)。
   それでも健全なのは、perform が解決済みの完全名を運ぶからです。規則を
   1 つ増やしたのではなく、すでにある規則を思い出しただけ、というのが
   良いところです。

   中心が `rewrite_row row label` です。行の中から**最初の** `label` を探し、
   先頭へ持ち上げて `(フィールド型, 残り)` を返します。
   行の末尾が未定の行変数だったときは、その場で
   `TRowExtend (label, 新しい型変数, 新しい行変数)` へ伸ばします。

   ### 罠 1: 挿入する型変数のレベル

   伸ばすときに作る 2 つの変数は、**現在のレベルではなく行変数自身のレベル**
   で作らなければなりません。ここを間違えると、一般化してはいけない変数を
   一般化します。

   これは机上の心配ではなく、Diktor が実際に踏んでいた不健全なバグでした
   (計画 §0.2 の既存バグ 11)。旧実装はフィールド型を直接 splice しており、
   レベル調整の走る経路を通っていませんでした。その結果

   ```
   fn(r) => { r.a; let g = fn() => r.b; ... }
   ```

   相当のコードで `g : () => A` (すべての `A` について、の意味の A) が付き、
   引数のフィールドから任意の型が取り出せてしまうことを実機で確認しています。
   行変数を経由しない単一化経路 (`unify` から `bind` へ直行する道) は
   正しかったので、**行の再書き換え経路だけが穴**でした。
   現在の形では挿入したフィールドは必ず新変数を経由し、呼び出し側の
   `unify` から `bind` に入るので、レベル調整が確実に走ります。

   ### 罠 2: 行変数のカインドを構造で見てはいけない

   もう 1 つ、こちらは敵対的検証 (260829-2b) で見つかった実バグです。
   旧コードは行変数かどうかを `vkind = KRow` の**構造マッチ**で判定して
   いました。ところが第11章 (elab.ml) の `make_rigids` は、arity 0 の
   型パラメータ — `let fst[A, R](...)` の `R` のような束縛子 — に
   `new_kind_var ()` を渡します (D7)。この `R` が行位置で使われると、
   カインドは `KStar` でも `KRow` でもなく `KVar` のまま、
   リンク先が `KRow` という状態になります。構造マッチはこれを取りこぼします。

   実害は仕様の中心部に出ました。sample.kel:195 の
   `fst(t: {_item: A extends R})` にレコード `{x = 1, _item = ...}` を
   渡す例 (:201-203) と、:209-215 の `describe(#Other)` — つまり
   「行多相レコード」と「構造的ヴァリアントの残りの行」の両方が
   型エラーで落ちていました。第1章 (syntax.ml) が
   「`KVar` は宣言終了時に `KStar` へ既定化する」と決めた以上、
   既定化までカインドは確定していません。ならば結論は 1 つです。

   > カインドは構造で比べない。`same_kind` で比べる。

   `same_kind` は比較しながら `KVar` を相手に張る (単一化する) ので、
   ここを通した瞬間に `R :: Row` が確定するというおまけも付きます。 *)

(* 最左の label を先頭へ持ち上げ、(フィールド型, 残り) を返す。
   新変数は行変数自身のレベルで作る(MiniLang:805-808 / 既存バグ 0.2-11 の修正形) *)
let rec rewrite_row row label =
  match repr row with
  | TRowEmpty -> type_error ("ラベル " ^ name_of label ^ " がありません(行は閉じています)")
  | TRowExtend (l, f, rest) when l = label -> (f, rest)
  | TRowExtend (l, f, rest) ->
      let f2, rest2 = rewrite_row rest label in
      (f2, TRowExtend (l, f, rest2))
  | TVar v -> (
      match !v with
      (* カインドは構造マッチでなく same_kind で見る。[R] のような arity 0 の
         型パラメータは new_kind_var() を貰い、行位置で使われると KVar{→KRow} に
         なるため、KRow の構造マッチだと取りこぼす(検証で実証) *)
      | Unbound { vlevel; vkind; _ } when same_kind vkind KRow ->
          let f2 = new_var vlevel in
          let rest2 = new_row_var vlevel in
          v := Link (TRowExtend (label, f2, rest2));
          (f2, rest2)
      | Rigid { vkind; _ } when same_kind vkind KRow ->
          (* 注釈で固定された行にラベルを追加することはできない — 高階の
             エフェクト注釈を書き間違えたとき最初に出る診断なので、
             「行型ではありません: ς1」ではなく原因を語る(M20 / I9。
             §8.8 の Heap の言い換え細工と同じ発想) *)
          type_error
            ("行 " ^ show (TVar v) ^ " は注釈で固定された行変数なので、ラベル " ^ name_of label
           ^ " を足せません(注釈側に " ^ name_of label ^ " を(必要なら引数つきで)書き足してください)")
      | _ -> type_error ("行型ではありません: " ^ show (TVar v)))
  | t -> type_error ("行型ではありません: " ^ show t)

(* ## 8.7 単一化の本体

   前置きが長かったぶん、本体は素直な構造的単一化です。
   まず両辺を `repr` し、同じものなら何もしない。片方が未定変数なら `bind`。
   どちらでもなければ形で分解する。それだけです。

   最初の `same_var` が Keleut 版に固有です。MiniLang の `TVar` は
   オブジェクトなので参照等価 (`eq`) 1 回で済みますが、OCaml の
   `TVar r` はバリアントの箱なので、同じ `ref` を指す別の箱が
   簡単にできます。物理等価は箱ではなく `ref` で見なければなりません。
   ここを箱で見ると、同一変数どうしの単一化が `bind v (TVar v)` に落ち、
   occurs check が自分自身を見つけてエラーになります。

   ### 矢印 (D5)

   `TArrow` は 3 要素すべてを単一化します。引数・返り値に加えて
   **エフェクト行**も、です。関数を呼ぶ側の行と呼ばれる側の行が
   ここで結ばれることで、エフェクトが型に乗ります。
   そして Keleut では引数が「閉じた `_item` 行のレコード」なので、
   arity の不一致は行の単一化から自動的に出ます。
   引数の個数を数える専用のコードは、この推論器のどこにもありません。

   ### 型適用 (高階カインド)

   高階カインドのために足したのは `TApp` の 3 ケースだけです。

   ```
     f a ~ g b        →  f ~ g,  a ~ b
     f a ~ List Int   →  f ~ List,  a ~ Int      (最後の引数を剥がす)
   ```

   これで一階の単一化のまま済むのは、**型レベルλが無い**からです。
   λが書ければ `f := λx. List Int` のような解も候補になり、
   mgu が一意でなくなって主要型を失います。第1章 (syntax.ml) の `tapp` と
   `repr` が「頭が飽和形 `TCon` なら引数に畳む」正規化を保証しているので、
   `TApp` の頭は必ず型変数であり、分解の仕方に選択の余地がありません。
   MiniLang §0 の 2 つの硬い規則 — 型レベルλを入れない、部分適用できる
   型シノニムを入れない — は Keleut でもそのまま生きています。

   ### 最後の 2 ケース

   `(TVar _, _ | _, TVar _)` に落ちてくる `TVar` は必ず `Rigid` です
   (`Unbound` は上の `bind` で処理済み)。ここに専用のメッセージを置くのは、
   これが**リージョンの取り違え**の主要な出口だからです。MiniLang §16-7 の
   入れ子 `runST` — 外側のヒープの参照を内側で読もうとする例 — は、
   直感に反して `occurs_adjust` の脱出検査ではなく**この経路**で落ちます。
   行の中の Rigid どうしの不一致だからです。検証で確認済みで、
   これは仕様どおりの正しい拒否です (実装記録の「バグでないと確認した項目」)。 *)

let rec unify a b =
  let t1 = repr a in
  let t2 = repr b in
  let same_var = match (t1, t2) with TVar r1, TVar r2 -> r1 == r2 | _ -> false in
  if not (t1 == t2 || same_var) then
    match (unbound_var t1, unbound_var t2) with
    | Some v, _ -> bind v t2
    | _, Some v -> bind v t1
    | None, None -> (
        match (t1, t2) with
        | TCon (n1, as1), TCon (n2, as2) when n1 = n2 && List.length as1 = List.length as2 ->
            List.iter2 unify as1 as2
        | TApp (f1, a1), TApp (f2, a2) ->
            unify f1 f2;
            unify a1 a2
        (* f a ~ List Int → f ~ List, a ~ Int(最後の引数を剥がす。MiniLang:752-757) *)
        | TApp (f, x), TCon (n, args) when args <> [] ->
            let init, last = split_last args in
            unify f (TCon (n, init));
            unify x last
        | TCon (n, args), TApp (f, x) when args <> [] ->
            let init, last = split_last args in
            unify (TCon (n, init)) f;
            unify last x
        | TArrow (p1, r1, e1), TArrow (p2, r2, e2) ->
            unify p1 p2;
            unify r1 r2;
            unify e1 e2
        | TRecord r1, TRecord r2 -> unify r1 r2
        | TVariant r1, TVariant r2 -> unify r1 r2
        | TRowEmpty, TRowEmpty -> ()
        | TRowExtend (l, f, rest), _ -> unify_row l f rest t2
        | _, TRowExtend (l, f, rest) -> unify_row l f rest t1
        (* ここに来る TVar は Rigid(unbound は上で処理済み)。専用エラー(計画 §7.2)。
           相手が行のときは原因を語る枝を先に(M20 / I9 — 「{} と ς1」から
           閉じた行と剛な尾部の衝突を読み取るのは難しい) *)
        | ((TVar _ as rv), TRowEmpty) | (TRowEmpty, (TVar _ as rv)) ->
            type_error
              ("行 " ^ show rv ^ " は注釈で固定された行変数なので、この行と一致させられません(注釈を extends 付きの形にしてください)")
        | (TVar _, _ | _, TVar _) -> type_error ("スコープ付きの型が一致しません: " ^ show2 t1 t2)
        | _ -> type_error ("型が一致しません: " ^ show2 t1 t2))

and split_last = function
  | [] -> bug "split_last: empty"
  | xs ->
      let rec go acc = function [ x ] -> (List.rev acc, x) | x :: tl -> go (x :: acc) tl | [] -> assert false in
      go [] xs

(* ## 8.8 行どうしの単一化と、無限行の罠

   `<l : field | rest>` と `row2` を単一化します。やることは
   「`row2` から `l` を引っ張り出して、フィールドと残りをそれぞれ単一化」
   だけですが、1 点だけ罠があります。

   `rewrite_row` は `row2` の末尾変数を**書き換えます**。
   もしその末尾変数が `rest` の末尾変数と**同一**だったら、
   結果は `ρ = <l : τ | ρ>` という無限行になります。
   しかも型の occurs check では捕まりません。書き換えのほうが先に
   起きてしまい、`unify rest rest2` に到達した時点では
   すでに `rest` が伸びているからです。

   そこで書き換える**前**に `rest` の末尾変数を覚えておき、
   書き換えた後にそれが束縛されていたらエラーにします。
   3 行で済みますが、無ければ推論器が停止しなくなる 3 行です。

   もう 1 つ細工があります。フィールドの単一化が `Heap` ラベルで
   失敗したときだけ、メッセージを差し替えます。`Heap[h]` の `h` は
   `run` が与えた剛定数なので、ここでの不一致はほぼ確実に
   「別の `run` スコープのヒープを触った」です。生の
   「スコープ付きの型が一致しません」より、原因に近い言葉で言えます。

   これは Keleut 独自の思いつきではありません。MiniLang §6 (:836-840) の
   同じ細工をそのまま持ってきたもので、変えたのはラベル名だけ —
   `st` → `Heap`、`runST` → `run` — です。本章で本当に Keleut 固有なのは
   §8.7 の `same_var`、§8.4 と §8.6 の `same_kind` によるカインド比較、
   §8.4 の構造的導出のほうです。移植と自作は分けて読んでください。

   なお `rewrite_row` はラベルの**名前だけ**で一致を判定し、
   ラベル引数 (`Heap[h]` の `h`) は見つけてから単一化します。
   型全体で一致を見ると、どのラベルを選ぶかが引数に依存して
   決定性が壊れます。この方針も MiniLang §6 (:834-835) のままです。 *)

(* 書き換え前に rest の末尾変数を覚え、書き換え後に束縛されていたらエラーにする。
   ρ = <l : τ | ρ> という無限行の検出(MiniLang:826-833) *)
and unify_row label field rest row2 =
  let tail_before = row_tail_var rest in
  let field2, rest2 = rewrite_row row2 label in
  (match tail_before with
  | Some tv -> ( match !tv with Link _ -> type_error "再帰的な行型が発生しました" | _ -> ())
  | None -> ());
  (try unify field field2
   with Type_error msg when label = eff_heap -> type_error ("別の run スコープのヒープを使おうとしています(" ^ msg ^ ")"));
  unify rest rest2

(* ## 8.9 一般化 — in-place で、既定化を先に

   `generalize level t` は `t` を歩き、`level` より深いレベルの `Unbound` を
   `Generic` へ書き換えます。**戻り値はありません。tvar を破壊的に書き換えます。**

   関数型を返す実装 (置換を作って新しい型を組み立てる形) にしなかったのは、
   第5章 (tree.ml) の精緻化木のためです。第11章 (elab.ml) は推論の途中で
   AST ノードに型を書き込みます。新しい型を作って返す方式だと、
   書き込み済みの型と一般化後の型の共有が切れ、木の中に古い型が残ります。
   in-place なら書き込み済みのノードも自動的に一般化後の姿になります。
   MiniLang も同じ理由で in-place です。

   `Rigid` は決して一般化しません。剛定数はスコープの中で共有される定数で、
   「どんな型でもよい」の反対だからです。ここを一般化した瞬間、
   `run` のリージョン安全性も注釈の検査も無意味になります。

   ### 既定化を一般化より先に (D8)

   分岐の順序に注目してください。`vcls` に `Integral` が入っていたら
   `Generic` にせず `Int32` へ `bind` します。`Fractional` なら `Float64`。
   これは順序を守らないと動きません。先に `Generic` にしてしまうと、
   あとから `bind` しようにも `bind` は `Unbound` しか受け付けず、
   `bug` で落ちます。だから同じ `match` の中で述語を先に見ます。

   予約述語を制約集合に相乗りさせた効果がここに出ます。`1 + x` のような式で
   `x` の変数に `{Integral, Add}` が同時に乗ったとき、
   既定化は `Int32` を選び、`bind` が `add_class` を呼んで
   `Int32` に `Add` インスタンスがあることを確かめます。
   述語のための別経路を書かなくても、順序が正しいだけで整合します。

   ### default_numerics — 台帳の掃き出し

   一般化点に到達しない述語つき変数が残ります。式文として捨てられた
   中間結果の型などです。それを宣言の終わりに掃くのが `default_numerics`
   で、§8.4 で積んだ台帳をここで消費します。掃いたら台帳は空に戻します。

   掃き出しの順序は計画 §7.2 が決めています。宣言終了時に走らせるのは
   `default_numerics` だけで、網羅性検査の遅延キューはそれより早く、
   各 let 束縛群の `generalize` の**直前**に流します。逆にすると、
   `Generic` 化済みの行変数に第10章 (exhaust.ml) が `unify` を掛けて
   内部エラーになります — §8.3 で `Generic` を `bug` にしたのと同じ境界です。 *)

(* level より深い Unbound を Generic に。Rigid は決して一般化しない。
   予約述語つきは既定値へ bind(D8: Integral → Int32, Fractional → Float64) *)
let rec generalize level t =
  match repr t with
  | TVar v -> (
      match !v with
      | Unbound i when i.vlevel > level ->
          if List.mem cls_integral i.vcls then bind v t_int32
          else if List.mem cls_fractional i.vcls then bind v t_float64
          else v := Generic i
      | _ -> ())
  | TCon (_, args) -> List.iter (generalize level) args
  | TApp (f, a) ->
      generalize level f;
      generalize level a
  | TArrow (p, r, e) ->
      generalize level p;
      generalize level r;
      generalize level e
  | TRecord row | TVariant row -> generalize level row
  | TRowEmpty -> ()
  | TRowExtend (_, f, rest) ->
      generalize level f;
      generalize level rest

(* 宣言終了時: 台帳に残った述語つき弱変数を既定値に落とす(計画 §7.2)。
   非述語の変数はどちらの分岐にも当たらず素通りする *)
let default_numerics () =
  List.iter
    (fun v ->
      match !v with
      | Unbound { vcls; _ } ->
          if List.mem cls_integral vcls then bind v t_int32
          else if List.mem cls_fractional vcls then bind v t_float64
      | _ -> ())
    !class_vars;
  class_vars := []

(* 型に現れる変数の vid 集合(MiniLang の collectVars) *)
let rec collect_vars t (acc : (oid, unit) Hashtbl.t) =
  match repr t with
  | TVar r -> ( match !r with Link _ -> () | _ -> Hashtbl.replace acc (var_info_of r).vid ())
  | TCon (_, args) -> List.iter (fun a -> collect_vars a acc) args
  | TApp (f, a) ->
      collect_vars f acc;
      collect_vars a acc
  | TArrow (p, r, e) ->
      collect_vars p acc;
      collect_vars r acc;
      collect_vars e acc
  | TRecord row | TVariant row -> collect_vars row acc
  | TRowEmpty -> ()
  | TRowExtend (_, f, rest) ->
      collect_vars f acc;
      collect_vars rest acc

(* 一般化されようとしている(all なら宣言の終わりまで残った)制約つき
   変数のうち、スキーマの型から到達できないものを曖昧として報告する
   (M17 / D48。MiniLang §7 の checkAmbiguity)。
   予約述語 (Integral / Fractional) が乗った変数は既定化で必ず決まる
   ので対象外(D8 / D48)— 免除しないと let ne = 1 != 2 のような
   既定化頼みの形が全部落ちる。kept には「まだ Unbound のもの」だけを
   残す — 到達不能な述語つき変数を default_numerics に届け続けるため
   であり、Link / Generic の死んだ項目を刈って走査を線形に保つためでも
   ある(台帳は instantiate のたびに伸びる)。刈っても、生きた制約つき
   変数を大量に抱えた宣言では 検査点の数 × 台帳長 の積が残る —
   病的な入力では二次(260829-5 台帳 V16、M19) *)
let check_ambiguity ~all ~level tys =
  let reach = Hashtbl.create 32 in
  List.iter (fun t -> collect_vars t reach) tys;
  let kept = ref [] in
  List.iter
    (fun v ->
      match !v with
      | Unbound i ->
          kept := v :: !kept;
          if
            (all || i.vlevel > level)
            && i.vcls <> []
            && (not (List.exists is_predicate i.vcls))
            && not (Hashtbl.mem reach i.vid)
          then
            type_error
              ("曖昧な制約: "
              ^ String.concat " + " (List.sort compare (List.map name_of i.vcls))
              ^ " を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)")
      | _ -> ())
    !class_vars;
  class_vars := List.rev !kept

(* ## 8.10 map_generics — 3 つの写像の共通骨格

   `instantiate` / `skolemize` / `subst_params` は、どれも
   「型を歩いて `Generic` を何かに置き換える」関数です。
   違うのは**何に置き換えるか**だけなので、走査は 1 つにまとめます。
   `map_generics_with` は `Hashtbl` の memo を持ち、同じ `vid` の
   `Generic` には必ず同じ結果を返します。この memo が無いと
   `A => A` の 2 つの `A` が別物になり、多相が壊れます。

   | 関数 | `Generic` を何にするか | 使う場所 |
   |---|---|---|
   | `instantiate` | 現在のレベルの新しい未定変数 | 変数参照 (第11章) |
   | `skolemize` | 現在のレベルの新しい剛定数 | インスタンス本体の包摂検査 (§11.38) |
   | `subst_params` | 指定された実引数 (無ければ新変数) | 宣言表の展開 (第10章・第11章) |

   ### instantiate が型クラスの複製点

   `new_var ~kind:i.vkind ~classes:i.vcls level` — カインドと制約集合を
   **ごとコピーする**のがここです。`[A: Add] let double(x: A) = x + x` を
   一般化すると `A` は `{Add}` を持った `Generic` になり、
   使うたびに `{Add}` を持った新しい未定変数が生まれます。その変数が
   `Int32` と単一化されれば `bind` が `add_class` を呼び、
   `Int32` に `Add` があるかを確かめます。制約の検査は
   これ以上何もしません。Diktor の旧実装はこの複製が抜けていて
   (計画 §7.2)、制約が使用点に届いていませんでした。

   複製した変数に制約が乗っていたら台帳にも載せます(`new_class_var`
   経由 — 制約つき変数の作成経路はこの 1 本に寄せてあります)。§8.4 で
   述べたとおり、一般化点に届かない制約つき変数を宣言の終わりに掃き、
   途中の一般化点では曖昧性を見るためです。`instantiate` はプログラム中で
   最も多く呼ばれる関数なので、台帳が伸び続けないよう `default_numerics` が
   毎宣言空に戻し、`check_ambiguity` も死んだ項目を刈ります。

   ### skolemize が vcls を持っていく

   `{ i with vid = new_oid (); vlevel = level }` は `vkind` と `vcls` を
   そのまま引き継ぎ、識別子とレベルだけを差し替えます。ここで `vcls` を
   落とすと、クラス宣言が期待型に書いた制約が剛定数から消えます。
   すると包摂検査は、インスタンス側の推論結果が持つ制約つき変数を
   その剛定数へ束縛しようとした瞬間に `add_class` で落ち、
   正しいインスタンスまで「制約を書いてください」と拒否されてしまいます。
   引き継ぐのは、期待型側の制約を落とさないためです。

   名前から誤解しやすい点をひとつ断っておきます。`skolemize` は
   **注釈付き let の検査には使われていません**。全リポジトリで唯一の
   呼び出し元は第11章の `check_instance_bodies` (§11.38) で、
   インスタンスメソッドがクラス宣言の型を満たすかを見る包摂検査です。
   `let f[A: Add](x: A) = ...` の `A` を剛定数にするのは第11章の
   `make_rigids` (§11.25) のほうで、そちらは `Generic` を写すのではなく
   `tp_classes` から `vcls` を組み立てて `Rigid` を直接作ります。
   第11章が「注釈の skolem 化の 3 点セット」と呼ぶのも
   `make_rigids` / `open_explicit_eff` / `release_rigids` であって、
   本章の `skolemize` はその外にいます。

   ただし**宣言に書いていない制約は付かない**という性質は、どちらの
   経路でも同じです。だから §8.4 の `Rigid` ケースが自信を持って
   「`[A: C]` のように制約を書いてください」と案内できます。

   ### ランク 1 である理由

   `generalize` を呼ぶのは let 束縛のときだけ、`instantiate` を呼ぶのは
   変数参照のときだけです。ラムダの引数には常に単なる未定変数を割り当てるので、
   引数を 2 つの異なる型で使うと単一化に失敗します。これがランク 1 の正体で、
   量化子を型の中に持たない (`Generic` マークだけで済ませる) 設計は
   この呼び出し規律とセットになっています。多引数クラスを実装しない (D11)
   と決めたおかげで型スキーマ用のデータ型すら不要になり、
   本章には `Scheme` に相当する型が 1 つも出てきません。

   `reset` は台帳を空に戻すだけです。呼び場所は 2 つ — 第11章の
   `type_check_decls` が**検査を始める前**の初期化として警告リストや
   第10章のキューと並べて叩き、`process_decls` が**パス 2 に入る直前**にも
   叩きます。後者はパス 1(インスタンス頭・前方参照シグネチャの
   instantiate)で溜まった制約つき変数を、宣言ごとの曖昧性判定に
   持ち込まないための後始末で、1 回の型検査で 2 回走ります。 *)

let map_generics_with memo f t =
  let rec go t =
    match repr t with
    | TVar v -> (
        match !v with
        | Generic i -> (
            match Hashtbl.find_opt memo i.vid with
            | Some t -> t
            | None ->
                let t = f i in
                Hashtbl.add memo i.vid t;
                t)
        | _ -> TVar v)
    | TCon (n, args) -> TCon (n, List.map go args)
    | TApp (g, a) -> tapp (go g) (go a)
    | TArrow (p, r, e) -> TArrow (go p, go r, go e)
    | TRecord row -> TRecord (go row)
    | TVariant row -> TVariant (go row)
    | TRowEmpty -> TRowEmpty
    | TRowExtend (l, fld, rest) -> TRowExtend (l, go fld, go rest)
  in
  go t

let map_generics f t = map_generics_with (Hashtbl.create 8) f t

(* Generic → 現在のレベルの新しい未定変数。vkind / vcls ごと複製する
   (型クラスの複製点。既存実装はここが抜けていた、計画 §7.2)。述語つきは台帳へ *)
let instantiate level t =
  map_generics
    (fun i ->
      new_class_var ~kind:i.vkind ~classes:i.vcls level)
    t

(* Generic → 現在のレベルの新しい剛定数。使うのはインスタンス本体の
   包摂検査だけ(§11.38)。注釈の skolem 化は elab の make_rigids *)
let skolemize level t = map_generics (fun i -> new_rigid ~kind:i.vkind ~classes:i.vcls level) t

(* Generic → 指定した型(データ宣言・エフェクト宣言のパラメータ置換) *)
let subst_params level args t =
  map_generics
    (fun i -> match List.assoc_opt i.vid args with Some t -> t | None -> new_class_var ~kind:i.vkind ~classes:i.vcls level)
    t

let reset () = class_vars := []
