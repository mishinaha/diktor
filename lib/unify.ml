(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第8章 単一化

   本章は型推論器の中心にあたる単一化を実装する。
   第11章(elab.ml)が構文から読み取る要求は、
   最終的にすべて「この型とこの型を等しくする」という 1 つの命令になる。
   その命令を実行するのが本章の `unify` で、
   ほかの関数はこの命令を安全に実行するための前後処理である。

   本章が使う材料は 2 つある。
   第1章(syntax.ml)が定める型・カインド・行の表現と、
   第6章(decls.ml)が持つ宣言表・クラス表・インスタンス表である。
   本章が外へ渡す主な関数と、それを使う章は次のとおりである。

   | 関数 | 使う章 |
   |---|---|
   | `unify` / `add_class` | 第11章(elab.ml)の全規則、第10章(exhaust.ml)の 1 か所 |
   | `generalize` / `default_numerics` / `check_ambiguity` / `reset` | 第11章の let と宣言の終わり |
   | `instantiate` / `skolemize` | 第11章の変数参照と、インスタンス本体の包摂検査 |
   | `subst_params` | 第10章と第11章でのコンストラクタのフィールドの展開 |
   | `rewrite_row` | 第11章のフィールドアクセスの規則 |
   | `kind_of` / `var_info_of` / `map_generics_with` | 第11章の型の補助関数 |
   | `is_predicate` / `show_ref` | 第9章(show.ml)。制約の印字と、循環参照を避けるための穴 |

   `bind` も外から見えるが、呼ぶのは本章の `unify` / `generalize` / `default_numerics` だけである。
   外向けの関数ではないので、§8.5 で内部の手続きとして扱う。
   第10章が `unify` を呼ぶのは構造的ヴァリアントの行を閉じる 1 か所だけで、
   それ以外は型を読むだけである。

   Keleut の型には、単一化の実装に効く特徴が次のようにある。

   | 特徴 | 本章での扱い |
   |---|---|
   | 矢印が 3 要素 | `TArrow` は引数の閉じた `_item` 行、返り値、エフェクト行を持つ |
   | カインド変数がある | `KVar` があるので、カインドの比較には `same_kind` を使う |
   | 予約述語 | 数値リテラルの `Integral` / `Fractional` がクラス制約の集合に同居する |
   | `Rigid` が 2 役 | `run` のリージョン変数と、注釈の検査で作る剛定数の両方を表す |
   | 多パラメータ型クラスを持たない | 型スキーマ専用の型を持たない |
   | レベルは引数 | 現在のレベルを可変の大域変数に置かない |

   最後の行について補足する。
   本章の関数はレベルをすべて引数で受け取り、
   `generalize` や `instantiate` が大域状態を暗黙に読むことはない。
   そのため、ある宣言の処理が残したレベルが次の宣言を汚すことがない。
   その代わり、呼び出し側は正しいレベルを渡す責任を負う。 *)

open Aux
open Syntax
open Type

(* ## 8.1 カインドの計算

   Diktor はカインド検査のための専用の走査パスを持たない。
   型構成子は宣言表からカインドを引き、適用された引数の数だけ矢印を落とす。
   `kind_of` / `drop_arrows` が見るのは結果のカインドだけである。
   矢印の定義域、つまり型引数が宣言のパラメータのカインドと合うかどうかは、精緻化の側で照合する。
   型構成子の適用では宣言表のカインドと照合し(第11章 §11.3 の `elab_con_args`)、
   高階カインドの型変数への適用 `F[A]` では頭のカインドと照合する。
   どちらも、型引数を読んだその場で照合する。

   `drop_arrows` には `KVar` の場合がある。
   Keleut の型パラメータの束縛子は、`[A]` も `[R]` も `[E]` も字句がまったく同じで、
   型なのか行なのかは使われた位置からしか分からない。
   `F[_]` のように `[_]` が書いてあるときだけ、その場で `KArrow` が確定する。

   そのため、型引数を適用したときに頭のカインドがまだ分からない、という状況は普通に起きる。
   `drop_arrows` は `KVar` に出会うと、
   その場で `KArrow (新しいカインド変数, 新しいカインド変数)` を張って先へ進む。
   本実装のカインド推論はこれだけである。
   張った定義域を型引数と照合するのは、上に書いたとおり精緻化の側である。
   `drop_arrows` 自身は矢印の左を捨て、右だけを返す。
   未解決のまま残った `KVar` は、宣言の終わりに第1章の `default_kind` が `KStar` へ既定化する。

   `var_info_of` は、型変数の 4 つの状態(`Unbound` / `Generic` / `Rigid` / `Link`)から `var_info` を取り出す。
   `Link` に当たったときは `bug` にする。
   `repr` を通した後の `TVar` は `Link` ではない、という不変条件をここで確かめるためである。
   本章の関数はすべて、型を `repr` してから `match` する。 *)

let rec drop_arrows k n =
  if n = 0 then k
  else
    match kind_repr k with
    | KArrow (_, r) -> drop_arrows r (n - 1)
    | KVar r ->
        (* 使われた位置でカインドを確定させる *)
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

(* ## 8.2 型の印字関数を後から差し込む

   本章のエラーメッセージは型を印字する。
   一方、印字を担う第9章(show.ml)も、制約を印字するときに本章の `is_predicate` を呼ぶ。
   2 つのモジュールが互いを参照するが、OCaml のモジュールは循環できない。
   そこで本章は印字関数を `ref` の穴として置き、show.ml の末尾が起動時にそこを埋める。

   穴が埋まる前に呼ばれても、`<型>` と印字するだけで落ちない。
   型エラーの本文に `<型>` が並ぶときは、
   show.ml のトップレベルの初期化が走っていない(show.ml がリンクされていない)。 *)

let show_ref : (ty -> string) ref = ref (fun _ -> "<型>") (* Show が後から差し込む(循環回避) *)

let show t = !show_ref t

let show2_ref : (ty -> ty -> string) ref = ref (fun _ _ -> "<型>")

let show2 a b = !show2_ref a b

(* ## 8.3 occurs check、レベル調整、脱出検査

   型変数 `tv` に型 `t` を代入する前に、`occurs_adjust` が `t` を 1 度だけ走査して、
   次の 3 つを同時に行う。

   - **occurs check**：`t` の中に `tv` 自身が現れたら、無限型になるのでエラーにする。
   - **レベル調整**：`t` の中の未定変数のレベルを、`tv` のレベルまで下げる。
   - **脱出検査**：`t` の中に `tv` より深いレベルの剛定数があれば、エラーにする。

   レベル調整を省くと、型システムが不健全になる。
   内側の let で作られた深いレベルの変数が外側の浅いレベルの変数と単一化されたなら、
   その変数はもう内側だけのものではない。
   代入は変数の生存範囲を外側へ広げるので、レベルは両者の小さいほうに合わせる。

   剛定数のレベルは下げられない。
   剛定数は、導入したスコープの外では意味を持たない定数として作るものだからである。
   下げると剛定数をスコープの外へ持ち出すことになるので、下げるかわりにエラーにする。

   `Rigid` は 2 つの役を兼ねる。
   `run h { ... }` が導入するリージョン変数 `h` と、
   `let f[A](...)` の注釈を検査するときの `A` である。
   どちらも、与えたスコープの外へ漏らしてはならないという同じ性質を持つので、
   この 1 つの場合が両方を守る。
   第11章は、`run` の規則(§11.17)と let 束縛の規則(§11.28)で、剛定数を次の同じ手順で扱う。

   1. レベルを上げる
   2. 剛定数を作る
   3. 出口で、剛定数が浅いレベルへ漏れていないかを調べる

   `Generic` に当たったときは、`type_error` ではなく `bug` にする。
   `Generic` は一般化済みのスキーマの中にしか現れない。
   単一化まで流れてきたなら第11章(elab.ml)が `instantiate` を呼び忘れており、
   利用者のプログラムの誤りではなく実装の誤りである。 *)

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

(* ## 8.4 クラス制約の伝播

   Keleut の型クラスは、辞書渡しも修飾型も持たない。
   クラス制約は型変数そのものに付いたフィールド(`vcls`)で、
   文脈の簡約は単一化の途中でその場で決定的に終わる。
   `add_class t c` は「型 `t` はクラス `c` のインスタンスでなければならない」という要求を、
   `t` の形で場合分けして解消する。

   最初にカインドを調べる。
   ここで `=` ではなく `same_kind` を使う理由は §8.6 で述べる。

   | `t` の形 | 処理 |
   |---|---|
   | `Unbound` | 制約の集合に加え、台帳にも載せる |
   | `Rigid` / `Generic` | 宣言されていない制約ならエラーにし、直し方を案内する |
   | `TCon` | インスタンス表を引き、インスタンスの前提(`ii_premises`)を型引数へ伝播する |
   | `TRecord` / `TVariant` | クラスが構造的導出を有効にしていれば、閉じた行の各フィールドへ伝播する |
   | `TApp` | 制約を付けられないのでエラーにする |

   `Generic` に制約の要求が届くのは、
   宣言のスキーマの中(newtype のフィールド型やクラスメソッドの型)で制約つきエイリアスを展開したときである。
   展開したエイリアスの制約が、パラメータを表す `Generic` に要求される。
   規則は `Rigid` と同じで、宣言済みの制約に含まれていれば満たされ、
   含まれていなければ `[A: Show]` のように制約を書くよう案内する。

   `Rigid` の場合のエラーメッセージは、要求された制約が予約述語かどうかで 2 通りに分かれる。
   予約述語 `Integral` は利用者が宣言できないクラスなので、
   `let f[A: Add](x: A) = x + 1` に対して「A は Integral のインスタンスではない」と伝えても、
   利用者には直す手段がない。
   そこで、`0i32` のように接尾辞を付けるか具体型を使うよう案内する。
   普通のクラスなら `[A: Add]` と書けば直るので、そう案内する。

   この例に `[A: Add]` を付けているのは、予約述語の分岐まで到達させるためである。
   制約を外した `let f[A](x: A) = x + 1` では、
   `+` のスキーマが持つ `Add` の要求のほうが先に剛定数に届く。
   その結果、普通のクラスの分岐で落ち、次のメッセージを出す。

   ```
   型パラメータ ς1 は Add のインスタンスではありません。[A: Add] のように制約を書いてください
   ```

   注釈を経由する `let f[A](x: A): A = 1` でも、予約述語の分岐に到達する。

   構造的導出の分岐は sample.kel:391-395 の規則を実装する。
   カインドが `* -> *` のクラスはこの分岐に到達しない。
   第11章がクラス宣言の時点でカインドを調べ、
   そうしたクラスの `derive structural` を拒否するからである。
   `Eq` のようにクラス宣言に `derive structural` が付いていれば、レコードやヴァリアントを分解し、
   各フィールドに同じ制約を要求する。
   ただし、分解するのは行が閉じているときだけである。
   `{x: Int32 extends R}` の `R` に何が入るか分からない以上、比較できるとは約束できない。
   行変数ごとの制約 `[R: Eq]` を導入すれば開いた行も扱えるが、
   カインドの扱いと制約の解決の両方を変えることになるので、仕様はこれを採らない。

   `TCon` の分岐は、インスタンス表に登録された前提を使う(前提の表は第6章 §6.9)。
   `Eq[List[_]]` の前提 `A: Eq` は `(0, Eq)` として表に載っている。
   `List[Opaque]` に `Eq` を要求すると、`Opaque` に `Eq` が伝播し、
   「Opaque は Eq のインスタンスではありません」で落ちる(`test/premise.t` の pr2 / pr3)。
   分岐の中の `if i < List.length args` は到達しない保険である。
   冒頭のカインドの照合が先に落とすので、前提が位置 `i` を持つなら `args` は `i + 1` 個以上ある。

   `TApp` に制約を付けられないのは、修飾型を持たないからである。
   Haskell は `Show (f a)` のような制約を残して解決を後回しにできるが、
   本実装の制約は型変数か具体型の頭にしか付けられない。
   `TApp` への制約を扱うには、制約を型と一緒に持ち回る仕組みが要る。

   ### 台帳 class_vars

   `class_vars` は、制約が付いた変数を記録する台帳である。
   台帳は 2 つの処理が使う。
   1 つは、予約述語つきの変数を宣言の終わりに既定の型へ落とす処理(§8.9 の `default_numerics`)で、
   もう 1 つは、型から到達できない制約つき変数を報告する曖昧性検査(§8.9 の `check_ambiguity`)である。
   どちらも、一般化や宣言の終わりまで決まらなかった制約つき変数を扱うので、同じ台帳を使う。
   既定化は台帳を掃き出すだけで、型から到達できるかどうかは調べない。
   到達を調べるのは曖昧性検査だけである。 *)

let is_predicate c = c = cls_integral || c = cls_fractional

(* 制約つき変数の台帳(宣言終了時の default_numerics が掃き、
   check_ambiguity が到達不能な制約を報告する) *)
let class_vars : tvar ref list ref = ref []

(* 制約つきの新変数は必ずここで作り、作った時点で台帳に載せる。
   台帳が制約つき変数をすべて控えるのは、作成の経路がこの 1 本だからである。
   instantiate、subst_params、第11章のコンストラクタの具体化(dd_params の展開)もここを通る。
   別の経路で作ると、その変数の制約は曖昧性検査に届かない *)
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
          (* Generic に届くのは、宣言のスキーマの中(newtype のフィールドや
             クラスメソッドの型)で制約つきエイリアスを展開したとき。規則は
             Rigid と同じで、宣言済みの制約に含まれていれば満たされ、
             無ければ制約を書くよう案内する *)
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

(* ## 8.5 代入の 4 つの手順

   代入先になれるのは `Unbound` の変数だけである。
   `Rigid`、`Generic`、`Link` はここに来ない(来たら実装の誤りなので `bug` にする)。
   `bind` は次の 4 つの手順を、この順に行う。
   順序を入れ替えると正しく動かない。

   1. カインドが一致するかを調べる(`same_kind`。あわせて `KVar` を解決する)
   2. `occurs_adjust` で occurs check、レベル調整、脱出検査を行う
   3. 変数に付いていた制約を代入先の型へ伝播する(`add_class`)
   4. `Link` を張る

   手順 2 は手順 4 より先でなければならない。
   `v := Link t` を先に実行すると、以後 `repr (TVar v)` は `t` を返すので、
   `t` の中に `v` が含まれていても `occurs_adjust` は `v` を見つけられない。
   occurs check が何も検出しないまま、無限型が通ってしまう。

   手順 3 を手順 4 より先に行うのは、失敗したときの後始末のためである。
   制約の伝播が `type_error` で落ちたとき、まだ `Link` を張っていなければ `v` は未定変数のまま残り、
   型の状態が中途半端にならない。

   `unbound_var` は `repr` を呼ばない。
   呼び出し側の `unify` が `repr` 済みの型を渡すことを前提にしている。 *)

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

(* ## 8.6 行の書き換えと最左一致

   Diktor の行は、Daan Leijen の *Extensible Records with Scoped Labels*(2005)に従う。
   通常の行型システムは、同じラベルを 2 度含まないという lacks 制約(`ρ \ x`)を課す。
   lacks 制約は正しいが、制約を型と一緒に持ち回る必要があり、実装量が増える。

   Scoped Labels は逆に、ラベルの重複を許す。
   その代わり、次のように定める。

   - `r.x` は最も左の `x` を取り出す
   - `{x = e | 残り}` は無条件に追加でき、それまでの `x` は隠れる
   - `r \ x` は最も左の `x` を消し、隠れていた `x` が再び見える

   同じ名前のラベルは、レキシカルスコープの変数のように積み重なる。

   Keleut では、この最左一致が 3 つの場所で同じ意味を持つ。
   レコードでは手前のフィールドが勝ち、エフェクト行では最も左のラベルが選ばれ、
   `run` の入れ子では内側のヒープが優先される。
   修飾なしで書いた操作名の解決も、行の最左優先で決まる(第11章 §11.20)。
   sample.kel:620 の `copy` の中の `write` は File と Console の両方の操作に該当するが、
   最左を採ると、handle の入れ子から推論で組み立てた行では最も内側のハンドラと一致する。
   ただし、注釈で行を明示したときの最左は書かれた順序で決まるので、
   実行時の入れ子の順序と食い違うことがある(§11.20)。
   それでも健全なのは、perform が解決済みの完全名を運ぶからである。

   中心になる関数は `rewrite_row row label` である。
   行の中から最初の `label` を探して先頭へ持ち上げ、`(フィールド型, 残り)` を返す。
   行の末尾が未定の行変数だったときは、
   その場で `TRowExtend (label, 新しい型変数, 新しい行変数)` へ伸ばす。
   この関数には注意点が 2 つある。

   ### 注意点 1:挿入する型変数のレベル

   行を伸ばすときに作る 2 つの変数は、現在のレベルではなく、行変数自身のレベルで作る。
   現在のレベルで作ると、一般化してはならない変数を一般化してしまう。
   たとえば次の式を考える。

   ```
   fn(r) => { r.a; let g = fn() => r.b; ... }
   ```

   `r.b` が `r` の行を伸ばすのは、`g` の右辺、つまり 1 段深いレベルの中である。
   `b` のフィールド型を現在のレベルで作ると、`g` を一般化するときにその変数が `Generic` になり、
   `g` に任意の `A` について `() => A` という型が付く。
   引数のフィールドから任意の型を取り出せることになるので、不健全である。

   行変数のレベルで作った新しい変数は、呼び出し側の `unify` から `bind` を通って相手の型と結ばれる。
   そのとき `occurs_adjust` が走り、相手の型に含まれる変数のレベルも下がる。

   ### 注意点 2:行変数のカインドは same_kind で調べる

   変数が行変数かどうかは、`vkind = KRow` という構造の一致ではなく、`same_kind` で判定する。
   第11章(elab.ml)の `make_rigids` は、
   arity が 0 の型パラメータ(`let fst[A, R](...)` の `R` のような束縛子)に `new_kind_var ()` を渡す。
   §8.1 で述べたとおり、束縛子のカインドは使われた位置で決まるからである。
   この `R` が行の位置で使われると、そのカインドは `KStar` でも `KRow` でもなく、
   リンク先が `KRow` である `KVar` になる。
   構造の一致ではこれを行変数と判定できない。

   構造の一致で判定すると、仕様の中心的な例が型エラーになる。
   sample.kel:195 の `fst(t: {_item: A extends R})` にレコード `{x = 1, _item = ...}` を渡す例(:201-203)と、
   :209-215 の `describe(#Other)` で、それぞれ行多相のレコードと、
   構造的ヴァリアントの残りの行を使う例である。
   第1章(syntax.ml)は `KVar` を宣言の終わりに `KStar` へ既定化するので、
   既定化までカインドは確定していない。
   そのため、カインドは構造では比べず、`same_kind` で比べる。

   `same_kind` は比較しながら `KVar` を相手のカインドに張る(単一化する)ので、
   ここを通った時点で `R` のカインドが `Row` に確定する。 *)

(* 最左の label を先頭へ持ち上げ、(フィールド型, 残り) を返す。
   新変数は行変数自身のレベルで作る(§8.6 の注意点 1) *)
let rec rewrite_row row label =
  match repr row with
  | TRowEmpty -> type_error ("ラベル " ^ name_of label ^ " がありません(行は閉じています)")
  | TRowExtend (l, f, rest) when l = label -> (f, rest)
  | TRowExtend (l, f, rest) ->
      let f2, rest2 = rewrite_row rest label in
      (f2, TRowExtend (l, f, rest2))
  | TVar v -> (
      match !v with
      (* カインドは構造の一致でなく same_kind で見る。[R] のような arity 0 の
         型パラメータは new_kind_var() を受け取り、行の位置で使われると
         KVar{→KRow} になるので、KRow との構造の一致では取りこぼす *)
      | Unbound { vlevel; vkind; _ } when same_kind vkind KRow ->
          let f2 = new_var vlevel in
          let rest2 = new_row_var vlevel in
          v := Link (TRowExtend (label, f2, rest2));
          (f2, rest2)
      | Rigid { vkind; _ } when same_kind vkind KRow ->
          (* 注釈で固定された行にはラベルを追加できない。高階のエフェクト
             注釈を書き間違えたときに最初に出る診断なので、「行型では
             ありません: ς1」ではなく原因を述べる(§8.8 の Heap の
             言い換えと同じく、原因を名指しする) *)
          type_error
            ("行 " ^ show (TVar v) ^ " は注釈で固定された行変数なので、ラベル " ^ name_of label
           ^ " を足せません(注釈側に " ^ name_of label ^ " を(必要なら引数つきで)書き足してください)")
      | _ -> type_error ("行型ではありません: " ^ show (TVar v)))
  | t -> type_error ("行型ではありません: " ^ show t)

(* ## 8.7 単一化の本体

   単一化の本体は素直な構造的単一化である。
   まず両辺を `repr` し、同じものなら何もしない。
   片方が未定変数なら `bind` する。
   どちらでもなければ、形に従って分解する。

   最初の `same_var` は、OCaml での型変数の表現に合わせた判定である。
   OCaml の `TVar r` はヴァリアントの箱なので、同じ `ref` を指す別の箱が簡単にできる。
   そのため、同じ変数かどうかは箱ではなく `ref` の物理等価で調べる。
   箱で比べると、同じ変数どうしの単一化が `bind v (TVar v)` になり、
   occurs check が自分自身を見つけてエラーになる。

   ### 矢印

   `TArrow` は、引数と返り値に加えてエフェクト行も単一化する。
   関数を呼ぶ側の行と呼ばれる側の行がここで結ばれることで、エフェクトが型に乗る。
   Keleut の引数は閉じた `_item` 行のレコードなので、引数の個数の不一致は行の単一化から検出される。
   引数の個数を数える専用のコードは、この推論器にはない。

   ### 型適用(高階カインド)

   高階カインドのための場合は `TApp` の 3 つだけである。

   ```
     f a ~ g b        →  f ~ g,  a ~ b
     f a ~ List Int   →  f ~ List,  a ~ Int      (最後の引数を剥がす)
   ```

   一階の単一化のままで済むのは、Keleut が型レベルのλを持たないからである。
   λを書けるなら `f := λx. List Int` のような解も候補になり、mgu が一意でなくなって主要型を失う。
   同じ理由で、型エイリアスの部分適用も認めない(第11章 §11.5 の `expand_alias` が拒否する)。
   第1章(syntax.ml)の `tapp` と `repr` は、頭が飽和した `TCon` なら引数を畳み込むように正規化する。
   したがって `TApp` の頭は常に型変数で、分解の仕方は一通りに決まる。

   ### 最後の 2 つの場合

   `(TVar _, _ | _, TVar _)` に落ちてくる `TVar` は、
   常に `Rigid` である(`Unbound` は上の `bind` で処理済み)。
   ここで専用のメッセージを出すのは、この分岐がリージョンの取り違えを報告する主な経路だからである。
   `run` を入れ子にして外側のヒープの参照を内側で読もうとすると、
   `occurs_adjust` の脱出検査ではなく、この分岐で落ちる。
   エフェクト行の中で、外側と内側の `run` が作った 2 つの剛定数が一致しないからである。
   これは仕様どおりの拒否である。

   空の行と剛な行変数が衝突したときは、その手前の分岐で、
   行が注釈で固定されていることを述べるメッセージを出す。
   「{} と ς1」が一致しないとだけ伝えても、利用者は原因を読み取りにくいからである。 *)

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
        (* f a ~ List Int → f ~ List, a ~ Int(最後の引数を剥がす) *)
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
        (* ここに来る TVar は Rigid(Unbound は上で処理済み)なので、専用の
           エラーにする。相手が空の行のときは、閉じた行と剛な行変数の衝突で
           あることを述べる分岐を先に置く。「{} と ς1」の不一致とだけ
           伝えても、原因を読み取りにくいからである *)
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

(* ## 8.8 行どうしの単一化と無限行

   `unify_row` は `<l : field | rest>` と `row2` を単一化する。
   `row2` から `l` を取り出し、フィールドどうしと残りどうしをそれぞれ単一化するだけだが、
   注意点が 1 つある。

   `rewrite_row` は `row2` の末尾の変数を書き換える。
   その末尾の変数が `rest` の末尾の変数と同一だった場合、
   結果は `ρ = <l : τ | ρ>` という無限行になる。
   この無限行は、型の occurs check では捕まらない。
   書き換えが先に起きるので、`unify rest rest2` に到達した時点では、
   すでに `rest` が伸びているからである。

   そこで、書き換える前に `rest` の末尾の変数を覚えておき、
   書き換えた後にそれが束縛されていたらエラーにする。
   この検査が無いと、推論器が停止しなくなる。

   フィールドの単一化が `Heap` ラベルで失敗したときは、エラーメッセージを差し替える。
   `Heap[h]` の `h` は `run` が与えた剛定数なので、ここでの不一致はほぼ確実に、
   別の `run` のスコープのヒープを使おうとしたことを意味する。
   そのため、「スコープ付きの型が一致しません」より原因に近い言葉で伝える。

   `rewrite_row` はラベルの名前だけで一致を判定し、
   ラベル引数(`Heap[h]` の `h`)は見つけた後で単一化する。
   ラベル引数まで含めて一致を判定すると、どのラベルを選ぶかが引数に左右され、
   選択が決定的でなくなる。 *)

(* 書き換え前に rest の末尾変数を覚え、書き換え後に束縛されていたらエラーにする。
   ρ = <l : τ | ρ> という無限行の検出 *)
and unify_row label field rest row2 =
  let tail_before = row_tail_var rest in
  let field2, rest2 = rewrite_row row2 label in
  (match tail_before with
  | Some tv -> ( match !tv with Link _ -> type_error "再帰的な行型が発生しました" | _ -> ())
  | None -> ());
  (try unify field field2
   with Type_error msg when label = eff_heap -> type_error ("別の run スコープのヒープを使おうとしています(" ^ msg ^ ")"));
  unify rest rest2

(* ## 8.9 一般化

   `generalize level t` は `t` を走査し、
   `level` より深いレベルの `Unbound` を `Generic` へ書き換える。
   戻り値は持たず、型変数をその場で破壊的に書き換える。

   置換を作って新しい型を組み立てて返す形にしないのは、第5章(tree.ml)の精緻化木のためである。
   第11章(elab.ml)は推論の途中で木のノードに型を書き込む。
   新しい型を作って返すと、書き込み済みの型と一般化後の型が共有されなくなり、木の中に古い型が残る。
   その場で書き換えれば、書き込み済みのノードの型も一般化後の姿になる。

   `Rigid` は一般化しない。
   剛定数はスコープの中で共有される定数で、「どんな型でもよい」とは逆の意味を持つ。
   一般化すると、`run` のリージョンの安全性も、注釈の検査も成り立たなくなる。

   ### 既定化は一般化より先に

   `generalize` の分岐は、`vcls` に `Integral` が入っていれば `Generic` にせず `Int32` へ `bind` し、
   `Fractional` なら `Float64` へ `bind` する。
   この順序は入れ替えられない。
   先に `Generic` にすると、`bind` は `Unbound` しか受け付けないので、
   後から `bind` しようとして `bug` で落ちる。
   そのため、同じ `match` の中で述語を先に調べる。

   予約述語をクラス制約の集合に同居させた効果がここに現れる。
   `1 + x` のような式で `x` の変数に `{Integral, Add}` が同時に付いたとき、既定化は `Int32` を選ぶ。
   続いて `bind` が `add_class` を呼び、`Int32` に `Add` のインスタンスがあることを確かめる。
   述語のための別の経路を書かなくても、この順序を守るだけで整合する。

   ### default_numerics による台帳の掃き出し

   一般化点に到達しない述語つきの変数も残る。
   式文として捨てられた中間結果の型などである。
   `default_numerics` は宣言の終わりにそれらを既定の型へ落とす。
   §8.4 で積んだ台帳をここで消費し、掃いた後は台帳を空に戻す。

   宣言の終わりに走らせるのは `default_numerics` だけである。
   網羅性検査の遅延キューはそれより早く、各 let 束縛群の `generalize` の直前に処理する。
   順序が逆だと、第10章(exhaust.ml)が `Generic` になった行変数に `unify` を掛けて、
   内部エラーになる。
   §8.3 で `Generic` を `bug` にしたのと同じ境界である。 *)

(* level より深い Unbound を Generic にする。Rigid は一般化しない。
   予約述語つきの変数は既定の型へ bind する(Integral → Int32、Fractional → Float64) *)
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

(* 宣言の終わりに、台帳に残った述語つきの弱い変数を既定の型に落とす。
   述語のない変数はどちらの分岐にも当たらず素通りする *)
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

(* 型に現れる変数の vid の集合 *)
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
   変数のうち、スキーマの型から到達できないものを曖昧として報告する。
   予約述語(Integral / Fractional)が付いた変数は既定化で決まるので
   対象外にする。免除しないと let ne = 1 != 2 のような、既定化に頼る
   形がすべて落ちる。kept には、まだ Unbound の変数だけを残す。
   到達できない述語つき変数を default_numerics に届け続けるためと、
   Link / Generic になった項目を刈って走査を線形に保つためである
   (台帳は instantiate のたびに伸びる)。刈っても、生きている制約つき
   変数を大量に抱えた宣言では、検査点の数と台帳の長さの積だけ時間が
   かかる。病的な入力では二次になる *)
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

(* ## 8.10 map_generics と 3 つの写像

   `instantiate` / `skolemize` / `subst_params` は、
   どれも型を走査して `Generic` を別の型に置き換える。
   違うのは何に置き換えるかだけなので、走査は `map_generics_with` の 1 つにまとめる。
   `map_generics_with` は `Hashtbl` のメモを持ち、同じ `vid` の `Generic` には常に同じ結果を返す。
   このメモが無いと、`A => A` の 2 つの `A` が別々の型になり、多相が壊れる。

   | 関数 | `Generic` の置き換え先 | 使う場所 |
   |---|---|---|
   | `instantiate` | 現在のレベルの新しい未定変数 | 変数参照(第11章) |
   | `skolemize` | 現在のレベルの新しい剛定数 | インスタンス本体の包摂検査(§11.38) |
   | `subst_params` | 指定された型引数(無ければ新しい変数) | 宣言表の展開(第10章と第11章) |

   ### instantiate は型クラス制約を複製する

   `instantiate` は `new_class_var ~kind:i.vkind ~classes:i.vcls level` で、
   カインドと制約の集合をまとめて複製する。
   `[A: Add] let double(x: A) = x + x` を一般化すると、`A` は `{Add}` を持つ `Generic` になり、
   `double` を使うたびに `{Add}` を持つ新しい未定変数が作られる。
   その変数が `Int32` と単一化されると、`bind` が `add_class` を呼び、
   `Int32` に `Add` のインスタンスがあるかを確かめる。
   制約の検査はこれで完結する。
   この複製が無ければ、制約は使用点に届かない。

   複製した変数に制約が付いていれば、`new_class_var` がそれを台帳にも載せる。
   §8.4 で述べたとおり、一般化点に届かない制約つき変数を宣言の終わりに掃き出し、
   途中の一般化点では曖昧性を調べるためである。
   `instantiate` はプログラム中で最も多く呼ばれる関数なので、台帳が伸び続けないよう、
   `default_numerics` が宣言ごとに台帳を空に戻し、`check_ambiguity` も不要になった項目を刈る。

   ### skolemize は vcls を引き継ぐ

   `skolemize` が作る剛定数は、`vkind` と `vcls` をそのまま引き継ぎ、
   識別子とレベルだけを新しくする。
   `vcls` を落とすと、クラス宣言が期待型に書いた制約が剛定数から消える。
   すると包摂検査は、インスタンス側の推論結果が持つ制約つき変数をその剛定数へ束縛しようとした時点で `add_class` で落ち、
   正しいインスタンスまで「制約を書いてください」と拒否する。

   名前から誤解しやすいが、`skolemize` は注釈つきの let の検査には使わない。
   呼び出し元は第11章の `check_instance_bodies`(§11.38)だけで、
   インスタンスメソッドがクラス宣言の型を満たすかを調べる包摂検査に使う。
   `let f[A: Add](x: A) = ...` の `A` を剛定数にするのは第11章の `make_rigids`(§11.25)である。
   `make_rigids` は `Generic` を写すのではなく、
   `tp_classes` から `vcls` を組み立てて `Rigid` を直接作る。
   第11章が注釈の検査に使う 3 つの関数は `make_rigids` / `open_explicit_eff` / `release_rigids` で、
   本章の `skolemize` はそこに含まれない。

   どちらの経路でも、宣言に書いていない制約は剛定数に付かない。
   そのため、§8.4 の `Rigid` の場合は「`[A: C]` のように制約を書いてください」と案内できる。

   ### ランク 1 多相

   `generalize` を呼ぶのは let 束縛のときだけで、`instantiate` を呼ぶのは変数参照のときだけである。
   ラムダの引数には常に単なる未定変数を割り当てるので、
   引数を 2 つの異なる型で使うと単一化に失敗する。
   この呼び出しの規律によって、多相はランク 1 に限られる。
   量化子を型の中に持たず、`Generic` の印だけで多相を表す設計は、この規律を前提にしている。
   Keleut は多パラメータ型クラスを持たないので(sample.kel:356)、型スキーマ専用のデータ型も要らない。
   本章には `Scheme` に相当する型が出てこない。

   `reset` は台帳を空に戻すだけである。
   呼び出し元は第11章の 2 か所にある。
   `type_check_decls` は検査を始める前の初期化として、警告の一覧や第10章のキューと並べて呼ぶ。
   `process_decls` はパス 2 に入る直前に呼ぶ。
   後者は、パス 1(インスタンスの頭や前方参照のシグネチャの instantiate)で溜まった制約つき変数を、
   宣言ごとの曖昧性の判定に持ち込まないための後始末である。
   1 回の型検査で `reset` は 2 回走る。 *)

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
   (型クラス制約の複製点)。制約つきの変数は台帳へ *)
let instantiate level t =
  map_generics
    (fun i ->
      new_class_var ~kind:i.vkind ~classes:i.vcls level)
    t

(* Generic → 現在のレベルの新しい剛定数。使うのはインスタンス本体の
   包摂検査だけ(§11.38)。注釈の剛定数は elab の make_rigids が作る *)
let skolemize level t = map_generics (fun i -> new_rigid ~kind:i.vkind ~classes:i.vcls level) t

(* Generic → 指定した型(データ宣言・エフェクト宣言のパラメータ置換) *)
let subst_params level args t =
  map_generics
    (fun i -> match List.assoc_opt i.vid args with Some t -> t | None -> new_class_var ~kind:i.vkind ~classes:i.vcls level)
    t

let reset () = class_vars := []
