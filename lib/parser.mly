(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第3章 — 構文解析と脱糖

   第2章 (lexer.ml) が渡してくるのは、ASI で区切りを補い、`{` を3種に分類し終えた
   (トークン, 開始位置, 終了位置) の三つ組の列です。本章はそれを LR(1) で読み、
   第5章 (tree.ml) 以降が扱う小さな AST に落とします。

   このファイルの仕事は2つに分かれます。

   | 仕事 | 何をするか | どこに書いてあるか |
   |---|---|---|
   | 形を認める | Keleut の表面構文を LR(1) の文法として記述する | 文法規則の並び (3.14 以降) |
   | 糖衣を剥がす | 表面の糖衣を AST の素の形へ | 冒頭のヘルパ群 (3.4〜3.10) |

   後者が本章の主題です。Keleut の表面構文は見た目のわりに AST が小さく、
   その差はほぼ全部このファイルの冒頭で吸収されています。脱糖の一覧は計画 §6.4 に
   表としてあり、ヘルパ群はその表をそのまま関数にしたものです。

   逆に、ここで**しない**ことをはっきりさせておきます。名前解決をしません。
   型を見ません。`case` の節が `return` 節なのか操作節なのかも決めません。
   判断材料は「形」だけ — 具体的には「識別子の先頭が大文字か」「ドットの連鎖か」
   「引数が何個か」だけです。それ以外は第11章 (elab.ml) の仕事です。

   > 構文解析器が決めてよいのは形だけ。名前の意味は第11章に渡す。

   骨格は計画時の spike (`doc/log/260829-1-spike/menhir/kel.mly`) をそのまま
   持ってきたものです。spike の時点で `--strict` で conflict 0、sample.kel 全文
   パース済みでした。本文中の [FIX-n] は spike で踏んだ conflict とその修正の
   通し番号で、計画 §6 に同じ番号で理由が書いてあります。
   旧 Orphos 文法は git 履歴の f0cafd4 にあります。

   ### 前章から受け取るもの

   - ASI 適用後のトークン列。改行は意味のある位置にだけ `NL` として残っている
   - `{` は `LBRACE_BLOCK` / `LBRACE_RECORD` / `LBRACE_TYPE` に分類済み (D12)
   - 各トークンに開始位置と終了位置が付いている (D16)

   ### 次章以降へ渡すもの

   - 脱糖済みの `decl list`。第4章 (dump.ml) が S 式で目視でき、
     第11章 (elab.ml) が型と解決結果を書き込む対象になる
   - 全ノードに `Location.span`。エラーメッセージの出所はここで決まる *)

(* ## 3.1 `%parameter` — 注釈の型を外から差し替える

   第1章 (syntax.ml) の AST は `Syntax.Make (Data)` というファンクタの中にあり、
   ノードはすべて `(Data.t, 中身)` の対でした。`Data.t` が「1ノードに貼りつける注釈」で、
   `Data.allocate : Location.span -> t` がその生成器です。

   パーサ側も同じ形にします。menhir の `%parameter` は、生成されるモジュール全体を
   `Make (Data : Syntax.Data)` というファンクタで包む指示です。つまり
   **第1章の `Syntax.Make` と本章の `Parser.Make` は対**であり、
   両方に同じ `Data` を渡すと同じ木の型になります。

   なぜそうするかというと、木を作る人と木に書き込む人が別だからです。
   第5章 (tree.ml) の `ElabData` は `ty_field` と `resolved` という可変フィールドを
   持っていて、第11章 (elab.ml) がそこへ型と解決結果を書きます。パーサはそんな
   フィールドの存在を知る必要がありません。第16章 (driver.ml) が
   `Parser.Make (Tree.ElabData)` を呼ぶ、それだけで接続されます。
   逆に注釈が要らない用途では、第1章の `EmptyData` を渡せばノードは unit になります。

   これが成立するのは `Syntax.Make` が**アプリカティブ**ファンクタだからです。
   OCaml では、同じファンクタに同じ引数を与えた `F(X).t` と `F(X).t` は同じ型です。
   パーサの中で `Syntax.Make(Data).decl` として作られた値が
   `Tree.Tree.decl` としてそのまま elab に渡せるのはこの性質のおかげで、
   もし `Make` が生成的 (ジェネレーティブ) だったらここで型が合わず、
   木の詰め替えという無意味な一往復が要りました。

   代償も書いておきます。文法を触るたびにファンクタ越しの型検査が走るのでビルドが重く、
   型エラーも読みにくくなります (計画のリスク R6)。割に合わなくなったときの退避案は
   「`Data` を `ElabData` に固定して `%parameter` をやめる」ことだ、と計画に書いてあります。 *)
%parameter <Data : Syntax.Data>
%{
(* ## 3.2 dune のラッパーと、空モジュール1個のワークアラウンド

   次の1行は Keleut とも構文解析とも関係のない、ビルド系の傷跡です。

   dune はライブラリを `Diktor` という名前でラップし、中の各モジュールを
   `Diktor__Syntax` のような実名に置き換えます。一方 menhir は、生成したパーサの型を
   ocamlc に推論させて `.mli` に書き出します (dune の menhir ルールはこの型推論を
   既定で回します)。この2つが噛み合わず、推論に使う一時モジュールが
   ライブラリ自身のラッパー名 `Diktor` を参照してしまって壊れる、というのが
   ocaml/dune#2450 です。

   同じ名前の空モジュールを冒頭で1個定義してその名前を局所的に潰す、というのが
   当時から知られている回避策です。計画では dune 3.x なら不要になっているはずだから
   M1 で外してみる、と書きましたが、現在も残っています。外すときは必ずビルドで
   確かめること — これは消しても静かに壊れない類の1行ではなく、消すと壊れる類の1行です。

   続く2つの `open` で、AST の構成子と、意味アクションが投げる `Syntax_error`
   (第1章 syntax.ml で定義) が非修飾で書けるようになります。 *)
module Diktor = struct end

open Syntax
open Syntax.Make(Data)

(* ## 3.3 位置は三つ組で運ぶ (D16)

   旧実装はトークン自身に位置を載せていました (`%token <Location.t> LET` の形)。
   これをやめたのが裁定 D16 です。理由は単純で、まともなエラーメッセージには
   **全ノード**に span が要るからです。ノードの一部にしか位置が無いと、
   後から足すときに全ノードの書き換えになります。MiniLang §17 が
   「型に出所 (ソース位置) を持たせるのは、実用上は最重要の改善点」と書いているのがこれで、
   後付けが高くつくと分かっているものは最初から入れておきます。

   そこで位置は、字句と構文のあいだをトークンとは別に流れます。menhir の伝統 API は
   `(Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a` という形をしていて、位置を
   `Lexing.lexbuf` の可変フィールドから読みます。sedlex はその lexbuf を持たないので、
   第2章 (lexer.ml) は `MenhirLib.Convert.Simplified.traditional2revised` で
   改訂 API — `(unit -> token * position * position) -> 'a` — に変換し、
   (トークン, 開始位置, 終了位置) の三つ組を1個ずつ手渡します。
   この関数呼び出し1つが、字句層と構文層をつなぐ唯一の継ぎ目です。

   この一手間で `$sloc` が本物の位置を返すようになり、意味アクションは `mk $sloc x` と
   書くだけで済みます。旧実装にあった「位置が2トークンぶんずれる」バグ (0.2-9) も、
   位置の出所が1か所になったことで消えました。

   > 位置は全ノードに、最初から。後から足す位置情報には、全ノード書き換えという値札が付く。

   不変条件が1つあります。**新しいノードは必ず `mk` を通す**こと。例外は
   「既にあるノードの位置を借りる」場合だけで、本章では `block_of_items` が
   宣言の位置を借りて `Let` を作る箇所などが該当します (3.7)。借りるのは意図的で、
   `let x = 1` から作った `Let` ノードの位置がその `let` 宣言の位置になるのは自然だからです。 *)
let mk (sp, ep) x = (Data.allocate { Location.start = sp; Location.finish = ep }, x)

(* ## 3.4 大文字であること、そして `dot_select`

   Keleut には名前空間を分ける構文がありません。`Foo.bar` が「モジュール `Foo` の `bar`」
   なのか「変数 `Foo` のフィールド `bar`」なのかは、**先頭が大文字かどうか**だけで決まります。
   `is_upper` はその全判定で、この 1 行がこのファイル中の分岐の大半を支えています。

   ドット連鎖の扱いは spike で最初に転んだ場所です ([FIX-1])。式位置で `long_id` 非終端を
   使うと、`Foo.bar` を読んだ時点で「`long_id` を伸ばす」か「後置の選択に落とす」かが
   決まらず shift/reduce になります。型位置とパターン位置には競合する DOT 規則が無いので
   `long_id` をそのまま使えますが、式位置だけは駄目です。

   そこで文法側は `postfix_exp DOT id` の一様な左再帰チェーンで**全部**食い、仕分けは
   意味アクション `dot_select` の仕事にします。規則はひとつ:
   **先頭の連続する大文字成分 + 直後の1成分をパスに畳み、残りをレコード選択にする**。
   `Db.Conn.exec.x` なら `Db.Conn.exec` がパス、`.x` が選択です。

   `t._N` の脱糖だけは説明が要ります。タプルは第1章のとおり `_item` を**重複させた**行で
   表されており、Scoped Labels の最左一致では `t._item` が常に最初の要素を指します。
   2番目が欲しければ最初の1枚を剥がしてから選ぶ、つまり `(t \ _item)._item` です。
   一般化して `t._N = (t \ _item)` を N 回してから `._item` — この短い再帰が
   タプル射影の全部で、専用の AST ノードも専用の型規則も要りません。
   剥がす側の機構は第8章 (unify.ml) の `rewrite_row` にあります。

   `t.0` と書くと構文エラーになります。`_0` は LOWER_IDENTIFIER なので選択規則に
   そのまま乗りますが、`0` は NUMBER なので乗らないからです。sample.kel:120 の意図どおりで、
   これは実装の都合ではなく仕様です。`is_index_label` が見ているのは
   「先頭が `_` で、残りが 10 進の桁だけ」という綴りの形だけです。 *)
let is_upper s = s <> "" && s.[0] >= 'A' && s.[0] <= 'Z'

let is_index_label s =
  String.length s >= 2 && s.[0] = '_'
  && (let ok = ref true in
      String.iteri (fun i c -> if i > 0 && not (c >= '0' && c <= '9') then ok := false) s;
      !ok)

let dot_select sloc e id =
  match e with
  | (_, Ident (LongId comps)) when List.for_all is_upper comps ->
      mk sloc (Ident (LongId (comps @ [ id ])))
  | _ ->
      if is_upper id then raise (Syntax_error ("レコードのラベルに大文字識別子は使えません: " ^ id))
      else if is_index_label id then
        (* t._N = (t \ _item)^N ._item(§6.4) *)
        let n = int_of_string (String.sub id 1 (String.length id - 1)) in
        let rec strip e n = if n = 0 then e else strip (mk sloc (RecordRestriction (e, "_item"))) (n - 1) in
        mk sloc (RecordSelection (strip e n, "_item"))
      else mk sloc (RecordSelection (e, id))

(* ## 3.5 引数リストは行になる (D5)

   Keleut の関数は多引数ですが、型のほうに多引数の矢印はありません。裁定 D5 は
   「**引数 = 閉じた `_item` 行のレコード**」で、`TArrow` の第1引数はただのレコード型です。
   `record_of_args` がその変換で、`f(a, b)` は `Apply (f, {_item = a, _item = b})` になります。
   ラベル付き引数 `l = e` を書いたときだけラベルが `_item` の代わりに入ります。

   得るものが2つあります。第一に **arity 検査がただの単一化になる**こと —
   引数の個数違いは閉じた行どうしの単一化が勝手に落とします。第二に
   `fst[A, R](t: {_item: A extends R})` のような「タプルの先頭を取る前置多相」が
   同じ機構でそのまま書けることです。タプルと引数リストが同じ表現だからこうなります。

   行の組み方にも意味があります。`row` は末尾から畳むので**先頭の要素が最も外側**の
   `RecordExtend` になり、第14章 (interp.ml) が外側から評価すれば、引数の評価順が
   自然に a → b → c になります。評価順を別途決める必要がありません。

   arity 1 まわりには規約が3つあり、**3つとも別**です。混ぜると壊れます。

   | 書き方 | 脱糖 | 理由 |
   |---|---|---|
   | `f(a)` | `{_item = a}` (1要素の引数行) | 引数は常に行 |
   | `(a)` | `a` そのもの (グループ化) | 括弧はグループ化。1-タプルは `(a,)` |
   | `#Foo(a)` | ペイロード `a` そのもの | 下記 |

   `#Foo(a)` を1要素タプルに包まないのは、式 `#Syntax((l, c))` とパターン
   `case #Syntax(l, c)` が単一化できるようにするためです。両方が「ペイロードは2要素タプル」に
   落ちる必要があり、片方だけ余分に包むと合いません。`variant_payload` の1引数ケースが
   この規約の実体で、同じ規約をパターン側と型側にも置いてあります (3.9)。 *)
let record_of_args sloc args =
  let rec row = function
    | [] -> mk sloc RecordEmpty
    | (label, v) :: tl ->
        let l = match label with Some l -> l | None -> "_item" in
        mk sloc (RecordExtend (row tl, l, v))
  in
  row args

let tuple_exp sloc exps = record_of_args sloc (List.map (fun e -> (None, e)) exps)

let variant_payload sloc = function
  | [ (None, e) ] -> e
  | args ->
      if List.exists (fun (l, _) -> l <> None) args then
        raise (Syntax_error "#Foo(...) にラベル付き引数は使えません")
      else tuple_exp sloc (List.map snd args)

(* ## 3.6 `call` — 先頭が大文字なら構築、小文字なら適用

   呼び出しの `(` を読んだ時点で、それが何なのかは3通りあります。

   - `#Foo(...)` — ヴァリアントの構築。`atom` の `HASH_IDENT` が作った空ペイロードの
     `Variant` を、ここで本物のペイロードに差し替えます (spike [FIX-3]。
     `atom` 側に引数リストを持たせると shift/reduce になります)
   - `Parser.Parser(...)` — パスの最後の成分が大文字なので `Construct`
   - `Parser.bind(...)` — 最後の成分が小文字なので `Apply`

   判定は最後の成分だけを見ます。`Parser.Parser` と `Parser.bind` が同じパス接頭辞を
   持ちながら違う意味になるのはそのためで、「大文字は構築子、小文字は値」という
   Keleut の綴り規約をそのまま利用しています。

   `Construct` だけは引数を行に畳まず、ラベル (`ca_label`) を持ったまま残します。
   構築子のフィールドには宣言側の順序があり、ラベル付き引数を実引数位置へ並べ替えるには
   宣言表が要るからです。並べ替えは第11章 (elab.ml) が行い、結果を第5章 (tree.ml) の
   `resolved` に `RCtor` として書きます。パーサは知らないことを推測せず、素材のまま渡します。 *)
let call sloc callee args =
  match callee with
  | (_, Variant (s, (_, RecordEmpty))) -> mk sloc (Variant (s, variant_payload sloc args))
  | (_, Ident (LongId comps)) when is_upper (List.nth comps (List.length comps - 1)) ->
      mk sloc (Construct (LongId comps, List.map (fun (l, e) -> { ca_label = l; ca_exp = e }) args))
  | _ -> mk sloc (Apply (callee, record_of_args sloc args))

(* ## 3.7 `block_of_items` — 宣言の列を式にする

   `{ ... }` のブロックの中身は、トップレベルと**同じ** `items` 非終端で読みます (3.15)。
   読んだ結果は宣言の列なので、式にするにはここで畳み直します (§4.2)。

   - 末尾の式がブロックの値になる
   - `let` は右側の残り全部を本体にした `Let`。スコープが自然に効く
   - `let rec ... and ...` は `LetRec`
   - 値にならない式が並んだら `Seq` にまとめる
   - 空ブロック `{}` は `RecordEmpty`。Keleut の Unit は空レコードです

   `Seq` の畳み込みが `Seq (e :: es)` の形を見ているのは、`Seq` の入れ子を作らないためです。
   ここで平らにしておくと、第4章 (dump.ml) の出力も第14章 (interp.ml) のループも素直になります。

   位置は借ります (3.3 の例外)。`Let` には `let` 宣言自身の `d` を使うので、これは正確です。
   `Seq` のほうは粗い借り方で、2文なら先頭の式の位置ですが、3文以上を平らに畳むときは
   内側で作った `Seq` の位置を引き継ぐので、結果として2文目の位置が付きます。
   診断に使うには足りない精度で、直すなら `mk sloc` に替えるところです。

   最後の節は、`items` を全位置で共有した代償です。`module` や `type` はブロック内では
   式に落とせないので、ここで構文エラーにするしかありません。
   「文脈違反は elab が検査する」という原則 (計画 §6.1) の例外がこの1行で、
   例外にしている理由は「落とす先が無い」という構造的なものです。 *)
let rec block_of_items sloc items =
  match items with
  | [] -> mk sloc RecordEmpty
  | [ (_, DExp e) ] -> e
  | (_, DExp e) :: rest -> (
      match block_of_items sloc rest with
      | (_, Seq es) as r -> (fst r, Seq (e :: es))
      | r -> (fst e, Seq [ e; r ]))
  | (d, DLet b) :: rest -> (d, Let (b, block_of_items sloc rest))
  | (d, DLetRec bs) :: rest -> (d, LetRec (bs, block_of_items sloc rest))
  | _ :: _ -> raise (Syntax_error "この宣言はブロック内では使えません(let / let rec / 式のみ)")

(* ## 3.8 `with_splice` — 継続を引数の末尾に差し込む

   `with` は Keleut でいちばん効く糖衣です。

   ```
   with x = f(a)
   残りの文…
   ```

   これが `f(a, fn(x) => 残りの文…)` になります。CPS を手で書かずに、
   コールバックを取る API を素直な直列コードのまま書けます。

   実装は「引数行の最内 `RecordEmpty` を `RecordExtend (RecordEmpty, _item, k)` に
   差し替える」だけです。行は末尾から畳まれている (3.5) ので、最内 = 最後の引数であり、
   継続は引数リストの末尾に付きます。「継続が最後に評価される」という評価順も、
   同じ理由で自動的に正しくなります。

   継続の引数の個数が2通りある点が肝です。

   - `pat` が `_` なら **0引数**の継続 `fn() => 残り`
   - それ以外なら **1引数**の継続 `fn(pat) => 残り`

   `with _ = with_file(src)` (sample.kel:416-417) が要求する `body: () => A` と、
   `with x = Parser.bind(...)` (:430) が要求する `(A) => ...` の両方を、同じ糖衣で
   満たすための分岐です。`_` を「値を捨てる1引数」にしてしまうと前者が型付きません。

   右辺が呼び出しでなければエラーにします。行を差し込む先が無いからで、これは
   「パーサが形だけで判断できる」数少ない意味的な検査のひとつです。 *)
let with_splice sloc pat call k_body =
  let k_params = match snd pat with PWildcard -> [] | _ -> [ pat ] in
  let k = mk sloc (Lambda { l_params = k_params; l_body = k_body }) in
  match call with
  | (d, Apply (f, args)) ->
      let rec splice (ad, a) =
        match a with
        | RecordEmpty -> (ad, RecordExtend (mk sloc RecordEmpty, "_item", k))
        | RecordExtend (rest, l, v) -> (ad, RecordExtend (splice rest, l, v))
        | _ -> raise (Syntax_error "with: 呼び出しの引数形が不正です")
      in
      (d, Apply (f, splice args))
  | _ -> raise (Syntax_error "with の右辺は関数呼び出しでなければなりません")

(* ## 3.9 閉じた行と開いた行の分岐点

   ここから3つのヘルパは、タプル・レコード・ヴァリアントの「行を閉じるか開くか」を
   決めます。この選択が第8章 (unify.ml) の単一化と第10章 (exhaust.ml) の網羅性検査に
   そのまま効くので、パーサの中でいちばん意味論に近い場所です。

   - `pat_tuple` の `rest_opt` が `None` なら**閉じた行**。要素数がぴったり合うことを
     単一化が要求します。これがタプルパターンの arity 検査そのものです
   - `Some p` なら尾部を `p` に束縛する。`(x, ...rest)` の形
   - レコードパターン (3.22) は逆に**開いた行が既定**。書いていないフィールドがあっても通ります

   タプルは「全部で何個か」が意味を持ち、レコードは「必要なものがあるか」が意味を持つ、
   という違いを、そのまま行の開閉に写しています。

   `variant_pat_payload` と `variant_ty_payload` は 3.5 の 1 引数規約をパターン側と型側に
   置き直したものです。式・パターン・型の3か所で同じ畳み方をしていることが、
   `#Syntax((l, c))` と `case #Syntax(l, c)` が噛み合う条件です。
   `tuple_ty` が閉じた `EBraceRow` を作るのも同じ理由 — 型位置のタプルにも arity があります。 *)
let pat_tuple sloc pats rest_opt =
  (* rest_opt: None = 閉じた行(arity 検査)、Some p = 尾部束縛 *)
  mk sloc (PRecord (List.map (fun p -> ("_item", p)) pats, rest_opt))

let variant_pat_payload sloc = function
  | [ { cap_label = None; cap_pat = p } ] -> p
  | args ->
      if List.exists (fun a -> a.cap_label <> None) args then
        raise (Syntax_error "#Foo(...) パターンにラベル付き引数は使えません")
      else pat_tuple sloc (List.map (fun a -> a.cap_pat) args) None

let tuple_ty sloc tys = mk sloc (EBraceRow (List.map (fun t -> BField ("_item", t)) tys, None))

let variant_ty_payload sloc = function [ t ] -> t | ts -> tuple_ty sloc ts

(* ## 3.10 `pub` と、`newtype` の右辺を一度生で受ける理由

   `pub` は宣言の前に付く修飾子です。文法で「`pub` 付き」と「無し」の2系統を書くと
   宣言の規則が倍になるので、`decl_body` を作ってから `set_pub` で被せます。
   付けられない宣言 — `type instance` と式文 — はここで弾きます。

   `newtype` の右辺は4形あります。省略・短縮形 `newtype UserId(Int32)`・構築子の並び・
   `???` (未実装の穴)。このうち短縮形は `newtype UserId = UserId(Int32)` の略で、
   **構築子の名前が型の名前と同じ**です。ところが右辺の規則の中に型の名前はありません。
   そこで `nt_rhs_raw` という生の中間形でいったん受け、名前が見えている `decl_body` の
   意味アクションで解釈します (3.17)。文法を分けずに済ませるための、小さいけれど
   有効な逃げ道です。 *)
let set_pub = function
  | DType t -> DType { t with ta_pub = true }
  | DNewtype n -> DNewtype { n with nt_pub = true }
  | DEffect e -> DEffect { e with ef_pub = true }
  | DClass c -> DClass { c with cls_pub = true }
  | DLet (d, b) -> DLet (d, { b with lb_pub = true })
  | DLetRec bs -> DLetRec (List.map (fun (d, b) -> (d, { b with lb_pub = true })) bs)
  | DModule (_, n, ds) -> DModule (true, n, ds)
  | DExtern e -> DExtern { e with ex_pub = true }
  | DInstance _ -> raise (Syntax_error "type instance に pub は付けられません")
  | DExp _ -> raise (Syntax_error "式文に pub は付けられません")

type nt_rhs_raw = RhsNone | RhsShort of field_decl list | RhsCtors of ctor_decl list | RhsHole
%}

(* ## 3.11 トークン表

   上段の 44 個は旧 Orphos の字句から維持したもの、下段の 20 個が Keleut 化で新設した
   ものです。新設側にこの言語の性格が出ています — `{` の3分割 (D12)、
   `\` (レコードからのフィールド除去)、`...` (尾部束縛)、`???` (穴)、そして
   `class` / `instance` / `derive` / `extends` / `extern` / `newtype` / `perform` /
   `resume` / `run` / `pub` のキーワード群。

   トークンに位置のペイロードが**無い**ことに注意してください (D16、3.3)。
   値を運ぶのは `BOOL` / 2種の識別子 / `TEXT` / `NUMBER` / `HASH_IDENT` の6種だけで、
   ほかは名前が全情報です。 *)
%token AND AT ASTERISK BIG_AMPERSAND BIG_EQ BIG_VERTICAL CASE COLON COMMA DOT
%token EFFECT EOF EQ EQ_GREATER EXCLAMATION EXCLAMATION_EQ FN GREATER HANDLE
%token HYPHEN IF LBRACKET LESS LET LOWLINE LPAREN MATCH MODULE NL PLUS RBRACKET
%token REC RPAREN SEMI SOLIDUS TYPE VAL VERTICAL WITH
%token <bool> BOOL
%token <string> LOWER_IDENTIFIER UPPER_IDENTIFIER TEXT
%token <Syntax.number> NUMBER

%token LBRACE_BLOCK LBRACE_RECORD LBRACE_TYPE RBRACE
%token BACKSLASH DOTDOTDOT LESS_EQ GREATER_EQ HOLE
%token CLASS INSTANCE DERIVE EXTENDS EXTERN NEWTYPE PERFORM PUB RESUME RUN
%token <string> HASH_IDENT

(* ## 3.12 開始記号の型と、`Error` という名前の取り合い

   開始記号の型を `Syntax.Make(Data).decl list` と**完全なパスで**書いているのには
   理由があります。menhir はこの型注釈をそのまま、生成する `.mli` のシグネチャに
   書き出します。冒頭の `open` はファンクタ本体の中でしか効かないので、
   シグネチャに現れる型はファンクタの外から辿れるパスでなければなりません。
   非修飾の `decl list` と書くと、生成された `.mli` がコンパイルできません。

   そしてこのパスが 3.1 のアプリカティブ性と繋がります。生成されるのは
   `Parser.Make (Data)` の中の `val program : ... -> Syntax.Make(Data).decl list` で、
   ドライバが `Parser.Make (Tree.ElabData)` を呼ぶと返る型は
   `Syntax.Make(Tree.ElabData).decl list`、すなわち `Tree.Tree.decl list` です。
   詰め替え無しで elab に渡せるのは、この型の等式のおかげです。

   もう1点。menhir は構文エラーを `Error` という名前の例外で投げます。第2章 (lexer.ml) の
   字句エラーが同じ名前だと、ドライバの `try` がどちらを捕まえたのか区別できません。
   だから字句側は `Lex_error` という別の名前にしてあります。第16章 (driver.ml) は
   この2つと、意味アクションが投げる `Syntax_error` の3種を別々に捕まえ、
   字句エラーと構文エラーを言い分けたうえで、どちらも終了コード 2 に揃えます。 *)
%start <Syntax.Make(Data).decl list> program

(* ## 3.13 `--strict` で conflict 0 を保ち続ける

   `lib/dune` は menhir を `--explain --strict` で走らせます。

   menhir は既定では conflict を**警告**にし、記述順と優先順位で黙って解決します。
   つまり conflict を放置した文法は「ビルドは通るが、意味が書いたつもりと違う」状態に
   なります。spike ではこれで実際に転びました — 初稿の文法をそのまま符号化したら
   17 状態が conflict で、しかも黙って動いていたのです。11 個の修正 (本章の [FIX-n]) で
   conflict 0 に到達しています。

   `--strict` は警告をエラーに変え、`--explain` は競合の説明をファイルに書きます。
   前者が無いと、後者を読む機会が来ません。

   conflict 0 は「達成した状態」ではなく「保ち続ける規律」です。1 個許した文法は次の 1 個を
   止められません。とくに reduce/reduce は記述順で黙って倒れるので、
   `let f(x) = e` が関数定義ではなく小文字構築子のパターンとして読まれる、といった事故が
   **テストが通ったまま**起こり得ます (3.16)。

   > conflict は 0 か、そうでないかの二値。1 を許した文法は、次の 1 を止められない。

   代償として、文法の書き方は縛られます。本章の設計判断のうち5つ —
   ドット連鎖を意味アクションに逃がす (3.4)、`#Foo(...)` を後置で受ける (3.6)、
   矢印型を分離する (3.23)、束縛パターンを別言語にする (3.16)、
   レコード型とエフェクト行を1本に統合する (3.23) — は、どれも
   「そう書かないと conflict する」から選ばれた形であって、美意識から選んだ形ではありません。

   投入の時期にも躓きが1つありました。計画では M2 から `--strict` を入れる予定でしたが、
   その時点ではまだ文法が無く、宣言だけあるトークンが未使用警告 → エラーになります。
   実際には文法を書き始める M3 の頭から入れました (実装記録 260829-2 の乖離10)。 *)

%%

(* ## 3.14 文法の骨組み — 区切り、ブレース、パス

   ここから下が文法本体です。まず3つの小さな非終端を用意します。

   `semi` は改行とセミコロンを同一視します。ASI (第2章) が意味のある改行だけを `NL` として
   残しているので、ここで両者を区別する理由がありません。

   `lbrace` は3分割した `{` を再び1つに束ねます。分割は「式位置の `{}` を LR(1) で解く」ために
   必要でしたが、module 本体やレコードパターンのように**どの分類で来ても同じ意味**の
   場所ではまとめて受けます ([FIX-7]: `run h {}` の `{}` は中身が空なので
   `LBRACE_RECORD` に分類されます)。分類は見た目で決まるものであって、
   意味で決まるものではない、という第2章の性質がここに漏れ出しています。

   `long_id` は型位置とパターン位置で使うパスです。式位置では使いません (3.4、[FIX-1])。 *)

%inline semi: NL { () } | SEMI { () }

%inline lbrace:
  | LBRACE_BLOCK  { () }
  | LBRACE_RECORD { () }
  | LBRACE_TYPE   { () }

lower_id: LOWER_IDENTIFIER { $1 }
upper_id: UPPER_IDENTIFIER { $1 }

upper_path:
  | upper_id                { [ $1 ] }
  | upper_path DOT upper_id { $1 @ [ $3 ] }
long_id:
  | lower_id                { LongId [ $1 ] }
  | upper_path              { LongId $1 }
  | upper_path DOT lower_id { LongId ($1 @ [ $3 ]) }

(* ## 3.15 プログラムと宣言

   トップレベル・module 本体・`instance` 本体・ブロックは、**同じ** `items` 非終端で読みます。
   ブロックの中に `module` を書くといった文脈違反は、原則として第11章 (elab.ml) が
   検査します (計画 §6.1)。文法を4種類に割ると、同じ規則を4回書いたうえに
   4通りの conflict の面倒をみることになるからです。

   `items` は余分な `semi` を読み飛ばします。ASI が改行を落とす境目は完全ではないので、
   ここは寛容にしておくのが実際的です。

   `with` の規則が `items` に2本あるのは、この糖衣が「残りの文**全部**」を継続の本体に
   取るからです (3.8)。左再帰では書けず、`WITH pat EQ exp semi items` と右再帰で受けて、
   `items` の解析結果をそのまま `block_of_items` に通します。1本目 — `with` がファイルや
   ブロックの末尾に来た場合 — の継続本体は空レコード、つまり Unit です。

   `pub` は `decl` の階層で被せます (3.10)。`decl_body` の中で `let rec` の `and` の前に
   `semi` を挟んでいないのは意図的で ([FIX-6])、ASI が `and` の前の改行を落とすため
   素直に並べるだけで足ります。`semi?` を足すと shift/reduce になります。 *)

program: items EOF { $1 }

items:
  |                            { [] }
  | semi items                 { $2 }
  | item                       { [ $1 ] }
  | item semi items            { $1 :: $3 }
  | WITH pat EQ exp            { [ mk $sloc (DExp (with_splice $sloc $2 $4 (mk $sloc RecordEmpty))) ] }
  | WITH pat EQ exp semi items { [ mk $sloc (DExp (with_splice $sloc $2 $4 (block_of_items $sloc $6))) ] }

item: decl { $1 } | exp { mk $sloc (DExp $1) }

decl: PUB decl_body { mk $sloc (set_pub $2) } | decl_body { mk $sloc $1 }

decl_body:
  | LET binding                                        { DLet $2 }
  (* spike [FIX-6]: ASI が AND の前の NL を落とすので semi は挟まない *)
  | LET REC binding and_bindings                       { DLetRec ($3 :: $4) }
  | TYPE upper_id typarams_opt kind_annot_opt EQ ty
      { DType { ta_pub = false; ta_name = $2; ta_params = $3; ta_kind = $4; ta_body = $6 } }
  | TYPE CLASS upper_id typarams class_body
      { let vals, derives = $5 in
        DClass { cls_pub = false; cls_name = $3; cls_params = $4; cls_vals = vals; cls_derives = derives } }
  | TYPE INSTANCE upper_id LBRACKET ty_args RBRACKET instance_body
      { DInstance { ins_class = $3; ins_args = $5; ins_body = $7 } }
  | NEWTYPE upper_id typarams_opt newtype_rhs
      { let rhs =
          match $4 with
          | RhsNone -> NtCtors []
          | RhsHole -> NtHole
          | RhsCtors cs -> NtCtors cs
          (* newtype UserId(Int32) = newtype UserId = UserId(Int32) の略記(§6.4) *)
          | RhsShort fields -> NtCtors [ { cd_name = $2; cd_fields = fields } ]
        in
        DNewtype { nt_pub = false; nt_name = $2; nt_params = $3; nt_rhs = rhs } }
  | EFFECT upper_id typarams_opt EQ eff_decl_body
      { DEffect { ef_pub = false; ef_name = $2; ef_params = $3; ef_ops = $5 } }
  | MODULE upper_id module_body                        { DModule (false, $2, $3) }
  | EXTERN TEXT LET extern_sig
      { let name, tparams, params, (ret, eff) = $4 in
        DExtern { ex_pub = false; ex_abi = $2; ex_name = name; ex_tparams = tparams; ex_params = params;
                  ex_ret = ret; ex_eff = eff } }

and_bindings:
  |                          { [] }
  | AND binding and_bindings { $2 :: $3 }

(* ## 3.16 束縛 — パターンの言語を2つに分ける

   `binding` には2形あります。関数形 `f[T](x, y): R @ E = body` と、
   パターン束縛形 `p: T = e` です。

   ここは spike でいちばん危なかった箇所です ([FIX-5])。節のパターン (`pat`、3.22) は
   `case print(m)` のように**小文字**を構築子の頭に許します — `print` が操作名なのか
   変数なのかはパーサには分からないので、形としては受けるしかありません。
   一方 `let f(x) = e` は関数定義です。同じ `pat` を束縛側でも使うと、この2つが
   reduce/reduce で衝突します。しかも reduce/reduce は記述順で黙って倒れるので、
   `--strict` が無ければ「動くが `let f(x) = e` の意味が違う」文法が出来上がります。

   解決は文法を分けることでした。`bind_pat` (3.22) は `_` / 変数 / **大文字頭**の構築子 /
   レコード / タプルだけを受け、小文字頭の呼び出し形を持ちません。同じ「パターン」という
   言葉で呼ばれる2つのものが、置かれる位置によって別の言語である、というのが事実です。

   > 同じ見た目の構文でも、置かれる位置が違えば別の言語になることがある。

   尾部の注釈は `sig_tail` にまとめてあります ([FIX-9])。返り値の型だけ、エフェクト行だけ、
   両方、どれも書かない、の4通りです。`ty_ret` が `union_ty` と `arrow_ty` を分けて
   並べているのは 3.23 の矢印分離の帰結で、`@` を書けるのは返り値が矢印でないときだけです
   (矢印を返すなら `@` は括弧の中に書きます)。`extern` のシグネチャ (`extern_sig`) は
   本体を持たない `binding` の頭で、同じ `sig_tail` を共有します。 *)

binding:
  | lower_id typarams_opt LPAREN params RPAREN sig_tail EQ exp
      { let ret, eff = $6 in
        mk $sloc { lb_pub = false; lb_name = mk $sloc (PVar $1); lb_tparams = $2; lb_params = Some $4;
                   lb_ret = ret; lb_eff = eff; lb_body = $8 } }
  | bind_pat annot_opt EQ exp
      { mk $sloc { lb_pub = false; lb_name = $1; lb_tparams = []; lb_params = None;
                   lb_ret = $2; lb_eff = None; lb_body = $4 } }

sig_tail:
  |              { (None, None) }
  | AT eff       { (None, Some $2) }
  | COLON ty_ret { $2 }
ty_ret:
  | union_ty        { (Some $1, None) }
  | union_ty AT eff { (Some $1, Some $3) }
  | arrow_ty        { (Some $1, None) }

annot_opt: { None } | COLON ty { Some $2 }

extern_sig: lower_id typarams_opt LPAREN params RPAREN sig_tail { ($1, $2, $4, $6) }

(* ## 3.17 宣言の細部 — 共有できるものは共有する

   `module_body` と `instance_body` は `items` を、`class_body` と `eff_decl_body` は
   専用の非終端を使います。前2つは中身が普通の宣言列ですが、クラス本体は `val` と
   `derive` しか、`effect` 本体は `op: ty` しか取れないからです。`class_items` が
   `Either` で2種類を仕分けているのは、1回の走査で `cls_vals` と `cls_derives` に
   振り分けるためです。

   カンマ区切りのリストは**すべて末尾カンマを許します**。
   `X | X COMMA | X COMMA list` という3択の形なら、`(a)` と `(a,)` を意味アクションで
   区別できて conflict も出ません。sample.kel:397 の effect 本体や :512-515 の
   パラメータリストに実例があります。同じ手口が `pp_items` の真偽値にも出てきます (3.22)。

   型パラメータ束縛子 (`typaram`) は名前・アリティ・クラス制約の3点セットです。
   `F[_]` と書いたときだけ `hkt_opt` が正の数になり、その場でカインドが `KArrow` に
   決まります (D7)。`[A]` や `[h]` のような裸の束縛子は字句だけではカインドが決まらない —
   行変数なのか型なのかは使われ方で決まる — ので、第1章のカインド変数に委ねます。
   `ty_ident` が大文字も小文字も受けるのは、リージョン変数 `h` が小文字で書かれるからです。

   `newtype_rhs` の4形は 3.10 のとおり `nt_rhs_raw` で運びます。
   `params` の `param` は `pat annot_opt` で、注釈があれば `PAnnot` で包むだけ。
   その注釈が skolem 化されるかどうかは第11章の判断です。 *)

module_body:   lbrace items RBRACE { $2 }
instance_body: lbrace items RBRACE { $2 }

class_body: lbrace class_items RBRACE { $2 }
class_items:
  |                             { ([], []) }
  | semi class_items            { $2 }
  | class_item                  { (match $1 with Either.Left v -> ([ v ], []) | Either.Right d -> ([], [ d ])) }
  | class_item semi class_items
      { let vals, derives = $3 in
        match $1 with Either.Left v -> (v :: vals, derives) | Either.Right d -> (vals, d :: derives) }
class_item:
  | VAL lower_id typarams_opt COLON ty { Either.Left { cv_name = $2; cv_tparams = $3; cv_ty = $5 } }
  | DERIVE lower_id                    { Either.Right $2 }

newtype_rhs:
  |                           { RhsNone }
  | LPAREN ctor_fields RPAREN { RhsShort $2 }
  | EQ ctors                  { RhsCtors $2 }
  | EQ HOLE                   { RhsHole }

ctors: ctor { [ $1 ] } | ctor VERTICAL ctors { $1 :: $3 }
ctor:
  | upper_id                           { { cd_name = $1; cd_fields = [] } }
  | upper_id LPAREN ctor_fields RPAREN { { cd_name = $1; cd_fields = $3 } }
ctor_fields: { [] } | ctor_field_list { $1 }
ctor_field_list:
  | ctor_field                       { [ $1 ] }
  | ctor_field COMMA                 { [ $1 ] }
  | ctor_field COMMA ctor_field_list { $1 :: $3 }
ctor_field: ty { { fd_label = None; fd_ty = $1 } } | lower_id COLON ty { { fd_label = Some $1; fd_ty = $3 } }

eff_decl_body: lbrace eff_ops RBRACE { $2 }
eff_ops: { [] } | eff_op_list { $1 }
eff_op_list:
  | eff_op                   { [ $1 ] }
  | eff_op COMMA             { [ $1 ] }
  | eff_op COMMA eff_op_list { $1 :: $3 }
eff_op: lower_id COLON ty { ($1, $3) }

typarams_opt: { [] } | typarams { $1 }
typarams: LBRACKET typaram_list RBRACKET { $2 }
typaram_list: typaram { [ $1 ] } | typaram COMMA typaram_list { $1 :: $3 }
typaram: ty_ident hkt_opt cls_opt { { tp_name = $1; tp_arity = $2; tp_classes = $3 } }
ty_ident: lower_id { $1 } | upper_id { $1 }
hkt_opt: { 0 } | LBRACKET lowline_list RBRACKET { $2 }
lowline_list: LOWLINE { 1 } | LOWLINE COMMA lowline_list { 1 + $3 }
cls_opt: { [] } | COLON cls_list { $2 }
cls_list: upper_id { [ LongId [ $1 ] ] } | upper_id PLUS cls_list { LongId [ $1 ] :: $3 }

kind_annot_opt: { None } | COLON upper_id { Some $2 }

params: { [] } | param_list { $1 }
param_list:
  | param                  { [ $1 ] }
  | param COMMA            { [ $1 ] }
  | param COMMA param_list { $1 :: $3 }
param: pat annot_opt { match $2 with None -> $1 | Some t -> mk $sloc (PAnnot ($1, t)) }

(* ## 3.18 式の優先順位

   優先順位は非終端の階層で表し、`%left` のような優先順位宣言は使いません。
   曖昧な文法を宣言で押さえ込むと、`--strict` が沈黙してしまうからです (3.13)。
   弱いほうから、`fn` → 後置 `match` / `handle` → `||` → `&&` → 比較 → 加減 → 乗除 →
   前置 → 後置 → アトムの順に並びます。

   後置の `match` / `handle` が最弱である帰結として、`x match {...} + 1` は書けません。
   `(x match {...}) + 1` と括弧が要ります。Scala と同じ選択で、仕様側の §12 に記録済みです。

   比較は**非結合**です。`a < b < c` は文法の段階で落ちます。

   単項マイナスは `HYPHEN NUMBER` の形でだけ受け、その場で負リテラルに畳みます。
   AST に単項マイナス演算子は存在しません (§5.5、sample.kel:72)。符号を字句側で扱うと
   `1-2` が「1 と -2 の並置」に化けるので、その分担を第2章から引き取っています。
   二項の `-` (sample.kel:260 の `is_even(0 - n)` がその用例) と併存して
   conflict しないことは実測済みです。 *)

exp:
  | FN LPAREN params RPAREN EQ_GREATER exp { mk $sloc (Lambda { l_params = $3; l_body = $6 }) }
  | postfixed                              { $1 }

postfixed:
  | postfixed MATCH clause_body  { mk $sloc (Match ($1, $3)) }
  | postfixed HANDLE clause_body { mk $sloc (Handle ($1, $3)) }
  | or_exp                       { $1 }

or_exp:  or_exp BIG_VERTICAL and_exp   { mk $sloc (BinOp ($1, Or, $3)) } | and_exp { $1 }
and_exp: and_exp BIG_AMPERSAND cmp_exp { mk $sloc (BinOp ($1, And, $3)) } | cmp_exp { $1 }
cmp_exp: add_exp cmp_op add_exp        { mk $sloc (BinOp ($1, $2, $3)) } | add_exp { $1 }
%inline cmp_op:
  | BIG_EQ { Eq } | EXCLAMATION_EQ { Ne } | LESS { Lt } | LESS_EQ { Le }
  | GREATER { Gt } | GREATER_EQ { Ge }
add_exp: add_exp add_op mul_exp { mk $sloc (BinOp ($1, $2, $3)) } | mul_exp { $1 }
%inline add_op: PLUS { Add } | HYPHEN { Sub }
mul_exp: mul_exp mul_op prefix_exp { mk $sloc (BinOp ($1, $2, $3)) } | prefix_exp { $1 }
%inline mul_op: ASTERISK { Mul } | SOLIDUS { Div }
prefix_exp:
  | EXCLAMATION prefix_exp { mk $sloc (Not $2) }
  (* 符号は parser が畳む(§5.5)。AST に単項マイナス演算子は存在しない *)
  | HYPHEN NUMBER          { mk $sloc (Number { $2 with n_text = "-" ^ $2.n_text }) }
  | postfix_exp            { $1 }

(* ## 3.19 後置とアトム

   後置は3種 — ドット選択 (3.4)、`\` によるフィールド除去、そして呼び出し (3.6) です。
   Keleut に**並置適用が無い**ので、`f (x)` の `(` が呼び出しなのかグループ化なのかで
   迷う余地がありません。これが式の `(` を素直に読める理由です。

   `atom` の `#Ident` は空ペイロードの `Variant` として作り、引数が付いていれば後置の
   呼び出し規則が `call` で差し替えます (3.6、[FIX-3])。

   `resume` の引数だけは `record_of_args` を通しません (§6.2)。`resume(e)` の `e` は
   「操作の返り値そのもの」であって引数リストではないからで、`{_item = e}` に包むと
   第11章で操作の返り値型と単一化できません。引数は高々1個、0個なら `Resume None` です。
   この形が第14章 (interp.ml) のアフィンな resume にそのまま対応します。

   `block` は `LBRACE_BLOCK` だけを受けますが、`run h {}` の `{}` は中身が空なので
   字句側で `LBRACE_RECORD` に分類されます。だから `run_body` は3種を束ねた `lbrace` で
   受けます ([FIX-7]、3.14)。 *)

postfix_exp:
  | postfix_exp DOT lower_id            { dot_select $sloc $1 $3 }
  | postfix_exp DOT upper_id            { dot_select $sloc $1 $3 }
  | postfix_exp BACKSLASH lower_id      { mk $sloc (RecordRestriction ($1, $3)) }
  | postfix_exp LPAREN call_args RPAREN { call $sloc $1 $3 }
  | atom                                { $1 }

atom:
  | NUMBER { mk $sloc (Number $1) }
  | TEXT   { mk $sloc (Text $1) }
  | BOOL   { mk $sloc (Bool $1) }
  | HOLE   { mk $sloc Hole }
  | lower_id                                   { mk $sloc (Ident (LongId [ $1 ])) }
  | upper_id                                   { mk $sloc (Ident (LongId [ $1 ])) }
  | HASH_IDENT                                 { mk $sloc (Variant ($1, mk $sloc RecordEmpty)) }
  | PERFORM perform_op LPAREN call_args RPAREN { mk $sloc (Perform ($2, record_of_args $sloc $4)) }
  | RESUME LPAREN call_args RPAREN
      { (* 引数を record_of_args に通さない(§6.2): ペイロードは操作の返り値そのもの *)
        match $3 with
        | [] -> mk $sloc (Resume None)
        | [ (None, e) ] -> mk $sloc (Resume (Some e))
        | _ -> raise (Syntax_error "resume の引数は高々1個です") }
  | RUN lower_id run_body                      { mk $sloc (Run ($2, $3)) }
  | block                                      { $1 }
  | record_exp                                 { $1 }
  | paren_exp                                  { $1 }

perform_op: long_id { $1 }

block: LBRACE_BLOCK items RBRACE { block_of_items $sloc $2 }
run_body: lbrace items RBRACE { block_of_items $sloc $2 }

call_args: { [] } | arg_list { $1 }
arg_list:
  | arg                { [ $1 ] }
  | arg COMMA          { [ $1 ] }
  | arg COMMA arg_list { $1 :: $3 }
arg: lower_id EQ exp { (Some $1, $3) } | exp { (None, $1) }

(* ## 3.20 レコード式と括弧

   レコード式は5形です。空、`extends` だけ、フィールドの並び、並び + `extends`、
   そして更新 `{base with l = e}`。`extends` は「残りの行をこの式から取る」で、
   フィールドを外側から順に積み上げます。

   更新だけは `RecordUpdate` として AST に残します (計画 §6.4 の「脱糖しないもの」)。
   拡張 (`RecordExtend`) が「同じラベルをもう1枚重ねる」のに対し、更新は
   「既にあるラベルを書き換える」という別の操作だからです — 最左一致の下では
   この2つは違う型を持ちます。`{base with ...}` の `base` が実質 `lower_id` 1個に
   限られるのは字句分類の帰結です。`{` の直後に来るものが分類を決める (§5.3) ので、
   ここに任意の式は置けません。

   パンニング `{a, b}` は `{a = a, b = b}` に展開します。式でもパターンでも同じ規則です。

   括弧は3形。`()` は空レコード (Unit)、`(e)` は**グループ化**、`(e,)` と
   `(e1, e2, ...)` がタプルです。3.5 の表のとおり、式位置の `(e)` を1-タプルにしないことが
   ここで効いています — そして**型位置の `(A)` は逆に常に1-タプル**です (3.23)。
   同じ括弧が式と型で違う意味を持つのは気持ちの良い設計ではありませんが、
   式では括弧がグループ化として必要で、型では `(A) => B` の引数リストと形を揃えたい、
   という両立しない要求から出た裁定です (§12 に記録)。 *)

record_exp:
  | LBRACE_RECORD RBRACE                        { mk $sloc RecordEmpty }
  | LBRACE_RECORD EXTENDS exp RBRACE            { $3 }
  | LBRACE_RECORD field_list RBRACE             { record_of_args $sloc (List.map (fun (l, e) -> (Some l, e)) $2) }
  | LBRACE_RECORD field_list EXTENDS exp RBRACE
      { let rec row = function
          | [] -> $4
          | (l, v) :: tl -> mk $sloc (RecordExtend (row tl, l, v))
        in
        row $2 }
  | LBRACE_RECORD exp WITH field_list RBRACE
      { (* {base with l = e}: base は字句分類の帰結で実質 lower_id 1個(§5.3) *)
        List.fold_left (fun acc (l, v) -> mk $sloc (RecordUpdate (acc, l, v))) $2 $4 }
field_list:
  | field                  { [ $1 ] }
  | field COMMA            { [ $1 ] }
  | field COMMA field_list { $1 :: $3 }
field:
  | lower_id EQ exp { ($1, $3) }
  | lower_id        { ($1, mk $sloc (Ident (LongId [ $1 ]))) } (* パンニング {a, b} = {a = a, b = b} *)

paren_exp:
  | LPAREN RPAREN                    { mk $sloc RecordEmpty }
  | LPAREN exp RPAREN                { $2 } (* グループ化。タプルにしない(§6.4) *)
  | LPAREN exp COMMA RPAREN          { tuple_exp $sloc [ $2 ] }
  | LPAREN exp COMMA exp_list RPAREN { tuple_exp $sloc ($2 :: $4) }
exp_list:
  | exp                { [ $1 ] }
  | exp COMMA          { [ $1 ] }
  | exp COMMA exp_list { $1 :: $3 }

(* ## 3.21 節列 — 空を許す

   `match` の節と `handle` の節は**同じ** `clause` 非終端です。`return` / `cancel` /
   `Console.write` のような操作名は、すべて `PCtor` の頭として受かります。
   どれがどれなのかの分類は第11章 (elab.ml) が行い、結果を第5章 (tree.ml) の
   `resolved` に書きます (3.6 と同じ分担)。

   節の間に区切りを書かないのは、ASI が `case` の前の改行を落とすからです
   ([FIX-8]: `CASE` は「文を始められるトークン」の集合に入っていません)。

   そして `clauses` は**空を許します**。`n match {}` — 節がゼロ個の `match` です。
   これは書き間違いではなく、`Never` (構築子を持たない型) の値に対する正しい網羅的な
   `match` です。値が存在しないので、扱うべき場合もありません。

   ここは実装記録 260829-2 の乖離9 に対応します。文法で空を許すだけでは足りず、
   第10章 (exhaust.ml) の網羅性判定も直しました。Maranget の complete 判定は
   ふつう「構築子の根が空でないこと」を条件に含めますが (MiniLang:1727 の
   `roots.nonEmpty` がそれです)、`Never` の節ゼロではその条件が誤って「非網羅」を出します。
   シグネチャが空だと分かっているなら、根が空でも網羅です。

   > 「ゼロ個」を特別扱いしない設計は、たいてい「ゼロ個」で一度は転ぶ。 *)

clause_body: lbrace clauses RBRACE { $2 }
clauses: { [] } | clause clauses { $1 :: $2 } (* 空 = Never の節ゼロ match *)
clause: CASE pat guard_opt EQ_GREATER exp { mk $sloc { cl_pat = $2; cl_guard = $3; cl_body = $5 } }
guard_opt: { None } | IF exp { Some $2 }

(* ## 3.22 パターン — 2つの言語

   上が節のパターン `pat`、下が束縛のパターン `bind_pat` です。分けた理由は 3.16 に
   書いたとおりで、`pat` だけが小文字を頭に持つ呼び出し形 (`case print(m)` のため) を
   持ちます。

   `pat` の `long_id` 単独ケースが、小文字1成分なら変数、それ以外なら引数ゼロの
   構築子パターンに落ちるのは、3.4 と同じ大文字性の判定です。

   レコードパターンは**開いた行が既定**です (§4.2)。`rest` が `None` のときに
   `PWildcard` を尾部へ置いているのがそれで、書いていないフィールドは無視されます。
   `{x}` と書いたときの `{` は字句側で `LBRACE_BLOCK` に分類されてしまうため、
   ここも `lbrace` で3種を束ねて受けます (§5.3)。

   タプルパターンは逆に**閉じた行**です (3.9)。`(p)` はグループ化、`(p,)` が1-タプル、
   `(x, ...rest)` が尾部束縛。`pp_items` の3つ目の要素 (真偽値) は「カンマを見たか」を
   運ぶためだけにあり、`(p)` と `(p,)` を意味アクションで区別するのに使います
   (3.17 の末尾カンマと同じ手口です)。 *)

pat:
  | LOWLINE                           { mk $sloc PWildcard }
  | NUMBER                            { mk $sloc (PNumber $1) }
  | HYPHEN NUMBER                     { mk $sloc (PNumber { $2 with n_text = "-" ^ $2.n_text }) }
  | TEXT                              { mk $sloc (PText $1) }
  | BOOL                              { mk $sloc (PBool $1) }
  | long_id
      { match $1 with
        | LongId [ x ] when not (is_upper x) -> mk $sloc (PVar x)
        | li -> mk $sloc (PCtor (li, [])) }
  | long_id LPAREN pat_args RPAREN    { mk $sloc (PCtor ($1, $3)) }
  | HASH_IDENT                        { mk $sloc (PVariant ($1, mk $sloc (PRecord ([], None)))) }
  | HASH_IDENT LPAREN pat_args RPAREN { mk $sloc (PVariant ($1, variant_pat_payload $sloc $3)) }
  | record_pat                        { $1 }
  | paren_pat                         { $1 }

(* spike [FIX-5]: let 束縛のパターン: 小文字頭の呼び出し形を持たない *)
bind_pat:
  | LOWLINE                            { mk $sloc PWildcard }
  | lower_id                           { mk $sloc (PVar $1) }
  | upper_path                         { mk $sloc (PCtor (LongId $1, [])) }
  | upper_path LPAREN pat_args RPAREN  { mk $sloc (PCtor (LongId $1, $3)) }
  | record_pat                         { $1 }
  | paren_pat                          { $1 }

pat_args: { [] } | pat_arg_list { $1 }
pat_arg_list:
  | pat_arg                    { [ $1 ] }
  | pat_arg COMMA              { [ $1 ] }
  | pat_arg COMMA pat_arg_list { $1 :: $3 }
pat_arg: lower_id EQ pat { { cap_label = Some $1; cap_pat = $3 } } | pat { { cap_label = None; cap_pat = $1 } }

record_pat: lbrace rp_items RBRACE
  { let fields, rest = $2 in
    mk $sloc (PRecord (fields, Some (match rest with Some r -> r | None -> mk $sloc PWildcard))) }
rp_items:
  |                            { ([], None) }
  | DOTDOTDOT lower_id         { ([], Some (mk $sloc (PVar $2))) }
  | pat_field                  { ([ $1 ], None) }
  | pat_field COMMA rp_items   { let fs, r = $3 in ($1 :: fs, r) }
pat_field:
  | lower_id EQ pat { ($1, $3) }
  | lower_id        { ($1, mk $sloc (PVar $1)) } (* パンニング *)

paren_pat: LPAREN pp_items RPAREN
  { match $2 with
    | [ p ], None, false -> p
    | pats, rest, _ -> pat_tuple $sloc pats rest }
pp_items:
  |                        { ([], None, true) }
  | DOTDOTDOT lower_id     { ([], Some (mk $sloc (PVar $2)), true) }
  | pat                    { ([ $1 ], None, false) }
  | pat COMMA pp_items     { let ps, r, _ = $3 in ($1 :: ps, r, true) }

(* ## 3.23 型式 — 矢印を分け、ブレースを統合する

   型のところで spike が2回転びました。どちらも「1本の規則にまとめたい」という欲から
   出た conflict です。

   1つ目 ([FIX-2])。括弧型を単一の規則にして矢印もそこで扱おうとすると、
   `(A) => B | C`、`((A) => B)[C]`、入れ子の矢印に付く `@` の3か所で conflict します。
   だから `arrow_ty` を `ty` の直下に分離しました。裁定は
   **`@` は直前 (最内) の矢印に結合し、曖昧な位置は括弧を要求する**です。
   `arrow_ret` の矢印ケースにだけ `@` が無いのがその現れで、入れ子矢印の外側に `@` を
   書きたければ括弧で囲みます (§6.3。sample.kel の用例はすべて括弧済みでした)。

   2つ目 ([FIX-2b][FIX-10])。レコード型 `{x: Int32}` とエフェクト行 `{Print, Log}` を
   別の非終端にすると reduce/reduce になります。`{` を読んだ時点ではどちらか分からない
   からです。そこで `brace_ty` 1本に統合し、要素は `l: T` (レコード型のフィールド) か
   `Name[args]` (エフェクトラベル、または splice される行エイリアス) の2択とし、
   **どちらの意味なのかは第11章が要素の形から判定します**。おかげで `@ {}`、
   `@ {Print extends E}`、`{ReqId, Logger, Tracer}` (sample.kel:446)、`effect` 宣言の本体が、
   全部同じ規則に乗ります。

   > 文法で決まらないものを文法で決めようとすると conflict になる。
   > 決めずに運んで、意味の層で決める。

   残りは短く。型位置の `(A)` は常に1-タプル `{_item: A}` です (3.20、§12)。
   `#Foo(A, B)` は 3.5 と同じ規約で畳みます。カインド注釈は `COLON upper_id` としか
   書いておらず、`Type` なのか `EffectRow` なのかの解釈は第11章に任せます —
   ここでもパーサは形しか見ません。 *)

ty: union_ty { $1 } | arrow_ty { $1 }

arrow_ty: LPAREN ty_list0 RPAREN EQ_GREATER arrow_ret
  { let ret, eff = $5 in
    mk $sloc (EArrow ($2, ret, eff)) }
arrow_ret:
  | union_ty eff_opt { ($1, $2) }
  | arrow_ty         { ($1, None) } (* 入れ子 arrow の外側には @ を書けない(要括弧、§6.3) *)
eff_opt: { None } | AT eff { Some $2 }

union_ty:
  | union_ty VERTICAL app_ty { match $1 with (_, EUnion ts) -> mk $sloc (EUnion (ts @ [ $3 ])) | t -> mk $sloc (EUnion [ t; $3 ]) }
  | app_ty                   { $1 }

app_ty:
  | atom_ty                           { $1 }
  | atom_ty LBRACKET ty_args RBRACKET { mk $sloc (EApply ($1, $3)) }

ty_args: ty_arg { [ $1 ] } | ty_arg COMMA ty_args { $1 :: $3 }
ty_arg: ty { $1 } | LOWLINE { mk $sloc EHole }

atom_ty:
  | long_id                           { mk $sloc (EIdent $1) }
  | HASH_IDENT                        { mk $sloc (EVariantCase ($1, None)) }
  | HASH_IDENT LPAREN ty_list0 RPAREN
      { match $3 with
        | [] -> mk $sloc (EVariantCase ($1, None))
        | ts -> mk $sloc (EVariantCase ($1, Some (variant_ty_payload $sloc ts))) }
  | brace_ty                          { $1 }
  | LPAREN ty_list0 RPAREN            { tuple_ty $sloc $2 } (* 型位置の (A) は常に 1-タプル(§12) *)

ty_list0: { [] } | ty_list { $1 }
ty_list:
  | ty               { [ $1 ] }
  | ty COMMA         { [ $1 ] }
  | ty COMMA ty_list { $1 :: $3 }

brace_ty:
  | lbrace RBRACE                            { mk $sloc (EBraceRow ([], None)) }
  | lbrace EXTENDS ty RBRACE                 { mk $sloc (EBraceRow ([], Some $3)) }
  | lbrace brace_item_list RBRACE            { mk $sloc (EBraceRow ($2, None)) }
  | lbrace brace_item_list EXTENDS ty RBRACE { mk $sloc (EBraceRow ($2, Some $4)) }
brace_item_list:
  | brace_item                       { [ $1 ] }
  | brace_item COMMA                 { [ $1 ] }
  | brace_item COMMA brace_item_list { $1 :: $3 }
brace_item:
  | lower_id COLON ty { BField ($1, $3) }   (* レコード型のフィールド *)
  | eff_name          { let li, args = $1 in BLabel (li, args) }   (* エフェクト行の要素 *)

eff:
  | eff_name { let li, args = $1 in
               match args with [] -> mk $sloc (EIdent li) | _ -> mk $sloc (EApply (mk $sloc (EIdent li), args)) }
  | brace_ty { $1 }
eff_name:
  | long_id                           { ($1, []) }
  | long_id LBRACKET ty_args RBRACKET { ($1, $3) }
