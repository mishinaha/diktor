(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第10章 — 網羅性検査 (Maranget)

   `match` が全部のケースを覆っているか、どの節も到達できるかを調べます。
   出典は Luc Maranget, Warnings for pattern matching (JFP 2007)。
   お手本 MiniLang §12 (MiniLang.scala:1594-1790) の移植で、骨格 —
   specialize と default という 2 つの行列操作、そこから出るアルゴリズム I と
   アルゴリズム U — はそのままです。計画 §7.5 に当たります。

   ## 前の章から受け取るもの

   - 第5章 (tree.ml) の精緻化木。`PCtor` は `Tree.get_resolved` に書かれた
     `RCtorPat` を読んで展開するので、**この検査は elab がパターンを
     精緻化したあとでしか動きません**。木だけではコンストラクタが誰のものか
     分かりません。
   - 第6章 (decls.ml) の宣言表。`Decls.datas` と `Decls.ctor_owner` が
     「この型のコンストラクタは全部でこれだけ」という完全シグネチャの出所です。
   - 第8章 (unify.ml)。行を閉じる 1 か所だけで `unify` を呼びます。
     この章で型を書き換えるのはそこだけで、あとはすべて読むだけです。

   ## 次の章へ渡すもの

   - 第11章 (elab.ml) は `match` を見つけるたびに `queue` へ積み、
     束縛の一般化の直前に `drain` して警告文字列のリストを受け取ります。
   - 第16章 (driver.ml) がそれを警告として出し、`--strict-exhaustive`
     が指定されていればエラー化します。網羅性も到達不能も**既定では警告**です。

   ## この章の地図

   | 節 | 中身 |
   |---|---|
   | §10.1 | usefulness — 1 つの述語から 2 つの答えが出る |
   | §10.2-10.3 | 内部パターン `ipat` と、木からの変換 |
   | §10.4-10.6 | コンストラクタ・レコードの整列・`specialize` / `default` |
   | §10.7-10.8 | 完全シグネチャと反例の組み立て |
   | §10.9 | 構造的ヴァリアントの行を閉じる |
   | §10.10-10.11 | アルゴリズム I (非網羅) と U (冗長) |
   | §10.12 | 反例の表示 |
   | §10.13 | 遅延キュー — なぜ `match` の瞬間に検査しないのか | *)

(* ## 10.1 usefulness — 1 つの述語から 2 つの答えが出る

   Maranget の中心概念はひとつだけです。

   > パターン行列 `P` に対してベクトル `q` が *useful* とは、
   > 「`P` のどの行にもマッチしないが `q` にはマッチする値」が存在すること。

   この述語を 2 通りに使うと、欲しい検査が両方出ます。

   - **網羅性**: 全部ワイルドカードのベクトルが useful なら非網羅。
     しかも「どんな値が漏れているか」を構成できるので、警告に反例を載せられます。
   - **到達可能性**: i 番目の節が、それより前の節の行列に対して useful でなければ、
     その節にしか来ない値は存在しない — つまり冗長です。

   実装は行列に対する 2 つの操作だけでできています。

   - `specialize c P` — 先頭列がコンストラクタ `c` の行だけ残し、`c` の引数を
     先頭に展開する
   - `default_matrix P` — 先頭列がワイルドカードの行だけ残し、先頭列を落とす

   **再帰型でも停止します。** コンストラクタごとの再帰は「シグネチャが roots に
   含まれる」ときにしか起きず、roots はパターンに実際に現れたコンストラクタの
   集合ですから、再帰の深さはパターンの深さで抑えられます。`List` のような
   無限に深い型に対して検査が発散しないのはこの理由です。

   > 深さを決めるのは型ではなくパターン。だから再帰型でも止まる。 *)

open Aux
open Syntax
open Type
module T = Tree.Tree

(* ## 10.2 内部パターン `ipat` — 1 列の行列に載せる正規形 (D18)

   Keleut の `match` は後置の単一スクルティニ (`v match { ... }`) しかありません。
   MiniLang の行列は多スクルティニ前提で列が複数ありますが、Keleut では
   **入口の列は常に 1 列**です。それで表現力が落ちないのは、タプルが `_item`
   ラベルのレコードの糖衣だから (D4) です。`(a, b) match { ... }` の 1 列は、
   先頭で `CRecord [_item; _item]` に specialize した瞬間に 2 列に開きます。
   多スクルティニ行列は「内部表現としてだけ」現れる、というのが裁定 D18 です。

   表層の `T.pat` をそのまま行列に載せず、ここで内部形 `ipat` に写します。
   正規化で消えるものが 3 つあります。

   | 表層 | 内部 | 消える理由 |
   |---|---|---|
   | `PVar x` / `PWildcard` | `IWild` | 束縛名は網羅性に関係しない |
   | `PAnnot (p, ty)` | `p` の変換結果 | 注釈は elab が済ませた |
   | `PCtor` のラベル指定・省略 | 宣言順に整列した `ipat list` | 下の §10.3 |

   `PVar` を潰しておくと、以降のすべての場所で `IWild` の 1 ケースだけを見れば
   済みます。お手本が MiniLang §12 の中だけで `case PWild | PVar(_)` という
   2 つ組を 4 か所書いているのが、移植では 1 ケースになっているのはそのためです。

   `ICtor` の第 3 成分は**フィールドの宣言順**に整列済みであること、
   `IRecord` の第 2 成分 (closed?) は表示のためだけに持つことが不変条件です。 *)

type lit = LBool of bool | LText of string | LNum of string

type ipat =
  | IWild
  | ILit of lit
  | IVariant of oid * ipat
  | ICtor of oid * ipat list (* ctor、フィールド宣言順に整列済み *)
  | IRecord of (oid * ipat) list * bool (* フィールド列, closed? *)

(* ## 10.3 木から行列へ — 数値の正規化とフィールドの整列

   ### 数値は字面でなく値で比べる — 同値関係は実行時の照合が決める

   `case 1` と `case 0x1` は同じ値です。字面のまま `ILit` に入れると、
   後者が「別のコンストラクタ」に見えて冗長節の検出を取りこぼします。
   実装記録 260829-2-impl.md の乖離 11 — 計画に書き漏らしていた裁定です。

   では「同じ値」とは何の同値関係か。**実行時の照合**です (D24)。第14章の
   パターン照合は**値の型で**字面を読み直します — `VInt32` なら
   `Int32.of_string`、`VInt64` なら `Int64.of_string`、`VFloat64` なら
   `float_of_string` の値一致。ところが検査側の正規化は**列の型を知りません**。
   型を知らないまま 1 つの読みで鍵を作ると、どの読みを選んでも反例が
   出ます。最初の実装は native int(**63 ビット**)で読み、
   `0x7FFFFFFFFFFFFFFF` が -1 に折り返して `case -1` と同じ鍵になり、
   到達可能な節に偽の冗長警告を出しました(本文の旧版は「整数の正規化は
   往復するので健全です」と書いていましたが誤りでした)。Int64 で読み直した
   版は、Int32 の列で `4294967295`(Int32 では読めず、どの値にも一致
   しない)と `0xFFFFFFFF`(-1 に折り返して一致する)を同じ鍵に潰し、
   やはり到達可能な節に「到達不能」と誤警告しました(敵対的検証で実測)。

   そこで鍵は **3 通りの読みの積**にします。字面を `Int32` / `Int64` /
   `Float64` のそれぞれで読み(読めなければその成分は「読めない」の印)、
   3 成分を並べたものが鍵です。**すべての読みで等しい字面だけ**が同じ鍵に
   なるので、列の型がどれであっても「違う値を同じ鍵へ」は起きません。
   `1` と `0x1` はどの読みでも 1 なので従来どおり同じパターンです
   (乖離 11)。`1.` と `1.0` も浮動小数の読みだけが定義され、その値が
   同じなので同じパターンです。浮動小数の成分は `norm_float` で ±0.0 を
   畳みます(実行時の IEEE の = がそうだから)。%.17g は binary64 を
   一意に決めるので、相異なる値は必ず別の成分になります。第12章 §12.7 の
   最短表現を使わないのは、**鍵は誰にも見せない**ので桁を詰める理由が
   無く、章をまたぐ依存も作らずに済むからです。inf は `1e999` と `1e1000`
   が同じ成分になりますが、これは正しい — どちらも実行時には infinity
   です。NaN はリテラルとして書けないので考えません。

   読めなかったときに元の字面へ落ちるのは、ここが**検査であって評価ではない**
   からです。桁あふれした数値リテラルは型検査を素通りします — 第11章 (elab.ml)
   の `number_ty` は接尾辞しか見ず、`n_text` の中身をパースも範囲検査もしません。
   実際に落とすのは第14章 (interp.ml) で、評価の瞬間に
   「数値リテラルが範囲外です」を出して終了コード 3 で終わります。
   検査側は値を作る必要がないので、読めない字面は字面のまま重複判定に使えば
   足ります。ここで例外を投げても、利用者に届くのは網羅性検査の内部エラーで、
   本当の原因からは遠ざかるだけです。

   残る不完全性は**見逃す側**に揃っています。積の鍵は「列の型で読んだ鍵」
   より細かいので、実行時には同じ値になる組 — Int32 の列の
   `case 0xFFFFFFFF` と `case -1`(どちらも -1l に読まれる)— を別の鍵に
   し、本物の冗長を見逃します。また、列の型で読めない字面の節(Int32 の
   列の `case 4294967295`)はどの値にも一致しない死に節ですが、それ自体の
   診断はありません(式の位置なら実行時エラーになるのと非対称。260829-5 の
   課題台帳 V8)。どちらも偽の警告を出さない側の誤りです。両方直すには
   スクルティニ型を `convert` に流す設計変更(入れ子パターンの型も要る)が
   必要になるため、v0 では積の鍵で止めます。

   > 正規化は「同じ値を同じ字面へ」だけでなく「違う値を違う字面へ」も
   > 守らなければならない。列の型を知らないなら、**どの型で読んでも同じ**
   > ときだけ同じ鍵にする — 誤るなら、見逃す側で誤る。

   ### `PCtor` は解決結果を読んで宣言順に並べ替える

   Keleut のコンストラクタパターンはラベル指定とフィールド省略を許します
   (`case Cons(tail = t)`)。省略されたフィールドは `_` とみなす、というのが
   仕様側の裁定です (sample.kel §6 と、計画 §2.1 の表)。この対応づけを elab が
   `RCtorPat (data, ctor, field_to_arg)` として木に書き込んでいます。
   `field_to_arg` は**フィールド宣言位置から実引数位置への写像**で、
   `None` が省略を表します。

   ここで宣言順に直しておくと、以降の `arity` / `sub_types` /
   `rebuild` がすべて「宣言順」というひとつの約束の上で書けます。

   > `ICtor` の引数列と `ctor_fields` の並びは常に同じ順序。
   > この 1 つの約束が specialize と sub_types を噛み合わせている。

   解決が無いまま呼ばれたら `bug` で落とします。これは利用者のプログラムの
   誤りではなく elab の実装の誤りなので、型エラーではなく内部エラーが正しい報告です。 *)

(* 浮動小数の読みの正規化。±0.0 は実行時の IEEE の = に合わせて畳む。
   %.17g は binary64 を一意に決める(この鍵は誰にも見せない) *)
let norm_float f = if f = 0.0 then "0" else Printf.sprintf "%.17g" f

(* 鍵は Int32 / Int64 / Float64 の 3 通りの読みの積(§10.3)。検査は列の型を
   知らないので、どの読みでも等しい字面だけを同じ鍵にする — 列の型がどれで
   あっても「違う値を同じ鍵へ」は起きない。誤るなら見逃す側で誤る。
   §10.10 の反例候補も同じ norm_text で読む(鍵の形をここに閉じ込める) *)
let norm_text s =
  let read f to_s = match f s with Some v -> to_s v | None -> "X" in
  read Int32.of_string_opt Int32.to_string
  ^ "|"
  ^ read Int64.of_string_opt Int64.to_string
  ^ "|"
  ^ read float_of_string_opt norm_float

let norm_num (n : number) = norm_text n.n_text

let rec convert ((_, p) as node : T.pat) : ipat =
  match p with
  | T.PWildcard | T.PVar _ -> IWild
  | T.PBool b -> ILit (LBool b)
  | T.PText s -> ILit (LText s)
  | T.PNumber n -> ILit (LNum (norm_num n))
  | T.PAnnot (sub, _) -> convert sub
  | T.PVariant (s, sub) -> IVariant (intern s, convert sub)
  | T.PRecord (fields, rest) ->
      IRecord (List.map (fun (l, sub) -> (intern l, convert sub)) fields, rest = None)
  | T.PCtor (_, args) -> (
      (* 引数列は外側のパターンで束縛する。内側でもう一度分解して
         assert false で塞ぐ形にすると、到達しないはずの枝の例外だけが
         bug の [BUG] 前置を持たず、§16.8 の catch-all に「内部エラー」と
         して拾われる — 分類も文言も他の防御枝と不揃いだった(M19 / G3d) *)
      match Tree.get_resolved node with
      | Some (Tree.RCtorPat (_, ctor, field_to_arg)) ->
          let subs =
            Array.to_list
              (Array.map
                 (fun ai -> match ai with Some i -> convert (List.nth args i).T.cap_pat | None -> IWild)
                 field_to_arg)
          in
          ICtor (ctor, subs)
      | _ -> bug "PCtor が解決されていません(elab_pat が resolved を書いていない)")

(* ## 10.4 コンストラクタ・arity・部分型

   行列の先頭列を割るときの単位が `ctor` です (MiniLang:1594-1608)。

   | コンストラクタ | arity | どこから型を取るか |
   |---|---|---|
   | `CVariant l` | 1 | ヴァリアント行の `l` フィールド |
   | `CData c` | フィールド数 (多値) | 宣言表 + 型引数の代入 |
   | `CLit _` | 0 | — |
   | `CRecord ls` | ラベル数 | レコード行のフィールド型 |

   MiniLang の `CData` は arity 1 固定 (コンストラクタは必ず 1 引数) ですが、
   Keleut の `newtype` は多値コンストラクタを持つので、arity は宣言表を引いて
   決めます。`data_of_ctor` が `ctor_owner` から所属データ型へ登り、`ctor_fields`
   がフィールド宣言のリストを返す — この 2 段が **`CData` がコンストラクタ名
   だけを持てる理由**です。コンストラクタ名は大域一意 (第6章 (decls.ml) の §6.6)
   なので、名前から親をたどれます。

   `ctor_of` で 1 つだけ注意すべきなのは `IRecord` です。返す `CRecord` の
   ラベル列は**パターンではなく型の行**から取ります。開いたレコードパターン
   `{x, ...}` は型より少ないフィールドしか書いていないので、パターン側を
   基準にすると列数が行ごとにずれてしまいます。型の行だけが、行列の全行に
   共通する唯一の基準です。

   `sub_types` は `CData` のときだけ手間がかかります。宣言表のフィールド型は
   型パラメータを `Generic` マークで持っているので、スクルティニ型の実引数を
   代入してから返します (`Unify.subst_params`)。`List[Int32]` の `Cons` を割ったら
   部分型は `Int32` と `List[Int32]` でなければならず、`A` と `List[A]` では
   入れ子のリテラルパターンが型と噛み合いません。

   ここで作る `new_var 0` は**行列の桁数を合わせるための穴埋め**です。
   引数の数が宣言と食い違うなど、型検査が既に別のエラーを出しているはずの
   場面でしか現れません。この穴埋めは `TVar` のまま残り、§10.9 の `close_row` が
   `unify` を掛けるのは repr が `TVariant` になる実型の行尾だけなので、
   穴埋め変数が単一化に巻き込まれることはありません。 *)

type ctor = CVariant of oid | CData of oid (* ctor 名 *) | CLit of lit | CRecord of oid list

let data_of_ctor c = Hashtbl.find Decls.datas (Hashtbl.find Decls.ctor_owner c)

let ctor_fields c = (List.find (fun ct -> ct.Decls.ct_name = c) (data_of_ctor c).Decls.dd_ctors).Decls.ct_fields

let arity = function
  | CVariant _ -> 1
  | CData c -> List.length (ctor_fields c)
  | CLit _ -> 0
  | CRecord ls -> List.length ls

let record_labels ty =
  match repr ty with TRecord row -> List.map fst (fst (row_fields row)) | _ -> []

let ctor_of (p : ipat) ty =
  match p with
  | IWild -> None
  | ILit l -> Some (CLit l)
  | IVariant (l, _) -> Some (CVariant l)
  | ICtor (c, _) -> Some (CData c)
  | IRecord _ -> Some (CRecord (record_labels ty))

let field_type_of row label =
  match List.assoc_opt label (fst (row_fields row)) with Some t -> t | None -> new_var 0

let sub_types c ty =
  match (c, repr ty) with
  | CVariant l, TVariant row -> [ field_type_of row l ]
  | CData ctor, TCon (n, args) when Hashtbl.mem Decls.datas n ->
      let dd = Hashtbl.find Decls.datas n in
      let subst =
        try List.map2 (fun (i : var_info) a -> (i.vid, a)) dd.Decls.dd_params args with Invalid_argument _ -> []
      in
      List.map (fun f -> Unify.subst_params 0 subst f.Decls.fi_ty) (ctor_fields ctor)
  | CRecord _, TRecord row -> List.map snd (fst (row_fields row))
  | CLit _, _ -> []
  | _ -> List.init (arity c) (fun _ -> new_var 0)

(* ## 10.5 レコードの整列 — タプルはラベルの重複

   **移植で唯一つまずいたのがここです** (計画 §7.5 が「移植上の唯一の罠」と
   名指ししている箇所)。MiniLang:1645 はレコードパターンを
   ラベルからパターンへの Map に変換し、型の行のラベル順に引き直します。

   Keleut ではこれが使えません。タプルは `_item` ラベルの連なりだからです。
   `(1, 2, 3)` のパターンは同じラベル `_item` を 3 つ持ち、Map にすると
   **3 要素が 1 要素に潰れます**。潰れた行列は列数が合わず、
   3 要素タプルの網羅性がまるごと壊れます。

   正しい対応づけは、単一化側の規約から決まります。行の重複ラベルは
   **最左一致** (Scoped Labels) で対応する — つまり型の k 番目の `_item` は
   パターンの k 番目の `_item` に対応します。違うラベル同士の順序は
   意味を持たず、同じラベル同士の相対順序だけが意味を持ちます。

   そこで「ラベルごとのキュー」を作ります。型の行のフィールドを左から順に見て、
   各ラベルについてパターン側の**まだ使っていない最左の同名フィールド**を
   取り出す。`used` 配列がそのキューの消費済みマークです。書かれていない
   フィールドは `IWild` で埋まるので、開いたレコードパターンも
   閉じたパターンと同じ列数に揃います。

   > 同じラベルが並ぶ行では、Map ではなくキューを使う。
   > 最左一致は単一化だけの規約ではなく、網羅性検査の規約でもある。

   レコードは直積であって直和ではないので、パターンに書かれていない
   フィールドを `_` で埋めても場合分けは増えません。だからこの整列は
   「情報を捨てずに列を揃える」操作として安全です。 *)

let align_record_pat labels fields =
  let used = Array.make (List.length fields) false in
  List.map
    (fun l ->
      let rec find i = function
        | [] -> IWild
        | (l2, p) :: rest ->
            if l2 = l && not used.(i) then (
              used.(i) <- true;
              p)
            else find (i + 1) rest
      in
      find 0 fields)
    labels

(* ## 10.6 `specialize` と `default` — 行列を削る 2 つの操作

   アルゴリズムの全部がこの 2 つに乗ります (MiniLang:1634-1657)。

   `specialize c rows` は「先頭列が `c` にマッチしうる行」だけを残します。

   - `IWild` — どのコンストラクタにもマッチするので残る。先頭には `c` の arity
     だけワイルドカードを並べて列数を合わせる
   - 同じコンストラクタ — 引数を先頭に展開する。`ICtor` は既に宣言順なので
     `subs @ rest` と連結するだけで済む (§10.3 の約束の配当)
   - 別のコンストラクタ — 落とす

   `default_matrix rows` は逆に「先頭列がワイルドカードの行」だけを残して
   先頭列を捨てます。**シグネチャが完全でないとき**、つまり
   「まだ見ぬコンストラクタがありうる」ときに使う枝で、その未知の
   コンストラクタに対して生き残る行はワイルドカードの行だけだ、という理屈です。

   `specialize` が受け取る型引数を使っていないのは、レコードのラベル列を
   `CRecord ls` 自身が持っているからです (MiniLang も同じく使っていません)。
   引数として残してあるのは、お手本と呼び出し側の形を揃えるためです。

   `default_matrix` に `IVar` に相当するケースが無いことに注目してください。
   §10.2 で `PVar` を `IWild` に正規化したので、ここは 1 ケースで足ります。 *)

let specialize c _ty rows =
  List.concat_map
    (fun row ->
      match row with
      | [] -> []
      | h :: rest -> (
          match (h, c) with
          | IWild, _ -> [ List.init (arity c) (fun _ -> IWild) @ rest ]
          | IVariant (l1, sub), CVariant l2 when l1 = l2 -> [ sub :: rest ]
          | ICtor (l1, subs), CData l2 when l1 = l2 -> [ subs @ rest ]
          | ILit a, CLit b when a = b -> [ rest ]
          | IRecord (fs, _), CRecord labels -> [ align_record_pat labels fs @ rest ]
          | _ -> []))
    rows

let default_matrix rows =
  List.concat_map (fun row -> match row with IWild :: rest -> [ rest ] | _ -> []) rows

(* ## 10.7 完全シグネチャ — 「これで全部」と言えるのはいつか

   `complete_sig` は「この型の値は、このコンストラクタのどれかで必ず始まる」と
   言い切れるときだけコンストラクタの一覧を返します (MiniLang:1659-1672)。
   `None` は「言い切れない」であって「コンストラクタが無い」ではありません。

   | 型 | 返す値 | 理由 |
   |---|---|---|
   | 閉じたヴァリアント行 | ラベル全部 | 行尾が `TRowEmpty` なら増えない |
   | 開いたヴァリアント行 | `None` | 行変数が残る = ラベルはいくらでも増えうる |
   | `newtype` (透明) | 宣言表の全 ctor | 宣言が閉じている |
   | `newtype X = ???` (opaque) | `None` | 中身を知らないので数え上げられない |
   | `Never` | `Some []` | **コンストラクタゼロ** |
   | `Boolean` | true と false | 2 値だけ |
   | レコード | 単一の `CRecord` | 直積は 1 ケース |
   | `Int32` / `String` など | `None` | 有限個に数え上げない |

   ### `Never` — コンストラクタゼロは「節ゼロで網羅」

   `Never` は住人のいない型です (sample.kel §6)。`dd_ctors = []` で登録されているので
   `Some []` が返り、これは「この型の値は 0 通りのコンストラクタのどれかで
   始まる」、つまり**値が存在しない**という主張です。だから

       let absurd[A](n: Never): A = n match {}

   の節ゼロが網羅になります。文法が空の `match` 本体を許すのも同じ理由です
   (実装記録の乖離 9)。§10.10 でこの `Some []` が効きます。

   ### opaque が `None` なのは臆病ではなく正しい

   `Ref` や `Array` は `newtype X = ???` として登録されます。中身の
   コンストラクタを知らないのだから、どんな `match` を書いてもワイルドカード
   なしでは網羅を主張できません。ここで `Some []` を返してしまうと
   「`Ref` の値は存在しない」という嘘になり、到達不能警告まで巻き添えで壊れます。
   コンストラクタが無いこととコンストラクタを知らないことは別だ、という区別が
   `Some [] / None` の使い分けの正体です。

   ### レコードの行が開いていても構わない

   レコード型の行尾が変数のままでも `Some [CRecord 既知のラベル]` を返します。
   直積は場合分けを増やさないので、未知のフィールドが増えても
   「レコードは 1 ケース」という主張は揺らぎません。ヴァリアントの
   開いた行が `None` になるのとは非対称ですが、和と積の違いそのものです。

   `Unit` に専用ケースが無いのは、Keleut の `()` が空レコードだからです。
   `TRecord` の枝が `CRecord []` (arity 0) を返して、そのまま処理されます。 *)

(* Boolean の oid。intern は表引きなので、complete_sig のたびに引かず
   1 回で済ませる。Type.intern_map は reset されない(第1章 §1.2)ので
   初期化時に確定してよい(M19 / G3e) *)
let oid_boolean = intern "Boolean"

let complete_sig ty =
  match repr ty with
  | TVariant row -> (
      let fs, tail = row_fields row in
      match repr tail with
      | TRowEmpty -> Some (List.sort_uniq compare (List.map (fun (l, _) -> CVariant l) fs))
      | _ -> None (* 開いた行 = ラベルはいくらでも増えうる *))
  | TCon (n, _) when Hashtbl.mem Decls.datas n ->
      let dd = Hashtbl.find Decls.datas n in
      if dd.Decls.dd_opaque then None else Some (List.map (fun ct -> CData ct.Decls.ct_name) dd.Decls.dd_ctors)
  | TCon (n, []) when n = oid_boolean -> Some [ CLit (LBool true); CLit (LBool false) ]
  | TRecord row -> Some [ CRecord (List.map fst (fst (row_fields row))) ]
  | _ -> None

(* ## 10.8 `rebuild` — 反例を組み立て直す

   アルゴリズム I は行列を割りながら降りていき、いちばん底で
   ワイルドカードのベクトルを見つけます。帰り道でそれを元の形に組み直すのが
   `rebuild` です。`ws` は「このコンストラクタの引数」と「残りの列」が
   連結された 1 本のリストなので、arity で切り分けて先頭だけを包み直します。

   `split_at` を直前に 1 つ置いているのは、標準ライブラリに無く
   `List.filteri` 系では書きにくいからです (M19 / G3c)。1 回の走査で
   切り出しと残りを両方返すので、`take` と `drop` を別々に書いて 2 回
   歩く形にはしていません(かつては同じ 2 本組が 2 か所に複製されて
   いました)。`ws` が短くても落ちませんが、**この関数全体が
   例外を投げないわけではありません**。`CRecord` 枝の `List.combine ls fs`
   は長さが違えば `Invalid_argument` を、`CVariant` 枝の `List.hd ws` は
   空リストで `Failure` を送出します。つまりここは
   「行列とベクトルと型リストが同じ幅で歩く」という §10.11 の不変条件に
   寄りかかっていて、それが破れたら内部エラーとして落ちる、というのが
   実際の姿勢です。反例の表示のために防御的な分岐を足す価値はありません。

   `IRecord` を `true` (閉じている) で組むのは、反例として見せるレコードは
   常に全フィールドを書き下したものだからです。この `true` が
   §10.12 のタプル再糖衣化の入口になります。 *)

(* 先頭 n 個とその残りに割る。stdlib に無く、List.filteri 系では書きにくい。
   ws が n より短くても落ちない(§10.8 の不変条件が破れたときの被害を
   ここで増やさないため。M19 / G3c — かつて take / drop の 2 本組を
   2 か所に複製し、リストを 2 回歩いていた) *)
let rec split_at n xs =
  if n = 0 then ([], xs)
  else
    match xs with
    | [] -> ([], [])
    | x :: tl ->
        let a, b = split_at (n - 1) tl in
        (x :: a, b)

let rebuild c ws =
  match c with
  | CVariant l -> IVariant (l, List.hd ws) :: List.tl ws
  | CData l ->
      let args, rest = split_at (arity (CData l)) ws in
      ICtor (l, args) :: rest
  | CLit l -> ILit l :: ws
  | CRecord ls ->
      let fs, rest = split_at (List.length ls) ws in
      IRecord (List.combine ls fs, true) :: rest

(* ## 10.9 構造的ヴァリアントの行を閉じる

   行多相ヴァリアントには固有の問題があります (MiniLang:1699-1710 と同じ話)。
   `#Lft(n)` の型は `#Lft(τ) | R` と**開いて**いるので、`match` を書いた時点では
   「他にどんなラベルがありうるか」が分かりません。開いたままだと
   `complete_sig` が永遠に `None` を返し、構造的ヴァリアントに対する
   どんな `match` にもワイルドカード節が要ることになります。

   そこで規則をひとつ置きます。

   > その列にワイルドカードの節が無いなら、そこで行を閉じる。

   利用者が `case _` を書かなかったことを「これで全部のつもりだ」という
   意思表示とみなし、行尾を `TRowEmpty` に単一化するわけです。これで

       let closed = fn(t) => t match { case #Lft(n) => n + 0  case #Rgt(_) => 0 }

   の `t` は `#Lft(Int32) | #Rgt(A)` に確定し、ワイルドカードなしで網羅になります。
   逆に `case _` を書けば行は開いたまま (`#Lft(Int32) | R1`) で、
   その関数はもっと多くのラベルを受け取れる多相な関数になります。
   **どちらが欲しいかを、ワイルドカードの有無で選べる**ということです。

   `roots <> []` の条件が要るのは、全行がワイルドカードのときに
   意味もなく行を閉じないためです。列にコンストラクタがひとつも現れて
   いなければ、その列について利用者は何も主張していません。

   再帰は行列と同じ形で降ります。コンストラクタごとに specialize した先でも
   入れ子のヴァリアントの行を閉じる必要があるからです。

   **代償**: これは型を書き換える操作なので、順序が結果を変えます。
   だから §10.13 の遅延キューが要ります。宣言された `newtype` を使えば
   最初から閉じていて、この細工も型注釈も要りません — 構造的ヴァリアントは
   「宣言を書くほどでもない使い捨ての和」のための道具です。 *)

let close_row ty =
  match repr ty with
  | TVariant row -> ( match row_tail_var row with Some tv -> Unify.unify (TVar tv) TRowEmpty | None -> ())
  | _ -> ()

let rec close_variant_rows rows tys =
  match tys with
  | [] -> ()
  | ty0 :: tys_tail ->
      if rows <> [] then (
        let ty0 = repr ty0 in
        let has_default = List.exists (fun r -> match r with IWild :: _ -> true | _ -> false) rows in
        let roots =
          List.sort_uniq compare (List.concat_map (fun r -> match r with h :: _ -> Option.to_list (ctor_of h ty0) | [] -> []) rows)
        in
        if (not has_default) && roots <> [] then close_row ty0;
        let ty = repr ty0 in
        List.iter (fun c -> close_variant_rows (specialize c ty rows) (sub_types c ty @ tys_tail)) roots;
        close_variant_rows (default_matrix rows) tys_tail)

(* ## 10.10 アルゴリズム I — 抜けているケースを 1 つ構成する

   `missing rows tys` は「`rows` のどの行にもマッチしない値」を
   パターンの形で 1 つ返します。返り値が `None` なら網羅、
   `Some w` なら `w` が反例です (MiniLang:1714-1741)。

   底は列が尽きたときで、行が 1 本でも残っていれば全部覆われているので `None`、
   1 本も無ければ空ベクトルが反例です。

   分岐は先頭列のシグネチャが完全かどうかで決まります。

   - **完全**なら、コンストラクタごとに specialize して降り、最初に見つかった
     反例を `rebuild` で包み直す。全コンストラクタで `None` なら網羅
   - **不完全**なら `default_matrix` で降り、帰りに先頭へ「まだ使われていない
     コンストラクタ」を置く。それも無ければワイルドカードを置く

   ### `Some []` を先に分岐させた理由 (Never の直し)

   お手本 MiniLang:1721 の完全判定は次の形でした。

       roots.nonEmpty && sig.exists(s => s.forall(c => roots.contains(c)))

   この `roots.nonEmpty` は、**シグネチャが空でないときは何も変えません**。
   `s` が空でないのに `roots` が空なら `forall` はどのみち偽だからです。
   効くのは `s` が空のとき — そしてそのとき答えが逆になります。
   `Never` に対する `n match {}` は roots も空なので、
   お手本は「非網羅、例えば `_` が漏れています」と誤って警告します。

   そこで `Some [] -> true` を先に置きました。コンストラクタゼロのシグネチャは
   「節ゼロで網羅」であって「常に非網羅」ではありません。
   実装記録 260829-2-impl.md の乖離 9 に記録した修正です。

   > 「コンストラクタが全部覆われている」の全部は、0 個の全部でもよい。

   `Some s` の枝に `roots <> []` の連言は要りません — この枝に届く `s` が
   空でない以上、`roots` が空なら `List.for_all` は必ず偽です。以前は
   「お手本との対応を目で追えるように」と冗長な連言をあえて残して
   いましたが、同じ 6 行が `missing` と `useful` に**複製**された時点で
   その理由は持たなくなりました。判定は `sig_complete` の 1 か所にあり、
   §10.11 も同じものを引きます (M19 / G3a)。

   ### 反例を構成する — 整数・浮動小数・文字列

   シグネチャが `None` の型 (`Int32` など) では、使われていないコンストラクタを
   一覧から選ぶことができません。そこで「まだパターンに現れていない値」を
   候補列から探して具体的な反例にします。`case 0 => ... case 1 => ...` に
   対して `2` が漏れていると言えるほうが、`_` が漏れていると言うより
   役に立ちます。候補列は 3 通りです。

   - 整数: 0, 1, 2, …(`string_of_int`)
   - 浮動小数: 0.0, 1.0, 2.0, …(表示は `%.1f`)
   - 文字列: 空文字列, a, aa, …(`String.make i` の a の反復)

   いずれも roots(現れているリテラル)は有限なので必ず止まります。
   要は**突き合わせは §10.3 の鍵で、表示は読める字面で**という分業です。
   以前は鍵と `string_of_int` を直に突き合わせていたため、Float64 の列では
   `case 0.0` の鍵(`0.` の類)と字面 `0` が噛み合わず、既に覆われている
   `0` を witness として提示していました — 非網羅という結論は正しくても、
   利用者がその値で試すと第 1 節に当たり、警告が嘘に見えます。文字列には
   構成そのものが無く、反例は情報量ゼロの `_` でした。

   反例に出す字面は必ず Keleut のリテラルとして読めるものにします。
   §10.3 の鍵(%.17g や ±0 畳み)はここに**流さない** — 鍵は同値判定の
   ための内部表現で、誰にも見せない、が両節の分業の不変条件です。
   列の型がまだ既定化前の弱い変数のとき(注釈の無い引数の match は
   宣言末の既定化より先に検査される)は、Fractional 述語が付いていれば
   浮動小数の候補列を使います — 整数の字面 `2` はその列には書けない
   反例だからです。

   > 反例は「存在する」と言うだけでは反例ではない。指させて初めて反例になる。 *)

let roots_of rows ty =
  List.sort_uniq compare (List.concat_map (fun r -> match r with h :: _ -> Option.to_list (ctor_of h ty) | [] -> []) rows)

(* シグネチャが完全か。Some [] = コンストラクタゼロ(Never)は節が
   無くても網羅(計画 §7.5)。Some s の枝に roots <> [] は要らない —
   s が非空なら List.for_all は roots が空のとき必ず偽になる(§10.10。
   M19 / G3a — かつて同じ 6 行が missing / useful に複製されていた) *)
let sig_complete sig_ roots =
  match sig_ with
  | Some [] -> true
  | Some s -> List.for_all (fun c -> List.mem c roots) s
  | None -> false

let rec missing rows tys =
  match tys with
  | [] -> if rows = [] then Some [] else None
  | ty :: tys_tail -> (
      let ty = repr ty in
      let roots = roots_of rows ty in
      let sig_ = complete_sig ty in
      let is_complete = sig_complete sig_ roots in
      if is_complete then
        List.find_map
          (fun c ->
            match missing (specialize c ty rows) (sub_types c ty @ tys_tail) with
            | Some w -> Some (rebuild c w)
            | None -> None)
          (Option.get sig_)
      else
        match missing (default_matrix rows) tys_tail with
        | None -> None
        | Some w ->
            let head =
              match sig_ with
              | Some s -> (
                  match List.find_opt (fun c -> not (List.mem c roots)) s with
                  | Some c -> List.hd (rebuild c (List.init (arity c) (fun _ -> IWild)))
                  | None -> IWild)
              | None -> (
                  (* シグネチャが無い型 (Int32/Int64/Float64/String) は、まだ
                     使われていない値を候補列から探して具体的な反例にする。
                     候補は必ず読める字面にする — 鍵 (§10.3) は表示しない *)
                  let used_num = List.filter_map (function CLit (LNum n) -> Some n | _ -> None) roots in
                  let used_txt = List.filter_map (function CLit (LText s) -> Some s | _ -> None) roots in
                  if used_txt <> [] then
                    (* 候補列は空文字列, a, aa, … 。roots は有限なので必ず止まる *)
                    let rec fresh i =
                      let s = String.make i 'a' in
                      if List.mem s used_txt then fresh (i + 1) else s
                    in
                    ILit (LText (fresh 0))
                  else if used_num = [] then IWild
                  else
                    (* 列がまだ既定化前の弱い変数のとき(注釈の無い引数)は、
                       Fractional 述語で浮動小数の列だと分かる — 整数の字面を
                       出すと、その列には書けない反例になる(検証の指摘) *)
                    let is_float_col =
                      match ty with
                      | TCon (n, []) -> n = intern "Float64"
                      | TVar { contents = Unbound i } -> List.mem cls_fractional i.vcls
                      | _ -> false
                    in
                    if is_float_col then
                      (* 候補は 0.0, 1.0, 2.0, …。突き合わせは §10.3 と同じ鍵
                         (norm_text)で行い、見せるのは読める字面のほう *)
                      let rec fresh i =
                        let s = Printf.sprintf "%.1f" (float_of_int i) in
                        if List.mem (norm_text s) used_num then fresh (i + 1) else s
                      in
                      ILit (LNum (fresh 0))
                    else
                      let rec fresh i =
                        let s = string_of_int i in
                        if List.mem (norm_text s) used_num then fresh (i + 1) else s
                      in
                      ILit (LNum (fresh 0)))
            in
            Some (head :: w))

(* ## 10.11 アルゴリズム U — ベクトル `q` が useful か

   冗長節の検出はこちらです (MiniLang:1745-1767)。`useful rows q tys` は
   「`rows` のどの行にもマッチしないが `q` にはマッチする値がある」かを返します。
   `rows` に先行する節を全部入れて `q` に i 番目の節を置き、偽なら
   その節には決して来ないので冗長です。

   構造は `missing` と対称で、違いは「行列を割る基準を `q` から取る」ことです。

   - `q` の先頭がコンストラクタなら、そのコンストラクタで両方 specialize して
     降りる
   - `q` の先頭がワイルドカードなら、シグネチャが完全なときだけ
     コンストラクタごとに調べて **どれか 1 つでも** useful なら useful、
     そうでなければ `default_matrix` で降りる

   底の `rows = []` が「まだ誰も覆っていない値が残っている」の判定です。

   ここでも `Some []` を先に分岐させています。`Never` を相手にした節は
   `List.exists` が空リストに対して偽を返すので useful にならず、
   正しく「到達不能」と報告されます。値の無い型に対する節は、
   確かにどんな値でも実行されません。

   `List.hd q` が安全なのは、`q` の長さが常に `tys` の長さと等しいという
   不変条件によります。`specialize` が両方を同じだけ伸ばし、
   `default_matrix` と `List.tl` が同じだけ縮めるので、この対応は崩れません。

   > 行列とベクトルと型リストは、いつも同じ幅で歩く。 *)

let rec useful rows q tys =
  match tys with
  | [] -> rows = []
  | ty :: tys_tail -> (
      let ty = repr ty in
      match ctor_of (List.hd q) ty with
      | Some c ->
          let q2 = match specialize c ty [ q ] with [ q2 ] -> q2 | _ -> bug "useful: specialize q" in
          useful (specialize c ty rows) q2 (sub_types c ty @ tys_tail)
      | None ->
          let roots = roots_of rows ty in
          let sig_ = complete_sig ty in
          let is_complete = sig_complete sig_ roots in
          if is_complete then
            List.exists
              (fun c ->
                useful (specialize c ty rows) (List.init (arity c) (fun _ -> IWild) @ List.tl q) (sub_types c ty @ tys_tail))
              (Option.get sig_)
          else useful (default_matrix rows) (List.tl q) tys_tail)

(* ## 10.12 反例の表示 — 内部形から Keleut の見た目へ

   反例は `ipat` のまま出しても読めないので、表層構文に戻して見せます。
   第9章 (show.ml) が型に対してやっていることの、パターン版です。

   再糖衣化が 2 か所あります。

   - **ペイロードの無いヴァリアント**: `#Even` の内部形は
     `IVariant (l, IRecord ([], true))` — 空レコード (= `Unit`) を
     引数に取る形です。これを `#Even(())` と出さずに `#Even` と出します。
   - **タプル**: 閉じたレコードで、全フィールドのラベルが `_item` なら
     `(a, b)` と括弧で並べます。そうでなければ波括弧のレコード記法です。
     `(false, false)` という反例が出るのはこの経路で、
     `{_item = false, _item = false}` と出たら教材として失格です。
     1 要素のときは `(a,)` と末尾カンマを打ちます(sample.kel:182、D101)。
     `(false)` はパターンとしてはグループ化なので、貼り戻しても
     1 要素タプルのパターンにならず、同じ失格になるからです。
     第9章 §9.3(型)と第12章 §12.7(値)も同じ規則です。仕様 §4 は
     この戻し方が「型の表示、型エラーの文面、実行時エラーに出る値、
     網羅性警告の反例の 4 つすべて」に及ぶと数えており
     (sample.kel:179-180、D112)、反例はその 4 つ目です。

   フィールドが空で閉じているレコードは `()` — こちらは `Unit` の
   値そのものなので、タプル規則より先に判定しています。パターンの位置で
   空行を `()` と書くのは仕様の書き分けどおりで(sample.kel:182)、型の
   位置に出る `{}` とは字面が違うだけで、指すものは同じです
   (sample.kel:183-185)。

   これは第1章の裁定 D4「タプルは `_item` 行の糖衣、`TTuple` は持たない」の
   後始末です。型を単純にした代償は必ずどこかで払うことになり、
   ここと第9章の 2 か所がその支払い場所になっています。 *)

let show_lit = function LBool b -> string_of_bool b | LText s -> "\"" ^ String.escaped s ^ "\"" | LNum n -> n

let rec show_ipat = function
  | IWild -> "_"
  | ILit l -> show_lit l
  | IVariant (l, IRecord ([], true)) -> "#" ^ name_of l
  | IVariant (l, sub) -> "#" ^ name_of l ^ "(" ^ show_ipat sub ^ ")"
  | ICtor (c, []) -> name_of c
  | ICtor (c, subs) -> name_of c ^ "(" ^ String.concat ", " (List.map show_ipat subs) ^ ")"
  | IRecord ([], true) -> "()"
  | IRecord (fs, closed) ->
      if closed && fs <> [] && List.for_all (fun (l, _) -> l = l_item) fs then
        "(" ^ String.concat ", " (List.map (fun (_, p) -> show_ipat p) fs) ^ (match fs with [ _ ] -> ",)" | _ -> ")")
      else "{" ^ String.concat ", " (List.map (fun (l, p) -> name_of l ^ " = " ^ show_ipat p) fs) ^ "}"

(* ## 10.13 検査キュー — なぜ `match` の瞬間に検査しないのか

   お手本 MiniLang は `match` を推論したその場で網羅性を検査します。
   そして MiniLang §17「意図的に落とした要素」の 8 で自分の設計を
   こう振り返っています —「実際には、遅延キューに積み、その let の一般化直前に
   走らせるのが良いバランスです」。この章はその助言を採った形です (計画 §7.2)。

   遅延には理由が 2 つあります。

   ### 理由 1: 一般化のあとでは行を閉じられない

   §10.9 の `close_variant_rows` は `unify` を呼びます。一方 `generalize` は
   型変数を `Generic` マークに書き換えます。`Generic` は型スキーマの
   量化変数を表すので、それに `unify` を掛けるのは内部エラーです
   (第8章の `bind` も `occurs_adjust` も `bug` で落とします)。
   したがって検査は**必ず一般化より前**に走らなければなりません。

   ### 理由 2: 早すぎると行がまだ全部のラベルを集めていない

   逆に `match` の瞬間に閉じてしまうのも困ります。

       let f = fn(t) => { t match { case #A => 1  case #B => 2 }; g(t) }

   ここで `g` が `#C` を要求するなら、`match` の直後に行を閉じた `t` は
   `g` に渡せず**型エラー**になります。束縛の右辺を全部推論し終えてから
   閉じれば、`t` の行は `#A | #B | #C` まで育っており、
   検査は「`#C` が漏れています」という**正しい警告**を出します。
   型エラーと網羅性警告のどちらを出すかが、走らせる時点で変わるわけです。

   > 行を閉じるのは破壊的操作。だから「いちばん遅く、しかし一般化より前」。

   この 2 つの制約が挟み込むただ 1 つの時点が、
   各 let 束縛群の `generalize` の直前です。第11章 (elab.ml) はそこで
   `drain` を呼びます。`queue` は先頭に積み、`drain` が `List.rev` で
   戻します (M19 / G3b)。末尾に `@` で足すと積んだ数の二乗になるので、
   順序の保証は反転のほうへ移しました。**ゴールデンテストがこの順序を
   見ています**。

   正直な留保を 2 つ (M19 検証)。第一に、drain は**内側の** let の
   一般化点でも走るので、上の例の match を `let a = t match { … }` と
   局所束縛に包むと、内側の drain が `t` の行をそこで閉じ、`g(t)` は
   警告ではなく型エラーになります。「いちばん遅く」が保証されるのは
   自分の束縛の中だけです。第 11 章はこの帰結を踏み、関数引数と
   return 節の検査エントリ(V10)を本体の推論より**後**に積みます —
   先に積むと本体中の let に食われて、受理されていたプログラムが
   型エラーに変わりました。第二に、順序の保証は**宣言をまたぐ順序**
   です。1 宣言の中では、引数パターンの警告は(本体の後に積むため)
   本体の match の警告より後に出ます。

   ### ガード付き節は網羅性に数えない

   `case P if cond => e` は、実行時に `cond` が偽なら次の節へ落ちます。
   つまり**その節は必ずマッチするとは限らない**ので、被覆として数えると
   不健全な「網羅です」を出してしまいます。仕様も
   sample.kel:322-324 で「ガード付きのケースは網羅性検査で
   必ずマッチするとは数えられないので、最後のケース (ガードなし) が必要」
   と明言しています。

   そこで行列を 2 通りに使い分けます。

   | 用途 | 使う行 | 理由 |
   |---|---|---|
   | 行を閉じる / 網羅性 (`missing`) | ガード無しの節だけ | 覆うと言えるのはこれだけ |
   | 到達可能性 (`useful`) の被験者 | 全節 | ガード付き節も冗長になりうる |
   | 到達可能性の被覆側 | 先行するガード無しの節だけ | 同上 |

   ガード付き節は「他を覆わないが、他に覆われうる」という非対称な扱いです。
   節番号 (`第 %d 節`) は全節を通した 1 起点の番号なので、
   ガード付き節を飛ばして数えることはしません。利用者が見ているのは
   ソースに並んだ節であって、行列に載った行ではないからです。

   `reset` は宣言の処理を始める前にキューを空にします。キューは大域状態なので、
   前のファイルやエラーで中断した推論の残骸を持ち越さないための掃除です。 *)

type entry = { qe_rows : (T.pat * bool (* ガードつき *)) list; qe_ty : ty }

let pending : entry list ref = ref []

(* 積むのは先頭。ソース順は drain の List.rev が戻す(§10.13。
   M19 / G3b — 末尾 @ は積んだ数の二乗) *)
let queue rows ty = pending := { qe_rows = rows; qe_ty = ty } :: !pending

let check_entry { qe_rows; qe_ty } =
  let out = ref [] in
  let all = List.map (fun (p, guarded) -> ([ convert p ], guarded)) qe_rows in
  let unguarded = List.filter_map (fun (r, g) -> if g then None else Some r) all in
  let tys = [ qe_ty ] in
  close_variant_rows unguarded tys;
  (* 単一パターンのエントリ(let のパターン束縛・関数引数・return 節)には
     「節」が無いので、節番号を出さない(M19 検証 — 利用者が存在しない
     第 1 節を探すことになる) *)
  let single = match qe_rows with [ _ ] -> true | _ -> false in
  (* ガード付き節は「必ずマッチ」と数えない(sample.kel:322-324)ので網羅性から除外 *)
  (match missing unguarded tys with
  | Some w -> out := !out @ [ "match が非網羅的です。例えば " ^ String.concat ", " (List.map show_ipat w) ^ " が漏れています" ]
  | None -> ());
  (* 到達不能: 先行するガード無し節だけを被覆として数える *)
  List.iteri
    (fun i (row, _) ->
      let prior = List.filteri (fun j _ -> j < i) all in
      let prior_unguarded = List.filter_map (fun (r, g) -> if g then None else Some r) prior in
      if not (useful prior_unguarded row tys) then
        out :=
          !out
          @ [
              (if single then "このパターンには一致する値がありません"
               else Printf.sprintf "第 %d 節は到達不能です(冗長)" (i + 1));
            ])
    all;
  !out

let drain () =
  let entries = List.rev !pending in
  pending := [];
  List.concat_map check_entry entries

let reset () = pending := []
