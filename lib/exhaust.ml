(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第10章 網羅性検査

   本章は、`match` がすべての場合を覆っているか、どの節にも到達できるかを調べる。
   アルゴリズムは Luc Maranget の Warnings for pattern matching(JFP 2007)に従う。
   骨格は、specialize と default という 2 つの行列操作と、
   そこから導くアルゴリズム I(非網羅の検出)とアルゴリズム U(冗長な節の検出)である。

   ## 前の章から受け取るもの

   - 第5章(tree.ml)の精緻化木。
     木だけでは、コンストラクタがどの型に属するかが分からない。
     `PCtor` は、第11章(elab.ml)が木に書き込んだ `RCtorPat` を `Tree.get_resolved` で読んで展開する。
     そのため、この検査は第11章がパターンを精緻化した後でしか動かない。
   - 第6章(decls.ml)の宣言表。
     「この型のコンストラクタはこれですべて」という完全シグネチャは、
     `Decls.datas` と `Decls.ctor_owner` から作る。
   - 第8章(unify.ml)。
     本章は行を閉じる 1 か所だけで `unify` を呼ぶ。
     本章が型を書き換えるのはそこだけで、それ以外は型を読むだけである。

   ## 次の章へ渡すもの

   - 第11章(elab.ml)は `match` を見つけるたびに `queue` へ積み、
     束縛の一般化の直前に `drain` を呼んで警告の文字列のリストを受け取る。
   - 第16章(driver.ml)はそれを警告として出す。
     非網羅も到達不能も既定では警告にとどまり、`--strict-exhaustive` を指定するとエラーになる。

   ## この章の地図

   | 節 | 中身 |
   |---|---|
   | §10.1 | usefulness と、そこから導く 2 つの検査 |
   | §10.2-10.3 | 内部パターン `ipat` と、木からの変換 |
   | §10.4-10.6 | コンストラクタ、レコードの整列、`specialize` / `default` |
   | §10.7-10.8 | 完全シグネチャと反例の組み立て |
   | §10.9 | 構造的ヴァリアントの行を閉じる |
   | §10.10-10.11 | アルゴリズム I(非網羅)と U(冗長) |
   | §10.12 | 反例の表示 |
   | §10.13 | 検査キューと、`match` の時点で検査しない理由 | *)

(* ## 10.1 usefulness と 2 つの検査

   Maranget のアルゴリズムの中心にある概念は usefulness である。

   **useful**：パターン行列 `P` に対してベクトル `q` が useful であるとは、
   `P` のどの行にも一致しないが `q` には一致する値が存在することをいう。

   この述語を 2 通りに使うと、必要な検査が両方得られる。

   - **網羅性**：ワイルドカードだけからなるベクトルが useful なら、`match` は網羅的でない。
     しかも漏れている値を構成できるので、警告に反例を載せられる。
   - **到達可能性**：i 番目の節が、それより前の節からなる行列に対して useful でなければ、
     その節に一致する値は、どれもそれより前の節に先に一致する。
     つまり、その節には到達できず、冗長である。

   実装は、行列に対する次の 2 つの操作だけでできている。

   - `specialize c P` は、先頭列がコンストラクタ `c` に一致しうる行だけを残し、
     `c` の引数を先頭に展開する
   - `default_matrix P` は、先頭列がワイルドカードの行だけを残し、先頭列を落とす

   この検査は、`List` のような無限に深くなりうる再帰型に対しても停止する。
   行列の先頭列に実際に現れたコンストラクタの集合を roots と呼ぶ。
   `close_variant_rows` は roots のコンストラクタで再帰する。
   `useful` は、`q` の先頭がコンストラクタなら、そのコンストラクタで再帰する。
   `missing` と、`q` の先頭がワイルドカードのときの `useful` は、
   シグネチャのコンストラクタを並べて再帰する。
   ただし、それはシグネチャのすべてのコンストラクタが roots にあるとき(シグネチャが完全なとき)に限られる。
   どの場合も、再帰に使うのはパターンに現れたコンストラクタなので、
   再帰の深さはパターンの深さで抑えられる。 *)

open Aux
open Syntax
open Type
module T = Tree.Tree

(* ## 10.2 内部パターン `ipat`

   Keleut の `match` は後置で、スクルティニを 1 つだけ取る(`v match { ... }`)。
   そのため、行列の入口の列は常に 1 列である。
   1 列でも表現力は落ちない。
   タプルは `_item` ラベルのレコードの糖衣なので、`(a, b) match { ... }` の 1 列は、
   先頭で `CRecord [_item; _item]` に specialize したときに 2 列に開く。
   複数の列を持つ行列は、この展開の途中で内部的に現れるだけである。

   表層の `T.pat` はそのまま行列に載せず、ここで内部形 `ipat` に写す。
   この正規化で消えるものが 3 つある。

   | 表層 | 内部 | 消える理由 |
   |---|---|---|
   | `PVar x` / `PWildcard` | `IWild` | 束縛名は網羅性に関係しない |
   | `PAnnot (p, ty)` | `p` の変換結果 | 注釈は第11章が処理済み |
   | `PCtor` のラベル指定と省略 | 宣言順に整列した `ipat list` | §10.3 で述べる |

   `PVar` を `IWild` にまとめておくと、以降のすべての箇所で `IWild` の 1 つの分岐だけを見れば済む。

   不変条件は 2 つある。
   `ICtor` の第 2 成分は、フィールドの宣言順に整列している。
   `IRecord` の第 2 成分(closed?)は、表示のためだけに持つ。 *)

type lit = LBool of bool | LText of string | LNum of string

type ipat =
  | IWild
  | ILit of lit
  | IVariant of oid * ipat
  | ICtor of oid * ipat list (* ctor、フィールド宣言順に整列済み *)
  | IRecord of (oid * ipat) list * bool (* フィールド列, closed? *)

(* ## 10.3 数値の正規化とフィールドの整列

   ### 数値は字面でなく値で比べる

   `case 1` と `case 0x1` は同じ値である。
   字面のまま `ILit` に入れると、後者が別のコンストラクタに見え、冗長な節を検出できない。

   ここでの同じ値とは、実行時の照合で一致することをいう。
   第14章のパターン照合は、値の型に従って字面を読み直す。
   `VInt32` なら `Int32.of_string`、`VInt64` なら `Int64.of_string`、
   `VFloat64` なら `float_of_string` で読み、その値が等しければ一致する。
   一方、網羅性検査の正規化は列の型を知らない。

   正規化は、数値の字面を比較に使う鍵に写す。
   このとき、同じ値を同じ鍵にするだけでなく、違う値を違う鍵にしなければならない。
   列の型を知らないまま 1 通りの読みで鍵を作ると、どの読みを選んでも、
   違う値が同じ鍵になる場合が生じる。
   たとえば native int(63 ビット)で読むと、
   `0x7FFFFFFFFFFFFFFF` が -1 に折り返して `case -1` と同じ鍵になる。
   その結果、検査は到達できる節に到達不能の警告を出す。
   Int64 で読むと、Int32 の列で `4294967295` と `0xFFFFFFFF` が同じ鍵になる。
   前者は Int32 では読めず、どの値にも一致しないが、後者は -1 に折り返して一致する。
   この場合も、検査は到達できる節に到達不能の警告を出す。

   そこで鍵は、3 通りの読みの積にする。
   字面を `Int32`、`Int64`、`Float64` のそれぞれで読み、3 つの成分を並べたものを鍵とする。
   読めなかった成分は、読めないことを表す印 `X` にする。
   すべての読みで等しい字面だけが同じ鍵になる。
   そのため、列の型がどれであっても、違う値が同じ鍵になることはない。
   `1` と `0x1` はどの読みでも 1 なので、同じパターンになる。
   `1.` と `1.0` は浮動小数の読みだけが定義され、その値が等しいので、同じパターンになる。

   浮動小数の成分は、`norm_float` で ±0.0 を 1 つにまとめる。
   実行時の IEEE の `=` が ±0.0 を等しいとみなすからである。
   `%.17g` は binary64 の値を一意に決めるので、異なる値は必ず別の成分になる。
   第12章 §12.7 の最短表現を使わないのは、鍵は誰にも見せないので桁を詰める理由がなく、
   章をまたぐ依存も作らずに済むからである。
   `1e999` と `1e1000` は同じ成分になるが、どちらも実行時には infinity なので正しい。
   NaN はリテラルとして書けないので考えない。

   読めない成分を例外にせず印にするのは、ここが評価ではなく検査だからである。
   網羅性検査は値を作る必要がないので、読めない成分は印のまま鍵に使えば足りる。
   桁あふれした数値リテラルは型検査を通る。
   第11章(elab.ml)の `number_ty` は接尾辞と浮動小数かどうかだけを見て、`n_text` の中身は読まない。
   範囲外のリテラルを落とすのは第14章(interp.ml)である。
   評価の時点で「数値リテラルが範囲外です」を出し、終了コード 3 で終わる。
   網羅性検査で例外を投げると、利用者には網羅性検査の内部エラーが届き、本当の原因が見えなくなる。

   残る不完全性は、どれも見逃す側の誤りである。
   積の鍵は、列の型で読んだ鍵より細かい。
   そのため、実行時には同じ値になる組を別の鍵にし、本当の冗長を見逃す。
   たとえば Int32 の列では、`case 0xFFFFFFFF` と `case -1` はどちらも `-1l` と一致する。
   しかし、積の鍵ではこの 2 つは別の鍵になる。
   また、列の型で読めない字面の節(Int32 の列の `case 4294967295`)はどの値にも一致しないが、
   この節を報告する診断はない。
   式の位置では同じ字面が実行時エラーになるので、パターンと式で扱いが対称でない。
   両方を直すには、スクルティニの型を `convert` に渡す必要がある(入れ子のパターンの型も要る)。
   これは設計を大きく変えるので、Diktor は積の鍵にとどめる。

   ### `PCtor` は解決結果を読んで宣言順に並べ替える

   Keleut のコンストラクタパターンは、ラベル指定とフィールドの省略を許す。
   たとえば `case Cons(tail = t)` と書ける(sample.kel §6)。
   省略したフィールドは `_` とみなす。
   第11章は、パターンの引数とフィールドの対応を `RCtorPat (data, ctor, field_to_arg)` として木に書き込む。
   `field_to_arg` はフィールドの宣言位置から実引数の位置への写像で、`None` が省略を表す。

   ここで宣言順に並べ直しておくと、以降の `arity`、`sub_types`、`rebuild` は、
   すべて宣言順という 1 つの約束の上で書ける。
   `ICtor` の引数の列と `ctor_fields` の並びは常に同じ順序であり、
   この約束が `specialize` の展開する列と `sub_types` の返す型を対応させる。

   `PCtor` に解決結果が書かれていなければ、`convert` は `bug` で落とす。
   これは利用者のプログラムの誤りではなく第11章の実装の誤りなので、
   型エラーではなく内部エラーとして報告する。 *)

(* 浮動小数の読みの正規化。±0.0 は実行時の IEEE の = に合わせて 1 つにまとめる。
   %.17g は binary64 の値を一意に決める(この鍵は誰にも見せない) *)
let norm_float f = if f = 0.0 then "0" else Printf.sprintf "%.17g" f

(* 鍵は Int32 / Int64 / Float64 の 3 通りの読みの積(§10.3)。
   検査は列の型を知らないので、どの読みでも等しい字面だけを同じ鍵にする。
   こうすれば、列の型がどれであっても違う値が同じ鍵になることはない。誤るときは見逃す側で誤る。
   §10.10 の反例の候補も同じ norm_text で読み、鍵の形をこの関数に閉じ込める *)
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
      (* 引数の列は外側のパターンで束縛する。内側でもう一度分解して
         assert false で塞ぐと、到達しないはずの分岐の例外が bug の [BUG]
         前置を持たず、§16.8 の catch-all に「内部エラー」として拾われる。
         そうなると、ほかの防御の分岐と分類も文言も揃わない *)
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

(* ## 10.4 コンストラクタ、arity、引数の型

   行列の先頭列を割るときの単位が `ctor` である。

   | コンストラクタ | arity | 型の取り出し元 |
   |---|---|---|
   | `CVariant l` | 1 | ヴァリアント行の `l` フィールド |
   | `CData c` | フィールド数 | 宣言表と、型引数の代入 |
   | `CLit _` | 0 | なし |
   | `CRecord ls` | ラベル数 | レコード行のフィールド型 |

   Keleut の `newtype` のコンストラクタは複数のフィールドを持てるので、
   `CData` の arity は宣言表を引いて決める。
   コンストラクタ名は大域的に一意(第6章(decls.ml)の §6.6)なので、
   名前からコンストラクタの属するデータ型をたどれる。
   `data_of_ctor` が `ctor_owner` を引いてそのデータ型を求め、
   `ctor_fields` がフィールド宣言のリストを返す。
   この 2 段の表引きがあるので、`CData` はコンストラクタ名だけを持てばよい。

   `ctor_of` で注意が要るのは `IRecord` だけである。
   返す `CRecord` のラベル列は、パターンではなく型の行から取る。
   開いたレコードパターン `{x, ...}` は型より少ないフィールドしか書かないので、
   パターンを基準にすると列数が行ごとにずれる。
   行列のすべての行に共通する基準は、型の行だけである。

   `sub_types` は `CData` のときだけ手間がかかる。
   宣言表のフィールド型は型パラメータを `Generic` として持っているので、
   スクルティニの型の実引数を代入してから返す(`Unify.subst_params`)。
   `List[Int32]` の列を `Cons` で割ったら、引数の型は `Int32` と `List[Int32]` でなければならない。
   `A` と `List[A]` のままでは、入れ子のリテラルパターンと型が噛み合わない。

   ここで作る `new_var 0` は、行列の列数を合わせるための穴埋めである。
   引数の数が宣言と食い違うなど、型検査が既に別のエラーを出しているはずの場面でしか現れない。
   穴埋めの変数は `TVar` のまま残る。
   §10.9 の `close_row` が `unify` を掛けるのは、
   `repr` の結果が `TVariant` である型の行の尾部に限られる。
   そのため、穴埋めの変数が単一化に巻き込まれることはない。 *)

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

(* ## 10.5 レコードの整列

   レコードパターンを行列の列に並べるときは、ラベルの重複に注意が要る。
   レコードパターンをラベルからパターンへの写像(Map)に変換し、
   型の行のラベル順に引き直す方法は、Keleut では使えない。
   タプルは `_item` ラベルの連なりだからである。
   `(1, 2, 3)` のパターンは同じラベル `_item` を 3 つ持つので、
   Map にすると 3 つの要素が 1 つに潰れる。
   潰れた行列は列数が合わず、3 要素のタプルの網羅性検査がまるごと壊れる。

   正しい対応づけは、単一化の側の規約から決まる。
   行の中の重複ラベルは、最左一致(Scoped Labels)で対応する。
   つまり、型の k 番目の `_item` はパターンの k 番目の `_item` に対応する。
   違うラベルどうしの順序は意味を持たず、同じラベルどうしの相対的な順序だけが意味を持つ。

   そこで `align_record_pat` は、Map ではなくラベルごとのキューを使う。
   型の行のフィールドを左から順に見て、各ラベルについて、
   パターンの側でまだ使っていない最左の同名フィールドを取り出す。
   `used` 配列が、そのキューの消費済みの印である。
   書かれていないフィールドは `IWild` で埋まるので、
   開いたレコードパターンも閉じたパターンと同じ列数に揃う。

   レコードは直積であって直和ではないので、
   パターンに書かれていないフィールドを `_` で埋めても場合分けは増えない。
   そのため、この整列は情報を捨てずに列を揃える操作として安全である。 *)

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

(* ## 10.6 行列の操作 `specialize` と `default`

   アルゴリズムの全体が、この 2 つの操作の上に成り立つ。

   `specialize c rows` は、先頭列が `c` に一致しうる行だけを残す。

   - `IWild` の行は、どのコンストラクタにも一致するので残す。
     先頭には `c` の arity の数だけワイルドカードを並べ、列数を合わせる。
   - 同じコンストラクタの行は、引数を先頭に展開する。
     `ICtor` の引数は既に宣言順なので、`subs @ rest` と連結するだけで済む(§10.3 の約束による)。
   - 別のコンストラクタの行は落とす。

   `default_matrix rows` は逆に、先頭列がワイルドカードの行だけを残して先頭列を捨てる。
   これはシグネチャが完全でないとき、つまりまだ現れていないコンストラクタがありうるときに使う。
   その未知のコンストラクタに一致しうる行は、ワイルドカードの行だけだからである。

   `specialize` は、型を受け取る第 2 引数 `_ty` を使わない。
   レコードのラベル列は、`CRecord ls` 自身が持っているからである。

   `default_matrix` には変数パターンの分岐がない。
   §10.2 で `PVar` を `IWild` に正規化したので、`IWild` の 1 つの分岐で足りる。 *)

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

(* ## 10.7 完全シグネチャ

   `complete_sig` は、「この型の値は、このコンストラクタのどれかで必ず始まる」と言い切れるときだけ、
   コンストラクタの一覧を返す。
   `None` は「言い切れない」という意味で、「コンストラクタがない」という意味ではない。

   | 型 | 返す値 | 理由 |
   |---|---|---|
   | 閉じたヴァリアント行 | すべてのラベル | 行の尾部が `TRowEmpty` なら増えない |
   | 開いたヴァリアント行 | `None` | 行変数が残るので、ラベルはいくらでも増えうる |
   | `newtype`(不透明でない) | 宣言表のすべてのコンストラクタ | 宣言が閉じている |
   | `newtype X = ???`(不透明) | `None` | 中身を知らないので数え上げられない |
   | `Never` | `Some []` | コンストラクタがゼロ個 |
   | `Boolean` | true と false | 2 値だけ |
   | レコード | 単一の `CRecord` | 直積は 1 つの場合 |
   | `Int32` / `String` など | `None` | 有限個に数え上げない |

   ### `Never` は節がなくても網羅的

   `Never` は値を持たない型である(sample.kel §6)。
   `dd_ctors = []` で登録されているので、`complete_sig` は `Some []` を返す。
   これは「この型の値は 0 通りのコンストラクタのどれかで始まる」、
   つまり値が存在しないという主張である。
   そのため、次の `match` は節がゼロ個でも網羅的である。

   ```
   let absurd[A](n: Never): A = n match {}
   ```

   文法が空の `match` 本体を許すのも、同じ理由による。
   この `Some []` は §10.10 で使う。

   ### 不透明な型は `None` を返す

   `Ref` や `Array` は、`newtype X = ???` と同じ不透明なデータ型として宣言表に登録されている。
   中身のコンストラクタを知らないので、どんな `match` を書いても、
   ワイルドカードなしでは網羅を主張できない。
   ここで `Some []` を返すと「`Ref` の値は存在しない」という誤った主張になり、
   網羅性の判定だけでなく、到達不能の警告も誤る。
   コンストラクタがないことと、コンストラクタを知らないことは別であり、
   `Some []` と `None` はこの 2 つを区別する。

   ### レコードの行が開いていても構わない

   レコード型の行の尾部が変数のままでも、`Some [CRecord 既知のラベル]` を返す。
   直積は場合分けを増やさないので、未知のフィールドが増えても、
   レコードは 1 つの場合だという主張は変わらない。
   ヴァリアントの開いた行が `None` になるのとは非対称だが、これは和と積の違いによる。

   `complete_sig` に `Unit` 専用の分岐がないのは、Keleut の `()` が空レコードだからである。
   `Unit` は `TRecord` の分岐で `CRecord []`(arity 0)になり、ほかのレコードと同じ経路をたどる。 *)

(* Boolean の oid。intern は表を引くので、complete_sig を呼ぶたびに引かず、
   1 回で済ませる。Type.intern_map は reset されない(第1章 §1.2)ので、
   初期化時に確定してよい *)
let oid_boolean = intern "Boolean"

let complete_sig ty =
  match repr ty with
  | TVariant row -> (
      let fs, tail = row_fields row in
      match repr tail with
      | TRowEmpty -> Some (List.sort_uniq compare (List.map (fun (l, _) -> CVariant l) fs))
      | _ -> None (* 開いた行ではラベルはいくらでも増えうる *))
  | TCon (n, _) when Hashtbl.mem Decls.datas n ->
      let dd = Hashtbl.find Decls.datas n in
      if dd.Decls.dd_opaque then None else Some (List.map (fun ct -> CData ct.Decls.ct_name) dd.Decls.dd_ctors)
  | TCon (n, []) when n = oid_boolean -> Some [ CLit (LBool true); CLit (LBool false) ]
  | TRecord row -> Some [ CRecord (List.map fst (fst (row_fields row))) ]
  | _ -> None

(* ## 10.8 `rebuild` による反例の組み立て直し

   アルゴリズム I は、行列を割りながら降りていき、いちばん底でワイルドカードのベクトルを見つける。
   帰り道で、それを元の形に組み直すのが `rebuild` である。
   `rebuild c ws` の `ws` は、コンストラクタ `c` の引数と残りの列を連結した 1 本のリストである。
   `rebuild` は、`ws` の先頭の arity 個を `c` で包み直し、残りの列の前に置く。

   `split_at` は、先頭の n 個とその残りを 1 回の走査で返す。
   OCaml の標準ライブラリにはなく、`List.filteri` の類では書きにくいので、ここで定義する。

   `split_at` は `ws` が短くても落ちないが、`rebuild` 全体が例外を投げないわけではない。
   `CRecord` の分岐の `List.combine ls fs` は長さが違えば `Invalid_argument` を送出し、
   `CVariant` の分岐の `List.hd ws` は空リストに対して `Failure` を送出する。
   `rebuild` は、行列とベクトルと型のリストが同じ幅で進むという §10.11 の不変条件に依存している。
   この不変条件が破れたら、内部エラーとして落ちる。
   反例の表示のためだけに防御の分岐を足すことはしない。

   `IRecord` を `true`(閉じている)で組むのは、
   反例として見せるレコードは常にすべてのフィールドを書き下したものだからである。
   この `true` が、§10.12 のタプルの再糖衣化の条件の 1 つを満たす。 *)

(* 先頭 n 個とその残りに割る。stdlib になく、List.filteri の類では書きにくい。
   ws が n より短くても落ちない(§10.11 の不変条件が破れたときの被害を、
   ここで増やさないため) *)
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

   行多相のヴァリアントには固有の問題がある。
   `#Lft(n)` の型は `#Lft(τ) | R` と開いているので、
   `match` を書いた時点では、ほかにどんなラベルがありうるかが分からない。
   開いたままだと `complete_sig` は常に `None` を返し、
   構造的ヴァリアントに対するどんな `match` にもワイルドカードの節が要ることになる。

   そこで、ある列にワイルドカードの節がなければ、その列の型の行を閉じる、という規則を置く。
   利用者が `case _` を書かなかったことを、「これですべてのつもりだ」という意思表示とみなし、
   行の尾部を `TRowEmpty` に単一化する。
   これにより、次の `t` は `#Lft(Int32) | #Rgt(A)` に確定し、ワイルドカードなしで網羅的になる。

   ```
   let closed = fn(t) => t match { case #Lft(n) => n + 0  case #Rgt(_) => 0 }
   ```

   逆に `case _` を書けば行は開いたまま(`#Lft(Int32) | R1`)で、
   その関数はより多くのラベルを受け取れる多相な関数になる。
   利用者は、どちらが欲しいかをワイルドカードの有無で選べる。

   `roots <> []` の条件は、すべての行がワイルドカードのときに、
   意味もなく行を閉じないためのものである。
   列にコンストラクタが 1 つも現れていなければ、利用者はその列について何も主張していない。

   `close_variant_rows` は、行列を割りながら再帰的に降りる。
   コンストラクタごとに specialize した先でも、
   入れ子のヴァリアントの行を閉じる必要があるからである。

   行を閉じる操作は型を書き換えるので、いつ走らせるかで結果が変わる。
   そのため、§10.13 の検査キューが要る。

   宣言した `newtype` を使えば型は最初から閉じているので、行を閉じる操作も型注釈も要らない。
   構造的ヴァリアントは、宣言を書くほどでもない使い捨ての和のための道具である。 *)

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

(* ## 10.10 アルゴリズム I による反例の構成

   `missing rows tys` は、`rows` のどの行にも一致しない値を、パターンの形で 1 つ返す。
   返り値が `None` なら網羅的で、`Some w` なら `w` が反例である。

   再帰の底は、列が尽きたときである。
   行が 1 本でも残っていればすべて覆われているので `None` を返し、
   1 本もなければ空のベクトルが反例になる。

   分岐は、先頭列のシグネチャが完全かどうかで決まる。

   - 完全なら、コンストラクタごとに specialize して降り、
     最初に見つかった反例を `rebuild` で包み直す。
     すべてのコンストラクタで `None` なら網羅的である。
   - 完全でなければ、`default_matrix` で降り、帰りに先頭へまだ使われていないコンストラクタを置く。
     それもなければワイルドカードを置く。

   ### `Some []` を先に判定する

   シグネチャが完全かどうかは `sig_complete` が判定し、§10.11 の `useful` も同じ関数を使う。
   `sig_complete` は、コンストラクタがゼロ個のシグネチャ `Some []` を先に判定して真を返す。
   コンストラクタがゼロ個の型では、節がゼロ個でもすべてのコンストラクタを覆っている。

   完全性の条件に `roots <> []` を加えると、コンストラクタがゼロ個の型で答えが逆になる。
   `Never` に対する `n match {}` は roots も空なので、網羅的なのに、
   `_` が漏れているという非網羅の警告を出してしまう。
   一方、`Some s` の分岐に `roots <> []` の条件は要らない。
   この分岐に来る `s` は空でないので、`roots` が空なら `List.for_all` は必ず偽になる。

   ### 整数、浮動小数、文字列の反例

   シグネチャが `None` の型(`Int32` など)では、使われていないコンストラクタを一覧から選べない。
   そこで、まだパターンに現れていない値を候補の並びから探し、具体的な反例にする。
   `case 0 => ... case 1 => ...` に対しては、`_` が漏れていると言うより、
   `2` が漏れていると言うほうが役に立つ。
   候補の並びは 3 通りある。

   - 整数：0, 1, 2, …(`string_of_int`)
   - 浮動小数：0.0, 1.0, 2.0, …(表示は `%.1f`)
   - 文字列：空文字列, a, aa, …(`String.make i` による a の繰り返し)

   どの場合も roots(パターンに現れたリテラル)は有限なので、探索は必ず止まる。

   候補と roots の突き合わせには §10.3 の鍵を使い、表示には読める字面を使う。
   候補の字面をそのまま鍵と比べると、Float64 の列では `case 0.0` の鍵と字面 `0` が一致しない。
   そのため、既に覆われている `0` を反例として示してしまう。
   非網羅という結論は正しくても、利用者がその値で試すと第 1 節に当たるので、
   警告が誤っているように見える。

   反例に出す字面は、常に Keleut のリテラルとして読めるものにする。
   §10.3 の鍵(`%.17g` の表記や、±0 のまとめ)は同値判定のための内部表現なので、表示には使わない。

   `fn(x) => x match { ... }` のように、注釈のない引数をスクルティニとする `match` では、
   網羅性検査が宣言の終わりの既定化より先に走る。
   そのため、列の型がまだ既定化前の弱い変数であることがある。
   そのときは、`Fractional` 述語が付いていれば浮動小数の候補を使う。
   整数の字面 `2` は、浮動小数の列には書けない反例だからである。 *)

let roots_of rows ty =
  List.sort_uniq compare (List.concat_map (fun r -> match r with h :: _ -> Option.to_list (ctor_of h ty) | [] -> []) rows)

(* シグネチャが完全か。Some [](コンストラクタがゼロ個の Never)は、節がなくても
   網羅的である。Some s の分岐に roots <> [] は要らない。s が空でなければ、
   roots が空のとき List.for_all は必ず偽になる(§10.10) *)
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
                  (* シグネチャがない型(Int32/Int64/Float64/String)は、まだ
                     使われていない値を候補の並びから探して具体的な反例にする。
                     候補は必ず読める字面にし、鍵(§10.3)は表示しない *)
                  let used_num = List.filter_map (function CLit (LNum n) -> Some n | _ -> None) roots in
                  let used_txt = List.filter_map (function CLit (LText s) -> Some s | _ -> None) roots in
                  if used_txt <> [] then
                    (* 候補の並びは空文字列, a, aa, …。roots は有限なので必ず止まる *)
                    let rec fresh i =
                      let s = String.make i 'a' in
                      if List.mem s used_txt then fresh (i + 1) else s
                    in
                    ILit (LText (fresh 0))
                  else if used_num = [] then IWild
                  else
                    (* 列がまだ既定化前の弱い変数のとき(注釈のない引数)は、
                       Fractional 述語で浮動小数の列だと分かる。整数の字面を
                       出すと、その列には書けない反例になる *)
                    let is_float_col =
                      match ty with
                      | TCon (n, []) -> n = intern "Float64"
                      | TVar { contents = Unbound i } -> List.mem cls_fractional i.vcls
                      | _ -> false
                    in
                    if is_float_col then
                      (* 候補は 0.0, 1.0, 2.0, …。突き合わせは §10.3 と同じ鍵
                         (norm_text)で行い、見せるのは読める字面のほうにする *)
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

(* ## 10.11 アルゴリズム U による冗長な節の検出

   冗長な節は `useful` で検出する。
   `useful rows q tys` は、`rows` のどの行にも一致しないが `q` には一致する値があるかどうかを返す。
   i 番目の節を調べるときは、`rows` にそれより前の節をすべて入れ、`q` に i 番目の節を置く。
   偽が返れば、i 番目の節に来る値はないので、その節は冗長である。

   構造は `missing` と対称で、違いは行列を割る基準を `q` から取ることである。

   - `q` の先頭がコンストラクタなら、そのコンストラクタで行列と `q` の両方を specialize して降りる。
   - `q` の先頭がワイルドカードなら、シグネチャが完全なときだけコンストラクタごとに調べ、
     どれか 1 つでも useful なら useful とする。
     完全でなければ `default_matrix` で降りる。

   底の `rows = []` は、まだどの行にも覆われていない値が残っていることを表す。

   ここでも `sig_complete` が `Some []` を先に判定する。
   `Never` を相手にした節は、`List.exists` が空リストに対して偽を返すので useful にならず、
   到達不能と報告される。
   値のない型に対する節は、実際にどんな値でも実行されないので、この報告は正しい。

   `List.hd q` が安全なのは、`q` の長さが常に `tys` の長さと等しいからである。
   `specialize` と `sub_types` は `q` と `tys` を同じだけ伸ばし、
   `default_matrix` で降りるときは `List.tl` と `tys_tail` が同じだけ縮める。
   行列の各行、ベクトル `q`、型のリスト `tys` は、常に同じ幅で進む。 *)

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

(* ## 10.12 反例の表示

   反例は `ipat` のまま出しても読めないので、表層構文に戻して見せる。
   第9章(show.ml)が型に対して行っていることの、パターン版である。

   再糖衣化は 2 か所ある。

   - **ペイロードのないヴァリアント**：`#Even` の内部形は `IVariant (l, IRecord ([], true))` で、
     空レコード(`Unit`)を引数に取る形である。
     これを `#Even(())` ではなく `#Even` と表示する。
   - **タプル**：閉じたレコードで、すべてのフィールドのラベルが `_item` なら、
     `(a, b)` と括弧で並べる。
     そうでなければ波括弧のレコード記法で書く。
     `(false, false)` という反例はこの経路で出る。
     `{_item = false, _item = false}` と表示すると、利用者にはタプルの反例だと読み取りにくい。

   1 要素のタプルは、`(a,)` と末尾にカンマを打って表示する(sample.kel:182)。
   `(false)` はパターンとしてはグループ化なので、
   貼り戻しても 1 要素のタプルのパターンにならないからである。
   第9章 §9.3(型)と第12章 §12.7(値)も同じ規則に従う。
   仕様 §4(sample.kel:179-180)は、この戻し方の対象を
   「型の表示、型エラーの文面、実行時エラーに出る値、網羅性警告の反例の 4 つすべて」と定めている。
   本章の反例は、その 4 つ目にあたる。

   フィールドが空で閉じているレコードは `()` と表示する。
   これは `Unit` の値そのものなので、タプルの規則より先に判定する。
   パターンの位置で空の行を `()` と書くのは、仕様の書き分けに従っている(sample.kel:182)。
   型の位置に出る `{}` とは字面が違うが、指すものは同じである(sample.kel:183-185)。

   Keleut はタプル専用の型(`TTuple`)を持たず、タプルを `_item` 行の糖衣として表す(第1章)。
   型を単純にした分、表示するときにタプルの形へ戻す処理が要り、
   本章と第9章と第12章がそれぞれ受け持つ。 *)

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

(* ## 10.13 検査キュー

   Diktor は、`match` を推論したその場では網羅性を検査しない。
   検査するものをキューに積み、束縛の一般化の直前にまとめて検査する。
   検査を遅らせる理由は 2 つある。

   ### 理由 1:一般化の後では行を閉じられない

   §10.9 の `close_variant_rows` は `unify` を呼ぶ。
   一方、`generalize` は型変数を `Generic` に書き換える。
   `Generic` は型スキーマの量化変数を表すので、それに `unify` を掛けるのは内部エラーである。
   第8章の `bind` も `occurs_adjust` も、`Generic` に出会うと `bug` で落とす。
   したがって、検査は必ず一般化より前に走らなければならない。

   ### 理由 2:早すぎると行がまだすべてのラベルを集めていない

   逆に、`match` の時点で行を閉じるのも困る。

   ```
   let f = fn(t) => { t match { case #A => 1  case #B => 2 }; g(t) }
   ```

   ここで `g` が `#C` を要求するなら、
   `match` の直後に行を閉じた `t` は `g` に渡せず、型エラーになる。
   束縛の右辺をすべて推論し終えてから閉じれば、`t` の行は `#A | #B | #C` まで育っており、
   検査は、`#C(_)` が漏れているという正しい警告を出す。
   型エラーと網羅性の警告のどちらを出すかが、検査を走らせる時点で変わる。

   行を閉じる操作は型を書き換えるので、検査はできるだけ遅く、ただし一般化より前に走らせる。
   この 2 つの制約を満たす時点は、各 let 束縛群の `generalize` の直前しかない。
   第11章(elab.ml)はそこで `drain` を呼ぶ。

   `queue` はリストの先頭に積み、`drain` が `List.rev` で積んだ順に戻す。
   末尾に `@` で足すと、積んだ数の二乗の時間がかかるからである。
   ゴールデンテストはこの順序に依存している。

   この方式には留保が 2 つある。

   1 つ目の留保は、`drain` が内側の let の一般化の直前にも走り、
   それまでに積まれたエントリをすべて処理することである。
   上の例の `match` を `let a = t match { … }` と局所束縛に包むと、
   内側の `drain` が `t` の行をそこで閉じ、`g(t)` は警告ではなく型エラーになる。
   `match` の直後に `let b = 1` のような無関係な局所束縛を置いた場合も、同じく型エラーになる。
   検査を遅らせられるのは、`match` の後で最初に `drain` を呼ぶ let 束縛までである。
   そのため第11章は、関数の引数と return 節の検査エントリを、本体の推論より後に積む。
   本体より先に積むと、本体の中の let の `drain` がそのエントリを処理して行を閉じ、
   受理されるはずのプログラムが型エラーになる。

   2 つ目の留保は、警告がソース順に並ぶのは宣言どうしのあいだに限られることである。
   1 つの宣言の中では、引数パターンの警告は(本体の後に積むので)本体の `match` の警告より後に出る。

   ### ガード付き節は網羅性に数えない

   `case P if cond => e` は、実行時に `cond` が偽なら次の節へ進む。
   つまり、その節が必ず一致するとは限らないので、被覆として数えると誤って網羅的と判定してしまう。
   仕様も sample.kel:322-324 で、網羅性検査はガード付きの節を必ず一致する節として数えず、
   そのため最後にガードのない節が必要になる、と定めている。

   そこで、行列を用途によって使い分ける。

   | 用途 | 使う行 | 理由 |
   |---|---|---|
   | 行を閉じる / 網羅性(`missing`) | ガードのない節だけ | 覆うと言えるのはこれだけ |
   | 到達可能性(`useful`)の検査対象 | すべての節 | ガード付き節も冗長になりうる |
   | 到達可能性の被覆側 | 先行するガードのない節だけ | 1 行目と同じ |

   ガード付き節は、ほかの節を覆わないが、ほかの節に覆われることはある、という非対称な扱いになる。
   節番号(`第 %d 節`)はすべての節を通した 1 始まりの番号で、ガード付き節も飛ばさずに数える。
   利用者が見ているのはソースに並んだ節であって、行列に載った行ではないからである。

   `reset` は、宣言の処理を始める前にキューを空にする。
   キューは大域状態である。
   空にしないと、前のファイルの処理やエラーで中断した推論が積んだエントリが残る。 *)

type entry = { qe_rows : (T.pat * bool (* ガードつき *)) list; qe_ty : ty }

let pending : entry list ref = ref []

(* 先頭に積み、積んだ順は drain の List.rev が戻す。末尾に @ で足すと、
   積んだ数の二乗の時間がかかる(§10.13) *)
let queue rows ty = pending := { qe_rows = rows; qe_ty = ty } :: !pending

let check_entry { qe_rows; qe_ty } =
  let out = ref [] in
  let all = List.map (fun (p, guarded) -> ([ convert p ], guarded)) qe_rows in
  let unguarded = List.filter_map (fun (r, g) -> if g then None else Some r) all in
  let tys = [ qe_ty ] in
  close_variant_rows unguarded tys;
  (* エントリの行が 1 つなら、節番号を出さない。
     let のパターン束縛、関数の引数、return 節には節がなく、
     節番号を出すと、利用者が存在しない第 1 節を探すことになる。
     節が 1 つだけの match も同じ扱いになる *)
  let single = match qe_rows with [ _ ] -> true | _ -> false in
  (* ガード付き節は必ず一致する節として数えない(sample.kel:322-324)ので、網羅性の判定から除く *)
  (match missing unguarded tys with
  | Some w -> out := !out @ [ "match が非網羅的です。例えば " ^ String.concat ", " (List.map show_ipat w) ^ " が漏れています" ]
  | None -> ());
  (* 到達不能の判定では、先行するガードのない節だけを被覆として数える *)
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
