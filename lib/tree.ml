(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第5章 精緻化木

   第3章(parser.mly)が返す AST は、ソースに書いてあることしか持たない。
   しかし実行するには、ソースに書いていないことをいくつも知る必要がある。

   | 実行に要る知識 | ソースだけでは決まらない理由 |
   |---|---|
   | `perform write(x)` がどの操作か | `Console.write` と `File.write` のように、同じ名前の操作が並存しうる |
   | `Point(y = 2, x = 1)` の引数をどの順に格納するか | ラベル指定で引数を並べ替えられる |
   | `handle` の節の種類 | 構文上はどの節も `match` の節と同じ形である |
   | `1` が Int32、Int64、Float64 のどれか | 既定化が決める |
   | トップレベルの名前 `f` がどの宣言の値か | 同名の再束縛や module の値同義語で、同じ綴りが別の宣言を指しうる |

   これらはすべて型検査が決める。
   本実装の型検査は、決めた答えを木そのものに書き戻す。
   型検査を、真偽を返す判定器ではなく、入力の木を実行できる木へ育てる関数として実装している。
   この育てる操作を精緻化(elaboration)と呼ぶ。
   本章のファイルは、精緻化の結果を書き込む場所だけを用意する。

   この設計により、第14章(interp.ml)は、表に挙げた 5 つのことを決め直さずに済む。
   評価器がこれらを決め直すなら、elab と interp が同じ解決規則を二重に実装することになり、
   片方だけを変更したときに両者が食い違う。
   型検査が見ていたエフェクトと実行時に perform されるエフェクトが違う、という種類の不具合は、
   再現例を作るのが難しく、直すのはさらに難しい。
   局所の変数名だけは、評価器が実行時に局所環境から引く。
   局所の束縛の規則は単純で、elab と評価器の規則が食い違う余地が小さいからである。
   トップレベルの値は、elab が解決した実体(`RVar`)を評価器がそのまま使う(第14章 §14.4)。

   ## 前章から受け取るもの

   第1章(syntax.ml)の `Syntax.Make` ファンクタ(AST をノードに付くデータでパラメータ化したもの)と、
   第3章(parser.mly)が組み立てた木を受け取る。

   ## 次章へ渡すもの

   `Tree.Tree` を渡す。
   これは、精緻化用のデータを載せて具体化した AST 型である。
   第6章(decls.ml)、第10章(exhaust.ml)、第11章(elab.ml)、第12章(value.ml)、
   第14章(interp.ml)の 5 つのファイルは、`module T = Tree.Tree` の 1 行で精緻化木の型を取り込む。
   木を扱わない章(第7章(prims.ml)など)はこの行を持たない。
   第8章(unify.ml)は木を扱わないが、§5.1b の証拠の型を使う。 *)
open Aux

(* ## 5.1 elab から interp への受け渡し

   `resolved` は、型検査が解いた答えのうち、実行時には解けないものの一覧である。
   ここに並ぶ 5 つは、どれも必要な情報が型検査の最中にしか揃わない。
   たとえば、perform を書いた位置のエフェクト行に現れるラベルは、実行時には残っていない。
   コンストラクタのフィールドの順序は、宣言表を引かないと分からない。
   節の分類は、宣言されたエフェクトの操作の集合を知って初めてできる。

   書くのは第11章(elab.ml)で、読むのは第14章(interp.ml)と第10章(exhaust.ml)である。
   それぞれの値の行き先は次のとおりである。

   | 値 | 書く場所 | 読む場所 | 読む側の用途 |
   |---|---|---|---|
   | `RVar` | トップレベルの値を指す `Ident` | 第14章 | 値の実体(組み込み、クラスメソッド、宣言した値) |
   | `ROp` | `Perform` と操作節 | 第14章 | perform する操作、ハンドラの節の選択 |
   | `RReturnClause` | `return` 節 | 第14章 | 正常終了時に実行する節の選択 |
   | `RCancelClause` | `handle` の `cancel` 節 | 第14章 | 巻き戻し時に実行する節の選択 |
   | `RCtor` | `Construct` と裸のコンストラクタ参照 | 第14章 | 格納位置と、引数のないコンストラクタの値 |
   | `RCtorPat` | `PCtor` | 第14章と第10章 | 照合するフィールドと、省略したフィールドの補完 |

   ### ROp と完全な操作名

   Keleut では、同じ名前の操作を複数のエフェクトで宣言できる。
   標準環境の `Console.write` と、sample.kel が宣言する `File.write` が、同じ操作名を持つ。
   そのため、`perform write(x)` の `write` がどちらの操作かは、
   その地点のエフェクト行を見ないと決まらない。
   このように候補が 2 つ以上あるときは、行に現れる候補が 1 つだけならそれを選び、
   1 つも現れないときと 2 つ以上現れるときは修飾を求める(第11章 §11.20)。
   行の中のラベルの位置は使わないので、ラベルの順序だけが違う行の下では同じ操作に解決する。
   静的な解決と実行時の捕捉が食い違わないのは、
   次の段落のとおり、解決した完全な操作名を実行時まで運ぶからである(第11章 §11.20)。

   解決の結果は、完全な操作名(`Console.write` のような文字列を intern した oid)として `ROp` に入る。
   第14章はこの oid をそのまま OCaml のエフェクトに載せて perform し、
   ハンドラの側も oid が一致するかどうかだけを見る。
   操作名の解決を実行時に行うことはない。

   ### RReturnClause と RCancelClause

   `handle` の節は、構文上はただのパターン節である。
   どれが操作節で、どれが `return` 節や `cancel` 節かは、
   頭のコンストラクタ名を宣言表と突き合わせて初めて分かる。
   この分類は第11章が済ませてここに書くので、
   第14章は `get_resolved` の値を等値比較するだけで 3 種類の節を区別できる。

   ### RCtor と RCtorPat の対応表の向き

   `RCtor` の `int array` は、添字が実引数の位置、値がフィールドの位置である。
   式でのコンストラクタ適用はすべてのフィールドを要求し(欠けるとエラーになる)、
   実引数がすべてのフィールドを覆うので、option は要らない。
   第14章は引数をソースの順に評価し、格納先だけをこの表で宣言したフィールドの位置へ振り替える。
   そのため、副作用のある引数をラベル指定で並べ替えて書いても、評価器は書いた順に評価する。

   `RCtor` が付くのは `Construct` ノードだけではない。
   `None` のような引数のないコンストラクタは `Ident` として構文解析されるので、
   第11章は `Ident` の経路からも同じ `elab_construct` を呼び、
   その `Ident` ノードにも `RCtor` を書く。
   この場合の対応表は長さ 0 の配列である。
   第14章は、局所環境に名前が無く、`RVar` も無いときに、
   この `RCtor` を引き、フィールドが 0 個の値をその場で作る(§14.4)。
   この経路があるので、裸のコンストラクタ参照は「未束縛の変数」にならない。

   `RCtorPat` の `int option array` は逆向きで、添字がフィールドの位置、値が実引数の位置である。
   パターンではフィールドを省略できるので、`None` が要る。
   第10章(exhaust.ml)は、この `None` を `IWild` に変換してから行列に載せる。
   ラベル指定のパターンで省略したフィールドは、こうしてワイルドカードとして扱われる。

   片方の表だけを持ち、もう片方を逆写像として計算することもできるが、そうはしない。
   逆写像を作る側で、ラベルの探索と省略の補完の規則をもう一度書くことになるからである。
   同じ規則を 2 か所に実装すると、両者が食い違いうる。
   本章の木は、その食い違いを避けるためにある。

   向きが違うのは、使い方が違うからでもある。
   式の評価は引数を順にたどり、各引数の格納先を表で引く。
   パターンの照合はフィールドを順にたどり、各フィールドの部分パターンを表で引く。 *)
(* トップレベルの値の実体。組み込みの値は名前で、クラスメソッドは修飾名で、
   宣言した値は束縛ノードの oid と束縛した名前の組で指す *)
type gref =
  | GBuiltin of string
  | GMethod of string (* Cls.m *)
  | GDecl of oid * string

type resolved =
  | RVar of gref (* Ident。トップレベルの値の参照 *)
  | ROp of oid (* perform と handle の操作節。Console.write のような完全な操作名の oid *)
  | RReturnClause (* handle の return 節 *)
  | RCancelClause (* handle の cancel 節 *)
  | RCtor of oid * oid * int array (* Construct。data、ctor、実引数の位置 → フィールドの位置 *)
  | RCtorPat of oid * oid * int option array (* PCtor。data、ctor、フィールドの位置 → 実引数の位置(None は省略) *)

(* ## 5.1b 型クラスの制約の証拠

   型クラスのメソッドをどのインスタンスで呼ぶかは、型検査が型から決める。
   実行時の値は、この選択に関わらない。
   型検査は、制約付きのスキーマを具体化するたびに、制約ごとに**穴**(`hole`)を 1 つ作って木に書く。
   束縛の終わりに穴を解き、解を `h_sol` にその場で書く。
   評価器は、書かれた証拠から辞書を作ってメソッドを選ぶ。

   証拠(`evidence`)は 5 つの形を持つ。

   | 形 | 意味 |
   |---|---|
   | `EvParam k` | 囲む束縛かインスタンスが受け取る辞書パラメータ。鍵 `k` は(型変数の `vid`, クラスの oid) |
   | `EvInst (c, n, ps)` | (クラス `c`, 型構成子 `n`)のインスタンス。`ps` は前提の証拠で、順序はインスタンス表の `ii_premises` と同じ |
   | `EvRecord fs` | 閉じたレコード型の構造的な `Eq`。行の順のラベルと、フィールドの証拠 |
   | `EvVariant fs` | 閉じたヴァリアント型の構造的な `Eq` |
   | `EvHole h` | 後で解く穴。`h_sol` が `None` なら未解決 |

   穴の型 `h_ty` は単一化と共有する。
   穴を解く時点で `h_ty` を見れば、具体化した型変数がどの型に決まったかが分かる。
   木に書いた型が一般化を共有する仕組み(§5.2)と同じ考え方である。

   ノードに付く辞書の情報(`dict_info`)は 5 つの形を持つ。

   | 形 | 付くノード | 意味 |
   |---|---|---|
   | `DNone` | すべて | 辞書に関わらない |
   | `DUse hs` | 変数の参照、演算子、前置の `-` | この使用が渡す辞書の穴。スキーマの制約の正準順(第8章 §8.11) |
   | `DAbs ks` | 束縛、`extern`、式文 | この値が受け取る辞書パラメータの鍵の列(正準順) |
   | `DMethod (own, mk, adapter)` | インスタンスのメソッドの束縛 | `own` は実装を推論した型の辞書パラメータ、`mk` はクラスの宣言のメソッドの型のうちクラスパラメータを除く制約の鍵、`adapter` は実装に `own` の辞書を渡す証拠 |
   | `DInstance ks` | インスタンス宣言 | 前提の辞書パラメータの鍵の列(`ii_premises` の順) |

   書くのは第11章(elab.ml)で、解くのは第8章(unify.ml)、読むのは第14章(interp.ml)である。 *)

type dkey = oid * oid

type evidence =
  | EvParam of dkey
  | EvInst of oid * oid * evidence list
  | EvRecord of (oid * evidence) list
  | EvVariant of (oid * evidence) list
  | EvHole of hole

and hole = { h_id : oid; h_cls : oid; h_ty : Syntax.Type.ty; h_loc : Location.span; mutable h_sol : evidence option }

type dict_info =
  | DNone
  | DUse of hole list
  | DAbs of dkey list
  | DMethod of dkey list * dkey list * hole list
  | DInstance of dkey list

(* ## 5.2 ノードに付く 5 つのもの

   AST のすべてのノードに、`ElabData.t` が 1 つずつ付く。
   中身は次の 5 つである。

   - `oid`：ノードの同一性。物理等価(`==`)に頼らずにノードを指せる。
   - `loc`：ソース位置。パーサがノードを作るときに埋める。
   - `ty_field`：型検査が決めた型。`None` は、まだ精緻化されていないことを表す。
   - `resolved`：§5.1 の解決結果。
   - `dict`：§5.1b の辞書の情報。`DNone` は、辞書に関わらないことを表す。

   `allocate` が受け取るのは `loc` だけで、残りのフィールドは `None`(`dict` は `DNone`)から始まる。
   ノードを作るのは第3章(parser.mly)であって、型検査ではないからである。
   型検査は、すでにあるノードの空欄を埋めていくだけである。

   ### 可変フィールドである必要

   型を木に書き戻す設計は、一般化(generalize)が型変数をその場で書き換えることと組になっている。
   `set_ty` で書き込んだ型は、その後で一般化される型変数と同じ `ref` を共有している。
   そのため、後から一般化した結果が木の側にも反映される。
   一般化が新しい型を返す実装なら、木に書いた型は一般化する前の古い型のまま残る。

   評価器でこの経路を使うのは数値リテラルである。
   `1` の型は最初、`Integral` 述語の付いた新しい未定変数で、既定化が最後にそれを Int32 に落とす。
   第14章は評価のたびに `get_ty` で型を引き、
   `Int32.of_string`、`Int64.of_string`、`float_of_string` のどれを使うかを選ぶ。
   つまり、既定化の結果は木を通って評価器に届く。

   ### loc と oid の読み手

   `loc` は、型エラーのメッセージに位置を付けるために使う。
   第11章の `at_node` が `loc_of` で span を取り出し、
   位置のない `Type_error` に最も内側のノードの位置を付けて、`Type_error_at` として投げ直す。

   `oid_of` は、宣言がどの module に属するかを引くために使う。
   `Decls.decl_module` はノードの oid を鍵にしているので、第11章と第14章が `oid_of` を呼ぶ(§6.4)。

   `data` を呼ぶ箇所はない。
   ファンクタ越しに `ElabData.t` をまるごと取り出す唯一の関数として残してある。 *)
module ElabData = struct
  type t = {
    oid : oid;
    loc : Location.span;
    mutable ty_field : Syntax.Type.ty option;
    mutable resolved : resolved option;
    mutable dict : dict_info;
  }

  let allocate loc = { oid = new_oid (); loc; ty_field = None; resolved = None; dict = DNone }
end

(* ## 5.3 この木を独立したファイルに置く理由

   理由は 2 つある。

   1 つ目は、依存の循環を切るためである。
   この定義を第11章(elab.ml)に置くと、評価器も網羅性検査も、木を扱うために elab.ml に依存する。
   一方で elab.ml は網羅性検査の `Exhaust.queue` を呼ぶので、
   exhaust.ml と elab.ml が互いに依存して循環する。
   そこで、木の定義を依存関係の葉に置く。
   依存は一方向である。
   木を扱う側(第4章(dump.ml)、第6章(decls.ml)、第10章(exhaust.ml)、第11章(elab.ml)、
   第12章(value.ml)、第14章(interp.ml)、第16章(driver.ml))はこのファイルに依存し、
   このファイルはそのどれにも依存しない。
   tree.ml 自身が依存するのは、木の定義に要る 3 つの材料、
   つまり第1章(syntax.ml)の `Syntax.Make`、`Location.span`、`Aux` の `new_oid` と `bug` だけである。
   ここで言う葉は、何にも依存しないという意味ではない。
   切りたい循環の相手に依存しない、という意味である。

   2 つ目は、パーサの木と型検査の木を同じ型にするためである。
   `Syntax.Make` は OCaml のアプリカティブファンクタなので、
   `Syntax.Make (ElabData)` を別々の場所で適用しても、結果は同じ型になる。
   第16章(driver.ml)が作る `Parser.Make (Tree.ElabData)` の `exp` と、
   このファイルが作る `Syntax.Make (ElabData)` の `exp` は同じ型である。
   そのため、パーサが返した木をそのまま型検査に渡せる。

   `Syntax.Make` がジェネレーティブなファンクタ(`()` を取る形)だと、適用のたびに別の型ができる。
   その場合は、パーサの木を型検査の木へ写す変換関数を、AST のすべての場合について書く必要がある。 *)
module Tree = Syntax.Make (ElabData)

(* ## 5.4 アクセサ

   どのノードも、タプルの第 1 要素がノードに付くデータ、第 2 要素が構文そのものという形をしている。
   そのため、アクセサはどれも `(d, _)` という 1 つのパターンで書ける。

   `get_ty` は、`ty_field` が `None` のときに `bug` を呼ぶ。
   これは、精緻化されていない木を評価してはならないという不変条件を表している。
   この不変条件が破れるのは、利用者のプログラムがどう書かれていても起きてはならない事態、
   つまり処理系の誤りなので、型エラー(`Type_error`)ではなく `bug`(`Panic`)を投げる。
   第16章(driver.ml)は `Panic` を実行時エラーと同じ終了コード 3 で報告するが、
   `bug` がメッセージの先頭に `[BUG]` を付けるので、利用者のプログラムの誤りではないことが分かる。

   この不変条件が守られるのは、第11章の `elab_exp` が、
   どの式についても 1 か所で `set_ty` を通るように書かれているからである。
   式の種類ごとに `set_ty` を書く形では、書き忘れた分岐だけが実行時に落ちる。
   しかも落ちる場所は、型検査から遠く離れた評価器の中になる。 *)
let data (d, _) = d

let loc_of (d, _) = d.ElabData.loc

let oid_of (d, _) = d.ElabData.oid

let get_ty (d, _) = match d.ElabData.ty_field with Some t -> t | None -> bug "get_ty: node not elaborated"

let set_ty (d, _) t = d.ElabData.ty_field <- Some t

let get_resolved (d, _) = d.ElabData.resolved

let set_resolved (d, _) r = d.ElabData.resolved <- Some r

let get_dict (d, _) = d.ElabData.dict

let set_dict (d, _) x = d.ElabData.dict <- x
