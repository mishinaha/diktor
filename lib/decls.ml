(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第6章 宣言環境

   型検査の仕事は 2 つに分かれる。
   1 つは型と型を突き合わせる仕事で、第8章(unify.ml)が受け持つ。
   もう 1 つは名前が何を指すかを決める仕事である。
   型構成子、型エイリアス、コンストラクタ、エフェクト、操作、型クラスの名前については、
   本章の宣言表がその答えを持つ。
   変数と、スコープにある型パラメータの型は、第11章(elab.ml)の環境が持つ。

   宣言表は、たとえば次のような問い合わせに答える。

   - `List[A]` の `List` がどのカインドの型構成子か
   - `IoError` がエイリアスとエフェクト名のどちらか
   - `Some` がどのデータ型のコンストラクタで、そのフィールドがどう並ぶか
   - `write` がどのエフェクトの操作か
   - `Add` がどんなメソッドを持ち、`Int32` がそのインスタンスかどうか

   主な表は次の 8 つである。

   | 表 | キー | 値 | 主な読み手 |
   |---|---|---|---|
   | `con_kinds` | 型構成子 | カインド | 第8章(`kind_of`) |
   | `con_synonyms` | 非修飾名 | 正準の修飾名 | 第11章、第14章 |
   | `aliases` | エイリアス名 | パラメータと本体 | 第11章(透過的な展開) |
   | `datas` / `ctor_owner` | 型名 / コンストラクタ名 | コンストラクタとフィールド | 第10章、第11章 |
   | `effects` / `op_index` | エフェクト名 / 操作名 | スキーマ / 候補列 | 第11章 |
   | `classes` | クラス名 | パラメータとメソッド | 第8章、第11章、第14章 |
   | `instances` | (クラス, 型構成子) | 前提とメソッド本体 | 第8章、第11章、第14章 |
   | `externs` | extern 名 | 登録済みの印 | 第11章 |

   第14章(interp.ml)が読む表と読まない表があるのは、
   第5章(tree.ml)で述べたとおり、評価器が名前解決をやり直さないからである。
   データ型とコンストラクタは精緻化のときに `RCtor` / `RCtorPat` へ書き込んであるので、
   評価器は `datas` / `ctor_owner` を引かない。
   一方、型クラスのインスタンスは実行時に値のタグを見て選ぶので、
   `classes` と `instances` は評価器も読む。

   上に挙げた表は、どれも大域の可変ハッシュ表である。
   そのため、インスタンスの探索もカインドの取得も表を 1 回引くだけで終わる。
   その代わり、処理系の状態が大域にあるので `reset` が要り、2 つのプログラムを同時には検査できない。
   同じプロセスで複数のプログラムを検査する API(第16章の `type_check_string` / `eval_string`)では、
   `reset` がすべての表を戻すので、前の呼び出しの宣言が次の呼び出しに残らない(§6.13)。

   ## プレリュード所有名の再宣言

   宣言表の規則は、素朴に考えれば、同じ名前を二度宣言したら拒否するだけで済む。
   しかし Keleut ではこの規則が成り立たない。
   仕様書である sample.kel 自身が、標準ライブラリの中身を示すために、
   プレリュードと組み込みにある名前を宣言しているからである。
   たとえば `Unit` / `List` / `Console` / `Add` / `Add[Int32]` / `Never` がそうである。

   そこで本章は、**照合の上で受理する**という規則を採る。
   プレリュードや組み込みが先に置いた名前を利用者がもう一度宣言したら、
   宣言そのものは検査して受理するが、表の実体としては採用せず、先に置いた実体を残す。
   利用者の宣言どうしの重複は拒否する。
   クラスとインスタンスでこの規則が効くのは、組み込み(§6.12)が先に置いたものだけである(§6.1)。
   実体を差し替えないという規則は、第14章(interp.ml)の側でも守る必要がある(§6.9)。

   ## 前章から受け取るもの

   第5章(tree.ml)の `Tree.Tree`(型式を表に格納するため)と、
   第1章(syntax.ml)の内部型 `Type.ty` を使う。

   ## 次章へ渡すもの

   第8章(unify.ml)以降の章が、名前の問い合わせ先として本章の表を引く。
   間にある第7章(prims.ml)は本章を参照せず、第1章(syntax.ml)の `bin_op` だけを使う。
   本章が登録したクラスにも、第7章はクラス名の文字列でしか触れない。 *)
open Aux
open Syntax
module T = Tree.Tree

(* ## 6.1 プレリュード所有の記録

   照合の上で受理するには、表の各項目がプレリュード由来か利用者由来かを区別できなければならない。
   その区別を持つのが `prelude_keys` である。

   第11章(elab.ml)はプレリュードを処理する間だけ `in_prelude` を立て、
   組み込みの登録(§6.12)も同じフラグを立てて走る。
   `mark` は、フラグが立っている間に登録された `(表の種別, 名前)` の組だけを `prelude_keys` に記録する。
   あとから同じ名前が来たとき、`prelude_owned` がこの記録を引いて分岐を決める。

   鍵に表の種別を含めるのは、`extern` の `foo` と型エイリアスの `foo` が別物だからである。
   名前だけを鍵にすると、片方の登録がもう片方の再宣言を黙って許してしまう。

   照合の上で受理するかどうかを決める印は、ここの鍵の集合のほかにもう 1 つある。
   クラスとインスタンスのレコードの中のフラグ `ci_builtin` / `ii_builtin`(§6.8、§6.9)である。
   クラスとインスタンスでは、項目が組み込みのものかどうかを、ほかの章も知る必要がある。
   クラスでは、`add_class_decl` が組み込みの項目を `` `Builtin prev `` として呼び出し側に返し、
   第11章はその項目のメソッドを使う(§6.8)。
   第14章(interp.ml)は、インスタンス宣言を評価する前に `ci_builtin` と `builtin_instance_exists` を引き、
   組み込みの実体を差し替えない(§6.9)。
   そのため、クラスとインスタンスの項目は、値の中にフラグを持つ。

   このフラグが表すのは、本章の `register_builtins`(§6.12)が登録したことで、
   プレリュードが宣言したことではない。
   第11章は、プレリュードが宣言したクラスとインスタンスも、フラグを偽にして登録する。
   したがって、プレリュードが宣言したクラスやインスタンスと同じ名前やキーを利用者が宣言すると、
   照合の上で受理するのではなく、重複として拒否する。
   たとえば、プレリュードの `Show[List[_]]` を宣言し直すと、コヒーレンス違反になる。 *)
let in_prelude = ref false

let prelude_keys : (string * oid, unit) Hashtbl.t = Hashtbl.create 64

let mark kind name = if !in_prelude then Hashtbl.replace prelude_keys (kind, name) ()

let prelude_owned kind name = Hashtbl.mem prelude_keys (kind, name)

(* 型名の名前空間は 1 つで、newtype も型エイリアスも effect もこの名前空間を共有する。
   一方、二重宣言の検査は種別ごとの表に分かれているので、
   それだけでは種別を替えた再宣言がすべての検査をすり抜ける。
   たとえば `type List[A] = Int32` は aliases 表では初出なので素通りし、
   以後の `List[X]` がすべて Int32 を意味することになる。
   そうなると、プレリュードの List は、値は作れるのに型名を書けない型になってしまう。
   §6.1 では、名前だけを鍵にすると片方の登録がもう片方の再宣言を黙って許すと述べた。
   名前空間を共有する型名では、逆に種別ごとに表を分けたことが同じ問題を起こす。
   そこで先に置いた種別をこの表に記録し、別の種別での再宣言を登録の時点で拒否する *)
let type_namespace : (oid, string) Hashtbl.t = Hashtbl.create 64

let claim_type_name kind name =
  match Hashtbl.find_opt type_namespace name with
  | Some prev_kind when prev_kind <> kind ->
      type_error (Type.name_of name ^ " は既に " ^ prev_kind ^ " として宣言されています(" ^ kind ^ " では再宣言できません)")
  | _ -> Hashtbl.replace type_namespace name kind

(* プレリュード所有名の照合の上での受理は、1 つのプログラムにつき 1 回までである。
   2 つ目からは利用者の宣言どうしの重複なので拒否する。
   この表が無いと、プレリュード所有名だけは、何度宣言しても「二重に宣言されています」が出なくなる。
   インスタンス側の builtin_redecls(§6.9)と同じ理屈である *)
let user_type_redecls : (string * oid, unit) Hashtbl.t = Hashtbl.create 16

let note_user_redecl kind name what =
  if not !in_prelude then
    if Hashtbl.mem user_type_redecls (kind, name) then
      type_error (what ^ " " ^ Type.name_of name ^ " が二重に宣言されています")
    else Hashtbl.add user_type_redecls (kind, name) ()

(* ## 6.2 extern 登録簿

   `extern` はプリミティブに型を与える宣言である。
   実装は第13章(builtin.ml)の表にあり、型はプレリュードの `extern` 宣言が与える。
   つまり `extern` の型注釈は、処理系が正しさを確かめられない約束である。

   そのため、プリミティブの再宣言を許すと型システムが壊れる。
   許した場合、たとえば `__int32_add` の引数型を String と偽る宣言が型検査を通る。
   ところが第13章の実装は Int32 を前提にしているので、
   実行時には Int32 用の実装に String の値が渡る。
   プリミティブの型注釈は型システム全体が信頼する起点なので、上書きを許すわけにはいかない。

   extern の登録簿は、登録済みの名前の再宣言を拒否する。
   プレリュード所有の名前なら「再宣言できません」、
   利用者由来の名前なら「二重に宣言されています」で拒否する。
   プレリュード所有の newtype、型エイリアス、effect や、
   組み込みのクラスとインスタンスは照合の上で受理するが、
   `extern` は照合せずに拒否する。
   `extern` には照合すべき実体が処理系の側に無いからである。
   名前が同じでも、同じ約束だとは言えない。

   登録簿が守るのは、プレリュードが宣言した名前だけである。
   実装表にあるのに宣言の無い名前は登録簿に載らないので、嘘の型で宣言して実装に到達できてしまう。
   この死角を無くすために、プレリュードは実装表のすべての名前に型を与える(第15章 §15.5 の不変条件)。

   ただし `--no-prelude` のときは登録簿が空になり、すべてのプリミティブを再宣言できる。
   宣言の欠けたプレリュードを `--prelude` で与えたときは、
   そのプレリュードが宣言しなかった名前を再宣言できる。
   どちらの場合も、型と実装の約束は、フラグを指定した利用者(処理系の開発者)が引き受ける。

   登録簿は 2 種類の鍵を使い分ける。
   プレリュードの保護は、非修飾の実装名(第1章の `ex_prim`)で見る。
   module 内の `extern` は Keleut 側の名前が `M.f` に修飾されるので、
   修飾名で見ると、module の中からプレリュードの保護をすり抜けられる。
   二重宣言の検査は、修飾名で見る。
   実装名まで大域で一意にすると、`module Fast` と `module Precise` が同じ C シンボル `sqrt` を
   それぞれの名前で束縛する正当な形が書けなくなる。 *)
let externs : (oid, unit) Hashtbl.t = Hashtbl.create 64

let add_extern ~prim name =
  let o = Type.intern name in
  let po = Type.intern prim in
  (* プレリュードの保護は実装名(非修飾の prim)で、二重宣言は Keleut 側の名前(修飾名)で見る。
     鍵を使い分ける理由は §6.2 で述べた *)
  if prelude_owned "extern" po then type_error ("プレリュードの extern " ^ prim ^ " は再宣言できません")
  else if Hashtbl.mem externs o then type_error ("extern " ^ name ^ " が二重に宣言されています")
  else (
    Hashtbl.add externs o ();
    mark "extern" po)

(* ## 6.2b extern C 既知名の型契約

   §6.2 では、extern には照合すべき実体が処理系の側に無いと述べた。
   C リンケージの既知名(sin / cos / sqrt / exp / log)だけは例外である。
   これらの実装は第13章の `c_prims` 表として処理系が持っているので、照合すべき実体がある。
   そこで第11章は、C 既知名を束縛する extern 宣言の型を、
   本章の署名 `c_known_signatures` と照合する。

   照合しないと、C 既知名 `sin` が String を取って String を返すと偽った宣言が型検査を通る。
   その関数を呼ぶと、「Float64 ではありません」という、利用者には原因の見えない実行時エラーになる。
   §6.2 のプレリュードの保護では、この宣言を防げない。
   保護が効くのはプレリュードが宣言した名前だけで、sin はプレリュードで宣言できないからである。
   sample.kel:791 が sin を自前で宣言するので、プレリュードが先に宣言すると、
   sample.kel の検査が再宣言の拒否で落ちる。

   署名との照合で見るのは引数型と返り値型だけで、行は見ない。
   仕様(sample.kel:794)が、`@ Blocking` を付けるかどうかをバインディングの作者の判断に委ねているからである。

   署名は本章、実装は第13章と、2 つの表に分かれる。
   署名を本章に置くのは、第11章(elab.ml)から第13章を参照すると章の順序が逆転するからである。
   2 つの表は、同じ名前の集合(sin / cos / sqrt / exp / log)を持つように保つ。
   実装だけ足して署名を忘れると、その名前は表に無い名前と同じく照合されずに受理され、
   型を偽った宣言でも実装に届く。
   署名だけ足して実装を忘れると、宣言は通り、呼ぶと「未実装のプリミティブ」になる。 *)

let c_known_signatures : (string * (oid list * oid * string)) list =
  let f64 = Type.intern "Float64" in
  let f1 = ([ f64 ], f64, "(Float64) => Float64") in
  [ ("sin", f1); ("cos", f1); ("sqrt", f1); ("exp", f1); ("log", f1) ]

let c_known_signature name = List.assoc_opt name c_known_signatures

(* ## 6.3 型構成子のカインド表

   第8章(unify.ml)の `kind_of` は、型構成子に出会うとこの表を引き、
   適用された引数の数だけ矢印を落とす。
   Diktor はカインド検査のための専用の走査パスを持たない。
   カインドは、この表と、精緻化の側で行う型引数の照合で決まる(§8.1)。

   `con_kind` は、未知の構成子のカインドを `k_arrow nargs`(適用した個数ぶんの `*` を取る形)とみなす。
   前方参照のときや、パス 1 の途中で表を引いたときに、
   カインドの不一致という誤ったエラーを出さないための、保守的な既定である。

   この表は、引数の数だけ矢印を落とすための表であると同時に、パラメータのカインドを運ぶ表でもある。
   newtype の頭には、第11章のパス 1a がパラメータごとのカインド変数を積む。
   パス 1b の `register_newtype` は、頭のカインドの矢印を剥がし、
   定義域のセルを `dd_params` の `vkind` に置く。
   セルを共有しているので、本体での使われ方で決まったカインドは頭にも現れる。 *)

let con_kinds : (oid, Type.kind) Hashtbl.t = Hashtbl.create 64

(* 未知の構成子は、適用した個数ぶんの引数を取る形とみなす *)
let con_kind c nargs = match Hashtbl.find_opt con_kinds c with Some k -> k | None -> Type.k_arrow nargs

(* 組み込みスカラー型の名前(Boolean / Int32 などは con_kinds にはあるが datas には無い)。
   newtype、エイリアス、effect の再宣言検査がどれも引くので、ここに置く *)
let reserved_type_names : (oid, unit) Hashtbl.t = Hashtbl.create 8

(* ## 6.4 module の平坦化のための同義語表と可視性台帳

   Diktor は Keleut の `module` を平坦化として実装する。
   第11章(elab.ml)の `flatten_modules` が `module M` の中身を取り出し、
   型と let を `M.名前` へ改名してトップレベルに並べ直す。
   改名しただけでは、module の中からの非修飾の参照が壊れる。
   たとえば module 内の `let parse(...): BigInt` の `BigInt` は、
   改名された `newtype BigInt` を指せなくなる。
   そこで同義語表を張り、型の名前は `resolve_con` を通して引く。

   module の内部の名前は module の中でだけ意味を持つので、同義語も module ごとのスコープを持つ。
   `module_con_synonyms` の鍵は `(module 名, 非修飾名)` で、
   いま処理している宣言の module(`current_module`)がその module のときだけ引ける。
   同義語を大域の 1 つの表に置くと、`module M { newtype List[A] = … }` と書くだけで、
   プレリュードの中の `List` までこの module の型を指してしまう。
   その結果、プレリュード自身の型検査が壊れ、
   利用者に落ち度の無い「未知の型」が `<prelude>` の位置で出る。

   スコープの規則は、型と値で非対称である。

   - **型は module 内を先に引く**：module の中では `(M, 名前)` を先に引き、
     無ければ大域を引く(語彙的な遮蔽)。
     型の解決は表が出そろってから始まるので、宣言の順序に依存しない。
     評価器が実行時にインスタンスの頭を解決するときも、同じ規則で引ける。
   - **値は大域を先に引き、衝突を禁止する**：値の解決では、elab は宣言の時点の環境を見て、
     評価器は呼び出しの時点の globals を見る。
     2 つの解決器が別の時点の環境を見るので、module 内の名前とトップレベルの名前が同じだと、
     解決が食い違うことがある。
     そうなると型検査と実行が別の実体を選び、黙って別の値が返る。
     そこで平坦化は、module 内の値の名前が利用者のトップレベルの値の名前と同じになること自体を拒否する。
     同名を禁止すれば、環境に無かったときだけ module スコープの同義語を引くというフォールバックの結果が、
     2 つの解決器で一致する。

   **コンパニオン型**：module と同名の型で、module 名だけで参照できる(sample.kel:838)。
   コンパニオン型の同義語だけは、大域の `con_synonyms` に張る。
   `module BigInt` の中の `newtype BigInt` は `BigInt.BigInt` へ改名され、
   大域の同義語 `BigInt` → `BigInt.BigInt` が張られる。
   module の外から非修飾で見えてよい型名は、コンパニオンだけである。
   ただし、コンパニオンは既存の型名とは衝突できない。
   黙って同義語を張ると、`module Foo` を 1 行足すだけでトップレベルやプレリュードの型 `Foo` が乗っ取られ、
   名目型の抽象が破れる。
   プレリュードの名前が乗っ取られると、処理系そのものが正しく動かなくなる。
   トップレベルの名前との衝突は、平坦化が拒否する。
   プレリュードの名前との衝突の拒否と、大域の同義語の登録は、第11章のパス 1a が行う。
   平坦化の時点では、プレリュードの宣言表がまだ空だからである。

   値を大域から先に引く規則では、プレリュードの名前も大域の側に入る。
   そのため、module 内で `__string_concat` と同名の let を宣言しても、
   module 内からの非修飾の参照はプレリュードの `__string_concat` を指す(elab と評価器で一致する)。
   module 内の自分の束縛を参照するには、`M.名前` と修飾する。

   `con_hints` / `val_synonyms` は診断専用の候補列である。
   名前の解決には使わず、スコープの外からの非修飾の参照に「A.T か B.T と修飾してください」と
   案内するためだけに引く。
   黙って後勝ちする名前解決は、§6.7 の `op_index` と同じ理由で採らない。

   可視性は、同義語表とは別の台帳に載せる。
   `value_visibility` / `con_visibility` は、修飾名から、出身の module と pub の有無を引く表である。
   可視性の検査は module の境界でだけ行う。
   Diktor は複数のファイルを 1 つのプログラムに連結するので、ファイルの境界は見ない。
   コンストラクタの可視性は、所属する newtype の pub に従う。

   同義語表を引くのは第11章だけではない。
   第14章(interp.ml)も、`type instance Add[BigInt]` の頭を解決するときに同じ表を通る。
   名前を oid に落とす経路が 2 つあるので、両方が同じ表を通らないと、
   型検査と実行で名前の指す実体が食い違う。
   評価器の側で `current_module` にあたるのは、
   環境の `mod_scope`(閉包が出身の module を覚える)である。 *)
let current_module : string option ref = ref None

(* コンパニオン型だけを載せる大域の同義語。値は候補の列で、
   resolve_con は候補が 1 つのときだけ使う *)
let con_synonyms : (oid, oid list) Hashtbl.t = Hashtbl.create 16

let add_con_synonym short qual =
  let prev = Option.value ~default:[] (Hashtbl.find_opt con_synonyms short) in
  if not (List.mem qual prev) then Hashtbl.replace con_synonyms short (prev @ [ qual ])

(* module スコープの同義語。(module 名, 非修飾名) → 修飾名 *)
let module_con_synonyms : (string * oid, oid) Hashtbl.t = Hashtbl.create 16

let module_val_synonyms : (string * oid, oid) Hashtbl.t = Hashtbl.create 16

let resolve_con c =
  let global c = match Hashtbl.find_opt con_synonyms c with Some [ c' ] -> c' | _ -> c in
  match !current_module with
  | Some m -> ( match Hashtbl.find_opt module_con_synonyms (m, c) with Some q -> q | None -> global c)
  | None -> global c

(* 診断専用の候補列。解決には使わない *)
let con_hints : (oid, oid list) Hashtbl.t = Hashtbl.create 16

let add_con_hint short qual =
  let prev = Option.value ~default:[] (Hashtbl.find_opt con_hints short) in
  if not (List.mem qual prev) then Hashtbl.replace con_hints short (prev @ [ qual ])

let con_synonym_candidates c = Option.value ~default:[] (Hashtbl.find_opt con_hints c)

let val_synonyms : (oid, oid list) Hashtbl.t = Hashtbl.create 16

let add_val_synonym short qual =
  let prev = Option.value ~default:[] (Hashtbl.find_opt val_synonyms short) in
  if not (List.mem qual prev) then Hashtbl.replace val_synonyms short (prev @ [ qual ])

let val_synonym_candidates short = Option.value ~default:[] (Hashtbl.find_opt val_synonyms short)

(* 可視性台帳。鍵は修飾名 *)
type visibility = { vis_module : string; vis_pub : bool }

let value_visibility : (oid, visibility) Hashtbl.t = Hashtbl.create 16

let con_visibility : (oid, visibility) Hashtbl.t = Hashtbl.create 16

(* 宣言ノードの oid(Tree.oid_of で取り出す)→ 出身 module。
   第11章の 4 つのパスと第14章の exec_decl が、この表から current_module / mod_scope を復元する *)
let decl_module : (oid, string) Hashtbl.t = Hashtbl.create 16

let visible_here (v : visibility) = v.vis_pub || !current_module = Some v.vis_module

let check_con_visible oid =
  match Hashtbl.find_opt con_visibility oid with
  | Some v when not (visible_here v) ->
      type_error ("型 " ^ Type.name_of oid ^ " は module " ^ v.vis_module ^ " の外からは参照できません(pub を付けてください)")
  | _ -> ()

let check_value_visible oid =
  match Hashtbl.find_opt value_visibility oid with
  | Some v when not (visible_here v) ->
      type_error (Type.name_of oid ^ " は module " ^ v.vis_module ^ " の外からは参照できません(pub を付けてください)")
  | _ -> ()

let check_ctor_visible ctor owner =
  match Hashtbl.find_opt con_visibility owner with
  | Some v when not (visible_here v) ->
      type_error
        ("コンストラクタ " ^ Type.name_of ctor ^ " は module " ^ v.vis_module ^ " の外からは参照できません(newtype "
       ^ Type.name_of owner ^ " に pub を付けてください)")
  | _ -> ()

(* ## 6.5 型エイリアス

   エイリアスは透過である。
   表には精緻化済みの型ではなく型式(`al_body`)をそのまま置き、
   使われるたびに第11章がその場で精緻化する。
   型式を置く理由は 2 つある。
   1 つは、展開のたびに新しい型変数を作れることである。
   もう 1 つは、`al_kind`(`: Type` か `: EffectRow` か)によって、
   同じ型式を型としてもエフェクト行としても展開できることである。
   型式を置くので、第11章はエイリアスを使うたびに、
   パラメータの制約(`type P[A: Show]`)も課す(§11.5)。

   透過でも、パラメータのカインドだけは表に残す(`al_kinds`)。
   引数を読むのは使用点で、そこでは行として読むか型として読むかを、
   パラメータのカインドで決めるしかない。
   本体を見てから引数を読み直すことはできないからである。
   カインドは、第11章のパス 1b の後始末が本体を一度投機的に精緻化して推論し、
   決まらなければ `Type` に既定化する。
   `al_kinds` は、newtype の `dd_params` が持つ `vkind` と同じ役目を、エイリアスについて果たす。

   エイリアスには 2 つの制限がある。
   再帰しないことと、部分適用できないことである。
   部分適用できるエイリアスは実質的に型レベルの λ である。
   これを許すと単一化の結果が一意に決まらなくなり(mgu が一意でない)、主要型が失われる。 *)

(* ## 6.4b 構造照合

   本節の関数は、照合の上で受理するときの照合を実装する。
   名前の一致だけで受理すると、プレリュード所有名の再宣言は、宣言ごと黙って捨てられる。
   コンストラクタの集合が違う newtype も、本体の違う型エイリアスも、操作の型が違う effect も、
   終了コード 0 で警告も無く受理され、以後はプレリュード側の定義だけが使われる。
   標準ライブラリの中身を示すための宣言が本物と食い違っていても、誰も気づけない。

   照合するのは、Keleut のプログラムから観測できるものだけである。

   - **newtype**：コンストラクタ名の集合、各コンストラクタのフィールドの数とラベルと型(α 同値)、
     型パラメータの個数とカインドと制約、`???`(不透明)かどうか。
     コンストラクタの宣言の順序は照合しない。
     Keleut にはコンストラクタの序数が無く、順序を観測できないからである。
   - **型エイリアス**：種別(`: Type` / `: EffectRow`)、パラメータ、本体の型式。
     パラメータ名は位置で読み替えるので、`[A] = (A, A)` と `[B] = (B, B)` は同じ宣言である。
   - **effect**：操作名の集合と、各操作のスキーマ(α 同値)。
   - **type class**：パラメータのカインド、`derive structural` の有無、
     メソッド名の集合の完全な一致、各メソッドの型(α 同値)。
     メソッドの部分集合は認めない。
     newtype や effect と同じく、宣言を部分的な記述ではなく完全な記述として読む。
   - **インスタンス**：組み込み(§6.12)が登録したインスタンスと同じキーなら、
     キーの一致だけを見る(本体は第11章が独立に検査する)。
     プレリュードが宣言したインスタンス(`Show[List[_]]` など)と同じキーの宣言は、
     照合せずにコヒーレンス違反として拒否する(§6.1)。
   - **extern**：照合せずに拒否する(§6.2。照合すべき実体が処理系の側に無い)。

   型は α 同値で比べる。
   Generic 変数は双方向の全単射で対応づけ、行はラベルごとに列を分けて突き合わせる。
   同じラベルの中の順序は保ち、異なるラベルの間の順序は無視する(Scoped Labels の規則)。
   カインドは、副作用の無い `kind_equiv` で比べる。
   `same_kind` は KVar を破壊的に張るので、照合に使うと宣言の順序で結果が変わってしまう。 *)

let rec kind_equiv a b =
  match (Type.kind_repr a, Type.kind_repr b) with
  | Type.KStar, Type.KStar | Type.KRow, Type.KRow -> true
  | Type.KArrow (a1, a2), Type.KArrow (b1, b2) -> kind_equiv a1 b1 && kind_equiv a2 b2
  | Type.KVar _, Type.KVar _ -> true (* 未確定どうしは等しいとみなす(張らない) *)
  | _ -> false

(* α 同値の判定。
   m / rev は Generic / Unbound 変数の vid の双方向の対応で、宣言ごとに共有する
   (同じパラメータは全フィールドで同じ相手に写る) *)
let ty_equiv_with (m : (oid, oid) Hashtbl.t) (rev : (oid, oid) Hashtbl.t) a b =
  let var_pair (ia : Type.var_info) (ib : Type.var_info) =
    match (Hashtbl.find_opt m ia.Type.vid, Hashtbl.find_opt rev ib.Type.vid) with
    | Some x, Some y -> x = ib.Type.vid && y = ia.Type.vid
    | None, None ->
        Hashtbl.replace m ia.Type.vid ib.Type.vid;
        Hashtbl.replace rev ib.Type.vid ia.Type.vid;
        true
    | _ -> false
  in
  let rec go a b =
    match (Type.repr a, Type.repr b) with
    | Type.TCon (ca, aa), Type.TCon (cb, ab) -> ca = cb && List.length aa = List.length ab && List.for_all2 go aa ab
    | Type.TApp (fa, xa), Type.TApp (fb, xb) -> go fa fb && go xa xb
    | Type.TArrow (pa, ra, ea), Type.TArrow (pb, rb, eb) -> go pa pb && go ra rb && go ea eb
    | Type.TRecord ra, Type.TRecord rb | Type.TVariant ra, Type.TVariant rb -> row_equiv ra rb
    (* 空行どうしはここで打ち切る。row_equiv に回すと、尾部の比較が
       また空行どうしになって無限に再帰する *)
    | Type.TRowEmpty, Type.TRowEmpty -> true
    | Type.TRowExtend _, (Type.TRowEmpty | Type.TRowExtend _) | Type.TRowEmpty, Type.TRowExtend _ -> row_equiv a b
    | Type.TVar ra, Type.TVar rb -> (
        match (!ra, !rb) with
        | Type.Generic ia, Type.Generic ib | Type.Unbound ia, Type.Unbound ib ->
            var_pair ia ib
            && kind_equiv ia.Type.vkind ib.Type.vkind
            && List.sort compare ia.Type.vcls = List.sort compare ib.Type.vcls
        | _ -> false)
    | _ -> false
  and row_equiv ra rb =
    let fa, ta = Type.row_fields ra in
    let fb, tb = Type.row_fields rb in
    let group fs =
      List.fold_left
        (fun acc (l, t) ->
          let prev = Option.value ~default:[] (List.assoc_opt l acc) in
          (l, prev @ [ t ]) :: List.remove_assoc l acc)
        [] fs
    in
    let ga = group fa and gb = group fb in
    List.length ga = List.length gb
    && List.for_all
         (fun (l, ts) ->
           match List.assoc_opt l gb with
           | Some ts' -> List.length ts = List.length ts' && List.for_all2 go ts ts'
           | None -> false)
         ga
    && go ta tb
  in
  go a b

let ty_equiv a b = ty_equiv_with (Hashtbl.create 8) (Hashtbl.create 8) a b

(* パラメータを位置で対応づけ、全単射の最初の対応にする。
   パラメータの個数とカインドと制約も、ここで照合する *)
let params_match (prev_ps : Type.var_info list) (info_ps : Type.var_info list) m rev =
  List.length prev_ps = List.length info_ps
  && List.for_all2
       (fun (pa : Type.var_info) (pb : Type.var_info) ->
         Hashtbl.replace m pa.Type.vid pb.Type.vid;
         Hashtbl.replace rev pb.Type.vid pa.Type.vid;
         kind_equiv pa.Type.vkind pb.Type.vkind && List.sort compare pa.Type.vcls = List.sort compare pb.Type.vcls)
       prev_ps info_ps

(* 型式(ソース上の型)の比較。
   エイリアスの本体は精緻化済みの型を持たないので、span を無視して構文を再帰的にたどる。
   パラメータ名は、位置で対応づけた表で読み替える。

   読み替えは全単射でなければならない(ty_equiv_with の m / rev と同じ)。
   片方向の対応だけだと、宣言側のパラメータ名が相手側の自由な型名を捕獲する。
   たとえば、プレリュードの `type Cap[A] = (A, G)` と利用者の `type Cap[G] = (G, G)` を同じ宣言と誤って判定する。
   しかも表の実体はプレリュード側のままなので、利用者は自分の宣言が捨てられたことを知らされない。
   `na` が読み替えの表に無いときは、`nb` がどの読み替えの像でもないことを確かめてから、
   素の名前の比較に進む。

   行とヴァリアントと制約は、順序を見ない(ty_equiv_with がラベルで揃えるのと同じ規律)。
   構文のまま List.for_all2 で突き合わせると、
   型としては同じ `{x: Int32, y: String}` と `{y: String, x: Int32}` を、
   「本体が違います」で誤って拒否する。
   そこで、ラベルで安定ソートしてから比べる。
   同名のラベルが重なるときは相対的な順序を保つので、遮蔽の順序は照合に残る *)
let rec type_exp_equiv (ren : (string * string) list) ((_, a) : T.type_exp) ((_, b) : T.type_exp) =
  let ren_of na = match List.assoc_opt na ren with Some x -> x | None -> na in
  let id_equiv (la : long_id) (lb : long_id) =
    match (la, lb) with
    | LongId [ na ], LongId [ nb ] -> (
        match List.assoc_opt na ren with
        | Some nb' -> nb = nb'
        | None -> (not (List.exists (fun (_, y) -> y = nb) ren)) && na = nb)
    | LongId xs, LongId ys -> xs = ys
  in
  (* 行の要素を並べ替えるための鍵。prev 側(第1引数)はラベルを読み替えてから
     比べるので、両側が同じ名前で揃う *)
  let bkey rename = function
    | T.BField (l, _) -> (0, l)
    | T.BLabel (LongId ids, _) -> (1, String.concat "." (List.map rename ids))
  in
  (* ヴァリアントのタグ名は型パラメータではないので読み替えない *)
  let usort xs =
    List.stable_sort
      (fun ((_, x) : T.type_exp) ((_, y) : T.type_exp) ->
        let k = function T.EVariantCase (n, _) -> (0, n) | _ -> (1, "") in
        compare (k x) (k y))
      xs
  in
  match (a, b) with
  | T.EIdent la, T.EIdent lb -> id_equiv la lb
  | T.EApply (fa, xa), T.EApply (fb, xb) ->
      type_exp_equiv ren fa fb && List.length xa = List.length xb && List.for_all2 (type_exp_equiv ren) xa xb
  | T.EArrow (pa, ra, ea), T.EArrow (pb, rb, eb) ->
      List.length pa = List.length pb
      && List.for_all2 (type_exp_equiv ren) pa pb
      && type_exp_equiv ren ra rb
      && (match (ea, eb) with
         | None, None -> true
         | Some x, Some y -> type_exp_equiv ren x y
         | _ -> false)
  | T.EBraceRow (ea, ta), T.EBraceRow (eb, tb) ->
      let sa = List.stable_sort (fun x y -> compare (bkey ren_of x) (bkey ren_of y)) ea in
      let sb = List.stable_sort (fun x y -> compare (bkey Fun.id x) (bkey Fun.id y)) eb in
      List.length sa = List.length sb
      && List.for_all2
           (fun x y ->
             match (x, y) with
             | T.BField (lx, tx), T.BField (ly, ty) -> lx = ly && type_exp_equiv ren tx ty
             | T.BLabel (lx, ax), T.BLabel (ly, ay) ->
                 id_equiv lx ly && List.length ax = List.length ay && List.for_all2 (type_exp_equiv ren) ax ay
             | _ -> false)
           sa sb
      && (match (ta, tb) with
         | None, None -> true
         | Some x, Some y -> type_exp_equiv ren x y
         | _ -> false)
  | T.EVariantCase (na, pa), T.EVariantCase (nb, pb) ->
      na = nb
      && (match (pa, pb) with
         | None, None -> true
         | Some x, Some y -> type_exp_equiv ren x y
         | _ -> false)
  | T.EUnion xs, T.EUnion ys ->
      let xs = usort xs and ys = usort ys in
      List.length xs = List.length ys && List.for_all2 (type_exp_equiv ren) xs ys
  | T.EHole, T.EHole -> true
  | _ -> false

type alias_info = {
  al_name : oid;
  al_params : type_param list;
  al_kinds : Type.kind list; (* パラメータのカインド。パス 1a で作り、パス 1b の後始末で本体から推論する *)
  al_kind : string option; (* : Type / : EffectRow *)
  al_body : T.type_exp;
  (* 本体は宣言のスコープで展開する。module 内のエイリアスが module の内部の型を
     指していても外から展開して壊れないように、展開の間はこの module を
     current_module に立てる。引数は使う側のスコープで読む *)
  al_module : string option;
}

let aliases : (oid, alias_info) Hashtbl.t = Hashtbl.create 64

let add_alias info =
  (* 組み込みスカラーの名前はエイリアスでも奪えない(newtype 側と同じ検査)。
     C 既知名の署名との照合は型名で比べるので、type Float64 = String が通ると、
     照合は Float64 と書いた宣言に、Float64 でなければならないという自己矛盾した診断を出す *)
  if Hashtbl.mem reserved_type_names info.al_name && not !in_prelude then
    type_error ("組み込み型 " ^ Type.name_of info.al_name ^ " は型エイリアスで再宣言できません")
  else claim_type_name "型エイリアス" info.al_name;
  if Hashtbl.mem aliases info.al_name then
    if not (prelude_owned "alias" info.al_name) then
      type_error ("型エイリアス " ^ Type.name_of info.al_name ^ " が二重に宣言されています")
    else (
      note_user_redecl "alias" info.al_name "型エイリアス";
      (* 照合の上で受理する。表の実体は差し替えない *)
      let prev = Hashtbl.find aliases info.al_name in
      let name = Type.name_of info.al_name in
      let fail why = type_error ("型エイリアス " ^ name ^ " の宣言がプレリュードの宣言と一致しません(" ^ why ^ ")") in
      if prev.al_kind <> info.al_kind then fail ": Type と : EffectRow が違います";
      if List.length prev.al_params <> List.length info.al_params then
        fail
          (Printf.sprintf "型パラメータの個数が違います: プレリュードは %d、宣言は %d" (List.length prev.al_params)
             (List.length info.al_params));
      if
        not
          (List.for_all2
             (fun (pa : type_param) (pb : type_param) ->
               (* 制約の並び順は照合しない(params_match が vcls をソート
                  するのと同じ規律) *)
               pa.tp_arity = pb.tp_arity && List.sort compare pa.tp_classes = List.sort compare pb.tp_classes)
             prev.al_params info.al_params)
      then fail "型パラメータが違います";
      let ren = List.map2 (fun (pa : type_param) (pb : type_param) -> (pa.tp_name, pb.tp_name)) prev.al_params info.al_params in
      if not (type_exp_equiv ren prev.al_body info.al_body) then fail "本体が違います")
  else (
    Hashtbl.add aliases info.al_name info;
    mark "alias" info.al_name)

(* ## 6.6 データ宣言表と予約型名

   名目的なデータ型の表である。
   データ型を足しても、型の表現は変わらない。
   データ型は `TCon` 1 つで表し、データ型ごとの情報はこの表だけが持つ。

   フィールドの型に現れるパラメータは、Generic の印を付けた変数で置いてある。
   使うときは、`dd_params` の各 `vid` に新しい変数を割り当てて `subst_params` する。
   インスタンス化と同じ機構である。

   この表には、注意すべき点が 3 つある。

   ### コンストラクタ名は大域で一意

   `ctor_owner` はコンストラクタ名からデータ型名を引く逆引きの表で、登録のときに重複を拒否する。
   コンストラクタ名が大域で一意なので、ラベルなしのコンストラクタ適用や、
   裸のコンストラクタ参照(`None` のような引数の無いコンストラクタ)を、名前だけで解決できる。

   ### `dd_ctors = []` には 2 つの意味がある

   `dd_opaque` が真なら、その型は `newtype X = ???` である。
   未実装のホールと、`Ref` / `Array` のような組み込みの不透明型がこれにあたる。
   偽なら `Never`、つまりコンストラクタが 0 個であることが確定した型である。
   第10章(exhaust.ml)の `complete_sig` は、この型に `Some []` を返す。
   完全性の判定(`sig_complete`)は、パターンの根が 1 つも無くても `Some []` を完全とみなす。
   そのため、`Never` に対する節が 0 個の `match` は網羅していると判定される。
   根が空でないことを完全性の条件に含めると、この `match` を誤って非網羅と判定してしまう。

   ### 予約型名

   `Boolean` / `Int32` / `Int64` / `Float64` / `String` は `con_kinds` には載るが、
   `datas` には載らない。
   組み込みスカラーにはコンストラクタが無いので、データ宣言を作る意味がないからである。

   ただし、`datas` に載っていなくても、その名前が空いているわけではない。
   `datas` だけで二重宣言を検査すると、`newtype Boolean = Yes` が検査を素通りし、
   新しいデータ型として登録される。
   すると網羅性検査と組み込みインスタンスの両方が壊れる。
   第10章は Boolean をコンストラクタ `Yes` だけを持つ型とみなし、
   組み込みの `Eq[Boolean]` は元の真偽値を前提にしたまま残る。

   そこで `reserved_type_names` に組み込みスカラーの名前を載せる。
   ここに載っている名前は、プレリュードの処理中でない限り `newtype` で再宣言できない。

   `Never` は `reserved_type_names` に入れない。
   `Never` は §6.12 でコンストラクタが 0 個のデータ宣言として `datas` に登録されるので、
   sample.kel が `Never` を宣言し直しても、
   プレリュード所有の名前を照合の上で受理する経路にそのまま乗る。 *)

type field_info = { fi_label : oid option; fi_ty : Type.ty (* パラメータは Generic の変数。カインドは Type *) }

type ctor_info = { ct_name : oid; ct_fields : field_info list }

type data_info = {
  dd_name : oid;
  dd_params : Type.var_info list; (* Generic 変数の情報(vid を鍵に subst_params する) *)
  dd_ctors : ctor_info list; (* Never は [] *)
  dd_opaque : bool; (* newtype X = ??? *)
}

let datas : (oid, data_info) Hashtbl.t = Hashtbl.create 64

let ctor_owner : (oid, oid) Hashtbl.t = Hashtbl.create 128 (* コンストラクタ名 → データ型名 *)

(* newtype の構造照合。
   コンストラクタ名の集合、フィールドの数とラベルと型、パラメータ、不透明かどうかを突き合わせる。
   どれも観測できるもので、観測できないコンストラクタの宣言の順序は照合しない *)
let data_match (prev : data_info) (info : data_info) =
  let name = Type.name_of info.dd_name in
  let fail why = type_error ("newtype " ^ name ^ " の宣言がプレリュードの宣言と一致しません(" ^ why ^ ")") in
  if prev.dd_opaque <> info.dd_opaque then fail "片方だけが ??? のホールです";
  if List.length prev.dd_params <> List.length info.dd_params then
    fail
      (Printf.sprintf "型パラメータの個数が違います: プレリュードは %d、宣言は %d" (List.length prev.dd_params)
         (List.length info.dd_params));
  let m = Hashtbl.create 8 and rev = Hashtbl.create 8 in
  if not (params_match prev.dd_params info.dd_params m rev) then fail "型パラメータのカインドか制約が違います";
  let names cs = List.sort compare (List.map (fun (c : ctor_info) -> c.ct_name) cs) in
  if names prev.dd_ctors <> names info.dd_ctors then
    fail
      (match prev.dd_ctors with
      | [] -> "コンストラクタが違います: プレリュードはコンストラクタを持ちません"
      | cs -> "コンストラクタが違います: プレリュードは " ^ String.concat ", " (List.map (fun c -> Type.name_of c.ct_name) cs));
  List.iter
    (fun (pc : ctor_info) ->
      let ic = List.find (fun (c : ctor_info) -> c.ct_name = pc.ct_name) info.dd_ctors in
      let cn = Type.name_of pc.ct_name in
      if List.length pc.ct_fields <> List.length ic.ct_fields then
        fail
          (Printf.sprintf "コンストラクタ %s のフィールド数が違います: プレリュードは %d、宣言は %d" cn (List.length pc.ct_fields)
             (List.length ic.ct_fields));
      List.iteri
        (fun i (pf, inf) ->
          let show_l = function Some l -> Type.name_of l | None -> "ラベルなし" in
          if pf.fi_label <> inf.fi_label then
            fail
              (Printf.sprintf "コンストラクタ %s の第%dフィールドのラベルが違います: プレリュードは %s、宣言は %s" cn (i + 1)
                 (show_l pf.fi_label) (show_l inf.fi_label));
          if not (ty_equiv_with m rev pf.fi_ty inf.fi_ty) then
            fail (Printf.sprintf "コンストラクタ %s の第%dフィールドの型が違います" cn (i + 1)))
        (List.combine pc.ct_fields ic.ct_fields))
    prev.dd_ctors

let add_data info =
  if Hashtbl.mem reserved_type_names info.dd_name && not !in_prelude then
    type_error ("組み込み型 " ^ Type.name_of info.dd_name ^ " は newtype で再宣言できません")
  else claim_type_name "newtype" info.dd_name;
  if Hashtbl.mem datas info.dd_name then (
    if not (prelude_owned "data" info.dd_name) then
      type_error ("newtype " ^ Type.name_of info.dd_name ^ " が二重に宣言されています")
    else (
      note_user_redecl "data" info.dd_name "newtype";
      data_match (Hashtbl.find datas info.dd_name) info))
  else (
    Hashtbl.add datas info.dd_name info;
    mark "data" info.dd_name;
    List.iter
      (fun ct ->
        if Hashtbl.mem ctor_owner ct.ct_name then
          type_error ("コンストラクタ " ^ Type.name_of ct.ct_name ^ " が二重に宣言されています(コンストラクタ名は大域一意)")
        else Hashtbl.add ctor_owner ct.ct_name info.dd_name)
      info.dd_ctors)

(* ## 6.7 エフェクト表と操作の索引

   エフェクト宣言は、非修飾の操作名と操作のスキーマの組の並びである。
   スキーマは Generic 化済みの `TArrow(引数行, 返り値, ρ)` で、
   クラスメソッドと同じ形をしている(§6.10)。

   精緻化木では、操作を完全名、つまり `Console.write` を intern した oid で表す。
   第5章(tree.ml)の `ROp` に入るのがこの完全名である。
   一方、本章の `ef_ops` と `op_index` は、非修飾の操作名を鍵にする。
   非修飾で書かれた `perform write(x)` を完全名に解決するために、`op_index` を使う。

   ### 操作名は大域で一意ではない

   sample.kel 自身が `Console.write`(:464)と `File.write`(:590)の両方を宣言しているので、
   操作名を大域で一意にするという素朴な規則は使えない。
   そこで Diktor は操作名の重複した宣言を許す。
   `op_index` は、非修飾の操作名から、その操作を持つエフェクトを宣言の順に並べた列を引く表である。
   `add_effect` が `prev @ [ ef_name ]` と末尾に足すのは、この列を宣言の順に保つためである。

   ### 選ぶのは表ではなく、その地点のエフェクト行

   候補の先頭を採ると、宣言の順序に依存した誤った解決になる。
   そこで第11章は、候補が複数あるとき、その地点のエフェクト行で最も左に現れる候補を採る。
   明示されたラベルにある候補を優先する規則では足りない。
   sample.kel:616 の `copy` は `File` と `Console` の両方が行に載っている文脈で `write` を呼ぶ(:620)ので、
   この規則では曖昧になる。
   仕様は :530-532 で、`with_file` が積んだ `File` が左にあることと、
   同じエフェクトを二重に積むと操作は内側のハンドラにしか届かないことを定めている。
   最も左を採る規則は、Scoped Labels の最左一致と同じである。
   推論で組み立てた行では、最も左の候補が最も内側のハンドラと一致する。
   注釈で明示した行では、最も左は書かれた順序で決まり、
   入れ子の順序と一致するとは限らない(第11章 §11.20)。
   それでも型検査と実行が食い違わないのは、`perform` が解決済みの完全名の oid を運ぶからである。
   別のエフェクトのハンドラが、同名の操作を横取りすることはない。

   したがって、この表の宣言の順序が最終的な選択を決めることはない。
   宣言の順序が効くのは、行に候補が 1 つも無く、
   修飾を案内するエラーで候補を並べるときだけである。 *)

type effect_info = {
  ef_name : oid;
  ef_ops : (oid * Type.ty) list; (* 非修飾の操作名 → スキーマ TArrow(引数行, 返り値, ρ)(Generic 化済み) *)
}

let effects : (oid, effect_info) Hashtbl.t = Hashtbl.create 32

(* 操作名の重複した宣言を許す(sample.kel 自身が Console.write と File.write を宣言する)。
   非修飾の操作名 → その操作を持つエフェクトの、宣言順の列 *)
let op_index : (oid, oid list) Hashtbl.t = Hashtbl.create 64

let add_effect info =
  (* 組み込みスカラーの名前は effect でも奪えない(add_alias と同じ検査)。型名の
     名前空間も newtype やエイリアスと共有する(effect List は List の再宣言になる。
     §6.1 の後の type_namespace) *)
  if Hashtbl.mem reserved_type_names info.ef_name && not !in_prelude then
    type_error ("組み込み型 " ^ Type.name_of info.ef_name ^ " は effect で再宣言できません")
  else claim_type_name "effect" info.ef_name;
  if Hashtbl.mem effects info.ef_name then (
    if not (prelude_owned "effect" info.ef_name) then
      type_error ("effect " ^ Type.name_of info.ef_name ^ " が二重に宣言されています")
    else (
      note_user_redecl "effect" info.ef_name "effect";
      (* 照合の上で受理する。操作名の集合と、各スキーマの α 同値を見る *)
      let prev = Hashtbl.find effects info.ef_name in
      let name = Type.name_of info.ef_name in
      let fail why = type_error ("effect " ^ name ^ " の宣言がプレリュードの宣言と一致しません(" ^ why ^ ")") in
      let names ops = List.sort compare (List.map fst ops) in
      if names prev.ef_ops <> names info.ef_ops then
        fail
          (match prev.ef_ops with
          | [] -> "操作が違います: プレリュードは操作を持ちません"
          | ops -> "操作が違います: プレリュードは " ^ String.concat ", " (List.map (fun (o, _) -> Type.name_of o) ops));
      List.iter
        (fun (op, pty) ->
          let ity = List.assoc op info.ef_ops in
          if not (ty_equiv pty ity) then fail ("操作 " ^ Type.name_of op ^ " の型が違います"))
        prev.ef_ops))
  else (
    Hashtbl.add effects info.ef_name info;
    mark "effect" info.ef_name;
    List.iter
      (fun (op, _) ->
        let prev = Option.value ~default:[] (Hashtbl.find_opt op_index op) in
        Hashtbl.replace op_index op (prev @ [ info.ef_name ]))
      info.ef_ops)

let find_effect e = Hashtbl.find_opt effects e

let op_candidates op = Option.value ~default:[] (Hashtbl.find_opt op_index op)

(* ## 6.8 クラス表

   Keleut の型クラスはパラメータを 1 つだけ持つ。
   クラス表の項目は、クラス名、パラメータのカインド、メソッドのほかに、次の 3 つのフィールドを持つ。

   - `ci_param`：クラスパラメータの Generic 変数の情報。
     全メソッドが同じ変数を共有する。
     この変数がインスタンス検査の代入点で、頭の型を 1 回代入すれば、
     クラス内の全メソッドの型が同時に具体化される。
   - `ci_derive_structural`：`derive structural`(sample.kel:388)の有無。
     真なら、閉じた行の `TRecord` / `TVariant` について、同じ制約を各フィールドへ再帰的に要求する。
     Diktor で真になるのは `Eq` だけである(利用者は新しいクラスに `derive structural` を書けない)。
     閉じた行にしか適用しないのは仕様の規則である(sample.kel:391-395)。
     行変数を含む型を比較できるようにするにはフィールドごとの行制約 `[R: Eq]` が要り、
     カインドと制約の解決の両方に手を入れることになる。
   - `ci_builtin`：この項目を本章の `register_builtins`(§6.12)が登録したかどうか。
     照合の上で受理するのは、この印が真のクラスと同名の宣言だけである(§6.1)。

   `add_class_decl` は、呼び出し側がどちらのメソッドを使うかを決められるように、3 通りの結果を返す。

   | 結果 | 意味 | 第11章の処理 |
   |---|---|---|
   | `` `Added `` | 新規の宣言 | 宣言したメソッドをそのまま使う |
   | `` `Builtin prev `` | 組み込みと同名で、構造照合に通った | 型は組み込み側を使う |
   | 例外 | 利用者の宣言どうしの重複、または照合の不一致 | 宣言を拒否する |

   照合の中身は §6.4b のとおりである。
   sample.kel の `Add` が組み込みと一致していることは、処理系がこの照合で確かめる。 *)

type class_info = {
  ci_name : oid;
  ci_param : Type.var_info; (* クラスパラメータの Generic 変数(インスタンス検査の代入点) *)
  ci_param_kind : Type.kind;
  ci_derive_structural : bool;
  ci_builtin : bool;
  ci_methods : (string * Type.ty) list; (* メソッド名 → Generic 化済みのスキーマ *)
}

let classes : (oid, class_info) Hashtbl.t = Hashtbl.create 64

let find_class c = Hashtbl.find_opt classes c

(* 組み込みと同名の利用者の宣言は、照合の上で受理する(実体は組み込みのまま)。
   sample.kel 自身が、組み込みにある Add などを宣言するからである *)
let add_class_decl info =
  match Hashtbl.find_opt classes info.ci_name with
  | Some prev when prev.ci_builtin ->
      (* 照合の上で受理する。メソッド名の集合は完全に一致しなければならない。
         クラス宣言の照合は、第11章ではなくここだけで行う *)
      let name = Type.name_of info.ci_name in
      note_user_redecl "class" info.ci_name "type class";
      let fail why = type_error ("type class " ^ name ^ " の宣言が組み込みの宣言と一致しません(" ^ why ^ ")") in
      if not (kind_equiv prev.ci_param_kind info.ci_param_kind) then fail "パラメータのカインドが違います";
      if prev.ci_derive_structural <> info.ci_derive_structural then fail "derive structural の有無が違います";
      let names ms = List.sort compare (List.map fst ms) in
      if names prev.ci_methods <> names info.ci_methods then
        fail ("メソッドが違います: 組み込みは " ^ String.concat ", " (List.map fst prev.ci_methods));
      let m = Hashtbl.create 8 and rev = Hashtbl.create 8 in
      Hashtbl.replace m prev.ci_param.Type.vid info.ci_param.Type.vid;
      Hashtbl.replace rev info.ci_param.Type.vid prev.ci_param.Type.vid;
      List.iter
        (fun (mn, pty) ->
          let ity = List.assoc mn info.ci_methods in
          if not (ty_equiv_with m rev pty ity) then fail ("メソッド " ^ mn ^ " の型が違います"))
        prev.ci_methods;
      `Builtin prev
  | Some _ -> type_error ("type class " ^ Type.name_of info.ci_name ^ " が二重に宣言されています")
  | None ->
      Hashtbl.add classes info.ci_name info;
      `Added

(* ## 6.9 インスタンス表とコヒーレンス

   インスタンス表 `instances` のキーは、(クラス, 型構成子の頭)の oid の組である。
   `Functor[List[_]]` でも、キーになるのは頭の名前 `List` だけで、
   適用する引数の個数はカインドが決める。
   頭に書かれた穴 `_` は、カインドの検査にしか使わない。
   キーが頭の名前だけなので、インスタンスの探索は表を 1 回引くだけで終わる。

   `ii_premises` は、引数の位置と、その位置に要求するクラスの組の列で、
   第8章(unify.ml)の制約の伝播が読む。
   `Show[List[_]]` のインスタンスなら、要素の型 `A` が `Show` であることを、
   `List[A]` が `Show` であるための前提として持つ。
   `add_instance` を呼ぶのは、組み込みの登録(§6.12)と、
   利用者の宣言を登録する第11章の `register_instance`(§11.35)の 2 か所である。
   組み込みの登録は前提を持たない。
   `register_instance` は、`type instance[A: Eq] Eq[List[_]]` の `[A: Eq]` のような束縛子から、
   `(引数位置, クラス)` の組を作って渡す。

   組み込みの登録は、`Show` のインスタンスを `List` と `Option` に置かない。
   これらの `Show` は、プレリュードが前提つきのインスタンスとして宣言する(第15章 §15.8)。
   宣言の頭は `Show[List[_]]` と `Show[Option[_]]` である。
   この前提により、`show` は、要素の型が `Show` である `List` や `Option` にも効く。
   仕様も、標準ライブラリが `List` と `Option` に `Show` のインスタンスを持つと定めている(sample.kel:449-450)。
   `List` の `Eq` は、利用者が宣言する(sample.kel:421 の `type instance[A: Eq] Eq[List[_]]`)。

   コヒーレンスの規則は、sample.kel:357 のとおり、重複したキーを拒否することだけである。
   インスタンスは常に大域で見え、隠すことも選び直すこともできない。

   ### 実体を差し替えないことを、型検査と実行の両方で守る

   `add_instance` の最初の分岐は、組み込みのインスタンスがすでにあり、利用者の宣言が来た場合を扱う。
   この分岐は、インスタンス表に何も書かずに返る。
   利用者の本体は第11章が普通に型検査するが、表に残るのは組み込みのインスタンスである。
   受理するが採用しない、という規則をここで実装している。

   第14章(interp.ml)も同じ規則を守らなければならない。
   `type instance Add[Int32]` を再宣言したときに実行時のディスパッチ表だけが利用者の本体に差し替わると、
   elab は組み込みの `Add[Int32]` で型検査したのに、実行時には別の実装に飛ぶ。
   たとえば利用者の本体が引き算を実装していれば、`2 + 3` が `-1` を返す。
   これはコヒーレンスの破れである。
   第5章で述べた、elab と interp が同じ規則を二重に実装して食い違う問題の例でもある。

   そこで第14章は、インスタンス宣言を評価する前に `builtin_instance_exists` に問い合わせ、
   組み込みのキーなら実体を差し替えない。
   第14章は規則を自分で書き直さず、規則を持っている本章に問い合わせる。 *)

type instance_info = {
  ii_premises : (int * oid) list; (* 引数位置 → 要求クラス *)
  ii_builtin : bool;
  ii_methods : (oid * T.let_binding) list; (* 利用者が宣言したメソッド本体(interp のディスパッチ用) *)
}

let instances : (oid * oid, instance_info) Hashtbl.t = Hashtbl.create 256

(* 組み込みのキーを再宣言した利用者の宣言の記録。
   受理するが採用しないという扱いは 1 回までで、2 回目は普通のコヒーレンス違反として拒否する。
   この記録が無いと、同じキーを 2 度登録したらエラーにするという規則が、
   組み込みのキーにだけ効かない *)
let builtin_redecls : (oid * oid, unit) Hashtbl.t = Hashtbl.create 16

(* 予約述語の名前の表。
   予約の規則を持つのはこの表だけで、クラス宣言の側(第11章の register_class)と
   インスタンス宣言の側(下の add_instance)がどちらもここを引く。
   登録するのは §6.12 の register_builtins である *)
let reserved_predicates : (oid, unit) Hashtbl.t = Hashtbl.create 4
let reserved_predicate c = Hashtbl.mem reserved_predicates c

(* コヒーレンスの規則として、重複したキーを拒否する(sample.kel:357)。
   組み込みと同じキーの利用者の宣言は、照合の上で受理する(本体は第11章が検査する) *)
let add_instance ?(builtin = true) ?(methods = []) ~cls ~con premises =
  (* 予約述語は、インスタンスの入口でも拒否する(§6.12)。免除するのは組み込みの
     登録(builtin = true)だけである。組み込みの登録自身が Integral[Int32] /
     Fractional[Float64] をここから入れる。免除の条件を in_prelude にしない理由は §6.12 *)
  (if reserved_predicate cls && not builtin then
     type_error (Type.name_of cls ^ " は予約されたリテラル述語です(インスタンスは宣言できません、D8)"));
  match Hashtbl.find_opt instances (cls, con) with
  | Some prev when prev.ii_builtin && not builtin ->
      (* 実体は組み込みのまま。利用者の本体は第11章が検査する(受理は 1 回まで) *)
      if Hashtbl.mem builtin_redecls (cls, con) then
        type_error
          ("インスタンス " ^ Type.name_of cls ^ "[" ^ Type.name_of con ^ "] が二重に宣言されています(コヒーレンス違反)")
      else Hashtbl.add builtin_redecls (cls, con) ()
  | Some _ ->
      type_error
        ("インスタンス " ^ Type.name_of cls ^ "[" ^ Type.name_of con ^ "] が二重に宣言されています(コヒーレンス違反)")
  | None -> Hashtbl.add instances (cls, con) { ii_premises = premises; ii_builtin = builtin; ii_methods = methods }

let find_instance ~cls ~con = Hashtbl.find_opt instances (cls, con)

(* そのキーが組み込みインスタンスとして登録済みか(interp が実体を差し替えないため) *)
let builtin_instance_exists cls con =
  match Hashtbl.find_opt instances (cls, con) with Some { ii_builtin; _ } -> ii_builtin | None -> false

(* ## 6.10 組み込み登録の補助関数

   ここから下は、ソースに書けない宣言や、ソースに書かせたくない宣言を、
   本章が直接表へ入れる部分である。

   `generic` が作るのは Generic の型変数、つまり量化されていることを表す印を付けた変数である。
   Diktor は型スキーマ専用のデータ型を持たず、変数の状態 1 つで多相を表す。
   Generic の変数では `vlevel` を使わない。

   `closed_args_row` は、引数の並びを `_item` ラベルの閉じた行に畳む。
   Keleut の引数の並びは `_item` の連なりでできたタプル、つまりレコードなので、
   矢印の引数側はいつもこの形になる。
   行を閉じるのは、引数の個数が呼び出しで確定しなければならないからである。

   メソッドのスキーマは、§6.12 の `arrow1` / `arrow2` がその場で組み立てる。
   要点は 2 つある。
   1 つ目は、最外の矢印の行を Generic の行変数にすることである。
   仕様は、メソッドの最外の矢印で `@` を省略すると、どのインスタンスの実装も純粋でなければならず、
   公開される型は行多相になると定めている(仕様 §9、sample.kel:433-436)。
   入れ子の矢印で省略した `@` を `@ {}` と読む規則(sample.kel:496-502)もあるが、
   組み込みのメソッドはどれも高階ではないので、この規則が効く箇所は無い。
   2 つ目は、クラスパラメータの変数をクラス内で共有することである(§6.12 の代入点)。 *)

(* 登録用の Generic 変数(Generic の変数は vlevel を使わない) *)
let generic ?(kind = Type.KStar) ?(classes = []) () =
  Type.TVar (ref (Type.Generic { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes }))

let closed_args_row tys =
  List.fold_right (fun t acc -> Type.TRowExtend (Type.l_item, t, acc)) tys Type.TRowEmpty

let intern = Type.intern

(* ## 6.11 Ref と配列、リージョンの行

   `Ref` と配列の操作は、本章が直接登録する。
   型パラメータ `[h]` を持つ extern 署名として同じ型を書くことはでき、その場合も脱出検査は効く。
   それでも組み込みにするのは、実装が OCaml 側の値(§14.11)と切り離せず、
   プレリュードに型を置くと型と実装を別々に管理することになるからである(§15.1 の基準)。

   ### 行を開いておく

   `heap_row h` は、`Heap[h]` を Generic の行変数の尾部の上に載せ、行を開いておく。
   行を `Heap[h]` だけの閉じた行にすると、
   `Console` の下でも `Async` の下でも `Ref.get` を呼べなくなる。
   プログラムのほとんどは何かのエフェクトの下で走るので、
   行を閉じるとこれらの操作は実質的に使えない。

   ### `Ref` はリージョンを型に持つ

   `Ref.new` の返り型は `Ref[h, A]` で、リージョン変数 `h` が値の型に現れる。
   そのため、参照を `run` の外へ持ち出そうとすると、
   第8章の脱出検査(剛定数がスコープの外に漏れていないかの検査)が拒否する。
   Haskell の `ST` と同じ仕組みである。

   ### 不変の `Array[A]` と可変の `MutableArray[h, A]`

   仕様 §10 は配列を 2 つに分ける。
   不変の `Array[A]` はリージョンを型に持たず、読む操作しか持たない。
   可変の `MutableArray[h, A]` は、`Ref[h, A]` と同じくリージョン変数 `h` を値の型に持ち、
   生成も読み出しも書き込みも `Heap[h]` を要求する。
   2 つをつなぐのは `MutableArray.freeze` だけで、
   `MutableArray[h, A]` から `h` の消えた `Array[A]` を取り出す。

   この分け方は、次の 3 つを守る。
   第一に、引数の可変配列に書き込む関数は、純粋な関数として型付けされない。
   可変配列の `h` は呼び出し側から来た剛定数で、
   関数の中の `run` が導入した別の剛定数とは一致しないからである。
   第二に、§6.11b の `par_map` に渡す `@ {}` のコールバックは、可変配列に触れられない。
   第三に、`@` を省略した `pub` の宣言は純粋であるという規則を守る。
   newtype のフィールドを経由しても、死んだリージョンの可変配列に書き込む閉包を、
   純粋な関数として取り出すことはできない。
   入れ子の矢印で省略した `@` は `@ {}` と読むので、
   フィールドの閉包の型に `Heap[h]` を隠せないからである。
   `test/region.t` の adv5 が、この経路が閉じていることを確かめる。

   リージョンが守れるのは、`h` が型に現れている値だけである。
   `Array[A]` は `h` を持たないので、`Array` の組み込み操作には生成と書き込みを置かない。
   `Heap[h]` を要求しても結果の型に `h` が現れなければ、`run` の中で作った配列を外へ持ち出せ、
   外から渡された配列を `run h { … }` で包むだけで書き換えられてしまう。
   `test/region.t` の noset と nonew は、`Array.set` と `Array.new` が存在しないことを確かめる。

   `freeze` の契約では、取り出した後に元の可変配列へ書き込んでも、取り出した不変配列は変わらない。
   この契約は 1 段だけに適用する。
   要素そのものが可変配列なら、取り出した配列の要素は、
   元の可変配列の要素と同じものを指す(sample.kel:690)。
   `test/region.t` の nested は、`freeze` の後に内側の配列へ書き込んだ 99 を、
   `frozen` を通して読み出す。
   値は共有されるが、型は破れない。
   要素の `h` が結果の型 `Array[MutableArray[h, A]]` に残るので、
   脱出検査がリージョンの外への持ち出しを拒否する(sample.kel:691)。
   nested2 は、この持ち出しが「スコープ付きの型 ς1 がスコープの外に漏れています」で落ちることを確かめる。
   flat は、要素が可変配列でなければ同じ形が通ることを確かめる。

   `Array.length` と `Array.get` は純粋な操作なので、行に何も足さない。
   ただし、これらの行は `TRowEmpty` ではなく Generic の行変数にする。
   `TRowEmpty` にすると呼び出し側の行まで空に縛られ、`Console` の下から読めなくなる。
   `MutableArray.length` は、長さが変わらないのに `Heap[h]` を要求する。
   これは仕様の署名の一覧のとおりで、仕様はその理由も定めている。
   `Heap[h]` を要求するのは、長さが変わりうるからではなく(長さを変える操作は無い)、
   可変配列に触れること自体を行に記録するためである(sample.kel:692)。

   `Array.each` の行 `e` は、コールバックと呼び出し全体で共有する。
   高階関数がエフェクト多相であるための最小の形である。
   別々の変数にすると、`each` にエフェクトを起こす関数を渡せなくなる。
   `Array.each` は `Heap` を要求しない。
   不変配列を読むことは純粋だからである。

   `MutableArray` のカインドは `Ref` と同じ `k_arrow 2` で、
   リージョンのパラメータのカインドは `KStar` である。
   `run h` が作る剛定数の既定のカインドが `KStar` なので、リージョンのために別のカインドは要らない。

   ここで決まる 11 個の操作名は、そのまま値環境での名前になる。
   内訳は、`Ref` の `new` / `get` / `set`、`Array` の `length` / `get` / `each`、
   `MutableArray` の `new` / `length` / `get` / `set` / `freeze` である。
   第11章の module の平坦化は、利用者の `module` 宣言がこれと同じ綴りの修飾名を作ることを拒否する(§11.42)。
   組み込みの操作をここに足すと、保護される綴りも同時に 1 つ増える。 *)

let builtin_ops : (string * Type.ty) list ref = ref []

let register_ref_array () =
  let ref_oid = intern "Ref" and arr_oid = intern "Array" and marr_oid = intern "MutableArray" in
  Hashtbl.replace con_kinds ref_oid (Type.k_arrow 2);
  Hashtbl.replace con_kinds arr_oid (Type.k_arrow 1);
  Hashtbl.replace con_kinds marr_oid (Type.k_arrow 2);
  let ginfo () = { Type.vid = new_oid (); vlevel = 0; vkind = Type.KStar; vcls = [] } in
  add_data { dd_name = ref_oid; dd_params = [ ginfo (); ginfo () ]; dd_ctors = []; dd_opaque = true };
  add_data { dd_name = arr_oid; dd_params = [ ginfo () ]; dd_ctors = []; dd_opaque = true };
  add_data { dd_name = marr_oid; dd_params = [ ginfo (); ginfo () ]; dd_ctors = []; dd_opaque = true };
  (* 操作を持たない組み込みのエフェクトラベル *)
  add_effect { ef_name = Type.eff_heap; ef_ops = [] };
  add_effect { ef_name = Type.eff_blocking; ef_ops = [] };
  let arrow args ret eff = Type.TArrow (Type.TRecord (closed_args_row args), ret, eff) in
  let heap_row h = Type.TRowExtend (Type.eff_heap, h, generic ~kind:Type.KRow ()) in
  let def name ty = builtin_ops := !builtin_ops @ [ (name, ty) ] in
  (* Ref.new : [h, A] (A) => Ref[h, A] @ {Heap[h] extends ρ} *)
  (let h = generic () and a = generic () in
   def "Ref.new" (arrow [ a ] (Type.TCon (ref_oid, [ h; a ])) (heap_row h)));
  (let h = generic () and a = generic () in
   def "Ref.get" (arrow [ Type.TCon (ref_oid, [ h; a ]) ] a (heap_row h)));
  (let h = generic () and a = generic () in
   def "Ref.set" (arrow [ Type.TCon (ref_oid, [ h; a ]); a ] Type.t_unit (heap_row h)));
  (* Array は不変(仕様 §10)。読み出しは行に何も足さない。TRowEmpty ではなく Generic の
     行変数にするのは、行を閉じると Console の下から読めなくなるため *)
  (let a = generic () in
   def "Array.length" (arrow [ Type.TCon (arr_oid, [ a ]) ] Type.t_int32 (generic ~kind:Type.KRow ())));
  (let a = generic () in
   def "Array.get" (arrow [ Type.TCon (arr_oid, [ a ]); Type.t_int32 ] a (generic ~kind:Type.KRow ())));
  (let a = generic () and e = generic ~kind:Type.KRow () in
   def "Array.each" (arrow [ Type.TCon (arr_oid, [ a ]); arrow [ a ] Type.t_unit e ] Type.t_unit e));
  (* MutableArray は h を型に持つ。すべての操作が Heap[h] を要求する。length も
     仕様 §10 の署名の一覧のとおり *)
  (let h = generic () and a = generic () in
   def "MutableArray.new" (arrow [ Type.t_int32; a ] (Type.TCon (marr_oid, [ h; a ])) (heap_row h)));
  (let h = generic () and a = generic () in
   def "MutableArray.length" (arrow [ Type.TCon (marr_oid, [ h; a ]) ] Type.t_int32 (heap_row h)));
  (let h = generic () and a = generic () in
   def "MutableArray.get" (arrow [ Type.TCon (marr_oid, [ h; a ]); Type.t_int32 ] a (heap_row h)));
  (let h = generic () and a = generic () in
   def "MutableArray.set" (arrow [ Type.TCon (marr_oid, [ h; a ]); Type.t_int32; a ] Type.t_unit (heap_row h)));
  (let h = generic () and a = generic () in
   def "MutableArray.freeze" (arrow [ Type.TCon (marr_oid, [ h; a ]) ] (Type.TCon (arr_oid, [ a ])) (heap_row h)))

(* ## 6.11b par / par_map

   `par` / `par_map` の型は、下のとおり Keleut の構文で書ける。
   Diktor はこの 2 つを、Ref / Array と同じく組み込みとして登録する。
   型は本章に、値は §14.11 に置く。
   値の実装は関数の適用を使い、適用は第14章にあるので、第13章には置けない。
   §14.11 の実装は、コールバックを決まった順序で逐次に呼ぶ。
   コールバックの行が `@ {}` に閉じているので、
   コールバックは実行の順序を観測できるエフェクトを起こせない。

   型の要点は 2 つある。
   1 つ目は、コールバックの行を閉じた空の行(`TRowEmpty`)にすることである。
   仕様は sample.kel:720 で、「並列処理は純粋な計算に限るので、結果は決定的である」と保証している。
   この保証が成り立つのは、ここでコールバックに純粋であることを要求しているからである。
   2 つ目は、外側の行を Generic の行変数にすることである。
   `TRowEmpty` にすると、トップレベルから呼べない関数になる。

   同じ型の `par` を Keleut のソースで定義すると、型が付くかどうかは書き方で決まる。
   行の部分型付け(サブエフェクティング)が無いからである(§11.26)。
   本体に `(fa(), fb())` と書くと、`@ {}` のコールバックを呼ぶので、本体の行は空に固まる。
   書き方ごとの結果は次のとおりである。

   - `@` を省略した `let` なら、§11.26 の `reopen_pure_row` が公開の前に行を開き直すので、
     `par` と同じ型になる。
   - 外側の矢印に `@ {}` を明示すると、行は閉じたままになり、
     トップレベルから呼ぶと「ラベル Console がありません」で落ちる。
   - `pub let` にすると、「pub な宣言はエフェクトを起こせません」で落ちる。
   - 本体を `run h { … }` で包むと、`Heap[h]` が行にある文脈で `@ {}` の関数を呼ぶことになり、
     「ラベル Heap がありません」で落ちる。 *)
let register_parallel () =
  let arr_oid = intern "Array" in
  let arrow args ret eff = Type.TArrow (Type.TRecord (closed_args_row args), ret, eff) in
  let def name ty = builtin_ops := !builtin_ops @ [ (name, ty) ] in
  (* par_map : [A, B] (Array[A], (A) => B @ {}) => Array[B] @ ρ *)
  (let a = generic () and b = generic () and e = generic ~kind:Type.KRow () in
   def "par_map" (arrow [ Type.TCon (arr_oid, [ a ]); arrow [ a ] b Type.TRowEmpty ] (Type.TCon (arr_oid, [ b ])) e));
  (* par : [A, B] (() => A @ {}, () => B @ {}) => (A, B) @ ρ *)
  (let a = generic () and b = generic () and e = generic ~kind:Type.KRow () in
   def "par" (arrow [ arrow [] a Type.TRowEmpty; arrow [] b Type.TRowEmpty ] (Type.TRecord (closed_args_row [ a; b ])) e));
  (* pinned : [A, E] (() => A @ {Blocking extends E}) => A @ E。
     Blocking は操作を持たない組み込みのラベル(§6.11)なので、Blocking を行から
     落とすのは型の上だけの操作である。run が実行時には恒等写像である(§14.4)のと
     同じ構図である。@ Blocking の関数はトップレベルから直接呼べる(仕様 §9 / §12)。
     pinned が要るのは、行を注釈で閉じた内側の文脈へ持ち込むときである *)
  (let a = generic () and e = generic ~kind:Type.KRow () in
   def "pinned" (arrow [ arrow [] a (Type.TRowExtend (Type.eff_blocking, Type.t_unit, e)) ] a e))

(* ## 6.12 組み込みのクラスと数値インスタンス

   演算子が呼ぶクラス(第7章(prims.ml)の表の右辺)を、ここで直接登録する。
   これらをプレリュードのソースで書かずに OCaml 側に置くのは、
   これらのクラスの実装がプリミティブにしか無いからである。

   `register_builtins` の最初の 3 行は、`in_prelude` を立て、`Fun.protect` で必ず元に戻す。
   組み込みの登録をプレリュードの処理として扱うので、
   `mark` が組み込みのデータ型とエフェクトを `prelude_keys` に記録する。
   そのため、sample.kel が `Never` を宣言し直しても §6.1 の経路に乗る。
   `Add` や `Add[Int32]` のようなクラスとインスタンスは、
   `in_prelude` ではなく `ci_builtin` / `ii_builtin` で見分ける(§6.1)。
   `Fun.protect` は、例外で抜けてもフラグが戻ることを保証する。
   フラグが戻らないと、以後の利用者の宣言がすべてプレリュード所有として記録され、
   二重宣言の検査がまったく効かなくなる。

   `def_class` は、クラスパラメータの Generic 変数 `pinfo` を 1 つ作り、
   全メソッドで共有する(§6.8 の代入点)。
   クラスの分け方は sample.kel:371 のとおりである。
   `Num` のような 1 つのクラスにまとめないのは、`String` のように `+` だけを持つ型があるからである。
   そのため、`Add` のインスタンスにだけ String が入り、`Sub` / `Mul` / `Div` には入らない。
   `Ord` に Boolean が入っていないのは、真偽値に大小を定めていないからである。

   `Integral` / `Fractional` は予約述語である。
   メソッドを持たないクラスとしてクラス表 `classes` に同居させるだけで、専用の機構は持たない。
   型変数に付くクラス制約の集合がすでにあるので、リテラルの型を絞る仕組みを別に作らずに済む。
   `1 + x` で `{Integral, Add}` の 2 つが同じ変数に付くときも、
   制約の集合の扱いがそのまま正しく働く。
   既定化は一般化の直前に走るので、通常はこの述語が表示に現れることはない。

   予約は、宣言の 3 つの入口のすべてで効かせる。
   同名のクラス宣言は、第11章の `register_class` が拒否する。
   インスタンス宣言は、第11章の `register_instance` が頭を見た時点で拒否し、
   §6.9 の `add_instance` も拒否する。
   型パラメータの制約(`[A: Integral]` と書く形)は、第11章の `class_names_of` が拒否する。
   どの検査も、§6.9 の `reserved_predicates` 表を引く。
   `reserved_predicates` 表は入口で名前を検査するだけで、
   予約述語の意味(リテラルの既定化でどう扱うか)は持たない。
   その意味は、第8章(unify.ml)が第1章の定数で別に持つ。

   入口を 1 つでも開けておくと、予約述語が汚染され、リテラルの既定化の前提が崩れる。
   インスタンス宣言の入口が開いていると、`type instance Integral[String]` が表に載り、
   `[A: Integral]` の制約の解決に使われる。
   メソッドが 0 個なので、メソッドの網羅と過剰の検査はこの宣言を止めない。
   制約の入口が開いていると、`let f[A: Integral](): A = 1` が型検査を通り、
   実行時に「数値リテラルの型が解決されていません」で落ちる。

   インスタンス側の検査を免除するのは、組み込みの登録(`builtin = true`)だけである。
   下の `register_builtins` 自身が、
   `Integral[Int32]` や `Fractional[Float64]` を `add_instance` で登録するからである。
   免除の条件を `in_prelude` にすると、`--prelude` で差し替えた利用者のプレリュードまで免除され、
   予約を迂回する経路になる。

   `register_builtins` が登録する `Never` が、
   §6.6 で述べたコンストラクタが 0 個のデータ宣言である。 *)

let register_builtins () =
  (* 組み込みの登録はプレリュードとして扱う(同名の利用者の宣言を照合の上で受理するため) *)
  let saved = !in_prelude in
  in_prelude := true;
  Fun.protect ~finally:(fun () -> in_prelude := saved) @@ fun () ->
  (* 組み込み型。実行できる数値型は 3 つで、ほかの数値型の名前の受理と拒否は elab が行う *)
  List.iter
    (fun n -> Hashtbl.replace con_kinds (intern n) Type.KStar)
    [ "Boolean"; "Int32"; "Int64"; "Float64"; "String"; "Never" ];
  List.iter (fun n -> Hashtbl.replace reserved_type_names (intern n) ())
    [ "Boolean"; "Int32"; "Int64"; "Float64"; "String" ];
  let numerics = [ "Int32"; "Int64"; "Float64" ] in
  (* クラスとメソッド(sample.kel:372-395 にあたる宣言を本章が直接登録する)。
     クラスパラメータの変数はクラス内で共有する(インスタンス検査の代入点) *)
  let def_class name ~derive ~methods ~instances:insts =
    let cls = intern name in
    let pinfo = { Type.vid = new_oid (); vlevel = 0; vkind = Type.KStar; vcls = [ cls ] } in
    let a = Type.TVar (ref (Type.Generic pinfo)) in
    Hashtbl.replace classes cls
      {
        ci_name = cls;
        ci_param = pinfo;
        ci_param_kind = Type.KStar;
        ci_derive_structural = derive;
        ci_builtin = true;
        ci_methods = methods a;
      };
    List.iter (fun con -> add_instance ~cls ~con:(intern con) []) insts
  in
  let arrow2 a ret = Type.TArrow (Type.TRecord (closed_args_row [ a; a ]), ret, generic ~kind:Type.KRow ()) in
  let arrow1 a ret = Type.TArrow (Type.TRecord (closed_args_row [ a ]), ret, generic ~kind:Type.KRow ()) in
  def_class "Add" ~derive:false ~methods:(fun a -> [ ("add", arrow2 a a) ]) ~instances:("String" :: numerics);
  def_class "Sub" ~derive:false ~methods:(fun a -> [ ("sub", arrow2 a a) ]) ~instances:numerics;
  def_class "Mul" ~derive:false ~methods:(fun a -> [ ("mul", arrow2 a a) ]) ~instances:numerics;
  def_class "Div" ~derive:false ~methods:(fun a -> [ ("div", arrow2 a a) ]) ~instances:numerics;
  def_class "Eq" ~derive:true
    ~methods:(fun a -> [ ("eq", arrow2 a Type.t_boolean) ])
    ~instances:("String" :: "Boolean" :: numerics);
  def_class "Ord" ~derive:false
    ~methods:(fun a -> List.map (fun m -> (m, arrow2 a Type.t_boolean)) [ "lt"; "le"; "gt"; "ge" ])
    ~instances:("String" :: numerics);
  def_class "Show" ~derive:false
    ~methods:(fun a -> [ ("show", arrow1 a Type.t_string) ])
    ~instances:("String" :: "Boolean" :: numerics);
  (* 予約述語。メソッドの無いクラスとして表に同居させる *)
  List.iter (fun n -> Hashtbl.replace reserved_predicates (intern n) ()) [ "Integral"; "Fractional" ];
  def_class "Integral" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Int32"; "Int64" ];
  def_class "Fractional" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Float64" ];
  (* Never はコンストラクタが 0 個のデータ宣言。complete_sig が Some [] を返すので、
     節が 0 個の match が網羅になる *)
  add_data { dd_name = intern "Never"; dd_params = []; dd_ctors = []; dd_opaque = false };
  builtin_ops := [];
  register_ref_array ();
  register_parallel ()

(* ## 6.13 値環境への登録と表の初期化

   `builtin_values` は、クラスメソッドを普通の多相の定数として値環境に並べる。
   型クラスのメソッドに特別な扱いは要らない。
   メソッドの型はクラス制約つきの Generic 変数を含む多相型で、名前の探索は普通の変数参照であり、
   実装の選択は第14章が実行時に値のタグを見て行う。

   sample.kel はメソッドを非修飾名 `add` と修飾名 `Add.add` のどちらの形でも参照するので、
   メソッドは両方の名前で値環境に登録する。

   組み込みの値の名簿は `builtin_values` の 1 つだけである。
   第11章の平坦化が、組み込みがすでに置いている綴りかどうかを問い合わせるときも、
   問い合わせ口 `is_builtin_value` を通して `builtin_values` を引く(§11.42)。
   名簿を 2 つ作ると、組み込みの操作を足したときに片方を直し忘れ、
   保護しているはずの綴りが保護されなくなる。
   `is_builtin_value` は問い合わせのたびに名簿を組み立て直す。
   その費用は `classes` を 1 回たどるだけで、
   呼ばれるのも module のメンバ 1 つにつき高々 1 回である。

   `reset` は、同じプロセスで繰り返し呼ぶ API のためにある。
   CLI は 1 つのプロセスで 1 つのプログラムしか扱わないので、`reset` を呼ばない。
   呼ぶのは第16章の `type_check_string` / `eval_string` である。
   宣言表が残っていると、2 回目の呼び出しは同じプログラムでも「二重に宣言されています」で落ちる。

   第16章は、`reset`、平坦化、型検査の順に呼ぶ。
   平坦化の後に `reset` を呼ぶと、平坦化が張った同義語を `reset` が消してしまう。

   `reset` が表を 1 つでも戻し忘れると、前の呼び出しが残した宣言が次の呼び出しに漏れる。
   その結果、単独では通るプログラムが、ほかのプログラムの後に検査すると落ちるという、
   原因を追いにくい不具合になる。
   本章に表を足したら、`reset` にも足さなければならない。
   `Type.intern` の oid の表は戻さない。
   長時間走る API では oid が単調に増えるが、実害は無い。

   末尾の `let () = register_builtins ()` は、モジュールを初期化する時点で組み込みを登録する。
   表がモジュールの状態なので、この副作用を伴う初期化が要る。
   第16章(driver.ml)が何かをする前に、組み込みはすでに表に載っている。 *)

let builtin_values () =
  Hashtbl.fold
    (fun _ ci acc ->
      List.fold_left
        (fun acc (m, ty) -> (m, ty) :: (Type.name_of ci.ci_name ^ "." ^ m, ty) :: acc)
        acc ci.ci_methods)
    classes []
  @ !builtin_ops

(* 組み込みが値環境に置く名前かどうか(修飾名 Ref.new / MutableArray.set と、
   クラスメソッドの Show.show / show の両方を含む)。
   module の平坦化が同じ綴りの修飾名を作るのを拒否するために、第11章が引く。
   名簿は builtin_values の 1 つだけで、この関数は問い合わせ口にすぎない *)
let is_builtin_value name = List.mem_assoc name (builtin_values ())

let reset () =
  Hashtbl.reset con_kinds;
  Hashtbl.reset aliases;
  Hashtbl.reset classes;
  Hashtbl.reset instances;
  Hashtbl.reset builtin_redecls;
  Hashtbl.reset datas;
  Hashtbl.reset ctor_owner;
  Hashtbl.reset effects;
  Hashtbl.reset op_index;
  Hashtbl.reset prelude_keys;
  Hashtbl.reset con_synonyms;
  Hashtbl.reset val_synonyms;
  Hashtbl.reset reserved_type_names;
  Hashtbl.reset reserved_predicates;
  Hashtbl.reset externs;
  Hashtbl.reset type_namespace;
  Hashtbl.reset user_type_redecls;
  Hashtbl.reset module_con_synonyms;
  Hashtbl.reset module_val_synonyms;
  Hashtbl.reset con_hints;
  Hashtbl.reset value_visibility;
  Hashtbl.reset con_visibility;
  Hashtbl.reset decl_module;
  current_module := None;
  in_prelude := false;
  register_builtins ()

let () = register_builtins ()
