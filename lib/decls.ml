(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第6章 — 宣言環境: 名前の世界

   型検査には 2 つの半分があります。ひとつは型と型を突き合わせる仕事で、
   これは第8章 (unify.ml) が受け持ちます。もうひとつは**名前が何を指すかを
   決める**仕事で、その答えを持っている唯一の場所が本章です。

   `List[A]` の `List` はカインドいくつの構成子か。`IoError` はエイリアスか
   エフェクト名か。`Some` はどのデータ型のコンストラクタで、フィールドは
   何番目か。`write` はどのエフェクトの操作か。`Add` にはどんなメソッドが
   あり、`Int32` はそのインスタンスか。これらはすべて宣言表への問い合わせで、
   主な表が 8 系統あります(計画 §7.1)。

   | 表 | キー | 値 | 主な読み手 |
   |---|---|---|---|
   | `con_kinds` | 型構成子 | カインド | 第8章 (`kind_of`) |
   | `con_synonyms` | 非修飾名 | 正準の修飾名 | 第11章・第14章 (D21) |
   | `aliases` | エイリアス名 | パラメータと本体 | 第11章 (透過展開) |
   | `datas` / `ctor_owner` | 型名 / ctor 名 | コンストラクタとフィールド | 第10・11章 |
   | `effects` / `op_index` | 効果名 / 操作名 | スキーマ / 候補列 | 第11章 (D22) |
   | `classes` | クラス名 | パラメータとメソッド | 第8章・第11章・第14章 |
   | `instances` | (クラス, 型構成子) | 前提とメソッド本体 | 第8章・第11章・第14章 |
   | `externs` | extern 名 | 登録済みの印 | 第11章 |

   読み手の欄に第14章 (interp.ml) が並ぶ表と並ばない表があるのは、第5章
   (tree.ml) が掲げた「評価器は名前解決をやり直さない」の裏返しです。データ型と
   コンストラクタは精緻化のときに `RCtor` / `RCtorPat` へ焼き込んであるので、
   評価器が `datas` / `ctor_owner` を引くことは 1 度もありません。逆に型クラスの
   選択だけは実行時の値のタグを見て決める(裁定 D3)ので、`classes` と
   `instances` は評価器も読みます。

   全部が大域の可変ハッシュ表です。利点は MiniLang と同じで、
   **インスタンス探索もカインド取得も表引き 1 回**で終わること
   (MiniLang §2 と MiniLang §3 と同じ設計)。代償も同じで、処理系の状態が
   大域にあるため `reset` が要り、2 つのプログラムを同時に検査できません。
   ひとつのプロセスで複数のテストを回す本実装では、`reset` の網羅性が
   そのままテストの独立性になります(§6.13)。

   ## 本章を貫く 1 つの問題

   宣言表の規則は素朴には「同じ名前を二度宣言したら拒否」で済みます。
   ところが Keleut ではこれが成り立ちません。**仕様書である sample.kel 自身が、
   プレリュードにあるはずの `Unit` / `List` / `Console` / `Add` /
   `Add[Int32]` / `Never` を宣言しているから**です。教材として「これが標準
   ライブラリの中身だ」と示すことが目的なので、当然そう書かれています。

   そこで採った運用裁定が「**照合の上で受理する**」です(実装記録 260829-2 の
   乖離 4、計画 §7.4 の具体化)。プレリュードや組み込みが先に置いた名前と
   同じ宣言をユーザが書いたら、宣言そのものは検査するが、**表に入っている
   実体は差し替えない**。ユーザ同士の重複は従来どおり拒否する。

   > 受理することと、採用することは別である。

   この 1 行を守り損ねた箇所が、敵対的検証で実際に見つかりました(§6.9)。

   ## 前章から受け取るもの

   第5章 (tree.ml) の `Tree.Tree`(型式を表に格納するため)と、
   第1章 (syntax.ml) の内部型 `Type.ty`。

   ## 次章へ渡すもの

   第8章 (unify.ml) 以降が、名前の問い合わせ先としてこの表を引きます。
   間に挟まる第7章 (prims.ml) だけは葉のままで、第1章 (syntax.ml) の
   `bin_op` 以外には何も要りません。このファイルが登録したクラスにも、
   **名前だけ**を文字列で触れます。 *)
open Aux
open Syntax
module T = Tree.Tree

(* ## 6.1 誰が先に置いたかを覚える

   「照合の上で受理」を実装するには、表の各エントリについて
   **プレリュード由来か、ユーザ由来か**を区別できなければなりません。
   その区別を持つのが `prelude_keys` です。

   第11章 (elab.ml) はプレリュードを処理する間だけ `in_prelude` を立て、
   組み込み登録(§6.12)も同じフラグを立てて走ります。フラグが立っている間に
   登録された `(表の種別, 名前)` の組だけが `prelude_keys` に記録され、
   あとから同じ名前が来たときの分岐に使われます。

   種別を鍵に含めているのは、`extern` の `foo` と型エイリアスの `foo` が
   別物だからです。名前だけを鍵にすると、片方の登録がもう片方の再宣言を
   黙って許してしまいます。

   なお「プレリュード所有」の表し方はこのファイルの中で 2 通りあります。
   ここの鍵集合と、`ci_builtin` / `ii_builtin` というレコード内のフラグ
   (§6.8, §6.9)です。クラスとインスタンスは**呼び出し側に「どちらが勝ったか」
   を返す必要がある** — 受理した宣言の本体は検査を続けるので — ため、
   値の中にフラグを持たせるほうが素直でした。 *)
let in_prelude = ref false

let prelude_keys : (string * oid, unit) Hashtbl.t = Hashtbl.create 64

let mark kind name = if !in_prelude then Hashtbl.replace prelude_keys (kind, name) ()

let prelude_owned kind name = Hashtbl.mem prelude_keys (kind, name)

(* 型名の名前空間は 1 つ — newtype も型エイリアスも effect も、名前は同じ
   `con_kinds` に落ちる。ところが二重宣言検査は種別ごとの表に分かれている
   ので、それだけだと**種別を替えた再宣言**が全部の検査をすり抜ける。
   `type List[A] = Int32` は aliases 表には初出なので素通りし、以後の
   `List[X]` がすべて Int32 を意味して、プレリュードの List は値だけ作れて
   型名を書けない幽霊型になる(M15 検証)。§6.1 の理屈 —「名前だけを鍵に
   すると、片方の登録がもう片方の再宣言を黙って許してしまう」— は、
   同じ名前空間を共有する型名たちには裏返しに効く。先に置いた種別をここに
   覚え、別種別での再宣言は登録の時点で拒否する *)
let type_namespace : (oid, string) Hashtbl.t = Hashtbl.create 64

let claim_type_name kind name =
  match Hashtbl.find_opt type_namespace name with
  | Some prev_kind when prev_kind <> kind ->
      type_error (Type.name_of name ^ " は既に " ^ prev_kind ^ " として宣言されています(" ^ kind ^ " では再宣言できません)")
  | _ -> Hashtbl.replace type_namespace name kind

(* プレリュード所有名の「照合の上で受理」(D35)は 1 プログラム 1 回まで。
   2 本目からはユーザ同士の重複そのもので、従来どおり拒否する。これが
   無いと「二重に宣言されています」がプレリュード所有名についてだけ嘘に
   なる — インスタンス側の builtin_redecls (§6.9) と同じ理屈(M15 検証) *)
let user_type_redecls : (string * oid, unit) Hashtbl.t = Hashtbl.create 16

let note_user_redecl kind name what =
  if not !in_prelude then
    if Hashtbl.mem user_type_redecls (kind, name) then
      type_error (what ^ " " ^ Type.name_of name ^ " が二重に宣言されています")
    else Hashtbl.add user_type_redecls (kind, name) ()

(* ## 6.2 extern 登録簿 — 敵対的検証で塞いだ穴 (1)

   `extern` はプリミティブに**型を与える**宣言です。実装は第13章 (builtin.ml)
   の表にあり、型はプレリュードの `extern` 宣言で与えられます(計画 §8.6)。
   つまり `extern` の型注釈は、処理系が検証できない約束です。

   ここが穴でした。当初 `extern` 名には登録簿が無く、ユーザが

   - `__int32_add` の引数型を String だと**再宣言**する

   ことができました。第13章の実装は Int32 を前提にしているので、型検査は
   通り、実行時に嘘の型のまま呼ばれます。**プリミティブの型注釈は信頼の
   基点なので、上書きを許した時点で型システム全体の土台が抜けます。**

   対策はこの登録簿 1 枚です。すでに登録済みの名前は、プレリュード所有なら
   「再宣言できません」、ユーザ由来なら「二重に宣言されています」で拒否する。
   ここだけ「照合の上で受理」を採らないのは、`extern` には照合すべき実体が
   処理系側に無いからです。名前が同じでも、それが同じ約束だとは言えません。

   > 検証できない宣言は、上書きも許してはいけない。

   もうひとつ、登録簿の効き目は**プレリュードが宣言した名前の分だけ**です。
   実装表にあるのに宣言の無い名前は登録簿に載らず、そこが死角になります。
   かつて比較の 9 本と `__show_int32` がこの死角にあり、嘘の型で宣言して
   実装に到達できました(型検査が Int32 と言った式が実行時に false を表示
   するところまで実測)。塞ぎ方は検査の追加ではなく、プレリュード側の
   一覧を実装表と完全対応にすること(第15章 §15.5 の不変条件)でした。

   効き目の範囲も正直に書いておきます。登録簿が守るのは**プレリュードが
   宣言した名前だけ**です。`--no-prelude`(と、宣言の欠けた `--prelude`)
   では登録簿が空になり、全プリミティブが再宣言可能に戻ります — そこでは
   型と実装の約束をユーザ(処理系開発者)が引き受けます。旗を立てた人が
   責任を持つ、という線引きです。

   鍵は 2 種類を使い分けます。**プレリュード保護は非修飾の実装名**
   (第1章 `ex_prim`)で見ます — module 内の `extern` は Keleut 側の名前が
   `M.f` に修飾されるので、修飾名で見ると保護を module の中からすり抜け
   られます(実測)。**二重宣言の検査は修飾名**で見ます — 実装名まで大域
   一意にすると、`module Fast` と `module Precise` が同じ C シンボル
   `sqrt` をそれぞれの名前で束縛する正当な形が書けなくなります(これも
   敵対的検証が見つけた、実装名一本鍵の版の回帰でした)。 *)
let externs : (oid, unit) Hashtbl.t = Hashtbl.create 64

let add_extern ~prim name =
  let o = Type.intern name in
  let po = Type.intern prim in
  (* プレリュード保護は実装名(非修飾の prim)で見る — module の中からの
     迂回を防ぐ。二重宣言のほうは Keleut 側の名前(修飾名)で見る — 別々の
     module が同じ C シンボルをそれぞれの名前で束縛するのは正当で、
     実装名まで大域一意にすると module Fast と module Precise が両方
     sqrt を包めなくなる(敵対的検証で見つけた回帰の修正) *)
  if prelude_owned "extern" po then type_error ("プレリュードの extern " ^ prim ^ " は再宣言できません")
  else if Hashtbl.mem externs o then type_error ("extern " ^ name ^ " が二重に宣言されています")
  else (
    Hashtbl.add externs o ();
    mark "extern" po)

(* ## 6.2b extern C 既知名の型契約

   §6.2 は「extern には照合すべき実体が処理系側に無い」と書きました。
   C リンケージの既知名 (sin/cos/sqrt/exp/log) だけは例外です。実装は
   第13章の `c_prims` 表として処理系が持っているので、照合すべき実体が
   **ある**。検証できない宣言は上書きを許さない、が §6.2 の格言なら、
   ここは続きです — **検証できる宣言は検証する**。

   かつては検査が無く、C 既知名 `sin` を String を取って String を返すと
   偽った宣言が型検査を通りました。呼ぶと「Float64 ではありません」という、
   ユーザには原因の見えない実行時エラーです
   (プレリュード保護は宣言済みの名前にしか効かず、
   sin はプレリュードが宣言できません — sample.kel:548 が自前で宣言するので、
   先に置くと再宣言拒否で仕様が落ちます)。

   契約で照合するのは**引数型と返り値型だけ**で、行は見ません。`@ Blocking`
   を付けるかどうかはバインディングの作者の判断だと仕様 (sample.kel:551) が
   明言しているからです。

   署名はここ (第6章)、実装は第13章、と 2 表に分かれます。elab (第11章)
   から第13章を参照すると章の前後が逆転するための配置で、二重管理の
   リスクは**安全側に縮退します**: 実装だけ足して署名を忘れれば検査が
   効かないだけ (= かつての状態)、署名だけ足して実装を忘れれば宣言は通り
   呼ぶと「未実装のプリミティブ」。どちらからも嘘の型は生まれません。 *)

let c_known_signatures : (string * (oid list * oid * string)) list =
  let f64 = Type.intern "Float64" in
  let f1 = ([ f64 ], f64, "(Float64) => Float64") in
  [ ("sin", f1); ("cos", f1); ("sqrt", f1); ("exp", f1); ("log", f1) ]

let c_known_signature name = List.assoc_opt name c_known_signatures

(* ## 6.3 型構成子のカインド表

   MiniLang の `conKinds` (:641) をそのまま持ってきた表です。第8章 (unify.ml)
   の `kind_of` は、型構成子に出会うとこの表を引き、適用された引数の数だけ
   矢印を落とします。**これがカインド検査の全部**で、専用のパスはありません。

   未知の構成子を `k_arrow nargs`(適用個数ぶんの `*` を取る形)で既定するのは
   MiniLang と同じです。宣言前の前方参照や、パス 1 の途中で引かれたときに、
   カインド不一致という誤ったエラーを出さないための保守的な既定です。 *)

let con_kinds : (oid, Type.kind) Hashtbl.t = Hashtbl.create 64

(* 未知の構成子は飽和形とみなす(MiniLang:641 と同じ既定) *)
let con_kind c nargs = match Hashtbl.find_opt con_kinds c with Some k -> k | None -> Type.k_arrow nargs

(* 組み込みスカラー型(Boolean/Int32/... は con_kinds にはあるが datas には
   無い)。newtype とエイリアスの両方の再宣言検査が引くので、ここに置く *)
let reserved_type_names : (oid, unit) Hashtbl.t = Hashtbl.create 8

(* ## 6.4 module 平坦化の同義語表と可視性台帳 (裁定 D21, D41-D43)

   Keleut の `module` は、v0 では**平坦化**として実装されています。
   第11章 (elab.ml) の `flatten_modules` が `module M` の中身を取り出し、
   型と let を `M.名前` へ改名してトップレベルに並べ直す。改名だけでは
   module の中からの非修飾参照(`newtype BigInt` を `let parse(...): BigInt`
   が参照する)が壊れるので、同義語表を張って `resolve_con` を通します。

   M16 からこの同義語は **module でスコープ**されています(D43)。
   `module_con_synonyms` の鍵は `(module 名, 非修飾名)` で、引けるのは
   「いまどの module の宣言を処理しているか」(`current_module`)が
   その module のときだけ。かつて同義語は大域 1 枚で、`module M {
   newtype List[A] = … }` と書くだけで**プレリュード自身の型検査が壊れ**、
   ユーザに非の無い `!  <prelude>:…: 未知の型` が出ました(M15 検証)。
   module の内部名は module の中でだけ意味を持つ — スコープを表の鍵に
   刻んだ形です。

   スコープの規則は型と値で**非対称**です。どちらも実測に基づく裁定です。

   - **型は module 内先勝ち(語彙的遮蔽)**: module の中では `(M, 名前)` を
     先に引き、無ければ大域へ。型の解決は表がそろってから始まるので
     宣言順に依存せず、実行時(インスタンス頭)も同じ規則で引けます。
   - **値は大域先勝ち + 衝突の禁止**: 値の解決は elab が宣言時点の環境、
     評価器が呼び出し時点の globals と、**別の時点の環境**を見るため、
     module 内名とトップレベル名が同名だと解決が食い違い得ます(M15 検証
     V12: 型検査と実行が別の実体を選び黙って別の値が返る)。そこで
     module 内の値名がユーザのトップレベル値名と同名になること自体を
     平坦化の時点で拒否します。禁止すれば「環境に無かったときだけ
     module スコープの同義語を引く」フォールバックが両解決器で一致します。

   コンパニオン型規則(sample.kel:580「モジュール名と同名の型は
   モジュール名自体で参照できる」)だけは大域の `con_synonyms` に残ります。
   `module BigInt` の `newtype BigInt` は `BigInt.BigInt` へ改名され、
   大域同義語 `BigInt` → `BigInt.BigInt` が張られる — 外から見えてよい
   非修飾名はコンパニオンだけ、という D43 の言い換えです。ただし
   **既存の型名とは衝突できません**。黙って張ると `module Foo` を 1 行
   足すだけでトップレベルやプレリュードの型 `Foo` が乗っ取られ、名目型の
   抽象が破れました(M16 検証 — プレリュード名なら処理系ごと壊れる)。
   トップレベル名との衝突は平坦化が、プレリュード名との衝突と登録本体は
   第11章のパス 1a が拒否・実行します(平坦化の時点ではプレリュードの
   宣言表がまだ空だから)。

   値の大域先勝ちには 1 つ含意があります: **プレリュード名も先にいる側**
   です。module 内で `__string_concat` と同名の let を宣言しても、module 内
   からの非修飾参照はプレリュードを指します(elab と評価器で一致)。自分の
   束縛は `M.名前` と修飾して参照してください。

   `con_hints` / `val_synonyms` は**診断専用**の候補列です。解決には
   使わず、スコープ外からの非修飾参照に「A.T か B.T と修飾してください」を
   出すためだけに引きます。黙って後勝ちする名前解決は D22(§6.7 の
   `op_index`)が既に否定した設計です。

   可視性(D41-D42)はこの隣の台帳に載ります。`value_visibility` /
   `con_visibility` は修飾名 → { 出身 module, pub } で、検査は module
   境界だけ(D41。Diktor は複数ファイルを 1 プログラムに連結するので、
   ファイル境界は見ません)。コンストラクタの可視性は所属 newtype の
   pub に従います(D42)。

   なお**この表を引くのは第11章だけではありません**。第14章 (interp.ml) が
   `type instance Add[BigInt]` の頭を解決するときも同じ表を通ります
   (260829-2b 健全性 6)。名前を oid に落とす経路が 2 つある以上、
   両方が同じ表を通らなければなりません。評価器側の `current_module` 相当は
   環境の `mod_scope`(閉包が出身 module を覚える)です。 *)
let current_module : string option ref = ref None

(* コンパニオンだけの大域同義語(D43)。候補列の形は D39 のまま *)
let con_synonyms : (oid, oid list) Hashtbl.t = Hashtbl.create 16

let add_con_synonym short qual =
  let prev = Option.value ~default:[] (Hashtbl.find_opt con_synonyms short) in
  if not (List.mem qual prev) then Hashtbl.replace con_synonyms short (prev @ [ qual ])

(* module スコープの同義語(D43)。(module 名, 非修飾名) → 修飾名 *)
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

(* 可視性台帳(D41-D42)。鍵は修飾名 *)
type visibility = { vis_module : string; vis_pub : bool }

let value_visibility : (oid, visibility) Hashtbl.t = Hashtbl.create 16

let con_visibility : (oid, visibility) Hashtbl.t = Hashtbl.create 16

(* 宣言ノードの oid → 出身 module。第11章の 4 パスと第14章の exec_decl が
   これで current_module / mod_scope を復元する。Tree.oid_of の最初の
   利用者(260829-3 課題 11) *)
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

(* ## 6.5 型エイリアス — 透過、非再帰、部分適用禁止

   表に置くのは精緻化済みの型ではなく**型式そのもの**なので、パラメータ
   制約 (`type P[A: Show]`) も使うたびに言及時に課されます (第11章 §11.5 の
   規則 3、M17 / D51)。

   エイリアスは**透過**です。表には elaborate 済みの型ではなく型式
   (`al_body`) をそのまま置き、使われるたびに第11章がその場で elaborate
   します(計画 §7.3)。理由は 2 つあります。展開のたびに新しい型変数が
   採れること、そして `al_kind`(`: Type` か `: EffectRow` か)によって
   同じ型式が型としてもエフェクト行としても展開されうることです。

   エイリアスには 2 つの禁止事項が付いています — **再帰しない**ことと、
   **部分適用できない**こと(計画 §2.1)。後者は MiniLang §0 の
   「規則 2: 部分適用できる型シノニムを入れない」と同じもので、
   理由も同じです。部分適用できるシノニムは実質的に型レベルλであり、
   それを許した瞬間に単一化が unitary でなくなり主要型を失います。

   > この線だけは越えないこと。越えた瞬間、mgu が一意でなくなる。 *)

(* ## 6.4b 構造照合 — 受理する前に、同じものかを確かめる(D35)

   「照合の上で受理」(乖離 4)の照合の実体です。かつては名前が一致する
   ことしか見ておらず、プレリュード所有名の再宣言は**宣言ごと黙って消えて**
   いました — 嘘のコンストラクタ集合の newtype、本体の違う型エイリアス、
   操作の型が違う effect、どれも exit 0・警告ゼロで受理され、以後は
   プレリュード側の定義だけが生きていました(260829-3 課題 5。9 通りの
   再現を実測)。「これが標準ライブラリの中身だ」と示す教材の宣言が、
   本物と食い違っていても誰も気づかない、ということです。

   照合するのは「Keleut のプログラムから**観測できるもの**」だけです。

   - newtype: コンストラクタ名の**集合**、各コンストラクタのフィールドの
     数・ラベル・型(α 同値)、型パラメータの個数とカインドと制約、
     `???`(不透明)かどうか。**コンストラクタの宣言順は照合しない** —
     Keleut にコンストラクタ序数は無く、順序は観測できません。
   - 型エイリアス: 種別(: Type / : EffectRow)、パラメータ、本体の型式
     (パラメータ名は位置で読み替える — `[A] = (A, A)` と `[B] = (B, B)`
     は同じ宣言)。
   - effect: 操作名の集合と、各操作のスキーマ(α 同値)。
   - type class: パラメータのカインド、`derive structural` の有無、
     **メソッド名集合の完全一致**と各メソッド型(α 同値)。従来の
     「部分集合は許す」は撤回しました — 宣言は部分的な記述ではなく完全な
     記述である、が newtype / effect と揃う読み方です(D35)。
   - インスタンス: キー一致のみ(本体は第11章が独立に検査します)。
   - extern: 照合せず拒否のまま(§6.2 — 照合すべき実体が処理系側に無い)。

   型の比較は α 同値です。Generic 変数は**双方向の全単射**で対応づけ、
   行はラベルごとに列を分けて突き合わせます(同一ラベル内の順序は保ち、
   異なるラベル間の順序は無視 — Scoped Labels、D5)。カインドは**純粋な**
   `kind_equiv` で比べます — `same_kind` は KVar を破壊的に張るので、
   照合に使うと宣言の順序で結果が変わってしまいます。 *)

let rec kind_equiv a b =
  match (Type.kind_repr a, Type.kind_repr b) with
  | Type.KStar, Type.KStar | Type.KRow, Type.KRow -> true
  | Type.KArrow (a1, a2), Type.KArrow (b1, b2) -> kind_equiv a1 b1 && kind_equiv a2 b2
  | Type.KVar _, Type.KVar _ -> true (* 未確定どうしは同型とみなす(張らない) *)
  | _ -> false

(* α 同値。m / rev は Generic / Unbound 変数の vid の双方向対応で、
   宣言単位で共有する(同じパラメータは全フィールドで同じ相手に写る) *)
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
       また空行どうしになって無限再帰する(実装時に踏んだ罠) *)
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

(* パラメータを位置で対応づけて全単射の種にする。個数・カインド・制約も
   ここで照合する *)
let params_match (prev_ps : Type.var_info list) (info_ps : Type.var_info list) m rev =
  List.length prev_ps = List.length info_ps
  && List.for_all2
       (fun (pa : Type.var_info) (pb : Type.var_info) ->
         Hashtbl.replace m pa.Type.vid pb.Type.vid;
         Hashtbl.replace rev pb.Type.vid pa.Type.vid;
         kind_equiv pa.Type.vkind pb.Type.vkind && List.sort compare pa.Type.vcls = List.sort compare pb.Type.vcls)
       prev_ps info_ps

(* 型式(source)の比較。エイリアス本体は精緻化済みの型を持たないので、
   span を無視して構文を再帰する。パラメータ名は位置対応の表で読み替える。

   読み替えは**全単射**でなければならない(ty_equiv_with の m / rev と同じ)。
   片方向の連想だけだと、宣言側のパラメータ名が相手側の自由な型名を捕獲する
   — プレリュードの `type Cap[A] = (A, G)` に対しユーザの
   `type Cap[G] = (G, G)` が「同じ宣言」と誤判定され、しかも表の実体は
   プレリュード側のままなので、ユーザは自分の宣言が捨てられたことを
   知らされない(M15 検証)。`na` が読み替え表に無いときは、`nb` が
   **どの読み替えの像でもない**ことまで確かめてから素の名前比較に落とす。

   行とヴァリアントと制約は**順序を見ない**(ty_equiv_with がラベルで
   揃えるのと同じ規律)。構文のまま List.for_all2 で突き合わせると
   `{x: Int32, y: String}` と `{y: String, x: Int32}` — 型としては同一
   (相互代入が型検査を通ることを実測)— を「本体が違います」で誤って
   拒否する(M15 検証)。ラベルで安定ソートしてから比べる。同名ラベルの
   重なりは相対順を保つので、遮蔽の順序はちゃんと照合に残る *)
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
  (* 行要素の並べ替え鍵。prev 側(第1引数)はラベルを読み替えてから比べる
     ことで、両側が同じ座標系に乗る *)
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
  al_kind : string option; (* : Type / : EffectRow *)
  al_body : T.type_exp;
  (* 本体は**宣言スコープ**で展開する(D43)。module 内のエイリアスが
     内部型を指しているとき、外から展開しても壊れないように、展開時は
     この module を current_module に立てる。引数は使用スコープのまま *)
  al_module : string option;
}

let aliases : (oid, alias_info) Hashtbl.t = Hashtbl.create 64

let add_alias info =
  (* 組み込みスカラー名はエイリアスでも奪えない(V2。newtype 側と同じ検査。
     type Float64 = String が通ると、C 既知名の契約照合が名前照合ゆえに
     自己矛盾した診断を出す) *)
  if Hashtbl.mem reserved_type_names info.al_name && not !in_prelude then
    type_error ("組み込み型 " ^ Type.name_of info.al_name ^ " は型エイリアスで再宣言できません")
  else claim_type_name "型エイリアス" info.al_name;
  if Hashtbl.mem aliases info.al_name then
    if not (prelude_owned "alias" info.al_name) then
      type_error ("型エイリアス " ^ Type.name_of info.al_name ^ " が二重に宣言されています")
    else (
      note_user_redecl "alias" info.al_name "型エイリアス";
      (* 照合の上で受理(D35)。表の実体は差し替えない *)
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

(* ## 6.6 データ宣言表と、予約型名 — 敵対的検証で塞いだ穴 (2)

   名目的データ型の表です。型言語そのものは変わりません(データ型は `TCon`
   ひとつで表され、増えるのはこの表だけ)。MiniLang §3 と同じ構えです。

   フィールド型に現れるパラメータは **Generic マーク**で置いてあります。
   使うときは `dd_params` の各 `vid` に新しい変数を割り当てて
   `subst_params` する — インスタンス化と同じ機構です。

   3 つ、目を留めるところがあります。

   ### コンストラクタ名は大域一意

   `ctor_owner` は ctor 名からデータ型名への逆引きで、登録時に重複を拒否
   します。ラベルなしのコンストラクタ適用や裸のコンストラクタ参照
   (`None` のような引数ゼロの ctor)を名前だけで解決するための前提です。

   ### `dd_ctors = []` には 2 つの意味がある

   `dd_opaque` が真なら `newtype X = ???`(未実装のホール、あるいは
   `Ref` / `Array` のような組み込み不透明型)。偽なら **`Never`**、つまり
   コンストラクタがゼロ個であることが確定した型です。第10章 (exhaust.ml) の
   `complete_sig` はこれを `Some []` と答え、**節がゼロの `match` が
   網羅と判定される**。MiniLang:1721(アルゴリズム I。同じ式が U 側の
   :1756 にもあります)は `roots.nonEmpty`、つまり「根が空でない」ことを
   完全性の条件に含めていますが、その条件だと `Never` の節ゼロ `match` が
   誤って非網羅になるため、本実装では修正してあります(実装記録の乖離 9)。

   ### 予約型名 — 「表に無い」は「空いている」ではない

   `Boolean` / `Int32` / `Int64` / `Float64` / `String` は `con_kinds` には
   載りますが、`datas` には載りません。組み込みスカラーにはコンストラクタが
   無いので、データ宣言を作る意味がないからです。

   その**不在**が穴でした。敵対的検証で `newtype Boolean = Yes` を書いたら、
   `Hashtbl.mem datas` の二重宣言検査を素通りして新しいデータ型として登録され、
   網羅性検査と組み込みインスタンスの両方が破綻しました。第10章は Boolean を
   「ctor `Yes` だけを持つ型」と見るようになり、`Eq[Boolean]` の組み込み
   インスタンスは別物の型に付いたままになります。

   対策が `reserved_type_names` です。ここに載っている名前は、
   プレリュード処理中でない限り `newtype` で再宣言できません。

   `Never` がこの表に**入っていない**のは正しい設計です。`Never` は
   §6.12 で ctor ゼロのデータ宣言として `datas` に登録されるので、
   sample.kel が `Never` を宣言し直しても、通常の「プレリュード所有だから
   照合の上で受理」の経路にそのまま乗ります。表に載っている型は表の規則で、
   表に載らない型は別の表で守る。

   > 表に載っていないことは、空いていることを意味しない。 *)

type field_info = { fi_label : oid option; fi_ty : Type.ty (* パラメータは Generic マーク *) }

type ctor_info = { ct_name : oid; ct_fields : field_info list }

type data_info = {
  dd_name : oid;
  dd_params : Type.var_info list; (* Generic 変数の情報(vid で subst_params する) *)
  dd_ctors : ctor_info list; (* Never は [] *)
  dd_opaque : bool; (* newtype X = ??? *)
}

let datas : (oid, data_info) Hashtbl.t = Hashtbl.create 64

let ctor_owner : (oid, oid) Hashtbl.t = Hashtbl.create 128 (* ctor 名 → data 名 *)

(* newtype の構造照合(D35)。観測できるもの — コンストラクタ名の集合、
   フィールドの数・ラベル・型、パラメータ、不透明かどうか — を突き合わせ、
   宣言順は照合しない *)
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

(* ## 6.7 エフェクト表と操作の索引 (裁定 D22)

   エフェクト宣言は「非修飾の操作名 → 操作スキーマ」の並びです。
   スキーマは Generic 化済みの `TArrow(引数行, 返り値, ρ)` で、
   クラスメソッドとまったく同じ形をしています(§6.10)。

   内部表現では操作は**常に完全名**、つまり `Console.write` を intern した
   oid です。第5章 (tree.ml) の `ROp` に入るのもこの完全名でした。
   では非修飾で書かれた `perform write(x)` はどう完全名になるのか
   — それを支えるのが `op_index` です。

   ### なぜ「操作名は大域一意」にできなかったか

   素朴な裁定は「操作名は大域一意」でしたが、**sample.kel 自身がそれを
   破っています**。`Console.write` (:342) と `File.write` (:397) の両方が
   宣言されている。仕様が破っている規則は規則ではありません。

   そこで D22 は重複宣言を許し、`op_index` に「非修飾 op 名 → 宣言順の
   所属エフェクト列」を持たせました。`add_effect` が `prev @ [ ef_name ]`
   と末尾に足しているのは、この列の順序が宣言順であることを保つためです。

   ### 選ぶのは表ではなく、その地点のエフェクト行

   MiniLang の `lookupOp` (:1261-1264) は候補の先頭を採ります。これは
   **移植しません**。宣言順に依存した誤解決になるからです。

   本実装では、候補が複数あるとき第11章はその地点の**エフェクト行の最左**
   に現れる候補を採ります。当初の計画は「明示ラベルにあるものを優先」でしたが、
   sample.kel:415 の `copy` — `File` と `Console` の両方が行に載っている
   文脈で :418 が `write` を呼ぶ — がそれでは曖昧になり、最左優先まで
   精密化しました(実装記録の乖離 3)。最左は Scoped Labels の最左一致とも、
   実行時に最も内側のハンドラが捕まえることとも一致します。**型検査が選ぶ操作と、
   実行時に捕まえるハンドラが、同じ規則で決まる**わけです。

   したがってこの表の宣言順が最終的な選択を決めることはありません。
   順序が表に出るのは、行に候補が 1 つも無くて「`E.op` と修飾してください」
   と案内するときの、候補の並べ方だけです。 *)

type effect_info = {
  ef_name : oid;
  ef_ops : (oid * Type.ty) list; (* 非修飾 op 名 → スキーマ TArrow(引数行, 返り値, ρ)(Generic 化済み) *)
}

let effects : (oid, effect_info) Hashtbl.t = Hashtbl.create 32

(* D22: 操作名の重複宣言を許す(sample.kel 自身が Console.write と File.write を宣言)。
   非修飾 op 名 → 宣言順の所属エフェクト列 *)
let op_index : (oid, oid list) Hashtbl.t = Hashtbl.create 64

let add_effect info =
  (* 組み込みスカラー名は effect でも奪えず(V2 と同じ検査)、型名の
     名前空間も newtype / エイリアスと共有する(effect List は List の
     再宣言。§6.1b) *)
  if Hashtbl.mem reserved_type_names info.ef_name && not !in_prelude then
    type_error ("組み込み型 " ^ Type.name_of info.ef_name ^ " は effect で再宣言できません")
  else claim_type_name "effect" info.ef_name;
  if Hashtbl.mem effects info.ef_name then (
    if not (prelude_owned "effect" info.ef_name) then
      type_error ("effect " ^ Type.name_of info.ef_name ^ " が二重に宣言されています")
    else (
      note_user_redecl "effect" info.ef_name "effect";
      (* 照合の上で受理(D35): 操作名の集合と各スキーマの α 同値 *)
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

   1 パラメータ型クラスなので、表の構造は MiniLang §2 とほぼ同じです。
   Keleut 固有のフィールドが 3 つあります。

   - `ci_param` — クラスパラメータの Generic 変数の情報。全メソッドが
     **同じ変数**を共有します。これがインスタンス検査の代入点で、
     頭型を 1 回代入すればクラス内の全メソッドの型が同時に具体化されます。
   - `ci_derive_structural` — `derive structural` (sample.kel:302)。
     真なら、閉じた行の `TRecord` / `TVariant` に対して制約をフィールドへ
     再帰させます。v0 では `Eq` だけが真です。**閉じた行にしか適用しない**
     のは仕様どおりで (sample.kel:305-309)、行変数を含む型を比較できるように
     するには点ごとの行制約 `[R: Eq]` が要り、カインドと制約解決に手が
     入るからです。
   - `ci_builtin` — この表のエントリが組み込みかどうか。§6.1 で述べた
     「プレリュード所有」の、クラス版の表し方です。

   `add_class_decl` が 3 通りの結果を返すのは、呼び出し側に判断を返すためです。

   | 結果 | 意味 | 第11章がすること |
   |---|---|---|
   | `` `Added `` | 新規 | 宣言したメソッドをそのまま使う |
   | `` `Builtin prev `` | 組み込みと同名・**構造照合済み** | 型は組み込み側を使う |
   | 例外 | ユーザ同士の重複 / 照合不一致 | 拒否 |

   照合の中身は §6.4b の D35 のとおりです — パラメータのカインド、derive の
   有無、**メソッド名集合の完全一致**、各メソッド型の α 同値。かつては
   「組み込みに無いメソッドを足していないか」の一方向・部分集合の確認だけで、
   sample.kel の `Add` が組み込みと一致していることは読者が目で確かめる
   前提でした。いまは処理系が確かめます。 *)

type class_info = {
  ci_name : oid;
  ci_param : Type.var_info; (* クラスパラメータの Generic 変数(インスタンス検査の代入点) *)
  ci_param_kind : Type.kind;
  ci_derive_structural : bool;
  ci_builtin : bool;
  ci_methods : (string * Type.ty) list; (* メソッド名 → Generic マーク済みスキーマ *)
}

let classes : (oid, class_info) Hashtbl.t = Hashtbl.create 64

let find_class c = Hashtbl.find_opt classes c

(* 組み込みと同名のユーザ宣言は「照合の上で受理」(実体は組み込みのまま)。
   sample.kel 自身がプレリュード相当の Add 等を宣言するため(計画 §7.4 の運用裁定) *)
let add_class_decl info =
  match Hashtbl.find_opt classes info.ci_name with
  | Some prev when prev.ci_builtin ->
      (* 照合の上で受理(D35)。従来は「組み込みに無いメソッドを足して
         いないか」の一方向・部分集合の照合(第11章)だったが、完全一致に
         締めて第6章に一本化した *)
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

(* ## 6.9 インスタンス表とコヒーレンス — 敵対的検証で塞いだ穴 (3)

   キーは (クラス, 型構成子の頭) の oid ペアです。`Functor[List[_]]` でも
   キーになるのは `List` という頭の名前だけで、適用個数はカインドが決めます
   (MiniLang:274-277)。頭に書かれた穴 `_` はカインド検査にしか使いません。
   **だからインスタンス探索は表引き 1 回**で終わります。

   `ii_premises` は「引数位置 → その位置に要求するクラス」で、第8章
   (unify.ml) の制約伝播が読みます。`Show[List[_]]` のようなもの — `List[A]`
   が `Show` であるには `A` が `Show` であること — を表すための欄です。

   **ただし v0 には、前提つきのインスタンスが 1 つも登録されていません。**
   `add_instance` を呼ぶ場所はリポジトリ全体で 2 箇所しかなく、組み込み側
   (§6.12) もユーザ宣言側(第11章の `register_instance`)も、前提には必ず
   空リストを渡します。組み込みの `Show` が付いているのも `String` /
   `Boolean` / `Int32` / `Int64` / `Float64` だけで、`List` は入りません。
   つまり伝播の側は動くのに、流れるものがまだ無い。**器だけが先に入って
   いる**状態です。器を先に置いたのは、前提を足す日に伝播の呼び出し点を
   探し直すより安いからで、教材としては「未実装をどこまで先取りするか」の
   一例として読んでください。

   コヒーレンスの規則は sample.kel:276 が言うとおり、
   **重複キーを拒否する。それだけ**です。インスタンスは常に大域可視で、
   隠すことも選び直すこともできません。

   ### 実体を差し替えないことを、両側で守る

   `add_instance` の 1 番目の分岐 — 組み込みが既にあり、来たのがユーザ宣言 —
   は、何もせずに返ります。ユーザの本体は第11章が普通に型検査しますが、
   表に残るのは組み込みのままです。「受理するが採用しない」の実装です。

   敵対的検証はここに穴を見つけました。**第14章 (interp.ml) が同じ規則を
   守っていなかった**のです。`type instance Add[Int32]` を再宣言すると、
   elab は組み込みを使い続けるのに実行時のディスパッチ表だけがユーザ本体に
   差し替わり、`2 + 3` が `-1` を返しました。

   型検査が「組み込みの `Add[Int32]` を使う」と決めた式が、実行時には
   別の実装に飛ぶ。これはコヒーレンスの破れであると同時に、第5章で述べた
   「elab と interp の二重実装がドリフトする」の実例でもあります。

   対策が `builtin_instance_exists` です。第14章はインスタンス宣言を評価する
   前にこの関数へ問い合わせ、組み込みキーなら実体を差し替えません。
   規則をもう一度書き直すのではなく、**規則を持っている側に聞きに行く**形に
   したのが要点です。

   > 「受理するが採用しない」と決めたら、採用しないことを全員に守らせる。 *)

type instance_info = {
  ii_premises : (int * oid) list; (* 引数位置 → 要求クラス *)
  ii_builtin : bool;
  ii_methods : (oid * T.let_binding) list; (* ユーザ宣言のメソッド本体(interp のディスパッチ用) *)
}

let instances : (oid * oid, instance_info) Hashtbl.t = Hashtbl.create 256

(* 組み込みキーを再宣言したユーザ宣言の記録。「受理するが採用しない」
   (乖離 4)は 1 回まで — 2 回目は普通のコヒーレンス違反として拒否する。
   これが無いと「同じキーを 2 度登録したらエラー」が組み込みキーだけ
   嘘になる(敵対的検証の指摘) *)
let builtin_redecls : (oid * oid, unit) Hashtbl.t = Hashtbl.create 16

(* 予約述語(D8)の名前表。規則を持つのはこの表 1 枚で、クラス宣言側
   (第11章 register_class)とインスタンス宣言側(下の add_instance)の
   両方がここを引く。登録は §6.12 の register_builtins *)
let reserved_predicates : (oid, unit) Hashtbl.t = Hashtbl.create 4
let reserved_predicate c = Hashtbl.mem reserved_predicates c

(* コヒーレンス: 重複キーを拒否。それだけ(sample.kel:276)。
   組み込みと同じキーのユーザ宣言は照合の上で受理する(本体は検査される) *)
let add_instance ?(builtin = true) ?(methods = []) ~cls ~con premises =
  (* 予約述語はインスタンス側の入口でも拒否する(§6.12)。免除は「組み込み
     登録であること」(builtin = true) — 組み込み登録自身が Integral[Int32] /
     Fractional[Float64] をここから入れるため。当初は in_prelude を免除に
     していたが、それだと --prelude で差し替えたユーザ製プレリュードまで
     免除され、迂回路になった(敵対的検証で実測) *)
  (if reserved_predicate cls && not builtin then
     type_error (Type.name_of cls ^ " は予約されたリテラル述語です(インスタンスは宣言できません、D8)"));
  match Hashtbl.find_opt instances (cls, con) with
  | Some prev when prev.ii_builtin && not builtin ->
      (* 実体は組み込みのまま。ユーザ本体は検査済みという扱い(1 回まで) *)
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

(* ## 6.10 組み込み登録の道具立て

   ここから下は、ソースに書けない — あるいは書かせたくない — 宣言を
   このファイルが直接表へ入れる部分です。

   `generic` が作るのは **Generic マークの型変数**、つまり
   「量化されている」ことを表す印です。型スキーマ用の別データ型を持たず、
   変数の状態 1 つで多相を表すのは MiniLang §1.3 と同じ設計で、
   `vlevel` は Generic では使われません。

   `closed_args_row` は引数リストを `_item` ラベルの**閉じた行**に畳みます。
   Keleut の引数列は「タプル = `_item` の連なり」というレコードなので、
   矢印の引数側はいつもこの形です。閉じているのは、引数の個数が
   呼び出しで確定しなければならないからです。

   メソッドのスキーマは §6.12 の `arrow1` / `arrow2` がその場で書きます。
   要点は 2 つ — **省略された `@` は Generic 行変数になる**こと
   (sample.kel:315-316。閉じた行だったらクラスメソッドに純粋な関数しか
   渡せず、高階関数が使い物になりません)と、**クラスパラメータ変数は
   クラス内で共有する**こと(§6.12 の代入点)。かつて arity を取る一般形
   `method_scheme` がここにありましたが、消しました(C10)— 呼び出し元が
   1 つも無く、しかもパラメータ変数を**自分で作る**設計だったので、
   共有の規約と噛み合いませんでした。抽象化が要求と食い違うなら、
   その場に 2 行書くほうが正確です。 *)

(* 登録用の Generic 変数(vlevel は Generic では使われない) *)
let generic ?(kind = Type.KStar) ?(classes = []) () =
  Type.TVar (ref (Type.Generic { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes }))

let closed_args_row tys =
  List.fold_right (fun t acc -> Type.TRowExtend (Type.l_item, t, acc)) tys Type.TRowEmpty

let intern = Type.intern

(* ## 6.11 Ref / Array と、リージョンの行

   `Ref` と `Array` の操作は、このファイルが直接登録します(計画 §11.2)。
   置き場所の理由は「extern 宣言の**束縛子側**に `Heap[h]` の `h` を導入
   する構文が無い」ことでした。正確を期すと、型パラメータ `[h]` を持つ
   extern 署名として同じ型を**書くこと自体はできます**(M20 検証で実測 —
   脱出検査も効く)。組み込みに残しているのは、実装が OCaml 側の値
   (§14.11)と分かちがたく、プレリュードに置くと二重管理になるからです
   (§15.1 の基準)。

   ### 行を開いておくこと

   `heap_row h` は `Heap[h]` を**開いた Generic 尾部**の上に載せます。
   これは MiniLang の `newref` と同じ形で、理由も同じです。閉じた行
   — ちょうど `Heap[h]` だけ — にしてしまうと、`Console` の下でも
   `Async` の下でも `Ref.get` が呼べなくなります。プログラムのほとんどは
   何かのエフェクトの下で走るので、閉じた瞬間にこの操作は使えなくなります。

   ### `Ref` はリージョンを覚え、`Array` は覚えない

   `Ref.new` の返り型は `Ref[h, A]` で、リージョン変数 `h` が**値の型に
   現れます**。だから `run` の外へ持ち出そうとすると、第8章の脱出検査
   (剛定数がスコープの外に漏れている)が捕まえます。Haskell の `ST` と同じ
   仕掛けで、MiniLang §17 の「同じ形が 3 回出てくる」の 1 つです。

   `Array.new` は `Heap[h]` を要求するのに、返り型は `Array[A]` で `h` を
   持ちません。**したがって `run` の中で作った配列は外へ持ち出せてしまいます。**
   これは実装の手抜きではなく仕様側の穴で、計画 §11.2 と計画 §12 に記録し、
   親リポジトリへのフィードバック事項に挙げてあります。教材としては
   「型に現れない情報はスコープ検査が守れない」ことの実例です。

   > リージョンは型に現れているぶんだけしか守れない。

   `Array.each` の行 `e` がコールバックと呼び出し全体で共有されているのは、
   高階関数がエフェクト多相であるための最小の形です。ここを別々の変数に
   すると、`each` にエフェクトを起こす関数を渡せなくなります。 *)

let builtin_ops : (string * Type.ty) list ref = ref []

let register_ref_array () =
  let ref_oid = intern "Ref" and arr_oid = intern "Array" in
  Hashtbl.replace con_kinds ref_oid (Type.k_arrow 2);
  Hashtbl.replace con_kinds arr_oid (Type.k_arrow 1);
  let ginfo () = { Type.vid = new_oid (); vlevel = 0; vkind = Type.KStar; vcls = [] } in
  add_data { dd_name = ref_oid; dd_params = [ ginfo (); ginfo () ]; dd_ctors = []; dd_opaque = true };
  add_data { dd_name = arr_oid; dd_params = [ ginfo () ]; dd_ctors = []; dd_opaque = true };
  (* 操作なしの組み込みエフェクトラベル *)
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
  (* Array は h を持たない(計画 §11.2)。この穴 — 引数を破壊する関数が
     純粋として型付く — は test/spec_gaps.t がゴールデンとして見張り、
     仕様への対案(Array / MutArray 分離)は doc/log/260830-1-m20.md に
     ある(M20 / I1 / D64) *)
  (let h = generic () and a = generic () in
   def "Array.new" (arrow [ Type.t_int32; a ] (Type.TCon (arr_oid, [ a ])) (heap_row h)));
  (let a = generic () in
   def "Array.length" (arrow [ Type.TCon (arr_oid, [ a ]) ] Type.t_int32 (generic ~kind:Type.KRow ())));
  (let h = generic () and a = generic () in
   def "Array.get" (arrow [ Type.TCon (arr_oid, [ a ]); Type.t_int32 ] a (heap_row h)));
  (let h = generic () and a = generic () in
   def "Array.set" (arrow [ Type.TCon (arr_oid, [ a ]); Type.t_int32; a ] Type.t_unit (heap_row h)));
  (let a = generic () and e = generic ~kind:Type.KRow () in
   (* Array.each に Heap を課す一貫性修正(I12)は M20 検証で**撤回**した。
      each はコールバックの行と自分の行を共有する(エフェクト多相の最小形)
      ため、Heap を課すと共有経由でコールバック側にも課され、明示的に
      純粋な @ {} の関数が渡せなくなる(実測 — run の内側でも落ちた)。
      行を分けて自分の行だけに課す形も、@ {} コールバックが結果行を
      閉じて同じ失敗になる。全要素を読む par_map が Heap 不要のままで
      ある以上、表の一貫性も得られない。読みの純粋性の扱いは
      Array / MutArray 分離(D64、260830-1)で一括裁定する *)
   def "Array.each" (arrow [ Type.TCon (arr_oid, [ a ]); arrow [ a ] Type.t_unit e ] Type.t_unit e))

(* ## 6.11b par / par_map — 型は書けるが値が書けない組(H2 / D45)

   Ref / Array は「ソースに書ける構文では型が付けられない」ので組み込みに
   なりました。`par` / `par_map` は**逆**です。型は下のとおり Keleut の
   構文で書けますが、**値が Keleut ソースで書けない**ことが実測で確定して
   います(計画 §10 H2)。理由はサブエフェクティングの不在(§11.26 /
   計画 §12)で、決定的なものが 2 つ:

   - `(fa(), fb())` を本体に書くと、その行が `@ {}` に固まり、トップレベル
     (行 {Console, Async})から呼べない —「ラベル Console がありません」。
   - `run h { … }` で書くと Heap[h] の立った文脈で `@ {}` の f を呼ぶ
     ことになり「ラベル Heap がありません」。

   だから Ref / Array と同じ組み込み登録にします(型はここ、値は §14.11 —
   apply が第14章にあるので、実装は第13章にも置けません)。

   型の要点は 2 つです。**コールバックの行は閉じた空行**(TRowEmpty)。
   仕様 (sample.kel:477) の決定性保証 —「並列性は純粋な計算に限る」— は、
   純粋であることの証明をここで要求し続けることに乗っています。そして
   **外側の行は Generic の行変数**。TRowEmpty にするとトップレベルから
   呼べない関数になります(実測済みの罠)。 *)
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
  (* pinned : [A, E] (() => A @ {Blocking extends E}) => A @ E(H11)。
     Blocking は操作を持たない組み込みラベル(§6.11)なので、それを落とす
     のは純粋に型の上の行為 — run が実行時に恒等写像である(§14.4)のと
     同じ構図がもう一度出る。トップレベルからは直接呼べる(仕様 §9 /
     §12、D88。かつてはトップレベル行に Blocking が無く pinned が必須
     だった)。pinned は、より内側の — 行を注釈で閉じた — 文脈へ
     持ち込むために要る *)
  (let a = generic () and e = generic ~kind:Type.KRow () in
   def "pinned" (arrow [ arrow [] a (Type.TRowExtend (Type.eff_blocking, Type.t_unit, e)) ] a e))

(* ## 6.12 組み込みのクラスと数値インスタンス

   演算子が呼ぶクラス群(第7章 (prims.ml) の表の右辺)を、ここで直接
   登録します。プレリュード相当をソースで書かずに OCaml 側に置いたのは、
   これらが「実装がプリミティブにしかない」層だからです。

   最初の 3 行が大事です。`in_prelude` を立てて登録し、`Fun.protect` で
   必ず戻す。**組み込み登録をプレリュード扱いにする**ことで、sample.kel が
   `Add` や `Add[Int32]` を宣言し直しても §6.1 の経路に乗ります。
   例外で抜けてもフラグが戻ることを `Fun.protect` が保証しており、
   ここが漏れると以後のユーザ宣言が全部「プレリュード所有」になって、
   二重宣言検査が丸ごと効かなくなります。

   `def_class` はクラスパラメータの Generic 変数 `pinfo` を 1 つ作り、
   それを全メソッドで共有します(§6.8 の代入点)。クラスの分け方は
   sample.kel:285 の言うとおりで、`Num` にまとめないのは
   **`String` のように `+` だけを持つ型がある**からです。だから `Add` の
   インスタンスにだけ String が入り、`Sub` / `Mul` / `Div` には入りません。
   `Ord` に Boolean が入っていないのは、真偽値に大小を決めていないからです。

   `Integral` / `Fractional` は裁定 D8 の**予約述語**です。メソッドを持たない
   クラスとしてこの表に相乗りさせているだけで、専用の機構は何も足していません。
   「型変数に貼りつく制約集合」が既にあるので、リテラルの型を絞る仕掛けを
   別に作らずに済みます。`1 + x` で `{Integral, Add}` の 2 つが同じ変数に
   乗るときの挙動が自動的に正しくなる、というのが D8 の理由です。既定化は
   一般化の直前に走るので、通常はこの述語が表示に出ることはありません。

   予約は**宣言の 3 つの入口すべて**で効かせます。同名の**クラス宣言**は
   第11章の `register_class` が、**インスタンス宣言**は第11章の
   `register_instance` の頭と §6.9 の `add_instance` の両方が、
   **型パラメータ制約**(`[A: Integral]` と書く形)は第11章の
   `class_names_of` が拒否します。どの検査も §6.9 の `reserved_predicates`
   表を引きます。ただし予約述語の**意味論**(リテラル既定化でどう扱うか)は
   第8章 (unify.ml) が第1章の定数で別に持っています — この表は入口の番人で
   あって、意味の持ち主ではありません。

   かつてはクラス宣言側にしか検査が無く、`type instance Integral[String]` と
   書けば表に載って `[A: Integral]` の制約解決に本当に使われました。メソッドが
   0 個なので網羅も過剰も何も言わず、素通りだったのです。制約の入口も
   別途開いていて、`let f[A: Integral](): A = 1` は型検査を通ってから実行時に
   「数値リテラルの型が解決されていません」で落ちました。予約述語が汚染
   できるとリテラル既定化 (D8) の前提が崩れるので、入口の全部に検査を
   置きました。インスタンス側の検査の免除条件は「組み込み登録であること」
   (`builtin = true`。この関数の下の組み込み登録自身が `Integral[Int32]` /
   `Fractional[Float64]` を入れるため)です。当初は `in_prelude` を免除に
   していましたが、それだと --prelude で差し替えたユーザ製プレリュードまで
   免除されてしまい、迂回路になりました(敵対的検証で実測)。

   > 名前を予約したつもりでも、予約したのは入口の一部だけだった。数えて
   > 塞いだつもりの入口も、免除条件が広ければやはり開いている。

   最後の `Never` の登録が §6.6 で述べた ctor ゼロのデータ宣言です。 *)

let register_builtins () =
  (* 組み込み登録はプレリュード扱いにする(同名のユーザ宣言を照合の上で受理) *)
  let saved = !in_prelude in
  in_prelude := true;
  Fun.protect ~finally:(fun () -> in_prelude := saved) @@ fun () ->
  (* 組み込み型(D13: 実行できる幅は3種。他の名前の受理と拒否は elab が行う) *)
  List.iter
    (fun n -> Hashtbl.replace con_kinds (intern n) Type.KStar)
    [ "Boolean"; "Int32"; "Int64"; "Float64"; "String"; "Never" ];
  List.iter (fun n -> Hashtbl.replace reserved_type_names (intern n) ())
    [ "Boolean"; "Int32"; "Int64"; "Float64"; "String" ];
  let numerics = [ "Int32"; "Int64"; "Float64" ] in
  (* クラスとメソッド(sample.kel:286-320 のプレリュード相当を decls 直登録。M4)。
     クラスパラメータ変数はクラス内で共有する(インスタンス検査の代入点、M7) *)
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
  (* 予約述語(D8)。メソッドなしのクラスとして表に相乗りさせる *)
  List.iter (fun n -> Hashtbl.replace reserved_predicates (intern n) ()) [ "Integral"; "Fractional" ];
  def_class "Integral" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Int32"; "Int64" ];
  def_class "Fractional" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Float64" ];
  (* Never は ctor ゼロのデータ宣言(complete_sig が Some [] を返し、節ゼロの match が網羅になる) *)
  add_data { dd_name = intern "Never"; dd_params = []; dd_ctors = []; dd_opaque = false };
  builtin_ops := [];
  register_ref_array ();
  register_parallel ()

(* ## 6.13 値環境への流し込みと、表の初期化

   `builtin_values` は、クラスメソッドを**ただの多相定数**として値環境に
   並べます。型クラスのメソッドに特別な扱いは要りません — 型は
   「クラス制約つきの Generic 変数を含む多相型」で、探索は普通の変数参照、
   実装の選択は第14章の実行時タグディスパッチ(裁定 D3)。

   非修飾名 `add` と修飾名 `Add.add` の**両方**を登録します
   (実装記録の乖離 12)。sample.kel はメソッドをどちらの形でも参照するので、
   環境に 2 つ入れるのが最も安い実装でした。

   `reset` は**再入する API のため**にあります(C11 / D40)。CLI は
   1 プロセス 1 プログラムなので呼びません。呼ぶのは第16章の
   `type_check_string` / `eval_string` — 同一プロセスで繰り返し呼ばれる
   想定の API で、宣言表が残っていると 2 回目が同じプログラムでも
   「二重に宣言されています」で落ちます(かつて reset には呼び出し元が
   1 つも無く、まさにそうなっていました)。順序は
   **reset → 平坦化 → 型検査** — 逆にすると平坦化が張った同義語が
   消えます。ここに 1 枚書き忘れると、**単体では通るのに他のテストと
   一緒に走らせると落ちるテスト**という、最も追いにくい種類の不具合に
   なります。表を足したら `reset` にも足す — このファイルを触るときの
   不変条件です。なお `Type.intern` の oid 表は戻しません — 長時間走る
   API では oid が単調に増えますが、実害はありません。

   末尾の副作用付き初期化 `let () = register_builtins ()` は、表がモジュールの
   状態であることの代償です。第16章 (driver.ml) が何かする前に、
   組み込みはもう表に載っています。 *)

let builtin_values () =
  Hashtbl.fold
    (fun _ ci acc ->
      List.fold_left
        (fun acc (m, ty) -> (m, ty) :: (Type.name_of ci.ci_name ^ "." ^ m, ty) :: acc)
        acc ci.ci_methods)
    classes []
  @ !builtin_ops

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
