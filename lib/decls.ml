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

(* ## 6.4 module 平坦化の同義語表 (裁定 D21)

   Keleut の `module` は、v0 では**平坦化**として実装されています。
   第11章 (elab.ml) の `flatten_modules` が `module M` の中身を取り出し、
   型と let を `M.名前` へ改名してトップレベルに並べ直す。それだけです。
   名前空間も可視性も導入しません。

   改名だけでは、モジュールの中から内側の型を非修飾で参照している箇所
   (`newtype BigInt` を `let parse(...): BigInt` が参照する)が壊れます。
   そこで改名と同時に「非修飾名 → 正準の修飾名」の同義語を張り、
   型構成子を引くところは必ず `resolve_con` を通す、という形にしました。

   この同義語表 1 枚で、**仕様のコンパニオン型規則が自動的に出る**のが
   気持ちのよいところです。sample.kel:580 は「モジュール名と同名の型は
   モジュール名自体で参照できる」と述べています。`module BigInt` の中の
   `newtype BigInt` は `BigInt.BigInt` に改名され、同義語 `BigInt` →
   `BigInt.BigInt` が張られる。したがってモジュール名 `BigInt` を型の位置に
   書くと、そのままコンパニオン型に解決されます。規則を別途実装していません。

   **代償も正直に書いておきます。** 同義語は大域なので、コンパニオンでない
   内部型の非修飾名も外から見えてしまいます。可視性 (`pub`) の検査を v0 で
   延期している(計画 §2.1 と計画 §13)以上、これは今のところ検出されません。
   module の入れ子と module 内 let の相互参照も未対応です(実装記録の乖離 5)。

   なお**この表を引くのは第11章だけではありません**。敵対的検証で、
   第14章 (interp.ml) が `type instance Add[BigInt]` の頭を解決するときに
   同義語を通しておらず、module 内のインスタンスが実行時に見つからない、
   という欠陥が見つかりました。名前を oid に落とす経路が 2 つある以上、
   両方が同じ表を通らなければなりません。 *)
let con_synonyms : (oid, oid) Hashtbl.t = Hashtbl.create 16

let resolve_con c = match Hashtbl.find_opt con_synonyms c with Some c' -> c' | None -> c

(* ## 6.5 型エイリアス — 透過、非再帰、部分適用禁止

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

type alias_info = {
  al_name : oid;
  al_params : type_param list;
  al_kind : string option; (* : Type / : EffectRow *)
  al_body : T.type_exp;
}

let aliases : (oid, alias_info) Hashtbl.t = Hashtbl.create 64

let add_alias info =
  if Hashtbl.mem aliases info.al_name then (
    if not (prelude_owned "alias" info.al_name) then
      type_error ("型エイリアス " ^ Type.name_of info.al_name ^ " が二重に宣言されています"))
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

(* 組み込みスカラー型(Boolean/Int32/... は con_kinds にはあるが datas には無い) *)
let reserved_type_names : (oid, unit) Hashtbl.t = Hashtbl.create 8

let add_data info =
  if Hashtbl.mem reserved_type_names info.dd_name && not !in_prelude then
    type_error ("組み込み型 " ^ Type.name_of info.dd_name ^ " は newtype で再宣言できません")
  else if Hashtbl.mem datas info.dd_name then (
    if not (prelude_owned "data" info.dd_name) then
      type_error ("newtype " ^ Type.name_of info.dd_name ^ " が二重に宣言されています"))
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
  if Hashtbl.mem effects info.ef_name then (
    if not (prelude_owned "effect" info.ef_name) then
      type_error ("effect " ^ Type.name_of info.ef_name ^ " が二重に宣言されています"))
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
   | `` `Builtin prev `` | 組み込みと同名 | **メソッド名を照合**し、型は組み込み側を使う |
   | 例外 | ユーザ同士の重複 | 拒否 |

   ここでの「照合」の中身は、組み込みに無いメソッドを足していないかの確認
   までです。メソッド型が組み込みと同型かまでは見ていません — sample.kel が
   書いている `Add` の形が組み込みと一致していることは、教材としては
   読者が目で確かめる前提になっています。 *)

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
  | Some prev when prev.ci_builtin -> `Builtin prev
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

   `Ref` と `Array` の操作は、ソースに書ける構文では型が付けられません。
   エフェクトのパラメータ(`Heap[h]` の `h`)を宣言する構文が v0 に無いから
   です。そこでこのファイルが直接登録します(計画 §11.2)。

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
  (* Array は h を持たない(計画 §11.2。既知の穴も計画 §12 に記録済み) *)
  (let h = generic () and a = generic () in
   def "Array.new" (arrow [ Type.t_int32; a ] (Type.TCon (arr_oid, [ a ])) (heap_row h)));
  (let a = generic () in
   def "Array.length" (arrow [ Type.TCon (arr_oid, [ a ]) ] Type.t_int32 (generic ~kind:Type.KRow ())));
  (let h = generic () and a = generic () in
   def "Array.get" (arrow [ Type.TCon (arr_oid, [ a ]); Type.t_int32 ] a (heap_row h)));
  (let h = generic () and a = generic () in
   def "Array.set" (arrow [ Type.TCon (arr_oid, [ a ]); Type.t_int32; a ] Type.t_unit (heap_row h)));
  (let a = generic () and e = generic ~kind:Type.KRow () in
   def "Array.each" (arrow [ Type.TCon (arr_oid, [ a ]); arrow [ a ] Type.t_unit e ] Type.t_unit e))

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
  register_ref_array ()

(* ## 6.13 値環境への流し込みと、表の初期化

   `builtin_values` は、クラスメソッドを**ただの多相定数**として値環境に
   並べます。型クラスのメソッドに特別な扱いは要りません — 型は
   「クラス制約つきの Generic 変数を含む多相型」で、探索は普通の変数参照、
   実装の選択は第14章の実行時タグディスパッチ(裁定 D3)。

   非修飾名 `add` と修飾名 `Add.add` の**両方**を登録します
   (実装記録の乖離 12)。sample.kel はメソッドをどちらの形でも参照するので、
   環境に 2 つ入れるのが最も安い実装でした。

   `reset` はテストのためにあります。ひとつのプロセスで複数の `.kel` を
   検査するとき、前のプログラムの宣言が残っていると結果が実行順に依存します。
   ここに 1 枚書き忘れると、**単体では通るのに他のテストと一緒に走らせると
   落ちるテスト**という、最も追いにくい種類の不具合になります。
   表を足したら `reset` にも足す — このファイルを触るときの不変条件です。

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
  Hashtbl.reset reserved_type_names;
  Hashtbl.reset reserved_predicates;
  Hashtbl.reset externs;
  in_prelude := false;
  register_builtins ()

let () = register_builtins ()
