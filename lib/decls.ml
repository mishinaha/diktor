(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第6章 宣言環境

   型検査の処理は 2 つに分かれる。
   1 つは型どうしを単一化する処理で、第8章(unify.ml)が担当する。
   もう 1 つは、名前が何を指すかを決める処理である。
   型構成子、型エイリアス、コンストラクタ、エフェクト、操作、型クラスの名前は、
   本章の宣言表を引いて解決する。
   変数と、スコープにある型パラメータの型は、第11章(elab.ml)の環境が持つ。

   宣言表は、たとえば次の問い合わせに答える。

   - `List[A]` の `List` がどのカインドの型構成子か
   - `IoError` がエイリアスとエフェクト名のどちらか
   - `Some` がどのデータ型のコンストラクタで、そのフィールドがどう並ぶか
   - `write` がどのエフェクトの操作か
   - `Add` がどんなメソッドを持ち、`Int32` がそのインスタンスかどうか

   主な表は次の 8 つである。

   | 表 | キー | 値 | 主に読む章 |
   |---|---|---|---|
   | `con_kinds` | 型構成子 | カインド | 第8章(`kind_of`) |
   | `con_synonyms` | コンパニオン型の非修飾名 | 修飾名の候補 | 第11章、第14章 |
   | `aliases` | エイリアス名 | パラメータと本体 | 第11章(透過的な展開) |
   | `datas` / `ctor_owner` | 型名 / コンストラクタ名 | コンストラクタとフィールド / 型名 | 第10章、第11章 |
   | `effects` / `op_index` | エフェクト名 / 操作名 | 操作の型スキーム / エフェクトの候補 | 第11章 |
   | `classes` | クラス名 | パラメータとメソッド | 第8章、第11章、第14章 |
   | `instances` | (クラス, 型構成子) | 前提 | 第8章、第11章、第14章 |
   | `externs` | extern 名 | なし(登録済みであることだけを表す) | 第11章 |

   第5章(tree.ml)で述べたとおり、評価器は名前解決をやり直さないので、
   第14章(interp.ml)には読む表と読まない表がある。
   データ型とコンストラクタは、精緻化のときに `RCtor` / `RCtorPat` へ書き込んであるので、
   評価器は `datas` / `ctor_owner` を引かない。
   一方、メソッドの実装は、型検査が木に書いた証拠の辞書から実行時に選ぶので(第14章 §14.6)、
   `classes` と `instances` は評価器も読む。

   上に挙げた表は、どれもグローバルな可変ハッシュ表である。
   そのため、インスタンスの探索もカインドの取得も、表を 1 回引くだけで終わる。
   その代わり、処理系の状態がグローバルにあるので `reset` が必要で、
   2 つのプログラムを同時には検査できない。
   同じプロセスで複数のプログラムを検査する API(第16章の `type_check_string` / `eval_string`)では、
   `reset` がすべての表を初期状態に戻すので、前の呼び出しの宣言が次の呼び出しに残らない(§6.13)。

   ## 標準環境の名前の再宣言

   宣言表は、同じ名前の 2 回目の宣言を拒否する。
   そのときの診断は、先にあった宣言が標準環境のものかユーザのものかで分ける。
   プレリュードか組み込みの登録(§6.12)が先に登録した型エイリアス、newtype、effect と、
   組み込みの登録が先に登録した type class とインスタンスについて(起点でない単位のクラスの扱いは §6.1)、
   同じ種別の宣言をユーザが書いたときは、
   `標準環境の … は再宣言できません` で拒否する(仕様 sample.kel:237、:375、:467、:807)。
   種別の違う宣言は、型の名前空間(§6.1 の `type_namespace`)が `既に … として宣言されています` で拒否する。
   `extern` の再宣言は、§6.2 の登録表が別のメッセージで拒否する。
   ユーザの宣言どうしの重複は、`二重に宣言されています` で拒否する。
   診断を `再宣言できません` と `二重に宣言されています` に分けるのは、
   名前を変えるべきか、自分の重複を消すべきかを、ユーザが診断から判断できるようにするためである。
   標準環境の宣言は、ユーザの宣言を登録する時点で保護されるので、
   第14章(interp.ml)の側で実装の差し替えを防ぐ処理は不要である。

   ## 前章から受け取るもの

   第5章(tree.ml)の `Tree.Tree` と、第1章(syntax.ml)の内部型 `Type.ty` を使う。
   `Tree.Tree` は、型の式を表に格納するために使う。

   ## 次章へ渡すもの

   第8章(unify.ml)以降の章が、名前の問い合わせ先として本章の表を引く。
   間にある第7章(prims.ml)は本章を参照せず、第1章(syntax.ml)の `bin_op` だけを使う。
   本章が登録するクラスも、第7章はクラス名の文字列でしか扱わない。 *)
open Aux
open Syntax
module T = Tree.Tree

(* ## 6.1 プレリュードが登録した名前の記録

   診断を `再宣言できません` と `二重に宣言されています` に分けるには、
   表の各項目を登録したのがプレリュードかユーザかを区別できなければならない。
   その区別を持つのが `prelude_keys` である。

   第11章(elab.ml)は、プレリュードを処理する間だけ `in_prelude` を立てる。
   組み込みの登録(§6.12)も、同じフラグを立てて実行する。
   `mark` は、フラグが立っている間に登録された `(表の種別, 名前)` の組だけを `prelude_keys` に記録する。
   後から同じ名前の宣言が来たときは、`prelude_owned` がこの記録を引き、
   どちらの診断を出すかを決める。

   キーに表の種別を含めるのは、`extern` の `foo` と型エイリアスの `foo` が別のものだからである。
   名前だけをキーにすると、片方の登録が、もう片方の再宣言を黙って許してしまう。

   クラスとインスタンスでは、診断を分けるのに `prelude_keys` を使わない。
   クラス表とインスタンス表の項目が持つフラグ `ci_builtin` / `ii_builtin`(§6.8、§6.9)を使う。
   このフラグは、本章の `register_builtins`(§6.12)が登録した項目であることを表す。
   プレリュードが宣言した項目であることは表さない。
   第11章は、プレリュードが宣言したクラスとインスタンスも、フラグを偽にして登録する。
   したがって、プレリュードが宣言したクラスやインスタンスと同じ名前やキーをユーザが宣言すると、
   `二重に宣言されています` で拒否する。
   たとえば、プレリュードの `Show[List[_]]` をユーザが宣言し直すと、
   コヒーレンス違反の診断になる。
   ただし、起点でない単位のクラスは内部名に接頭辞が付くので(§6.4)、
   接頭辞のない同名のクラスが表にあれば、
   フラグによらず `標準環境の type class … は再宣言できません` で拒否する(§6.8 の `add_class_decl`)。 *)
let in_prelude = ref false

let prelude_keys : (string * oid, unit) Hashtbl.t = Hashtbl.create 64

let mark kind name = if !in_prelude then Hashtbl.replace prelude_keys (kind, name) ()

let prelude_owned kind name = Hashtbl.mem prelude_keys (kind, name)

(* 型名の名前空間は 1 つで、newtype、型エイリアス、effect がこの名前空間を共有する。
   一方、二重宣言の検査は種別ごとの表に分かれている。
   そのため、種別ごとの検査だけでは、種別を変えた再宣言がどの検査にもかからない。
   たとえば `type List[A] = Int32` は、aliases 表では初めての名前なので検査に通り、
   それ以降の `List[X]` がすべて Int32 を意味することになる。
   そうなると、プレリュードの List は、値は作れるのに型名を書けない型になってしまう。
   `prelude_keys` の説明では、名前だけをキーにすると片方の登録がもう片方の再宣言を黙って許すと述べた。
   名前空間を共有する型名では、逆に、種別ごとに表を分けたことが同じ問題を起こす。
   そこで、名前を先に登録した種別をこの表に記録し、別の種別での再宣言を登録の時点で拒否する *)
let type_namespace : (oid, string) Hashtbl.t = Hashtbl.create 64

let claim_type_name kind name =
  match Hashtbl.find_opt type_namespace name with
  | Some prev_kind when prev_kind <> kind ->
      type_error (Type.display_of name ^ " は既に " ^ prev_kind ^ " として宣言されています(" ^ kind ^ " では再宣言できません)")
  | _ -> Hashtbl.replace type_namespace name kind

(* ## 6.2 extern の登録表

   `extern` はプリミティブに型を与える宣言である。
   実装は第13章(builtin.ml)の表にあり、型はプレリュードの `extern` 宣言が与える。
   処理系は、`extern` の型注釈が実装と合っているかどうかを検査できない。

   そのため、プリミティブの再宣言を許すと型システムが壊れる。
   許した場合、たとえば `__int32_add` の引数型を String と偽る宣言が型検査に通る。
   ところが第13章の実装は Int32 を前提にしているので、
   実行時には Int32 用の実装に String の値が渡る。
   型システム全体がプリミティブの型注釈を信頼しているので、上書きを許すわけにはいかない。

   extern の登録表は、登録済みの名前の再宣言を拒否する。
   プレリュードが登録した名前なら `再宣言できません`、
   ユーザが登録した名前なら `二重に宣言されています` で拒否する。
   標準環境の newtype、型エイリアス、effect、クラス、
   インスタンスの再宣言を拒否するのと同じ扱いである。

   登録表が保護するのは、プレリュードが宣言した名前だけである。
   実装表にあるのに宣言のない名前は登録表に載らないので、
   ユーザが偽の型で宣言すれば、その実装を呼び出せてしまう。
   この漏れをなくすために、プレリュードは実装表のすべての名前に型を与える(第15章 §15.5 の不変条件)。

   ただし `--no-prelude` のときは登録表が空になり、すべてのプリミティブを再宣言できる。
   宣言の欠けたプレリュードを `--prelude` で与えたときは、
   そのプレリュードが宣言しなかった名前を再宣言できる。
   どちらの場合も、型と実装が合っていることは、
   オプションを指定したユーザ(処理系の開発者)が保証する。

   登録表は 2 種類のキーを使い分ける。
   プレリュードの保護は、非修飾の実装名(第1章の `ex_prim`)で調べる。
   module 内の `extern` は Keleut 側の名前が `M.f` に修飾されるので、
   修飾名で調べると、module の中で宣言すればプレリュードの保護にかからなくなる。
   二重宣言の検査は、修飾名で調べる。
   実装名までグローバルに一意にすると、
   `module Fast` と `module Precise` が同じ C のシンボル `sqrt` を
   それぞれの名前で束縛する正当なプログラムが書けなくなる。 *)
let externs : (oid, unit) Hashtbl.t = Hashtbl.create 64

let add_extern ~unit ~prim name =
  (* 二重宣言のキーは、宣言した単位と Keleut 側の名前の組である。値の名前には単位の接頭辞が付かない
     (§6.4)ので、別々のファイルにある同名の extern を区別するために単位を加える *)
  let o = Type.intern (if unit > 0 then "%" ^ string_of_int unit ^ "." ^ name else name) in
  let po = Type.intern prim in
  (* プレリュードの保護は実装名(非修飾の prim)で、二重宣言は Keleut 側の名前(修飾名)で調べる。
     キーを使い分ける理由は §6.2 で述べた *)
  if prelude_owned "extern" po then type_error ("プレリュードの extern " ^ prim ^ " は再宣言できません")
  else if Hashtbl.mem externs o then type_error ("extern " ^ Type.display name ^ " が二重に宣言されています")
  else (
    Hashtbl.add externs o ();
    mark "extern" po)

(* ## 6.2b C の既知名のシグネチャ

   §6.2 では、処理系は `extern` の型注釈が実装と合っているかどうかを検査できないと述べた。
   C リンケージの既知名(sin / cos / sqrt / exp / log)だけは例外である。
   これらの実装は第13章の `c_prims` 表として処理系が持っているので、宣言の型を照合できる。
   そこで第11章は、C の既知名を束縛する extern 宣言の型を、
   本章のシグネチャ `c_known_signatures` と照合する。

   照合しないと、C の既知名 `sin` が String を取って String を返すと偽った宣言が型検査に通る。
   その関数を呼ぶと、`Float64 ではありません` という、ユーザには原因の分からない実行時エラーになる。
   §6.2 のプレリュードの保護では、この宣言を防げない。
   保護されるのはプレリュードが宣言した名前だけで、sin はプレリュードで宣言できないからである。
   sample.kel:795 が sin を自分で宣言するので、プレリュードが先に宣言すると、
   sample.kel の検査が再宣言の拒否でエラーになる。

   シグネチャとの照合で調べるのは引数型と返り値型だけで、エフェクト行は調べない。
   C リンケージの `extern` で `@` を省略すると、`@ Blocking` と読む。
   行変数を明示すれば呼び出し元の行を伝える型に、`@ {}` と書けば純粋な型にもできる。
   どれを選ぶかは、仕様(sample.kel:798-799)がバインディングの作者に委ねている。

   シグネチャは本章、実装は第13章と、2 つの表に分かれる。
   シグネチャを本章に置くのは、第11章(elab.ml)から第13章を参照すると章の順序が逆転するからである。
   2 つの表は、同じ名前の集合(sin / cos / sqrt / exp / log)を持つように保つ。
   実装だけを追加してシグネチャを忘れると、その名前の宣言は、
   表にない名前と同じく照合されずに受理され、
   型を偽った宣言でも実装が呼ばれる。
   シグネチャだけを追加して実装を忘れると、宣言は検査に通り、
   呼ぶと `未実装のプリミティブ` の実行時エラーになる。 *)

let c_known_signatures : (string * (oid list * oid * string)) list =
  let f64 = Type.intern "Float64" in
  let f1 = ([ f64 ], f64, "(Float64) => Float64") in
  [ ("sin", f1); ("cos", f1); ("sqrt", f1); ("exp", f1); ("log", f1) ]

let c_known_signature name = List.assoc_opt name c_known_signatures

(* ## 6.3 型構成子のカインド表

   第8章(unify.ml)の `kind_of` は、型構成子に出会うとこの表を引き、
   適用された引数の個数だけカインドの矢印を取り除く。
   Diktor は、カインド検査だけを行う走査のパスを持たない。
   カインドは、この表と、精緻化のときに行う型引数の照合で決まる(§8.1)。

   `con_kind` は、表にない構成子のカインドを `k_arrow nargs` とみなす。
   これは、適用した引数の個数だけ `*` を取るカインドである。
   前方参照のときや、パス 1 の途中で表を引いたときに、
   カインドの不一致という誤ったエラーを出さないための、保守的な既定である。

   この表は、パラメータのカインドも保持する。
   newtype の型構成子には、第11章のパス 1a が、
   パラメータごとにカインド変数を置いたカインドを登録する。
   パス 1b の `register_newtype` は、そのカインドの矢印を取り除き、
   引数の側のセルを `dd_params` の `vkind` に入れる。
   セルを共有しているので、本体での使われ方で決まったカインドは、この表のカインドにも現れる。 *)

let con_kinds : (oid, Type.kind) Hashtbl.t = Hashtbl.create 64

(* 表にない構成子は、適用した引数の個数だけ引数を取る構成子とみなす *)
let con_kind c nargs = match Hashtbl.find_opt con_kinds c with Some k -> k | None -> Type.k_arrow nargs

(* 組み込みスカラー型の名前の表。Boolean / Int32 などは con_kinds にはあるが datas にはない。
   newtype、エイリアス、effect の再宣言の検査がどれも引くので、ここに置く *)
let reserved_type_names : (oid, unit) Hashtbl.t = Hashtbl.create 8

(* 起点でない単位の宣言の名前には単位の接頭辞が付くので、標準環境の宣言と表のキーが重ならない。
   そこで、接頭辞を取り除いた名前で標準環境の型の名前空間を引き、起点の宣言と同じ診断で拒否する。
   起点より前に処理する単位から見て、接頭辞のない名前は標準環境のものだけである *)
let check_std_type_twin kind name =
  let s = Type.name_of name in
  let dn = Type.display s in
  if dn <> s then (
    let d = Type.intern dn in
    (* メッセージは起点の宣言の診断とそろえる。型エイリアスだけは種別名の前後に空白を置かない *)
    let sp = if kind = "型エイリアス" then "" else " " in
    if Hashtbl.mem reserved_type_names d then
      type_error ("組み込み型 " ^ dn ^ " は" ^ sp ^ kind ^ sp ^ "で再宣言できません");
    match Hashtbl.find_opt type_namespace d with
    | Some prev when prev <> kind ->
        type_error (dn ^ " は既に " ^ prev ^ " として宣言されています(" ^ kind ^ " では再宣言できません)")
    | Some _ -> type_error ("標準環境の" ^ sp ^ kind ^ " " ^ dn ^ " は再宣言できません")
    | None -> ())

(* ## 6.4 module の平坦化のための別名表と可視性の表

   Diktor は、Keleut の `module` を平坦化して実装する。
   第11章(elab.ml)の `flatten_modules` が `module M` の内容を取り出し、
   型と let の名前を `M.名前` に変えて、トップレベルに並べ直す。
   名前を変えただけでは、module の中からの非修飾の参照が解決できなくなる。
   たとえば module 内の `let parse(...): BigInt` の `BigInt` は、
   名前の変わった `newtype BigInt` を指せなくなる。
   そこで、非修飾名から修飾名を引く別名表を作り、型の名前は `resolve_con` を通して引く。
   エフェクト行の位置に書いた EffectRow エイリアスの名前も、`resolve_con` を通して引く。
   ただし、module の中の同名の宣言が、行にならない Type エイリアスや newtype のときは、
   `resolve_con_global` でグローバルな名前を引き直す(第11章 §11.6)。

   module の内部の名前は module の中でだけ意味を持つので、別名も module ごとのスコープを持つ。
   `module_con_synonyms` のキーは `(module 名, 非修飾名)` で、
   現在処理している宣言の module(`current_module`)がその module のときだけ引ける。
   別名をグローバルな 1 つの表に置くと、`module M { newtype List[A] = … }` と書くだけで、
   プレリュードの中の `List` までこの module の型を指してしまう。
   その結果、プレリュード自身の型検査が失敗し、
   ユーザに落ち度のない `未知の型` のエラーが `<prelude>` の位置で出る。

   スコープの規則は、型と値で異なる。

   - **型は module 内を先に引く**：module の中では `(M, 名前)` を先に引き、
     なければグローバルな名前を引く。
     module の中の型が、外側の同名の型を隠す(シャドーイング)。
     型の解決は表が出そろってから始まるので、宣言の順序に依存しない。
     評価器が実行時にインスタンスの対象の型を解決するときも、同じ規則で引ける。
   - **値はグローバルな名前を先に引き、衝突を禁止する**：elab は値の名前をまず型検査の環境で引き、
     なかったときだけ module スコープの別名を引く。
     値の名前を解決するのは elab だけで、評価器は elab が木に書いた参照先を使う(第14章 §14.4)。
     平坦化は、module 内の値の名前がユーザのトップレベルの値の名前と同じになる宣言を拒否する。
     この禁止は言語の規則であり、elab と評価器の名前解決を一致させるための実装の制約ではない。

   **コンパニオン型**：module と同名の型で、module 名だけで参照できる(sample.kel:848)。
   コンパニオン型の別名だけは、グローバルな `con_synonyms` に登録する。
   `module BigInt` の中の `newtype BigInt` は名前が `BigInt.BigInt` に変わり、
   グローバルな別名 `BigInt` → `BigInt.BigInt` が登録される。
   module の外から非修飾で見えてよい型名は、コンパニオン型だけである。
   ただし、コンパニオン型の名前は、既存の型名ともエフェクト名とも衝突してはならない。
   黙って別名を登録すると、`module Foo` を 1 行追加するだけで、
   トップレベルやプレリュードの型 `Foo` が別の型に置き換わり、名目的な型の抽象化が破られる。
   プレリュードの名前が置き換わると、処理系そのものが正しく動かなくなる。
   トップレベルの名前との衝突は、平坦化が拒否する。
   プレリュードの名前との衝突の拒否と、グローバルな別名の登録は、第11章のパス 1a が行う。
   平坦化の時点では、プレリュードの宣言表がまだ空だからである。

   値はグローバルな名前を先に引くので、プレリュードの名前も module の中の名前より先に引かれる。
   そのため、module 内で `__string_concat` と同名の let を宣言しても、
   module 内からの非修飾の参照はプレリュードの `__string_concat` を指す。
   評価器は elab が解決した参照先を使うので(第14章 §14.4)、型検査と評価器の解決は一致する。
   module 内の自分の束縛を参照するには、`M.名前` と修飾する。

   `con_hints` / `val_synonyms` は、診断だけに使う候補の表である。
   名前の解決には使わず、スコープの外からの非修飾の参照に `A.T か B.T と修飾してください` と
   案内するためだけに引く。
   後から宣言したものを黙って優先する名前解決は、§6.7 の `op_index` と同じ理由で採用しない。

   可視性は、別名表とは別の表に記録する。
   `value_visibility` / `con_visibility` は、修飾名から、
   宣言した module と pub の有無を引く表である。
   可視性の検査は module の境界でだけ行う。
   Diktor は複数のファイルを 1 つのプログラムに連結するので、ファイルの境界は調べない。
   コンストラクタの可視性は、所属する newtype の pub に従う。

   別名表を引くのは第11章だけではない。
   第14章(interp.ml)も、`type instance Add[BigInt]` の対象の型を解決するときに同じ表を引く。
   名前を oid に変換する経路が 2 つあるので、両方が同じ表を引かないと、
   型検査と実行で名前の指す宣言が食い違う。
   第14章は、宣言した module を `decl_module` から引き、`current_module` に設定してから解決する。
   値の名前は、第11章が解決した参照先を木に書くので、第14章は別名表を引かない。

   **単位**：プログラムは単位(ソースファイル)の集まりである。
   コマンド行で渡したファイル群は起点の単位(0)で、
   標準環境(プレリュードと組み込み)は単位 -1 として扱う。
   それ以外の単位は、宣言の名前に単位の接頭辞を付けて区別する。
   起点でない単位の型、コンストラクタ、エフェクト、クラス、module の名前は、
   `%3.T` のように、先頭に `%` と単位の番号と `.` を付けた内部名で intern する。
   `%` は識別子に現れない文字である。
   module の中の宣言は `%3.M.T` になる。
   型が同じかどうかは内部名で決まるので、接頭辞を付けた宣言は、本章の表でも、型の単一化でも、
   実行時のインスタンスの選択でも、別の単位にある同名の宣言と別のものになる。
   トップレベルの値の名前には接頭辞を付けない。
   値は、第11章が解決した参照先(束縛ノードの oid)で区別される。
   module の値は、接頭辞の付いた module 名で始まる内部名(`%3.M.x`)になる。

   起点と標準環境の名前には接頭辞を付けない。
   単位は依存される側から順に処理するので、起点でない単位を検査する時点では、
   起点の宣言はまだ表にない。
   したがって、起点でない単位から見て、接頭辞のない名前は標準環境のものだけである。
   レコードとヴァリアントのラベルと、`op_index` のキーである非修飾の操作名にも、接頭辞を付けない。
   ラベルは構造的な型の構成要素で、単位をまたいで単一化できなければならない。

   名前から宣言を引く処理は、単位の別名表を通る。
   `unit_synonyms`(型の名前空間)、`unit_ctors`(コンストラクタ)、`unit_classes`(クラス)は、
   (単位, 接頭辞のない名前)から内部名を引く。
   型とコンストラクタは同じ名前を持てるので、表を分ける。
   `unit_qualifiers` は、修飾名 `M.x` の先頭にある module 名かクラス名を、
   内部名に置き換えるための表である。
   `resolve_con` は、module スコープの別名、単位の別名、グローバルな別名の順に引く。
   `op_candidates` は、`op_index` の候補を、現在の単位から見えるエフェクトに絞る。
   現在の単位は、`with_decl_scope` が、宣言した単位の記録(`decl_unit`)から設定する。
   接頭辞を取り除いた表示名は第1章の `Type.display` が返し、型の表示と診断はそれを使う。 *)
let current_module : string option ref = ref None

(* 単位の番号。起点は 0、標準環境は -1 で、import した単位には 1 から番号を振る。
   起点でない単位の型、コンストラクタ、エフェクト、クラス、module の名前は、
   先頭に接頭辞 %N. を付けて intern する *)
type unit_id = int

let root_unit = 0

let std_unit = -1

let current_unit : unit_id ref = ref root_unit

(* 単位の番号 → 表示用のパス *)
let unit_paths : (unit_id, string) Hashtbl.t = Hashtbl.create 8

(* 宣言ノードの oid → その宣言が属する単位 *)
let decl_unit : (oid, unit_id) Hashtbl.t = Hashtbl.create 64

(* 単位の別名。(単位, 非修飾名) → 内部名。型の名前空間(型、型エイリアス、エフェクト)、
   コンストラクタ、クラスで表を分ける。型とコンストラクタは同じ名前を持てるからである *)
let unit_synonyms : (unit_id * oid, oid) Hashtbl.t = Hashtbl.create 16

let unit_ctors : (unit_id * oid, oid) Hashtbl.t = Hashtbl.create 16

let unit_classes : (unit_id * oid, oid) Hashtbl.t = Hashtbl.create 16

(* 修飾名の先頭の要素。(単位, module 名かクラス名) → 内部名 *)
let unit_qualifiers : (unit_id * string, string) Hashtbl.t = Hashtbl.create 16

let marks_unit u = u > root_unit

let mark_spelling u name = if marks_unit u then "%" ^ string_of_int u ^ "." ^ name else name

(* 内部名の接頭辞から単位を求める。接頭辞のない名前は None *)
let unit_of_spelling name =
  if String.length name > 1 && name.[0] = '%' then
    match String.index_opt name '.' with
    | Some i -> int_of_string_opt (String.sub name 1 (i - 1))
    | None -> None
  else None

let resolve_in tbl c = match Hashtbl.find_opt tbl (!current_unit, c) with Some q -> q | None -> c

let resolve_unit c = resolve_in unit_synonyms c

let resolve_ctor c = resolve_in unit_ctors c

let resolve_class c = resolve_in unit_classes c

(* 修飾名 M.x の先頭の要素を、現在の単位での内部名に置き換える *)
let qualify name =
  if String.length name > 0 && name.[0] = '%' then name
  else
    match String.index_opt name '.' with
    | Some i -> (
        match Hashtbl.find_opt unit_qualifiers (!current_unit, String.sub name 0 i) with
        | Some h -> h ^ String.sub name i (String.length name - i)
        | None -> name)
    | None -> name

(* 現在の単位から見える宣言なら真を返す。
   接頭辞のない名前は標準環境か起点のもので、どの単位からも見える。
   ただし、起点より前に処理する単位を検査する時点では、起点の宣言はまだ表にない。
   接頭辞の付いた名前は、現在の単位の別名が指しているものだけが見える *)
let visible_in_unit tbl oid =
  let name = Type.name_of oid in
  match unit_of_spelling name with
  | None -> true
  | Some _ -> Hashtbl.find_opt tbl (!current_unit, Type.intern (Type.display name)) = Some oid

(* コンパニオン型だけを登録するグローバルな別名表。値は候補のリストで、
   resolve_con は候補が 1 つのときだけ使う *)
let con_synonyms : (oid, oid list) Hashtbl.t = Hashtbl.create 16

let add_con_synonym short qual =
  let prev = Option.value ~default:[] (Hashtbl.find_opt con_synonyms short) in
  if not (List.mem qual prev) then Hashtbl.replace con_synonyms short (prev @ [ qual ])

(* module スコープの別名。(module 名, 非修飾名) → 修飾名 *)
let module_con_synonyms : (string * oid, oid) Hashtbl.t = Hashtbl.create 16

let module_val_synonyms : (string * oid, oid) Hashtbl.t = Hashtbl.create 16

(* module スコープを飛ばし、単位の別名とグローバルな別名(コンパニオン型)をたどる。
   エフェクト位置の名前の解決(第11章 §11.6)は、module の中の同名の宣言が行にならないときに、
   `resolve_con_global` でグローバルな名前を引き直す *)
let resolve_con_global_only c = match Hashtbl.find_opt con_synonyms c with Some [ c' ] -> c' | _ -> c

let resolve_con_global c =
  let c = Type.intern (qualify (Type.name_of c)) in
  match Hashtbl.find_opt unit_synonyms (!current_unit, c) with Some q -> q | None -> resolve_con_global_only c

let resolve_con c =
  let c = Type.intern (qualify (Type.name_of c)) in
  match !current_module with
  | Some m -> ( match Hashtbl.find_opt module_con_synonyms (m, c) with Some q -> q | None -> resolve_con_global c)
  | None -> resolve_con_global c

(* 診断だけに使う候補の表。名前の解決には使わない *)
let con_hints : (oid, oid list) Hashtbl.t = Hashtbl.create 16

let add_con_hint short qual =
  let prev = Option.value ~default:[] (Hashtbl.find_opt con_hints short) in
  if not (List.mem qual prev) then Hashtbl.replace con_hints short (prev @ [ qual ])

(* 案内する候補は、現在の単位から見える module のものに限る。別の単位の module を案内すると、
   そのとおりに修飾しても名前が見つからない *)
let here q = match unit_of_spelling (Type.name_of q) with None -> true | Some u -> u = !current_unit

let con_synonym_candidates c = List.filter here (Option.value ~default:[] (Hashtbl.find_opt con_hints c))

let val_synonyms : (oid, oid list) Hashtbl.t = Hashtbl.create 16

let add_val_synonym short qual =
  let prev = Option.value ~default:[] (Hashtbl.find_opt val_synonyms short) in
  if not (List.mem qual prev) then Hashtbl.replace val_synonyms short (prev @ [ qual ])

let val_synonym_candidates short = List.filter here (Option.value ~default:[] (Hashtbl.find_opt val_synonyms short))

(* 可視性の表。キーは修飾名 *)
type visibility = { vis_module : string; vis_pub : bool }

let value_visibility : (oid, visibility) Hashtbl.t = Hashtbl.create 16

let con_visibility : (oid, visibility) Hashtbl.t = Hashtbl.create 16

(* 宣言ノードの oid(Tree.oid_of で取り出す)→ その宣言が属する module。
   第11章の 4 つのパスと第14章の exec_decl が、この表から current_module を復元する *)
let decl_module : (oid, string) Hashtbl.t = Hashtbl.create 16

(* 宣言ノードが属する module と単位を current_module と current_unit に設定して f を呼び、
   f が終わったら元の値に戻す。単位の記録がない宣言は起点のものとして扱う *)
let with_decl_scope oid f =
  let cm = !current_module and cu = !current_unit in
  current_module := Hashtbl.find_opt decl_module oid;
  current_unit := Option.value ~default:root_unit (Hashtbl.find_opt decl_unit oid);
  Fun.protect
    ~finally:(fun () ->
      current_module := cm;
      current_unit := cu)
    f

let visible_here (v : visibility) = v.vis_pub || !current_module = Some v.vis_module

let check_con_visible oid =
  match Hashtbl.find_opt con_visibility oid with
  | Some v when not (visible_here v) ->
      type_error ("型 " ^ Type.display_of oid ^ " は module " ^ Type.display v.vis_module ^ " の外からは参照できません(pub を付けてください)")
  | _ -> ()

let check_value_visible oid =
  match Hashtbl.find_opt value_visibility oid with
  | Some v when not (visible_here v) ->
      type_error (Type.display_of oid ^ " は module " ^ Type.display v.vis_module ^ " の外からは参照できません(pub を付けてください)")
  | _ -> ()

let check_ctor_visible ctor owner =
  match Hashtbl.find_opt con_visibility owner with
  | Some v when not (visible_here v) ->
      type_error
        ("コンストラクタ " ^ Type.display_of ctor ^ " は module " ^ Type.display v.vis_module ^ " の外からは参照できません(newtype "
       ^ Type.display_of owner ^ " に pub を付けてください)")
  | _ -> ()

(* ## 6.5 型エイリアス

   エイリアスは透過的で、型検査では本体に展開した型として扱う。
   表には精緻化済みの型ではなく型の式(`al_body`)をそのまま置き、
   エイリアスを使うたびに、第11章がその場で本体を精緻化して展開する(§11.5)。
   型の式を置く理由は 2 つある。
   1 つは、展開のたびに新しい型変数を作れることである。
   もう 1 つは、`al_kind`(`: Type` か `: EffectRow` か)によって、
   同じ型の式を型としてもエフェクト行としても展開できることである。

   透過的でも、パラメータのカインドだけは表に残す(`al_kinds`)。
   引数を読むのはエイリアスを使う箇所で、そこでは行として読むか型として読むかを、
   パラメータのカインドで決めるしかない。
   本体を見てから引数を読み直すことはできないからである。
   カインドは、第11章がパス 1b の前と後に、本体を試しに精緻化して推論する(§11.39)。
   推論で決まらなかったパラメータのカインドは、パス 1b の後の処理が `Type` に決める。
   エイリアスの `al_kinds` は、newtype の `dd_params` が持つ `vkind` に相当する。

   エイリアスには 2 つの制限がある。
   再帰できないことと、部分適用できないことである。
   部分適用できるエイリアスは、実質的に型レベルの λ である。
   これを許すと、最汎単一化子(mgu)が一意に決まらなくなり、主要型が失われる。 *)

type alias_info = {
  al_name : oid;
  al_params : type_param list;
  al_kinds : Type.kind list; (* パラメータのカインド。パス 1a で作り、パス 1b の前と後に本体から推論する *)
  al_kind : string option; (* : Type / : EffectRow *)
  al_body : T.type_exp;
  (* 本体は宣言のスコープで展開する。module 内のエイリアスが module の内部の型を
     指していても、module の外で展開したときに解決できるように、展開の間はこの module を
     current_module に設定する。引数はエイリアスを使う側のスコープで読む *)
  al_module : string option;
  al_unit : unit_id; (* 本体を展開する間、current_unit に設定する単位 *)
}

let aliases : (oid, alias_info) Hashtbl.t = Hashtbl.create 64

let add_alias info =
  (* 組み込みスカラーの名前は、エイリアスでも再宣言できない(newtype と同じ検査)。
     C の既知名のシグネチャとの照合は型名で比べるので、type Float64 = String が通ると、
     照合は、Float64 と書いた宣言に対して、Float64 でなければならないという矛盾した診断を出す *)
  if Hashtbl.mem reserved_type_names info.al_name && not !in_prelude then
    type_error ("組み込み型 " ^ Type.display_of info.al_name ^ " は型エイリアスで再宣言できません")
  else check_std_type_twin "型エイリアス" info.al_name;
  claim_type_name "型エイリアス" info.al_name;
  if Hashtbl.mem aliases info.al_name then
    if prelude_owned "alias" info.al_name then
      type_error ("標準環境の型エイリアス " ^ Type.display_of info.al_name ^ " は再宣言できません")
    else type_error ("型エイリアス " ^ Type.display_of info.al_name ^ " が二重に宣言されています")
  else (
    Hashtbl.add aliases info.al_name info;
    mark "alias" info.al_name)

(* ## 6.6 データ宣言表と予約型名

   名目的なデータ型の表である。
   データ型を追加しても、型の表現は変わらない。
   データ型は `TCon` 1 つで表し、データ型ごとの情報はこの表だけが持つ。

   フィールドの型に現れるパラメータは、`Generic` の変数として置いてある。
   使うときは、`dd_params` の各 `vid` に新しい変数を割り当て、`subst_params` で置き換える。
   多相型の具体化と同じ仕組みである。

   この表には、注意すべき点が 3 つある。

   ### コンストラクタ名はグローバルに一意

   `ctor_owner` はコンストラクタ名からデータ型名を引く逆向きの表で、登録のときに重複を拒否する。
   コンストラクタ名がグローバルに一意なので、ラベルなしのコンストラクタ適用や、
   引数のないコンストラクタの参照(`None` のように Ident として書いたもの)を、名前だけで解決できる。

   ### `dd_ctors = []` には 2 つの意味がある

   `dd_opaque` が真なら、その型は `Ref` / `Array` / `MutableArray` のような組み込みの不透明型である。
   偽なら、`Never` や `newtype X` のように、コンストラクタが 0 個と確定した型である。
   第10章(exhaust.ml)の `complete_sig` は、この型に `Some []` を返す。
   完全性の判定(`sig_complete`)は、パターン行列の先頭列にコンストラクタが 1 つも現れなくても、
   `Some []` を完全とみなす。
   そのため、`Never` に対する節が 0 個の `match` は網羅的と判定される。
   先頭列にコンストラクタが現れることを完全性の条件に含めると、
   この `match` を誤って非網羅的と判定してしまう。

   ### 予約型名

   `Boolean` / `Int32` / `Int64` / `Float64` / `String` は `con_kinds` には載るが、
   `datas` には載らない。
   組み込みスカラーにはコンストラクタがないので、データ宣言を作る意味がないからである。

   ただし、`datas` に載っていなくても、その名前が空いているわけではない。
   `datas` だけで二重宣言を検査すると、`newtype Boolean = Yes` が検査に通り、
   新しいデータ型として登録される。
   すると、網羅性検査と組み込みインスタンスの両方が正しく動かなくなる。
   第10章は Boolean をコンストラクタ `Yes` だけを持つ型とみなし、
   組み込みの `Eq[Boolean]` は元の真偽値を前提にしたまま残る。

   そこで `reserved_type_names` に組み込みスカラーの名前を載せる。
   ここに載っている名前は、プレリュードの処理中でない限り、
   `newtype` でも型エイリアスでも effect でも再宣言できない。

   `Never` は `reserved_type_names` に入れない。
   `Never` は §6.12 でコンストラクタが 0 個のデータ宣言として `datas` に登録されるので、
   ユーザが `Never` を宣言すると、標準環境の名前の再宣言として拒否される。 *)

type field_info = { fi_label : oid option; fi_ty : Type.ty (* パラメータは Generic の変数。カインドは Type *) }

type ctor_info = { ct_name : oid; ct_fields : field_info list }

type data_info = {
  dd_name : oid;
  dd_params : Type.var_info list; (* Generic 変数の情報(vid をキーにして subst_params で置き換える) *)
  dd_ctors : ctor_info list; (* Never は [] *)
  dd_opaque : bool; (* 組み込みの不透明型(Ref / Array / MutableArray) *)
}

let datas : (oid, data_info) Hashtbl.t = Hashtbl.create 64

let ctor_owner : (oid, oid) Hashtbl.t = Hashtbl.create 128 (* コンストラクタ名 → データ型名 *)

let add_data info =
  if Hashtbl.mem reserved_type_names info.dd_name && not !in_prelude then
    type_error ("組み込み型 " ^ Type.display_of info.dd_name ^ " は newtype で再宣言できません")
  else check_std_type_twin "newtype" info.dd_name;
  claim_type_name "newtype" info.dd_name;
  if Hashtbl.mem datas info.dd_name then
    if prelude_owned "data" info.dd_name then
      type_error ("標準環境の newtype " ^ Type.display_of info.dd_name ^ " は再宣言できません")
    else type_error ("newtype " ^ Type.display_of info.dd_name ^ " が二重に宣言されています")
  else (
    Hashtbl.add datas info.dd_name info;
    mark "data" info.dd_name;
    List.iter
      (fun ct ->
        let s = Type.name_of ct.ct_name in
        if Hashtbl.mem ctor_owner ct.ct_name || Hashtbl.mem ctor_owner (Type.intern (Type.display s)) then
          type_error ("コンストラクタ " ^ Type.display s ^ " が二重に宣言されています(コンストラクタ名はファイルの中で一意)")
        else Hashtbl.add ctor_owner ct.ct_name info.dd_name)
      info.dd_ctors)

(* ## 6.7 エフェクト表と操作の索引

   エフェクト宣言は、非修飾の操作名と操作の型スキームの組の並びである。
   型スキームは Generic 化済みの `TArrow(引数行, 返り値, ρ)` で、
   クラスメソッドと同じ形をしている(§6.10)。

   精緻化木では、操作を完全名、つまり `Console.write` を intern した oid で表す。
   第5章(tree.ml)の `ROp` と `RNeverOp` に入るのがこの完全名である。
   一方、本章の `ef_ops` と `op_index` は、非修飾の操作名をキーにする。
   非修飾で書かれた `perform write(x)` を完全名に解決するために、`op_index` を使う。

   ### 操作名はグローバルに一意ではない

   標準環境の `Console.write`(sample.kel:466)と、sample.kel が宣言する `File.write`(:594)は、
   同じ操作名を持つので、操作名をグローバルに一意にする規則は使えない。
   そこで Diktor は、複数のエフェクトが同じ名前の操作を宣言することを許す。
   `op_index` は、非修飾の操作名から、
   その操作を持つエフェクトを宣言の順に並べたリストを引く表である。
   `set_effect_ops` が `prev @ [ ef_name ]` と末尾に追加するのは、
   このリストを宣言の順に保つためである。

   ### 候補は、その位置で有効なエフェクト行で選ぶ

   候補の先頭を選ぶと、宣言の順序に依存した誤った解決になる。
   そこで第11章は、候補が複数あるとき、
   その位置で有効なエフェクト行に現れる候補が 1 つだけならそれを選び、
   1 つも現れないときと 2 つ以上現れるときは修飾を求める。
   行の中の位置では選ばない。
   位置で選ぶと、ラベルの順序だけが違う同じ型の行で、
   同じ `perform` が別の操作に解決されるからである。
   sample.kel:620 の `copy` は、`File` と `Console` の両方が行にある文脈で `write` を呼ぶので、
   `File.write` と修飾してある(:624)。
   仕様は :532-535 で、ラベルの順序を操作名の解決に使わないことと、
   同じエフェクトを二重に積むと操作は内側のハンドラにしか届かないことを定めている。
   型検査と実行が食い違わないのは、`perform` が解決済みの完全名の oid を持つからである。
   別のエフェクトのハンドラが、同名の操作を先に受け取ることはない。

   したがって、この表の宣言の順序が最終的な選択を決めることはない。
   宣言の順序が影響するのは、修飾を案内するエラーで候補を並べるときだけである。
   行に候補が 1 つも現れないときは、現在の単位から見える、その操作を宣言するエフェクトのすべてを、
   宣言の順に並べる。
   2 つ以上現れるときは、行に現れる候補を宣言の順に並べる。 *)

type effect_info = {
  ef_name : oid;
  ef_ops : (oid * Type.ty) list; (* 非修飾の操作名 → 型スキーム TArrow(引数行, 返り値, ρ)(Generic 化済み) *)
}

let effects : (oid, effect_info) Hashtbl.t = Hashtbl.create 32

(* 複数のエフェクトが同じ名前の操作を宣言できる(標準環境の Console.write と sample.kel の File.write が同名である)。
   非修飾の操作名 → その操作を持つエフェクトを宣言の順に並べたリスト *)
let op_index : (oid, oid list) Hashtbl.t = Hashtbl.create 64

(* エフェクトの登録は 2 段階に分かれる。
   `declare_effect` は名前だけを表に登録し、操作を持たない項目を作る。
   `set_effect_ops` は操作の型スキームを書き込み、操作の索引に追加する。
   第11章のパス 1a が前者を、パス 1b が後者を呼ぶ。
   型の本体に書いたエフェクトラベルの検査は、表に名前があるかどうかだけを調べる。
   そのため、パス 1b で処理する newtype のフィールドや effect の操作の型は、
   後ろで宣言されたエフェクトを参照できる。
   名前の重複と予約の検査は、名前を登録する `declare_effect` が行う。 *)
let declare_effect name =
  (* 組み込みスカラーの名前は effect でも再宣言できない(add_alias と同じ検査)。型名の
     名前空間も newtype や型エイリアスと共有するので、effect List は List の再宣言に
     なる(§6.1 の type_namespace) *)
  if Hashtbl.mem reserved_type_names name && not !in_prelude then
    type_error ("組み込み型 " ^ Type.display_of name ^ " は effect で再宣言できません")
  else check_std_type_twin "effect" name;
  claim_type_name "effect" name;
  if Hashtbl.mem effects name then
    if prelude_owned "effect" name then
      type_error ("標準環境の effect " ^ Type.display_of name ^ " は再宣言できません")
    else type_error ("effect " ^ Type.display_of name ^ " が二重に宣言されています")
  else (
    Hashtbl.add effects name { ef_name = name; ef_ops = [] };
    mark "effect" name)

let set_effect_ops info =
  Hashtbl.replace effects info.ef_name info;
  List.iter
    (fun (op, _) ->
      let prev = Option.value ~default:[] (Hashtbl.find_opt op_index op) in
      Hashtbl.replace op_index op (prev @ [ info.ef_name ]))
    info.ef_ops

let add_effect info =
  declare_effect info.ef_name;
  set_effect_ops info

let find_effect e = Hashtbl.find_opt effects e

(* 現在の単位から見えるエフェクトに限る。op_index のキーは接頭辞を付けない非修飾の操作名なので、
   別の単位のエフェクトの同名の操作も同じキーに入る *)
let op_candidates op =
  List.filter (visible_in_unit unit_synonyms) (Option.value ~default:[] (Hashtbl.find_opt op_index op))

(* ## 6.8 クラス表

   Keleut の型クラスはパラメータを 1 つだけ持つ。
   クラス表の項目は、クラス名、パラメータのカインド、メソッドのほかに、次の 3 つのフィールドを持つ。

   - `ci_param`：クラスパラメータの Generic 変数の情報。
     全メソッドが同じ変数を共有する。
     この変数は、インスタンスの検査がインスタンスの対象の型を代入する箇所(代入点)である。
     対象の型を 1 回代入すれば、クラス内の全メソッドの型が同時に具体化される。
   - `ci_derive_structural`：組み込みの構造的導出を持つかどうか(sample.kel:384-385)。
     真なら、閉じた行の `TRecord` / `TVariant` について、同じ制約を各フィールドに再帰的に要求する。
     真になるのは組み込みの `Eq` だけで、ユーザの宣言では常に偽である。
     導出を指定する構文がないからである。
     閉じた行にしか適用しないのは仕様の規則である(sample.kel:392-396)。
     行変数を含む型を比較できるようにするには、フィールドごとの行制約 `[R: Eq]` が必要で、
     カインドと制約の解決の両方を変更することになる。
   - `ci_builtin`：この項目を本章の `register_builtins`(§6.12)が登録したかどうか。
     このフラグが真のクラスと同名の宣言は、標準環境の名前の再宣言として拒否する(§6.1)。 *)

type class_info = {
  ci_name : oid;
  ci_param : Type.var_info; (* クラスパラメータの Generic 変数(インスタンス検査の代入点) *)
  ci_param_kind : Type.kind;
  ci_derive_structural : bool;
  ci_builtin : bool;
  ci_methods : (string * Type.ty) list; (* メソッド名 → Generic 化済みの型スキーム *)
}

let classes : (oid, class_info) Hashtbl.t = Hashtbl.create 64

let find_class c = Hashtbl.find_opt classes c

(* クラスの宣言の順位を持つ表である。
   順位は、まず組み込みのクラスに、登録した順で振る。
   その続きの順位を、ソースで宣言されたクラスに、宣言を処理した順で振る。
   第8章の正準順は、1 つの型変数に付いた制約をこの順位の昇順に並べる。
   単位は初期化の順に、単位の中の宣言は書いた順に処理するので、
   クラスを順位の昇順に並べると、KIR のクラス表の順序と一致する。
   対話的な実行で取り消した宣言の順位は表に残るが、後の宣言はそれより大きい順位を持つので、
   順位の大小は変わらない。 *)
let class_ranks : (oid, int) Hashtbl.t = Hashtbl.create 64

let class_count = ref 0

let note_class_rank c =
  incr class_count;
  Hashtbl.replace class_ranks c !class_count

let class_rank c = Option.value ~default:max_int (Hashtbl.find_opt class_ranks c)

(* `entity_unit` は、型、クラス、エフェクトの宣言がどの単位のものかを返す。
   内部名に接頭辞が付いていれば、その接頭辞が表す単位を返す。
   接頭辞のない名前には、標準環境(組み込みとプレリュード)の宣言なら標準環境を、
   それ以外なら起点を返す。
   `std_type` と `std_class` は、その名前が標準環境の宣言かどうかを調べる補助関数である。
   `entity_unit` は、孤児規則の検査と、
   型の表示で同名の型に添えるファイルのパス(show.ml の unit_label)が使う *)
let std_type c = Hashtbl.mem reserved_type_names c || prelude_owned "data" c || prelude_owned "alias" c

let std_class c = match Hashtbl.find_opt classes c with Some ci -> ci.ci_builtin || prelude_owned "class" c | None -> false

let entity_unit oid =
  match unit_of_spelling (Type.name_of oid) with
  | Some u -> u
  | None -> if std_type oid || std_class oid || prelude_owned "effect" oid then std_unit else root_unit

let unit_path u = if u = std_unit then "標準環境" else Option.value ~default:"?" (Hashtbl.find_opt unit_paths u)

(* 組み込みと同名の宣言は標準環境の名前の再宣言、それ以外の重複は二重宣言として拒否する *)
let add_class_decl info =
  let s = Type.name_of info.ci_name in
  (match Hashtbl.find_opt classes (Type.intern (Type.display s)) with
  | Some _ when Type.display s <> s ->
      (* 起点でない単位のクラスの内部名には接頭辞が付く。接頭辞のない同名のクラスは標準環境のものである *)
      type_error ("標準環境の type class " ^ Type.display s ^ " は再宣言できません")
  | _ -> ());
  match Hashtbl.find_opt classes info.ci_name with
  | Some prev when prev.ci_builtin ->
      type_error ("標準環境の type class " ^ Type.display_of info.ci_name ^ " は再宣言できません")
  | Some _ -> type_error ("type class " ^ Type.display_of info.ci_name ^ " が二重に宣言されています")
  | None ->
      Hashtbl.add classes info.ci_name info;
      note_class_rank info.ci_name;
      mark "class" info.ci_name

(* ## 6.9 インスタンス表とコヒーレンス

   インスタンス表 `instances` のキーは、(クラス, 先頭の型構成子)の oid の組である。
   `Functor[List[_]]` でも、キーになるのは先頭の型構成子の名前 `List` だけで、
   適用する引数の個数はカインドが決める。
   インスタンスの対象の型に書いた穴 `_` は、カインドの検査にしか使わない。
   キーが型構成子の名前だけなので、インスタンスの探索は表を 1 回引くだけで終わる。

   `ii_premises` は、引数の位置と、その位置に要求するクラスの組のリストで、
   第8章(unify.ml)の制約の伝播が読む。
   `Show[List[_]]` のインスタンスなら、要素の型 `A` が `Show` であることを、
   `List[A]` が `Show` であるための前提として持つ。
   `add_instance` を呼ぶのは、組み込みの登録(§6.12)と、
   ソースに書いたインスタンス宣言を登録する第11章の `register_instance`(§11.35)の 2 か所である。
   プレリュードのインスタンス宣言も `register_instance` が登録する。
   組み込みの登録は前提を持たない。
   `register_instance` は、`type instance[A: Eq] Eq[List[_]]` の `[A: Eq]` のような束縛子から、
   `(引数位置, クラス)` の組を作って渡す。

   組み込みの登録は、`List` と `Option` の `Show` のインスタンスを登録しない。
   これらの `Show` は、プレリュードが前提付きインスタンスとして宣言する(第15章 §15.8)。
   宣言するインスタンスは `Show[List[_]]` と `Show[Option[_]]` で、
   どちらも要素の型が `Show` であることを前提に持つ。
   そのため、`show` は、要素の型が `Show` である `List` と `Option` にも使える。
   仕様も、標準環境が `List` と `Option` に `Show` のインスタンスを持つと定めている(sample.kel:451-452)。
   `List` と `Option` の `Eq` も、プレリュードが宣言する(第15章 §15.9)。
   sample.kel:422-429 が `Eq[List[_]]` の形を示している。

   コヒーレンスは、重複したキーを拒否することで守る(sample.kel:357)。
   インスタンスを書けるファイルは孤児規則(sample.kel:358)で限られ、第11章 §11.35 が検査する。
   インスタンスは隠すことも選び直すこともできない。 *)

type instance_info = {
  ii_premises : (int * oid) list; (* 引数の位置 → 要求するクラス *)
  ii_builtin : bool;
}

let instances : (oid * oid, instance_info) Hashtbl.t = Hashtbl.create 256

(* 予約述語の名前を登録する表である。
   どの名前が予約述語かを決めるのはこの表だけで、クラス宣言の検査(第11章の register_class)と
   インスタンス宣言の検査(下の add_instance)は、どちらもこの表を引く。
   登録するのは §6.12 の register_builtins である *)
let reserved_predicates : (oid, unit) Hashtbl.t = Hashtbl.create 4
let reserved_predicate c = Hashtbl.mem reserved_predicates c

(* コヒーレンスを守るために、重複したキーを拒否する(sample.kel:357)。
   組み込みと同じキーのユーザの宣言は、標準環境のインスタンスの再宣言として拒否する *)
let add_instance ?(builtin = true) ~cls ~con premises =
  (* 予約述語のインスタンスは、この関数でも拒否する(§6.12)。免除するのは組み込みの
     登録(builtin = true)だけである。組み込みの登録自身が Integral[Int32] と
     Fractional[Float64] をこの関数で登録するからである。免除の条件を in_prelude に
     しない理由は §6.12 で述べる *)
  (if reserved_predicate cls && not builtin then
     type_error (Type.display_of cls ^ " は予約されたリテラル述語です(インスタンスは宣言できません、D8)"));
  match Hashtbl.find_opt instances (cls, con) with
  | Some prev when prev.ii_builtin && not builtin ->
      type_error
        ("標準環境のインスタンス " ^ Type.display_of cls ^ "[" ^ Type.display_of con ^ "] は再宣言できません")
  | Some _ ->
      type_error
        ("インスタンス " ^ Type.display_of cls ^ "[" ^ Type.display_of con ^ "] が二重に宣言されています(コヒーレンス違反)")
  | None -> Hashtbl.add instances (cls, con) { ii_premises = premises; ii_builtin = builtin }

let find_instance ~cls ~con = Hashtbl.find_opt instances (cls, con)

(* ## 6.10 組み込み登録の補助関数

   ここから下は、ソースに書けない宣言や、ソースに書かせたくない宣言を、
   本章が直接表に登録する部分である。

   `generic` は Generic の型変数を作る。
   Generic は、その変数が量化されていることを表す状態である。
   Diktor は型スキーム専用のデータ型を持たず、変数の状態 1 つで多相を表す。
   Generic の変数では `vlevel` を使わない。

   `closed_args_row` は、引数の並びを `_item` ラベルの閉じた行にまとめる。
   Keleut の引数の並びは `_item` ラベルを並べたタプル、つまりレコードなので、
   矢印の引数の側はいつもこの形になる。
   行を閉じるのは、引数の個数が呼び出しで確定しなければならないからである。

   メソッドの型スキームは、§6.12 の `arrow1` / `arrow2` がその場で作る。
   要点は 2 つある。
   1 つ目は、最も外側の矢印の行を閉じた空の行にすることである。
   仕様は、メソッドの最も外側の矢印で省略した `@` を `@ {}` と読み、
   どのインスタンスの実装も純粋でなければならないと定めている(仕様 §9、sample.kel:437-438)。
   ユーザが宣言したクラスのメソッド(第11章 §11.33)と同じく、
   組み込みのメソッドもこの規則どおりの行を持つ。
   名前で参照するときと呼び出すときは、使用時に行を開く規則(第11章 §11.26)が行の末尾を開く。
   `+` や前置の `-` は `T.BinOp` と `T.Neg` のノードで、
   呼び出しの経路(第11章 §11.12)を通らないので、
   第11章 §11.13 が型スキームを具体化した直後に、同じ規則で行を開く。
   開かずに単一化すると、`1 + 2` が `@ Console` の本体で型検査に通らなくなる。
   インスタンスの実装が純粋であることは、第11章の包摂検査(§11.38)が検査する。
   入れ子の矢印で省略した `@` を `@ {}` と読む規則(sample.kel:498-504)もあるが、
   組み込みのメソッドはどれも高階ではないので、この規則が適用される箇所はない。
   2 つ目は、クラスパラメータの変数をクラス内で共有することである(§6.8 の代入点)。
   共有させるのは §6.12 の `def_class` である。 *)

(* 登録用の Generic 変数(Generic の変数は vlevel を使わない) *)
let generic ?(kind = Type.KStar) ?(classes = []) () =
  Type.TVar (ref (Type.Generic { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes }))

let closed_args_row tys =
  List.fold_right (fun t acc -> Type.TRowExtend (Type.l_item, t, acc)) tys Type.TRowEmpty

let intern = Type.intern

(* ## 6.11 Ref と配列、リージョンの行

   `Ref` と配列の操作は、本章が直接登録する。
   型パラメータ `[h]` を持つ extern のシグネチャとして同じ型を書くことはでき、
   その場合も脱出検査は行われる。
   それでも組み込みにするのは、実装が OCaml 側の値(§14.10)と切り離せず、
   プレリュードに型を置くと型と実装を別々に管理することになるからである(§15.1 の基準)。

   ### 行は閉じ、使うときに開く

   `heap_row h` は、`Heap[h]` だけを持つ閉じた行を作る。
   仕様は関数型の行を書いたとおりに読むので(sample.kel:475)、
   `Ref.get` の行は閉じた行 `@ {Heap[h]}` である。
   名前で参照するときと呼び出すときに、
   使用時に行を開く規則(第11章 §11.26)が行の末尾を新しい行変数で開くので、
   行が `Console` を持つ文脈でも `Print` を持つ文脈でも `Ref.get` を呼べる。
   ユーザが同じシグネチャを `pub let` で宣言した関数にも、この規則が適用される。

   ### `Ref` はリージョンを型に持つ

   `Ref.new` の返り値の型は `Ref[h, A]` で、リージョン変数 `h` が値の型に現れる。
   そのため、参照を `run` の外へ持ち出そうとすると、
   第8章の脱出検査(スコーレム定数がスコープの外に漏れていないかの検査)が拒否する。
   Haskell の `ST` と同じ仕組みである。

   ### 不変の `Array[A]` と可変の `MutableArray[h, A]`

   仕様 §10 は配列を 2 つに分ける。
   不変の `Array[A]` はリージョンを型に持たず、読む操作しか持たない。
   可変の `MutableArray[h, A]` は、`Ref[h, A]` と同じくリージョン変数 `h` を値の型に持ち、
   生成も読み出しも書き込みも `Heap[h]` を要求する。
   2 つをつなぐのは `MutableArray.freeze` だけで、
   `MutableArray[h, A]` から、型に `h` を持たない `Array[A]` を取り出す。

   この分け方は、次の 3 つを保証する。
   第一に、引数の可変配列に書き込む関数は、純粋な関数として型付けされない。
   可変配列の `h` は呼び出し元から来たスコーレム定数で、
   関数の中の `run` が導入した別のスコーレム定数とは一致しないからである。
   第二に、`@ {}` のコールバックは、
   可変配列を読むことも書くこともできない(`test/region.t` の pardet)。
   第三に、`@` を省略した `pub` の宣言は純粋であるという規則が保たれる。
   newtype のフィールドを経由しても、`run` を抜けた後のリージョンの可変配列に書き込むクロージャを、
   純粋な関数として取り出すことはできない。
   入れ子の矢印で省略した `@` は `@ {}` と読むので、
   フィールドのクロージャの型に `Heap[h]` を隠せないからである。
   `test/region.t` の adv5 が、この取り出しが型エラーになることを確かめる。

   リージョンが保護できるのは、`h` が型に現れている値だけである。
   `Array[A]` は `h` を持たないので、`Array` の組み込み操作には生成と書き込みを置かない。
   仮に置くと、操作が `Heap[h]` を要求しても結果の型に `h` が現れないので、
   `run` の中で作った配列を外へ持ち出せてしまう。
   外から渡された配列も、`run h { … }` で囲むだけで書き換えられてしまう。
   `test/region.t` の noset と nonew は、`Array.set` と `Array.new` が存在しないことを確かめる。

   `freeze` の契約では、取り出した後に元の可変配列へ書き込んでも、取り出した不変配列は変わらない。
   この契約は 1 段だけに適用する。
   要素そのものが可変配列なら、取り出した配列の要素は、
   元の可変配列の要素と同じものを指す(sample.kel:694)。
   `test/region.t` の nested は、`freeze` の後に内側の配列へ書き込んだ 99 を、
   `frozen` を通して読み出す。
   値は共有されるが、型安全性は損なわれない。
   要素の `h` が結果の型 `Array[MutableArray[h, A]]` に残るので、
   脱出検査がリージョンの外への持ち出しを拒否する(sample.kel:695)。
   nested2 は、この持ち出しが `スコープ付きの型 ς1 がスコープの外に漏れています` の型エラーになることを確かめる。
   flat は、要素が可変配列でなければ、同じ形のプログラムが型検査に通ることを確かめる。

   `Array.length` と `Array.get` は純粋な操作なので、行は閉じた空の行である。
   使用時に行を開く規則があるので、行が `Console` を持つ文脈からも呼べる。
   `MutableArray.length` は、長さが変わらないのに `Heap[h]` を要求する。
   これは仕様のシグネチャの一覧のとおりで、仕様はその理由も述べている。
   `Heap[h]` を要求するのは、長さが変わることがあるからではなく(長さを変える操作はない)、
   可変配列に触れること自体を行に記録するためである(sample.kel:696)。

   `Array.each` の行 `e` は、コールバックと呼び出し全体で共有する。
   行変数を 1 つ共有するこの型が、高階関数をエフェクト多相にする最小の形である。
   別々の変数にすると、`each` にエフェクトを起こす関数を渡せなくなる。
   不変配列の読み出しは純粋なので、`Array.each` は `Heap` を要求しない。

   `MutableArray` のカインドは `Ref` と同じ `k_arrow 2` で、
   リージョンのパラメータのカインドは `KStar` である。
   `run h` が作るスコーレム定数の既定のカインドが `KStar` なので、
   リージョンのために別のカインドを用意する必要はない。

   ここで決まる 11 個の操作名は、そのまま値環境での名前になる。
   内訳は、`Ref` の `new` / `get` / `set`、`Array` の `length` / `get` / `each`、
   `MutableArray` の `new` / `length` / `get` / `set` / `freeze` である。
   第11章の module の平坦化は、ユーザの `module` 宣言がこれと同じ修飾名を作ることを拒否する(§11.42)。
   組み込みの操作をここに追加すると、保護される名前も同時に 1 つ増える。 *)

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
  let heap_row h = Type.TRowExtend (Type.eff_heap, h, Type.TRowEmpty) in
  let def name ty = builtin_ops := !builtin_ops @ [ (name, ty) ] in
  (* Ref.new : [h, A] (A) => Ref[h, A] @ {Heap[h]} *)
  (let h = generic () and a = generic () in
   def "Ref.new" (arrow [ a ] (Type.TCon (ref_oid, [ h; a ])) (heap_row h)));
  (let h = generic () and a = generic () in
   def "Ref.get" (arrow [ Type.TCon (ref_oid, [ h; a ]) ] a (heap_row h)));
  (let h = generic () and a = generic () in
   def "Ref.set" (arrow [ Type.TCon (ref_oid, [ h; a ]); a ] Type.t_unit (heap_row h)));
  (* Array は不変(仕様 §10)。読み出しの行は閉じた空の行で、使うときに開く *)
  (let a = generic () in
   def "Array.length" (arrow [ Type.TCon (arr_oid, [ a ]) ] Type.t_int32 Type.TRowEmpty));
  (let a = generic () in
   def "Array.get" (arrow [ Type.TCon (arr_oid, [ a ]); Type.t_int32 ] a Type.TRowEmpty));
  (let a = generic () and e = generic ~kind:Type.KRow () in
   def "Array.each" (arrow [ Type.TCon (arr_oid, [ a ]); arrow [ a ] Type.t_unit e ] Type.t_unit e));
  (* MutableArray は h を型に持つ。すべての操作が Heap[h] を要求する。length が
     要求するのも、仕様 §10 のシグネチャの一覧のとおりである *)
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

(* ## 6.11b pinned

   `pinned` は、本体の行から `Blocking` を取り除いて結果を返す組み込みである。
   型は本章に、値は §14.10 に置く。
   型は Keleut の構文で書けるが、
   本体の行から `Blocking` を取り除く値は Keleut のソースでは書けない。
   本体を呼ぶと、その行の `Blocking` が呼び出し元の行に残るからである。
   値の実装は関数の適用を使う。
   適用は第14章(interp.ml)にあるので、ほかのプリミティブと同じ第13章(builtin.ml)には置けない。 *)
let register_pinned () =
  let arrow args ret eff = Type.TArrow (Type.TRecord (closed_args_row args), ret, eff) in
  let def name ty = builtin_ops := !builtin_ops @ [ (name, ty) ] in
  (* pinned : [A, E] (() => A @ {Blocking extends E}) => A @ E。
     Blocking は操作を持たない組み込みのラベル(§6.11)なので、Blocking を行から
     取り除くのは型の上だけの操作である。run が実行時には本体を評価するだけなのと
     同じである(§14.4)。@ Blocking の関数はトップレベルから直接呼べる(仕様 §9 / §12)。
     pinned が必要なのは、注釈で行を閉じた内側の文脈で @ Blocking の関数を呼ぶときである *)
  (let a = generic () and e = generic ~kind:Type.KRow () in
   def "pinned" (arrow [ arrow [] a (Type.TRowExtend (Type.eff_blocking, Type.t_unit, e)) ] a e))

(* ## 6.12 組み込みのクラスと数値インスタンス

   演算子が呼ぶクラス(第7章(prims.ml)の表の右辺)を、ここで直接登録する。
   プレリュードのソースに書かずに OCaml 側に置くのは、
   これらのクラスの実装がプリミティブにしかないからである。

   `register_builtins` の最初の 3 行は、`in_prelude` を立て、`Fun.protect` で必ず元に戻す。
   組み込みの登録をプレリュードの処理として扱うので、
   `mark` が組み込みのデータ型とエフェクトを `prelude_keys` に記録する。
   そのため、ユーザのプログラムが `Never` を宣言し直すと、
   標準環境の名前の再宣言として拒否される(§6.1)。
   `Add` や `Add[Int32]` のようなクラスとインスタンスは、
   `in_prelude` ではなく `ci_builtin` / `ii_builtin` で区別する(§6.1)。
   `Fun.protect` は、例外で抜けてもフラグが戻ることを保証する。
   フラグが戻らないと、以後のユーザの宣言がすべてプレリュードの宣言として扱われる。
   その結果、組み込みスカラーの名前の再宣言が検査に通り、
   ユーザの newtype、型エイリアス、effect、extern どうしの重複も `再宣言できません` と診断される。

   `def_class` は、クラスパラメータの Generic 変数 `pinfo` を 1 つ作り、
   全メソッドで共有する(§6.8 の代入点)。
   クラスの分け方は sample.kel:372 のとおりである。
   `Num` のような 1 つのクラスにまとめないのは、`String` のように `+` だけを持つ型があるからである。
   そのため、String は `Add` のインスタンスにだけ入り、`Sub` / `Mul` / `Div` には入らない。
   `Ord` に Boolean が入っていないのは、真偽値に大小を定めていないからである。
   `Rem` に Float64 が、`Neg` に String が入っていないのは、対応するプリミティブがないからである。

   `Integral` / `Fractional` は予約述語である。
   メソッドを持たないクラスとしてクラス表 `classes` に登録するだけで、専用の仕組みは持たない。
   型変数に付くクラス制約の集合がすでにあるので、リテラルの型を絞る仕組みを別に作らずに済む。
   `1 + x` で `{Integral, Add}` の 2 つが同じ変数に付くときも、
   制約の集合の処理をそのまま使える。
   既定化は一般化の直前に行うので、通常はこの述語が型の表示に現れることはない。

   予約述語の名前は、宣言の 3 つの経路のすべてで検査する。
   同名のクラス宣言は、第11章の `register_class` が拒否する。
   インスタンス宣言は、第11章の `register_instance` が、宣言のクラス名を取り出した時点で拒否し、
   §6.9 の `add_instance` も拒否する。
   型パラメータの制約(`[A: Integral]` と書く形)は、第11章の `class_names_of` が拒否する。
   どの検査も、§6.9 の `reserved_predicates` 表を引く。
   `reserved_predicates` 表は名前の検査に使うだけで、
   予約述語の意味(リテラルの既定化でどう扱うか)は持たない。
   その意味は、第8章(unify.ml)が第1章の定数で別に持つ。

   経路を 1 つでも検査しないでおくと、予約述語にユーザの宣言が入り、リテラルの既定化の前提が崩れる。
   インスタンス宣言を検査しないと、`type instance Integral[String]` が表に登録され、
   `[A: Integral]` の制約の解決に使われる。
   メソッドが 0 個なので、メソッドの不足と余分を調べる検査はこの宣言を拒否しない。
   型パラメータの制約を検査しないと、`let f[A: Integral](): A = 1` が型検査に通り、
   実行時に `数値リテラルの型が解決されていません` の実行時エラーになる。

   `add_instance` の検査を免除するのは、組み込みの登録(`builtin = true`)だけである。
   下の `register_builtins` 自身が、
   `Integral[Int32]` や `Fractional[Float64]` を `add_instance` で登録するからである。
   免除の条件を `in_prelude` にすると、`--prelude` で差し替えたユーザのプレリュードまで免除され、
   予約を回避できてしまう。

   `register_builtins` が登録する `Never` が、
   §6.6 で述べたコンストラクタが 0 個のデータ宣言である。 *)

let register_builtins () =
  (* 組み込みの登録はプレリュードとして扱う(同名のユーザの宣言を標準環境の名前の再宣言として拒否するため) *)
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
  (* クラスとメソッド(sample.kel:373-396 に相当する宣言を本章が直接登録する)。
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
    note_class_rank cls;
    List.iter (fun con -> add_instance ~cls ~con:(intern con) []) insts
  in
  let arrow2 a ret = Type.TArrow (Type.TRecord (closed_args_row [ a; a ]), ret, Type.TRowEmpty) in
  let arrow1 a ret = Type.TArrow (Type.TRecord (closed_args_row [ a ]), ret, Type.TRowEmpty) in
  def_class "Add" ~derive:false ~methods:(fun a -> [ ("add", arrow2 a a) ]) ~instances:("String" :: numerics);
  def_class "Sub" ~derive:false ~methods:(fun a -> [ ("sub", arrow2 a a) ]) ~instances:numerics;
  def_class "Mul" ~derive:false ~methods:(fun a -> [ ("mul", arrow2 a a) ]) ~instances:numerics;
  def_class "Div" ~derive:false ~methods:(fun a -> [ ("div", arrow2 a a) ]) ~instances:numerics;
  def_class "Rem" ~derive:false ~methods:(fun a -> [ ("rem", arrow2 a a) ]) ~instances:[ "Int32"; "Int64" ];
  def_class "Neg" ~derive:false ~methods:(fun a -> [ ("neg", arrow1 a a) ]) ~instances:numerics;
  def_class "Eq" ~derive:true
    ~methods:(fun a -> [ ("eq", arrow2 a Type.t_boolean) ])
    ~instances:("String" :: "Boolean" :: numerics);
  def_class "Ord" ~derive:false
    ~methods:(fun a -> List.map (fun m -> (m, arrow2 a Type.t_boolean)) [ "lt"; "le"; "gt"; "ge" ])
    ~instances:("String" :: numerics);
  def_class "Show" ~derive:false
    ~methods:(fun a -> [ ("show", arrow1 a Type.t_string) ])
    ~instances:("String" :: "Boolean" :: numerics);
  (* 予約述語。メソッドのないクラスとしてクラス表に登録する *)
  List.iter (fun n -> Hashtbl.replace reserved_predicates (intern n) ()) [ "Integral"; "Fractional" ];
  def_class "Integral" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Int32"; "Int64" ];
  def_class "Fractional" ~derive:false ~methods:(fun _ -> []) ~instances:[ "Float64" ];
  (* Never はコンストラクタが 0 個のデータ宣言。complete_sig が Some [] を返すので、
     節が 0 個の match が網羅的と判定される *)
  add_data { dd_name = intern "Never"; dd_params = []; dd_ctors = []; dd_opaque = false };
  builtin_ops := [];
  register_ref_array ();
  register_pinned ()

(* ## 6.13 値環境への登録と表の初期化

   `builtin_values` は、クラスメソッドを通常の多相の定数として値環境に並べる。
   型クラスのメソッドを特別に扱う必要はない。
   メソッドの型はクラス制約付きの Generic 変数を含む多相型で、名前の探索は通常の変数参照である。
   実装の選択は、型検査が木に書いた証拠から第14章が辞書を作って行う(§14.6)。

   sample.kel はメソッドを非修飾名 `add` と修飾名 `Add.add` のどちらの形でも参照するので、
   メソッドは両方の名前で値環境に登録する。

   組み込みの値の一覧は `builtin_values` の 1 つだけである。
   第11章の平坦化が、組み込みがすでに使っている名前かどうかを調べるときも、
   `is_builtin_value` を通して `builtin_values` を引く(§11.42)。
   一覧を 2 つ作ると、組み込みの操作を追加したときに片方を直し忘れ、
   保護しているはずの名前が保護されなくなる。
   `is_builtin_value` は呼ばれるたびに一覧を作り直す。
   そのコストは `classes` を 1 回たどるだけで、
   呼ばれるのも module のメンバ 1 つにつき高々 1 回である。

   `reset` は、同じプロセスで宣言表を初期状態に戻して検査をやり直す処理のためにある。
   ファイルを実行する CLI は、1 つのプロセスで 1 つのプログラムしか扱わないので、
   `reset` を呼ばない。
   呼ぶのは、第16章の `type_check_string` / `eval_string` と、対話的な実行の `:reset` である。
   宣言表が残っていると、2 回目の呼び出しは同じプログラムでも `二重に宣言されています` の型エラーになる。

   第16章の API は、`reset`、平坦化、型検査の順に呼ぶ。
   平坦化の後に `reset` を呼ぶと、平坦化が登録した別名を `reset` が消してしまう。

   `reset` が表を 1 つでも戻し忘れると、前の呼び出しが残した宣言が次の呼び出しに漏れる。
   その結果、単独では型検査に通るプログラムが、ほかのプログラムの後に検査するとエラーになるという、
   原因を追いにくい不具合になる。
   本章に表を追加したら、`reset` にも追加しなければならない。
   `Type.intern` の oid の表は戻さない。
   長時間動く API では oid が単調に増えるが、実害はない。

   `reset` の後にある `let () = register_builtins ()` は、
   モジュールを初期化する時点で組み込みを登録する。
   表がモジュールの状態なので、この副作用を伴う初期化が必要である。
   第16章(driver.ml)が処理を始める前に、組み込みはすでに表に登録されている。 *)

(* 名前、型、参照先の 3 つ組のリストを返す。
   クラスメソッドは、非修飾名も修飾名も同じ参照先 GMethod Cls.m を指す *)
let builtin_value_refs () =
  Hashtbl.fold
    (fun _ ci acc ->
      List.fold_left
        (fun acc (m, ty) ->
          let q = Type.name_of ci.ci_name ^ "." ^ m in
          (m, ty, Tree.GMethod q) :: (q, ty, Tree.GMethod q) :: acc)
        acc ci.ci_methods)
    classes []
  @ List.map (fun (n, ty) -> (n, ty, Tree.GBuiltin n)) !builtin_ops

let builtin_values () = List.map (fun (n, ty, _) -> (n, ty)) (builtin_value_refs ())

(* 組み込みが値環境に登録する名前なら真を返す。
   修飾名 Ref.new / MutableArray.set も、クラスメソッドの Show.show / show も、その名前に含まれる。
   module の平坦化が同じ修飾名を作るのを拒否するために、第11章が呼ぶ。
   一覧は builtin_values の 1 つだけで、この関数はそれを引くだけである *)
let is_builtin_value name = List.mem_assoc name (builtin_values ())

let reset () =
  Hashtbl.reset con_kinds;
  Hashtbl.reset aliases;
  Hashtbl.reset classes;
  Hashtbl.reset class_ranks;
  class_count := 0;
  Hashtbl.reset instances;
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
  Hashtbl.reset module_con_synonyms;
  Hashtbl.reset module_val_synonyms;
  Hashtbl.reset con_hints;
  Hashtbl.reset value_visibility;
  Hashtbl.reset con_visibility;
  Hashtbl.reset decl_module;
  Hashtbl.reset unit_paths;
  Hashtbl.reset decl_unit;
  Hashtbl.reset unit_synonyms;
  Hashtbl.reset unit_ctors;
  Hashtbl.reset unit_classes;
  Hashtbl.reset unit_qualifiers;
  current_module := None;
  current_unit := root_unit;
  in_prelude := false;
  register_builtins ()

let () = register_builtins ()

(* ## 6.14 宣言表のコピー

   対話的な実行(第16章)は、型検査に失敗した入力の宣言を表に残さない。
   `snapshot` は、本章のグローバルな表 27 個と参照 4 つの内容をコピーし、
   コピーした時点の内容に戻すクロージャを返す。
   戻すときは、表を空にしてからコピーを書き戻す。
   `Hashtbl.fold` は同じキーの束縛を新しい順に渡すので、リストの先頭に追加していき、
   できたリストの順に `add` すれば、隠れた束縛の順序も元に戻る。

   コピーは浅いコピーで足りる。
   表の値は不変で、値の中で書き換わるのは型変数とカインド変数のセルだけだからである。
   セルの書き換えは、第1章 §1.5 の書き換えの記録が元に戻す。
   コピーのコストは表の大きさに比例するが、プレリュードと sample の宣言を入れた表でも、
   1 回あたり数マイクロ秒で済む。 *)
let snapshot_tbl (t : ('a, 'b) Hashtbl.t) =
  let saved = Hashtbl.fold (fun k v acc -> (k, v) :: acc) t [] in
  fun () ->
    Hashtbl.reset t;
    List.iter (fun (k, v) -> Hashtbl.add t k v) saved

let snapshot () =
  let rs =
    [
      snapshot_tbl prelude_keys;
      snapshot_tbl type_namespace;
      snapshot_tbl externs;
      snapshot_tbl con_kinds;
      snapshot_tbl reserved_type_names;
      snapshot_tbl con_synonyms;
      snapshot_tbl module_con_synonyms;
      snapshot_tbl module_val_synonyms;
      snapshot_tbl con_hints;
      snapshot_tbl val_synonyms;
      snapshot_tbl value_visibility;
      snapshot_tbl con_visibility;
      snapshot_tbl decl_module;
      snapshot_tbl unit_paths;
      snapshot_tbl decl_unit;
      snapshot_tbl unit_synonyms;
      snapshot_tbl unit_ctors;
      snapshot_tbl unit_classes;
      snapshot_tbl unit_qualifiers;
      snapshot_tbl aliases;
      snapshot_tbl datas;
      snapshot_tbl ctor_owner;
      snapshot_tbl effects;
      snapshot_tbl op_index;
      snapshot_tbl classes;
      snapshot_tbl instances;
      snapshot_tbl reserved_predicates;
    ]
  in
  let ip = !in_prelude and cm = !current_module and cu = !current_unit and bo = !builtin_ops in
  fun () ->
    List.iter (fun r -> r ()) rs;
    in_prelude := ip;
    current_module := cm;
    current_unit := cu;
    builtin_ops := bo
