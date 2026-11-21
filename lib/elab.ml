(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第11章 型推論の本体

   本章は Keleut の型検査器を実装する。
   第5章(tree.ml)が用意した精緻化木を受け取り、
   ノードごとに型と解決結果を書き込みながら、第8章(unify.ml)の単一化を呼ぶ。
   名前と宣言の表は第6章(decls.ml)、演算子とランタイムエフェクトの表は第7章(prims.ml)、
   網羅性検査を遅らせるための検査キューは第10章(exhaust.ml)のものを使う。
   本章が出力するのは、型と解決結果を書き込んだ木である。
   第14章(interp.ml)はその木をたどって評価する。

   本章の関数は、次の 3 つの規則を守る。

   - eff は呼び出し元から引数で渡す。
     式が起こすエフェクトの集合を返り値で返して集めるのではなく、
     その位置で許されているエフェクト行を引数で渡す。
     perform を見つけたら、その行と 1 回単一化するだけで済む。
   - level は引数で渡し、グローバル変数に置かない。
     レベルをグローバル変数に置くと、例外で関数を抜けるたびに元の値へ戻す処理が必要になる。
     引数で渡せば、型エラーの例外で検査の途中から抜けても、レベルを戻し損ねることがない。
   - 推論の結果は木に書く。
     `elab_exp` は型を返すと同時に `set_ty` でノードに型を書き込み、
     コンストラクタ、操作、節の解決結果を `set_resolved` で書き込む。
     評価器はこの解決結果を読むので、名前解決をやり直さない。

   ## 宣言処理のパス構成

   トップレベルの宣言は、1 回の走査では処理しきれない。
   前方参照と、宣言どうしの相互再帰を型検査できるようにするために、宣言の並びを 4 回走査する。
   前方参照の例は、sample.kel:458 の `user_names` が、
   後ろで宣言される `println`(:510)を呼ぶ箇所である。

   | パス | 登録するもの | 独立のパスにする理由 |
   |---|---|---|
   | 1a | エイリアスの表、newtype の名前とカインド、effect の名前 | 型の本体を書く前に、型構成子のカインドとエフェクトの名前を引けるようにする |
   | 1a′ | (登録しない)newtype とエイリアスの本体を試しに精緻化する | パラメータのカインドを宣言順に依存せず決める |
   | 1b | newtype のコンストラクタ、effect の操作、class のメソッド | 型の本体を書くのでカインドの表とエフェクトの名前が必要である。1a′ の後なので、宣言順に依存しない |
   | 1c | インスタンスの対象の型、前方参照できる let のシグネチャ | 対象の型の検査にクラス表が必要である。シグネチャは前方参照に使う |
   | 2 | let / let rec / 式 / extern / インスタンス本体 | 本体を宣言順に推論し、順に型を表示する |

   1a〜1c は宣言の表を埋めるパス、2 は本体を推論するパスである。
   1a′ は独立のパスではなく、1a に続けて行う処理で、宣言の表には何も登録しない(§11.39)。
   結果を捨てる試行なので、ここで出た診断は報告しない。
   1b の後にも、独立のパスにしない後処理のループを 2 つ実行する(§11.39)。
   1c がシグネチャを登録するのは、引数と返り値に注釈がある let のうち、
   束縛の最も外側の `@` を書いたものと、`pub` のものだけである。
   それ以外の let は登録しないので、その let を参照できるかどうかは宣言順に依存する。
   この条件をこう決めた理由は §11.36 で述べる。

   ## 主要関数の一覧

   | 関数 | 役割 |
   |---|---|
   | `elab_type` / `elab_eff` | ソースに書いた型の式から内部型 / エフェクト行を作る。展開とカインド検査を含む |
   | `expand_alias` | エイリアスを展開する。再帰するエイリアスと部分適用をここで拒否する |
   | `elab_pat` | パターンを期待型に対して検査し、単相の束縛を追加した環境を返す |
   | `is_value` | 式が構文上の値かどうかを判定する(値制限) |
   | `elab_exp` / `elab_exp'` | 式の型を推論し、木に型を書き込む |
   | `elab_check` | 簡易な検査モード。無名関数とレコード拡張(呼び出しの引数リストを含む)にだけ期待型を渡す |
   | `resolve_perform` | 操作名から(エフェクト, 操作, 型スキーム)を引く。修飾なしの名前は、行に現れる候補が 1 つのときだけ解決する |
   | `at_node` | 位置なしの型エラーに、最も内側のノードの span を付ける |
   | `check_resume_static` | resume が第二級であることを構文上で検査する |
   | `elab_handle` | handle の節を分類し、対象エフェクトを決めて型を付ける |
   | `elab_binding` / `elab_rec_bindings` | let / let rec を検査する。Rigid を作り、出口で解放する |
   | `make_rigids` / `release_rigids` | 注釈の型パラメータをスコーレム定数にし、出口で解放する |
   | `open_closed_arrow` / `subsume_closed` | 閉じた行を、使用時に開く |
   | `register_newtype` ほか `register_*` | パス 1 で宣言を登録する |
   | `unwritten_effect` / `check_pub_annots` | pub の注釈が完全かどうかを検査する |
   | `signature_of_binding` | パス 1c が登録する、前方参照のためのシグネチャを作る |
   | `check_instance_bodies` | インスタンス本体を包摂で検査する |
   | `process_decls` / `type_check_decls` / `type_check` | 型検査のエントリポイントである |
   | `start_session` / `check_input` | 対話的な実行のエントリポイントである |
   | `flatten_modules` | module を平坦化する |

   本章で繰り返し使う手順は少ない。
   代表的なのは、§11.17 と §11.28 に出てくる次の 3 つの手順である。

   1. レベルを上げる。
   2. スコーレム定数を作る。
      スコーレム定数は型パラメータを固定した定数で、コードでは `Rigid` と書く。
   3. 出口で、スコーレム定数がスコープの外に漏れていないかを調べる。 *)

open Aux
open Syntax
open Type
module T = Tree.Tree
module SMap = Map.Make (String)

(* ## 11.1 環境の 5 つのフィールド

   環境は不変の Map で、値として渡す。
   enter / leave のようにスコープを破壊的に出入りする操作を持たないので、
   スコープを戻し忘れることがない。
   型エラーの例外で検査の途中から抜けても、呼び出し元が持っている env は変わらない。

   環境のフィールドは 5 つある。
   `values` は変数の型を持つ。
   Generic を含む型をそのまま型スキームとして使い、型スキーム専用のデータ型は持たない。
   `types` は型パラメータの束縛を持ち、リージョン変数 `h` もここに入る。
   `resume_ty` は、操作節の中でだけ Some になる 2 つ組である。
   `no_resume` は、`resume` を書けない位置を表し、
   その位置に `resume` を書いたときの診断に使う(§11.16)。
   位置は、再開しない操作(返り値の型が `Never` の操作)の節、操作節のガード、
   `return` 節、`cancel` 節の 4 種類で、再開しない操作の節はその操作名を持つ。
   これらの位置の外では `None` である。
   `tops` は、`values` の名前のうちトップレベルの宣言を指すものについて、
   名前から参照先の宣言(`Tree.gref`)を引く表である。
   `add_local` は、ローカルの束縛を追加するときに同じ名前を `tops` から取り除くので、
   ローカルの名前は同名のトップレベルの宣言を隠す(シャドーイング)。
   変数の参照では、`tops` に名前があれば、その参照先を木に書く(§11.11)。

   resume は第一級の値ではないので、`values` には入れず、
   その型付けに必要な型を env の `resume_ty` に置く。
   この設計では、resume が第二級であることを別に検査する必要がある。
   その検査は §11.21 で述べる。

   警告は `warnings` にためておき、後で表示する。
   `current_out` は、型エラーで型検査を中止するまでに確定した出力の行を持つ。
   型エラーで中止したときは、エントリポイントの `type_check`(§11.43)がここまでの行をエラーと一緒に返し、
   第16章のドライバがそれを表示する。

   `closed_item_row` は、引数の型のリストを閉じた `_item` 行にまとめるだけの補助関数である。
   関数適用(§11.12)の引数の個数の不一致は、この閉じた行の単一化でも検出される。
   実引数にラベルがなく、仮引数の行が閉じた `_item` 行に決まっている呼び出しでは、
   引数の行の単一化より前に `check_call_arity`(§11.12)が個数を比較する。
   呼び出し先の関数のエフェクト行の単一化はそれより前に行うので、
   エフェクト行の不一致はそちらで先に報告される。
   ラベル付きの実引数を含む呼び出しと、仮引数の型がまだ決まっていない呼び出しでは個数を比較せず、
   単一化に任せる。 *)

type no_resume = No_never_clause of oid | No_guard | No_return_clause | No_cancel_clause

type env = {
  values : ty SMap.t;
  types : ty SMap.t; (* 型パラメータの束縛。リージョン変数 h を含む *)
  resume_ty : (ty * ty) option; (* (操作の返り値の型, handle 式全体の型)。操作節の中でだけ Some *)
  no_resume : no_resume option; (* resume を書けない位置。resume の診断に使う *)
  tops : Tree.gref SMap.t; (* トップレベルの宣言を指す名前 → 参照先の宣言。ローカルの束縛と同じ名前は取り除く *)
}

(* ローカルの束縛を追加する。同名のトップレベルの宣言は隠される *)
let add_local env x t = { env with values = SMap.add x t env.values; tops = SMap.remove x env.tops }

(* トップレベルの宣言ごとの型を持つ表。
   環境は名前で引くので、同じ名前を束縛し直すと、前の束縛の型を環境からは引けない。
   対話的な実行が 1 つの入力の中にある同名の束縛の型を引くときと、
   公開表(§11.45)が pub の束縛の型を引くときに、参照先の宣言をキーにしてこの表を引く *)
let top_types : (Tree.gref, ty) Hashtbl.t = Hashtbl.create 64

(* トップレベルの宣言を環境に追加し、その型を top_types に記録する *)
let add_top env x t g =
  Hashtbl.replace top_types g t;
  { env with values = SMap.add x t env.values; tops = SMap.add x g env.tops }

let warnings : string list ref = ref []

let warnings_count = ref 0

(* 警告はリストの先頭に追加し、読む側が順序を逆にして元に戻す。
   末尾に @ で追加すると、警告の数の 2 乗に比例する時間がかかる *)
let warn msg =
  warnings := msg :: !warnings;
  incr warnings_count

(* 出力の 1 行。行の種別をコンストラクタで区別する。
   先頭に ⚠ を付けるなどの整形は第16章が行うので、表示する文字列を調べて種別を推測する必要がない *)
type out_line = Binding of string | Warning of string

(* 型エラーで型検査を中止するまでに確定した出力の行。エラーのときにもドライバが表示する *)
let current_out : out_line list ref = ref []

let closed_item_row tys = List.fold_right (fun t acc -> TRowExtend (l_item, t, acc)) tys TRowEmpty

(* 位置なしの Type_error に、例外を投げた最も内側のノードの span を付ける。
   位置つきの Type_error_at は捕捉せずにそのまま通すので、
   外側の at_node が位置を上書きすることはない。
   最後に訪れたノードをグローバル変数に持つ方法は採らない。
   eff と level を引数で渡すのと同じく、診断でもグローバルな状態を持たないためである *)
let at_node node f =
  try f () with
  | Type_error msg -> raise (Type_error_at (Tree.loc_of node, msg))
  | NotImplemented feat -> raise (NotImplemented_at (Tree.loc_of node, feat))

(* ## 11.2 数値リテラルの型

   Keleut は Int32 / Int64 / Float64 の 3 つの数値型を持つので、
   接尾辞のない `1` の型はその場では決められない。
   Diktor は整数リテラルの型を新しい型変数にし、
   その変数に予約述語 `Integral` をクラス制約として付ける。
   浮動小数点数のリテラルには、同じく予約述語の `Fractional` を付ける。

   リテラル専用の型も、リテラルの型を後で決めるための専用の段階も作らない。
   予約述語は、型変数に付くクラス制約の集合に、通常のクラス制約と一緒に入れるだけである。
   この集合は第8章の `add_class` が扱う。
   たとえば `1 + x` では、`{Integral, Add}` の 2 つの制約が同じ変数に付き、
   単一化のたびに両方が伝播する。
   そのため、リテラルの述語のための仕組みを別に持たなくても、
   既定化(defaulting)とクラスの解決は同じ制約の集合を使える。

   接尾辞が付いていれば具体型にする。
   意味を持つ接尾辞は `i32`、`i64`、`f64` の 3 つだけである。
   それ以外の接尾辞も字句解析では 1 個の数値トークンになるが、言語にない型を指すので、
   ここで型エラーにする。
   黙って別の幅に丸めることはしない。
   字句解析や構文解析の段階でエラーにしないのは、型エラーとして報告し(§11.43)、
   それまでに確定した、型を表示する行を出力に残すためである。
   浮動小数点数の本体に整数の接尾辞を付けたリテラルも、同じく型エラーにする。

   残った `Integral` / `Fractional` の変数は、
   束縛を一般化する `generalize` か、
   宣言の終わりの `default_numerics` が Int32 / Float64 に決める(第8章)。
   `number_ty` はリテラルの位置を第8章の `literal_origins` に記録する。
   既定の型がほかの制約を満たさないとき、既定化は報告する位置を、まず現在の宣言の証拠の穴から探す。
   記録したリテラルの位置を使うのは、穴が見つからないときである(第8章 §8.9)。
   既定化は型の表示より先に行うので、通常の型の表示にこれらの述語は現れない。

   ### パターンの数値リテラルは、宣言の終わりに型に従って読み取る

   `number_ty` はリテラルの表記を読まないので、型の範囲を超える数値リテラルも型検査に通る。
   式の位置では、評価器(第14章)がリテラルを評価する時点で、範囲外のリテラルを実行時エラーにする。
   パターンの位置のリテラルは評価されない。
   第14章の照合は、リテラルを値の型の数値として読み取れなければ、その節を不一致として次へ進む。
   そのため、Int32 の照合対象に書いた `case 4294967295` は、どの値にも一致しない節として、
   診断なしで残る。
   第10章(exhaust.ml)の網羅性検査はパターン行列の列の型を知らないので、この節を報告できない。

   そこで、パターンの数値リテラルを `pattern_numbers` に追加しておき、
   宣言の終わりの既定化の後に `check_pattern_numbers` で読み取る。
   既定化の後なら、どのリテラルのノードの型も Int32、Int64、Float64 のどれかに決まっている。
   その型の数値として読み取れなければ、リテラルの位置を指す型エラーにする。
   読み取りには、第14章の照合と同じく、OCaml の `Int32.of_string` などを使う。
   浮動小数点数の読み取りは、オーバーフローしても無限大になるだけで失敗しないので、
   調べるのは整数の 2 つの型だけである。

   パターンを推論する時点で検査しないのは、その時点ではまだ型が決まっていないことがあるからである。
   注釈のない引数を照合する `fn(x) => x match { case 4294967295 => … }` では、
   リテラルの型は `Integral` 述語の付いた変数のままで、宣言の終わりに Int32 に決まる。
   網羅性検査の時点(束縛の一般化の直前)でも、同じ理由で型が決まっているとは限らない。 *)

let number_ty ~loc level (n : number) : ty =
  match n.n_suffix with
  (* 浮動小数点数の本体に整数の接尾辞が付いたリテラル(1.i32 / 1e3i64)は拒否する。
     受理すると、評価器の Int32.of_string が本体を読み取れず、
     型検査に通ったリテラルが評価のたびに実行時エラーになる *)
  | Some (NsInt _ | NsUInt _) when n.n_is_float ->
      type_error ("数値リテラル " ^ Lexer.show_number n ^ " は浮動小数の本体に整数接尾辞が付いています")
  | Some (NsInt 32) -> t_int32
  | Some (NsInt 64) -> t_int64
  | Some (NsFloat 64) -> t_float64
  | Some _ ->
      type_error
        ("数値リテラル " ^ Lexer.show_number n ^ " の接尾辞 " ^ n.n_suffix_text ^ " はありません(接尾辞は i32、i64、f64 だけです)")
  | None ->
      let v = new_var level in
      let c = if n.n_is_float then cls_fractional else cls_integral in
      Unify.add_class v c;
      Unify.note_literal ~loc v c;
      v

(* パターンの数値リテラルのノードとリテラル。
   elab_pat がリストの先頭に追加し、check_pattern_numbers が読み取る *)
let pattern_numbers : (T.pat * number) list ref = ref []

(* 既定化の後に、パターンの整数リテラルを、ノードの型の数値として読み取る。
   読み取れないものがあれば、推論した順で最初のものを型エラーにする *)
let check_pattern_numbers () =
  let pats = List.rev !pattern_numbers in
  pattern_numbers := [];
  List.iter
    (fun (node, (n : number)) ->
      let fits =
        match repr (Tree.get_ty node) with
        | TCon (c, []) when c = intern "Int32" -> Some ("Int32", Option.is_some (Int32.of_string_opt n.n_text))
        | TCon (c, []) when c = intern "Int64" -> Some ("Int64", Option.is_some (Int64.of_string_opt n.n_text))
        | _ -> None
      in
      match fits with
      | Some (tyname, false) ->
          raise
            (Type_error_at
               ( Tree.loc_of node,
                 "数値リテラルのパターン " ^ Lexer.show_number n ^ " は " ^ tyname
                 ^ " の範囲を超えるので、どの値にも一致しません" ))
      | _ -> ())
    pats

(* 言語にない数値型の名前。
   宣言のない名前として引いたときに、未知の型の診断に、使える数値型の案内を添える *)
let absent_numeric = [ "Int8"; "Int16"; "UInt8"; "UInt16"; "UInt32"; "UInt64"; "Float32" ]

(* 未束縛の変数の診断。
   scoped が Some のときは、名前が module のスコープで解決済みなのに、解決先が環境にない。
   同じ module の中で後ろに宣言される値を、修飾なしで参照したときにそうなる。
   このときは修飾名を案内しないメッセージにする。
   scoped が None で、スコープの外に同じ名前の候補があるときだけ、修飾名を案内する *)
let unbound_value name scoped =
  match scoped with
  | Some _ -> type_error ("未束縛の変数: " ^ name)
  | None -> (
      (* 候補に挙げるのは pub の名前だけである。
         pub でない名前を案内すると、そのとおりに書いても可視性のエラーになる *)
      let pub_only qs =
        List.filter
          (fun q -> match Hashtbl.find_opt Decls.value_visibility q with Some v -> v.Decls.vis_pub | None -> true)
          qs
      in
      match pub_only (Decls.val_synonym_candidates (intern name)) with
      | [] -> type_error ("未束縛の変数: " ^ name)
      | qs ->
          type_error ("未束縛の変数: " ^ name ^ "(" ^ String.concat " か " (List.map display_of qs) ^ " と修飾してください)"))

(* パターンが構文上、反駁できない(どの値にも一致する)形なら真を返す。
   関数の引数、無名関数の引数、return 節のパターンの網羅性検査で、
   警告が出ないと分かっているパターンを第10章の検査キューに追加しないために使う。
   反駁できないパターンは、照合する値の型に値があればそのすべてに一致するので、
   検査キューに追加しても警告は出ない。
   照合する値の型が値を持たないときも、パターンが 1 つだけの項目について、
   検査キューは警告を出さない(第10章 §10.13)。
   どちらの場合も、真を返して追加を省いたときと、追加したときとで、警告の有無は変わらない。
   反駁できないパターンに偽を返しても、追加した先の検査キューが正しく判定するので、
   結果は変わらない。
   コンストラクタパターンには、コンストラクタが 1 つしかない型のものでも偽を返し、
   検査キューに任せる。
   操作節の引数のパターンが必ず一致するかどうかの検査(§11.24)は、この判定を使わず、
   第10章の missing で型を調べて判定する *)
let rec irrefutable_pat ((_, p) : T.pat) =
  match p with
  | T.PVar _ | T.PWildcard -> true
  | T.PAnnot (q, _) -> irrefutable_pat q
  | T.PRecord (fields, rest) ->
      List.for_all (fun (_, q) -> irrefutable_pat q) fields
      && (match rest with None -> true | Some rp -> irrefutable_pat rp)
  | T.PCtor _ | T.PVariant _ | T.PBool _ | T.PNumber _ | T.PText _ -> false

(* pub で @ を省略した宣言の本体の行。
   空の行へのリンクを持つセルで、型としての意味は TRowEmpty と同じである。
   perform や関数呼び出し(§11.12)がこの行と衝突したときに、単一化の一般的なメッセージではなく、
   pub の規則を明記したメッセージを出す。
   そのために、行がこのセルかどうかを、セルの物理的な同一性で判定する *)
let pub_pure_cells : tvar ref list ref = ref []

let new_pub_pure_row () =
  let r = ref (Link TRowEmpty) in
  pub_pure_cells := r :: !pub_pure_cells;
  TVar r

(* 行の末尾が pub_pure_cells のセルなら真を返す。
   handle や run の本体の行は、このセルの前にラベルを追加した形になるので、行の末尾までたどる。
   repr は使わない。
   repr はリンクをたどって空の行を返すので、どのセルだったかが分からなくなるからである *)
let rec is_pub_pure_row eff =
  match eff with
  | TVar r when List.memq r !pub_pure_cells -> true
  | TVar { contents = Link t } -> is_pub_pure_row t
  | TRowExtend (_, _, rest) -> is_pub_pure_row rest
  | _ -> false

let has_sub sub s =
  let n = String.length sub and m = String.length s in
  let rec go i = i + n <= m && (String.sub s i n = sub || go (i + 1)) in
  go 0

(* 単一化の失敗が行の単一化によるものなら真を返す。
   メッセージの部分文字列で判定するので、レコードやヴァリアントの行の失敗にも真を返す。
   エラーメッセージを言い換えるかどうかの判定に使う。
   引数の型の不一致まで、sample.kel §9 のエフェクト行の規則の説明に言い換えないためである。
   pub の言い換え(§11.12)、行が空の位置の言い換え(§11.12)、
   newtype のフィールドの言い換え(§11.18)、
   インスタンスメソッドの純粋性の言い換え(§11.38)が共通に使う *)
let row_failure msg =
  let has = has_sub in
  has "行型ではありません" msg || has "スコープ付きの型" msg || has "ラベル " msg || has "は注釈で固定された行変数" msg

(* 単一化の失敗が、スコーレム定数がスコープの外に漏れたことによるものなら真を返す。
   pub の言い換えのうち、呼び出し先の行の単一化(§11.12)は、この失敗を言い換えない。
   pub で @ を省略した本体の行は空の行で、スコーレム定数を含まない。
   その位置で漏れが起きるのは、本体の中で作ったスコーレム定数を、
   外側の単相の型変数に入れようとしたときである。
   run の本体の行に入っているヒープのラベルが、その例である。
   この失敗の原因は本体がエフェクトを起こすことではないので、pub の規則のメッセージにはしない *)
let escape_failure msg = has_sub "がスコープの外に漏れています" msg

(* 型の中に、閉じた行を書いた位置があれば真を返す。
   数えるのは、最も外側のエフェクト行が閉じている矢印と、
   型引数に書いた閉じた行(`Cb[{}]` の `{}`)である。
   入れ子の位置にあるものも数える。
   newtype のフィールドの言い換え(§11.18)が、言い換えの条件に使う。
   フィールドの型は宣言から作った型スキームで、型パラメータは Generic の変数である。
   型パラメータの位置は、閉じた行を書いた位置として数えない。 *)
let closed_row_arg t =
  match repr t with
  | TRowEmpty -> true
  | TRowExtend _ -> (match snd (row_fields t) with TRowEmpty -> true | _ -> false)
  | _ -> false

let rec has_closed_arrow ty =
  match repr ty with
  | TArrow (args, ret, eff) ->
      (match snd (row_fields eff) with TRowEmpty -> true | _ -> false) || has_closed_arrow args || has_closed_arrow ret
  | TCon (_, tys) -> List.exists (fun t -> closed_row_arg t || has_closed_arrow t) tys
  | TApp (f, a) -> has_closed_arrow f || has_closed_arrow a
  | TRecord r | TVariant r -> has_closed_arrow r
  | TRowExtend (_, f, rest) -> has_closed_arrow f || has_closed_arrow rest
  | TRowEmpty | TVar _ -> false

(* 呼び出しの実引数の個数を返す。
   実引数の並びは、ラベル _item の RecordExtend を連ねた式である。
   ラベル付きの引数を含むときは None を返す *)
let rec args_arity ((_, e) : T.exp) =
  match e with
  | T.RecordEmpty -> Some 0
  | T.RecordExtend (rest, l, _) when l = "_item" -> Option.map succ (args_arity rest)
  | _ -> None

(* 実引数の並びと仮引数の行がどちらも _item だけでできていて、個数が違えば、
   実引数を精緻化する前に、個数の不一致として報告する。
   そのため、実引数の中に別の型エラーがあっても、個数の不一致が先に報告される *)
let check_call_arity what arg params =
  match (args_arity arg, Unify.item_arity params) with
  | Some n, Some m when n <> m ->
      type_error
        ("引数の個数が一致しません: " ^ what ^ " " ^ string_of_int m ^ " 個の引数を取りますが、" ^ string_of_int n
       ^ " 個を渡しています")
  | _ -> ()

(* perform の引数と resume の引数の検査で、期待型の矢印の行が空のときに、
   行の不一致の報告に添えるメッセージ(§11.19)。
   操作の型は型パラメータを持たないので、矢印の行が空になるのは、
   型エイリアスを展開した後の操作の型に @ {} と書いたか、@ を省略したときである。
   @ P と書いても、P が空の行のエイリアスなら @ {} と同じになる *)
let op_row_note what =
  "(" ^ what
  ^ "が求める関数の行は空 = 純粋です。操作の型の矢印は書いたとおりに読み、@ の省略は @ {} と読みます。エフェクトを起こす関数を通すなら、操作の型のその矢印に @ で行を書いてください。§9)"

(* 矢印の最も外側のエフェクト行が閉じていれば、行の末尾を新しい行変数に替えて行を開く。
   使用時に行を開く規則(§11.26)の実装である。
   名前で参照した関数の型(§11.11)と、呼び出し先の関数の型(§11.12)に適用する。
   開いてから単一化するので、閉じた行の関数を、その行のラベルを含むどの行の位置でも使える。
   閉じた行は本体が起こすエフェクトの上限なので、行の末尾を開いても起こすエフェクトは増えず、
   健全である。
   行変数で終わる行と、矢印でない型はそのまま返す。
   矢印を新しく作り直して返すので、Tree.set_ty より前に呼ぶ。
   追加した行変数は opened_rows に記録し、reclose_opened_tail が使う *)
let opened_rows : tvar ref list ref = ref []

let open_closed_arrow level ty =
  match repr ty with
  | TArrow (a, r, e) -> (
      let _, tail = row_fields e in
      match repr tail with
      | TRowEmpty ->
          let v = new_row_var level in
          (match v with TVar rv -> opened_rows := rv :: !opened_rows | _ -> ());
          TArrow (a, r, row_append e v)
      | _ -> ty)
  | _ -> ty

(* 一般化しない束縛の終わりに呼ぶ。
   束縛の型の最も外側のエフェクト行の末尾が未束縛の行変数で、そのレベルが lvl 以上であり、
   opened_rows に記録した行変数のどれかと同じ変数であれば、空の行と単一化して閉じた行に戻す。
   open_closed_arrow は、その使用のためだけに行変数を追加する。
   何とも単一化されなかった行変数は、閉じたままの行と同じ意味である。
   戻さないと、束縛の行が、最初の使用で決まる弱い行変数になり、
   その束縛を、行の違う 2 つの位置で使えなくなる。
   行の末尾が、この束縛より外側のレベルの行変数と単一化されているときは戻さない。
   戻すと、外側の束縛の行を空に決めてしまうからである *)
let reclose_opened_tail lvl ty =
  match repr ty with
  | TArrow (_, _, e) -> (
      let _, tail = row_fields e in
      match repr tail with
      | TVar r -> (
          match !r with
          | Unbound i
            when i.vlevel >= lvl && List.exists (fun rv -> match repr (TVar rv) with TVar r' -> r' == r | _ -> false) !opened_rows ->
              Unify.unify (TVar r) TRowEmpty
          | _ -> ())
      | _ -> ())
  | _ -> ()

(* 期待型が矢印のときだけ、推論した型の閉じた行を開く。
   関数を値として渡す位置で行を開く規則(§11.26)の実装である。
   関数型を要求する位置、つまり検査モードから推論モードに切り替える分岐、返り値の注釈、
   値束縛の注釈が使う *)
let subsume_closed level ty expected = match repr expected with TArrow _ -> open_closed_arrow level ty | _ -> ty

(* 束縛の最も外側の矢印に @ が書かれていれば真を返す。
   pub で先頭の矢印の @ を省略した値束縛について、初期化式と注釈の単一化の失敗を
   pub の規則のメッセージに言い換えるかどうかの判定に使う(§11.28、§11.29)。
   関数束縛では lb_eff を調べる。
   値束縛では、注釈の最も外側が矢印の型の式なら、その @ を調べる。
   最も外側が矢印の型の式でない注釈(型エイリアスなど)では、
   展開した先の矢印を入れ子の矢印として読む。
   その矢印で省略した @ は、pub の規則によらず、初めから @ {} である。
   そこで、この形には @ が書かれているものとして真を返し、言い換えない *)
let outer_eff_written (b : T.let_binding') =
  match b.T.lb_params with
  | Some _ -> b.T.lb_eff <> None
  | None -> ( match b.T.lb_ret with Some (_, T.EArrow (_, _, eff)) -> eff <> None | Some _ -> true | None -> false)

(* pub で先頭の矢印の @ を省略した値束縛の、注釈の型と初期化式の型を単一化する(§11.28、§11.29)。
   注釈の先頭の矢印の行は空の行である。
   初期化式の型も矢印なら、引数と返り値を先に単一化し、最も外側の行どうしを最後に単一化する。
   pub の規則を明記したメッセージにするのは、最も外側の行どうしの単一化の失敗だけである。
   引数、返り値、入れ子の矢印の行の失敗は other に渡す。
   レコードのフィールドやヴァリアントのケースの失敗も、エフェクト行の失敗と同じ
   `ラベル X がありません` というメッセージになり、メッセージからは区別できないので、
   単一化を分けて行う。
   単一化する型の組と順序は、Unify.unify の矢印どうしの分岐(§8.7)と同じである。
   引数の個数を比較する方法と、その報告に示す 2 つの型も同じである *)
let unify_pub_value_annot vty body ~other =
  match (repr vty, repr body) with
  | (TArrow (p1, r1, e1) as ta), (TArrow (p2, r2, e2) as tb) ->
      (try
         Unify.check_arity ta tb p1 p2;
         Unify.unify p1 p2;
         Unify.unify r1 r2
       with Type_error msg -> other msg);
      (try Unify.unify e1 e2
       with Type_error msg ->
         type_error ("pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: " ^ msg ^ ")"))
  | _ -> ( try Unify.unify vty body with Type_error msg -> other msg)

(* 注釈の中の矢印のうち、@ を省略したものを探す。
   pub の完全注釈検査、つまり check_pub_annots と、§11.31 の pub newtype のフィールドの検査が使う。
   パス 1c が登録する前方参照のためのシグネチャは、先頭の矢印だけを調べる別の判定を使う(§11.36)。

   エイリアスは展開して読むものなので、注釈に書いたエイリアスの本体の矢印も、
   注釈の中の矢印として数える。
   数えなければ、矢印をエイリアスにするだけで、この検査を回避できる。
   sample.kel §9 も、型エイリアスを展開した矢印を入れ子の矢印に数える(sample.kel:488、:500)。
   エイリアスの本体の名前は、エイリアスを宣言した位置で解決する。
   そこで、本体を調べる間は、§11.5 の expand_alias と同じく、
   現在の単位と module を宣言の位置のものに切り替え、
   エイリアスのパラメータを、同じ名前のエイリアスを隠す名前として扱う。
   型引数は、エイリアスを使う位置で、注釈に直接書いた型として調べる。
   本体がパラメータを使うかどうかによらず調べるので、展開すると消える型引数の矢印も数える。
   束縛の型パラメータと、外側で束縛した型パラメータ(tparams)は、§11.3 の優先順位のとおり、
   同じ名前のエイリアスを隠す。
   EffectRow エイリアスの本体は調べない。
   エフェクト行の中は、注釈に直接書いたものも調べないからである。

   返り値は次の 3 通りである。

   - @ を省略した矢印が見つからなければ None を返す。
   - 注釈に直接書いた矢印なら Some None を返す。
   - エイリアスの本体の矢印なら、
     その矢印を本体に書いたエイリアスの名前を入れて Some (Some 名前) を返す。

   再帰するエイリアス、引数の個数が合わないエイリアスの使用、使う位置から見えないエイリアスでは、
   エイリアスの本体を調べず、本体には省略した @ がないものとして扱う。
   その場合も型引数は調べる。
   これらの診断は、後で注釈を精緻化するときに §11.3 と §11.5 が出す。 *)
type pub_scope = {
  ps_module : string option;
  ps_unit : Decls.unit_id;
  ps_tparams : string list;
  ps_alias : string option;
}

let rec unwritten_effect ~expanding sc ((_, te) : T.type_exp) =
  let nested t = unwritten_effect ~expanding sc t in
  let first f l = List.find_map f l in
  let lookup_alias name =
    let saved = !Decls.current_module and saved_unit = !Decls.current_unit in
    Decls.current_module := sc.ps_module;
    Decls.current_unit := sc.ps_unit;
    Fun.protect
      ~finally:(fun () ->
        Decls.current_module := saved;
        Decls.current_unit := saved_unit)
      (fun () ->
        let oid = Decls.resolve_con (intern name) in
        match (Hashtbl.find_opt Decls.aliases oid, Hashtbl.find_opt Decls.con_visibility oid) with
        | _, Some v when not (Decls.visible_here v) -> None
        | Some info, _ -> Some (oid, info)
        | None, _ -> None)
  in
  let alias_body li nargs =
    match li with
    | LongId [ n ] when List.mem n sc.ps_tparams -> None
    | _ -> (
        match lookup_alias (show_long_id li) with
        | None -> None
        | Some (_, info) when info.Decls.al_kind = Some "EffectRow" -> None
        | Some (oid, _) when List.mem oid expanding -> None
        | Some (_, info) when nargs <> List.length info.Decls.al_params -> None
        | Some (oid, info) ->
            let sc' =
              {
                ps_module = info.Decls.al_module;
                ps_unit = info.Decls.al_unit;
                ps_tparams = List.map (fun (tp : type_param) -> tp.tp_name) info.Decls.al_params;
                ps_alias = Some (display_of oid);
              }
            in
            unwritten_effect ~expanding:(oid :: expanding) sc' info.Decls.al_body)
  in
  match te with
  | T.EArrow (params, ret, eff) -> if eff = None then Some sc.ps_alias else first nested (params @ [ ret ])
  | T.EIdent li -> alias_body li 0
  | T.EApply ((_, T.EIdent li), args) -> (
      match first nested args with Some _ as r -> r | None -> alias_body li (List.length args))
  | T.EApply (f, args) -> first nested (f :: args)
  | T.EBraceRow (elems, ext) -> (
      match
        first (function T.BField (_, t) -> nested t | T.BLabel (_, ts) -> first nested ts) elems
      with
      | Some _ as r -> r
      | None -> Option.bind ext nested)
  | T.EVariantCase (_, Some t) -> nested t
  | T.EUnion ts -> first nested ts
  | T.EVariantCase (_, None) | T.EHole -> None

let pub_scope tparams =
  { ps_module = !Decls.current_module; ps_unit = !Decls.current_unit; ps_tparams = tparams; ps_alias = None }

(* 同じ名前のエイリアスを隠す型パラメータの名前を返す。
   束縛自身の型パラメータと、外側の束縛やインスタンスの型パラメータである *)
let pub_tparams (env : env) (tps : type_param list) =
  List.map (fun (tp : type_param) -> tp.tp_name) tps @ List.map fst (SMap.bindings env.types)

(* pub の完全注釈検査の診断を出す。
   引数は unwritten_effect の結果で、エイリアスの本体の矢印なら、
   メッセージにエイリアスの名前を添える *)
let pub_effect_error what = function
  | None -> ()
  | Some None -> type_error (what ^ "には完全な型注釈が必要です(注釈の中の矢印に @ がありません)")
  | Some (Some a) -> type_error (what ^ "には完全な型注釈が必要です(型エイリアス " ^ a ^ " の本体の矢印に @ がありません)")

(* pub の完全注釈検査。
   引数と返り値に注釈があるだけでなく、注釈の中の矢印にも @ が必要である。
   入れ子の矢印で省略した @ は @ {} と読むので、この規則は健全性のためのものではない。
   sample.kel §13(sample.kel:825-831)が読みやすさのために定めた規則である。
   公開 API では、純粋を意図したのか書き忘れたのかを、読者が区別できなければならない。
   pub newtype のフィールド(§11.31)にも同じ規則を適用する(sample.kel:828-829)。

   値束縛(引数リストを持たない `let`)の注釈の先頭の矢印は、この「中の矢印」に入らない。
   先頭の矢印は束縛の最も外側の矢印だからである。
   sample.kel §9 は、最も外側の矢印が指すものを、
   関数束縛と値束縛に分けて定めている(sample.kel:486-487)。
   sample.kel §13 は入れ子の矢印の `@` も省略できないと定め(sample.kel:825)、
   最も外側の矢印での省略には別の意味を与えている(sample.kel:830-831)。
   推論に任せず `@ {}` と読み、本体に純粋であることを要求するという意味である。
   値束縛の先頭の矢印も同じ扱いであることは、sample.kel §9 の表が定めている(:494)。

   値束縛の注釈の最も外側が矢印なら、引数と返り値だけを `unwritten_effect` に渡し、
   その矢印の `@` の有無は調べない。
   最も外側が矢印でない注釈(型エイリアスなど)には最も外側の矢印がないので、注釈をそのまま渡す。
   エイリアスを展開して先頭に現れた矢印は、
   最も外側の矢印ではなく入れ子の矢印である(sample.kel:488)。
   関数束縛の `lb_ret` は返り値の型、つまり入れ子の位置なので、すべての矢印に `@` が必要である。

   先頭の矢印を調べなくてよいのは、省略した `@` の意味を、この関数の呼び出し元が決めるからである。
   `let` の値束縛(§11.28)も `let rec` の値束縛(§11.29)も、`pub` で先頭の矢印の `@` を省略すれば
   `@ {}` と読み、本体が純粋であることを検査する。 *)
let check_pub_annots ~tparams ~params ~ret =
  let sc = pub_scope tparams in
  let what = "pub な宣言" in
  (match params with
  | Some ps ->
      List.iter
        (fun ((_, p) : T.pat) ->
          match p with
          | T.PAnnot (_, te) -> pub_effect_error what (unwritten_effect ~expanding:[] sc te)
          | _ -> type_error "pub な宣言には完全な型注釈が必要です(引数に型注釈がありません)")
        ps
  | None -> ());
  match ret with
  | None -> type_error "pub な宣言には完全な型注釈が必要です(返り値の型注釈がありません)"
  | Some te -> (
      let check t = pub_effect_error what (unwritten_effect ~expanding:[] sc t) in
      match (params, te) with
      | None, (_, T.EArrow (ps, r, _)) -> List.iter check (ps @ [ r ])
      | _ -> check te)

(* ## 11.3 型の式の精緻化

   `elab_type` は、ソースに書いた型の式を第1章の内部型に変換する。
   名前解決、エイリアスの展開、カインドの検査をここで同時に行い、
   カインド検査のための専用のパスは持たない。
   型構成子の適用では、宣言されたパラメータのカインドに従って型引数の読み方を選び、
   読んだ結果のカインドを照合する(`elab_con_args`)。
   行カインドのパラメータの位置では、型引数をエフェクト行として読む。
   そのため、`Callback[{}]` の `{}` は空の行、`Callback[{Print}]` はラベル 1 つの閉じた行、
   `Callback[{Print extends E}]` は開いた行になる。
   それ以外の位置では型として読み、`{}` は Unit になる。
   `Box[E]` に行変数を渡すと、宣言の位置で
   `Type を期待しましたが ς1 は Row です` というエラーになる(`test/kinds.t` の kinderr)。
   使用点まで遅れて、`bind` が内部名を並べたエラーを出すことはない。

   型引数の読み方をカインドで選ぶのは、sample.kel §6 が定める規則である(sample.kel:252-255)。
   この規則がないと、`pub let mk(): Callback[{}]` が書けない。
   sample.kel §13 は `pub` の型注釈を完全に書くことを要求するので、
   `Callback[{}]` と書く手段がなければ、`Callback` を公開 API に出せなくなる。
   同じ `{}` が、`Callback[{}]` では空の行、`Box[{}]` では Unit になる。
   この違いは型の表示では区別できず、値を入れて初めて分かる(`test/kinds.t` の rowarg)。

   読み方を選ぶ判定には `kind_repr` の構造の一致を使い、照合には `same_kind` を使う。
   カインドは原則として `same_kind` で比較する(第1章 §1.6)が、読み方を選ぶ判定はその例外である。
   `same_kind` は未確定のカインド変数 `KVar` を比較対象のカインドに決めるので、判定に使うと、
   未確定のパラメータがすべて `Row` に固定されてしまう。
   同じ理由で `same_kind` を避ける箇所は、ほかに 3 つある。
   型引数の照合(`arg_kind_ok`)と、レコード行の `extends` の右とヴァリアント型の末尾は、
   型変数への適用だけを構造の一致で調べる。
   §11.6 の `elab_eff` の最後の分岐は、読んだ結果をすべて構造の一致で調べる。
   照合のほうは、`KVar` を決めてよい。
   パス 1b の中(相互再帰する newtype が互いを参照する形)では、
   照合が `KVar` を決めることで、カインドが宣言から宣言へ伝わる。

   名前は次の優先順位で引く。

   1. `env.types` にある名前。型パラメータとリージョン変数で、これが最優先である。
      内側の `[A]` は外側の型構成子 `A` を隠す。
   2. 型エイリアス。あれば、その場で展開する(§11.5)。
   3. 宣言表の型構成子。カインドを引いて引数の個数を照合し、
      パラメータのカインドに従って引数を読み、照合する。

   どれにもなければ未知の型である。
   スコープの外の module に同名の pub の型があれば、引数の有無によらず修飾名を案内する
   (`unknown_type`。`test/visibility.t` の vis4b と vis4c)。

   `elab_type` は、型構成子とエイリアスの名前を、どの分岐でも `Decls.resolve_con` を通して引く。
   module の平坦化(§11.42)が作る別名の表を引くためである。
   `module Parser` の中で `Parser` と書いても、外から `Parser.Parser` と書いても、
   同じ oid になる。
   §11.6 の `elab_eff` も、EffectRow エイリアスの名前を `Decls.resolve_con` を通して引く。
   ただし、module の中の宣言が EffectRow エイリアスでないときに、
   グローバルな名前でもう一度引く点が、型の位置と違う。

   `EApply` で適用される側が型パラメータのときだけは、扱いが違う。
   `tapp` で適用を組み立て、カインドは使用時に `kind_of` と `drop_arrows` が決める。
   高カインド型(`F[_]`)の実装は、ほぼこれだけである。
   型レベルのλを持たないので、`f a ~ List Int` は `f ~ List, a ~ Int` に構造的に分解でき、
   単一化は一階のままで済む。
   高カインド型の実装にほかに必要なのは、定義域の照合だけである。
   `TCon` の適用は宣言表のカインドと照合するが、
   `TApp` の適用は、適用される側のカインド(`kind_of` が決めた `KArrow` の左)と照合する。
   `drop_arrows` は定義域を捨てるので、定義域はここでしか照合できない。
   `let f[F[_], E](x: F[E], g: () => Unit @ E)` では、
   `F[E]` が `E` のカインドを Type に確定させるので、
   宣言は次の `@ E` でエラーになる。
   診断の位置が 2 番目の使用点になるのは、`F[E]` の時点では `E` のカインドがまだ決まっておらず、
   照合に通るからである(`test/kinds.t` の hkt)。

   `Int8` のような言語にない数値型の名前(`absent_numeric`)は、宣言のない名前として引く。
   ユーザが同じ名前の型を宣言していればその型になり、宣言がなければ未知の型である。
   型引数のない名前を引く分岐では、未知の型の診断に、使える数値型の一覧を添える。
   ユーザがほかの言語にある幅の型のつもりで書いたときに、原因が分かるようにするためである。
   型引数を付けた名前(`Int8[Int32]`)と、インスタンスの対象の型に書いた未知の型構成子の診断には、
   一覧を添えない。

   値の型の位置で読んだ型は、カインドが `Type` であることも照合する。

   **値の型の位置**：矢印の引数と返り値、レコードのフィールド、タプルの要素、
   ヴァリアントのペイロード、
   および引数の注釈、返り値の注釈、値束縛の注釈。

   照合は `elab_value_type` が `elab_type` の結果に対して行う。
   引数と返り値の注釈も、この `elab_value_type` で読む。
   引数リストを持たない値束縛の注釈だけは `elab_value_type_outer` で読む。
   こちらは、最も外側の矢印で省略した `@` を行変数にする `elab_type_outer` で読んでから、
   同じ照合を行う。
   合わなければ、`check_value_kind` が型エラーにする。
   メッセージは `<名詞句>のカインドが Type ではありません: <型> :: <カインド>` である。
   この照合がないと、カインドを調べるのは newtype のフィールドの最も外側の型の照合(§11.31)だけになり、
   1 段でも内側の位置にある行カインドの型パラメータや `EffectRow` エイリアスが、
   値の型のまま宣言表に入る。
   `newtype Bad2[E] = Bad2((E, Int32), () => Unit @ E)` がその例である。
   値の位置に行がある型は、値を作る手段がない。
   そのため診断が使用点まで遅れ、使用点がなければ診断が出ない。

   照合には `same_kind` を使う。
   型パラメータだけを書いた位置(`let f[A](x: A)`)では、`A` のカインドはまだ `KVar` である。
   このとき照合は、`A` が値の位置に現れたことから、`A` のカインドを `Type` に決める。
   この副作用が診断の位置を決める。
   同じパラメータを行と値の両方で使う宣言では、先に読んだ側がカインドを決め、
   2 番目の使用点でエラーになる(§11.4)。

   メッセージの先頭の名詞句は位置ごとに違うので、`check_value_kind` の引数として渡す。
   名詞句は検査する型を指し、「… の型」か「型注釈」で終わる。
   newtype のフィールドの最も外側の型の検査もこの補助関数を呼び、
   名詞句にコンストラクタ名を添えて `コンストラクタ X のフィールドの型` とする(§11.31)。
   `test/kinds.t` の valkind / annotkind / rowval / hktval / fieldkind / fieldalias が、
   8 種類の名詞句とエラーになる位置をゴールデンテストで固定している。 *)

(* 値の型の位置のカインドの照合と、エフェクト位置のカインドの照合が共通に使う診断。
   what は、検査する型を指す名詞句で、「… の型」か「型注釈」で終わる。
   カインドが未確定の KVar のときは、メッセージにカインドを添えない。
   KVar を ?k997 の形で表示すると、その番号がプレリュードの行数で変わるからである。
   値の型の位置の照合は same_kind で行うので、KVar は Type に決まって照合に通り、
   この分岐は実行されない。
   この分岐が実行されるのは、構造の一致で判定するエフェクト位置だけだが、
   メッセージを作る箇所を 1 つにまとめている *)
let kind_error what ~expected ty =
  let k = kind_repr (Unify.kind_of ty) in
  let annot = match k with KVar _ -> "" | _ -> " :: " ^ show_kind k in
  type_error (what ^ "のカインドが " ^ expected ^ " ではありません: " ^ Show.show ty ^ annot)

(* 型のカインドが未確定の KVar なら真を返す。型変数への適用 F[E] のカインドがそうなる *)
let unresolved_kind ty = match kind_repr (Unify.kind_of ty) with KVar _ -> true | _ -> false

let check_value_kind what ty = if not (same_kind (Unify.kind_of ty) KStar) then kind_error what ~expected:"Type" ty

(* カインドの注釈のないエイリアスと : Type のエイリアスの本体は、行であってはならない。
   本体が行でパラメータのないエイリアス(type Q = P)を使うと、
   値の型の位置ではカインドの照合で、エフェクト位置では Type エイリアスを書いたことでエラーになる。
   パラメータを持つエイリアス(type Q[E] = P[E])は、この検査がなければ、
   @ Q[E] の位置で展開後のカインドが照合に通る。
   しかしそれでは、Type エイリアスを行の位置に書けたことになる。
   どちらも使用点を待たずに宣言の位置でエラーにし、メッセージで : EffectRow の注釈を案内する。
   高カインドの本体(type Q[F[_]] = F)は App[Q[F]] の形で使えるので、エラーにしない。
   カインドは same_kind で照合せず kind_repr で調べるだけなので、
   未確定のカインド変数を決めてしまうことはない *)
let check_alias_body_kind name ty =
  match kind_repr (Unify.kind_of ty) with
  | KRow ->
      type_error
        ("Type エイリアス " ^ name ^ " の本体のカインドが Type ではありません: " ^ Show.show ty
       ^ " :: Row(行に名前を付けるには : EffectRow を付けてください)")
  | _ -> ()

(* newtype とエイリアスの本体を試しに精緻化している間(§11.31、§11.39)だけ真になる。
   試しに精緻化した結果と診断は捨て、パラメータのカインドだけを決める。
   型引数を型として読むか行として読むかを決める elab_con_args と expand_alias がこれを調べ、
   型としても行としても読める記述をパラメータとの照合に使わない *)
let speculating = ref false

(* 非修飾名 n が、エイリアスの表にも宣言表にもなかったときの診断メッセージを作る。
   メッセージは引数の有無によらず同じである(W と W[A] の両方)。
   スコープの外の module に同名の型があれば、修飾名の候補を添える。
   案内するのは pub の型だけである。
   pub でない型は、案内のとおりに修飾しても可視性の検査でエラーになる。
   引数の個数は調べないので、修飾した後に個数が合わなければ、修飾名の分岐がそれを報告する。
   候補がなく、n が言語にない数値型の名前(absent_numeric)なら、使える数値型の一覧を添える *)
let unknown_type n oid =
  match
    List.filter
      (fun q -> match Hashtbl.find_opt Decls.con_visibility q with Some v -> v.Decls.vis_pub | None -> true)
      (Decls.con_synonym_candidates oid)
  with
  | _ :: _ as cands -> "未知の型: " ^ n ^ "(" ^ String.concat " か " (List.map display_of cands) ^ " と修飾してください)"
  | _ ->
      if List.mem n absent_numeric then "未知の型: " ^ n ^ "(数値型は Int32、Int64、Float64 だけです)"
      else "未知の型: " ^ n

let rec elab_type env level ~expanding ?(outer = false) (((_, te) as t) : T.type_exp) : ty =
  (* 再帰呼び出しごとに at_node で囲む。最初の呼び出しだけを囲むと、
     入れ子の注釈のどこでエラーになっても、注釈全体の先頭が診断の位置になってしまう *)
  at_node t @@ fun () ->
  match te with
  | T.EIdent (LongId [ n ]) -> (
      match SMap.find_opt n env.types with
      | Some t -> t
      | None ->
          let oid = Decls.resolve_con (intern n) in
          Decls.check_con_visible oid;
          (match Hashtbl.find_opt Decls.aliases oid with
          | Some info -> expand_alias env level ~expanding info []
          | None ->
              if Hashtbl.mem Decls.con_kinds oid then (
                match Decls.con_kind oid 0 with
                | KStar -> TCon (oid, [])
                | _ -> type_error ("型構成子 " ^ n ^ " には型引数が必要です"))
              else type_error (unknown_type n oid)))
  | T.EIdent li -> (
      (* 平坦化した module の型を修飾名で参照する形(Parser.Parser など)。
         修飾名でもエイリアスの表を引く(M.A の形) *)
      let oid = Decls.resolve_con (intern (show_long_id li)) in
      Decls.check_con_visible oid;
      match Hashtbl.find_opt Decls.aliases oid with
      | Some info -> expand_alias env level ~expanding info []
      | None ->
          if Hashtbl.mem Decls.con_kinds oid then (
            match Decls.con_kind oid 0 with
            | KStar -> TCon (oid, [])
            | _ -> type_error ("型構成子 " ^ show_long_id li ^ " には型引数が必要です"))
          else type_error ("未知の型: " ^ show_long_id li))
  | T.EApply ((_, T.EIdent (LongId comps)), args) when List.length comps > 1 -> (
      let oid = Decls.resolve_con (intern (String.concat "." comps)) in
      Decls.check_con_visible oid;
      match Hashtbl.find_opt Decls.aliases oid with
      | Some info -> expand_alias env level ~expanding info args
      | None ->
          if Hashtbl.mem Decls.con_kinds oid then (
            let k = Decls.con_kind oid (List.length args) in
            let rec arity k = match kind_repr k with KArrow (_, r) -> 1 + arity r | _ -> 0 in
            if arity k <> List.length args then type_error ("型構成子 " ^ String.concat "." comps ^ " の引数の個数が不正です")
            else TCon (oid, elab_con_args env level ~expanding (String.concat "." comps) k args))
          else type_error ("未知の型: " ^ String.concat "." comps))
  | T.EApply ((_, T.EIdent (LongId [ n ])), args) -> (
      match SMap.find_opt n env.types with
      | Some t ->
          (* 高カインドの型変数への適用。カインドは使用時に kind_of と drop_arrows が決める。
             drop_arrows は定義域を捨てるので、定義域はここでしか照合できない。
             acc は tapp に渡す前の適用される側の型で、acc' は tapp の結果である。
             適用される側が TCon なら、tapp は引数を TCon の引数の末尾に加える(§1.7)。
             kind_of acc' を先に呼ぶのは、acc のカインドがまだ KVar のときに、drop_arrows に
             そのカインドを KArrow(新しい変数, 新しい変数)に決めさせるためである。
             その後で kind_of acc を調べると、定義域を取り出せる *)
          List.fold_left
            (fun acc a ->
              let at = elab_type env level ~expanding a in
              let acc' = tapp acc at in
              ignore (Unify.kind_of acc');
              (match kind_repr (Unify.kind_of acc) with
              | KArrow (d, _) ->
                  if not (same_kind d (Unify.kind_of at)) then
                    type_error
                      ("型引数のカインドが一致しません: " ^ show_kind d ^ " を期待しましたが " ^ Show.show at ^ " は "
                     ^ show_kind (Unify.kind_of at) ^ " です")
              | _ -> ());
              acc')
            t
            (List.map (fun a -> check_no_hole a) args)
      | None -> (
          let oid = Decls.resolve_con (intern n) in
          Decls.check_con_visible oid;
          match Hashtbl.find_opt Decls.aliases oid with
          | Some info -> expand_alias env level ~expanding info args
          | None ->
              if Hashtbl.mem Decls.con_kinds oid then (
                let k = Decls.con_kind oid (List.length args) in
                let rec arity k = match kind_repr k with KArrow (_, r) -> 1 + arity r | _ -> 0 in
                let expected = arity k in
                if expected <> List.length args then
                  type_error (Printf.sprintf "型構成子 %s の引数は %d 個必要です(%d 個与えられました)" n expected (List.length args))
                else TCon (oid, elab_con_args env level ~expanding n k args))
              else type_error (unknown_type n oid)))
  | T.EApply _ -> type_error "型適用の頭は型名でなければなりません"
(* ## 11.4 矢印、レコード行、ヴァリアント型

   矢印 `(A, B) => R @ E` は `TArrow (引数レコード, 返り値, エフェクト行)` になる。
   引数は閉じた `_item` 行のレコードなので、
   `(A) => R` と `(A, B) => R` は行の長さが違い、別の型になる。

   `@` を省略した矢印の意味は、矢印の**位置**で決まる(sample.kel §9、sample.kel:472-504)。

   | 矢印の位置 | 書いた行(`@ {}` を含む) | `@` を省略 |
   |---|---|---|
   | 束縛の最も外側(`let` / `pub let` / `extern` / クラスメソッド) | 書いたとおり。本体のエフェクトの上限になる | `let` は推論、`pub let` とクラスメソッドは `@ {}`、C リンケージの `extern` は `@ Blocking`、prim リンケージの `extern` は新しい行変数(§11.26) |
   | 入れ子(引数の型、返り値の中、newtype のフィールド、レコード型のフィールド、タプル型の要素、effect の操作型の引数、エイリアスの展開先) | 書いたとおり | `@ {}`(純粋) |

   どちらの位置でも、閉じた行は書いたとおりに型になり、
   その型の関数を使うときに行の末尾を開く(使用時に行を開く規則。§11.26)。

   表の 1 行目の「束縛の最も外側の矢印」がどれを指すかは、束縛の書き方で変わる。
   関数束縛 `let f(x: T): R @ E` では、返り値の後ろの `@` を指す。
   値束縛 `let k: (T) => R @ E = …` では、注釈そのものの先頭の矢印の `@` を指す。
   注釈の先頭が型エイリアスのときは最も外側の矢印がなく、エイリアスが展開する矢印を入れ子として読む
   (§11.5 の規則 4)。
   この 3 つは sample.kel §9 が定めている(sample.kel:486-488)。

   関数束縛の最も外側の矢印は、`elab_binding` が `TArrow` を直接組み立てるので、
   この関数では読まない。
   この関数が読む矢印のうち最も外側なのは、`elab_type_outer` を通して渡される 2 つの位置
   (クラスメソッドの型と、引数リストを持たない値束縛の注釈の先頭)だけで、残りはすべて入れ子である。
   そのため `EArrow` で省略した `@` は、`outer` が真のときだけ新しい行変数になり、
   それ以外は閉じた空の行 `TRowEmpty` になる。
   `pub` やクラスメソッドの規則に従って最も外側の省略を `@ {}` にするのは、この関数ではない。
   呼び出し元が表層の構文を調べて、行を `TRowEmpty` に置き換える(値束縛は §11.28、
   クラスメソッドは §11.33)。

   入れ子で省略した `@` を新しい行変数として読むと、newtype のフィールドに書いた `() => Int32` が
   どのエフェクトでも起こせるクロージャの型になり、
   エフェクトを起こすクロージャを純粋なクロージャとして取り出せてしまう。
   入れ子の省略は `@ {}` と読むので、この形は型エラーになる(`test/annot_rows.t` の launder)。
   入れ子に書いたラベル付きの行も、書いたとおり閉じた行として読む。
   入れ子の矢印に行を伝えたいときは、`newtype Callback[E] = Callback(() => Unit @ E)` のように、
   行変数を型パラメータに取る。

   表の 2 行目のうち、レコード型のフィールドとタプル型の要素は、
   sample.kel §9 の入れ子の矢印の一覧にも挙がっている(sample.kel:498-500)。
   レコード型のフィールドにも、矢印を括弧で囲まずに書ける。
   `{run: () => Unit}` が構文エラーになるのは矢印のせいではなく、
   `run` が予約語(§2.4)で、ラベルの位置に置けないからである。
   フィールド名を変えれば書け、省略した `@` はほかの入れ子と同じく `@ {}` になる
   (`test/annot_rows.t` の nestrec、`test/nonfeatures.t` の kwlabel)。

   `extends` の右には、行そのものとレコード型の 2 通りを書ける。
   レコード型なら、その行を取り出して、書いたフィールドの後ろにつなぐ。
   `{x: Int32 extends Point}` と書けるのはこのためで、`Point` の行が `x` の後ろに展開される。

   矢印、レコード行、ヴァリアントの 3 つの構文は、どれも値の型の位置を持つ(§11.3)。
   そこで読んだ型のカインドが `Type` でなければ、その位置でエラーにする。

   | 構文 | 値の型の位置 | 値の型の位置ではない部分 |
   |---|---|---|
   | 矢印 `(A, B) => R @ E` | 引数 `A` `B` と返り値 `R` | `@` の右の行 `E` |
   | レコード行 `{a: A}` | 各フィールドの型(`_item` ラベルはタプルの要素) | `extends` の右 |
   | ヴァリアント `#Tag(T)` | ペイロード `T`(診断では「積載」) | 縦棒で並べた要素そのもの(行かヴァリアント) |

   エラーになる位置は、読む順で決まる。
   レコードとタプルの要素は `List.fold_right` で右から読むので、
   `(() => Unit @ E, E)` では第 2 要素の `E` のカインドが先に `Type` に決まり、
   第 1 要素の `@ E` が `行カインドではない型パラメータです` のエラーになる(`test/kinds.t` の rowval3)。
   コンストラクタのフィールドは左から読むので(§11.31)、
   同じ形を `newtype Bad2[E] = Bad2((E, Int32), () => Unit @ E)` と書くと、
   エラーになるのは第 2 フィールドである。
   どちらも宣言の時点でエラーになる点は同じで、位置だけが違う。
   読む順はそろえていない。
   どちらも左から読むようにするには、行を組み立てる順序を変える必要がある。

   `|` で並べたヴァリアント型 `#Even | #Odd | R`(診断では「ヴァリアント和」と呼ぶ)は、
   各要素を行に変換して `row_append` で連結する。
   開いていてよいのは、末尾の要素だけである。
   途中に開いた行があると、連結後にどのラベルがどの行の末尾に属するのかが決まらない。
   閉じた要素どうしを連結すれば、結果も閉じる。
   閉じたヴァリアント型は、網羅性検査(第10章)が `case _` なしで網羅と判定できる。
   たとえば `report`(sample.kel:222-227)がそうである。

   `EHole`(`_`)は、インスタンスの対象の型(診断では「インスタンス頭」)の `List[_]` にだけ書ける。
   型の式の一般の位置に穴を許すと部分適用と同じ問題が起きるので、ここで拒否する。 *)

  | T.EArrow (params, ret, eff_opt) ->
      let param_tys = List.map (fun p -> elab_value_type env level ~expanding "矢印の引数の型" p) params in
      (* 省略した @ の意味は、矢印の位置で決まる(sample.kel §9)。
         入れ子の矢印(引数の型、返り値の中、newtype のフィールド、effect の操作型、
         型エイリアスが展開する矢印など、最も外側以外のすべて)の省略は @ {}(純粋)になる。
         最も外側の矢印(outer = true。クラスメソッドの型と、引数リストを持たない値束縛の
         注釈の先頭)の省略だけが、新しい行変数になる。
         再帰呼び出しはどれも outer を渡さないので、入れ子の矢印は outer = false で読む *)
      let eff =
        match eff_opt with
        | Some e -> elab_eff env level ~expanding e
        | None -> if outer then new_row_var level else TRowEmpty
      in
      TArrow (TRecord (closed_item_row param_tys), elab_value_type env level ~expanding "矢印の返り値の型" ret, eff)
  | T.EBraceRow (elems, ext) ->
      let tail =
        match ext with
        | None -> TRowEmpty
        | Some t -> (
            let tt = elab_type env level ~expanding t in
            match repr tt with
            | TRecord row -> row (* {x: T extends Point}: レコード型の行を後ろにつなぐ *)
            | TApp _ as t' when unresolved_kind t' ->
                (* 型変数への適用 F[E] の結果のカインドは未確定の KVar である。
                   same_kind で Row に決めず、§11.5 の arg_kind_ok と同じくエラーにする *)
                kind_error "extends の右の型" ~expected:"Row" t'
            | t' ->
                if Unify.kind_of t' = KRow || same_kind (Unify.kind_of t') KRow then t'
                else type_error "extends の右は行かレコード型でなければなりません")
      in
      let row =
        List.fold_right
          (fun elem acc ->
            match elem with
            | T.BField (l, t) ->
                let what = if l = "_item" then "タプルの要素の型" else "レコードのフィールド " ^ l ^ " の型" in
                TRowExtend (intern l, elab_value_type env level ~expanding what t, acc)
            | T.BLabel _ -> type_error "エフェクトラベルはこの位置(レコード型)では使えません")
          elems tail
      in
      TRecord row
  | T.EVariantCase (s, payload) ->
      let pty =
        match payload with None -> t_unit | Some t -> elab_value_type env level ~expanding ("ヴァリアント #" ^ s ^ " の積載の型") t
      in
      TVariant (TRowExtend (intern s, pty, TRowEmpty))
  | T.EUnion ts ->
      (* 各要素を行に変換して連結する。開いていてよいのは末尾の要素だけである *)
      let n = List.length ts in
      let rows =
        List.mapi
          (fun i t ->
            let is_last = i = n - 1 in
            match snd t with
            | T.EVariantCase (s, payload) ->
                let pty =
                  match payload with
                  | None -> t_unit
                  | Some t -> elab_value_type env level ~expanding ("ヴァリアント #" ^ s ^ " の積載の型") t
                in
                TRowExtend (intern s, pty, TRowEmpty)
            | _ -> (
                let tt = elab_type env level ~expanding t in
                match repr tt with
                | TVariant row ->
                    let _, tail = row_fields row in
                    if (not is_last) && repr tail <> TRowEmpty then type_error "ヴァリアント和の途中の要素は閉じていなければなりません"
                    else row
                | TApp _ as t' when unresolved_kind t' ->
                    (* 型変数への適用 F[E] は、extends の右と同じく構造の一致で調べる *)
                    kind_error "ヴァリアント和の末尾の型" ~expected:"Row" t'
                | t' ->
                    if same_kind (Unify.kind_of t') KRow then
                      if is_last then t' else type_error "ヴァリアント和の途中に行変数は置けません"
                    else type_error ("ヴァリアント和の要素になれない型です: " ^ Show.show t')))
          ts
      in
      let rec fold = function [] -> TRowEmpty | [ r ] -> r | r :: rest -> row_append r (fold rest) in
      TVariant (fold rows)
  | T.EHole -> type_error "_ はこの位置では使えません(インスタンス頭の List[_] 専用)"

(* ## 11.5 型エイリアスの展開

   型エイリアスは**透過**である。
   表に本体を保存しておき、使われるたびにその場で精緻化して展開する。
   展開後の型に、エイリアスから来たという情報は残らない。
   そのため、型は `IoError | ParseError` ではなく、展開後の行として表示される。

   透過なエイリアスには、次の 5 つの規則を課す。

   1. エイリアスは再帰できない。
   2. エイリアスは部分適用できない。
   3. パラメータには型クラスの制約を書けない。
   4. エイリアスが展開する矢印は、常に入れ子として読む。
   5. 型引数は、パラメータのカインドに合わせて読む。

   規則 1 は、展開中のエイリアス名の集合 `expanding` を引数として受け渡して守る。
   展開中の名前がもう一度現れたら、そこでエラーにする。
   透過な展開に再帰を許すと、展開が停止しないからである。

   規則 2 は、単一化の性質を保つための規則である。
   `type P[A] = (A, Int32)` を `P` 単体で書けるようにすると、それは実質的に型レベルのλになる。
   型レベルのλがあると、`f a ~ P Int` の最も一般的な解が 1 つに決まらなくなり
   (単一化が unitary、つまり最汎単一化子が 1 つに決まる性質を失い)、
   型推論は主要型を求められなくなる。
   そこで、引数の個数が合わないエイリアスの使用は、その場でエラーにする。
   部分適用の禁止は、`expand_alias` の中で引数の個数を比べる 1 か所で実装している。

   規則 3 を置くのは、エイリアスに値を作る箇所がないからである。
   エイリアスは透過なので、制約を検査できるのは型を書いた時点しかない。
   newtype のパラメータに制約を書けるようにすると、検査するのは値を作る時点になり、
   型を書いた時点で検査するエイリアスと食い違う。
   そこで、エイリアスと newtype のどちらのパラメータにも制約を書けない規則にしている。
   制約は関数とインスタンスの型パラメータに書く。
   規則 3 は、§11.39 のパス 1a が宣言の時点で検査する(`no_param_constraints`)。

   規則 4 により、`type Thunk = () => Unit` の省略した `@` は、
   `Thunk` を束縛の最も外側に書いても `@ {}` になる
   (sample.kel §9 は、型エイリアスを展開した矢印を入れ子の側に挙げている)。
   `expand_alias` は本体の精緻化に `outer` を渡さないので、
   特別な処理をしなくてもこの意味になる(`test/annot_rows.t` の alias)。
   明示した行は、エイリアスを通しても書いたとおりに読む。
   `type F[A] = (A) => Int32 @ Print` を束縛の最も外側の位置に書いても、
   同じ矢印を注釈に直接書いても(以下、矢印リテラルと呼ぶ)、
   `{Print}` は同じ閉じた行で、どちらも使うときに開く(§11.26)。
   エイリアスと矢印リテラルの違いは、最も外側の `@` を省略したときにだけ現れる。
   型クラスのメソッドの登録は、最も外側の省略を `@ {}` に置き換える処理を別に持つので、
   `outer` を渡さないだけでは足りない。
   そこでメソッドの登録は、注釈の先頭が矢印リテラルのときに限って省略を置き換える
   (§11.33。`test/annot_rows.t` の clsalias3 / clslit)。

   規則 5 を置くのも、エイリアスに値を作る箇所がないからである。
   newtype なら、`Callback[{Print}]` の `{Print}` を行として読むための情報は、
   宣言表の `dd_params` にある。
   透過なエイリアスは、展開後の型に情報を残さない。
   そのため、パラメータのカインドだけは表(`al_kinds`、第6章 §6.5)に残しておかないと、
   使用点で型引数を型として読むか行として読むかを決められない。
   カインドは、1a′ と 1b の後処理で、本体を試しに精緻化して決める(§11.39)。
   読み方の判定と照合の規則は `elab_con_args` と同じで、
   `type Cb[E] = Callback[E]` に対して `Cb[{Print}]` と書ける(`test/kinds.t` の alias)。
   仮に型引数をすべて型として読むと、
   具体的な行は `エフェクトラベルはこの位置(レコード型)では使えません` のエラーになってしまう。

   `check_no_hole` も、型レベルのλを避けるための検査である。
   型引数の位置に `_` を書けると、引数を捨てる型関数を書いたのと同じことになるので、
   インスタンスの対象の型以外では穴を拒否する。

   展開の環境は閉じている。
   エイリアスの本体から見えるのは自分の型パラメータだけで、使用点の `env.types` は引き継がない。
   展開が使用点のスコープに依存すると、同じエイリアスが使用点ごとに別の型になってしまう。

   `al_kind` が `EffectRow` のときだけ、本体をエフェクト行として精緻化する。
   Keleut では行変数とエフェクト名が構文上同じ形なので、
   エイリアスの側にカインドの注釈が必要である(§11.6)。
   注釈のないエイリアスの本体は値の型として読み、そのカインドが行なら、
   パス 2 が宣言の位置でエラーにする(§11.40)。
   この検査がないと、本体が行である Type エイリアスのうち、
   パラメータのない形は使用点でエラーになり、
   パラメータを持つ形(`type Q[E] = P[E]`)は `@ Q[E]` の位置で照合に通ってしまう。 *)

(* 値の型の位置で読んだ型のカインドが Type であることを検査する。
   矢印の引数と返り値、レコードのフィールド(タプルの要素を含む)、
   ヴァリアントのペイロードを、この関数で読む。
   elab_type の外からは、引数と返り値の注釈をこの関数で読む。
   検査しないと、行カインドの型パラメータや EffectRow エイリアスが値の型として表に入り、
   診断が使用点まで遅れて、内部名を含むメッセージになる。
   型パラメータだけを書いた位置では、same_kind による照合が、
   値の位置に現れたことからそのパラメータのカインドを Type に決める。
   at_node を部分式に設定し直すのは、診断の位置を、
   注釈全体の先頭ではなくカインドが合わなかった位置にするためである *)
and elab_value_type env level ~expanding what t =
  let ty = elab_type env level ~expanding t in
  at_node t (fun () -> check_value_kind what ty);
  ty

(* 型引数を、宣言されたパラメータのカインドに合わせて読む(sample.kel §6、sample.kel:252-255)。
   Row のパラメータなら elab_eff、そうでなければ elab_type で読む。
   読み終えたらカインドを照合する。
   不一致をここでエラーにするほうが、subst_params を経て使用点の bind でエラーになるより早く、
   診断も読みやすい。
   どちらで読むかの判定は kind_repr の構造の一致で行い、same_kind は使わない。
   same_kind は KVar を比較対象のカインドに決めるので、判定に使うと、
   未確定のパラメータをすべて Row に固定してしまう(§1.6 の原則の例外)。
   照合には same_kind を使ってよく、パス 1b ではこの照合を通して、カインドが宣言から宣言へ伝わる。
   ただし型変数への適用 F[E] だけは、arg_kind_ok が構造の一致で調べる。
   elab_eff を ~check_row:false で呼ぶのは、読んだ結果が行にならなかったことを、
   すぐ下の照合が型構成子名と引数の位置を添えて報告するからである。
   elab_eff の側の検査を止めないと、
   より一般的な `エフェクト位置の型のカインドが Row ではありません` が先に出て、
   どの引数なのかを診断の位置からしか読み取れなくなる *)
and elab_con_args env level ~expanding cname k args =
  let rec go k i = function
    | [] -> []
    | a :: rest ->
        let pk, kr = match kind_repr k with KArrow (a', r) -> (a', r) | _ -> (new_kind_var (), KStar) in
        let a = check_no_hole a in
        (* 試しに精緻化している間は、カインドが未確定のパラメータへ渡した、
           要素のない波括弧({} と {extends R})を読まずに飛ばす。
           型としても行としても読めるのは、この 2 つの形だけである。
           型として読んで照合すると、渡す先のパラメータを Type に決めてしまい、
           パス 1b が宣言順に読めば Row に決まるはずの宣言をエラーにする。
           飛ばしても問題はない。
           パス 1b が、渡す先のパラメータのカインドが決まった状態でもう一度読むからである *)
        let ambiguous =
          !speculating && match (kind_repr pk, snd a) with KVar _, T.EBraceRow ([], _) -> true | _ -> false
        in
        let t =
          if ambiguous then t_unit
          else
            match kind_repr pk with KRow -> elab_eff ~check_row:false env level ~expanding a | _ -> elab_type env level ~expanding a
        in
        if (not ambiguous) && not (arg_kind_ok pk t) then
          type_error
            (Printf.sprintf "型構成子 %s の第%d引数のカインドが一致しません: %s" cname (i + 1) (arg_kind_mismatch pk t));
        t :: go kr (i + 1) rest
  in
  go k 0 args

(* 型引数のカインドを照合する。elab_con_args と expand_alias が共通に使う。
   照合は same_kind で行うが、Row のパラメータに型変数への適用(F[E])を渡した形だけは、
   読んだ結果のカインドを構造の一致で調べる。
   arity 0 の束縛子に引数を付けると、drop_arrows が結果のカインドを新しい KVar にする。
   これを same_kind で照合すると、検査ではなく Row への既定化になる。
   F のカインドが「何かを取って Row を返す」に固定されるが、
   そのようなカインドの型構成子は言語にないので、
   閉じた行を渡す使用点で、内部名を含む単一化のエラーになる。
   §11.6 の elab_eff の最後の分岐が @ F[E] をエラーにするのと同じ規則である。
   型変数そのもの(エイリアスの展開結果が型パラメータそのものになる形を含む)は、
   same_kind で Row に決めてよい。
   それは行変数のカインドの推論であり、パス 1b でカインドが伝わる経路でもある *)
and arg_kind_ok pk t =
  match (kind_repr pk, repr t) with
  | KRow, TApp _ -> kind_repr (Unify.kind_of t) = KRow
  | _ -> same_kind pk (Unify.kind_of t)

(* カインドが未確定のときは、kind_error が :: を添えないのと同じ理由(§11.3)で、
   カインドを表示しない *)
and arg_kind_mismatch pk t =
  let k = kind_repr (Unify.kind_of t) in
  show_kind pk ^ " を期待しましたが " ^ Show.show t
  ^ match k with KVar _ -> " は行になりません" | _ -> " は " ^ show_kind k ^ " です"

and check_no_hole ((_, te) as t : T.type_exp) =
  match te with T.EHole -> type_error "_ はこの位置では使えません(インスタンス頭の List[_] 専用)" | _ -> t

(* エフェクト位置に書いた名前 n を、EffectRow エイリアスとして引く。
   次の 2 か所を、この順に探す。
   1 つ目は、§11.3 の elab_type と同じく Decls.resolve_con で解決した名前である。
   module の中では同じ module の宣言が先に見つかるので、
   module の中で修飾せずに書いた W も、module の外で修飾して書いた M.W も、同じエイリアスになる。
   2 つ目は、module スコープを飛ばして、単位の別名とグローバルな別名だけをたどった名前
   (Decls.resolve_con_global)で、トップレベルのエイリアスとコンパニオン型が見つかる。
   module の中の同名の宣言が、行にならない Type エイリアスや newtype のときは、
   1 つ目では EffectRow エイリアスが見つからないので、2 つ目でグローバルな名前を引き直す。
   見つかったエイリアスを、解決した名前(oid)と対にして返す。
   可視性は検査せず、例外を出さないので、match の節のガード(when)からも呼べる *)
and find_row_alias n =
  let c = intern n in
  List.find_map
    (fun oid ->
      match Hashtbl.find_opt Decls.aliases oid with
      | Some info when info.Decls.al_kind = Some "EffectRow" -> Some (oid, info)
      | _ -> None)
    [ Decls.resolve_con c; Decls.resolve_con_global c ]

(* エフェクト位置に書いた名前 n を、エイリアスとして引く。
   EffectRow エイリアスが見つかれば、それを返す。
   見つからず、effect の宣言表に n があれば None を返し、呼び出し元が n を effect として読む。
   effect の宣言表は、単位の別名だけを通して引く(`Decls.resolve_unit`)。
   effect は module の中に宣言できない(§11.42)ので、module の別名をたどる必要がない。
   どちらでもなければ、行にならないエイリアスを同じ 2 か所で探して返す。
   呼び出し元はそれを、エフェクト位置に Type エイリアスを書いたエラーとして報告する。
   返すエイリアスが EffectRow エイリアスなら、elab_type と同じ可視性の検査を行う。
   行にならないエイリアスには、可視性の検査を行わない。
   行にならないエイリアスは pub を付けてもエフェクト位置で使えないので、
   可視性のエラーより、呼び出し元が報告する Type エイリアスのエラーを優先する。
   カインドの注釈を追加した後に pub が足りなければ、そのときにこの検査がエラーにする *)
and find_alias n =
  let c = intern n in
  let found =
    match find_row_alias n with
    | Some _ as r -> r
    | None when Hashtbl.mem Decls.effects (Decls.resolve_unit c) -> None
    | None ->
        List.find_map
          (fun oid -> Option.map (fun info -> (oid, info)) (Hashtbl.find_opt Decls.aliases oid))
          [ Decls.resolve_con c; Decls.resolve_con_global c ]
  in
  Option.map
    (fun (oid, info) ->
      if info.Decls.al_kind = Some "EffectRow" then Decls.check_con_visible oid;
      info)
    found

(* 未知のエフェクトを報告する診断メッセージを作る。
   名前が型として登録されていれば、名前の書き間違いではなく書く位置の間違いなので、そう報告する。
   resolve_con は module の別名をたどるので、
   スコープの外の module の内部の型名にもこのメッセージが出ることがあるが、
   プログラムを受理するか拒否するかは変わらない。
   型でもなければ、スコープの外の module にある同名の EffectRow エイリアスを探し、
   §11.3 の未知の型と同じく、修飾名を案内する。
   案内するのは pub の EffectRow エイリアスだけである。
   pub でない名前は、修飾しても可視性の検査でエラーになる。
   Type エイリアスや newtype は、修飾しても行にならない。
   引数の個数は調べない。
   案内の候補は EffectRow エイリアスだけなので、
   修飾した後に個数が合わなければ expand_alias が報告する *)
and unknown_effect n =
  if Hashtbl.mem Decls.con_kinds (Decls.resolve_con (intern n)) then
    "型 " ^ n ^ " はエフェクトではありません(ここにはエフェクト行が要ります)"
  else
    let pub_row_alias q =
      (match Hashtbl.find_opt Decls.con_visibility q with Some v -> v.Decls.vis_pub | None -> true)
      && match Hashtbl.find_opt Decls.aliases q with Some info -> info.Decls.al_kind = Some "EffectRow" | None -> false
    in
    match List.filter pub_row_alias (Decls.con_synonym_candidates (intern n)) with
    | [] -> "未知のエフェクト: " ^ n
    | cands -> "未知のエフェクト: " ^ n ^ "(" ^ String.concat " か " (List.map display_of cands) ^ " と修飾してください)"

(* エイリアスが開いた行に展開されたときに、展開結果を行の残りの要素とつなぐ。
   row_append は左の行が閉じていることを要求するので、展開結果の閉じた先頭部分をたどり、
   残りの要素(acc)を行変数の手前に挿入する。
   たとえば {W[E], Console} は {Print, Console extends E} になる。
   acc も開いていると行変数が 2 つになるので、型エラーにする *)
and splice_row alias_name expanded acc =
  let rec closed r = match repr r with TRowExtend (_, _, rest) -> closed rest | TRowEmpty -> true | _ -> false in
  let rec go r =
    match repr r with
    | TRowExtend (n, a, rest) -> TRowExtend (n, a, go rest)
    | TRowEmpty -> acc
    | tail ->
        if closed acc then row_append acc tail
        else
          type_error
            ("エイリアス " ^ alias_name ^ " は開いた行に展開されるので、extends や別の開いた行と同じ行には置けません(行変数は 1 つまで)")
  in
  go expanded

and expand_alias env level ~expanding info args =
  if List.mem info.Decls.al_name expanding then
    type_error ("型エイリアス " ^ display_of info.Decls.al_name ^ " が再帰しています(エイリアスは非再帰)")
  else if List.length args <> List.length info.Decls.al_params then
    type_error
      (Printf.sprintf "型エイリアス %s の引数は %d 個必要です(%d 個与えられました。部分適用は禁止)" (display_of info.Decls.al_name)
         (List.length info.Decls.al_params) (List.length args))
  else
    (* 引数は使用点のスコープで精緻化する(現在の module は使用点のままである)。
       型として読むか行として読むかは、表のカインド(al_kinds)で決める。
       規則は elab_con_args と同じで、判定は kind_repr の構造の一致、照合は same_kind である。
       al_kinds は、エイリアスを表に登録するときに al_params と同じ長さに作るので、
       長さが違えば処理系のバグである *)
    if List.length info.Decls.al_kinds <> List.length info.Decls.al_params then
      bug ("expand_alias: " ^ display_of info.Decls.al_name ^ " の al_kinds の長さが al_params と違います");
    let arg_tys =
      List.map2
        (fun a pk ->
          let a = check_no_hole a in
          (* 試しに精緻化している間は、カインドが未確定のパラメータへ渡した、
             要素のない波括弧({} と {extends R})を、パラメータとの照合に使わない。
             型として一度読むのは、extends の右の R のカインドを Row に決めるためである。
             行カインドは 1 つしかないので、行として読んでも R は同じカインドになる。
             本体へは、読んだ型の代わりに、カインドのセルをパラメータと共有する新しい型変数を渡す。
             本体がその変数を使う位置が、パラメータのカインドを決める。
             elab_con_args と違って Unit を渡さないのは、エイリアスが本体を展開するからである。
             Unit を渡すと、それが本体の中の別の型構成子の引数になり、
             その型構成子のパラメータを Type に決めてしまう *)
          let ambiguous =
            !speculating && match (kind_repr pk, snd a) with KVar _, T.EBraceRow ([], _) -> true | _ -> false
          in
          let t =
            if ambiguous then (
              ignore (elab_type env level ~expanding a);
              new_var ~kind:pk level)
            else
              match kind_repr pk with
              | KRow -> elab_eff ~check_row:false env level ~expanding a
              | _ -> elab_type env level ~expanding a
          in
          if (not ambiguous) && not (arg_kind_ok pk t) then
            type_error
              ("型エイリアス " ^ display_of info.Decls.al_name ^ " の型引数のカインドが一致しません: " ^ arg_kind_mismatch pk t);
          t)
        args info.Decls.al_kinds
    in
    let types =
      List.fold_left2 (fun m tp t -> SMap.add tp.tp_name t m) SMap.empty info.Decls.al_params arg_tys
    in
    (* エイリアスの本体の環境は閉じている。本体から見えるのは、エイリアスの型パラメータだけである *)
    let env' = { env with types } in
    let expanding = info.Decls.al_name :: expanding in
    (* 本体は、エイリアスを宣言したスコープで展開する。module の中のエイリアスが
       その module の内部の型を指していても、module の外から使えるようにするためである *)
    let saved = !Decls.current_module and saved_unit = !Decls.current_unit in
    Decls.current_module := info.Decls.al_module;
    Decls.current_unit := info.Decls.al_unit;
    Fun.protect
      ~finally:(fun () ->
        Decls.current_module := saved;
        Decls.current_unit := saved_unit)
      (fun () ->
        match info.Decls.al_kind with
        | Some "EffectRow" -> elab_eff env' level ~expanding info.Decls.al_body
        | _ -> elab_type env' level ~expanding info.Decls.al_body)

(* ## 11.6 エフェクト行の精緻化

   Keleut では、`@ E`(行変数)と `@ Print`(エフェクト名)が構文上同じ形をしている。
   区別できるのは型検査器だけで、`elab_eff` が次の順に判定する。

   1. `env.types` にあり、カインドが行なら、行変数である。
   2. `EffectRow` の注釈のあるエイリアスなら、展開する。
      波括弧の中では、展開結果を行のほかの要素とつなぐ。
      `@` の後でも波括弧の中でも、引数があってもなくても、
      エイリアスを effect の宣言表より先に調べる。
      エイリアスは `find_row_alias` が 2 か所で探す。
      1 つ目は `Decls.resolve_con` で解決した名前で、
      module の中では同じ module の宣言が先に見つかる。
      そのため module の中では、同じ module のエイリアスを修飾せずに書ける。
      2 つ目はグローバルな名前で、トップレベルのエイリアスとコンパニオン型が見つかる。
   3. effect の宣言表にあれば、ラベル 1 つの閉じた行にする。
      `@ Print` は `@ {Print}` の略記だからである。
      effect の宣言表は、単位の別名だけを通して引く。

   エフェクト位置で、module の宣言が同名のグローバルな名前を隠すのは、
   その宣言が EffectRow エイリアスのときだけである。
   2 を 3 より先に調べるので、module の中に、エフェクトやトップレベルのエイリアスと同名の
   EffectRow エイリアスを宣言すると、その module の中では、その名前は module のエイリアスを指す。
   `@ Heap[E]` と `@ {Heap[E]}` も、どちらも module のエイリアスを指す。
   その module の中のエフェクト位置に、隠されたエフェクトを直接書く方法はない
   (操作名の修飾 `E.op` は effect の宣言表を引くので、隠されない)。
   エイリアスの本体は、宣言したスコープで読む(§11.5)。
   そのため、トップレベルに置いたエイリアスを経由すれば、隠されたエフェクトを書ける。
   逆に、module のエイリアスの本体に同じ名前を書くと、エイリアス自身を指すので、再帰のエラーになる。
   module の中の型の位置に `type T = (T, Int32)` を書いたときと同じである。
   一方、module の Type エイリアスと newtype は、エフェクト位置では何も隠さない。
   `find_row_alias` が 1 つ目ではエイリアスを見つけられず、
   2 つ目と effect の宣言表を引くからである。
   型の位置では、module の型は種類を問わず同名のトップレベルの型を隠すので、
   エフェクト位置とは規則が違う。
   行にならない宣言はエフェクト位置で使えず、隠させても型エラーになるだけなので、
   隠さない規則にしている。
   この規則により、module に `type Console = Int32` を追加しても、
   その module の中の `@ Console` の意味は変わらない
   (`test/visibility.t` の visrow6 から visrow11)。

   1 の判定に `same_kind` を使うのは、arity 0 の型パラメータのカインドが、
   宣言時には未確定(`KVar`)だからである。
   `[E]` と書いただけでは行なのか型なのか分からず、使われた位置で決まる。
   構造の一致で `KRow` かどうかを調べると、まだ `KVar` のままの行変数を漏らす。
   第8章の `rewrite_row` も、同じ理由で `same_kind` を使う(§8.6)。

   カインドを `same_kind` で比べるという原則には、例外が 2 つある。
   §11.5 の `elab_con_args` が型引数を型として読むか行として読むかを決める判定
   (同じ節の `expand_alias` も同じ規則で判定する)と、後で説明する最後の分岐の照合である。
   型変数への適用 `F[E]` を行の位置で調べる箇所(§11.5 の `arg_kind_ok`、
   レコード行の `extends` の右、ヴァリアント型の末尾)も、最後の分岐と同じ規則で構造を調べる。
   どれも、`same_kind` が `KVar` を決めると未確定のカインドが固定されてしまう位置で、
   構造で比べてよい理由をそれぞれの箇所に書いてある。

   ラベルの引数は 1 つまでである(`Heap[h]` のように)。
   行のラベルが持つ型がそのままエフェクトのパラメータで、
   パラメータを持たないエフェクトではそれを `Unit` にする。
   行変数をラベルと並べて書く合成(`{E1, Print}` の `E1`)は拒否する。
   波括弧の中に引数なしで書いた型パラメータは、エイリアスや可視性を調べる前に、
   この合成として拒否する。
   型パラメータは、型の位置と同じく、同名のエイリアスとコンパニオン型を種類を問わず隠す。
   同名の Type エイリアス、EffectRow エイリアス、pub でないコンパニオン型があっても、
   この診断になる(`test/visibility.t` の visrow22 から visrow28)。
   `@ W` の形も 1 の判定で型パラメータを先に引くので、
   型パラメータと EffectRow エイリアスが同名のとき、`@ W` と `@ {W}` はどちらも型パラメータを指す
   (visrow26b と visrow29)。
   引数つきの要素 `{W[E]}` でも、型パラメータと同名のエイリアスは引かない。
   型パラメータへの適用は行の要素になれないので、effect の宣言表になければ未知のエフェクトになる
   (visrow30)。
   `@ W[E]` の形も、型パラメータと同名のエイリアスを引かない。
   行の合成を末尾の `extends` だけに限ると、
   `row_append` の左辺が閉じているという不変条件を保てる。
   例外は、開いた行に展開されるエイリアスである。
   この場合は `splice_row` が、展開結果の閉じた先頭部分の後ろに残りの要素を挿入し、
   同じ不変条件を守る
   (`{W[E], Console}` は `{Print, Console extends E}` になる。`test/kinds.t` の splice2)。
   行変数が 2 つになる形(`{W[E] extends E2}`)は型エラーである。

   `Heap[h]`(ラベルの引数)と `WithPrint[E]`(パラメータつきの EffectRow エイリアスの適用)は、
   構文上同じ形をしている。
   型名、エフェクト名、エイリアス名は `claim_type_name` が管理する 1 つの名前空間にあるので、
   名前を引けばどちらなのかが決まる(`test/kinds.t` の splice)。

   未知のエフェクトの診断は、名前の書き間違いと書く位置の間違いの 2 通りに分ける。
   名前が型として登録されているなら、書き間違いではなく書く位置の間違いなので、
   `Callback[Int32]` には `型 Int32 はエフェクトではありません` と報告する(`unknown_effect`)。

   適用される側がどこにも宣言されていない適用(module の外から修飾せずに書いた `@ W[E]`)も、
   未知のエフェクトとして報告する。
   最後の分岐に進めると、`elab_type` が `未知の型` のエラーにするので、
   メッセージにエフェクトという語も修飾の案内も出ない。
   引数のない `@ W` や行の要素の `{W[E]}` と同じく、
   スコープの外の module にある pub の EffectRow エイリアスを修飾名で案内する
   (`test/visibility.t` の visrow4b)。

   ここまでの分岐のどれにも該当しなかった型の式は、最後の分岐に進む。
   `@` の後(文法の `eff` / `eff_name`)に書いた型の式のうち、最後の分岐に進む形は 2 つある。
   module 修飾の名前とその適用(`M.T` / `M.W` / `M.W[E]`)と、
   エフェクト名でも EffectRow エイリアスでもない、宣言のある名前への適用
   (型パラメータへの適用 `F[E]`、`MutableArray[Int32, Int32]`、Type エイリアスの適用)である。
   このほか `elab_eff` は、文法が `ty` を取る位置を 3 つ読む。
   `{… extends <ty>}` の右(`parser.mly` の `lbrace EXTENDS ty RBRACE`)、
   EffectRow エイリアスの本体(`type` 宣言の右辺)、
   行カインドのパラメータへの型引数(§11.5 の `elab_con_args` と `expand_alias`)である。
   extends の右は、`EBraceRow` の分岐がその `ty` をそのまま `elab_eff` に再帰で渡す。
   これらの位置からは、`@ {extends #Tag}` や `type W: EffectRow = #Tag` のように、
   `eff` では書けない型の式も最後の分岐に進む。
   修飾した EffectRow エイリアス(`M.W` / `M.W[E]`)は最後の分岐を通って正しく行になるので、
   この分岐に来たものを一律に型エラーにするわけにはいかない。
   そこで最後の分岐は、`elab_type` で読んだ結果のカインドを照合し、行でなければ型エラーにする。
   メッセージは `エフェクト位置の型のカインドが Row ではありません: <型> :: <カインド>` で、
   §11.3 の値の型の位置と同じ `kind_error` が作る。
   照合しないと、`let f(x: Int32): Int32 @ MutableArray[Int32, Int32] = x` が
   `@ {extends MutableArray[Int32, Int32]}` という型で検査に通ってしまう。
   行の末尾に置かれた、カインドが Type の型は何とも単一化できないので、
   その関数は宣言できても呼び出せない。
   module 修飾の型名(`@ M.T`)と、
   EffectRow エイリアスの本体(`type W: EffectRow = MutableArray[Int32, Int32]`)も、
   この照合でエラーにする(`test/kinds.t` の effkind 〜 effkind5)。

   `EBraceRow` の分岐には `extends の右は行でなければなりません` という検査があるが、
   このエラーが出ることはない。
   extends の右は `elab_eff` で読む(`?check_row` は既定の true のまま)。
   最後の分岐を通った型は、そこでの照合によりカインドが `Row` であり、
   ほかの分岐が返すのも行だからである。
   `@ {extends #Tag}` は `エフェクト位置の型のカインドが Row ではありません: #Tag :: Type` のエラーになる。
   失敗しないこの検査は、念のために残してある。

   最後の分岐の照合だけは `kind_repr` の構造の一致で判定し、`same_kind` を使わない。
   エフェクト位置ではカインドを推論させないためである。
   型パラメータだけを書いた形は 1 の判定が処理し、そこでは `same_kind` を使って、
   カインドがまだ `KVar` の型パラメータも行変数として受理する。
   最後の分岐にも、カインドが未確定のまま来るものがあり、その経路は 2 つある。
   1 つは arity 0 の束縛子への適用(`let f[F, E](x: Int32): Int32 @ F[E]`)で、
   `drop_arrows` が束縛子のカインドを `KArrow (KVar, KVar)` に決め、
   その結果の側の新しい `KVar` が来る。
   もう 1 つは、パラメータのカインドがまだ推論されていない型エイリアスの適用で、
   こちらは `TVar` が返る。
   本体がパラメータのカインドを決めないエイリアスでは、
   パス 1b の newtype の本体から見ても、`al_kinds` は `KVar` のままである
   (`type Id[A] = A` と `newtype N[X] = MkN(() => Unit @ Id[X])` を並べると、
   展開結果の `A` が `KVar` のカインドのまま最後の分岐に返る)。
   つまり、構造で比べるのは、この分岐に未確定のカインドが来ないからではなく、来るからである。
   ここで `same_kind` を呼ぶと、それは検査ではなく `Row` への既定化になる。
   `F[E]` なら `F` のカインドが「Type を取って Row を返す」に固定されるが、
   そのようなカインドの型構成子は言語にないので、
   閉じた行を渡すと内部名を含む単一化のエラーになる `f` が、宣言として受理されてしまう。
   カインドが未確定のときは、メッセージに `:: <カインド>` を添えない。
   内部の連番を表示すると、番号がプレリュードの行数で変わり、診断が再現しなくなるからである
   (§11.3 の `kind_error`)。

   この照合は、`?check_row` に false を渡すと行わない。
   false を渡すのは、型引数を読む 2 か所(`elab_con_args` と `expand_alias`)だけである。
   そこでは呼び出し元が、`型構成子 Callback の第1引数のカインドが一致しません` のように、
   型構成子名と引数の位置を添えて報告する(`test/kinds.t` の nest2)。
   呼び出し元の照合(`arg_kind_ok`)も、型変数への適用にはこの分岐と同じ構造の一致を使う。
   既定値が `true` なので、`?check_row` を渡さない呼び出しはすべて照合する。

   エフェクト位置に名前や適用を書き、読んだ結果が行にならなかったときの診断は 3 通りある。
   名前の書き間違い(`未知のエフェクト: Nope`)、
   書く位置の間違い(`型 Int32 はエフェクトではありません`)、
   読んだ結果のカインドが行でない場合(`エフェクト位置の型のカインドが Row ではありません`)である。
   1 つのメッセージにまとめるとどれかが事実と合わなくなるので、
   `test/kinds.t` が 3 つを並べて固定している。
   エフェクト位置のエラーの診断は、この 3 つだけではない。
   行カインドでない型パラメータ(`@ h`)と Type エイリアス(`@ P`)は、
   名前を引いた時点で、手前の分岐が別のメッセージでエラーにする。
   前者は `行カインドではない型パラメータです: h`、
   後者は `エフェクト位置に Type エイリアス P は使えません(: EffectRow を付けてください)` である
   (`test/kinds.t` の regionkind / classrow / effkind6)。

   相互再帰の関数群を定義し終えたら、`elab_type` / `elab_value_type` / `elab_eff` を、
   `~expanding` に空リストを渡す同名の関数で隠す。
   以降の呼び出し元は、展開中の名前の集合を渡さなくてよい。 *)

and elab_eff ?(check_row = true) env level ~expanding ((_, te) as t : T.type_exp) : ty =
  at_node t @@ fun () ->
  match te with
  | T.EIdent (LongId [ n ]) when SMap.mem n env.types ->
      let tv = SMap.find n env.types in
      if same_kind (Unify.kind_of tv) KRow then tv else type_error ("行カインドではない型パラメータです: " ^ n)
  | T.EIdent (LongId [ n ]) -> (
      match find_alias n with
      | Some info ->
          if info.Decls.al_kind = Some "EffectRow" then expand_alias env level ~expanding info []
          else type_error ("エフェクト位置に Type エイリアス " ^ n ^ " は使えません(: EffectRow を付けてください)")
      | None ->
          (* @ Print は @ {Print} の略記である *)
          let e = Decls.resolve_unit (intern n) in
          if Hashtbl.mem Decls.effects e then TRowExtend (e, t_unit, TRowEmpty) else type_error (unknown_effect n))
  | T.EApply ((_, T.EIdent (LongId [ n ])), args)
    when (not (SMap.mem n env.types)) && Option.is_some (find_row_alias n) ->
      (* EffectRow エイリアスの適用(@ W[E])。
         波括弧の中の要素と同じく find_row_alias で引き、effect の宣言表より先に調べる。
         module のエイリアスが同名の effect を隠すときも、
         @ Heap[E] と @ {Heap[E]} は同じエイリアスを指す *)
      let oid, info = Option.get (find_row_alias n) in
      Decls.check_con_visible oid;
      expand_alias env level ~expanding info args
  | T.EApply ((_, T.EIdent (LongId [ n ])), args) when Hashtbl.mem Decls.effects (Decls.resolve_unit (intern n)) ->
      (* @ Heap[h] は @ {Heap[h]} の略記である。
         sample.kel:469 の略記の規則は、引数つきのラベルを除外していない *)
      TRowExtend
        ( Decls.resolve_unit (intern n),
          (match args with
          | [ a ] -> elab_type env level ~expanding a
          | _ -> type_error "エフェクトラベルの引数は1個までです"),
          TRowEmpty )
  | T.EApply ((_, T.EIdent (LongId [ n ])), _)
    when (not (SMap.mem n env.types))
         &&
         let oid = Decls.resolve_con (intern n) in
         not (Hashtbl.mem Decls.aliases oid || Hashtbl.mem Decls.con_kinds oid) ->
      (* 先頭の名前が、型パラメータでもエイリアスでも宣言表の型でもない適用(@ W[E])。
         最後の分岐に渡すと elab_type が未知の型としてエラーにするので、
         ここで未知のエフェクトとして報告する。
         引数のない @ W や行の要素の {W[E]} と同じく、
         スコープの外にある pub の EffectRow エイリアスを修飾名で書くよう案内する。
         条件は、elab_type の EApply の分岐が名前を引く順
         (型パラメータ、エイリアス表、宣言表)に合わせてある。
         elab_type の側で未知の名前の検査を追加するときは、この条件も合わせて直す *)
      type_error (unknown_effect n)
  | T.EBraceRow (elems, ext) ->
      let tail =
        match ext with
        | None -> TRowEmpty
        | Some t -> (
            (* extends の右は、文法(parser.mly)が eff ではなく ty を取るので、
               ここで elab_eff を再帰的に呼んで読む。
               これが最後の分岐に来る経路の 1 つである。
               下の検査は、最後の分岐の照合が先にエラーにするので失敗しないが、
               念のために残してある(§11.6) *)
            let tt = elab_eff env level ~expanding t in
            if same_kind (Unify.kind_of tt) KRow then tt else type_error "extends の右は行でなければなりません")
      in
      List.fold_right
        (fun elem acc ->
          match elem with
          | T.BLabel (li, args) -> (
              let n = show_long_id li in
              (* 型パラメータでなければエイリアスを先に調べ、引数の有無で経路を分けない。
                 エフェクト名と型名は同じ名前空間(claim_type_name)にあるので、
                 Heap[h](ラベルの引数)と WithPrint[E](エイリアスの適用)を取り違えない。
                 修飾名(M.W)も同じ経路で引く。
                 effect は module の中に宣言できないので、修飾名が指せるのはエイリアスだけで、
                 それ以外は unknown_effect の診断になる *)
              (* 型パラメータは find_alias より先に調べるので、
                 同名のエイリアスとコンパニオン型を隠す。
                 @ W の形を読む 1 番目の分岐と同じ順である。
                 `{E1, Print}` のように行変数を要素として並べる書き方は受理しない。
                 行変数を書けるのは末尾の extends だけである。
                 引数つきの型パラメータは、型パラメータへの適用が行の要素になれないので、
                 エイリアスを引かずに effect の宣言表を調べる *)
              let is_param = SMap.mem n env.types in
              if args = [] && is_param then type_error ("行変数 " ^ n ^ " は extends の位置にのみ書けます")
              else
                match if is_param then None else find_alias n with
                | Some info when info.Decls.al_kind = Some "EffectRow" ->
                    splice_row n (expand_alias env level ~expanding info args) acc (* 展開した行につなぐ *)
                | Some _ -> type_error ("エフェクト行に Type エイリアス " ^ n ^ " は置けません(: EffectRow を付けてください)")
                | None ->
                    if Hashtbl.mem Decls.effects (Decls.resolve_unit (intern n)) then
                      TRowExtend
                        ( Decls.resolve_unit (intern n),
                          (match args with
                          | [] -> t_unit
                          | [ a ] -> elab_type env level ~expanding a
                          | _ -> type_error "エフェクトラベルの引数は1個までです"),
                          acc )
                    else type_error (unknown_effect n))
          | T.BField (l, _) -> type_error ("エフェクト行にフィールド " ^ l ^ " は書けません"))
        elems tail
  | _ ->
      (* 最後の分岐。
         ここに来る型の式は 3 種類ある。
         1 つ目は、@ の後に書いた module 修飾の名前である。
         2 つ目は、エフェクト名でも EffectRow エイリアスでもない、宣言のある名前への適用である。
         3 つ目は、文法が ty を取る 3 つの位置
         (extends の右、EffectRow エイリアスの本体、行カインドのパラメータへの型引数)に書いた式である。
         このうち型引数の経路は ~check_row:false を渡すので照合しない。
         修飾した EffectRow エイリアス(M.W / M.W[E])はこの分岐で正しく行になるので、
         エラーにはせず、読んだ結果のカインドを照合する。
         判定は kind_repr の構造の一致で行い、same_kind は使わない。
         カインドが未確定のまま来る経路があり
         (F[E] と、カインドがまだ推論されていないエイリアスの適用)、
         same_kind で調べると、検査ではなく Row への既定化になるからである(§11.6) *)
      let ty = elab_type env level ~expanding t in
      if check_row && kind_repr (Unify.kind_of ty) <> KRow then kind_error "エフェクト位置の型" ~expected:"Row" ty;
      ty

(* 束縛の最も外側の矢印が注釈としてそのまま書かれている位置を読む関数。
   その位置は、型クラスのメソッドの型と、引数リストを持たない値束縛の注釈である。
   この位置でだけ、省略した @ が新しい行変数になる。
   sample.kel §9 の表にある規則のうち、let のエフェクト行を本体から推論する規則は、
   この行変数で実現する。
   pub let と型クラスのメソッドで省略した @ を @ {} と読む規則は、
   呼び出し元が行を TRowEmpty に置き換えて実現する(§11.28、§11.33)。
   インスタンスの実装を純粋とする規則は、包摂検査で実現する(§11.38)。
   ~outer:true を渡すのはこの 1 か所だけである *)
let elab_type_outer env level t = at_node t (fun () -> elab_type env level ~expanding:[] ~outer:true t)

let elab_type env level t = at_node t (fun () -> elab_type env level ~expanding:[] t)

(* 注釈の位置(引数、返り値、値束縛の注釈)も値の型の位置なので、同じカインドの照合を行う。
   照合しないと、EffectRow エイリアスを書いた注釈が束縛の単一化まで残り、
   `カインドが一致しません: _A :: Type と {Print}` のように内部名を含むエラーになる。
   引数と返り値の注釈はこの関数で読み、値束縛の注釈は下の elab_value_type_outer で読む *)
let elab_value_type env level what t = at_node t (fun () -> elab_value_type env level ~expanding:[] what t)

let elab_value_type_outer env level what t =
  let ty = elab_type_outer env level t in
  at_node t (fun () -> check_value_kind what ty);
  ty

let elab_eff env level t = at_node t (fun () -> elab_eff env level ~expanding:[] t)

(* ## 11.7 パターンの検査

   `elab_pat` はパターンの型を推論せず、期待型に対して検査する。
   呼び出し元から受け取った期待型 `expected` をパターンに沿って分解しながら、変数を環境に追加する。

   パターンが束縛する変数は常に単相である。
   パターン変数を一般化しないことはランク 1 多相の一部である。
   ここで一般化すると、`match` の各節が変数を別々の型で使えるようになり、型検査が不健全になる。

   `seen` は、同じパターンの中での変数の重複を拒否するためだけの可変リストである。
   環境そのものは不変の Map で、変数を追加した環境を引数として次の呼び出しに渡す。
   例外はコンストラクタパターンのフィールドを走査する箇所だけで、
   そこでは `Array.iteri` で走査するので、環境を ref に持つ(§11.8)。

   パターンを検査として扱う利点は 2 つある。
   第 1 に、リテラルパターンが `number_ty` を経由するので、
   `case 0 =>` が予約述語 `Integral` の付いた変数として期待型と単一化され、
   整数の幅が照合対象の型から決まる。
   第 2 に、レコードパターンで `rest` を書いたかどうかが、そのまま行の開閉になる。
   閉じた行との単一化が、タプルの要素数の検査を兼ねる。
   `(a, b)` が 3 要素のタプルに一致しないのは、行の長さが合わないからである。
   タプルの要素数を数える専用の検査はない。

   `PAnnot` が読む注釈は値の型の位置なので、
   `elab_value_type` でカインドを `Type` と照合する(§11.3)。
   引数の注釈はこの経路で読むので、`let f(x: P)` に `EffectRow` エイリアスを書くと、
   期待型との単一化まで進まず、注釈を読んだ時点でエラーになる(`test/kinds.t` の annotkind)。

   `elab_pat` は、式のノードと同じく、すべてのパターンのノードに期待型を `set_ty` で書き込む。 *)

let rec pat_var_names ((_, p) : T.pat) =
  match p with
  | T.PVar x -> [ x ]
  | T.PAnnot (q, _) -> pat_var_names q
  | T.PRecord (fs, tail) -> List.concat_map (fun (_, q) -> pat_var_names q) fs @ Option.fold ~none:[] ~some:pat_var_names tail
  | T.PCtor (_, args) -> List.concat_map (fun a -> pat_var_names a.T.cap_pat) args
  | T.PVariant (_, q) -> pat_var_names q
  | T.PWildcard | T.PBool _ | T.PNumber _ | T.PText _ -> []

let rec elab_pat env level seen expected ((_, p) as node : T.pat) : env =
  Tree.set_ty node expected;
  at_node node @@ fun () ->
  match p with
  | T.PWildcard -> env
  | T.PVar x ->
      if List.mem x !seen then type_error ("同じパターン内で変数 " ^ x ^ " が重複しています")
      else (
        seen := x :: !seen;
        add_local env x expected)
  | T.PAnnot (sub, te) ->
      Unify.unify expected (elab_value_type env level "型注釈" te);
      elab_pat env level seen expected sub
  | T.PBool _ ->
      Unify.unify expected t_boolean;
      env
  | T.PText _ ->
      Unify.unify expected t_string;
      env
  | T.PNumber n ->
      Unify.unify expected (number_ty ~loc:(Tree.loc_of node) level n);
      pattern_numbers := (node, n) :: !pattern_numbers;
      env
  | T.PRecord (fields, rest) -> (
      let ftys = List.map (fun (l, _) -> (l, new_var level)) fields in
      match rest with
      | None ->
          (* 閉じた行と単一化する。タプルの要素数の検査を兼ねる *)
          let row = List.fold_right (fun (l, t) acc -> TRowExtend (intern l, t, acc)) ftys TRowEmpty in
          Unify.unify expected (TRecord row);
          List.fold_left2 (fun env (_, sub) (_, t) -> elab_pat env level seen t sub) env fields ftys
      | Some rest_pat ->
          let tail = new_row_var level in
          let row = List.fold_right (fun (l, t) acc -> TRowExtend (intern l, t, acc)) ftys tail in
          Unify.unify expected (TRecord row);
          let env = List.fold_left2 (fun env (_, sub) (_, t) -> elab_pat env level seen t sub) env fields ftys in
          elab_pat env level seen (TRecord tail) rest_pat)
  | T.PVariant (str, sub) ->
      let tf = new_var level in
      let rest = new_row_var level in
      Unify.unify expected (TVariant (TRowExtend (intern str, tf, rest)));
      elab_pat env level seen tf sub
(* ## 11.8 コンストラクタパターン

   `Cons(head, tail)` のようなパターンに対して、`elab_pat` は宣言表からコンストラクタを引き、
   データ型のパラメータを新しい変数にして期待型と単一化し、
   フィールドの型を `subst_params` で具体化してから部分パターンを検査する。

   フィールドは位置引数とラベル指定の 2 通りで指定でき、両者を混ぜて書ける。
   ラベル指定だけのパターンでは、フィールドを省略できる。
   書かなかったフィールドは `_` と同じである。
   位置引数を使ったときだけ、すべてのフィールドが必要になる。
   ラベル指定で省略を許すのは、フィールドを増やしたときに既存のパターンを壊さないためである。

   フィールドを実引数に割り当てた結果(フィールドの位置から実引数の位置への配列)を、
   `set_resolved` で木に書く。
   評価器と網羅性検査に同じ計算をさせないためである。
   ラベルの並べ替えを 3 か所で実装すると、実装が食い違ったときに、
   型検査に通るのに値が入れ替わってしまう。

   `dd_opaque` が真の型は、パターンで分解できないよう、ここで拒否する。
   `dd_opaque` が真の型は組み込みの不透明型だけで、どれもコンストラクタを持たないので、
   コンストラクタの名前からこの分岐に来ることはない。
   この拒否は、念のために置いた分岐である。 *)

  | T.PCtor (li, args) -> (
      let (LongId comps) = li in
      let cname = List.nth comps (List.length comps - 1) in
      if not (cname.[0] >= 'A' && cname.[0] <= 'Z') then
        type_error ("未知のコンストラクタパターン: " ^ show_long_id li ^ "(操作節は handle の中でのみ使えます)")
      else
        let ctor = Decls.resolve_ctor (intern cname) in
        match Hashtbl.find_opt Decls.ctor_owner ctor with
        | None -> type_error ("未知のコンストラクタ: " ^ show_long_id li)
        | Some dname ->
            Decls.check_ctor_visible ctor dname;
            let dd = Hashtbl.find Decls.datas dname in
            if dd.Decls.dd_opaque then type_error ("newtype " ^ display_of dname ^ " の表現は ??? で隠されています")
            else
              let ct = List.find (fun c -> c.Decls.ct_name = ctor) dd.Decls.dd_ctors in
              let nfields = List.length ct.Decls.ct_fields in
              let field_to_arg = Array.make nfields None in
              let positional = List.filter (fun a -> a.T.cap_label = None) args in
              (* 位置引数があるときは、すべてのフィールドが必要である。
                 省略したフィールドを _ とみなすのは、ラベル指定だけのパターンである *)
              if positional <> [] && List.length args <> nfields then
                type_error
                  (Printf.sprintf "コンストラクタ %s のパターンは %d 個のフィールドを取ります(%d 個与えられました)" cname nfields
                     (List.length args));
              List.iteri
                (fun ai (a : T.ctor_arg_pat) ->
                  match a.T.cap_label with
                  | None ->
                      let rec first i =
                        if i >= nfields then type_error ("コンストラクタ " ^ cname ^ " のパターンの引数が多すぎます")
                        else if field_to_arg.(i) = None then i
                        else first (i + 1)
                      in
                      field_to_arg.(first 0) <- Some ai
                  | Some l ->
                      let lo = intern l in
                      let rec find i = function
                        | [] -> type_error ("コンストラクタ " ^ cname ^ " にフィールド " ^ l ^ " はありません")
                        | f :: rest -> if f.Decls.fi_label = Some lo then i else find (i + 1) rest
                      in
                      let i = find 0 ct.Decls.ct_fields in
                      if field_to_arg.(i) <> None then type_error ("フィールド " ^ l ^ " が二重に指定されています");
                      field_to_arg.(i) <- Some ai)
                args;
              Tree.set_resolved node (Tree.RCtorPat (dname, ctor, field_to_arg));
              let subst =
                List.map (fun (i : var_info) -> (i.vid, Unify.new_class_var ~kind:i.vkind ~classes:i.vcls level)) dd.Decls.dd_params
              in
              Unify.unify expected (TCon (dname, List.map snd subst));
              let env = ref env in
              Array.iteri
                (fun fi arg ->
                  match arg with
                  | Some ai ->
                      let f = List.nth ct.Decls.ct_fields fi in
                      env := elab_pat !env level seen (Unify.subst_params level subst f.Decls.fi_ty) (List.nth args ai).T.cap_pat
                  | None -> ())
                field_to_arg;
              !env)

(* ## 11.9 値制限

   `is_value` は式の構文だけを調べる判定で、式が構文上の値なら一般化してよいと決める。
   可変参照がある言語で一般化を無条件に許すと不健全になるので、一般化する束縛を制限する必要がある。
   その境界を構文で決めるのが、最も簡単である。

   実装では、値でない束縛の終わりに、`generalize` の代わりに `Unify.lower_levels` を呼ぶ。
   本体は、値かどうかにかかわらず 1 つ深いレベルで推論する。
   `lower_levels` が深いレベルに残った単一化変数を束縛のレベルまで下げるので、
   その束縛の型に残る単一化変数は、単相のまま環境に入る。
   注釈から作ったスコーレム定数は、この処理の対象にならない(§11.28)。

   ブロック(`Seq` や `Let` の連鎖)は、内容を調べずに値でないと判定する。
   内容を調べれば値と分かるブロックもあるが、調べないと決めておくほうが規則が短く、
   誤って値と判定することがない。
   値であるものを値でないと判定しても不健全にはならず、多相性が減るだけである。
   逆に、値でないものを値と判定すると不健全になる。 *)

let rec is_value ((_, e) : T.exp) =
  match e with
  | T.Bool _ | T.Number _ | T.Text _ | T.Ident _ | T.Hole | T.Lambda _ | T.RecordEmpty -> true
  | T.Variant (_, v) -> is_value v
  | T.Construct (_, args) -> List.for_all (fun a -> is_value a.T.ca_exp) args
  | T.RecordExtend (r, _, v) -> is_value r && is_value v
  | T.RecordRestriction (r, _) -> is_value r
  | _ -> false

(* ## 11.10 式の精緻化

   `elab_exp` が行う処理は 2 つある。
   式の型を返すことと、その型をノードに書き込むことである。
   第14章の評価器は、数値リテラルのノードに書き込まれた型を読んで、
   値を Int32 / Int64 / Float64 のどれで作るかを決める。

   式のノードのほかに、`env` / `level` / `eff` の 3 つを引数に取る。
   `eff` はその位置で許されているエフェクト行で、外側の式から内側の式へだけ渡す。
   この向きが役に立つのは perform の型付けである。
   エフェクトを内側の式から外側へ集める実装なら必要になる合流と差分の計算が、
   単一化 1 回で済む(§11.15)。

   リテラルの型はその場で決まる。
   `Hole`(`???`)の型は新しい型変数で、実行時に評価されると実行時エラーになる。 *)

(* 再帰群の束縛の本体を検査する前の pre の形を表す。
   Open は単一化変数のままだった位置で、その変数を持つ。
   Fixed は型が決まっていた位置で、その型の種類と子の形を持つ。
   Row は決まっていた行で、各ラベルとそのフィールドの形、および行の残りの形を持つ(§11.29) *)
type pre_shape = Open of tvar ref | Fixed of int * pre_shape list | Row of (oid * pre_shape) list * pre_shape

(* 再帰群の記録。
   再帰群の束縛の pre と束縛ノード、現在検査している束縛、pre を経由した参照の並びを持つ。
   参照の証拠は、再帰群の終わりに、参照先の辞書パラメータの正準順で作り直す(§11.29) *)
type group_rec = {
  g_pres : (ty * T.let_binding) list;
  g_cur : T.let_binding option ref;
  mutable g_refs : (T.exp * T.let_binding option * T.let_binding * (Tree.dkey * Tree.hole) list) list;
}

let group_stack : group_rec list ref = ref []

(* 参照した型 sch が、group_stack にある再帰群のどれかの pre そのものなら、
   その再帰群への参照として記録する *)
let record_group_ref node sch hs =
  List.iter
    (fun g ->
      match List.find_opt (fun (p, _) -> p == sch) g.g_pres with
      | Some (_, target) -> g.g_refs <- (node, !(g.g_cur), target, List.combine (Unify.dkeys_of sch) hs) :: g.g_refs
      | None -> ())
    !group_stack

(* 穴を解き、束縛の型から決められない辞書を曖昧性エラーにする(§11.28) *)
let solve_holes_at ~since ~params =
  try Unify.solve_holes ~since ~params
  with Unify.Unsolved_param (h, _) ->
    raise
      (Type_error_at
         ( h.Tree.h_loc,
           "曖昧な制約: " ^ display_of h.Tree.h_cls
           ^ " の辞書を束縛の型から決められません(束縛の型に現れない型変数に制約が付いています。注釈で型を決めてください)" ))

(* 型パラメータに付けた制約が、束縛の型の辞書パラメータに現れることを検査する。
   現れなければ曖昧性エラーにする(§11.28) *)
let check_tparam_constraints ~rigids dps =
  List.iter
    (fun (name, _, r) ->
      let i = Unify.var_info_of r in
      List.iter
        (fun c ->
          if (not (Unify.is_predicate c)) && not (List.mem (i.vid, c) dps) then
            type_error
              ("曖昧な制約: 型パラメータ " ^ name ^ " の制約 " ^ display_of c
             ^ " を束縛の型から決められません(束縛の型に現れない型パラメータに制約が付いています)"))
        i.vcls)
    rigids

(* 型の中に、予約述語以外の制約が付いた単一化変数があれば真を返す。
   式文を一般化するかどうかの判定に使う(§11.40)。
   予約述語の付いた変数は、既定化で Int32 か Float64 に決まり、
   辞書パラメータにならないので数えない *)
let rec has_constrained_unbound t =
  match repr t with
  | TVar v -> (
      match !v with
      | Unbound i -> (not (List.exists Unify.is_predicate i.vcls)) && List.exists (fun c -> not (Unify.is_predicate c)) i.vcls
      | _ -> false)
  | TCon (_, args) -> List.exists has_constrained_unbound args
  | TApp (f, a) -> has_constrained_unbound f || has_constrained_unbound a
  | TArrow (p, r, e) -> has_constrained_unbound p || has_constrained_unbound r || has_constrained_unbound e
  | TRecord row | TVariant row -> has_constrained_unbound row
  | TRowEmpty -> false
  | TRowExtend (_, f, rest) -> has_constrained_unbound f || has_constrained_unbound rest

let rec elab_exp env level eff ((_, e) as node : T.exp) : ty =
  let t = at_node node (fun () -> elab_exp' env level eff node e) in
  (* 名前で参照した関数の最も外側の行が閉じていれば、参照の位置で行の末尾を開く
     (使用時に行を開く規則。§11.11) *)
  let t = match e with T.Ident _ -> open_closed_arrow level t | _ -> t in
  Tree.set_ty node t;
  t

and elab_exp' env level eff node e =
  match e with
  | T.Bool _ -> t_boolean
  | T.Text _ -> t_string
  | T.Number n -> number_ty ~loc:(Tree.loc_of node) level n
(* ## 11.11 変数と無名関数

   ### 証拠の穴

   制約付きの型スキームを具体化する位置(変数参照、演算子、前置の `-`)では、
   `Unify.instantiate_ev` が制約ごとに証拠の穴を作り、`DUse` としてノードに書く(第5章 §5.1b)。
   穴の順序は型スキームの制約の正準順(第8章 §8.11)で、評価器はこの順に辞書を渡す。
   穴を解くのは、その参照を囲む束縛の終わり(§11.28、§11.29)、インスタンスの終わり(§11.38)、
   宣言の終わりと単位の終わり(§11.40)である。
   再帰群の `pre` への参照は、再帰群の終わりに証拠を作り直すので、
   ここでは `record_group_ref` で記録だけする。

   `instantiate_ev` を呼ぶ主な箇所は変数参照である。
   ほかに、演算子と前置の `-` がクラスのメソッドの型スキームを引く箇所(§11.13)と、
   インスタンス本体の包摂検査(§11.38)が `instantiate_ev` を呼ぶ。
   perform と操作節が操作の型スキームを引く箇所(§11.15、§11.24)は、
   操作の型スキームが制約を持たないので `instantiate` を呼ぶ。
   どれも、表から引いた型スキームの ∀ を取り除くという同じ用途である。
   ∀ を取り除く操作がこの用途に限られているので、
   型クラスの制約とカインドが複製される箇所も、型スキームを引いた直後だけだと分かる(第8章)。

   変数参照がトップレベルの宣言を指すときは、その宣言を `RVar` として木に書く。
   評価器は名前を引き直さず、この宣言から値を引く(第14章 §14.4)。
   同名の再束縛や module の値の別名があっても、型検査と実行は同じ宣言を選ぶ。
   module の値の別名を引いて見つけた名前には、修飾名の宣言を書く。

   大文字で始まる名前が値の環境になければ、引数のないコンストラクタとしてもう一度探す。
   `Nil()` と書かなくても `Nil` と書けるようにするためである。

   ### 名前の参照で開く

   変数参照の型は、`elab_exp` が木に書く直前に `open_closed_arrow` に渡す。
   参照した関数の最も外側の行が閉じていれば、
   その行の末尾を新しい行変数に替えて開く(使用時に行を開く規則。§11.26)。
   束縛した名前、引数、パターンで束縛した変数、型クラスのメソッドのどれも、この経路を通る。

   行を開く位置を呼び出し(§11.12)と関数型を要求する位置(§11.19)に限ると、
   期待型を渡さずに単一化する位置に名前を置いたとき、閉じた行のまま単一化される。
   コンストラクタの引数、レコードのフィールド、タプルの要素、`match` の節の値がそうである。
   たとえば `a` が `@ {}`、`b` が `@ Console` の関数なら、
   `Cons(a, Cons(b, Nil))` は 2 つの要素の行が `{}` と `{Console}` で一致せず、エラーになる。
   名前の参照で開けば、名前を置く位置によらず、`a` の型は `b` の型と単一化できる。

   開いた行の末尾は参照ごとに作る新しい行変数なので、
   同じ名前を行の違う 2 つの文脈で参照しても、互いの行に影響しない。
   行変数で終わる行は開かない。
   注釈のない引数や、行がまだ決まっていない一般化しない束縛の関数は、行変数のまま単一化され、
   その参照で決まった行がその後の参照にも適用される(LangSpec §13.2 の制限の 2 つ目)。

   無名関数の本体には、新しい行変数を割り当てる。
   無名関数の式そのものは値なので、周囲の `eff` には何も追加しない。
   関数を作ってもエフェクトは起きず、起きるのは関数を呼んだときである。
   呼び出しの扱いは §11.12 で述べる。 *)

  | T.Ident li -> (
      let name = Decls.qualify (show_long_id li) in
      match SMap.find_opt name env.values with
      | Some sch ->
          (* 修飾名で module の値を参照するときの可視性の検査。
             module M の値 x の修飾名 M.x が、同名のクラス M のメソッド x の修飾名と
             同じ名前になる形は、平坦化が拒否する(§11.42)。
             そのため、可視性の表に登録されている名前は必ず module の値であり、
             名前の形で検査を免除する必要はない。
             名前の形で免除すると、同名のクラスを 1 行宣言するだけで、
             pub でない任意の値を外から呼べてしまう *)
          Decls.check_value_visible (intern name);
          (match SMap.find_opt name env.tops with Some g -> Tree.set_resolved node (Tree.RVar g) | None -> ());
          (* 制約ごとに証拠の穴を作って木に書く。
             再帰群の pre への参照は、再帰群の終わりに証拠を作り直す(§11.29) *)
          let t, hs = Unify.instantiate_ev ~loc:(Tree.loc_of node) level sch in
          if hs <> [] then Tree.set_dict node (Tree.DUse hs);
          record_group_ref node sch hs;
          t
      | None -> (
          (* 環境になかったときだけ、module スコープの値の別名を引く。
             環境を先に引くので、ローカルの束縛は同名の別名を隠す。
             スコープの外では別名を解決せず、診断にだけ使う候補の一覧から修飾名を案内する。
             `未束縛の変数` とだけ報告すると、module の同名の let が原因であることを、
             ユーザがたどれないからである *)
          let scoped =
            match !Decls.current_module with
            | Some m -> Hashtbl.find_opt Decls.module_val_synonyms (m, intern name)
            | None -> None
          in
          match Option.bind scoped (fun q -> SMap.find_opt (name_of q) env.values) with
          | Some sch ->
              (* 別名が指すのは module の中のトップレベルの値で、ローカルの束縛ではない *)
              (match Option.bind scoped (fun q -> SMap.find_opt (name_of q) env.tops) with
              | Some g -> Tree.set_resolved node (Tree.RVar g)
              | None -> bug ("同義語の先が実体を持ちません: " ^ name));
              let t, hs = Unify.instantiate_ev ~loc:(Tree.loc_of node) level sch in
              if hs <> [] then Tree.set_dict node (Tree.DUse hs);
              (* module の中では、再帰群の pre も非修飾名でこの経路から引くので、
                 再帰群への参照をここでも記録する(§11.29) *)
              record_group_ref node sch hs;
              t
          | None -> (
              match li with
              | LongId comps when comps <> [] && String.length (List.nth comps (List.length comps - 1)) > 0 ->
                  let last = List.nth comps (List.length comps - 1) in
                  if last.[0] >= 'A' && last.[0] <= 'Z' then elab_construct env level node last []
                  else unbound_value (show_long_id li) scoped
              | _ -> unbound_value (show_long_id li) scoped)))
  | T.Hole -> new_var level
  | T.Lambda { l_params; l_body } ->
      let param_tys = List.map (fun _ -> new_var level) l_params in
      let seen = ref [] in
      let env2 = List.fold_left2 (fun env p t -> elab_pat env level seen t p) env l_params param_tys in
      let body_eff = new_row_var level in
      let tr = elab_exp env2 level body_eff l_body in
      (* 反駁可能な引数パターンは網羅性検査のキューに入れる。
         let のパターン束縛と同じ扱いである。
         検査しないと、型検査に通ったプログラムが、
         実行時に `パターンに値が一致しません` のエラーになる *)
      List.iter2 (fun p t -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) l_params param_tys;
      TArrow (TRecord (closed_item_row param_tys), tr, body_eff)
(* ## 11.12 関数適用

   適用の型付けの基本は、関数の型を `TArrow (引数レコード, 返り値, eff)` と単一化することである。
   第 3 要素に呼び出し元の `eff` を渡すので、
   この関数を呼ぶにはこのエフェクトが必要である、という情報が呼び出しの位置の行に伝わる。

   単一化と引数の型付けの順序には意味がある。
   単純に実装するなら、引数を先に推論してから関数型と単一化するが、`elab_exp'` はそうしない。

   1. 関数を推論する
   2. 先に `TArrow (pvar, tr, eff)` と単一化して、関数型を分解する
   3. 引数を、その `pvar` を期待型として検査する(§11.19)

   この順序が必要になるのは、引数が無名関数で、その本体が `perform` を含むときである。
   修飾なしの操作名は、その時点でエフェクト行に現れているラベルを使って解決する(§11.20)。
   引数を先に推論すると、無名関数の行はまだ何も決まっていない新しい行変数で、
   ラベルが 1 つも現れない。
   そのため、操作名を解決できない。

   その例が、sample.kel:604 の `with_file` を使う次の関数である。

   ```
   let save[E](path: String, s: String): Unit @ {Blocking extends E} = {
     with _ = with_file(path)
     perform write(s)
   }
   ```

   `with` は呼び出しの末尾に継続を加える糖衣構文(第3章)なので、
   これは `with_file(path, fn() => perform write(s))` に脱糖される。
   `with _ =` と書いたので、継続は引数を取らない(第3章 §3.8)。
   `with_file` の宣言は `body: () => A @ {File, Blocking extends E}` なので、
   関数型を先に分解して期待型を渡せば、
   無名関数の行が `{File, Blocking extends E}` に決まった状態で、
   無名関数の本体を推論できる。
   `write` を解決するときに、行に `File` が現れていて `Console` は現れていないので、
   `File.write` に決まる。
   順序を入れ替えると、無名関数の行はまだ新しい行変数で、候補が 1 つも現れない。
   そのため、`write` が複数のエフェクト(Console と File)に属するというエラーになる。
   関数型を先に分解して引数を期待型で検査するのは、多相のためではなく、
   操作名の解決に必要な行を先に決めるためである。

   単一化の前に、呼び出し先の行が閉じていれば、
   行の末尾を新しい行変数に替えて開く(使用時に行を開く規則。§11.26)。
   閉じた行は本体が起こすエフェクトの上限なので、行の末尾を開いても起こすエフェクトは増えない。
   そのため、閉じた行の関数は、その行のラベルを含むどの行の位置からでも呼べる。
   名前で参照した関数は参照の時点で開いているので(§11.11)、
   ここで開くのは、`mk()()` のような呼び出しの結果や `r.go()` のようなフィールドの選択を呼ぶときである。
   行変数で終わる行には何もしない。

   開くのは呼び出し先の行であり、呼び出し元の行は書いたとおりに残る。
   呼び出し元の行が閉じた空の行のときは、行にラベルを持つ関数を呼べない。
   最も外側に `@ {}` と書いた束縛の本体や、行が `@ {}` の高階の引数の中がそうである。

   単一化が行の不一致で失敗したときは、次の 2 つの場合にメッセージを言い換える。
   `pub` で `@` を省略した宣言の本体の行(`new_pub_pure_row` が作るセル。§11.26)と衝突した場合は、
   pub の規則を明記する。
   この位置の行が空である場合は、
   sample.kel §9 の、入れ子の矢印で省略した `@` を `@ {}`(純粋)と読む規則を案内する。
   行が空になるのは、注釈に `@ {}` と書いたときか、高階の引数の行が `@ {}` のときである。
   言い換えるのは、呼び出し先の型が矢印で、失敗の原因が行にあるときだけである。
   行が原因かどうかは `row_failure` が判定する。
   呼び出し先が矢印なら、それと単一化する矢印の引数と返り値は新しい型変数なので、
   失敗するのは行の単一化か、スコーレム定数の漏れだけである。
   呼び出し先が型パラメータのスコーレム定数のように矢印でない型なら、
   失敗の原因は呼び出し先が関数でないことなので、言い換えない。
   その報告のメッセージも `スコープ付きの型` を含むので、`row_failure` だけでは区別できない。
   引数の型の不一致は言い換えない。
   pub の規則を明記するのは、
   スコーレム定数がスコープの外に漏れた失敗(`escape_failure`)を除いた場合である。
   run の本体の行には、本体の中で作ったヒープのラベルが入っている。
   呼び出し先の関数の行が外側の単相の行変数なら、単一化はそのラベルを行変数に入れようとして、
   ヒープがスコープの外に漏れたと報告する。
   この失敗は pub の有無によらず起き、本体のエフェクトが原因ではない。

   引数を検査する前に、`check_call_arity` が実引数の個数と仮引数の個数を比べる。
   実引数の並びが `_item` だけでできていて、仮引数の行が閉じた `_item` 行のときに限り、
   個数が違えば、引数の個数の不一致として報告する。
   この検査がなくても、閉じた行どうしの単一化は失敗する。
   しかし、その報告は行の途中で足りなくなったラベル `_item` を示すだけで、
   個数の違いだとは読み取りにくい。
   ラベル付きの引数を含む呼び出しと、仮引数の型がまだ決まっていない呼び出しは比べず、
   単一化に任せる。
   実引数を精緻化する前に比べるので、実引数の中に別のエラーがあっても、個数の不一致を先に報告する。
   perform の引数(§11.15)にも同じ検査を行う。 *)

  | T.Apply (f, arg) ->
      let tf = elab_exp env level eff f in
      (* 呼び出し先の行が閉じていれば、行の末尾を新しい行変数に替えて開いてから単一化する
         (使用時に行を開く規則。§11.26) *)
      let tf = open_closed_arrow level tf in
      let tr = new_var level in
      let pvar = new_var level in
      (* 関数の行を呼び出し元の eff と単一化してから、引数を期待型で検査する(§11.12) *)
      (try Unify.unify tf (TArrow (pvar, tr, eff))
       with Type_error msg ->
         (* pub で省略した @ は純粋を意味する。
            エフェクトを起こす関数の呼び出しが本体の行と衝突する形は、perform の場合よりよく起きる。
            しかし、単一化の一般的なメッセージ `行型ではありません: ς1` からは原因が分からない。
            そこで、perform の側(§11.15)と同じ言い換えをここでも行う *)
         let pub_pure = is_pub_pure_row eff in
         let callee_arrow = match repr tf with TArrow _ -> true | _ -> false in
         if pub_pure && callee_arrow && row_failure msg && not (escape_failure msg) then
           type_error ("pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: " ^ msg ^ ")")
         else if callee_arrow && row_failure msg && repr eff = TRowEmpty then
           type_error
             (msg
            ^ "(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)")
         else type_error msg);
      check_call_arity "呼び出す関数は" arg pvar;
      elab_check env level eff arg pvar;
      tr
(* ## 11.13 演算子とレコードの 4 操作

   演算子は AST に `BinOp` として残し、意味は第7章の表から引く。
   `+` は、クラス `Add` のメソッド `add` の呼び出しと同じように型付けする。
   前置の `-` は `Neg` のノードで表し、
   クラス `Neg` のメソッド `neg` の呼び出しと同じように型付けする。
   `method_scheme` がクラス表からメソッドの型スキームを引き、
   それを `(左辺, 右辺)` の行に対する矢印と単一化するだけで、演算子専用の推論規則は持たない。
   型スキームの最も外側の行は閉じた空の行なので、
   具体化した直後に `open_closed_arrow` で行の末尾を開く(§11.26)。
   呼び出し(§11.12)が呼び出し先の行を開くのと同じである。
   この対応には例外が 2 つある。
   `&&` と `||` は短絡評価するので、両辺を Boolean とする組み込みの演算である。
   `!=` は `Eq.eq` の否定である。
   演算子をノードとして残すのは、この 2 つの例外を第7章の表の中だけで扱うためである。
   エラーメッセージに演算子の表記をそのまま出せるという利点もある。

   レコードの操作は、拡張、選択、フィールドの除去、更新の 4 つである。
   更新(`{r with l = v}`)は、フィールドを除去してから拡張するのと同じ型付けで、
   フィールドの型が変わってよい。
   行にあった古い型は捨て、新しい型で拡張し直す。

   `RecordEmpty` の型が Unit なのは、Keleut の仕様による。
   Unit は空のレコードであり、専用の型ではない。

   構造的ヴァリアント `#Foo(v)` は、ラベル 1 つと新しい行変数からなる行を作る。
   行の末尾が開いているので、`#Foo(1)` はそのまま `#Foo | #Bar` を期待する位置にも渡せる。
   行を閉じるのは、match の網羅性検査(第10章)と型注釈である。 *)

  | T.BinOp (l, op, r) -> (
      let tl = elab_exp env level eff l in
      let tr = elab_exp env level eff r in
      match Prims.bin_op_sem op with
      | Prims.OpBool ->
          Unify.unify tl t_boolean;
          Unify.unify tr t_boolean;
          t_boolean
      | Prims.OpMethod (cls, m) | Prims.OpMethodNot (cls, m) ->
          let scheme = method_scheme cls m in
          let ret = new_var level in
          (* 演算子の型スキームの制約はクラスパラメータに付く 1 つだけなので、穴はちょうど 1 つである *)
          let it, hs = Unify.instantiate_ev ~loc:(Tree.loc_of node) level scheme in
          Tree.set_dict node (Tree.DUse hs);
          let it = open_closed_arrow level it in
          Unify.unify it (TArrow (TRecord (closed_item_row [ tl; tr ]), ret, eff));
          ret)
  | T.Not e ->
      Unify.unify (elab_exp env level eff e) t_boolean;
      t_boolean
  | T.Neg e ->
      let te = elab_exp env level eff e in
      let cls, m = Prims.neg_method in
      let ret = new_var level in
      let it, hs = Unify.instantiate_ev ~loc:(Tree.loc_of node) level (method_scheme cls m) in
      Tree.set_dict node (Tree.DUse hs);
      let it = open_closed_arrow level it in
      Unify.unify it (TArrow (TRecord (closed_item_row [ te ]), ret, eff));
      ret
  | T.RecordEmpty -> t_unit
  | T.RecordExtend (rest, l, v) ->
      let tv = elab_exp env level eff v in
      let rest_row = new_row_var level in
      Unify.unify (elab_exp env level eff rest) (TRecord rest_row);
      TRecord (TRowExtend (intern l, tv, rest_row))
  | T.RecordSelection (r, l) ->
      let tf = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, tf, rest)));
      tf
  | T.RecordRestriction (r, l) ->
      let tf = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, tf, rest)));
      TRecord rest
  | T.RecordUpdate (r, l, v) ->
      (* フィールドを除去してから拡張するのと同じ型付けである。
         フィールドの型は変わってよい *)
      let told = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, told, rest)));
      TRecord (TRowExtend (intern l, elab_exp env level eff v, rest))
  | T.Variant (s, v) -> TVariant (TRowExtend (intern s, elab_exp env level eff v, new_row_var level))
(* ## 11.14 ブロック、let、match、コンストラクタ

   ブロックは各文を同じ `eff` で推論し、末尾の式の型を返す。
   文がなければ Unit である。
   let と let rec は、束縛を追加した環境で本体を推論するだけで、
   主な処理は `elab_binding` と `elab_rec_bindings` の側にある(§11.28、§11.29)。

   match は照合対象を推論し、各節のパターンをその型に対して検査し、
   ガードを Boolean と、本体を共通の結果型と単一化する。
   照合対象が 1 つだけなのは、Keleut が後置の `v match {...}` しか持たないからである。
   タプルはレコードなので、`(a, b) match` と書けば、複数の値を同時に照合できる。

   網羅性検査はここでは実行せず、パターンの並びと型を検査キューに入れるだけである。
   検査は構造的ヴァリアントの行を閉じて型を書き換えることがあるので、
   できるだけ遅く実行する(第10章 §10.13)。
   ただし、キューに入れた検査は一般化より前に処理し終えなければならない。
   `close_variant_rows` が Generic になった行変数を単一化しようとすると、
   単一化はその変数を単一化変数として扱わず、原因と関係のない型エラーになるからである(第8章 §8.9)。
   `Exhaust.drain` でキューを処理する箇所は 1 か所ではないが、どれも一般化より前にある。
   束縛(`elab_binding` / `elab_rec_bindings`)では `generalize` の直前、
   トップレベルの式(`DExp`)では推論の直後である(§11.28、§11.40)。
   節のない `match` の照合対象が未束縛の型変数のまま残ると、
   `drain` はそれを `Never` に決めることがある。
   決めるかどうかは、`drain` に渡す束縛のレベルと型で判定する(第10章 §10.13)。

   コンストラクタの適用は `elab_construct` が処理する(§11.18)。 *)

  | T.Seq es ->
      let rec go = function
        | [] -> t_unit
        | [ last ] -> elab_exp env level eff last
        | s :: rest ->
            ignore (elab_exp env level eff s);
            go rest
      in
      go es
  | T.Let (b, body) ->
      let env2 = elab_binding env level eff b in
      elab_exp env2 level eff body
  | T.LetRec (bs, body) ->
      let env2 = elab_rec_bindings env level eff bs in
      elab_exp env2 level eff body
  | T.Match (scrut, clauses) ->
      let tscrut = elab_exp env level eff scrut in
      let tres = new_var level in
      List.iter
        (fun ((_, c) : T.clause) ->
          let seen = ref [] in
          let env2 = elab_pat env level seen tscrut c.T.cl_pat in
          (match c.T.cl_guard with
          | Some g -> Unify.unify (elab_exp env2 level eff g) t_boolean
          | None -> ());
          Unify.unify (elab_exp env2 level eff c.T.cl_body) tres)
        clauses;
      Exhaust.queue (List.map (fun ((_, c) : T.clause) -> (c.T.cl_pat, c.T.cl_guard <> None)) clauses) tscrut;
      tres
  | T.Construct (li, args) ->
      let (LongId comps) = li in
      elab_construct env level node
        (List.nth comps (List.length comps - 1))
        ~eff
        (List.map (fun (a : T.ctor_arg) -> (a.T.ca_label, a.T.ca_exp)) args)
(* ## 11.15 perform と行の単一化

   操作の呼び出しは 4 つの手順で型付けする。
   名前を解決し(§11.20)、完全名を木に書き、
   操作の型スキームの引数の行を期待型として引数を検査し(§11.19)、
   最後に次の単一化を行う。

   ```
   unify eff (TRowExtend (エフェクト名, Unit, 新しい行変数))
   ```

   perform の位置でそのエフェクトを起こしてよいかどうかは、この 1 行の単一化だけで検査する。
   `eff` が開いていればラベルが追加され、
   閉じていれば単一化が失敗して `ここでは実行できません` のエラーになる。
   エフェクトの集合の包含の判定も差分の計算も、実装していない。
   行の単一化がそれを兼ねる。

   行に入るラベルは、操作名ではなくエフェクト名である。
   `perform write(...)` で行に入るのは `write` ではなく `File` である。
   ハンドラが受け取る単位がエフェクトだからである。

   木に書き込む解決結果は、完全名 `Effect.op` の oid である。
   評価器は名前解決をやり直さず、この oid でハンドラを探す(第14章)。

   引数を検査モードで検査するのは、関数呼び出しの引数(§11.12)と同じ扱いにするためである。
   引数に直接書いた無名関数の本体は、操作の型に書いた行で推論されるので、
   その中の修飾しない操作名は、その行に現れているエフェクトで解決できる。
   `mk()` のような名前の参照でない式は、操作の型の対応する部分が関数型なら、
   閉じた行を開いてから単一化する。

   引数の矢印の行が、操作の型が求める空の行と一致しないときは、
   `elab_check` に渡したメッセージ(`op_row_note`)を添えて、操作の型の矢印は書いたとおりに読み、
   `@` の省略は `@ {}` と読むこと(sample.kel §9)を案内する。
   操作の型は型パラメータを持たないので、期待型の空の行は、
   型エイリアスを展開した後の操作の型の `@ {}` か `@` の省略から来る。
   空の行のエイリアス `P` を `@ P` と書いた矢印も、展開すると `@ {}` になる。
   引数の型の不一致には添えない(§11.19)。

   perform の位置の行が閉じた空の行で、エフェクトを追加できずに失敗したときは、
   関数呼び出し(§11.12)と同じく、この位置の行が空 = 純粋であることを添える。
   次の 3 種類の本体で操作を起こす形がそうである。
   `@ {}` と注釈した関数とインスタンスメソッドの本体、その中の handle の節の本体、
   検査モードで期待型の矢印から空の行を受け取った無名関数の本体である。
   最後のものには、たとえば、操作の型の中にある、行が空の矢印の位置に直接書いた無名関数と、
   仮引数の型が `@ {}` の矢印である実引数の位置に直接書いた無名関数が該当する。
   トップレベル、`pub` で `@` を省略した宣言、行変数を注釈した本体は、この分岐に入らない。
   型注釈が `@ {}` の矢印である値束縛の初期化式と、
   返り値の型注釈が `@ {}` の矢印である関数束縛の本体に書いた無名関数も、この分岐に入らない。
   どちらも本体を注釈と別に推論してから注釈と単一化するので、
   行の不一致は、注釈を満たさないエラーとして報告される。

   ### 再開しない操作の perform の型

   返り値の型が `Never` の操作は再開しない操作である。
   `Never` は値を持たない型なので、その perform の式は値を返さず、評価はハンドラの操作節に移る。
   そこで、この式の型は操作の返り値の型ではなく、穴 `???` と同じく新しい型変数にする。
   `case None => perform throw(..)` のように値が必要な位置に書けるのは、このためである。
   `Never` を、任意の型と一致するボトム型にはしない。
   単一化が対称でなくなるからである。
   任意の型の位置で使える、失敗するだけの関数は、返り値の型を型パラメータにして書く。
   この型変数がその型パラメータと単一化され、関数は一般化される。
   判定は型エイリアスを展開した後の型で行う。
   操作の型は `elab_type` が展開済みなので、`is_never` は返り値の型の型構成子を調べるだけでよい。 *)

  | T.Perform (li, arg) ->
      let eff_name, op, scheme = resolve_perform eff li in
      Tree.set_resolved node (Tree.ROp (intern (name_of eff_name ^ "." ^ name_of op)));
      let args_row, op_ret =
        match repr (Unify.instantiate level scheme) with
        | TArrow (a, r, _) -> (a, r)
        | _ -> bug "操作スキーマが矢印型ではありません"
      in
      check_call_arity ("操作 " ^ display_of op ^ " は") arg args_row;
      elab_check ~row_note:(op_row_note ("操作 " ^ display_of op ^ " の引数の型")) env level eff arg args_row;
      (try Unify.unify eff (TRowExtend (eff_name, t_unit, new_row_var level))
       with Type_error msg ->
         (* pub で @ を省略した宣言の本体の行は、new_pub_pure_row が作る専用のセルである(§11.26)。
            その行と衝突したときだけ、pub の規則を明記して案内する。
            単一化の一般的なメッセージ `行型ではありません: ς1` からは原因が分からないからである *)
         let pub_pure = is_pub_pure_row eff in
         if pub_pure then type_error "pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください)"
         else if repr eff = TRowEmpty then
           type_error
             ("エフェクト " ^ display_of eff_name ^ " をここでは実行できません(" ^ msg
            ^ ")(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)")
         else type_error ("エフェクト " ^ display_of eff_name ^ " をここでは実行できません(" ^ msg ^ ")"));
      (* 再開しない操作(返り値の型が Never)の perform の式は、穴と同じく、周囲が要求する型になる *)
      if is_never op_ret then new_var level else op_ret
(* ## 11.16 環境に置く resume の型

   `resume` の型付けは、`env.resume_ty` が `Some` のときだけ成功する。
   `Some` が入るのは操作節の中だけなので、resume を操作節の中でしか書けないことが、
   環境の内容だけで保証される。

   `resume_ty` が持つ組は、操作の返り値の型と handle 式全体の型である。
   `resume(v)` は、操作の返り値の型を期待型として `v` を検査し(§11.19)、handle 式全体の型を返す。
   行の不一致に添えるメッセージは、perform の引数と同じである(§11.15)。
   これは深いハンドラ(deep handler)の型付けである。
   resume を呼ぶと残りの計算が同じハンドラの中で最後まで実行され、その最終結果が返ってくることを、
   この型が表している。

   引数の省略は、操作の返り値の型が Unit のときだけ許す(sample.kel:549)。
   `Unit` と単一化するだけなので、実装は 1 行で済む。

   resume を値の環境に入れず `env` のフィールドにするのは、
   値として束縛できないようにするためである。
   値として束縛できると、節を抜けた後に呼べる継続が作れてしまい、
   cancel による自動の巻き戻しが成り立たなくなる。
   環境だけでは防げないクロージャへのキャプチャは、§11.21 の 2 段階の検査で扱う。

   再開しない操作(§11.15)の節では、`resume_ty` を `None` のままにし、
   代わりに `no_resume` にその操作名を入れる。
   `resume` があったとき `no_resume` がその操作名なら、
   再開しない操作の節であることを明記した診断を出す。
   クロージャの本体の `resume` も、`resume_ty` が `None` の環境で推論されるので、
   この分岐でエラーになる。
   節の中に書いた入れ子の `handle` の本体の `resume` も、外側の節の継続を指すので同じ診断になる。
   入れ子の `handle` の操作節の `resume` は、その節が `resume_ty` を設定し直すので受理される。
   そのため、再開しない操作の節では §11.21 の静的な検査は不要である。

   操作節のガード、`return` 節、`cancel` 節でも、`resume_ty` を `None` にし、
   `no_resume` にその位置を入れる。
   `resume` があったとき `no_resume` が `Some` なら、その位置を明記した診断を出す。
   位置は最も内側のものを使う。
   たとえば、再開しない操作の節の中にある入れ子の `handle` の `return` 節では、
   `return` 節の診断になる。
   `resume_ty` と `no_resume` がどちらも `None` なのは操作節の外だけなので、
   そこで出す診断は、resume を操作節の中でだけ使えることを述べる。 *)

  | T.Handle (body, clauses) -> elab_handle env level eff clauses body
  | T.Resume arg -> (
      match env.resume_ty with
      | None -> (
          match env.no_resume with
          | Some (No_never_clause op) ->
              type_error ("再開しない操作 " ^ display_of op ^ " の節には resume を書けません(操作の返り値の型が Never です)")
          | Some No_guard -> type_error "操作節のガードには resume を書けません(ガードは節が選ばれる前に評価されるので、継続を再開できません)"
          | Some No_return_clause -> type_error "return 節には resume を書けません(再開する継続がありません)"
          | Some No_cancel_clause -> type_error "cancel 節には resume を書けません(再開する継続がありません)"
          | None -> type_error "resume は操作節の中でのみ使えます")
      | Some (op_ret, tres) ->
          (match arg with
          | Some e -> elab_check ~row_note:(op_row_note "操作の返り値の型") env level eff e op_ret
          | None ->
              (* 引数を省略できるのは、操作の返り値の型が Unit のときだけである(sample.kel:549) *)
              Unify.unify t_unit op_ret);
          tres)
(* ## 11.17 run

   `run h { ... }` はスコープ付きの可変状態である。
   中で作った `Ref` を外に持ち出せないことを、ランク 2 多相を使わずに保証する。
   実装は次の 3 つの手順からなる。

   1. 結果用の変数を、スコープの外のレベル L で作る
   2. スコーレム定数 `h` を、1 つ深いレベル L+1 で作る。これがリージョンの名前になる
   3. 本体をレベル L+1 と行 `{Heap[h] | eff}` で推論し、最後に結果用の変数と単一化する

   手順 3 の単一化で、`occurs_adjust` が本体の型に残るレベル L+1 の変数を調べる。
   単一化変数なら、レベルを L に下げるだけである。
   スコーレム定数はレベルを下げられないので、脱出検査がエラーにする(§8.3)。
   この検査が成り立つのは、結果用の変数をスコープの外のレベル L で作るからである。
   L+1 で作ると、`occurs_adjust` は L+1 のスコーレム定数を漏れとみなさず、
   スコーレム定数が脱出検査に通ってしまう。
   Diktor はレベルをグローバルな状態に持たず、引数で渡す。
   そのため脱出検査に影響するのは、2 つの変数を作る順序ではなく、それぞれを作るレベルである。

   同じ仕組みを、注釈の型パラメータにも使う。
   §11.25 の `make_rigids` と §11.28 の `lvl = level + 1` は、
   注釈の型パラメータをスコーレム定数にして本体を検査する。
   そのスコーレム定数は、スコープを出るところで Generic に変える。
   名前が違うだけで、行っていることは run と同じである。

   型 `Ref[h, A]` に加えてエフェクト行にも `Heap[h]` を置くのは、
   `run h { let r = Ref.new(0); fn() => Ref.get(r) }` のような式があるからである。
   返る関数の型に `h` は現れず、`h` はエフェクト行にだけ残る。
   行を調べなければ、この関数をリージョンの外へ持ち出せてしまう。

   `h` のカインドは `Type` である(sample.kel §10)。
   `new_rigid` を既定のカインドで呼ぶからで、リージョン専用のカインドは持たない。
   その結果は 2 つある。
   行の位置に書いた `@ h` は `行カインドではない型パラメータです: h` のエラーになる。
   値の型の位置に書いた `(h) => Int32` は受理される。
   値の型の位置が要求するのはカインド `Type` だからである(§11.3)。
   `test/kinds.t` の regionkind / regionkind2 が、この 2 つを確かめる。

   リージョン専用のカインドを設けても、変わるのは値の型の位置に `h` と書けなくなることだけである。
   値の型の位置に `h` を書けても、型 `h` の値を作る手段はないので、健全性は保たれる。
   一方、専用のカインドを設けるには、第1章のカインドの定義、`same_kind` と `kind_of`、宣言表、
   `show_kind`、組み込みの型スキームを書き換える必要がある。

   入れ子の run の内側で外側の `Ref` を読めないのは仕様どおりで、
   Haskell の ST と同じリージョンの安全性である。
   単一化は、これを第8章 §8.7 が述べるスコーレム定数どうしの不一致として報告する。 *)

  | T.Run (h, body) ->
      (* 結果用の変数はスコープの外の level で作り、スコーレム定数は level+1 で作る。
         本体は level+1 と、Heap[h] を追加した行で推論する *)
      let result = new_var level in
      let heap = new_rigid (level + 1) in
      let env2 = { env with types = SMap.add h heap env.types } in
      let t = elab_exp env2 (level + 1) (TRowExtend (eff_heap, heap, eff)) body in
      Unify.unify result t;
      result

(* ## 11.18 コンストラクタの適用

   式でのコンストラクタの適用は、パターンの側(§11.8)と対になる処理である。
   違いは 2 つある。

   - 式ではすべてのフィールドが必須である。
     パターンでは省略したフィールドを `_` と読むが、
     値を作るときに、書かなかったフィールドを暗黙に埋める規則はない。
   - 割り当ての向きが逆である。
     パターンは「フィールド → 実引数」、式は「実引数 → フィールド」の配列を木に書く。
     評価器が引数をソースの順に評価しながら、
     その値をこの配列でフィールドの位置へ書き込めるようにするためである。

   `eff` が必要なのは、引数を推論するときだけである。
   引数のないコンストラクタは `elab_exp` の `Ident` の経路からも来るので、
   `eff` を省略可能な引数にしている。
   引数があるのに `eff` がないのは呼び出し元のバグなので、`bug` で内部エラーにする。
   型検査器の内部の矛盾は、ユーザのプログラムのエラーではないからである。

   newtype のフィールドの矢印は書いたとおりに読み、`@` の省略は `@ {}` と読む(sample.kel §9)。
   コンストラクタの引数の単一化が行の不一致で失敗したときは、エラーにこの規則を添える。
   添えるのは、宣言したフィールドの型に、行の閉じた矢印か、
   型引数に書いた閉じた行があるときだけである。
   フィールドの型が型パラメータ(`Cons` の `A`)のときは、
   行の閉じた矢印はフィールドの宣言ではなく実引数の側から型パラメータに入ったもので、
   この規則は原因ではない。
   このときは、仮引数の型が型変数である関数の呼び出し(§11.12)と同じく、単一化の報告をそのまま出す。
   たとえば、エフェクトを起こすクロージャを newtype に入れて純粋な関数として取り出そうとする形は、
   この単一化で失敗し、この規則を添えたエラーになる。
   行が原因の失敗かどうかは、§11.12 と同じ `row_failure` で判定する。

   引数は、フィールドの型を期待型として渡さずに推論してから単一化する。
   そのため、ここでは実引数の閉じた行を開かない。
   名前で参照した関数は参照の時点で開いているので(§11.11)、
   閉じた行のまま単一化されるのは、
   呼び出しの結果やフィールドの選択のような、名前の参照でない式だけである。
   そうした式を行の違うフィールドに入れるには、無名関数で包むか、いったん名前に束縛する
   (LangSpec §13.2 の制限の 1 つ目)。 *)

and elab_construct env level node cname ?eff args =
  let ctor = Decls.resolve_ctor (intern cname) in
  match Hashtbl.find_opt Decls.ctor_owner ctor with
  | None -> type_error ("未知のコンストラクタ: " ^ cname)
  | Some dname ->
      (* コンストラクタの可視性は、所属する newtype の pub に従う *)
      Decls.check_ctor_visible ctor dname;
      let dd = Hashtbl.find Decls.datas dname in
      (* dd_opaque の型は組み込みの不透明型だけで、コンストラクタを持たないので、
         ここには来ない。下の分岐は、念のために置いた検査である *)
      if dd.Decls.dd_opaque then type_error ("newtype " ^ display_of dname ^ " の表現は ??? で隠されています")
      else
        let ct = List.find (fun c -> c.Decls.ct_name = ctor) dd.Decls.dd_ctors in
        let nfields = List.length ct.Decls.ct_fields in
        let assigned = Array.make nfields false in
        let arg_to_field =
          Array.of_list
            (List.map
               (fun (label, _) ->
                 match label with
                 | None ->
                     let rec first i =
                       if i >= nfields then type_error ("コンストラクタ " ^ cname ^ " の引数が多すぎます")
                       else if assigned.(i) then first (i + 1)
                       else i
                     in
                     let i = first 0 in
                     assigned.(i) <- true;
                     i
                 | Some l ->
                     let lo = intern l in
                     let rec find i = function
                       | [] -> type_error ("コンストラクタ " ^ cname ^ " にフィールド " ^ l ^ " はありません")
                       | f :: rest -> if f.Decls.fi_label = Some lo then i else find (i + 1) rest
                     in
                     let i = find 0 ct.Decls.ct_fields in
                     if assigned.(i) then type_error ("フィールド " ^ l ^ " が二重に指定されています");
                     assigned.(i) <- true;
                     i)
               args)
        in
        if Array.exists not assigned then
          type_error ("コンストラクタ " ^ cname ^ " の引数が不足しています(式では全フィールド必須)");
        Tree.set_resolved node (Tree.RCtor (dname, ctor, arg_to_field));
        let subst =
          List.map (fun (i : var_info) -> (i.vid, Unify.new_class_var ~kind:i.vkind ~classes:i.vcls level)) dd.Decls.dd_params
        in
        List.iteri
          (fun ai (_, e) ->
            let f = List.nth ct.Decls.ct_fields arg_to_field.(ai) in
            let ety =
              match eff with
              | Some eff -> elab_exp env level eff e
              | None -> bug "elab_construct: 引数つきなのに eff がない"
            in
            let fty = Unify.subst_params level subst f.Decls.fi_ty in
            (* エフェクトを起こすクロージャを newtype に入れる形は、この単一化で失敗する。
               行が原因の失敗にだけ、sample.kel §9 の規則を添える。
               フィールドの型に閉じた行を書いた箇所がなければ、この規則は原因でないので添えない *)
            try Unify.unify ety fty
            with Type_error msg when row_failure msg && has_closed_arrow f.Decls.fi_ty ->
              type_error
                (msg ^ "(コンストラクタ " ^ cname
               ^ " のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)"))
          args;
        TCon (dname, List.map snd subst)

(* ## 11.19 検査モード

   §11.12 で述べた、引数を期待型で検査する処理は、`elab_check` が実装する。
   双方向の型検査を簡略にしたものである。
   期待型を渡す式は、無名関数とレコード拡張の 2 種類だけである。
   呼び出しの引数リストは、レコード拡張の連鎖に脱糖されている(第3章)。
   それ以外の式は、通常どおり型を推論してから期待型と単一化する。
   期待型と式の形が合わないときは、エラーにせず `fallback` を呼ぶ。
   そのため、検査モードを使ったことが原因で型検査が失敗することはない。

   無名関数の分岐に入るのは、期待型が矢印で、その引数がラベル `_item` だけの閉じた行で、
   引数の個数が一致するときだけである。
   このとき本体は、期待型のエフェクト行 `eexp` で推論する。
   そのため、無名関数の本体の推論を始める前に、行のラベルが決まる。

   呼び出しの引数リストは `_item` の `RecordExtend` の連鎖なので、レコード拡張の分岐も必要である。
   期待型の行から `rewrite_row` でフィールドを 1 つ取り出し、その型で値を検査し、
   残りを再帰的に検査する。
   この再帰があるので、期待型は 2 番目以降の引数に書いた無名関数にも伝わる。
   `rewrite_row` が失敗したとき(そのラベルがないとき)も `fallback` を呼び、
   エラーは通常の経路の単一化が報告する。

   `fallback` は、期待型が矢印なら、
   推論した型の閉じた行を `subsume_closed` で開いてから単一化する。
   関数型を要求する位置で行を開く規則(§11.26)である。
   仮引数の型が関数型である実引数は、関数型を要求する位置にあるので、この規則が適用される。
   名前で参照した関数は参照の時点で開いているので(§11.11)、
   ここで行が開くのは `mk()` のような名前の参照でない式である。
   無名関数の分岐は本体を返り値の型 `rexp` で検査し、
   レコード拡張の分岐は各フィールドを対応するフィールドの型で検査する。
   どちらも `elab_check` を再帰的に呼ぶ。
   そのため、実引数に直接書いた無名関数の本体、レコード式のフィールド、タプル式の要素も、
   その期待型が矢印なら `fallback` で開く。
   入れ子になっていても同じである。

   `row_note` は、行の不一致のエラーに添えるメッセージである。
   渡すのは、perform の引数と resume の引数の検査(§11.15、§11.16)だけである。
   `fallback` は、`row_note` が渡されていて、推論した型と期待型がどちらも矢印で、
   期待型の行が閉じた空の行のときに、引数の個数、引数、返り値、行の順に調べる。
   メッセージを添えるのは、最後の行の単一化が失敗したときだけである。
   調べる順序は `Unify.unify` の矢印の分岐と同じなので、
   `row_note` を渡しても、受理するプログラムと拒否するプログラムは変わらない。
   引数の型の不一致は行の単一化より先に報告されるので、メッセージは付かない。
   エラーの文字列から行の失敗を判別する `row_failure` は、ここでは使わない。
   レコードのフィールドのエラー(`ラベル y がありません`)のように、
   行の不一致でないエラーも、行の失敗と同じ文字列になるからである。
   関数呼び出しの引数の検査には、`row_note` を渡さない。
   仮引数の型が型変数のとき、期待型の空の行は、前の引数から決まったものかもしれない。
   そこで `@` の省略を案内すると、原因を取り違える。

   検査に成功したノードにも、`set_ty` で型を書く。
   期待型を渡したノードは `elab_exp` を通らないので、ここで書かないと、
   木に型のないノードが残る。 *)

and elab_check ?row_note env level eff ((_, e) as node : T.exp) expected =
  at_node node @@ fun () ->
  let fallback () =
    let ty = subsume_closed level (elab_exp env level eff node) expected in
    match (row_note, repr ty, repr expected) with
    | Some note, TArrow (p1, r1, e1), TArrow (p2, r2, e2) when repr e2 = TRowEmpty -> (
        (* 引数の個数、引数、返り値を先に調べ、最後の行の単一化が失敗したときにだけメッセージを添える。
           調べる順序は Unify.unify の矢印の分岐と同じなので、
           row_note を渡しても、受理するプログラムと拒否するプログラムは変わらない *)
        Unify.check_arity ty expected p1 p2;
        Unify.unify p1 p2;
        Unify.unify r1 r2;
        try Unify.unify e1 e2 with Type_error msg -> type_error (msg ^ note))
    | _ -> Unify.unify ty expected
  in
  match (e, repr expected) with
  | T.Lambda { l_params; l_body }, TArrow (pexp, rexp, eexp) -> (
      match repr pexp with
      | TRecord prow ->
          let fields, tail = row_fields prow in
          if
            repr tail = TRowEmpty
            && List.length fields = List.length l_params
            && List.for_all (fun (l, _) -> l = l_item) fields
          then (
            let seen = ref [] in
            let env2 = List.fold_left2 (fun env p (_, t) -> elab_pat env level seen t p) env l_params fields in
            Tree.set_ty node expected;
            elab_check ?row_note env2 level eexp l_body rexp;
            (* 検査モードの無名関数も、引数のパターンを網羅性検査のキューに追加する。
               型注釈のある高階関数の引数に渡した無名関数は、この分岐を通る。
               elab_exp の側だけで追加すると、そうした無名関数の引数のパターンが検査されない。
               本体を検査した後で追加するのは、本体の中の let がキューを処理するときに、
               この項目まで処理して行を早く閉じてしまわないようにするためである *)
            List.iter2 (fun p (_, t) -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) l_params fields)
          else fallback ()
      | _ -> fallback ())
  | T.RecordExtend (rest, l, v), TRecord row -> (
      match Unify.rewrite_row row (intern l) with
      | fty, rest_row ->
          Tree.set_ty node expected;
          elab_check ?row_note env level eff v fty;
          elab_check ?row_note env level eff rest (TRecord rest_row)
      | exception Type_error _ -> fallback ())
  | _ -> fallback ()

(* ## 11.20 操作名の解決

   Keleut は操作名の重複を許す。
   標準環境の `Console.write`(sample.kel:466)と、仕様の sample.kel が宣言する `File.write`(:594)は、
   同じ操作名を持つので、操作名がプログラム全体で一意だとは仮定できない。

   修飾された操作名は、宣言表を直接引いて解決する。
   修飾されていない操作名は、次の 2 段階の規則で解決する。

   1. 操作名を宣言しているエフェクトが 1 つなら、行に現れているかどうかを問わず、それに解決する。
      候補が 1 つなら推測の余地がない。
      型注釈のない `let` の行は新しい行変数なので、その中の perform の行には候補が 1 つも現れない。
      1 段階目でも候補が行に現れることを求めると、
      そうした perform はすべて修飾しなければならなくなる。
   2. 候補が 2 つ以上のときは、現在の `eff` 行に現れる候補を数え、
      それが 1 つだけならそれに解決する。
      同じエフェクトが行に 2 回以上現れても、候補としては 1 つと数える。
      行の中のラベルの位置は使わない。

   `test/typecheck_m6.t` の onecand / twocand が、この 2 段階の振る舞いを確かめる。
   先に宣言された候補を選ぶ、という規則は採らない。
   その規則では解決が宣言の順序に依存し、プログラムを書いた人の意図と違う操作に解決することがある。

   2 段階目で行の中の位置を使わないのは、ラベルの順序だけが違う行が同じ型だからである(第8章 §8.6)。
   位置で選ぶと、同じ型の行なのに同じ `perform op` が別の操作に解決され、
   型の等価性と操作の意味が食い違う。
   行に候補が 2 つ以上現れる位置では、`File.write` のように修飾して書く。
   sample.kel:620-625 の `copy` は、2 つ目の `perform` の行に `File` も `Console` も現れているので、
   `File.write` と修飾してある。
   行に現れる候補が 1 つのときに解決する形は `test/typecheck_m6.t` の onerow.kel が、
   2 つ現れて修飾を求める形は同じファイルの ambigrow.kel が確かめる。

   行に現れる候補の集合は、本体の推論がその perform に達した時点のものである。
   型注釈のない関数の行には、本体の推論が操作に出会った順にラベルが加わる。
   そのため、同じ本体でも文の順序によって、候補が行に現れるかどうかが変わることがある。
   それでも、型検査での解決と、実行時にどのハンドラが操作を受け取るかは食い違わない。
   perform は解決済みの完全な名前の oid を持つので、`E2` のハンドラが `E1.op` を受け取ることはない。
   `E1.op` は `E2` のハンドラを通り過ぎて、`E1` のハンドラに届く(`test/eval.t` の leftmostrun.kel)。

   2 段階目で行に候補が 1 つも現れないときは、推測せず、`File.write` のように修飾するよう案内する。
   2 つ以上現れるときは、行に現れる候補を宣言の順に並べ、修飾した形をすべて示す。
   候補は宣言の順に並べるので、どちらの診断も行の中のラベルの順序によらない。

   行の中のラベルの順序は、操作名の解決にも型の等価性にも使わない。
   順序だけが違う行どうしは単一化できる(`test/typecheck_m6.t` の roworder)。 *)

and resolve_perform eff li =
  match li with
  | LongId [ ename; op ] -> (
      let e = Decls.resolve_unit (intern ename) in
      match Decls.find_effect e with
      | None -> type_error ("未知のエフェクト: " ^ ename)
      | Some info -> (
          match List.assoc_opt (intern op) info.Decls.ef_ops with
          | Some scheme -> (e, intern op, scheme)
          | None -> type_error ("エフェクト " ^ ename ^ " に操作 " ^ op ^ " はありません")))
  | LongId [ op ] -> (
      let opo = intern op in
      match Decls.op_candidates opo with
      | [] -> type_error ("未知の操作: " ^ op)
      | [ e ] -> (e, opo, List.assoc opo (Option.get (Decls.find_effect e)).Decls.ef_ops)
      | many -> (
          (* 現在の eff 行に現れる候補が 1 つだけなら、それに解決する。行の中の位置は使わない(§11.20) *)
          let labels = List.map fst (fst (row_fields eff)) in
          match List.filter (fun e -> List.mem e labels) many with
          | [ e ] -> (e, opo, List.assoc opo (Option.get (Decls.find_effect e)).Decls.ef_ops)
          | [] ->
              type_error
                ("操作 " ^ op ^ " は複数のエフェクト("
                ^ String.concat ", " (List.map display_of many)
                ^ ")に属します。" ^ display_of (List.hd many) ^ "." ^ op ^ " のように修飾してください")
          | in_row ->
              type_error
                ("操作 " ^ op ^ " は、この位置の行に現れる複数のエフェクト("
                ^ String.concat ", " (List.map display_of in_row)
                ^ ")に属します。"
                ^ String.concat "、" (List.map (fun e -> display_of e ^ "." ^ op) in_row)
                ^ " のどれかに修飾してください")))
  | li -> type_error ("不正な操作名です: " ^ show_long_id li)

(* ## 11.21 resume の第二級性

   resume は専用の構文木のノード(`Resume`)で、名前ではないので、
   変数に束縛することも値として渡すこともできない。
   それでも、構文だけでは resume が第二級であることを保証できない。

   ```
   case print(m) => { let f = fn() => resume(); f() }
   ```

   この操作節は、構文としては書ける。
   `resume` 自体は値になっていないが、それを含むクロージャが値になっており、操作節の外へ持ち出せる。

   そこで、次の 2 段階の検査で、resume を操作節の外へ持ち出せないようにする。

   1. 静的な検査：`check_resume_static` が操作節の本体を走査し、
      クロージャの本体の中にある、その操作節の `Resume` をエラーにする。
   2. 動的な検査：操作節が終わるときに、
      継続が生きていることを表すフラグ(第12章の `r_alive`)を評価器(第14章)が下ろし、
      その後の resume の呼び出しを実行時エラーにする。

   評価器(第14章)がクロージャを作るのは、無名関数(`Lambda` のノード)と関数束縛を評価するときである。
   関数束縛は、`let` と `let rec` の束縛のうち `lb_params` が `Some` のもので、
   `let f() = resume(41)` の形をしている。
   静的な検査は、この 2 つの本体をクロージャの本体として走査する。
   `with` はパーサが無名関数に脱糖する(§3.8)ので、無名関数として扱われる。
   値束縛(`lb_params` が `None`)の右辺は束縛の時点で評価されるので、
   外側と同じ `in_lambda` のまま走査する。
   操作節の本体に `let {value, output} = resume()` と書けるのは、このためである。

   関数束縛の本体の resume は、その関数を操作節の中で呼ぶだけであっても拒否する。
   `fn() => resume(41)` を変数に束縛して操作節の中で呼ぶ形を拒否するのと、同じ扱いである。
   クロージャが操作節の外へ出るかどうかは、構文だけでは決まらないからである。

   クロージャの本体は定義時の環境で評価される(§14.5)。
   そのため、操作節の継続を持つことがあるクロージャは、
   その操作節の本体の中に書かれたものだけである。
   静的な検査がクロージャの本体として走査する構文は、
   評価器(第14章)がクロージャを作る構文とそろえておく必要がある。
   クロージャを作る構文が増えたのに静的な検査をそろえ忘れた場合でも、
   動的な検査が、操作節の外での再開を実行時エラーにする。

   走査の途中で内側の `Handle` に出会ったら、その本体は走査し、節は走査しない。
   内側のハンドラの操作節は、その handle 式を型付けるときに、節ごとに検査されるからである。
   ここで内側の節まで走査すると、内側の操作節の resume を外側の操作節の resume と取り違える。

   2 段階の検査により、継続は操作節の外で呼べない。
   そのため、操作節を抜ける時点で、継続がまだ生きているかどうかが確定し、
   cancel による自動の巻き戻しが成り立つ(sample.kel:546-549)。
   継続がどこかのクロージャに残っている可能性があると、巻き戻しの時点を決められない。 *)

and check_resume_static ?(in_lambda = false) (((_, e) as node) : T.exp) =
  at_node node @@ fun () ->
  let go = check_resume_static ~in_lambda in
  (* 関数束縛(lb_params が Some)の本体は、無名関数の本体と同じくクロージャの本体として走査する *)
  let go_binding ((_, b) : T.let_binding) =
    match b.T.lb_params with
    | Some _ -> check_resume_static ~in_lambda:true b.T.lb_body
    | None -> go b.T.lb_body
  in
  match e with
  | T.Resume arg ->
      if in_lambda then type_error "resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)"
      else Option.iter go arg
  | T.Lambda { l_body; _ } -> check_resume_static ~in_lambda:true l_body
  | T.Handle (b, _) -> go b
  | T.Bool _ | T.Number _ | T.Text _ | T.Ident _ | T.Hole | T.RecordEmpty -> ()
  | T.Apply (f, a) ->
      go f;
      go a
  | T.Construct (_, args) -> List.iter (fun (a : T.ctor_arg) -> go a.T.ca_exp) args
  | T.Variant (_, v) -> go v
  | T.BinOp (l, _, r) ->
      go l;
      go r
  | T.Not v | T.Neg v -> go v
  | T.Let (b, rest) ->
      go_binding b;
      go rest
  | T.LetRec (bs, rest) ->
      List.iter go_binding bs;
      go rest
  | T.Seq es -> List.iter go es
  | T.Match (scrut, cs) ->
      go scrut;
      List.iter
        (fun ((_, c) : T.clause) ->
          Option.iter go c.T.cl_guard;
          go c.T.cl_body)
        cs
  | T.RecordExtend (r, _, v) | T.RecordUpdate (r, _, v) ->
      go r;
      go v
  | T.RecordRestriction (r, _) | T.RecordSelection (r, _) -> go r
  | T.Perform (_, a) -> go a
  | T.Run (_, b) -> go b

(* 操作の返り値の型が Never なら真を返す。
   型エイリアスは elab_type が展開済みなので、型構成子を調べるだけでよい *)
and is_never t = match repr t with TCon (n, []) -> n = intern "Never" | _ -> false

(* ## 11.22 handle の節を 3 種類に分ける

   handle の節は、エフェクト名ではなく操作名で書く。
   パーサから見ればどれもコンストラクタパターンなので、節の種別はここで決める。

   | 節の形 | 種別 | 意味 |
   |---|---|---|
   | `case print(m) =>` | 操作節 | 小文字で始まる名前は操作。`Print.print` と修飾もできる |
   | `case return(x) =>` | return 節 | 本体が値を返して終わったときの後処理。1 つまで。修飾できない |
   | `case cancel =>` | cancel 節 | 巻き戻されたときの後始末。1 つまで。修飾できない |

   `return` と `cancel` は予約語ではなく、下の `classify` が名前で区別しているだけである。
   `cancel` は、引数を取らない形だけを受理する。
   `cancel(reason)` の形は Diktor が実装しておらず、`noimpl` で報告する。
   操作節は 1 つ以上必要である。
   操作節が 1 つもない handle は、プログラムの誤りとみなしてエラーにする。

   修飾できるのは操作節だけである(sample.kel:518-519)。
   `return` と `cancel` は操作名ではなく handle の節の名前なので、修飾先を書いても、
   対象エフェクトの決定(§11.23)には使われない。
   `classify` は `List.rev comps` の先頭、つまり修飾名の末尾の要素で節を分類する。
   そのため、修飾された `return` / `cancel` は専用の分岐で検出し、修飾を外すよう促すエラーにする。
   この分岐は、`cancel` / `return` の分岐より前に置く必要がある。
   後ろに置くと、末尾の要素だけを調べる分岐が先に一致し、
   `case File.return(x)` の `File.` が黙って捨てられる。
   `test/typecheck_m6.t` の qualret / qualcancel が、この振る舞いを確かめる。

   操作節は、同じ操作に対して複数書ける。
   絞り込みパターンやガードで場合を分けて書くことができ、
   評価器は実行時に、match と同じく、一致しなければ次の節へ進む方法で節を選ぶ。
   引数のパターンが必ず一致する節とは、ガードがなく、
   その節だけを持つ match が引数の並びについて網羅的になる節である。
   この節より後ろに同じ操作の節を書くと、その節には到達しないので、警告を出す(§11.24)。

   分類の結果は、`set_resolved` で木に書く。
   評価器が節の種別を判定し直さないようにするためで、§11.8 と同じ方針である。

   次のエラーは、`at_node` でその節の位置を付けて報告する。
   節の先頭の形のエラー、2 つ目の return 節と cancel 節、return 節と cancel 節の修飾、
   対象エフェクトに属さない操作、操作節の引数の個数とラベルのエラーは、
   節のパターン(`case` の直後)を指す。
   return 節と cancel 節にガードを書いたエラーは、ガードの式を指す。
   handle 式全体の位置で報告すると、どの節のエラーかが位置から分からないからである。
   対象エフェクトの決定(§11.23)と、決まった対象の操作を網羅しているかどうかの検査は、
   節の位置を付けずに報告するので、そのエラーは handle 式の位置を指す。
   未知のエフェクトを指定した修飾のように、1 つの節の修飾だけから決まるエラーもここに入る。
   修飾を持つ最初の節の位置で報告することもできるが、
   そうすると §11.23 の中に位置の規則が 2 つできる。
   操作節が 1 つもないエラーも、特定の節が原因ではないので、handle 式の位置で報告する。
   操作節のガードの式の型が Boolean でないエラーと、節の値の型が節どうしで合わないエラーにも、
   節の位置を付けない。
   `test/handle_clause_loc.t` が、それぞれの位置を確かめる。
   到達不能な節の警告にも位置を付けない(`test/eval.t`)。 *)

and elab_handle env level eff clauses body =
  let classify ((_, c) as cnode : T.clause) =
    at_node c.T.cl_pat @@ fun () ->
    match snd c.T.cl_pat with
    | T.PVar "cancel" -> `Cancel cnode
    | T.PCtor (LongId comps, args) -> (
        match List.rev comps with
        (* return / cancel は操作名ではないので修飾できない。
           この分岐を `cancel` / `return` の分岐より前に置かないと、
           修飾名の末尾の要素だけを調べる後ろの分岐が先に一致し、修飾が黙って捨てられる *)
        | (("return" | "cancel") as kw) :: _ :: _ ->
            type_error (kw ^ " 節は修飾できません(" ^ kw ^ " は操作名ではなく handle の節の名前です。修飾を外してください)")
        | "cancel" :: _ ->
            if args <> [] then noimpl "cancel(reason)(v0 は case cancel のみ)" else `Cancel cnode
        | "return" :: _ -> (
            match args with
            | [ { T.cap_label = None; cap_pat } ] -> `Return (cap_pat, cnode)
            | _ -> type_error "return 節は case return(x) の形で書いてください")
        | op :: quals when op <> "" && op.[0] >= 'a' && op.[0] <= 'z' ->
            `Op
              ( intern op,
                (match quals with [] -> None | _ -> Some (Decls.resolve_unit (intern (String.concat "." (List.rev quals))))),
                args,
                cnode )
        | _ -> type_error ("handle の節は操作名 / return / cancel で始めてください: " ^ show_long_id (LongId comps)))
    | _ -> type_error "handle の節は操作名 / return / cancel で始めてください"
  in
  let classified = List.map classify clauses in
  let ops = List.filter_map (function `Op (op, q, args, cnode) -> Some (op, q, args, cnode) | _ -> None) classified in
  let rets = List.filter_map (function `Return (p, cnode) -> Some (p, cnode) | _ -> None) classified in
  let cancels = List.filter_map (function `Cancel cnode -> Some cnode | _ -> None) classified in
  (match rets with
  | _ :: (_, (_, c)) :: _ -> at_node c.T.cl_pat (fun () -> type_error "return 節は1つまでです")
  | _ -> ());
  (match cancels with
  | _ :: (_, c) :: _ -> at_node c.T.cl_pat (fun () -> type_error "cancel 節は1つまでです")
  | _ -> ());
  (if ops = [] then type_error "handle には少なくとも1つの操作節が必要です");
(* ## 11.23 対象エフェクトの決定

   節は操作名で書くので、このハンドラがどのエフェクトを処理するのかを決める必要がある。
   このエフェクトを、対象エフェクトと呼ぶ。
   規則は 2 段階である。
   sample.kel §9 は、修飾のない操作名の解決規則を perform と handle で書き分けている(sample.kel:521-531)。
   この 2 段階は、そのうち handle の側の規則である。

   1 段階目は、操作節の修飾を使う。
   操作節が 1 つでも修飾されていれば、その修飾先が対象である。
   修飾されていない節は、そのエフェクトの操作として読む。
   修飾先が 2 つ以上に分かれていれば、エラーにする(sample.kel:530-531)。
   実装は下の `List.sort_uniq compare quals` の 1 行である。
   要素が 1 つなら対象が決まり、2 つ以上ならエラーになり、空なら 2 段階目へ進む。
   判定に使うのは操作節の修飾だけである。
   修飾された `return` / `cancel` は §11.22 が先にエラーにするので、ここでは扱わない。
   曖昧な節を 1 つ修飾したら、残りの節もすべて修飾しなければならない、という規則は採らない。
   修飾は曖昧さを解消する手段であって、書式の要求ではないからである。
   `test/typecheck_m6.t` の qual1〜qual4b が、この段階を確かめる。
   qual4 と qual4b は、同じ handle を修飾して書いたものと修飾せずに書いたものの対である。
   2 つの診断が違うことから、修飾が対象の決定に使われていることが分かる。

   どの節も修飾されていなければ、2 段階目として、次の手順で候補を絞る。

   1. すべての操作名を宣言しているエフェクトを集める(`holds_all`)
   2. そのうち、自分の全操作がこの handle に書かれているものだけを残す(`covered`)
   3. ちょうど 1 つなら、それが対象である。0 個なら網羅漏れ、2 個以上なら曖昧としてエラーにする

   手順 1 は、書いた操作名のどれかを宣言していないエフェクトを外す。
   たとえば `Console` と `File` は、どちらも操作名 `write` を持つ。
   それでも `read` と `write` の両方を書けば、
   `read` を宣言しない `Console` は手順 1 の条件を満たさない。
   手順 2 は、書いた操作をすべて宣言したうえで、ほかの操作も持つエフェクトを外す。
   `File` のほかに `read` / `write` / `close` を持つエフェクトがあっても、
   `read` と `write` の節だけを書けば `File` に決まる。

   ランタイムが提供するエフェクト(プレリュードの `Console`)はハンドルできない。
   このエフェクトは、手順 1 の候補からも外す。
   `Console` を候補に残すと、`write` 節だけを書いた handle の対象は、
   手順 2 で、全操作が書かれている `Console` に決まる。
   候補から外すので、この handle は `Console` には決まらず、
   `File の read が漏れています` のエラーになる。
   `File` のつもりで `write` 節だけを書いた誤りは、この診断から分かる。
   `File` を意図していたなら、`File.write` と修飾するか、`read` 節も書けばよい。
   網羅漏れのエラーになるのは、どの候補にも、handle に書かれていない操作が残っているときである。
   2 つの操作を持つエフェクトの片方だけを書いた場合などが、これに該当する。

   修飾されたエフェクトが実在するかどうかは、対象を決める時点で調べる。
   調べないと、後の処理の `Option.get` が `None` を受け取り、
   型エラーとして報告すべきものが OCaml の例外としてそのまま外に出る。

   対象が決まったら、検査を 2 つ行う。
   すべての節が対象に属するかどうかと、対象の全操作が節にあるかどうかである。
   網羅を要求するのは、handle 式の行から対象エフェクトを取り除く型付けにしているからである(§11.24)。
   所属を先に調べるので、両方のエラーを含む入力では所属違反を報告する。
   所属違反は書かれた節を示し、網羅漏れは書かれていない操作を示す。
   書かれた節のエラーを先に示すほうが、どこを直せばよいかが分かりやすい。
   所属違反を直すと、網羅漏れが残っていればそれが次に報告される。
   この 2 つの検査がエラーを報告するのは、対象を修飾から決めたときだけである。
   修飾のない handle では、対象を決める段階で両方の条件を満たす候補だけを残すので、
   ここではエラーにならない。
   `test/typecheck_m6.t` の qual5 が、この順序を確かめる。 *)

  (* 対象エフェクトは、すべての節が属し、全操作が節に書かれているエフェクトである。
     そのようなエフェクトがちょうど 1 つでなければエラーにする *)
  let quals = List.filter_map (fun (_, q, _, _) -> q) ops in
  let op_names = List.map (fun (op, _, _, _) -> op) ops in
  (* ランタイムが提供するエフェクトは、ユーザのハンドラで処理できない。
     仕様は sample.kel:538 で、Console をそのエフェクトとして定めている。
     処理できると、出力を黙って捨てるハンドラが書ける。
     File.write のつもりで書いた case write(s) が、Console を処理してしまうことも起きる。
     ここで拒否するのは、Prims.runtime_effects に名前があり、
     かつプレリュードが宣言したエフェクトである。
     --no-prelude でユーザが自分の effect Console を宣言した場合は拒否しない。
     修飾された節では、この判定を `操作 X はエフェクト Y に属しません` の検査より先に行う。
     Heap と Blocking は Prims.runtime_effects にないので、ここでは拒否しない。
     入れると、case Blocking.nope() の診断がここのメッセージに変わってしまう(第7章 §7.3) *)
  let runtime_provided e = List.mem (name_of e) Prims.runtime_effects && Decls.prelude_owned "effect" e in
  let runtime_msg e =
    match name_of e with
    | "Console" ->
        "エフェクト Console はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:466, :538)。出力先を変えたいときは Print をハンドルしてください(プレリュードの with_stdout が Print を Console へ翻訳します)"
    | n -> "エフェクト " ^ n ^ " はランタイムが提供するため、ユーザはハンドルできません"
  in
  let target =
    match List.sort_uniq compare quals with
    | [ e ] ->
        (* 修飾されたエフェクトが実在するかどうかを調べる。
           調べないと、後の処理の Option.get が OCaml の例外を投げる *)
        if Decls.find_effect e = None then type_error ("未知のエフェクト: " ^ display_of e)
        else if runtime_provided e then type_error (runtime_msg e)
        else e
    | _ :: _ -> type_error "handle の節の修飾エフェクトが一致しません"
    | [] -> (
        let declares e op = List.mem_assoc op (Option.get (Decls.find_effect e)).Decls.ef_ops in
        let candidates = List.sort_uniq compare (List.concat_map Decls.op_candidates op_names) in
        (* ランタイムが提供するエフェクトを候補から外す。
           case write(s) だけを書いた handle は、対象が Console に決まらず、
           `File の read が漏れています` のエラーになるので、意図と違うことが診断から分かる。
           候補がすべてランタイムの提供するエフェクトだったときだけ、
           そのエフェクトはハンドルできないというエラーにする *)
        let all_effects = List.filter (fun e -> not (runtime_provided e)) candidates in
        (if all_effects = [] && candidates <> [] then type_error (runtime_msg (List.hd candidates)));
        let holds_all = List.filter (fun e -> List.for_all (declares e) op_names) all_effects in
        let covered =
          List.filter
            (fun e -> List.for_all (fun (op, _) -> List.mem op op_names) (Option.get (Decls.find_effect e)).Decls.ef_ops)
            holds_all
        in
        match covered with
        | [ e ] -> e
        | [] -> (
            match holds_all with
            | e :: _ ->
                let missing =
                  List.filter
                    (fun (op, _) -> not (List.mem op op_names))
                    (Option.get (Decls.find_effect e)).Decls.ef_ops
                in
                type_error
                  ("ハンドラが操作を網羅していません: " ^ display_of e ^ " の "
                  ^ String.concat ", " (List.map (fun (op, _) -> display_of op) missing)
                  ^ " が漏れています")
            | [] -> type_error ("この操作の組を宣言するエフェクトがありません: " ^ String.concat ", " (List.map display_of op_names)))
        | es ->
            type_error
              ("handle の対象エフェクトが曖昧です(" ^ String.concat ", " (List.map display_of es)
             ^ ")。" ^ display_of (List.hd es) ^ "." ^ display_of (List.hd op_names) ^ " のように修飾してください"))
  in
  let target_info = Option.get (Decls.find_effect target) in
  (* 対象が決まったら、すべての節が対象に属することと、対象の全操作が節にあることを調べる *)
  List.iter
    (fun (op, _, _, ((_, c) : T.clause)) ->
      if not (List.mem_assoc op target_info.Decls.ef_ops) then
        at_node c.T.cl_pat (fun () ->
            type_error ("操作 " ^ display_of op ^ " はエフェクト " ^ display_of target ^ " に属しません")))
    ops;
  List.iter
    (fun (op, _) ->
      if not (List.mem op op_names) then
        type_error ("ハンドラが操作を網羅していません: " ^ display_of target ^ " の " ^ display_of op ^ " が漏れています"))
    target_info.Decls.ef_ops;
  (* 操作節の引数のパターンを型付ける。
     引数のパターンが必ず一致するかどうかは引数の型を調べて判定するので、パターンだけを先にここで型付ける。
     本体、return 節、cancel 節、操作節のガードと本体は、この後で推論する(§11.24)。
     操作の型には型パラメータも行変数も書けないので、引数の型はこの時点で決まっている *)
  let op_clauses =
    List.map
      (fun ((op, _, args, ((_, c) as cnode)) as cl) ->
        let scheme = List.assoc op target_info.Decls.ef_ops in
        let args_row, op_ret =
          match repr (Unify.instantiate level scheme) with
          | TArrow (a, r, _) -> (a, r)
          | _ -> bug "操作スキーマが矢印型ではありません"
        in
        let full = intern (name_of target ^ "." ^ name_of op) in
        Tree.set_resolved cnode (if is_never op_ret then Tree.RNeverOp full else Tree.ROp full);
        let param_tys = match repr args_row with TRecord row -> List.map snd (fst (row_fields row)) | _ -> [] in
        (at_node c.T.cl_pat @@ fun () ->
         if List.length args <> List.length param_tys then
           type_error
             (Printf.sprintf "操作 %s は %d 引数です(節には %d 個書かれています)" (display_of op) (List.length param_tys)
                (List.length args));
         List.iter (fun (a : T.ctor_arg_pat) -> if a.T.cap_label <> None then type_error "操作節の引数にラベルは書けません") args);
        let seen = ref [] in
        let env2 =
          List.fold_left2
            (fun env (a : T.ctor_arg_pat) t -> elab_pat env level seen t a.T.cap_pat)
            env args param_tys
        in
        (* 引数のパターンが必ず一致する節なら真にする。
           条件は、ガードがなく、引数のパターンの並びを 1 行のパターン行列として
           第10章の missing に渡したときに、反例が返らないことである。
           引数の並びを照合対象とし、この節だけを持つ match が網羅的かどうかを調べるのと同じ判定である *)
        let total =
          c.T.cl_guard = None
          && Exhaust.missing [ List.map (fun (a : T.ctor_arg_pat) -> Exhaust.convert a.T.cap_pat) args ] param_tys = None
        in
        (cl, env2, op_ret, total))
      ops
  in
  (* 各操作に、引数のパターンが必ず一致する節が 1 つ以上あることを検査する。
     実行時の節の選択では、match と同じく、一致しなければ次の節へ進む(第14章)。
     しかし、どの節にも一致しなかった操作を外側のハンドラへ回す規則はないので、
     どの節にも一致しないことがある形はここで拒否する。
     実行時に操作を受け取る節がなくなるプログラムを、型検査で受理しないためである。
     絞り込みの節を複数合わせると網羅できる場合も、必ず一致する節がなければ拒否する(sample.kel:516) *)
  List.iter
    (fun (op, _) ->
      let mine = List.filter (fun ((o, _, _, _), _, _, _) -> o = op) op_clauses in
      if not (List.exists (fun (_, _, _, total) -> total) mine) then begin
        (* 網羅の検査に通っているので節は 1 つ以上あり、
           引数の個数の検査に通っているので、どの節の引数の個数も宣言と一致する *)
        let arity = match mine with ((_, _, args, _), _, _, _) :: _ -> List.length args | [] -> 0 in
        type_error
          ("操作 " ^ display_of op
         ^ " には、ガードがなく、どんな引数にも一致する節がありません(どの節にも一致しなかった操作を外側のハンドラへ回す規則はありません)。ガードの無い case "
         ^ display_of op ^ "(" ^ String.concat ", " (List.init arity (fun _ -> "_")) ^ ") を最後に置いてください")
      end)
    target_info.Decls.ef_ops;
  (* 到達不能な操作節を警告する。
     引数のパターンが必ず一致する節より後ろにある、同じ操作の節は実行されない。
     この検出は match の useful 判定(第10章)より弱い。
     ある節に一致する値を、それより前の複数の節がすべて受け取っていても、
     前に必ず一致する節がなければ警告しない(case ask(1) を 2 回書いた場合など)。
     健全性は上の検査が保証するので、弱いことで起きるのは、警告の出ない到達不能な節があることだけである *)
  let rec dead_scan seen_total = function
    | [] -> ()
    | ((o, _, _, _), _, _, total) :: rest ->
        if List.mem o seen_total then
          warn ("操作 " ^ display_of o ^ " の節は到達しません(前の節が既に取りこぼしません)");
        dead_scan (if total && not (List.mem o seen_total) then o :: seen_total else seen_total) rest
  in
  dead_scan [] op_clauses;
(* ## 11.24 本体と各節の型付け

   handle の型付けの規則は次のとおりである。

   ```
     Γ ⊢ e : α ! {E | ε}
     Γ, x : α ⊢ r : R ! ε                        -- return 節
     Γ, x : A_op, resume : B_op -> R ⊢ b : R ! ε  -- 再開する操作の節
     Γ, x : A_op ⊢ b : R ! ε                     -- 再開しない操作の節(resume はない)
     ---------------------------------------------
     Γ ⊢ e handle { ... } : R ! ε
   ```

   handle の本体だけは、外側の行 `eff` に対象エフェクトを追加した行で推論する。
   return 節、cancel 節、操作節は、すべて外側の `eff` で推論する。

   return 節と cancel 節は、自分のハンドラが外れた文脈で実行される(第14章 §14.9)。
   対象エフェクトを追加した行で型付けると、
   型検査が許した対象エフェクトの操作を、
   実行時にはこのハンドラが受け取らないという食い違いが生じる。

   操作節を外側の行で推論するのは、深いハンドラだからである。
   操作節の本体は、ハンドラの外側と同じ文脈で実行される。

   節ごとの規則は次のとおりである。

   - resume の型は「操作の返り値の型 → handle 式全体の型」である。
     これを `resume_ty` に入れて操作節の本体を推論する(§11.16)。
     return 節と cancel 節には継続がないので、`resume_ty` を `None` にし、
     `no_resume` にその節の種類を入れる。
   - cancel 節の値は捨てられるので、Unit と単一化する。
   - 操作節の引数にはラベルを書けず、位置引数だけを書ける。
     操作の引数は宣言の順序で意味が決まるので、並べ替えを許す理由がない。
   - return 節と cancel 節にはガードを書けない。
     節の構文(clause)は match と共通なのでパーサは受理するが、ここで拒否する。
     この 2 つは 1 つのハンドラに 1 節までなので(§11.22)、ガードが偽のときに進む先の節がない。
     第14章の `retc` / `run_cancel` はガードを読まないので、受理すると、
     型検査に通ったガードの式が実行時に黙って無視される。
     `case return(x) if c => a` と書きたいときは、節の本体で `c` を match すれば同じことを書ける。
   - 再開しない操作(返り値の型が `Never`。§11.15)の節では、`resume_ty` を `None`、
     `no_resume` を操作名にして本体を推論する(§11.16)。
     `check_resume_static` は呼ばない。
     クロージャの本体の `resume` も、`resume_ty` が `None` なら推論の時点でエラーになるからである。
   - 操作節のガードは受理するが、`resume` のない環境で推論し、
     `no_resume` には、ガードの中であることを表す `No_guard` を入れる。
     評価器(第14章)はガードを resume のない環境で評価するので、ここで resume を許すと、
     型検査に通るのに実行時エラーになるプログラムを受理してしまう。
     §11.21 の静的な検査は節の本体しか走査しないので、ガードの resume はここで防ぐ。
   - 各操作には、引数のパターンが必ず一致する節が 1 つ以上必要である(sample.kel:515-516)。
     この検査は、§11.23 で操作節の引数のパターンを型付けた直後に行う。
     引数のパターンが必ず一致する節とは、ガードがなく、
     その節だけを持つ match が引数の並びについて網羅的になる節である。
     判定には第10章の missing を使う。
     そのため、変数や `_` のほか、コンストラクタが 1 つしかない newtype の分解や、
     ラベルが 1 つの閉じたヴァリアントの分解も、引数のどの値にも一致すれば、この節に数える。
     実行時の節の選択では、一致しなければ次の節へ進む。
     しかし、どの節にも一致しなかった操作を外側のハンドラへ回す規則はないので、
     どの節にも一致しないことがある形はここで拒否する。
     必ず一致する節より後ろにある同じ操作の節には到達しないので、警告を出す。
     `--strict-exhaustive` を付けると、この警告はエラーになる。

   推論の順序は次のとおりである。
   操作節の引数のパターンは、上の検査が引数の型を調べるので、§11.23 で先に型付ける。
   その後で、本体、return 節、cancel 節、操作節のガードと本体の順に推論する。
   そのため、操作節の引数のパターンのエラーは、本体や各節の本体のエラーより先に報告される。

   `check_resume_static` は、再開する操作の節の本体を推論する直前に呼ぶ(§11.21)。 *)

  (* 本体は、対象エフェクトを追加した行で推論する *)
  let body_ty = elab_exp env level (TRowExtend (target, t_unit, eff)) body in
  let tres = new_var level in
  (* return 節と cancel 節は外側の eff で推論する。
     第14章の retc と exnc は、自分のハンドラが外れた文脈で実行されるからである *)
  (match rets with
  | [ (p, ((_, c) as cnode)) ] ->
      Tree.set_resolved cnode Tree.RReturnClause;
      Option.iter (fun g -> at_node g (fun () -> type_error "return 節にガードは書けません")) c.T.cl_guard;
      let seen = ref [] in
      let env2 = elab_pat { env with resume_ty = None; no_resume = Some No_return_clause } level seen body_ty p in
      Unify.unify (elab_exp env2 level eff c.T.cl_body) tres;
      (* return 節の反駁可能なパターンも、節の本体を推論した後で網羅性検査のキューに追加する。
         先に追加すると、節の本体の中の let がキューを処理するときに、
         この項目まで処理して行を早く閉じてしまう *)
      if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] body_ty
  | _ -> Unify.unify body_ty tres);
  (match cancels with
  | [ ((_, c) as cnode) ] ->
      Tree.set_resolved cnode Tree.RCancelClause;
      Option.iter (fun g -> at_node g (fun () -> type_error "cancel 節にガードは書けません")) c.T.cl_guard;
      let env2 = { env with resume_ty = None; no_resume = Some No_cancel_clause } in
      (* cancel 節の値は捨てられるので、Unit と単一化する *)
      Unify.unify (elab_exp env2 level eff c.T.cl_body) t_unit
  | _ -> ());
  (* 操作節のガードと本体を推論する。引数のパターンは §11.23 で型付けてある *)
  List.iter
    (fun ((op, _, _, ((_, c) : T.clause)), env2, op_ret, _) ->
      (* ガードは resume のない環境で推論する。
         評価器(第14章)はガードを resume = None で評価するので、ここで Some にすると、
         型検査に通るのに実行時エラーになるプログラムを受理してしまう。
         §11.21 の静的な検査は本体しか走査しないので、ガードの resume はここで防ぐ *)
      (match c.T.cl_guard with
      | Some g -> Unify.unify (elab_exp { env2 with resume_ty = None; no_resume = Some No_guard } level eff g) t_boolean
      | None -> ());
      (* 再開する操作の節では resume が使える。本体は外側の eff で推論する。
         再開しない操作の節では resume_ty を None にし、
         no_resume に操作名を入れて診断に使う *)
      let env2 =
        if is_never op_ret then { env2 with resume_ty = None; no_resume = Some (No_never_clause op) }
        else { env2 with resume_ty = Some (op_ret, tres); no_resume = None }
      in
      if not (is_never op_ret) then check_resume_static c.T.cl_body;
      Unify.unify (elab_exp env2 level eff c.T.cl_body) tres)
    op_clauses;
  tres

and method_scheme cls m =
  match Decls.find_class (intern cls) with
  | Some ci -> (
      match List.assoc_opt m ci.Decls.ci_methods with
      | Some t -> t
      | None -> bug ("組み込みクラス " ^ cls ^ " にメソッド " ^ m ^ " がありません"))
  | None -> bug ("組み込みクラス " ^ cls ^ " が未登録です")

(* ## 11.25 束縛の準備とスコーレム定数

   `let f[A](x: A): A = ...` の `[A]` を新しい単一化変数にすると、
   `fn x => x + 1` を `[A] (A) => A` と注釈しても型検査に通ってしまう。
   注釈は、少なくともこれだけ多相であることを要求するものなので、それでは注釈の意味がなくなる。

   そこで、型パラメータをスコーレム定数(`Rigid`)にして本体を検査する(スコーレム化)。
   スコーレム定数には型を代入できないので、`A` を Int32 に決めようとした時点で単一化がエラーになる。
   §11.17 の run の 3 つの手順と同じ仕組みで、
   `make_rigids` が 2 番目の手順(スコーレム定数を作る)を行う。

   カインドは、`F[_]` と書かれていればその場で決まる。
   `[A]` や `[E]` のように括弧がなければ、カインド変数にしておく。
   Keleut では、型パラメータが型なのか行なのかを表記では区別できず、
   使われた位置(`extends` の右か `@` の右か)でしか決まらないからである。
   未解決のまま残ったカインドは、
   スコーレム定数を解放するとき(§11.27 の `release_rigids`)に `KStar` に決める(既定化)。

   スコーレム定数は次の 3 つの段階を経る。

   1. `make_rigids` が、束縛のレベル + 1 で作る
   2. 本体を検査する間、代入されないことと外へ漏れないことを、単一化が検査する
   3. スコープを出たら、`release_rigids` が Generic に書き換える(§11.27)

   この 3 つの段階により、注釈つきの束縛の型は、本体の検査ではスコーレム定数を含む型として、
   環境の中では多相な型として働く。
   そのため、型スキーム専用のデータ型は必要ない。

   制約に書かれたクラス名は、スコーレム定数を作るこの時点で `class_names_of` が検証する。
   未知のクラスの検査を、束縛を使う位置の `add_class`(§8.4)まで遅らせると、
   `let f[A: Bogus](x: A): A = x` という宣言が型検査に通ってしまう。
   その宣言は `f : [A: Bogus] (A) => A` と表示され、
   呼んだ位置で初めて `未知のクラス` のエラーになる。
   これでは、どこが誤りなのかがユーザに分からない。 *)

(* 型パラメータに書かれたクラス名を oid にする。
   宣言済みのクラスでなければ、その場で型エラーにする(§11.25)。
   メッセージは add_class のものと同じにする *)
and class_names_of tp =
  List.map
    (fun li ->
      let c = Decls.resolve_class (intern (show_long_id li)) in
      if Decls.find_class c = None then type_error ("未知のクラス: " ^ show_long_id li);
      (* 予約述語は制約にも書けない。
         書けると、[A: Integral] の A が既定化の対象として扱われ、
         数値リテラルの型が決まらないまま実行に進む *)
      if Decls.reserved_predicate c then
        type_error (show_long_id li ^ " は予約されたリテラル述語です(制約には書けません、D8)");
      c)
    tp.tp_classes

and make_rigids ?kinds level tparams =
  (* kinds は、型エイリアスの表が持つカインドのセル(al_kinds)である。
     長さが tparams と合わないときは、エラーにせずに作り直す。
     kinds を作る箇所で長さを合わせているので、作り直すのは念のための処理である *)
  let kinds =
    match kinds with
    | Some ks when List.length ks = List.length tparams -> ks
    | _ -> List.map (fun (tp : type_param) -> if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var ()) tparams
  in
  List.map2
    (fun tp kind ->
      let classes = class_names_of tp in
      let r = new_rigid_ref ~kind ~classes level in
      (match !r with Rigid i -> Hashtbl.replace Unify.rigid_tparams i.vid tp.tp_name | _ -> ());
      (tp.tp_name, TVar r, r))
    tparams kinds

(* ## 11.26 使用時に行を開く規則

   関数型の行は、書いたとおりに読む(sample.kel §9、sample.kel:475)。
   閉じた行は、その関数が起こすことのあるエフェクトの全体を表し、
   行変数で終わる行は、その行変数の分だけほかのエフェクトを許す。
   2 つの行を一致させるのは単一化である。
   行にラベルを追加して暗黙に一致させる一般の規則は持たない。
   例外は、本節の使用時に行を開く規則だけである(LangSpec §13.2)。

   閉じた行をそのまま単一化すると、sample.kel:550 が型検査に通らない。

   ```
   println(test) handle {
     case print(message) => resume(perform write(message))
     case return(x) => x
   }
   ```

   `println : (String) => Unit @ Print` の本体は `perform print(...)` である。
   しかし、この handle の本体で `println` を呼ぶ位置の行は `{Print, Console}` で、
   `{Print}` とは一致しない。

   そこで、閉じた行を持つ関数を使うときは、その行の末尾を新しい行変数で開いてから、
   要求する側の行と単一化する(sample.kel:476、:480-483)。
   開いた行 `{Print extends ρ}` は `{Print, Console}` と単一化できるので、
   閉じた行のラベルが要求する側の行に含まれていれば型検査に通る。
   行変数で終わる行は開かず、書いたとおりに単一化する。
   開くのは次の 4 つの場面で、どれも `open_closed_arrow` を使う。

   | 場面 | 開く箇所 | 節 |
   |---|---|---|
   | 名前で参照するとき | `elab_exp` が `T.Ident` の型を木に書く直前 | §11.11 |
   | 呼び出すとき | `T.Apply` が呼び出し先の型を分解する直前 | §11.12 |
   | 関数型を要求する位置に置くとき | `subsume_closed`(期待型の先頭が矢印のときだけ開く) | §11.19、§11.28、§11.29 |
   | 演算子を型付けするとき | `T.BinOp` と `T.Neg` がメソッドの型スキームを具体化した直後 | §11.13 |

   関数型を要求する位置は、仮引数の型が関数型である実引数、
   返り値の注釈が関数型である関数束縛の本体、注釈が関数型である値束縛の初期化式である。
   `perform` の実引数と `resume` の引数も、操作の型の対応する部分が関数型なら、
   この位置に相当する(§11.15、§11.16)。
   検査モードは、実引数に直接書いた無名関数の本体と、
   実引数に直接書いたレコード式のフィールドやタプル式の要素にも期待型を渡す。
   そのため、そこに置いた式も、期待型が矢印なら開く(§11.19)。
   名前の参照は、どの位置に置いても参照の時点で開いている。
   そのため、表の「呼び出すとき」と「関数型を要求する位置に置くとき」の 2 つの場面で新たに行を開くのは、
   `mk()` のような呼び出しの結果や、`r.go` のようなフィールドの選択といった、
   名前の参照でない式である。
   そうした式を、コンストラクタの引数、レコードのフィールド、`match` の節の値のように、
   関数型を要求しない位置に置いたときは開かない(LangSpec §13.2 の制限の 1 つ目)。

   開いてよい理由は、閉じた行が本体の上限だからである。
   閉じた行を書いた束縛の本体は、その行の文脈で検査する(§11.28)。
   本体が注釈に書いていないエフェクトを起こせば、そこで単一化がエラーになる。
   したがって、本体が起こすエフェクトは閉じた行に含まれる。
   開いて追加する行の末尾は、その使用のために作る新しい行変数で、ほかのどの型変数とも共有されない。
   そのため、行の末尾を開いても型と実際の振る舞いは食い違わない。
   この理由は束縛を一般化するかどうかによらないので、一般化しない束縛の閉じた行も、
   使うたびに開いてよい。

   開くのは、使われる関数の型の最も外側の行だけである。
   要求する側の行は書いたとおりに残り、引数や返り値の中の矢印も変えない。
   そのため、`@ {}` のコールバックを受け取る高階関数には、エフェクトのある関数を渡せない。
   `@ Print` も、最も外側なら本体の上限として Print だけを許し(sample.kel:478-479)、
   入れ子の仮引数の型に書けば、そこに渡せる関数を、
   Print 以外のエフェクトを起こさない関数に限る(sample.kel:498-501)。

   行が決まっていない関数は開かない。
   注釈のない引数や、行がまだ行変数である一般化しない束縛を使うと、行変数のまま単一化し、
   その使用で決まった行がその後の使用にも適用される(LangSpec §13.2 の制限の 2 つ目)。
   開くかどうかは使用の時点の行の形で決まるので、
   型検査に通るかどうかが文や実引数の順序で変わることがある。

   開いて追加した行変数が、一般化しない束縛の型の最も外側の行の末尾として、
   束縛の終わりまで何とも単一化されずに残ることがある。
   残るのは次の 2 つの場合である。
   注釈の最も外側の `@` を省略した値束縛で、値でない初期化式が閉じた行の関数を返す場合と、
   パターンで束縛した閉じた行の関数を返す `match` を束縛する場合である。
   `reclose_opened_tail` はこの行変数を空の行と単一化して、閉じた行に戻す(§11.28)。
   戻さないと束縛の行が最初の使用で決まる弱い行変数になり、
   その束縛と、それを呼ぶ注釈のない関数を、行の違う 2 つの文脈で使えなくなる。

   ### `@` の省略の意味

   最も外側の矢印は、関数束縛ではその関数自身の矢印、値束縛では注釈の先頭に直接書いた矢印、
   型クラスのメソッドと `extern` では宣言した型の先頭の矢印である(sample.kel:486-488)。
   最も外側の矢印の行は、本体を検査する文脈の行になる。
   閉じた行を書いた束縛の本体が、その行にないエフェクトを起こすと、型検査に通らない。
   最も外側の `@` を省略したときの意味は、宣言の種類で決まる(sample.kel:490-496)。

   | 宣言 | `@` の省略の意味 | 実装 |
   |---|---|---|
   | `pub` のない `let` | 本体から推論する | 新しい行変数(§11.28) |
   | `pub let` | `@ {}` | 関数束縛は下で述べる専用のセル、値束縛の先頭の矢印は `TRowEmpty`(§11.28) |
   | 型クラスのメソッド | `@ {}`。各インスタンスの実装は純粋でなければならない | `TRowEmpty`(§11.33、§11.38) |
   | C リンケージの `extern` | `@ Blocking` | 閉じた行 `{Blocking}` |
   | prim リンケージの `extern` | 新しい行変数。使うたびに別の行へ具体化する | 新しい行変数を一般化する |

   入れ子の矢印(最も外側以外の矢印)では、`@` を省略すると `@ {}` と同じ意味になる(§11.4)。

   束縛の型は、注釈した型か推論した型そのものである。
   本体から推論した行が閉じた行に決まったときも、束縛の型はその閉じた行のままで、
   書いた閉じた行と同じく使うときに開く(sample.kel:491-493)。

   `pub` の束縛で省略した `@` は、`@ {}` と読む(sample.kel §13、sample.kel:494、:830-831)。
   関数束縛の本体の行は、空の行へのリンクを持つ専用のセル(`new_pub_pure_row`)で、
   意味は空の行と同じである。
   本体が起こしたエフェクトを報告する箇所は、行がこのセルかどうかをセルの同一性で調べ、
   このセルなら `pub` の規則を明記したメッセージにする(§11.12、§11.15)。
   値束縛の先頭の矢印は専用のセルを持たず、
   初期化式と注釈の単一化の失敗を同じメッセージに言い換える(§11.28)。
   閉じた空の行の関数は使うときに開くので、`Db.query` は `handle_request` から呼べる
   (sample.kel:654-657)。
   `pub` で `@` を省略した関数束縛の本体から、
   一般化されていないトップレベルの束縛(パターン束縛や、値でない式の束縛)を呼ぶと、
   その束縛の単相な行変数は空の行に決まる。 *)

(* ## 11.27 スコーレム定数の解放

   束縛のスコープを出るとき、`release_rigids` はこの束縛が作ったスコーレム定数を Generic に書き換える。
   これが注釈の一般化である。
   書き換えはその場で行う。
   木にはすでに `set_ty` で書いた型が入っていて、それとの共有を保つためである。

   この書き換えが安全であることは、書き換える側ではなく検査する側が保証する。
   スコーレム定数は束縛のレベル + 1 で作る(§11.25)。
   そのため、スコーレム定数が外へ漏れていれば、
   ここに来るまでに `unify` と `occurs_adjust` が検出している(第8章)。
   ここまで来たならスコーレム定数は漏れていないので、束縛を一般化するかどうかにかかわらず、
   無条件に Generic にしてよい。
   スコーレム定数を外側の単相の型変数と同じレベルで作ると、この前提が成り立たなくなる。
   その型変数がスコーレム定数を含む型に決まっても、`unify` と `occurs_adjust` は漏れを検出せず、
   スコーレム定数はここで Generic に変わる。
   その型変数を型に含む変数は、参照するたびに、その行が別の行へ具体化される。
   `run` の中の `Ref` なら、`Ref.set` で `Heap[h]` を追加した行と `Ref.get` で取り出した行が別になり、
   `Heap[h]` を読むクロージャが `run` の外へ出る。
   ただし `let rec` の再帰群では、ある束縛の検査を終えた時点で、
   同じ再帰群のほかの束縛をまだ検査していないことがある。
   そこで、ほかの束縛の型の中に現れたスコーレム定数の解放は、再帰群の終わりまで遅らせる(§11.29)。

   カインドの既定化もここで行う。
   `[E]` と書かれただけでどこにも使われなかった型パラメータは、カインドが `KVar` のまま残る。
   `release_rigids` は、それを `KStar` に決める。 *)

and release_rigids rigids =
  List.iter
    (fun (_, _, r) ->
      match !r with
      | Rigid i ->
          default_kind i.vkind (* 未解決のカインドは KStar に決める *);
          Type.set_tv r (Generic i)
      | _ -> ())
    rigids

(* ## 11.28 let 束縛

   ### 辞書パラメータと穴の解き方

   束縛の終わり(`finish_binding_dicts`)で、一般化する束縛の型の制約を正準順に並べたものを
   辞書パラメータとして `DAbs` に書き、本体で作った穴をその辞書パラメータで解く。
   一般化しない束縛の辞書パラメータは空である。
   本体の穴の型が束縛の型の `Generic` 変数なら、同じキーの辞書パラメータを渡す(`EvParam`)。
   具体型なら、インスタンスの証拠(`EvInst`)を作る。
   まだ決まっていない型変数なら、穴を未解決のまま残し、宣言の終わりか単位の終わりに解く。
   型パラメータに付けた制約が束縛の型に現れないときは、本体で使わなくても曖昧性エラーにする。
   渡す側がその辞書を作れないからである。

   束縛の処理は、次の順に行う。
   レベルを 1 つ上げ、型パラメータをスコーレム定数にし、注釈を精緻化し、本体を推論し、
   注釈と単一化し、一般化して、スコーレム定数を解放する。
   run と同じ 3 つの手順を、ここでは注釈のために使う。

   ### 一般化してよいのは、関数か構文上の値のとき

   ```
   let gen = is_fun || is_value b.T.lb_body
   ```

   本体の推論で生じた単一化変数を一般化するかどうかは、この 1 行で決まる。
   注釈が書いてあることは、一般化の条件に含めない。
   次の束縛は注釈を持つが、右辺の `Ref.new(...)` は関数の適用で値ではないので、一般化しない。

   ```
   let slot: Ref[h, T] = Ref.new(...)
   ```

   注釈は、単一化変数を多相にしてよいことの根拠にならない。
   根拠になるのは、値であることだけである。
   一般に、値でない式の束縛の型に残った単一化変数を一般化すると、可変参照を通じて不健全になる。

   値束縛の注釈の先頭の矢印に閉じた行を書いても、行を一般化する手順はない。
   `pub` で `@` を省略して空の行と読む場合も同じである。
   閉じた行は使うたびに開くので(§11.26)、一般化しなくても行の違う文脈から使える。
   初期化式の型の行が外側の単相の型変数と共有されていれば、
   その型変数は注釈の閉じた行に決まるだけである。

   値制限により、値でない式の束縛に型パラメータを書くことも拒否する。
   型パラメータを書くことは多相化の要求であり、値制限に反するからである。
   ただし、パーサが型パラメータを付けるのは関数束縛だけなので、この拒否に至るプログラムはない。
   値束縛に型パラメータを書けるように文法を拡張したときのための検査である。

   一方、関数の行が閉じていれば、使うたびにその行の末尾を開いてよい(§11.26)。
   型変数を多相にしてよい根拠は値であることだが、
   行の末尾を開いてよい根拠は行が閉じていることなので、
   こちらは束縛を一般化するかどうかによらない。

   ### 一般化しないときは、レベルを下げて単相に戻す

   本体は、一般化するかどうかにかかわらず、レベルを 1 つ上げて推論する(`lvl = level + 1`)。
   型パラメータのスコーレム定数も、このレベルで作る。
   一般化しない束縛でレベルを上げないと、型パラメータのスコーレム定数が束縛と同じレベルになる。
   同じレベルにある外側の単相の型変数が、そのスコーレム定数を含む型に決まっても、
   脱出検査は検出しない(§11.27)。

   一般化しない束縛の終わりには、`generalize` の代わりに `Unify.lower_levels` を呼ぶ。
   `lower_levels` は、型に残った深いレベルの単一化変数と、
   本体を推論する間に制約つき変数の一覧 `class_vars` に追加された深いレベルの単一化変数を、
   束縛のレベルまで下げる。
   一覧のうち対象にする範囲は、束縛の冒頭で `Unify.class_mark` が返した番号で区切る(第8章 §8.4)。
   下げずに環境へ置くと、後に続く一般化する束縛の `generalize` が、その変数を一般化してしまう。

   ### 注釈の精緻化は 1 回で済む

   注釈は 1 回だけ精緻化する。
   `release_rigids` がスコーレム定数をその場で Generic に書き換えるので(§11.27)、
   同じ型が、本体の検査ではスコーレム定数を含む型として、環境への登録では多相な型として、順に働く。
   木に `set_ty` で書いた型との共有も保たれる。

   関数束縛は、返り値の注釈があれば本体の型と単一化し、
   失敗を `注釈された返り値型を満たしません` に言い換える。
   値束縛は、注釈があれば初期化式の型と単一化し、失敗を `注釈された型を満たしません` に言い換える。
   どちらも、注釈が書かれているときだけ言い換える。
   注釈が関数型なら、本体や初期化式の型の閉じた行を `subsume_closed` で開いてから単一化する
   (関数型を要求する位置。§11.26)。
   `subsume_closed` は型の先頭だけを調べるので、注釈がレコード型なら、
   中のフィールドの矢印は開かない。
   単一化を try で囲み、エラーを注釈や宣言の側から述べ直すか、エラーに説明を添える箇所は、
   この 2 つのほかに次の 5 つがある。

   - 適用の単一化(§11.12)
   - perform の行の単一化(§11.15)
   - コンストラクタの引数の単一化(§11.18)
   - 検査モードに `row_note` を渡したときの行の単一化(§11.19)
   - インスタンス本体の包摂(§11.38)

   いずれも try で囲むのは `Unify.unify` と引数の個数の比較(`Unify.check_arity`)だけなので、
   `Type_error_at` を調べる必要はない。
   `let rec` の再帰群(§11.29)も、束縛の型の単一化を try で囲み、メッセージに事実を添える。
   こちらは束縛全体の検査も try で囲むので、`Type_error_at` も調べる。

   ### 値束縛の注釈は、先頭の矢印だけ扱いが違う

   値束縛の注釈は `elab_value_type_outer` で読む。
   先頭の矢印は束縛の最も外側の矢印なので、そこに書いた閉じた行は初期化式の関数の上限になる。
   省略した `@` は、`pub` でなければ新しい行変数(推論)、`pub` なら `@ {}` と読む(表は §11.26)。
   `pub` の束縛で省略した `@` の行を `TRowEmpty` に置き換えるかどうかは、
   `elab_value_type_outer` の結果ではなく、
   注釈の表層の構文 `snd t` が矢印リテラルかどうかで決める。
   先頭が型エイリアスなら、展開先の矢印は入れ子の矢印で、
   省略した `@` は初めから `@ {}` になっているからである。
   `pub` の言い換えの判定 `outer_eff_written` と、クラスメソッド側の判定(§11.33)も、
   同じ構文を調べる。
   注釈の行が閉じていれば、初期化式の型の行が一般化されない行変数のとき、
   その行変数は注釈の閉じた行に決まる(`test/verify_fixes.t` の vrleak4)。
   その後、同じ行変数を別の行で使うと型エラーになる(vrleak、vrleak2、vrleak3)。

   注釈と本体の単一化が失敗したとき、`pub` で先頭の矢印の `@` を省略した値束縛だけは、
   メッセージをさらに詳しく言い換える。
   注釈の先頭の矢印の行は空の行なので、
   先頭の矢印の行どうしの単一化が失敗する原因は、本体が純粋でないことである。
   そこで関数束縛(§11.12)と同じく、`pub` の規則を明記して元の報告を添える。
   `let rec` の値束縛(§11.29)でも、同じ形の束縛に同じ言い換えをする。
   先頭の矢印の行の失敗を区別するために、
   `unify_pub_value_annot` は先頭の矢印の行を、ほかの部分と分けて最後に単一化する。
   引数や返り値のレコードのフィールド、ヴァリアントのケース、入れ子の矢印の行の失敗は、
   `pub` でない束縛と同じメッセージで報告する。
   これらの失敗も `ラベル … がありません` というメッセージになるので、
   `row_failure` では先頭の矢印の行の失敗と区別できない。

   ここでいう本体は、注釈の先頭の矢印が表す関数の本体である。
   値束縛の初期化式そのものは `eff`(束縛の外側の行)で推論するので、
   そこに書いたエフェクトはこの検査の対象にならない。
   `pub let g: () => Int32 = { echo(s); fn() => 1 }` は型検査に通り、
   宣言を読み込むときに 1 度 Console を起こす。
   同じことを関数束縛で書いた `pub let g(): Int32 = { echo(s); 1 }` は型エラーになる。
   こちらの `{ … }` は、先頭の矢印の本体そのものだからである。
   両者の違いは、呼び出しのたびにエフェクトを起こすか、初期化時に 1 度だけ起こすかである。
   `pub` が保証する純粋さは、呼び出しのたびに起こすエフェクトについてだけである。

   ### 網羅性検査のキューを処理する時点

   網羅性検査の遅延キューを `drain` で処理するのは、`generalize` の直前である(§11.14)。
   `drain` には、束縛のレベル、束縛の型、束縛を一般化するかどうかを渡す。
   `drain` は、節のない `match` の照合対象の型変数を `Never` に決めるか、
   外側の束縛まで遅らせるかを、
   これらの値で判定する(第10章 §10.13)。
   インスタンスのメソッドの仮引数には宣言の引数の型を渡すので(§11.38)、
   照合対象がそうした仮引数なら、`drain` の時点でその型が決まっている。
   パターン束縛(`let (a, b) = ...`)は、節が 1 つだけの match と同じように扱う。
   単相に束縛し、網羅性検査のキューに追加する。
   この経路には一般化がないので、キューに追加した直後に `drain` を呼び、
   一般化しない束縛として渡す。 *)

and elab_binding ?expected_params env level eff ((_, b) as node : T.let_binding) : env =
  at_node node @@ fun () ->
  (* pub の束縛に完全な型注釈があることを検査する。
     注釈がなければ、省略した @ を純粋と読む規則も適用できない。
     この検査は、本体を調べる前に、冒頭で行う *)
  (if b.T.lb_pub then
    check_pub_annots ~tparams:(pub_tparams env b.T.lb_tparams) ~params:b.T.lb_params ~ret:b.T.lb_ret);
  let is_fun = b.T.lb_params <> None in
  (* 値制限により、本体の単一化変数を一般化してよいのは、関数束縛か、初期化式が値のときだけである(§11.28) *)
  let gen = is_fun || is_value b.T.lb_body in
  if (not gen) && b.T.lb_tparams <> [] then
    type_error "非値の束縛に型パラメータは付けられません(値制限。関数にするか値を束縛してください)";
  let lvl = level + 1 in
  let mark = Unify.class_mark () in
  let hmark = Unify.hole_mark () in
  let rigids = make_rigids lvl b.T.lb_tparams in
  let env_ty = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types rigids } in
  let fn_ty =
    match b.T.lb_params with
    | Some params ->
        let seen = ref [] in
        let param_tys = method_param_tys lvl expected_params params in
        let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
        let fn_eff =
          match b.T.lb_eff with
          | Some e -> elab_eff env_ty lvl e
          | None when b.T.lb_pub -> new_pub_pure_row ()
          | None -> new_row_var lvl
        in
        let ret_ty = match b.T.lb_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> new_var lvl in
        let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
        (* 言い換えるのは、注釈が書かれているときだけである(値束縛の側と同じ条件)。
           lb_ret = None でこの単一化が失敗する経路は現在はない。
           あれば、注釈を書いていないユーザに、注釈についてのメッセージを出すことになる *)
        (try Unify.unify ret_ty (subsume_closed lvl body_ty ret_ty)
         with Type_error msg when b.T.lb_ret <> None -> type_error ("注釈された返り値型を満たしません(" ^ msg ^ ")"));
        List.iter2 (fun p t -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) params param_tys;
        TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
    | None ->
        (* 値束縛の注釈の先頭の矢印は、束縛の最も外側の矢印である。
           注釈は elab_value_type_outer で読み、
           値の型の位置に書いた型のカインドが Type であることを先に検査する。
           pub で省略した @ は @ {} と読み、書いた閉じた行はそのまま束縛の型になる(§11.26) *)
        let vty =
          match b.T.lb_ret with
          | None -> new_var lvl
          | Some t -> (
              let ty = elab_value_type_outer env_ty lvl "型注釈" t in
              match (snd t, repr ty) with
              | T.EArrow (_, _, Some _), TArrow _ -> ty
              | T.EArrow (_, _, None), TArrow (a, r, _) when b.T.lb_pub -> TArrow (a, r, TRowEmpty)
              | _ -> ty)
        in
        (* 値束縛の初期化式は外側の eff で推論する。
           インスタンスのメソッドを注釈のない値束縛で書き、
           その初期化式が注釈のない仮引数だけを持つ無名関数なら、
           宣言の引数の型を検査モードで渡す(§11.38) *)
        let body_ty =
          match (expected_params, b.T.lb_ret, snd b.T.lb_body) with
          | Some ets, None, T.Lambda { l_params; _ }
            when List.length ets = List.length l_params
                 && List.for_all (fun (p : T.pat) -> match snd p with T.PVar _ | T.PWildcard -> true | _ -> false) l_params ->
              let t = TArrow (TRecord (closed_item_row ets), new_var lvl, new_row_var lvl) in
              elab_check env_ty lvl eff b.T.lb_body t;
              t
          | _ -> elab_exp env_ty lvl eff b.T.lb_body
        in
        let body_ty = subsume_closed lvl body_ty vty in
        (* pub で @ を省略した値束縛では、先頭の矢印の行の単一化が失敗する原因は、
           初期化式が返す関数が純粋でないことである。
           関数束縛(§11.12)と同じ言い換えを、先頭の矢印の行の失敗にだけ行う *)
        if b.T.lb_pub && not (outer_eff_written b) then
          unify_pub_value_annot vty body_ty ~other:(fun msg -> type_error ("注釈された型を満たしません(" ^ msg ^ ")"))
        else (
          try Unify.unify vty body_ty
          with Type_error msg when b.T.lb_ret <> None -> type_error ("注釈された型を満たしません(" ^ msg ^ ")"));
        vty
  in
  Tree.set_ty node fn_ty;
  (* 網羅性検査の遅延キューは、generalize の直前に drain で処理する *)
  match snd b.T.lb_name with
  | T.PVar x ->
      List.iter warn (Exhaust.drain ~level:level ~tys:[ fn_ty ] ~gen ());
      if gen then (
        (* 一般化の直前に曖昧性を調べる。
           generalize より前でなければならない。
           後では Unbound が Generic に変わっていて判定できない *)
        Unify.check_ambiguity ~all:false ~level [ fn_ty ];
        Unify.generalize level fn_ty)
      else (
        reclose_opened_tail lvl fn_ty;
        Unify.lower_levels ~since:mark level fn_ty);
      release_rigids rigids;
      finish_binding_dicts node ~gen ~rigids hmark fn_ty;
      add_local env x fn_ty
  | T.PWildcard ->
      List.iter warn (Exhaust.drain ~level:level ~tys:[ fn_ty ] ~gen ());
      if gen then (
        Unify.check_ambiguity ~all:false ~level [ fn_ty ];
        Unify.generalize level fn_ty)
      else (
        reclose_opened_tail lvl fn_ty;
        Unify.lower_levels ~since:mark level fn_ty);
      release_rigids rigids;
      finish_binding_dicts node ~gen ~rigids hmark fn_ty;
      env
  | _ ->
      (* パターン束縛は単相に束縛する(節が 1 つだけの match と同じ扱い)。
         網羅性の警告の対象にする。
         スコーレム定数の解放は elab_pat の後に行う。
         elab_pat は fn_ty を単一化に使うので、先に Generic へ書き換えると、
         単一化が Generic を見つけて内部エラーになる。
         注釈の先頭の矢印に閉じた行を書いたパターン束縛 let (5) が内部エラーにならないことは、
         test/verify_fixes.t の patrigid が検査する *)
      if not gen then (
        reclose_opened_tail lvl fn_ty;
        Unify.lower_levels ~since:mark level fn_ty);
      let seen = ref [] in
      let env' = elab_pat env level seen fn_ty b.T.lb_name in
      Exhaust.queue [ (b.T.lb_name, false) ] fn_ty;
      List.iter warn (Exhaust.drain ~level:level ~tys:[ fn_ty ] ~gen:false ());
      release_rigids rigids;
      finish_binding_dicts node ~gen:false ~rigids hmark fn_ty;
      env'

(* インスタンスのメソッドの仮引数の型を決める。
   宣言の引数の型が渡されていて、個数が合えば、
   注釈のない変数とワイルドカードの仮引数にはその型を使う。
   それ以外の仮引数には新しい型変数を使う *)
and method_param_tys lvl expected params =
  let fresh = List.map (fun _ -> new_var lvl) params in
  match expected with
  | Some ets when List.length ets = List.length params ->
      List.map2 (fun (p : T.pat) (e, f) -> match snd p with T.PVar _ | T.PWildcard -> e | _ -> f) params (List.combine ets fresh)
  | _ -> fresh

(* 束縛の終わりに、辞書パラメータを決めて束縛ノードに書き、本体で作った穴を解く(§11.28)。
   generalize と release_rigids の後に呼ぶので、この束縛のスコーレム定数は Generic に変わっており、
   予約述語の付いた変数は既定化されている。
   一般化しない束縛の辞書パラメータは空である *)
and finish_binding_dicts node ~gen ~rigids hmark fn_ty =
  let dps = if gen then Unify.dkeys_of fn_ty else [] in
  if gen then check_tparam_constraints ~rigids dps;
  if dps <> [] then Tree.set_dict node (Tree.DAbs dps);
  solve_holes_at ~since:hmark ~params:dps

(* ## 11.29 let rec

   ### 再帰群の中の参照と辞書

   再帰群の束縛は `pre` を通して互いを参照する。
   参照の時点で、`pre` の中の `Generic` 変数(本体を検査し終えて解放した型パラメータ)に付いた制約は穴になる。
   一方、まだ検査していない束縛の `pre` の型変数と、
   再帰群の終わりまでスコーレム定数のまま残る型パラメータ(`shared`)は穴にならない。
   そこで、`pre` を通る参照をすべて記録し(`record_group_ref`)、
   再帰群の終わりに `finish_group_dicts` が、
   参照先の辞書パラメータの正準順で証拠を作り直す。
   参照の時点で作った穴があればそれを使い、なければ同じキーの `EvParam` を渡す。
   再帰群の終わりに一般化した型変数は、参照先と参照元で同じ変数なので、同じキーで渡せる。
   `EvParam` のキーが参照元の束縛の辞書パラメータになければ、曖昧性エラーにする。
   束縛の本体で作った穴は、穴の一覧のうちその束縛の範囲(`member_marks`)にあるものを、
   その束縛の辞書パラメータで解く。
   再帰群のほかの束縛の型にだけ現れる型変数の穴は、その束縛の辞書パラメータでは解けないので、
   これも曖昧性エラーにする。

   型検査の手順は 4 つある。
   名前を単相の型 `pre` で先に束縛し、本体を推論し、`pre` と単一化し、最後に一般化する。
   `pre` は、注釈で決まる部分を先に置いた型か、新しい型変数である(下の「シグネチャを先に置く」)。
   この順序なので、再帰呼び出しは単相で、多相再帰はできない。
   多相再帰には型注釈が必要であり、そこまで扱うと推論が決定不能に近づく。

   右辺は関数でなければならない。
   これは型の都合ではなく、評価器の都合である。
   関数でない右辺(`let rec x = x + 1`)を許すと、型検査に通ったプログラムが実行時に必ずエラーになる。
   Diktor は、そうしたプログラムを型検査の段階で拒否する。

   束縛の名前をパターンにできないのも、同じ理由による。
   相互再帰の前方参照には名前が必要である。

   一般化は、すべての右辺を推論し終えてから、再帰群の全体について一度に行う。
   一方の束縛だけを先に一般化すると、
   相互再帰のもう一方の束縛が参照している型変数がすでに一般化されていて、単一化に失敗する。

   値束縛の注釈の先頭の矢印の読み方は、`let` と同じである(§11.28)。
   `pub let rec` の値束縛で先頭の矢印の `@` を省略すれば、`@ {}` と読む。
   初期化式の関数がエフェクトを起こして単一化に失敗したときは、
   `let` の値束縛と同じメッセージに言い換える。

   ### シグネチャを先に置く

   再帰群の中の参照は、名前を先に束縛した単相の `pre` を通る。
   前にある束縛の本体が後ろの束縛を参照する時点では、後ろの束縛の本体はまだ検査していない。
   `pre` が新しい型変数のままだと、呼び出し先の行はまだ決まっていない。
   使用時に行を開く規則は、行が決まっていない関数には適用されない(§11.26)。
   そのため、呼び出し元の本体の行と呼び出し先の行がそのまま単一化され、行の違う束縛を呼べなくなる。

   そこで、注釈で決まる部分を、再帰群のどの本体よりも前に `pre` に置く。
   置くものは次の 3 つである。

   - 最も外側の `@` を書いた関数束縛の矢印。引数と返り値は新しい型変数で、行は注釈の行である。
   - `pub` で `@` を省略した関数束縛の矢印。行は専用のセル(`new_pub_pure_row`、§11.26)である。
   - 型注釈を書いた値束縛の注釈の型。`pub` で先頭の矢印の `@` を省略していれば、
     その行を `TRowEmpty` にする。

   先に置いた行と型は、ループの中で本体を検査するときにそのまま使い、
   注釈を 2 回精緻化することはない。
   関数束縛の本体は、先に置いた行をその位置で有効なエフェクト行として検査する。
   値束縛の初期化式は、先に置いた注釈の型と単一化する。
   先に置いた閉じた行は、参照の時点で開く(§11.11)。
   そのため、行のラベルが呼び出し元の行に含まれていれば、前の束縛から後ろの束縛を呼べる
   (`test/annot_rows.t` の recandfwddiff)。
   後ろの束縛の本体が前の束縛を参照するときも同じ `pre` を通る。
   検査を終えた束縛の型は本体の型そのものなので、`pre` を別の型に置き換える必要はない。

   引数と返り値の注釈は先に置かない。
   呼び出しの時点で行を開くには、行だけが分かれば足りる。
   注釈を先に読むと、注釈のエラーを報告する順序が変わる範囲が広がる。

   型パラメータのスコーレム定数も、再帰群のどの本体よりも前に、束縛ごとに `make_rigids` で作る。
   先に置く注釈が型パラメータを含むことがあるからである。

   シグネチャを先に置いても、再帰群の中の参照は単相のままである。
   前の束縛が自分の型パラメータの型の値を、後ろの束縛の型パラメータの位置に渡すと、
   2 つの束縛のスコーレム定数が一致せず、`スコープ付きの型が一致しません` の型エラーになる。
   後ろの束縛の行変数のスコーレム定数も同じである。
   前の束縛の検査がその行変数を何かの行(前の束縛の注釈で決まった行や、
   ラベルを含む行)に決めようとすると、
   スコーレム定数と一致せず、型エラーになる。
   メッセージは、一致しない相手がスコーレム定数なら `スコープ付きの型が一致しません` を含み、
   相手が閉じた行やラベルなら `注釈で固定された行変数なので` を含む
   (`test/annot_rows.t` の recrowfwd、recrowclosed、recrowargeff)。
   行変数を引数の型にだけ書いた束縛にエフェクトを起こさない関数式を渡す場合のように、
   行変数を決めない呼び出しは型検査に通る(recrowargpure、recrowlam)。
   これは多相再帰を認めないことの帰結である。
   同じ 2 つの束縛を逆の順に書けば型検査に通る。
   前の束縛のスコーレム定数は、ほかの束縛の `pre` に現れていなければ、
   本体の検査の後に `Generic` に変わる。
   そのため、後ろの本体はそれを参照するたびに具体化できる(下の小節の recandpoly と同じ仕組み)。

   ### 型パラメータの衝突の報告

   `スコープ付きの型が一致しません` のメッセージは、表示用の名前 `ς1` と `ς2` しか含まず、
   どの束縛のどの型パラメータが衝突したかをユーザがたどれない。
   そこで、スコーレム定数の衝突で型エラーになったときに、
   第8章の `last_rigid_clash` に保存された 2 つの型を調べて、
   原因に近い事実をメッセージに添える(`group_note`)。
   添えるのは、衝突した一方が、検査している束縛自身の型パラメータのスコーレム定数のときに限る。
   もう一方が再帰群のほかの束縛の型パラメータで、
   そのスコーレム定数が検査している束縛の `pre` に現れていれば、
   その束縛と型パラメータの名前を挙げる(`test/rec_tparam_note.t` の twotp)。
   もう一方がそれ以外の型で、エラーになったのが `pre` と本体の型の単一化のときは、
   本体を検査する前に記録した `pre` の形(`pre_shape`)と、本体の型とを並べてたどる。
   たどりながら、本体の型の側にある、検査している束縛自身の型パラメータのスコーレム定数を集める。
   記録した形で単一化変数のままだった位置では、
   同じ単一化変数が記録した形のほかの位置にも現れていれば、その位置を決まっていたものとみなし、
   本体の型の側の部分木にあるスコーレム定数をすべて集める。
   記録した形で同じ単一化変数が 2 か所に現れるのは、
   たとえば前の束縛の参照がその 2 つの位置をつないだ場合である(alias3)。
   位置をつなぐことも、位置を決めることの一種とみなす。
   ほかの位置に現れない単一化変数の位置からは、何も集めない。
   記録した形で型が決まっていた位置では、本体の型の側のその位置にあるスコーレム定数を集める。
   行(レコードとヴァリアントの内容)は、フィールドを並びの位置ではなくラベルで対応づけてたどる。
   レコード式のラベルの順序は型に影響しないので(§7)、
   位置で対応づけると、別のラベルのフィールドどうしを比べてしまうからである。
   本体の型の側にしかないラベルのフィールドは、決まっていたものとみなし、
   その中のスコーレム定数をすべて集める。
   どちらかの側にしかないラベルのフィールドがあるときは、本体の型の側の行の残りも同じように扱う。
   両側のラベルがすべて対応するときは、行の残りどうしを並べてたどる。
   記録した形と本体の型とで型の種類が違う位置も、同じく決まっていたものとみなし、
   本体の型の側の部分木にあるスコーレム定数をすべて集める。
   記録した形の `Option[Int32]` と本体の型の `F[Int32]`(型パラメータ F の適用)を比べる位置が、
   その例である。
   このように判断がつかない位置では、メッセージに事実を添えるほうを選ぶ。
   このたどり方は、記録した形で決まっていた位置、記録した形の 2 か所以上に現れる単一化変数の位置、
   行のフィールドのラベルの対応、および型の種類の違いを調べる近似である。
   調べない形では、原因でない前の束縛を挙げることも、原因である前の束縛を挙げ損ねることもある。
   集めたスコーレム定数の中に衝突したスコーレム定数があれば、
   前にある束縛のうち、検査している束縛を参照したものの名前を挙げる(concrete)。
   このときは、メッセージの末尾に、具体的な型を渡す形を説明する §18.2 も挙げる。
   挙げる名前は再帰群の中の参照の記録から取り、その位置を決めた参照だけに絞ることはしない。
   selfrec は、前の束縛が g を名前で参照するだけの形である。
   その参照は g の `pre` のどの単一化変数も決めないので、`pre` の形を記録せず、前の束縛を挙げない。
   selfret は、前の束縛が g の返り値の位置を `Int32` に決め、
   型パラメータ B の位置(引数)を単一化変数のまま残す形である。
   B の位置の単一化変数は記録した形のほかの位置に現れないので、前の束縛を挙げない。
   alias3 は、前の束縛の本体の `fn(x) => g(x, x)` が、
   g の型パラメータ B と C の位置を同じ単一化変数につなぐ形で、つないだ位置として f を挙げる。
   recfield は、前の束縛が、ラベルを g の注釈と違う順序で書いたレコード式を渡し、
   g の型パラメータ B のフィールドを `Int32` に決める形で、f を挙げる。
   recfieldself は、前の束縛が同じようにラベルの順序の違うレコード式を渡すが、
   B のフィールドを単一化変数のまま残す形である。
   B のフィールドを `Int32` に決めるのは g 自身の本体の呼び出しなので、f を挙げない。
   rechkt は、前の束縛が高カインドの型パラメータ F の位置に `Option` を渡す形で、
   型の種類が違う位置として f を挙げる。
   衝突したスコーレム定数のどれも検査している束縛自身の型パラメータでなければ、何も添えない。
   notp では、f の型パラメータ A が f から g への参照を通って g の `pre` に現れ、
   g の `pre` と本体の型の単一化で `Int32` と衝突する。
   g は型パラメータを持たないので、このメッセージには何も添えない。
   本体の中で起きた衝突のうち、ほかの束縛の型パラメータと関わらないもの(別の `run` のヒープなど)にも添えない。
   再帰群の参照と関わらないエラーに、再帰群の順序についての説明を添えないためである(region)。

   ### スコーレム定数の解放は、ほかの束縛の `pre` に現れたものだけ再帰群の終わりに行う

   束縛が作った型パラメータのスコーレム定数のうち、
   再帰群のほかの束縛の `pre`(名前を先に束縛した単相の型)に現れたものだけを、
   再帰群の終わりに解放する。
   現れていないものは、単独の `let` と同じく束縛ごとに解放する(§11.27)。
   現れたかどうかは `mentions` で判定する。
   `mentions` は、ほかの束縛の `pre` の型をたどって、同じ `ref` が現れるかどうかを調べる。
   束縛自身の `pre` は調べない(`other != pre`)。
   先に置いた注釈が束縛自身のスコーレム定数を含んでいても、
   それだけでは解放を再帰群の終わりまで遅らせない。

   このように分けるのは、どちらか一方にそろえると正しく扱えない形があるからである。

   すべてを束縛ごとに解放すると、ほかの束縛が `pre` を通して参照している型の中で、
   スコーレム定数が `Generic` に変わる。
   その後でほかの束縛を単一化すると、その `Generic` 変数が現れ、
   第8章の `unify` が `[BUG] 単一化中に Generic 変数が現れました` で異常終了する。
   次の再帰群が、この形に該当する。

   ```
   let rec f[A](x: A): A = g(x)
   and g(y) = y
   ```

   `Panic` は、ユーザのプログラムがどう書かれていても起きてはならない(§1.18 の表)。
   しかもこの形は受理すべきプログラムなので、型エラーに変えるだけでは足りない。

   逆に、すべてを再帰群の終わりに解放すると、
   注釈を書いた前の束縛を後ろの束縛が多相に使う形が、型エラーになる。

   ```
   let rec f[A](x: A): A = x
   and g(n: Int32): Int32 = f(n)
   ```

   `f` の `A` は `g` の `pre` に現れない。
   解放を遅らせると、`g` の本体が `f` を呼ぶ時点で `A` がまだ `Rigid` なので、`Int32` と一致せず、
   `スコープ付きの型が一致しません` の型エラーになる。
   現れたかどうかで分ければ、この 2 つの形をどちらも受理できる。
   `test/annot_rows.t` の recandtp が前者を、recandpoly / recandeff が後者を確かめる。 *)

and elab_rec_bindings ?(top = false) ?(expected_params = fun _ -> None) env level eff bs : env =
  (* 名前を単相の型 pre で先に束縛し、本体を推論し、pre と単一化し、最後に一般化する。
     この順序なので、多相再帰はできない *)
  let lvl = level + 1 in
  (* 型パラメータのスコーレム定数は、シグネチャを先に置くために、再帰群のどの本体よりも前に作る(§11.29) *)
  let tps = List.map (fun ((_, b) as bnode : T.let_binding) -> at_node bnode (fun () -> make_rigids lvl b.T.lb_tparams)) bs in
  let types_with env rigids = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types rigids in
  (* 束縛の名前と、先に置く型 pre を作る。
     注釈で決まる部分(関数束縛の最も外側の行、値束縛の注釈)は本体の前に pre に置き、
     前にある束縛の本体が呼び出すときに使えるようにする。
     sig_eff は関数束縛の本体を検査する行で、pre の行と同じものを使う *)
  let names, sigs =
    List.split
      (List.map2
         (fun ((_, b) as bnode : T.let_binding) rigids ->
           (* 右辺と束縛名の検査のエラーは、束縛ではなく let rec の文の位置で報告する *)
           (match (b.T.lb_params, snd b.T.lb_body) with
           | None, T.Lambda _ | Some _, _ -> ()
           | None, _ -> type_error "let rec の右辺は関数でなければなりません");
           match snd b.T.lb_name with
           | T.PVar x -> at_node bnode @@ fun () -> (
               let env_ty = { env with types = types_with env rigids } in
               let arrow params e = TArrow (TRecord (closed_item_row (List.map (fun _ -> new_var lvl) params)), new_var lvl, e) in
               match (b.T.lb_params, b.T.lb_eff, b.T.lb_ret) with
               | Some params, Some e, _ ->
                   let e = elab_eff env_ty lvl e in
                   ((x, arrow params e), (Some e, None))
               | Some params, None, _ when b.T.lb_pub ->
                   let e = new_pub_pure_row () in
                   ((x, arrow params e), (Some e, None))
               | None, _, Some t ->
                   let ty = elab_value_type_outer env_ty lvl "型注釈" t in
                   let ty =
                     match (snd t, repr ty) with
                     | T.EArrow (_, _, None), TArrow (a, r, _) when b.T.lb_pub -> TArrow (a, r, TRowEmpty)
                     | _ -> ty
                   in
                   ((x, ty), (None, Some ty))
               | _ -> ((x, new_var lvl), (None, None)))
           | _ -> type_error "let rec の束縛はパターンにできません")
         bs tps)
  in
  (* トップレベルの let rec の自己参照と相互参照は、トップレベルの宣言(Tree.GDecl)を指す *)
  let bind_names env names =
    List.fold_left2
      (fun env bn (x, t) -> if top then add_top env x t (Tree.GDecl (Tree.oid_of bn, x)) else add_local env x t)
      env bs names
  in
  let env_rec = bind_names env names in
  (* 型パラメータのスコーレム定数のうち、再帰群のほかの束縛の pre に現れたものは再帰群の終わりに、
     それ以外は束縛ごとに解放する(§11.29) *)
  let group_rigids = ref [] in
  let rec mentions r t =
    match repr t with
    | TVar v -> v == r
    | TCon (_, args) -> List.exists (mentions r) args
    | TApp (f, a) -> mentions r f || mentions r a
    | TArrow (a, ret, e) -> mentions r a || mentions r ret || mentions r e
    | TRecord row | TVariant row -> mentions r row
    | TRowEmpty -> false
    | TRowExtend (_, f, rest) -> mentions r f || mentions r rest
  in
  let rec_arg_queue = ref [] in
  (* 再帰群の pre を通る参照を記録する。
     再帰群の検査を終えるときは、型エラーで終えるときも、この記録を group_stack から外す *)
  let g = { g_pres = List.map2 (fun (_, pre) bn -> (pre, bn)) names bs; g_cur = ref None; g_refs = [] } in
  group_stack := g :: !group_stack;
  let member_marks = ref [] in
  (* スコーレム定数の衝突のメッセージに、再帰群の中の参照が単相であることから生じた事実を添える(§11.29)。
     at_pre は、pre と本体の型の単一化でエラーになったときに真である *)
  let members = List.combine bs (List.combine names tps) in
  (* pre の中の単一化変数を、再帰群の検査の最初に集める。
     各束縛の本体を検査する前に、そのどれかがすでに決まっているか、
     つまり前にある束縛の参照が決めたかを調べる *)
  let rec unbound_vars acc t =
    match repr t with
    | TVar ({ contents = Unbound _ } as r) -> if List.memq r acc then acc else r :: acc
    | TVar _ | TRowEmpty -> acc
    | TCon (_, args) -> List.fold_left unbound_vars acc args
    | TApp (f, a) -> unbound_vars (unbound_vars acc f) a
    | TArrow (a, ret, _) -> unbound_vars (unbound_vars acc a) ret
    | TRecord row | TVariant row -> unbound_vars acc row
    | TRowExtend (_, f, rest) -> unbound_vars (unbound_vars acc f) rest
  in
  let pre_vars = List.map (fun (_, pre) -> (pre, unbound_vars [] pre)) names in
  let settled_before = ref [] in
  let settled pre =
    List.exists
      (fun r -> match repr (TVar r) with TVar { contents = Unbound _ } -> false | _ -> true)
      (List.assq pre pre_vars)
  in
  (* 本体を検査する前の pre の形を記録し、本体を検査した後で本体の型 fn_ty と並べてたどる。
     記録した形で型が決まっていた位置のうち、
     fn_ty の側が束縛自身の型パラメータのスコーレム定数であるものを集める。
     記録した形の 2 か所以上に現れる単一化変数(joined)の位置も決まっていたものとみなし、
     fn_ty の側の部分木にあるスコーレム定数をすべて集める。
     行のフィールドはラベルで対応づける。
     fn_ty の側にしかないラベルのフィールドと、型の種類が両側で違う位置では、
     fn_ty の側の部分木にあるスコーレム定数をすべて集める。
     どちらかの側にしかないラベルがあれば、fn_ty の側の行の残りも同じように集める。
     形を記録するのは、本体の検査が pre の単一化変数を決めると、
     どれが前から決まっていたかを型から区別できなくなるからである *)
  let kids t =
    match t with
    | TArrow (a, r, _) -> (1, [ a; r ])
    | TRecord r -> (2, [ r ])
    | TVariant r -> (3, [ r ])
    | TRowExtend (_, f, rest) -> (4, [ f; rest ])
    | TCon (_, args) -> (5, args)
    | TApp (f, a) -> (6, [ f; a ])
    | TVar _ | TRowEmpty -> (0, [])
  in
  let rec row_fields t =
    match repr t with
    | TRowExtend (l, f, rest) ->
        let fs, tl = row_fields rest in
        ((l, f) :: fs, tl)
    | t' -> ([], t')
  in
  let rec shape t =
    match repr t with
    | TVar ({ contents = Unbound _ } as r) -> Open r
    | TRowExtend _ as t' ->
        let fs, tl = row_fields t' in
        Row (List.map (fun (l, f) -> (l, shape f)) fs, shape tl)
    | t' ->
        let k, ts = kids t' in
        Fixed (k, List.map shape ts)
  in
  let rec rigids_in own t =
    match repr t with TVar r when List.memq r own -> [ r ] | t' -> List.concat_map (rigids_in own) (snd (kids t'))
  in
  let rec take l = function
    | [] -> None
    | (l', sh) :: rest when l' = l -> Some (sh, rest)
    | x :: rest -> Option.map (fun (sh, rest') -> (sh, x :: rest')) (take l rest)
  in
  let rec opens acc = function
    | Open r -> r :: acc
    | Fixed (_, shs) -> List.fold_left opens acc shs
    | Row (fs, tl) -> opens (List.fold_left (fun acc (_, sh) -> opens acc sh) acc fs) tl
  in
  let joined sh =
    let rs = opens [] sh in
    List.filter (fun r -> List.length (List.filter (fun r' -> r' == r) rs) >= 2) rs
  in
  let rec fixed_rigids own joint sh f =
    match (sh, repr f) with
    | Open r, f' -> if List.memq r joint then rigids_in own f' else []
    | _, TVar r when List.memq r own -> [ r ]
    | Row (sfs, stl), (TRowExtend _ as f') ->
        let bfs, btl = row_fields f' in
        let left, found, extra =
          List.fold_left
            (fun (sfs, acc, extra) (l, bf) ->
              match take l sfs with
              | Some (sh, sfs') -> (sfs', acc @ fixed_rigids own joint sh bf, extra)
              | None -> (sfs, acc @ rigids_in own bf, true))
            (sfs, [], false) bfs
        in
        found @ if left = [] && not extra then fixed_rigids own joint stl btl else rigids_in own btl
    | Fixed (k, shs), f' ->
        let k', ts = kids f' in
        if k = k' && List.length shs = List.length ts then List.concat (List.map2 (fixed_rigids own joint) shs ts)
        else rigids_in own f'
    | Row _, f' -> rigids_in own f'
  in
  Unify.last_rigid_clash := None;
  let group_note ~at_pre cur =
    let clashed =
      match !Unify.last_rigid_clash with
      | Some (t1, t2) -> List.filter_map (fun t -> match repr t with TVar r -> Some r | _ -> None) [ t1; t2 ]
      | None -> []
    in
    let (x, pre), own = List.assq cur members in
    let flowed =
      List.concat_map
        (fun (_, ((y, pre_y), rigids)) ->
          List.filter_map
            (fun (tp, _, r) ->
              if pre_y != pre && List.memq r clashed && mentions r pre then
                Some (Printf.sprintf "%s の型パラメータ %s が %s の型に入り込んでいます" y tp x)
              else None)
            rigids)
        members
    in
    let callers =
      List.sort_uniq compare
        (List.filter_map
           (fun (_, from, tgt, _) ->
             match from with Some f when tgt == cur && f != cur -> Some (fst (fst (List.assq f members))) | _ -> None)
           g.g_refs)
    in
    let facts =
      if not (List.exists (fun (_, _, r) -> List.memq r clashed) own) then []
      else if flowed <> [] then flowed
      else if
        at_pre
        && List.exists (fun r -> List.memq r clashed) (match List.assq_opt cur !settled_before with Some rs -> rs | None -> [])
      then List.map (fun y -> Printf.sprintf "%s の本体が、型パラメータを持つ %s を参照しています" y x) callers
      else []
    in
    let sections = if flowed <> [] then "§6.3" else "§6.3、§18.2" in
    match facts with
    | [] -> None
    | _ ->
        Some
          ("(再帰群の中で、前にある束縛から後ろにある束縛への参照は単相です。" ^ String.concat "。" facts
         ^ "。前にある束縛の本体が後ろの束縛の型パラメータを何かの型に決める形は、型検査に通りません。" ^ sections ^ ")")
  in
  let clash msg = has_sub "スコープ付きの型が一致しません" msg && not (has_sub "再帰群の中で、前にある束縛" msg) in
  Fun.protect ~finally:(fun () -> group_stack := List.filter (fun g' -> g' != g) !group_stack) @@ fun () ->
  List.iter2
    (fun ((_, b) as bnode) (((_, pre), (sig_eff, sig_vty)), rigids) ->
      (try
         at_node bnode @@ fun () ->
         g.g_cur := Some bnode;
         let snap = if settled pre then Some (shape pre) else None in
         member_marks := (bnode, Unify.hole_mark ()) :: !member_marks;
         (* pub の完全注釈検査と、省略した @ を @ {} と読む規則は、let(§11.28)と同じである。
            値束縛の先頭の矢印も、束縛の最も外側の矢印として扱う(§11.29) *)
         (if b.T.lb_pub then check_pub_annots ~tparams:(pub_tparams env_rec b.T.lb_tparams) ~params:b.T.lb_params ~ret:b.T.lb_ret);
         let env_ty = { env_rec with types = types_with env_rec rigids } in
         let fn_ty =
           match b.T.lb_params with
           | Some params ->
               let seen = ref [] in
               let param_tys = method_param_tys lvl (match snd b.T.lb_name with T.PVar x -> expected_params x | _ -> None) params in
               let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
               (* 本体を検査する行は、先に pre に置いた行と同じものを使う(§11.29) *)
               let fn_eff = match sig_eff with Some e -> e | None -> new_row_var lvl in
               let ret_ty = match b.T.lb_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> new_var lvl in
               let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
               Unify.unify ret_ty (subsume_closed lvl body_ty ret_ty);
               (* 引数パターンの網羅性検査の項目は、
                  再帰群のすべての本体を検査した後でキューに追加する(下)。
                  ここで追加すると、後ろの束縛の本体の中にある let の drain がその項目を処理して、
                  行を早く閉じてしまい、受理すべきプログラムが型エラーになる *)
               rec_arg_queue := (params, param_tys) :: !rec_arg_queue;
               TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
           | None ->
               (* 値束縛の注釈の型には、先に pre に置いた sig_vty を使う(§11.29)。
                  pub で先頭の矢印の @ を省略した注釈の行は、すでに {} と読んである。
                  本体がエフェクトを起こして単一化に失敗したときは、
                  let(§11.28)と同じ言い換えをする *)
               let vty = match sig_vty with Some t -> t | None -> new_var lvl in
               let body_ty = subsume_closed lvl (elab_exp env_ty lvl eff b.T.lb_body) vty in
               if b.T.lb_pub && not (outer_eff_written b) then unify_pub_value_annot vty body_ty ~other:type_error
               else Unify.unify vty body_ty;
               vty
         in
         (match snap with
         | Some sh -> settled_before := (bnode, fixed_rigids (List.map (fun (_, _, r) -> r) rigids) (joined sh) sh fn_ty) :: !settled_before
         | None -> ());
         (try Unify.unify pre fn_ty
          with Type_error msg when clash msg -> (
            match group_note ~at_pre:true bnode with Some note -> type_error (msg ^ note) | None -> type_error msg));
         Tree.set_ty bnode fn_ty;
         let shared, own =
           List.partition (fun (_, _, r) -> List.exists (fun (_, other) -> other != pre && mentions r other) names) rigids
         in
         release_rigids own;
         group_rigids := shared @ !group_rigids
       with Type_error_at (loc, msg) when clash msg -> (
         match group_note ~at_pre:false bnode with Some note -> raise (Type_error_at (loc, msg ^ note)) | None -> raise (Type_error_at (loc, msg)))))
    bs
    (List.combine (List.combine names sigs) tps);
  release_rigids !group_rigids;
  List.iter
    (fun (params, param_tys) ->
      List.iter2 (fun p t -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) params param_tys)
    (List.rev !rec_arg_queue);
  List.iter warn (Exhaust.drain ~level:level ~tys:(List.map snd names) ());
  (* 曖昧性は、再帰群の全体について一度に調べる。
     相互再帰の制約は、再帰群のどれかの束縛の型から到達できればよい *)
  Unify.check_ambiguity ~all:false ~level (List.map snd names);
  List.iter (fun (_, t) -> Unify.generalize level t) names;
  finish_group_dicts bs names tps g !member_marks;
  bind_names env names

(* 再帰群の終わりに、各束縛の辞書パラメータを決め、束縛ごとの穴を解き、
   pre を通った参照の証拠を、参照先の辞書パラメータの正準順で作り直す(§11.29) *)
and finish_group_dicts bs names tps g member_marks =
  let dps_of = List.map2 (fun bn (_, t) -> (bn, Unify.dkeys_of t)) bs names in
  List.iter2 (fun (bn, dps) rigids -> if dps <> [] then Tree.set_dict bn (Tree.DAbs dps); check_tparam_constraints ~rigids dps) dps_of tps;
  let marks = List.rev member_marks in
  let ends = List.tl (List.map snd marks) @ [ Unify.hole_mark () ] in
  List.iter2
    (fun (bn, lo) hi ->
      let dps = List.assq bn dps_of in
      try Unify.solve_holes_range ~lo ~hi ~params:dps
      with Unify.Unsolved_param (h, _) ->
        raise
          (Type_error_at
             ( h.Tree.h_loc,
               "曖昧な制約: " ^ display_of h.Tree.h_cls
               ^ " の辞書を、この式を含む再帰群の束縛の型から決められません(群のほかの束縛の型にだけ現れる型変数に制約が付いています。注釈で型を決めてください)"
             )))
    marks ends;
  List.iter
    (fun (node, from, tgt, keyed) ->
      let need = List.assq tgt dps_of in
      if need <> [] then (
        let have = match from with Some f -> List.assq f dps_of | None -> [] in
        let hs =
          List.map
            (fun ((_, c) as k) ->
              match List.assoc_opt k keyed with
              | Some h -> h
              | None ->
                  if not (List.mem k have) then
                    raise
                      (Type_error_at
                         ( Tree.loc_of node,
                           "曖昧な制約: 再帰群の中のこの参照が要る辞書を、呼ぶ側の束縛の型から決められません(注釈で型を決めてください)" ));
                  { Tree.h_id = new_oid (); h_cls = c; h_ty = t_unit; h_loc = Tree.loc_of node; h_sol = Some (Tree.EvParam k) })
            need
        in
        Tree.set_dict node (Tree.DUse hs)))
    g.g_refs

(* ## 11.30 トップレベルで許されるエフェクト

   トップレベルの初期エフェクト行は、ランタイムが提供する**閉じた**行である。
   内容は `{Console, Blocking}` の 2 つで、その一覧は第7章の `toplevel_effects` にある。
   2 つがこの行にある理由は、それぞれ異なる。

   - `Console`：出力が最終的に行き着くエフェクトである。
     ランタイムが実装を持ち、ユーザはハンドルできない(§11.23)。
   - `Blocking`：操作を持たないので、行に残っていても `perform` で起こせるものがない。
     sample.kel §12 は、`Blocking` を行から取り除く役目を `pinned` に任せている。
     ハンドルを禁じるエフェクトの一覧(`runtime_effects`)には入れない。
     操作がないのでハンドルを禁じる場面がなく、入れると診断が変わる(第7章 §7.3)。

   `Heap` がこの一覧にないのは、引数を取るラベルだからである(sample.kel:660-661)。
   下の `toplevel_eff` はラベルの引数に `t_unit` を置くので、`Heap` を一覧に追加しても、
   行に入るのは `Heap[Unit]` である。
   これは、`run h` が導入するスコーレム定数 `h` を持つ `Heap[h]` とは単一化できない。

   2 つのうち、`--no-prelude` でも行に残るのは `Blocking` だけである。
   `Console` はプレリュードが宣言する名前である。
   下の `toplevel_eff` は、`in_prelude` を立てている間に登録されたエフェクト
   (`Decls.prelude_owned` が真を返すもの)だけを行に入れる。
   `in_prelude` を立てるのは、プレリュードを処理する間と、組み込みを登録する間だけである。
   そのため、ユーザが同じ名前を宣言しても、それは行に入らない(`test/runtime_effects.t` の np3)。
   2 つの扱いが違うのは、宣言する箇所が違うからである。
   `Blocking` は §6.11 の組み込みの登録が宣言し、`Console` は第15章のプレリュードが宣言する。

   行が閉じているので、`perform print(...)` をトップレベルに書くと、
   `エフェクト Print をここでは実行できません` で始まる型エラーになる。
   Print はユーザが宣言したエフェクトで、ハンドラを書かない限りその操作を処理するものがないので、
   この動作は正しい。

   初期の値環境は、第6章の組み込みの表から作る。 *)

let toplevel_eff ?(extra = []) () =
  (* トップレベルの行に入れるのは、一覧 toplevel_effects のうち、
     プレリュードの処理中か組み込みの登録中に登録されたもの(Decls.prelude_owned)だけである。
     名前だけで判断して入れると、--no-prelude やプレリュードを差し替えた環境で、
     ユーザが自分の effect Console を宣言したとき、型はユーザのシグネチャ、実行はランタイムの実装になり、
     型検査に通ったプログラムが実行時にエラーになる。
     この条件を満たさなければ、その名前は行に入らず、
     perform write は `をここでは実行できません` を含む型エラーになる。
     Blocking がこの条件を満たすのは、§6.12 の register_builtins が in_prelude を立てた状態で
     add_effect を呼ぶからである(reset でも同じ経路を通る)。
     register_ref_array の呼び出しが in_prelude を立てている範囲の外に出ると、
     Blocking は、エラーを出さないままトップレベルの行から外れる。
     test/blocking_top.t の btop がこれを検出する *)
  List.fold_right
    (fun n acc -> if Decls.prelude_owned "effect" (intern n) then TRowExtend (intern n, t_unit, acc) else acc)
    (Prims.toplevel_effects @ extra) TRowEmpty

let initial_env () =
  let refs = Decls.builtin_value_refs () in
  {
    values = List.fold_left (fun m (n, t, _) -> SMap.add n t m) SMap.empty refs;
    types = SMap.empty;
    resume_ty = None;
    no_resume = None;
    tops = List.fold_left (fun m (n, _, g) -> SMap.add n g m) SMap.empty refs;
  }

(* ## 11.31 newtype の登録

   データ宣言は型の言語を変えない。
   名目的な `TCon` が 1 つ増え、宣言表にコンストラクタとフィールドの型が入るだけである。

   フィールドの型の中の型パラメータは `Generic` で束縛する。
   つまり、宣言表に置くのは型スキームで、使うたびに `subst_params` で具体化する(§11.8、§11.18)。
   組み込みメソッドの型スキームと同じ形なので、使う側のコードは 1 つで済む。

   パラメータのカインドは、本体での使われ方から推論する(sample.kel §6、sample.kel:246-247)。
   たとえば `newtype Callback[E] = Callback(() => Unit @ E)` では、`E` が矢印の `@` に現れるので、
   行カインドに決まる。
   使われ方がなければ、`Type` に決める(既定化)。

   本体で決まったカインドを型構成子のカインドにも反映するため、
   型構成子のカインドと本体は、パラメータごとに同じカインドのセルを共有する。
   パス 1a は、パラメータごとにカインドのセルを作り、
   それらを引数に持つ矢印のカインドを型構成子に登録する。
   `F[_]` と書いたパラメータ以外のセルは、新しいカインド変数である。
   パス 1b の `register_newtype` は、そのカインドからパラメータごとのカインドのセルを取り出して、
   `dd_params` の `vkind` に入れる。
   本体の精緻化が `same_kind` でそのセルのカインドを決めれば、型構成子のカインドにも反映される。
   型構成子と本体で別のセルを作ると、本体で決まったカインドが、
   1a で登録した型構成子のカインドと食い違う。

   カインドを決める手がかりは、自分の宣言の本体に限らない。
   同じ型宣言のグループ(LangSpec §6.4)にある型の本体すべてが手がかりになる(sample.kel:246-249)。
   値の本体(`let` の右辺)は手がかりにしない。
   これは、型構成子のカインドと本体が 1 つのセルを共有し、
   既定化を 1b の後処理まで遅らせる(次の段落)ことの帰結である。
   自分の本体では使っていないパラメータ(`newtype Ph[E] = MkPh(Int32)` の `E`)でも、
   同じグループの別の宣言がそれを行として使えば行カインドになる。
   例は `test/kinds.t` の phantomrow / phantomtype にある。
   宣言を 1 つ消すとカインドが変わることがあるのも、このためである。

   既定化は宣言ごとには行わず、1b の後処理で、グループのすべての宣言を処理し終えてから行う(§11.39)。
   `same_kind` は、未確定のカインド変数どうしを比べると、一方をもう一方にリンクする。
   そのため、先に処理した newtype を宣言ごとに既定化すると、
   まだ本体を読んでいないもう一方の宣言のカインドまで `KStar` に固定してしまい、
   相互に参照する newtype を受理するかどうかが宣言順に依存する(`test/kinds.t` の mutual / mutual2)。
   既定化は、`register_newtype` の呼び出し元が行う。

   この仕組みだけでは、宣言順に依存する形が 1 つ残る。
   後ろで宣言される型の行カインドのパラメータに、具体的な行を渡す形である。
   たとえば `newtype A[X] = MkA(B[{Print extends X}])` を `B` より前に置く。
   1b で `A` を処理する時点で `B` をまだ 1b で処理していないと、
   `B` のパラメータのカインドは `KVar` のままである。
   すると §11.5 の判別は `{…}` を型として読み、
   `エフェクトラベルはこの位置(レコード型)では使えません` の型エラーになる。
   行変数を渡す形(`B[X]`)は宣言順に依存しない。
   `KVar` のまま読んでも行変数がそのまま返り、後から `same_kind` がカインドを決めるからである。

   Diktor はこの形を、本体を**試しに精緻化する**ことで扱う。
   パス 1a の直後に宣言の並びをもう一度走査し、
   newtype とエイリアスの本体を読んでパラメータのカインドを決めてから、1b に入る。
   読んだ結果と診断は捨てる。
   この処理は `speculate_newtype` と `speculate_alias` が行う(§11.39)。
   1b で `A` を処理する時点で `B` のパラメータが行だと分かっているので、
   判別は `{…}` を行として読む。
   `test/kinds.t` の fwdrow / fwdrow2 が両方の宣言順を確かめ、
   fwdrow3 と fwdrowmod / fwdrowmod2 が連鎖と module の中の形を確かめる。
   連鎖の多くは、宣言順の 1 回の走査でカインドが決まる。
   `same_kind` はカインドのセルどうしをリンクするので、連鎖の末端で行に決まれば、
   手前のセルも同時に行に決まるからである。

   試しの精緻化を 1b の前に行っても安全なのは、次の 2 つの理由による。
   第一に、試しの精緻化は `elab_type` を呼ぶだけで、コンストラクタを登録しない。
   `Decls.add_data` も `Unify.generalize` も `pub` の完全注釈検査も呼ばないので、
   残る副作用は `elab_type` がカインドのセルを決めることだけで、それがこの処理の目的である。
   第二に、上の形で試しの精緻化が失敗しても、それまでに決まったカインドは正しい。
   `A` の試しの精緻化は `B[{Print extends X}]` を型として読む。
   `extends` の右は行かレコード型でなければならないので、
   `same_kind` が `X` を `Type` ではなく `Row` に決める。
   その後 `BLabel` の分岐が型エラーになり、試しの精緻化は診断を捨てるが、
   `X` に決まったカインドは正しい。

   試しに精緻化する時点で、ユーザが宣言したエフェクトの名前はすでに宣言表にある。
   パス 1a が名前だけを登録し、操作を 1b で書き込むからである(§11.32、§11.39)。
   そのため、`() => Unit @ {Log}` のような通常のフィールドも、この時点で読める。

   試しの精緻化では、次の 3 つの対処をしている。

   1 つ目は、例外をフィールドごとに捕捉して捨てることである。
   本体全体を 1 つの `try` で囲むと、
   あるフィールドの読み取りがエラーになったとき、後続のフィールドが読まれず、
   そのフィールドが決めるはずのカインドが `KVar` のまま 1b に入る。
   フィールドごとに捨てれば、手前のフィールドがエラーになっても、後続のフィールドがカインドを決める
   (`test/kinds.t` の specfield / specfield2 と、前方参照の連鎖の specfwd)。

   2 つ目は、試しに精緻化している間だけ、
   要素のない波括弧(`{}` と `{extends R}` の 2 つの形)をパラメータとの照合に使わないことである。
   照合に使わないのは、カインドが未確定のパラメータへ渡したものに限る。
   `newtype A[X] = MkA(B[{}], () => Unit @ X)` を `B` より前に置くと、
   `A` を試しに精緻化する時点では `B` のパラメータのカインドが `KVar` のままである。
   ここで `{}` を型として読んで照合すると、`elab_con_args` が `B` のパラメータを `Type` に決め、
   `B` 自身が `行カインドではない型パラメータです: E` の型エラーになる。
   対象をこの 2 つの形に限るのは、型としても行としても読めるのがこの 2 つだけだからである。
   ラベルが 1 つでもあれば、型として読むとエラーになるので、パラメータを `Type` に決めることはない。
   照合に使わなくても問題はない。
   渡す先のパラメータのカインドが決まった状態で、
   1b が同じ表記をもう一度読むからである(`test/kinds.t` の specunit / specunit2)。
   §11.5 の `expand_alias` も同じ規則で判別するが、
   照合に使わなかった引数の代わりに何を渡すかが違う。
   newtype への型引数は本体を展開しないので、`elab_con_args` は `Unit` を渡す。
   エイリアスは本体を展開するので、`Unit` を渡すと、それが本体の中の別の型構成子の引数になり、
   その型構成子のパラメータを `Type` に決めてしまう。
   そこで `expand_alias` は、カインドのセルをパラメータと共有する新しい型変数を渡す
   (`test/kinds.t` の aliasunit3)。

   3 つ目は、カインドが決まったパラメータの個数が増えなくなるまで、
   試しの精緻化を繰り返すことである。
   1 回の走査では決まらない形があるからである。
   `newtype B[E] = MkB((() => Unit @ E, C[{Log}]))` を `C` より前に置くと、
   `B` を読む時点で `C` のパラメータのカインドが未確定なので、
   右端の `C[{Log}]` を型として読んでエラーになり、`E` のカインドが決まらない。
   次の回では、`C` のパラメータが前の回で `Row` に決まっているので、`{Log}` を行として読める
   (`test/kinds.t` の specfix)。
   数えるのは newtype とエイリアスの両方のパラメータである。
   エイリアスのカインドだけが増えた回の後にも、
   そのエイリアスを読む newtype が前の回でエラーになっていることがある
   (`test/kinds.t` の specalias)。
   個数はパラメータの総数を超えないので、繰り返しは終わる。

   1 つのフィールドの中に行変数とラベルが並ぶ形
   (`MkB((() => Unit @ E, () => Unit @ {Log}))`)も、フィールド全体を読むので、
   どちらの宣言順でも `E` のカインドが決まる(`test/kinds.t` の specinner / specinner2 と speclab / speclab2)。

   右辺を省いた `newtype T` は、コンストラクタが 0 個のデータ型として登録する。
   値を持たない型になるので、`match {}` は網羅的で、`case _` には一致する値がない。

   フィールドの型の精緻化はこの登録のときに済ませるので、
   パス 2 で newtype に出会っても何もしない。
   未知の型を書けば、この時点でエラーになる。

   `pub newtype` のフィールドには完全な型注釈を要求する(sample.kel §13)。
   入れ子の矢印で省略した `@` は `@ {}` を意味する。
   しかし仕様は、公開 API では、純粋を意図したのか書き忘れたのかを読者が区別できなければならないとしている。
   判定には、`let` の `check_pub_annots` と同じ `unwritten_effect` を使う(`test/pub.t` の pubnt)。
   sample.kel の `Parser` が `@ {}` を明示しているのは、そのためである。

   フィールドの型のカインドが `Type` であることも、ここで検査する。
   検査しないと、行カインドのパラメータや `EffectRow` エイリアスがそのまま値の型になり、
   値を作る箇所までエラーにならない。
   `newtype Bad[E] = Bad(() => Unit @ E, E)` は、第 1 フィールドで `E` が行に決まり、
   第 2 フィールドでエラーになる。
   判定には `same_kind` を使うので、判定は推論も兼ねる。
   型パラメータ 1 つだけを書いたフィールド(`newtype Id[A] = Id(A)`)では `A` のカインドがまだ未確定で、
   判定が `A` のカインドを `Type` に決める(`test/kinds.t` の fieldkind)。

   この検査は、値の型の位置に対する一般の検査(§11.3)を、
   コンストラクタのフィールドに適用したものである。
   照合そのものは §11.3 の `check_value_kind` が行い、
   ここではメッセージの名詞句にコンストラクタ名を添えるだけである。
   フィールドの最も外側の型でカインドが合わないときのメッセージが、
   `コンストラクタ X のフィールドの型のカインドが Type ではありません` になるのはそのためである。
   どのコンストラクタのフィールドかをメッセージで示せるのは、この位置だけである
   (`test/kinds.t` の fieldkind / fieldalias)。

   フィールドの型の内側の位置は、§11.3 の照合が位置ごとにエラーにする。
   `newtype Bad2[E] = Bad2((E, Int32), () => Unit @ E)` は、
   第 1 フィールドのタプルで `E` が `Type` に決まり、第 2 フィールドの `@ E` でエラーになる。
   `newtype Bad3[E] = Bad3(() => Unit @ E, {a: E})` は逆の順なので、
   レコードのフィールド `a` の側でエラーになる。
   メッセージは `レコードのフィールド a の型のカインドが Type ではありません: R1 :: Row` である。
   位置ごとに照合しないと、どちらも受理され、
   行カインドのパラメータを値の型に持つ型スキームが宣言表に入る。
   `test/kinds.t` の rowval / rowval2 / rowval3 / hktval が、この照合を確かめている。 *)

(* 1a が型構成子のカインドに入れた、パラメータごとのカインドのセルを取り出して、
   パラメータの型環境を作る。
   型構成子と本体で別のセルを作ると、本体で決まったカインドが型構成子のカインドに反映されない。
   register_newtype と、1a の後に行う試しの精緻化が、この関数を使って同じセルを共有する *)
let newtype_param_env env (n : T.newtype') =
  let head_kinds =
    let k = Decls.con_kind (intern n.T.nt_name) (List.length n.T.nt_params) in
    let rec peel k n =
      if n = 0 then []
      else match kind_repr k with KArrow (a, r) -> a :: peel r (n - 1) | _ -> List.init n (fun _ -> new_kind_var ())
    in
    peel k (List.length n.T.nt_params)
  in
  let params =
    List.map2
      (fun (tp : type_param) hk ->
        let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else hk in
        { vid = new_oid (); vlevel = 0; vkind = kind; vcls = [] })
      n.T.nt_params head_kinds
  in
  let types =
    List.fold_left2
      (fun m (tp : type_param) i -> SMap.add tp.tp_name (TVar (ref (Generic i))) m)
      env.types n.T.nt_params params
  in
  (params, { env with types })

(* newtype の本体を 1b より前に試しに精緻化し、パラメータのカインドだけを決める(§11.31)。
   型エイリアスを試しに精緻化するとき(§11.39)と同じ方法を使う。
   コンストラクタの登録も、pub の注釈検査も、generalize も行わず、
   elab_type の副作用であるカインドの決定だけを残す。
   診断は捨てる。
   捕捉する例外は Type_error、Type_error_at、NotImplemented、NotImplemented_at の 4 つだけで、
   Panic は捕捉しない。
   試しの精緻化が必要なのは、後ろで宣言される型の行カインドのパラメータに、
   具体的な行を渡す形があるからである。
   たとえば `newtype A[X] = MkA(B[{Print extends X}])` を `B` より前に置くと、
   1b で A を処理する時点では B のパラメータのカインドがまだ決まっていないので、
   §11.5 の判別が `{…}` を型として読む(`test/kinds.t` の fwdrow) *)
let speculate_newtype env (n : T.newtype') =
  match n.T.nt_rhs with
  | T.NtCtors ctors ->
      let _, env' = newtype_param_env env n in
      (* 例外はフィールドごとに捕捉して捨てる。
         本体全体を 1 つの try で囲むと、1 つのフィールドがエラーになったときに、
         後続のフィールドが決めるはずのカインドまで決まらなくなる *)
      let speculate (f : T.field_decl) =
        try ignore (elab_type env' 1 f.T.fd_ty)
        with Type_error _ | Type_error_at _ | NotImplemented _ | NotImplemented_at _ -> ()
      in
      speculating := true;
      Fun.protect
        ~finally:(fun () -> speculating := false)
        (fun () -> List.iter (fun (c : T.ctor_decl) -> List.iter speculate c.T.cd_fields) ctors)

(* 型エイリアスの本体を試しに 1 回精緻化し、パラメータのカインドだけを決める(§11.39)。
   結果も診断も捨てる。
   捕捉する例外は speculate_newtype と同じ 4 つで、Panic は捕捉しない *)
let speculate_alias env (t : T.type_alias') =
  match Hashtbl.find_opt Decls.aliases (intern t.T.ta_name) with
  | None -> ()
  | Some info ->
      speculating := true;
      Fun.protect
        ~finally:(fun () -> speculating := false)
        (fun () ->
          try
            let rigids = make_rigids ~kinds:info.Decls.al_kinds 1 info.Decls.al_params in
            let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
            ignore
              (match info.Decls.al_kind with
              | Some "EffectRow" -> elab_eff env_ty 1 info.Decls.al_body
              | _ -> elab_type env_ty 1 info.Decls.al_body)
          with Type_error _ | Type_error_at _ | NotImplemented _ | NotImplemented_at _ -> ())

let register_newtype env (n : T.newtype') =
  (* newtype のパラメータのカインドは、本体での使われ方から推論する。
     F[_] と書いてあれば、その時点でカインドが決まる。既定化は 1b の後処理で行う *)
  let params, env' = newtype_param_env env n in
  match n.T.nt_rhs with
  | T.NtCtors ctors ->
      let ctors =
        List.map
          (fun (c : T.ctor_decl) ->
            {
              Decls.ct_name = intern c.T.cd_name;
              ct_fields =
                List.map
                  (fun (f : T.field_decl) ->
                    (* pub の完全注釈検査(sample.kel §13)は、フィールドの矢印も対象にする。
                       省略した @ の意味は @ {} に決まっているが、公開 API では、純粋な関数を
                       意図したのか、@ を書き忘れたのかを、読者が区別できなければならない
                       (sample.kel:825-831)。フィールドも対象になることは :828-829 に
                       書かれている。診断はそのフィールドの型を指す。
                       宣言の先頭を指すと、どのフィールドが原因かが位置から分からない *)
                    (if n.T.nt_pub then
                       at_node f.T.fd_ty (fun () ->
                           pub_effect_error "pub な newtype のフィールド"
                             (unwritten_effect ~expanding:[]
                                (pub_scope (List.map (fun (tp : type_param) -> tp.tp_name) n.T.nt_params))
                                f.T.fd_ty)));
                    let ty = elab_type env' 1 f.T.fd_ty in
                    (* フィールドの型のカインドは Type でなければならない。
                       値の型を書くどの位置にも行う検査(§11.3)をフィールドに適用したもので、
                       検査そのものは check_value_kind が行う。
                       フィールドの型全体のカインドをここで検査するのは、
                       どのコンストラクタのフィールドかをメッセージに書けるのがここだけだからである。
                       メッセージの名詞句にはコンストラクタ名を添える。
                       フィールドの型の内側にある型は、elab_value_type が位置ごとに検査する *)
                    at_node f.T.fd_ty (fun () -> check_value_kind ("コンストラクタ " ^ Type.display c.T.cd_name ^ " のフィールドの型") ty);
                    (* 省略した @ など、束縛されずに残った変数は、型スキームでは Generic にする *)
                    Unify.generalize 0 ty;
                    { Decls.fi_label = Option.map intern f.T.fd_label; fi_ty = ty })
                  c.T.cd_fields;
            })
          ctors
      in
      Decls.add_data { Decls.dd_name = intern n.T.nt_name; dd_params = params; dd_ctors = ctors; dd_opaque = false }

(* ## 11.32 effect の登録

   エフェクト宣言は、操作名から矢印の型スキームを引く表である。
   操作の型が矢印でなければならないのは、`perform` が引数と返り値を必要とするからである。

   effect 宣言には型パラメータを書けない(sample.kel §9)。
   エフェクトのパラメータは、行の中ではラベルの引数になる。
   ラベルの引数を使っているのは、`Heap[h]` のような組み込みのエフェクトである。
   ユーザが宣言するエフェクトにパラメータを許すと、操作の型がパラメータについて多相になる。
   するとハンドラの節が多相な継続を受け取ることになり、ランク 2 の型が必要になる。
   ランク 1 の範囲で扱えるのは、エフェクトのパラメータを組み込みのエフェクトにだけ許す形までである。

   操作の型の引数に現れる矢印は、入れ子の矢印として読む(sample.kel §9)。
   `spawn: (() => Unit @ Async) => Unit` の `@ Async` を暗黙に多相にしないのは、
   実装の都合ではなく仕様の規則である(`test/annot_rows.t` の opsig / opsig2)。
   操作の型の先頭の矢印で省略した `@` も `TRowEmpty` になる。
   ただし、`perform` も `handle` も操作の型スキームの行を使わないので、
   この行は検査の結果に影響しない。

   登録は 2 段階に分かれる。
   パス 1a が `Decls.declare_effect` で名前だけを宣言表に登録し、
   `register_effect` は 1b で操作の型スキームを書き込む(`Decls.set_effect_ops`)。
   型の本体に書いたエフェクトラベルは、宣言表に名前があるかどうかだけで解決する。
   そのため、型を書くどの位置にも、後ろで宣言する effect のラベルを書ける。
   1b で読む型の本体(newtype のフィールド、effect の操作の型、クラスのメソッドの型と、
   そこから使う型エイリアスの本体)でも同じである(`test/effect_order.t`)。
   型パラメータの検査は、操作の検査と同じく 1b で行う。

   同じエフェクトの中での操作名の重複は拒否する。
   別のエフェクトとの重複は許す。
   §11.20 の非修飾の操作名の解決は、
   別のエフェクトどうしで操作名が重複することがあるのを前提にしている。

   操作ごとの診断(予約された名前、名前の先頭の文字、矢印でない型、名前の重複)は、
   その操作の型の位置を指す。
   構文木の操作名は位置を持たないので、名前の右に書いた型の位置で操作を指す。
   名前の重複の診断は、2 度目の宣言の型を指す。 *)

let register_effect env (e : T.effect') =
  if e.T.ef_params <> [] then type_error "effect 宣言に型パラメータは書けません(sample.kel §9)";
  (* return / cancel は、handle の節の分類(§11.22)が return 節と cancel 節の名前として
     先に読むので、操作名としては宣言できない。受理すると、その操作の操作節は
     修飾しても書けないので、その操作を含む effect はハンドルできない *)
  List.iter
    (fun (op, te) ->
      at_node te @@ fun () ->
      if op = "return" || op = "cancel" then
        type_error ("操作名 " ^ op ^ " は予約されています(handle の " ^ op ^ " 節と衝突するため宣言できません)");
      (* 節の分類(§11.22)が操作節として読むのは、英小文字で始まる名前だけである。
         _ で始まる名前を受理すると、ハンドルできない effect になる *)
      if String.length op = 0 || not (op.[0] >= 'a' && op.[0] <= 'z') then
        type_error ("操作名 " ^ op ^ " は英小文字で始めてください(handle の節が操作名として読めません)"))
    e.T.ef_ops;
  (* 同じ effect の中での操作名の重複を拒否する。診断は 2 度目の宣言の型を指す *)
  let rec dup = function
    | [] -> ()
    | (op, _) :: rest ->
        (match List.assoc_opt op rest with
        | Some te2 -> at_node te2 (fun () -> type_error ("操作 " ^ op ^ " が二重に宣言されています"))
        | None -> ());
        dup rest
  in
  let ops =
    List.map
      (fun (op, te) ->
        match snd te with
        | T.EArrow _ ->
            let ty = elab_type env 1 te in
            Unify.generalize 0 ty;
            (intern op, ty)
        | _ -> at_node te (fun () -> type_error ("操作 " ^ op ^ " の型は矢印型でなければなりません")))
      e.T.ef_ops
  in
  dup e.T.ef_ops;
  Decls.set_effect_ops { Decls.ef_name = intern e.T.ef_name; ef_ops = ops }

let binding_name (b : T.let_binding') = match snd b.T.lb_name with T.PVar x -> Some x | _ -> None

(* ## 11.33 type class の登録

   クラスパラメータは 1 つだけである。
   仕様は多パラメータ型クラスを意図して除外している(sample.kel:356)。
   パラメータが 1 つなので、変数の状態 `Generic` だけで多相を表せて、
   型スキーム専用のデータ型も制約ストアも持たずに済む。

   パラメータは、個数だけでなくカインドも決まっている。
   `tp_arity` が 0 なら `KStar`、`F[_]` なら `[_] Type` である。
   一般には、`tp_arity` 個の `Type` を取って `Type` を返すカインドになる。
   newtype の束縛子と違い、クラスパラメータは `KVar` を経由しない(§1.12)。
   カインドをこう固定しているので、クラスパラメータは `EffectRow` を取れない。
   カインドを固定する理由は、インスタンス表のキー(§11.34)にある。
   インスタンス表のキーは(クラス, 型構成子)の組で、
   型検査は、クラスパラメータに決まった型の先頭の型構成子でこの表を引く(§8.11)。
   行はラベルの集合で、型構成子を持たないので、キーにならない。
   sample.kel §8 がこれを定めている(sample.kel:359-361)。

   クラスパラメータのカインドを固定していても、エフェクト多相なクラスは書ける。
   メソッドの型パラメータは `KVar` を作るので、行カインドになれる。
   `val run_[E]: (A, () => Unit @ E) => Unit @ E` は型検査に通る。
   エフェクトについて量化したいクラスは、クラスパラメータではなく、
   メソッドの型パラメータに行変数を取る(sample.kel:362-363)。
   sample.kel §8 の `Functor` の `map` がその例で、
   `test/kinds.t` の classrow / classrow2 / classrowok がこの形をテストしている。

   メソッドの型は、型スキームとして表に登録する。
   `val map[A, B, E]:` のようにメソッドは自分の型パラメータを持てるので、
   この型スキームでは、クラスパラメータとメソッド固有の型パラメータの両方を `Generic` にする。
   クラスパラメータには `vcls` としてクラス名が付いている。
   このクラス名が、メソッドを使う位置で、
   「この変数はこのクラスのインスタンスでなければならない」という制約になる。
   メソッドの型パラメータに書いた制約のクラス名の検証だけは、ここでは行わず、
   パス 1b の後に行う(§11.39)。
   クラスどうしの宣言順に依存させないためである。

   `Integral` と `Fractional` はユーザが宣言できない。
   どちらも、数値リテラルの型を絞る予約述語の名前である(§11.2)。
   どの名前が予約されているかの表は第6章(`Decls.reserved_predicates`)が持ち、
   ここではその表を引くだけである。
   インスタンス宣言を登録する `register_instance`(§11.35)と
   第6章の `add_instance`(§6.9)も、同じ表を引いて検査する。

   組み込みと同名のクラスをユーザが宣言すると、第6章の `add_class_decl` が、
   標準環境の名前の再宣言として拒否する。

   ### 最も外側の `@` の省略を `@ {}` と読むのは、注釈の先頭が矢印リテラルのときだけ

   sample.kel §9 は、束縛の最も外側の矢印の規則を、型クラスのメソッドにも適用する(sample.kel:478)。
   メソッドの注釈の最も外側の矢印で `@` を省略すると `@ {}` と読み、
   どのインスタンスの実装も純粋でなければならない(sample.kel:437-438、:495)。
   `elab_type_outer` はこの位置の省略を新しい行変数にするので、
   登録するときにそれを `TRowEmpty` に置き換える。
   実装が純粋であることは、インスタンス本体の包摂(§11.38)で検査する。

   書いた行は、閉じた行も行変数を含む行も、書いたとおりに型スキームに入れる。
   閉じた行のメソッドも、名前で参照するときと呼び出すときに行を開くので(§11.26)、
   `val f: (T) => Int32 @ Console` のメソッドは、Console を含むどの行の文脈からも呼べる。
   省略を `@ {}` と読んだメソッドも、同じくどの行の文脈からも呼べる。

   置き換えるのは、注釈の先頭が矢印リテラルのときに限る。
   先頭が型エイリアスなら、展開先の矢印は入れ子の矢印で(§11.5 の規則 4)、
   省略した `@` は初めから `@ {}` になっている。
   `elab_type_outer` の結果が矢印かどうかで判定すると、
   エイリアスの展開先に書いた行まで `TRowEmpty` に置き換えてしまう。
   そうすると、`type F[A] = (A) => Int32 @ Print` の `{Print}` が、値束縛では残り、
   クラスメソッドでは消えることになる。
   `test/annot_rows.t` の clsalias3 / clslit が、
   エイリアスで書いても矢印リテラルで書いても同じ閉じた行になることを固定している。

   判定には、ソースに書いた構文 `snd v.T.cv_ty` を使う。
   値束縛も同じ方法で判定する。
   注釈 `snd t` を調べて、`pub` で省略した `@` を置き換えるかどうかを決める(§11.28)。
   `pub` の言い換えの判定 `outer_eff_written` は `lb_ret` を調べる(§11.28)。
   同じことを調べる判定がこのように分かれているので、どれかを変えるときは、
   残りも合わせて変える必要がある。
   脱糖が変わると、これらの判定はエラーを出さずに働かなくなる。
   この変化は cram のテストで検出する(`test/annot_rows.t` の clsalias3 / clslit と valopen / alval)。

   エイリアスで書いたメソッドを、`@` を省略した関数から呼ぶと、
   呼び出し元の行は本体から推論され、メソッドの閉じた行のラベルを含む行になる(clsalias3ok)。
   この結果は、エイリアスで書いた値束縛(alval)と同じく、
   仕様が定めた注釈の読み方からそのまま導かれる。

   ### スーパークラスは持たない

   クラスパラメータへの制約 `type class Ord[A: Eq]` は拒否する。
   sample.kel §8 は、スーパークラスを導入しないと定めている。
   制約の含意がないほうが、シグネチャに書いた制約だけで解決が決まり、規則が単純になるからである。
   `Ord` は `Eq` を含意しないので、両方が必要な場面では `[A: Eq + Ord]` と並べて書く。
   診断もそう案内する(`test/classes.t` の super / ordeq / ordeq2)。
   含意がないことは、次の形で確かめられる。
   `[A: Ord]` だけで `==` を使うと、`Eq のインスタンスではありません` というエラーになる。

   ### クラスパラメータがメソッドの型に現れること

   Diktor は、メソッドの宣言に 2 つの条件を課す。
   メソッドの型は矢印型で、クラスパラメータがその型のどこかに現れていなければならない。
   引数の型に現れず、返り値の型にだけ現れてもよい(LangSpec §12.1)。

   この条件が必要なのは、どのインスタンスのメソッドを呼ぶかを、型検査が型から決めるからである。
   メソッドを参照すると、型スキームの具体化がクラスパラメータの制約の穴を作る(§8.11)。
   穴の型は、引数か返り値のうち、クラスパラメータが現れる位置の型が決まるときに決まる。
   `pure : (A) => F[A]` では、`let one: Option[Int32] = pure(1)` の注釈が `F` を決める。
   クラスパラメータが型に現れないメソッドは、どの位置の型が決まっても穴の型が決まらない。
   インスタンスを選ぶ手掛かりがないので、宣言を拒否する。
   検査では、一般化した型スキームの制約のキーの並び(`dkeys_of`)に、
   クラスパラメータのキーがあるかどうかを調べる。
   クラスパラメータは `vcls = [cls]` の `Generic` 変数なので、型のどこかに現れればキーの並びに入る。

   メソッド自身の型パラメータに制約を付けるときは、
   その型パラメータもメソッドの型に現れなければならない。
   `val pp[B: Show]: (A) => String` は拒否する。
   型に現れない型パラメータの制約はキーの並びに入らないので、メソッドを使う位置で辞書が作られず、
   制約を書いても何も要求しないからである。
   束縛の型パラメータの制約(§11.28)と同じ規則で、診断の形式もそろえている。
   制約のない型パラメータ(`val pp[B]: (A) => String`)は、型に現れなくても受理する。

   値のメソッド(`val empty: F[A]` のような矢印でない型のメソッド)は、
   辞書渡しの仕組みでは表せるが、許していない。
   初期化式をいつ評価するかを仕様が定めていないからである。

   ### 同じ非修飾のメソッド名を持つクラスは 1 つまで

   ここでは、同じ非修飾のメソッド名を持つクラスは 1 つまで、という不変条件も守る。
   非修飾のメソッド名は、単位から見えるクラスのうち、
   その名前のメソッドを持つものに解決する(パス 1b)。
   同名のメソッドを持つクラスが 2 つあると、名前からはどちらのメソッドかを決められない。
   型から決めるには、両方の候補の型スキームで検査を試す仕組みが必要になる。
   そこで、名前の衝突そのものを宣言の時点で拒否する。
   先に宣言したクラスを優先する規則も、後に宣言したクラスを優先する規則も採らない。
   どちらの規則でも、一方のクラスのメソッド名が、診断のないまま非修飾名では使えなくなるからである。
   検査は既存のクラスをすべて走査する。
   宣言のたびにこの不変条件を保つので、
   新しい宣言のメソッド名と衝突する既存のクラスは高々 1 つである。
   そのため、表を走査する順序によらず、エラーメッセージは同じになる。

   この検査が扱うのは、クラスどうしの衝突だけである。
   クラスメソッドと同名のトップレベルの `let` / `extern` との衝突は拒否せず、
   **先に宣言したほうを優先する**。
   非修飾名が指すのは、最初にその名前を持った宣言である。
   プレリュードの `echo` がある状態でユーザのクラスが `echo` メソッドを宣言しても、
   非修飾の `echo` はプレリュードの `echo` のままである(メソッドは `Cls.echo` と修飾すれば呼べる)。
   逆に、クラスより後に書いた同名の `let` は、パス 2 が束縛を宣言順に環境へ追加するので、
   その `let` より後のコードにだけ見える。
   評価器は、型検査が `resolved` に書いた参照先の宣言で値を引く(§11.11、第14章 §14.4)。
   そのため、どちらを優先する規則を選んでも、型検査と実行は同じ宣言を選ぶ。
   先に宣言したほうを優先するのは、先にあった名前(プレリュードの `echo` など)を、
   後から宣言したクラスが診断のないまま使えなくすることを防ぐためである。 *)

let register_class env (c : T.class_decl') =
  let cls = intern c.T.cls_name in
  (if Decls.reserved_predicate (intern (Type.display c.T.cls_name)) then
     type_error (Type.display c.T.cls_name ^ " は予約されたリテラル述語です(ユーザ宣言不可、D8)"));
  let param =
    match c.T.cls_params with
    | [ p ] -> p
    | _ -> type_error "type class のパラメータは1個です(多パラメータ型クラスは意図的に排除、sample.kel:356)"
  in
  let param_kind = if param.tp_arity > 0 then k_arrow param.tp_arity else KStar in
  (if param.tp_classes <> [] then
     type_error
       "クラスパラメータに制約は書けません(スーパークラスは入れない裁定です。両方が要るときは [A: Eq + Ord] のように並べて書いてください)");
  let pinfo = { vid = new_oid (); vlevel = 0; vkind = param_kind; vcls = [ cls ] } in
  let pvar = TVar (ref (Generic pinfo)) in
  let methods =
    List.map
      (fun (v : T.class_val) ->
        let mt_params =
          List.map
            (fun tp ->
              (* カインドは型パラメータを使った位置から推論する。決まらなかったカインドは、
                 メソッドの型を一般化した直後に KStar に決める(既定化。第1章 §1.6) *)
              let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var () in
              let classes = List.map (fun li -> Decls.resolve_class (intern (show_long_id li))) tp.tp_classes in
              (tp.tp_name, TVar (ref (Generic { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes }))))
            v.T.cv_tparams
        in
        let types = List.fold_left (fun m (n, t) -> SMap.add n t m) (SMap.add param.tp_name pvar env.types) mt_params in
        let ty = elab_type_outer { env with types } 1 v.T.cv_ty in
        (* メソッドの最も外側の矢印で省略した @ は @ {} と読む(§11.33)。elab_type_outer は
           この位置の省略を新しい行変数にするので、ここで TRowEmpty に置き換える。
           書いた行は書いたとおりに残し、閉じた行は使うときに開く(§11.26)。
           置き換えるのは、注釈の先頭が矢印リテラルのときだけである。先頭が型エイリアスなら、
           展開先の矢印は入れ子の矢印なので、省略した @ は初めから @ {} になっていて、
           書いた行は書いたとおりに残る(§11.5 の規則 4)。値束縛の判定(§11.28)と同じく、
           ソースに書いた構文を調べる判定で、ここでは cv_ty を調べる。
           どちらかを変えるときは、もう一方も合わせて変える *)
        let ty =
          match (snd v.T.cv_ty, repr ty) with
          | T.EArrow (_, _, None), TArrow (a, r, _) -> TArrow (a, r, TRowEmpty) (* 先頭の矢印で省略した @ は @ {} *)
          | _ -> ty
        in
        Unify.generalize 0 ty;
        List.iter (fun (_, t) -> match repr t with TVar r -> default_kind (Unify.var_info_of r).vkind | _ -> ()) mt_params;
        (* クラスパラメータがメソッドの型のどこかに現れることを要求する(§11.33)。
           メソッドの参照で作る穴の型が、クラスパラメータの現れる位置の型から決まるためである。
           一般化した型スキームの制約のキーの並びに、クラスパラメータのキーがあるかどうかで判定する *)
        (at_node v.T.cv_ty @@ fun () ->
         match repr ty with
         | TArrow _ ->
             if not (List.exists (fun (vid, _) -> vid = pinfo.vid) (Unify.dkeys_of ty)) then
               type_error
                 ("メソッド " ^ v.T.cv_name ^ " の型にクラスパラメータが現れません(どのインスタンスのメソッドかを型から決められません)")
         | _ -> type_error ("メソッド " ^ v.T.cv_name ^ " の型は矢印型でなければなりません"));
        (* メソッドの型パラメータに制約を付けたときは、その型パラメータがメソッドの型に
           現れることを要求する(束縛の check_tparam_constraints と同じ規則)。
           型に現れない変数の制約はキーの並びに入らないので、メソッドを使う位置で辞書が作られない。
           この検査は関数として返す。呼び出し元は、1b の後処理で未知のクラスと予約述語を
           検査した後に、この関数を呼ぶ *)
        let check_tparams () =
          let dks = Unify.dkeys_of ty in
          List.iter
            (fun (name, t) ->
              match repr t with
              | TVar r ->
                  let i = Unify.var_info_of r in
                  List.iter
                    (fun c ->
                      if (not (Unify.is_predicate c)) && not (List.mem (i.vid, c) dks) then
                        type_error
                          ("曖昧な制約: メソッド " ^ v.T.cv_name ^ " の型パラメータ " ^ name ^ " の制約 " ^ display_of c
                         ^ " をメソッドの型から決められません(メソッドの型に現れない型パラメータに制約が付いています)"))
                    i.vcls
              | _ -> ())
            mt_params
        in
        (v.T.cv_name, ty, check_tparams))
      c.T.cls_vals
  in
  let checks = List.map (fun (_, _, k) -> k) methods in
  let methods = List.map (fun (m, ty, _) -> (m, ty)) methods in
  (* 同じクラスの中でのメソッド名の重複を拒否する(register_effect の操作名の重複と同じ)。
     重複を受理すると、elab が修飾名に与える型は最後の宣言で決まり、インスタンス本体の検査は
     最初の宣言と比べるので、型検査に通ったプログラムが、実行時に型や引数の個数の
     食い違いで誤動作する。
     上の 2 つの検査(クラスパラメータが現れることと、型が矢印型であること)と、この重複の検査は、
     at_node で囲んでいるので、診断はメソッドの型の位置を指す。
     重複の診断は 2 度目の宣言の型を指す。
     メソッドの型パラメータの制約の検査(check_tparams と、1b の後処理の未知のクラスの検査)は
     at_node で囲んでいないので、診断は宣言の先頭を指す *)
  let rec dup = function
    | [] -> ()
    | (v : T.class_val) :: rest ->
        (match List.find_opt (fun (w : T.class_val) -> w.T.cv_name = v.T.cv_name) rest with
        | Some w -> at_node w.T.cv_ty (fun () -> type_error ("メソッド " ^ v.T.cv_name ^ " が二重に宣言されています"))
        | None -> ());
        dup rest
  in
  dup c.T.cls_vals;
  (* 同じ非修飾のメソッド名を持つクラスは 1 つまで、という不変条件をここで守る(§11.33)。
     この検査がないと、パス 1b は非修飾名を先に宣言したクラスのメソッドに解決し、
     後から宣言したクラスのメソッドは、診断のないまま非修飾名では呼べなくなる。
     組み込みと同名のクラスを宣言したときは、表示名が同じその組み込みのクラスを比較対象から外すので、
     ここでは衝突にならず、下の add_class_decl が拒否する。
     宣言のたびにこの不変条件を保つので、新しい宣言のメソッド名と衝突する既存のクラスは高々 1 つである。
     そのため、表を走査する順序によらず、メッセージは同じになる *)
  List.iter
    (fun (m, _) ->
      Hashtbl.iter
        (fun _ (other : Decls.class_info) ->
          if
            Type.display_of other.Decls.ci_name <> Type.display_of cls
            && Decls.visible_in_unit Decls.unit_classes other.Decls.ci_name
            && List.mem_assoc m other.Decls.ci_methods
          then
            type_error
              ("メソッド名 " ^ m ^ " は型クラス " ^ display_of other.Decls.ci_name
             ^ " が既に宣言しています(非修飾名が衝突するため、v0 では同名メソッドを複数のクラスに宣言できません)"))
        Decls.classes)
    methods;
  Decls.add_class_decl
    {
      Decls.ci_name = cls;
      ci_param = pinfo;
      ci_param_kind = param_kind;
      ci_derive_structural = false;
      ci_builtin = false;
      ci_methods = methods;
    };
  (methods, fun () -> List.iter (fun k -> k ()) checks)

(* ## 11.34 インスタンスの対象の型

   インスタンスの対象の型(診断では「インスタンス頭」)に書けるのは、
   `Int32` か `List[_]` の形だけである。
   `List[Int32]` のように引数を具体的な型にした形は書けない。
   `_` は型引数の位置を表す。
   前提付きインスタンス(sample.kel §8)の束縛子は、この位置に左から順に対応する(sample.kel:413-414)。
   型パラメータのリストを `instance` の直後に書くことと、
   `instance` と `[` の間に空白や改行を自由に置けることは、
   仕様の同じ段落の 1 行目に書かれている(sample.kel:411)。

   束縛子が左から順に穴 `_` を埋め、埋まらなかった穴はカインドの矢印として残る。
   同じ `List[_]` でも、表すものは束縛子の個数で変わる。
   `Functor[List[_]]` では、未適用の `List` を表す(束縛子 0 個、カインド `[_] Type`)。
   `type instance[A: Eq] Eq[List[_]]` では、`List[A]` を表す(束縛子 1 個、カインド `Type`)。
   対象の型のカインドは、型構成子を束縛子の個数だけ適用した後のカインドである。
   2 つの例は、この 1 つの規則で束縛子が最も少ない場合と最も多い場合である。
   束縛子の個数は、`_` の個数を超えられない。
   対応しなかった右側の `_` が未適用のまま残ることも、仕様が規則として書いている。
   `Eq[List[_]]` と `Functor[List[_]]` の 2 つの例も、仕様の同じ箇所にある(sample.kel:415-417)。

   `_` の個数そのものは、型構成子が取る型引数の個数と一致していなければならない(sample.kel:412)。
   この検査がないと、`Functor[List[_, _, _]]` も、穴のない `Functor[List]` も受理してしまう。
   カインド表にある型構成子では、`con_kind` が引数 `holes` を使わないからである。

   インスタンス表のキーは(クラス, 先頭の型構成子)の組で、前提はキーに入らない。
   インスタンスの探索は、表を 1 回引くだけである。
   重なり合うインスタンスは存在しないので、
   コヒーレンスは「同じキーを 2 度登録したらエラー」という 1 つの規則で保証できる(sample.kel:357)。
   組み込みのインスタンスと同じキーのユーザの宣言は、
   1 度目の宣言でも、標準環境のインスタンスの再宣言として拒否する(§6.9)。

   対象の型のカインドは、クラスパラメータのカインドと一致していなければならない(sample.kel:401)。
   `Functor` は `[_] Type` のクラスなので、`Functor[Int32]` はこの検査でエラーになる。
   束縛子があるときは、束縛子のカインドも、
   型構成子がその位置に要求するカインドと一致していなければならない(sample.kel:418)。
   たとえば `[F[_]: C]` を `List[_]` の穴には対応させられない。

   行カインドのパラメータを持つ型も、この検査でエラーになる。
   `newtype Callback[E]` の `Callback` のカインドは `EffectRow -> Type` なので、
   `Functor[F[_]]` が要求する `Type -> Type` と一致しない。
   そのため、`type instance Functor[Callback[_]]` は宣言の時点でエラーになる(`test/kinds.t` の nofunctor)。
   sample.kel §8 は、構造的導出を持つ `Eq` のパラメータのカインドが Type であること(sample.kel:398-400)に続けて、
   これを同じカインドの規則から導かれることとして書いている(sample.kel:401-403)。
   仕様の文の主語は「インスタンスの対象の型のカインド」で、
   対象の型のカインドをクラスパラメータのカインドと比べる検査
   (`register_instance` の `same_kind`)がこれに相当する。
   ユーザから見えるのは `Callback` を `Functor` にできないという制限だけだが、
   仕様がこれを書いているので、この制限は実装の都合ではなく言語の規則である。 *)

let instance_head (i : T.instance_decl') =
  let cls = Decls.resolve_class (intern i.T.ins_class) in
  let head =
    match i.T.ins_args with
    | [ h ] -> h
    | _ -> type_error "type instance の型引数は1個です(D11)"
  in
  let con, holes =
    (* 修飾名 M.T も受理する。受理しないと、module の外からその pub の型にインスタンスを
       書く手段がない。可視性も、型注釈と同じように検査する。検査しないと、名前を書くことも
       許されない pub でない型に、module の外からインスタンスを宣言できる。すると、
       module の外の宣言がそのキーを使い、module 自身は同じインスタンスを宣言できなくなる。
       型名を oid に解決する経路は、どれも同じ可視性の検査を行う *)
    match snd head with
    | T.EIdent (LongId comps) -> (Decls.resolve_con (intern (String.concat "." comps)), 0)
    | T.EApply ((_, T.EIdent (LongId comps)), args) ->
        List.iter (fun (a : T.type_exp) -> match snd a with T.EHole -> () | _ -> type_error "インスタンス頭の型引数は _ だけです(List[_] の形)") args;
        (Decls.resolve_con (intern (String.concat "." comps)), List.length args)
    | _ -> type_error "インスタンス頭は 型構成子 か 型構成子[_, ...] の形で書いてください"
  in
  Decls.check_con_visible con;
  (* 対象の型に書いた _ の個数は、型構成子が取る型引数の個数と一致していなければならない。
     これを検査しないと、Functor[List[_, _, _]] が型検査に通る *)
  let rec kind_arity k = match kind_repr k with KArrow (_, r) -> 1 + kind_arity r | _ -> 0 in
  let arity = kind_arity (Decls.con_kind con holes) in
  if holes <> arity then
    type_error
      ("インスタンス頭 " ^ display_of con ^ " は型引数を " ^ string_of_int arity ^ " 個取りますが、_ が "
     ^ string_of_int holes ^ " 個書かれています");
  (* 前提の束縛子は、対象の型の _ に左から順に対応する。対応しなかった _ は未適用のまま残り、
     カインドの矢印になる(Functor[List[_]] は、束縛子が 0 個でこの形になる) *)
  let np = List.length i.T.ins_tparams in
  if np > holes then
    type_error
      ("インスタンスの型パラメータが " ^ string_of_int np ^ " 個ありますが、頭 " ^ display_of con ^ " の _ は "
     ^ string_of_int holes ^ " 個です");
  (cls, con, holes)

(* ## 11.35 インスタンスの登録

   パス 1c では、インスタンスの対象の型と、束縛子から作った前提をインスタンス表に登録し、
   本体に書いたメソッド名をクラスの宣言と比べる。
   本体の検査はパス 2 で行う(§11.38)。
   本体の推論には、値環境がそろっている必要があるからである。
   前提は、`class_names_of` で(引数位置, クラス)の組にする。
   `class_names_of` が未知のクラスと予約述語を拒否するので、
   束縛子に書いた制約にも同じ検査が適用される(`test/premise.t` の pr8 / pr9)。
   第8章 §8.4 の `TCon` の分岐は、インスタンス表に登録したこの前提を使う。

   メソッド名は 2 つの方向で検査する。
   クラスが宣言していないメソッドを書いていないこと(余分)と、
   クラスのメソッドをすべて書いていること(網羅)である。
   片方だけでは足りない。
   余分を許すと、名前の書き間違いが診断のないまま無視される。
   網羅を検査しないと、実行時にメソッドが見つからない。

   インスタンス本体に書けるのは、`let` と `let rec` だけである。
   `Functor[List[_]]` の `map` は自分自身を再帰呼び出しするので、
   `let rec` が必要である(sample.kel:443-446)。

   インスタンスは、クラスか型構成子を宣言したファイルにだけ書ける(孤児規則。sample.kel:358)。
   クラスと型構成子を宣言した単位は、第6章の `entity_unit` が返す。
   `entity_unit` は、内部名に単位の接頭辞があればその単位を返し、
   接頭辞がなければ、標準環境の宣言には標準環境を、それ以外には起点を返す。
   クラスも型構成子も標準環境が宣言したものであるインスタンスは、標準環境だけが宣言できる。
   同じ組がすでにインスタンス表にあるときは、孤児規則を検査せず、
   重複の診断(第6章の `add_instance`)に任せる。
   重複のほうが原因に近いからである。 *)

let register_instance (i : T.instance_decl') =
  let cls, con, holes = instance_head i in
  (* 予約述語は、宣言のクラス名を取り出した時点で拒否する。add_instance にも同じ検査が
     あるが、add_instance を呼ぶのは未知の型構成子、カインド、メソッドの網羅の検査より
     後なので、宣言の書き方によっては、予約述語とは別の理由のエラーが先に出てしまう *)
  (if Decls.reserved_predicate cls then
     type_error (i.T.ins_class ^ " は予約されたリテラル述語です(インスタンスは宣言できません、D8)"));
  let ci = match Decls.find_class cls with Some ci -> ci | None -> type_error ("未知のクラス: " ^ i.T.ins_class) in
  if not (Hashtbl.mem Decls.con_kinds con) then type_error ("未知の型構成子: " ^ display_of con);
  (* 対象の型のカインドは、型構成子を束縛子の個数だけ適用した後のカインドである。
     このカインドを求めながら、束縛子のカインドが、型構成子がその位置に要求する
     カインドと一致することも検査する([F[_]: C] を List[_] の穴には対応させられない) *)
  let rec head_kind k tps =
    match tps with
    | [] -> k
    | tp :: rest -> (
        match kind_repr k with
        | KArrow (a, r) ->
            let kb = if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var () in
            if not (same_kind a kb) then
              type_error
                ("インスタンスの型パラメータ " ^ tp.tp_name ^ " のカインドが頭 " ^ display_of con ^ " の引数と一致しません");
            head_kind r rest
        | _ -> bug "instance: 束縛子が頭のアリティを超えています(D96 の検査が先に落とすはず)")
  in
  if not (same_kind ci.Decls.ci_param_kind (head_kind (Decls.con_kind con holes) i.T.ins_tparams)) then
    type_error
      ("インスタンス頭 " ^ display_of con ^ " のカインドがクラス " ^ i.T.ins_class ^ " のパラメータと一致しません");
  (* 前提は(引数位置, クラス)の組である。束縛子 i は対象の型の引数位置 i に対応するので、
     束縛子の番号をそのまま引数位置に使う。class_names_of が未知のクラスと予約述語を
     拒否するので、束縛子に書いた制約にも同じ検査が適用される *)
  let premises =
    List.concat (List.mapi (fun i tp -> List.map (fun c -> (i, c)) (class_names_of tp)) i.T.ins_tparams)
  in
  let methods =
    List.concat_map
      (fun ((_, d) : T.decl) ->
        let name_of_b ((_, b) as bnode : T.let_binding) =
          match binding_name b with
          | Some x -> (intern x, bnode)
          | None -> type_error "インスタンス本体の let は名前束縛でなければなりません"
        in
        match d with
        | T.DLet bnode -> [ name_of_b bnode ]
        | T.DLetRec bs -> List.map name_of_b bs
        | _ -> type_error "インスタンス本体には let(と let rec)だけが書けます")
      i.T.ins_body
  in
  (* 余分なメソッドがないことと、クラスのメソッドをすべて書いていることを検査する *)
  List.iter
    (fun (m, _) ->
      if not (List.exists (fun (m2, _) -> intern m2 = m) ci.Decls.ci_methods) then
        type_error ("クラス " ^ i.T.ins_class ^ " にメソッド " ^ display_of m ^ " はありません"))
    methods;
  List.iter
    (fun (m, _) ->
      if not (List.mem_assoc (intern m) methods) then
        type_error ("インスタンスがメソッドを網羅していません: " ^ m ^ " が漏れています"))
    ci.Decls.ci_methods;
  (* 孤児規則を検査する。インスタンスは、クラスか型構成子を宣言したファイルにだけ書ける。
     クラスも型構成子も標準環境が宣言したものであるインスタンスは、標準環境だけが宣言できる *)
  (* 同じ組がすでに表にあれば、重複の診断(add_instance)のほうが原因に近いので、そちらに任せる *)
  (if (not !Decls.in_prelude) && Decls.find_instance ~cls ~con = None then
     let cur = !Decls.current_unit in
     if Decls.entity_unit cls <> cur && Decls.entity_unit con <> cur then
       let c = display_of cls and t = display_of con in
       type_error (c ^ "[" ^ t ^ "] のインスタンスは、" ^ c ^ " か " ^ t ^ " を宣言したファイルにだけ書けます"));
  Decls.add_instance ~builtin:false ~cls ~con premises

(* ## 11.36 前方参照できる束縛の条件

   パス 1c は、注釈が完全な `let` のシグネチャを登録する。
   このシグネチャは前方参照のために使う。
   sample.kel:458 の `user_names` が、後ろで定義される `println`(:510)を呼べるのは、
   このシグネチャがあるからである。

   「完全」をどう定義するかで、前方参照の健全性が決まる。
   本体を調べずに作るシグネチャは、決まっていない部分を含んではならない。
   注釈の先頭の矢印で `@` を省略すると、束縛自身の行は本体からしか決まらない。
   本体を推論するときは、この行が呼び出し元の `eff` と単一化される。
   しかし、本体を調べずにシグネチャだけを作ると、
   この行は何とも単一化されない行変数のまま一般化される。
   するとその関数はどんなエフェクトでも起こしてよいことになり、
   エフェクトの検査に通るかどうかが宣言順で変わる。
   前方参照した呼び出しは型検査に通り、同じ呼び出しを定義の後ろに書くとエラーになる。

   入れ子の矢印で省略した `@` は、`@ {}` に決まる(sample.kel §9)。
   この行は本体を調べなくても決まっているので、シグネチャを作る妨げにならない。
   決まらずに残るのは束縛自身の行だけなので、条件は次のようになる。

   前方参照のシグネチャを作るのは、注釈の**先頭の矢印**で `@` を省略していない束縛か、
   `pub` の束縛だけである。
   関数束縛では、束縛自身の `@` を書いているか、束縛が `pub` であることを要求する。
   値束縛では、注釈の先頭が矢印なら、その `@` を書いているか、束縛が `pub` であることを要求する。
   どちらも、引数と返り値に型注釈があることが前提である(§11.37)。

   判定は `signature_of_binding`(§11.37)の `full` が行う。
   関数束縛では束縛自身の `@`(`lb_eff`)を調べ、
   値束縛では注釈の先頭の矢印を `head_effected` で調べる。
   どちらも入れ子の矢印は調べないので、
   `let helper[E](f: () => Unit @ E, g: (Int32) => Int32): Int32 @ {Console extends E}` は、
   `g` の `@` を省略していてもシグネチャを作れる(`test/typecheck_m6.t` の fwdsig)。
   入れ子の矢印にまで `@` を要求すると、
   この 1 つの省略だけで前方参照が `未束縛の変数: helper` というエラーになり、
   受理するかどうかが宣言順に依存する。
   注釈の中のすべての矢印に `@` を要求する `unwritten_effect` は、
   pub の完全注釈検査(§11.31)が使う。

   値束縛でも、`pub` なら、`@` を省略した注釈からシグネチャを作る。
   `pub` で省略した `@` の意味は `@ {}`(本体は純粋)に決まっているので、
   関数束縛と同じ理由で、本体を調べずにシグネチャを作れる。
   これを認めないと、`pub let k: (Int32) => Int32` を前方参照した呼び出しだけが、
   `未束縛の変数` というエラーになり、受理するかどうかが宣言順に依存する。
   注釈の先頭の矢印で `@` を省略した、`pub` でない値束縛には、シグネチャを作らない。
   行が本体からしか決まらないので、この形は前方参照できない。
   前方参照を許すには、本体を調べる必要がある。

   もう 1 つの規則として、同じ名前では先に宣言したほうを優先する。
   1c は、環境にまだない名前についてだけシグネチャを登録する。
   同名の `let` が 2 つあれば、1 つ目のシグネチャだけが前方参照に使われる。
   プレリュードの束縛やクラスメソッドと同名の `let` にはシグネチャを登録せず、
   その名前の前方参照は、すでにある宣言の型で検査する。
   前方参照する関数は、最初にその名前を持った宣言を参照する。
   評価器は、型検査が書いた参照先の宣言で値を引く(第14章 §14.4)ので、実行も同じ宣言を使う
   (`test/resolved_names.t` の前方参照と再束縛のブロック)。 *)

(* ## 11.37 シグネチャの構築

   条件を満たした束縛について、本体を調べずに型を組み立てる。
   型パラメータをスコーレム定数にし、注釈を精緻化し、一般化してからスコーレム定数を解放する。
   スコーレム定数の扱いは、§11.25 の 3 つの段階と同じである。

   関数束縛では、引数パターンがすべて `PAnnot`(注釈付き)であることも要求する。
   注釈のない引数があれば、その型は本体からしか分からない。

   `signature_of_binding` は、精緻化が投げた型エラーと未実装の例外を黙って捨てて `None` を返す。
   このパスの目的は、登録できるシグネチャを登録することで、エラーを報告することではない。
   ここでエラーになる型注釈は、パス 2 で本体を推論するときにもう一度精緻化され、
   そのときに、本体の検査の文脈でエラーとして報告される。
   1c で先に報告すると、エラーを報告する位置が宣言順に依存する。

   例外を捨てる節には `Type_error_at` も並べる。
   位置付きの例外だけを捕捉しないでおくと、
   1c が黙って捨てるはずの注釈のエラーを 1c の時点で報告してしまい、
   位置付きのエラーに限って、報告する位置が宣言順に依存する。
   この誤りは、`test/errloc.t` の sig.kel が検出する。

   シグネチャの型は、パス 2 で本体を検査した束縛の型と同じ規則で作る。
   `pub` で省略した最も外側の `@` は、関数束縛でも値束縛でも閉じた空の行 `TRowEmpty` にする。
   パス 2 の型も同じ閉じた行なので、前方参照と後方参照は同じ型を使う。
   シグネチャの行だけを行変数にすると、前方参照した使用だけが型検査に通り、
   受理するかどうかが宣言順に依存する。 *)

let signature_of_binding env (b : T.let_binding') : ty option =
  let params_annotated =
    match b.T.lb_params with
    | None -> true
    | Some ps -> List.for_all (fun (_, p) -> match p with T.PAnnot _ -> true | _ -> false) ps
  in
  (* 注釈の先頭の矢印にだけ @ を要求する(§11.36)。入れ子の矢印で省略した @ は @ {} に
     決まるので、本体を調べなくても決まっている。決まらずに残るのは束縛自身の行だけなので、
     関数束縛には lb_eff を、値束縛には注釈の先頭が矢印ならその @ を要求する。
     どちらも pub なら省略してよい。pub で省略した @ の意味は @ {} に決まっているからである *)
  let head_effected ((_, te) : T.type_exp) = match te with T.EArrow (_, _, eff) -> eff <> None | _ -> true in
  let full =
    params_annotated && b.T.lb_ret <> None
    && (match b.T.lb_params with
       | Some _ -> b.T.lb_eff <> None || b.T.lb_pub
       | None -> ( match b.T.lb_ret with Some t -> head_effected t || b.T.lb_pub | None -> false))
  in
  if not full then None
  else
    try
      let lvl = 1 in
      let rigids = make_rigids lvl b.T.lb_tparams in
      let env_ty = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types rigids } in
      let ty =
        match b.T.lb_params with
        | Some ps ->
            let param_tys =
              List.map
                (fun (_, p) -> match p with T.PAnnot (_, te) -> elab_value_type env_ty lvl "型注釈" te | _ -> assert false)
                ps
            in
            (* pub で省略した @ は @ {} *)
            let fn_eff = match b.T.lb_eff with Some e -> elab_eff env_ty lvl e | None -> TRowEmpty in
            let ret_ty = match b.T.lb_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> assert false in
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None -> (
            (* 1c のシグネチャも、パス 2 と同じ規則で作る(§11.37)。規則が違うと、前方参照が
               あるかどうかで値束縛の型が変わる。値の型を書く位置のカインドの検査(§11.3)も行う *)
            match b.T.lb_ret with
            | Some t -> (
                let ty = elab_value_type_outer env_ty lvl "型注釈" t in
                match (snd t, repr ty) with
                | T.EArrow (_, _, None), TArrow (a, r, _) when b.T.lb_pub -> TArrow (a, r, TRowEmpty) (* pub で省略した @ は @ {} *)
                | _ -> ty)
            | None -> assert false)
      in
      Unify.generalize 0 ty;
      release_rigids rigids;
      Some ty
    with Type_error _ | Type_error_at _ | NotImplemented _ | NotImplemented_at _ -> None

(* ## 11.38 インスタンス本体の検査

   ### 実装の行

   実装の最も外側の行が閉じていれば、使用時に行を開く規則(§11.26)と同じく、
   行の末尾を開いてから宣言の行と単一化する。
   宣言の行 `{Print, Console}` に含まれる `Print` だけを起こす実装を、
   閉じた行の注釈で書けるようにするためである。
   空の行の実装は、宣言の行と単一化せずに受理する。
   その理由は、包摂の説明の中で、最も外側の行の扱いとして述べる。

   ### 前提とメソッド自身の辞書

   インスタンスの前提は、束縛子のスコーレム定数の制約として本体から見える。
   本体の穴のうち、
   型が束縛子のスコーレム定数であるものは、
   インスタンスの終わりに前提の辞書パラメータ(`DInstance`)で解く。
   メソッドの実装の束縛には `DMethod (own, mk, adapter)` を書く。
   `own` は、実装を推論した型の辞書パラメータである。
   `mk` は、クラス宣言がメソッドの型に付けた制約から、
   クラスパラメータへの制約を除いたもののキーである。
   `adapter` は、包摂で実装の型を具体化したときの穴で、実装に `own` の辞書を渡す証拠になる。
   評価器はメソッドを選ぶたびに、前提と `mk` の辞書を束縛した環境で実装の束縛を評価する(第14章)。

   インスタンスのメソッド本体が、クラス宣言の型を満たしているかを検査する。
   期待型は、クラス宣言のメソッドの型に、インスタンスの対象の型を代入したものである。
   `Functor` の `map : (F[A], (A) => B @ E) => F[B] @ E` に `F := List` を代入すると、
   `(List[A], (A) => B @ E) => List[B] @ E` になる。
   代入は、`map_generics_with` のメモ表に項目を 1 つ入れておくだけで済む。
   `F[A]` は、`tapp` の正規化が `List[A]` にする(第1章)。

   検査は単一化ではなく**包摂**である。
   次の表のとおり、推論した型と期待型とで、型変数の扱いが逆になる。

   | 側 | 操作 | 意図 |
   |---|---|---|
   | 推論した型 | `instantiate_ev` | どんな型にでもなれるので、単一化変数にする。制約ごとの穴が、実装に辞書を渡す証拠になる |
   | 期待型 | スコーレム定数への置き換え(`map_generics_with`) | どの型でも検査に通らなければならないので、スコーレム定数にする |

   そのうえで単一化する。
   推論した型が期待型と同じか、期待型より多相であれば、単一化は成功する。
   多相さが足りなければ、スコーレム定数に具体型を代入しようとしてエラーになる。
   これが、実装は宣言と同じか、それより一般的でなければならない、という検査である。
   両方を単一化変数にすると、一致する具体型が 1 つあるだけで検査に通ってしまう。
   両方をスコーレム定数にすると、どの実装も検査に通らない。

   最も外側の行だけは、表の 2 つの操作とは別に扱う。
   引数と返り値を先に単一化し、その後で実装の最も外側の行を調べる。
   実装の行が空なら、宣言の行とは単一化せずに受理する。
   空の行は行の最小元である。
   純粋な実装は、宣言の行がどの行であっても、その行の文脈で呼んでよい。
   宣言の行が閉じた空の行(最も外側の `@` を省略したユーザのメソッドと、
   組み込みのクラスのメソッド。§11.33、第6章 §6.10)なら、
   空の実装の行は単一化してもそのまま一致する。
   単一化しないことで結果が変わるのは、宣言の行が空でないときである。
   宣言の行が行変数のスコーレム定数(`@ E` と書いたメソッド)なら、
   空の実装の行と単一化すると、スコーレム定数に空の行を代入しようとしてエラーになる。
   宣言が `@ Print` のようにラベルを書いていれば、閉じた行どうしのラベルの不一致でエラーになる。

   引数と返り値を先に単一化するのは、メソッドの引数に `@` を省略した矢印があると、
   引数の単一化で実装の行が `{}` に決まるからである(入れ子の矢印で省略した `@` は `@ {}` を意味する)。
   行が `{}` に決まったことは、本体が何も起こさないことを示すので、
   宣言の行と単一化せずに受理しても検査は健全である。
   空の行をこう扱わないと、`@ E` と行変数を書いたメソッドの引数の矢印で `@` を省略したとき、
   そのメソッドは、宣言できるのに実装できないものになる。
   sample.kel §9 は、型クラスのメソッドの最も外側の `@` の省略を `@ {}` と読み、
   インスタンスの実装が純粋でなければならないと定める(sample.kel:437-438)。
   宣言の行がスコーレム定数でも純粋な実装を受理するこの扱いは、同じ規則を包摂の側で補っている。

   引数と返り値を単一化した後の実装の行が、まだ何にも決まっていない行変数のこともある。
   値でない初期化式の値束縛は一般化しないので、
   初期化式が返す無名関数の行は、外側のレベルの行変数のまま包摂に渡される。
   この行変数を宣言のスコーレム定数と単一化すると、
   スコーレム定数がスコープの外に漏れるというエラーになる。
   そこで、この行変数は空の行に決めてから、空の行の扱いに進む。
   空の行は行の最小元なので、こう決めた実装は、宣言の行がどの行であってもその行の文脈で呼べる。

   インスタンスの本体の束縛は、新しい行変数をその位置の行として推論し、
   包摂の後で、その行を、初期化式に許される行と比べる。
   初期化式の行を推論の前に閉じた行に決めると、エフェクト多相な関数を初期化式で呼んだとき、
   その関数の行変数が初期化式の行に決まり、初期化式が返す関数の行にもその行が入る。
   すると、
   何もエフェクトを起こさない実装が、純粋性の検査でエラーになることがある。
   推論の後で比べれば、返す関数と共有している行変数は、
   包摂が実装の行を空の行に決めるときに空の行になる。
   比べるラベルがないので、この形はエラーにならない。
   宣言の実行で 1 回だけ評価する初期化式に許される行は、トップレベルの行である。
   この評価は、トップレベルの初期化に含まれるからである(LangSpec §13.7、§15.4)。
   前提付きインスタンスの初期化式と、制約を持つメソッドの初期化式は、
   メソッドを使うたびに評価するので、
   許される行は空の行である(LangSpec §6.4)。
   制約を持つメソッドでは、値でない初期化式は一般化しないので、
   その型のうちメソッドの型パラメータの位置は、外側のレベルの型変数か、
   宣言の側のスコーレム定数とは別の型になる。
   どちらもそのスコーレム定数とは単一化できないので、この初期化式は、
   行を比べる前の包摂でエラーになる。
   制約を持つメソッドで行を比べる段階まで進むのは値の初期化式だけで、
   値の評価はエフェクトを起こさない。
   そのため、この場合に許される行を空の行にしても、
   受理するかどうかは変わらない。
   許される行にないエフェクトは、そのエフェクトの名前を挙げる型エラーにする。
   エラーの位置は、そのエフェクトを起こした式ではなく、メソッドの束縛を指す。

   実装が純粋でなければ、包摂は失敗する。
   最も外側の行の単一化で失敗したときは、診断に純粋性の規則を明記する。

   ```
   型エラー: 型クラスのメソッドの実装は純粋でなければなりません(宣言の最外の行にラベルがありません — 仕様 §9)。
   インスタンスメソッド size の本体がエフェクトを起こしています。元の報告: (単一化の報告)
   ```

   規則を明記するかどうかは、宣言の側の行を調べて決める。
   宣言の行がラベルを持たない(行変数だけの行か、閉じた空の行である)なら、
   宣言が述べているのは、純粋であることか、どの行にもなれることだけである。
   そのため、失敗の理由は、実装が何かのエフェクトを起こしたことに限られる。
   最も外側の `@` を省略した形(clsimpure。宣言の行は閉じた空の行)でも、
   メソッドの型パラメータに行変数を取って `@ E` と書いた形(clsbarerow)でも、規則を明記する。
   宣言が `@ Print` のようにラベルを書いていれば、
   失敗の原因はそのラベルと実装が起こしたラベルの不一致で、純粋性の問題ではない。
   そのときは `クラス宣言の型を満たしません` というメッセージのエラーにする(clsmismatch)。
   失敗の原因が行にあるかどうかは、`pub` の言い換え(§11.12)と共通の `row_failure` で判定する。

   メッセージをこのように使い分けるために、`subsume` は最も外側の行の単一化だけを別の `try` で囲む。
   引数と返り値の単一化の失敗は、`wrap` が `クラス宣言の型を満たしません` というメッセージにする。
   `pub` の規則の検査は、本体の行を専用のセルにして一覧に記録するが(§11.26)、
   ここでは専用のセルを使わない。
   規則を明記するかどうかの判定に必要なのは宣言の側の行 `se` だけで、
   包摂のこの 1 か所でそれが手に入るからである。
   専用のセルの一覧を増やせば、そのぶん、
   プログラムの初期化(§11.41)で一覧を空にし忘れる危険も増える。

   規則を明記するかどうかは宣言の側の行だけで決まる。
   一方、メッセージの後半の、何が空でない行を作ったかを述べる部分は、実装の側の束縛を調べて決める。
   実装が最も外側の `@` を自分で書いていれば(`outer_eff_written` が真なら)、
   空でない行はその注釈が原因である。
   実装が自分の注釈に `@ Print` と書き、その本体は何も起こしていないときも、包摂は失敗する。
   そこで、このときは `本体がエフェクトを起こしています` ではなく
   `注釈に @ {} 以外の行を書いています` と述べる(clsannotrow)。
   本体が実際に `Print` を起こしている関数束縛でも、先に注釈のほうを述べてよい。
   注釈を取り除けば本体の行が残り、次は本体を指すメッセージになるからである。
   注釈に書いたのが行変数 `@ F` で、その行変数が、引数の型を通して宣言の行変数と単一化されたために
   空にならない形も、このメッセージで述べる。
   `@ F` を `@ {}` に書き換えると、本体の行は空の行に決まる。
   そのため、宣言の行変数を行に持つ引数を `g` とすると、本体が `g()` を呼ぶ形は、
   引数の行が本体の行に入るので、書き換えた注釈では束縛の検査がエラーになる。
   呼び出されない無名関数の中に `g()` を書くだけの形は、
   引数の行が本体の行に入らないので、型検査に通る。
   先頭に型エイリアスを書いた値束縛の注釈では、
   `outer_eff_written` は `@` を書いたものと判定する。
   そのため、エイリアスの中の `@ Print` も、注釈に書いた行として述べる(clsannotalias)。
   関数束縛が最も外側の `@` を書いていなければ、実装の行は本体から推論したものなので、
   空でない行は、本体が何かのエフェクトを起こしたことを意味する。
   値束縛が最も外側の `@` を書いていなければ、実装の行は初期化式の値の型で決まる。
   `let size = sizeP` のように、`@ Print` と注釈した関数を名前で渡すだけでも行は空でなくなるが、
   このとき本体は何も起こしていない。
   そこで、この形は `初期化式の値の型の最外の行が空ではありません` と述べる(clsvalrow)。

   純粋性の規則を明記できない形もある。
   メソッドが `(T, () => Unit @ E) => Unit @ E` のように関数を引数に取り、
   実装の本体がその引数を呼び出すと、本体の行が引数の行と単一化される。
   すると、
   先に行う引数の単一化のほうが失敗し、`wrap` のメッセージになる(clsargcall)。
   本体が引数を呼び出さなければ、最も外側の行の単一化まで進む(clsargpure)。
   同じ宣言でも実装によってメッセージが変わるが、エラーになること自体はどちらも同じである。

   宣言の行がラベルを持たないかどうかの判定は、
   期待型の `Generic` をスコーレム定数に置き換えた後の行の形に依存している。
   最も外側の `@` を省略したユーザのメソッドの行は、
   登録のときに `TRowEmpty` に置き換えるので(§11.33)、
   閉じた空の行のまま包摂に渡される。
   組み込みのクラスのメソッドの行も、登録の時点から `TRowEmpty` である(第6章 §6.12)。
   `@ E` と書いたメソッドの行は、`generalize` が `Generic` にした行変数である。
   スコーレム定数への置き換えがこれを `Rigid` にするので、行変数だけの行として包摂に渡される。
   この経路のどこかが変わると、規則の明記がエラーを出さずに働かなくなる。
   clsimpure と clsbarerow がこの変化を検出する。

   前提付きインスタンスでは、対象の型は、型構成子を束縛子に適用した形になる。
   `type instance[A: Eq] Eq[List[_]]` の対象の型は `List[A]` で、
   `A` は `make_rigids` が作るスコーレム定数である。
   このスコーレム定数の `vcls` には、前提の `Eq` が入っている。
   この前提がないと、包摂は本体を推論した型の中の変数(`Eq` 制約の付いた弱い変数)を
   このスコーレム定数に束縛しようとして、§8.4 の `Rigid` の分岐でエラーになる。
   その結果、正しい実装が `[A: Eq] のように制約を書いてください` というエラーで拒否される。
   スコーレム定数への置き換えは `Generic` だけを置き換えるので、対象の型の `Rigid` はそのまま残る。
   前提は、期待型の中のスコーレム定数が持つ制約として残る。
   `expected_of` には、前提付きインスタンスのための処理がない。
   `tapp` の正規化が `F[A]` を `List[A]` にするからである。
   `subsume` は、前提のキーをメソッド自身の制約のキーと合わせて辞書パラメータとして扱い、
   包摂で作った穴を解く(§11.29)。
   束縛子の名前は本体の型のスコープにも入るので、
   メソッドに `xs: List[A]` と注釈を書ける(sample.kel:419-420)。
   メソッド自身の型パラメータが同名なら、メソッドの型パラメータが束縛子を隠す。
   内側の名前を優先することも、仕様の同じ箇所(sample.kel:419-420)に書かれている。

   本体は、通常の束縛と同じ `elab_binding` / `elab_rec_bindings` で推論する。
   そのため、注釈付きのメソッドも `let rec` のメソッドも同じ経路で検査できる(sample.kel:443-446)。

   推論には、宣言の型の引数の型を、仮引数の型として渡す(`expected_params_of`)。
   渡すのは、宣言の引数の行が `_item` だけの閉じた行で、仮引数の個数がそれと同じときである。
   関数束縛と `let rec` の関数束縛では、型注釈のない変数と `_` の仮引数にその型を使い、
   それ以外の仮引数(注釈のある仮引数など)には新しい型変数を使う。
   `let` の注釈のない値束縛では、初期化式が無名関数で、
   その仮引数がすべて型注釈のない変数か `_` のとき、
   引数の型を持つ矢印を期待型にして `elab_check` で検査する。
   `let rec` の値束縛では、`elab_rec_bindings` の値束縛の分岐が `expected_params` を使わないので、
   無名関数の仮引数の型は本体から推論する。
   渡す型では、メソッド自身の型パラメータと行変数を制約のない新しい変数に置き換え、
   束縛子のスコーレム定数(前提付きインスタンスの束縛子から作ったもの)はそのまま残す。
   新しい変数に置き換えた位置の型は本体から推論し、後の包摂で宣言と比べる。
   こうして、型を渡した仮引数の型は、仮引数に宣言の型を注釈した関数と同じになり、
   本体の数値リテラルの既定化と、
   網羅性検査の遅延キューの処理(`Exhaust.drain`。§11.28)は、その型を使う。

   返り値の型と最も外側の行は渡さない。
   返り値の型を渡すと、返り値の型の不一致が本体の単一化で先にエラーになり、
   `クラス宣言の型を満たしません` への言い換えが行われない形ができる。
   最も外側の行を渡さないのは、純粋性の規則を明記する包摂の言い換えと、
   包摂の後に行う初期化式の行の検査を、推論の後で行うためである。 *)

let check_instance_bodies env eff0 inode (i : T.instance_decl') =
  let cls, con, _holes = instance_head i in
  let ci = match Decls.find_class cls with Some ci -> ci | None -> bug "instance: class 未登録" in
  let imark = Unify.hole_mark () in
  (* 前提付きインスタンスの対象の型は、型構成子を束縛子に適用した形である。
     束縛子はスコーレム定数にし、前提をその vcls に入れる。
     束縛子が 0 個なら、対象の型は TCon (con, []) である。
     束縛子の名前は、本体の型のスコープに入る *)
  let head_rigids = make_rigids 1 i.T.ins_tparams in
  let head_ty = TCon (con, List.map (fun (_, t, _) -> t) head_rigids) in
  (* 前提の辞書パラメータのキーを求める。
     順序はインスタンス表の ii_premises と同じで、束縛子の順に、束縛子ごとに制約の順で並べる *)
  let pk =
    List.concat_map
      (fun (_, _, r) ->
        let i = Unify.var_info_of r in
        List.filter_map (fun c -> if Unify.is_predicate c then None else Some (i.vid, c)) i.vcls)
      head_rigids
  in
  Tree.set_dict inode (Tree.DInstance pk);
  let env = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types head_rigids } in
  let expected_of mname =
    match List.assoc_opt mname ci.Decls.ci_methods with
    | Some scheme ->
        let memo = Hashtbl.create 8 in
        Hashtbl.add memo ci.Decls.ci_param.vid head_ty;
        Unify.map_generics_with memo (fun info -> TVar (ref (Generic info))) scheme
    | None -> bug "instance: メソッドスキーマ未登録"
  in
  (* 宣言の引数の型から、仮引数の推論に渡す型を作る。
     メソッドの型パラメータと行変数は制約のない新しい変数に置き換え、
     束縛子のスコーレム定数はそのまま残す。
     引数の行が _item だけの閉じた行でなければ、何も渡さない *)
  let expected_params_of mname =
    match repr (expected_of mname) with
    | TArrow (p, _, _) -> (
        let memo = Hashtbl.create 8 in
        match repr (Unify.map_generics_with memo (fun i -> new_var ~kind:i.vkind 1) p) with
        | TRecord row -> (
            match row_fields row with
            | fields, tail when repr tail = TRowEmpty && List.for_all (fun (l, _) -> l = l_item) fields -> Some (List.map snd fields)
            | _ -> None)
        | _ -> None)
    | _ -> None
  in
  let subsume bnode mname inferred =
    let lvl = 1 in
    let expected = expected_of mname in
    (* 宣言の型の Generic をスコーレム定数に置き換え、
       クラスパラメータへの制約を除いた制約のキー mk を正準順で求める。
       実装の型は instantiate_ev で具体化する。
       そのときの穴 adapter は、実装に own の辞書を渡す証拠になる *)
    let smemo = Hashtbl.create 8 in
    let skol = Unify.map_generics_with smemo (fun i -> new_rigid ~kind:i.vkind ~classes:i.vcls lvl) expected in
    let mk =
      List.map
        (fun ((gi : var_info), c) ->
          match repr (Hashtbl.find smemo gi.vid) with TVar r -> ((Unify.var_info_of r).vid, c) | _ -> bug "instance: 剛定数ではありません")
        (Unify.constraints_of expected)
    in
    let amark = Unify.hole_mark () in
    let inf, adapter = Unify.instantiate_ev ~loc:(Tree.loc_of bnode) lvl inferred in
    let finish_adapter () =
      solve_holes_at ~since:amark ~params:(mk @ pk);
      let own = match Tree.get_dict bnode with Tree.DAbs ks -> ks | _ -> [] in
      Tree.set_dict bnode (Tree.DMethod (own, mk, adapter))
    in
    (* f を実行し、包摂の失敗(Type_error)を、
       クラス宣言の型を満たさないという既定のメッセージの型エラーに変える。
       引数と返り値の単一化は、この関数を通して行う。
       最も外側の行の単一化だけは、純粋性の規則を明記したメッセージを出すために、別の try で囲む *)
    let wrap f = try f () with Type_error msg -> type_error ("インスタンスメソッド " ^ mname ^ " がクラス宣言の型を満たしません(" ^ msg ^ ")") in
    (* 最も外側の行は最後に調べる。
       sample.kel §9 は、型クラスのメソッドの実装が純粋でなければならないと定める。
       引数と返り値を先に単一化し、その後で実装の行が空(純粋)なら、
       宣言の行と単一化せずに受理する。
       空の行は行の最小元なので、宣言の行がスコーレム定数(@ E と書いたメソッド)でも、
       純粋な実装はその行の文脈で呼んでよい。
       メソッドの引数に @ を省略した矢印があると、実装の行は {} に決まる。
       この扱いがないと、そのメソッドは、宣言できるのに実装できないものになる *)
    match (repr inf, repr skol) with
    | TArrow (ia, ir, ie), TArrow (sa, sr, se) ->
        (* 引数の行どうしを単一化する前に、矢印どうしの単一化と同じく引数の個数を比べる *)
        wrap (fun () -> Unify.check_arity inf skol ia sa);
        wrap (fun () -> Unify.unify ia sa);
        wrap (fun () -> Unify.unify ir sr);
        (* 実装の最も外側の行が空でない閉じた行なら、使用時に行を開く規則(§11.26)と同じく、
           行の末尾を開いてから宣言の行と単一化する。
           宣言の行にあるラベルの一部だけを起こす実装を、閉じた行の注釈で書けるようにするためである *)
        let ie = match repr (snd (row_fields ie)) with TRowEmpty when repr ie <> TRowEmpty -> row_append ie (new_row_var lvl) | _ -> ie in
        (* 実装の最も外側の行がまだ何にも決まっていない行変数なら、空の行に決める。
           一般化しない値束縛の初期化式が返す無名関数の行が、この形になる。
           空の行は行の最小元なので、こう決めた実装は宣言の行の文脈で呼べる。
           宣言の行がスコーレム定数のとき、外側のレベルの行変数をそのスコーレム定数と単一化すると、
           スコーレム定数がスコープの外に漏れるというエラーになる *)
        (match repr ie with TVar { contents = Unbound _ } -> Unify.unify ie TRowEmpty | _ -> ());
        (if repr ie = TRowEmpty then ()
        else
          (* 宣言の側の行がラベルを持たないときだけ、純粋性の規則を明記する。
             ラベルを持たない行は、閉じた空の行か、行変数だけの行である。
             メソッドの最も外側の @ を省略した形が前者になり、@ E と書いた形が後者になる。
             単一化の一般的なメッセージ `行 ς1 は注釈で固定された行変数なので` では、
             実装が純粋でなければならないという規則が読者に伝わらない。
             宣言が @ Console と書いていればラベルの不一致なので、
             クラス宣言の型を満たさないというメッセージのままにする *)
          let bare = match row_fields se with [], tail -> ( match repr tail with TVar _ | TRowEmpty -> true | _ -> false) | _ -> false in
          (* 実装が最も外側の @ を自分で書いていれば、空でない行はその注釈が原因で、
             本体が何も起こしていなくてもエラーになる。
             そのときは、本体ではなく注釈を原因として述べる。
             最も外側の @ を書いていない値束縛の行は、初期化式の値の型で決まるので、
             本体とも注釈とも述べない *)
          let culprit =
            let b = snd bnode in
            if outer_eff_written b then " の注釈に @ {} 以外の行を書いています。元の報告: "
            else
              match b.T.lb_params with
              | Some _ -> " の本体がエフェクトを起こしています。元の報告: "
              | None -> " の初期化式の値の型の最外の行が空ではありません。元の報告: "
          in
          (try Unify.unify ie se
           with Type_error msg ->
             if bare && row_failure msg then
               type_error
                 ("型クラスのメソッドの実装は純粋でなければなりません(宣言の最外の行にラベルがありません — 仕様 §9)。インスタンスメソッド " ^ mname
                ^ culprit ^ msg)
             else type_error ("インスタンスメソッド " ^ mname ^ " がクラス宣言の型を満たしません(" ^ msg ^ ")")));
        finish_adapter ()
    | _ ->
        wrap (fun () -> Unify.unify inf skol);
        finish_adapter ()
  in
  (* 初期化式が起こしたエフェクトの行 rho のラベルを、初期化式に許される行と比べる。
     包摂の後に呼ぶ。
     包摂は、決まっていない実装の行を空の行に決める。
     そのため、初期化式の行と、初期化式が返す関数の行が行変数を共有していても、
     ここには空の行として渡される。
     前提付きインスタンスの初期化式と、制約を持つメソッドの初期化式は、
     メソッドを使うたびに評価するので、許される行は空の行である。
     制約を持つメソッドの初期化式のうち、この検査に渡されるのは値の初期化式だけで、
     その行にラベルはない。
     それ以外の初期化式は宣言の実行で 1 回だけ評価するので、
     許される行はトップレベルの行 eff0 である *)
  let check_init_row bnode mname rho =
    let mk = match Tree.get_dict bnode with Tree.DMethod (_, mk, _) -> mk | _ -> [] in
    let per_use = pk <> [] || mk <> [] in
    let allowed = if per_use then TRowEmpty else eff0 in
    let top = List.map fst (fst (row_fields allowed)) in
    let extra = List.filter (fun (l, _) -> not (List.mem l top)) (fst (row_fields rho)) in
    (match extra with
     | [] -> ()
     | _ ->
         let names = String.concat "、" (List.map (fun (l, _) -> display_of l) extra) in
         if per_use then
           type_error
             ("エフェクト " ^ names ^ " をインスタンスメソッド " ^ mname
            ^ " の初期化式では実行できません(メソッドを使うたびに評価する初期化式は、エフェクトを起こせません)")
         else
           type_error
             ("エフェクト " ^ names ^ " をインスタンスメソッド " ^ mname
            ^ " の初期化式では実行できません(初期化式が起こせるのはトップレベルの評価と同じエフェクトです)"));
    (* ラベルを比べ終えた行の末尾は、空の行に決めて閉じる。
       許される行と単一化すると、let rec の再帰群で行を共有するとき、
       先に比べた束縛に許される行のラベルが、後の束縛の行に残る *)
    match repr (snd (row_fields rho)) with TVar _ as tail -> Unify.unify tail TRowEmpty | _ -> ()
  in
  List.iter
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DLet ((_, b) as bnode) ->
          let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
          let rho = new_row_var 0 in
          let env2 = elab_binding ?expected_params:(expected_params_of mname) env 0 rho bnode in
          (* 包摂のエラーの位置は、そのメソッドの束縛にする。
             インスタンス宣言の先頭にすると、複数のメソッドのどれが原因かを位置から判断できない *)
          at_node bnode (fun () -> subsume bnode mname (SMap.find mname env2.values));
          at_node bnode (fun () -> check_init_row bnode mname rho)
      | T.DLetRec bs ->
          let rho = new_row_var 0 in
          let env2 = elab_rec_bindings ~expected_params:expected_params_of env 0 rho bs in
          List.iter
            (fun (((_, b) as bnode) : T.let_binding) ->
              let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
              at_node bnode (fun () -> subsume bnode mname (SMap.find mname env2.values)))
            bs;
          List.iter
            (fun (((_, b) as bnode) : T.let_binding) ->
              let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
              at_node bnode (fun () -> check_init_row bnode mname rho))
            bs
      | _ -> type_error "インスタンス本体には let だけが書けます")
    i.T.ins_body;
  (* 本体の穴のうち、型が束縛子のスコーレム定数であるものは、前提の辞書パラメータで解く *)
  solve_holes_at ~since:imark ~params:pk;
  release_rigids head_rigids

(* ## 11.39 宣言の並びを 4 回走査する

   `process_decls` は、章の冒頭の表のパスを実装する。
   ここでは、パスをこの順序にした理由をコードに沿って述べる。

   **1a**：エイリアスと、newtype の名前とカインドと、effect の名前を登録する。
   型の本体を精緻化するには、本体に現れるすべての型構成子のカインドを引ける必要がある。
   そこで、名前とカインドだけを先に登録する。
   エフェクトラベルも同じで、型の本体に書いたラベルは、宣言表に名前があるかどうかだけを調べて読む。
   そこで effect は名前だけを先に登録し、操作は 1b で登録する。
   名前の重複と標準環境の名前の再宣言は、名前を登録するこの時点で拒否する。
   プレリュードにある名前の newtype は、ここで標準環境の名前の再宣言として拒否する。
   型構成子のカインドを登録する前に拒否するので、
   プレリュードの型のカインドがユーザの宣言で書き換わることはない。

   **1a の後処理**：newtype とエイリアスの本体を試しに精緻化する。
   章の冒頭の表で 1a′ と書いた処理である。
   1a が終わった直後に宣言の並びを走査し、newtype とエイリアスの本体を宣言順に試しに精緻化する。
   カインドの決まったパラメータの個数が増えなくなるまで、これを繰り返す(§11.31)。
   目的は、パラメータのカインドを宣言順に依存せずに決めることだけである。
   `speculate_newtype` と `speculate_alias` は、本体を `elab_type`
   (`EffectRow` のエイリアスでは `elab_eff`)で精緻化するだけで、結果は捨てる。
   1b の `register_newtype` と違って、コンストラクタを登録しない。
   `Decls.add_data` も `Unify.generalize` も `pub` の完全注釈検査も呼ばないので、
   残る副作用は、精緻化がカインドのセルを決めることだけである。
   試しに精緻化している間だけ、`speculating` を立てる。
   §11.5 の判別(`elab_con_args` と `expand_alias`)はこのフラグを調べ、
   型としても行としても読める表記(要素のない波括弧)を、
   カインドが決まっていないパラメータとの照合に使わない(§11.31)。

   エイリアスを 1b の前にも試しに精緻化するのは、
   newtype の本体からエイリアスへ具体的な行を渡す形(`MkN(Cb[{Print}])`)があるからである。
   1b の判別は、エイリアスのパラメータのカインドを調べる。

   どちらの試行も診断を捨てるが、`Panic` は捕捉しない。
   捕捉して捨てるのは、`with` 節に並べた 4 つの例外
   (`Type_error` / `Type_error_at` / `NotImplemented` / `NotImplemented_at`)だけである。
   newtype の試行は、例外をフィールドごとに捕捉して捨てる。
   エイリアスは本体が 1 つなので違いが出ないが、newtype で本体全体を 1 つの `try` で囲むと、
   1 つのフィールドで例外が発生したときに、
   後続のフィールドが決めるはずのカインドまで決まらなくなる(§11.31)。
   試行と既定化は、次の順に行う。
   newtype とエイリアスの試行(1a の後)、1b、
   エイリアスの 2 回目の試行(1b の後処理の 1 つ目のループ)、既定化(2 つ目のループ)である。

   1a の後の試行のループも `with_decl_module` で囲む。
   module の中の newtype のフィールドの型は、module の中の型を修飾なしで参照する。
   そのため、あるパスで囲み忘れると、そのパスだけがその型を未知の型として扱う。
   これを検出するテストは `test/kinds.t` の fwdrowmod2 で、module の中に深さ 2 の連鎖を置いている。
   fwdrowmod は、module の中の型を参照しない `B6` の試行だけでカインドが決まるので、
   `with_decl_module` を外しても通り、この検出には使えない。

   **1b**：コンストラクタ、操作、メソッドを登録する。
   型の本体を精緻化して宣言表に登録するのは、このパスである。
   1a とその後処理が終わっているので、カインドは宣言の順序に依存しない。
   newtype どうしが互いを参照しても、effect が後ろの newtype を使っても、
   型の本体に後ろの effect のラベルを書いても、型検査に通る。
   クラスのメソッドは、非修飾名(`map`)と修飾名(`Functor.map`)の両方で値の環境に登録する。
   どちらの名前でも書けるという仕様を、環境に 2 つ登録するという最も単純な方法で実現している。
   非修飾名は、同じ名前の束縛がすでに環境にあれば登録しない。

   1b の後処理として、宣言の並びをもう一度走査する小さなループを 2 つ実行する。
   2 つのループは、合わせて 4 つの処理を行う。
   1 つ目のループは、クラスのメソッドの制約の検査と、エイリアスの 2 回目の試行を行う。
   2 つ目のループは、カインドの既定化と、行を返すカインドの検査を行う。

   制約の検査は、クラスのメソッドの型パラメータの制約に、
   未知のクラスや予約述語がないかを調べる。
   1b の中で検査すると、後ろで宣言されるクラスを制約に書いた形がエラーになるので、
   すべてのクラスがクラス表に登録されるのを待つ。
   `register_class` が返した検査(制約を付けた型パラメータがメソッドの型に現れること)も、
   この検査の後に行う。
   エイリアスの 2 回目の試行は、型エイリアスの本体をもう一度試しに精緻化して、
   パラメータのカインドを推論する。
   1b の後なので、1b が newtype の本体を読んで決めたカインドも使える。
   既定化は、newtype とエイリアスのパラメータのカインドのうち、
   未確定のまま残ったものを `Type` に決める。
   行を返すカインドの検査は、既定化したパラメータのカインドが、
   行を返す矢印になっていないかを調べる。

   エイリアスの本体の精緻化を試行と呼ぶのは、診断を捨てるからである。
   正式な検査(未知の型、再帰、部分適用)はパス 2 が同じ本体で行うので、ここでエラーにすると、
   §11.43 の「最初の 1 つ」がどのエラーになるかが変わる。
   捕捉する例外は newtype の試行と同じ 4 つだけで、`Panic` は捕捉しない。

   既定化を 2 つ目のループで行うのは、宣言ごとに既定化すると、
   相互参照する newtype の間で、カインドが早すぎる時点で `KStar` に決まるからである(§11.31)。
   newtype のパラメータのカインドが、エイリアスを経由して決まる形がある。
   `newtype A[X] = MkA(Cb[X])` と `type Cb[E] = Callback[E]` の `X` がその例である。
   既定化を試行より後に行うのは、この形で、
   試行が `X` のカインドを決める前に `X` を既定化しないためである。
   既定化は表に新しい項目を登録せず、表のセルを書き換えるだけである。

   既定化はパス 2 より前に終わるので、値の本体と使用点は、カインドを決める手がかりにならない。
   型宣言のグループ(LangSpec §6.4)を読み終えた時点のカインドがそのまま残り、
   `let f[E](x: Ph[E], c: Callback[E])` のような使用点が、
   `Ph` のパラメータを後から行に変えることはない。
   この形でエラーになるのは `let` 自身の `E` である。
   `Ph[E]` が先に `E` を `Type` に決めるからである。

   newtype とエイリアスのパラメータの制約はパス 1a で拒否するので(`no_param_constraints`)、
   行カインドになったパラメータに型クラスの制約が残ることはない。

   **1c**：インスタンスの対象の型と、前方参照に使うシグネチャを登録する。
   対象の型のカインドの検査にクラス表が必要なので、1b の後に行う。
   シグネチャの登録は、本体を推論するパス 2 より前に済ませる(§11.36、§11.37)。

   **2**：本体を推論する。
   宣言順に推論し、束縛ごとに型を表示する。
   表示の前に `default_numerics` を呼ぶ。
   予約述語の付いた弱い型変数が残ったまま表示すると、
   ユーザには意味のない内部の述語が見えるからである。

   プレリュードも同じ `process_decls` で処理する。
   違いは、何もしない `emit` を渡して出力を捨てることと、
   `Decls.in_prelude` を立てて処理すること(§11.41)である。 *)

(* コンパニオン型のグローバルな別名を登録する(sample.kel:848)。
   平坦化ではなく、パス 1a で登録する。
   プレリュードを平坦化する時点では、宣言表はまだ空である。
   平坦化してから型検査する API の経路では、ユーザの宣言を平坦化する時点でも空である。
   その時点で登録すると既存の名前と照合できず、
   module List { pub newtype List } のような宣言がプレリュード自身の型検査を壊す。
   プレリュードのエフェクトと組み込みのエフェクト(Console や Heap)の名前との衝突も、ここで拒否する。
   エフェクト名は、型名と 1 つの名前空間を共有する。
   グローバルな別名は、エフェクト位置のエイリアスの解決(§11.5 の find_row_alias)でも、
   effect の宣言表より先に引かれる。
   衝突を許すと、module Console を 1 行追加するだけで、プログラムのすべての @ Console が
   その module のエイリアスを指すようになる。
   ユーザが宣言したエフェクトとの衝突は、平坦化が拒否する *)
let register_companion tyname =
  match !Decls.current_module with
  | Some sm when tyname = sm ^ "." ^ Type.display sm ->
      (* sm は module の内部名で、起点でない単位では単位の接頭辞が付く。
         m は表示名である。
         既存の名前は、同じ単位の内部名(sm)と標準環境の名前(m)の両方で照合する *)
      let m = Type.display sm in
      let taken tbl = Hashtbl.mem tbl (intern sm) || Hashtbl.mem tbl (intern m) in
      if taken Decls.con_kinds || taken Decls.aliases || Hashtbl.mem Decls.reserved_type_names (intern m) then
        type_error
          ("module " ^ m ^ " のコンパニオン型 " ^ m ^ " は既存の型 " ^ m
         ^ " と同名です(module 内の型とトップレベルの型は同名にできません)")
      else if taken Decls.effects then
        type_error
          ("module " ^ m ^ " のコンパニオン型 " ^ m ^ " は既存のエフェクト " ^ m
         ^ " と同名です(型とエフェクトは同名にできません)")
      else if Decls.marks_unit !Decls.current_unit then
        Hashtbl.replace Decls.unit_synonyms (!Decls.current_unit, intern m) (intern tyname)
      else Decls.add_con_synonym (intern m) (intern tyname)
  | _ -> ()

(* 宣言が属する module と単位を current_module と current_unit に設定して f を呼ぶ。
   process_decls で宣言の並びを走査するループは、すべてこの関数で囲む。
   1b の newtype のフィールドの型や、1c の signature_of_binding も、
   module の中の型を修飾なしで参照するので、囲み忘れたパスがあると、
   そのパスだけがその型を未知の型として扱う。
   §11.41 の in_prelude と同じく、Fun.protect で元の値に戻す *)
let with_decl_module node f = Decls.with_decl_scope (Tree.oid_of node) f

(* 型エイリアスと newtype の型パラメータには、型クラスの制約を書けない(§11.5 の規則 3)。
   型パラメータの構文は関数、クラス、インスタンスと共通なので、文法ではなくここで拒否する *)
let no_param_constraints what (tparams : type_param list) =
  List.iter
    (fun (tp : type_param) ->
      if tp.tp_classes <> [] then
        type_error (what ^ " の型パラメータ " ^ tp.tp_name ^ " には型クラスの制約を書けません"))
    tparams

(* パス 1c のシグネチャの辞書パラメータと、パス 2 で決めた束縛の型の辞書パラメータが、
   位置とクラスで一致することを検査する。
   前方参照の穴はシグネチャの正準順で、束縛の辞書パラメータは本体の型の正準順で並ぶ。
   順序がずれると、エラーにならずに別の辞書が渡される。
   どちらも同じ注釈から作るので一致するはずだが、ここでも検査する *)
let check_signature_dicts node fn_ty sg =
  let a = List.map snd (Unify.dkeys_of fn_ty) and b = List.map snd (Unify.dkeys_of sg) in
  if a <> b then at_node node (fun () -> bug "署名と本体の辞書パラメータが一致しません")

let process_decls ?(toplevel_extra = []) env ~emit decls =
  let eff0 = toplevel_eff ~extra:toplevel_extra () in
  (* パス 1a: 型エイリアスと、newtype の名前とカインドと、effect の名前を登録する *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with
      | T.DType t ->
          no_param_constraints ("型エイリアス " ^ Type.display t.T.ta_name) t.T.ta_params;
          register_companion t.T.ta_name;
          Decls.add_alias
            {
              Decls.al_name = intern t.T.ta_name;
              al_params = t.T.ta_params;
              (* パラメータごとのカインドのセルを作る。
                 F[_] と書いてあれば、この時点でカインドが決まる。
                 それ以外は、1a′ と 1b の後処理が、本体を試しに精緻化して推論する *)
              al_kinds =
                List.map
                  (fun (tp : type_param) -> if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var ())
                  t.T.ta_params;
              al_kind = t.T.ta_kind;
              al_body = t.T.ta_body;
              al_module = !Decls.current_module;
              al_unit = !Decls.current_unit;
            }
      | T.DNewtype n ->
          no_param_constraints ("newtype " ^ Type.display n.T.nt_name) n.T.nt_params;
          (* 型の名前空間への名前の登録は、宣言順に走査するここで行う。
             add_data を呼ぶのは 1b なので、種別の違う再宣言の検出を add_data に任せると、
             1a の add_alias のほうが必ず先に名前を登録する。
             すると、後に書いたエイリアスではなく、先に書いた newtype のほうが再宣言として報告される *)
          Decls.claim_type_name "newtype" (intern n.T.nt_name);
          register_companion n.T.nt_name;
          if Decls.prelude_owned "data" (intern n.T.nt_name) && not !Decls.in_prelude then
            type_error ("標準環境の newtype " ^ Type.display n.T.nt_name ^ " は再宣言できません");
          (* 型構成子のカインドには、パラメータごとにカインドのセルを入れる。
             F[_] と書いたパラメータ以外のセルは、新しいカインド変数である。
             1b の register_newtype がこのセルを取り出して dd_params の vkind に使うので、
             本体で決まったカインドが、そのまま型構成子のカインドになる *)
          Hashtbl.replace Decls.con_kinds (intern n.T.nt_name)
            (List.fold_right
               (fun (tp : type_param) acc -> KArrow ((if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var ()), acc))
               n.T.nt_params KStar)
      | T.DEffect e ->
          (* エフェクトの名前はここで表に登録し、操作は 1b で登録する。
             1b で読む型の本体に、後ろで宣言されたエフェクトのラベルを書けるようにするためである *)
          Decls.declare_effect (intern e.T.ef_name)
      | _ -> ())
    decls;
  (* パス 1a の後処理: newtype とエイリアスの本体を試しに精緻化する。
     宣言順に依存せずにパラメータのカインドを決めるために、登録の前に本体を読み、結果を捨てる。
     ある回で決まったカインドによって、前の回でエラーになった本体を読めるようになることがある。
     そこで、カインドの決まったパラメータの個数が増えなくなるまで繰り返す。
     この個数はパラメータの総数を超えないので、繰り返しは終わる *)
  let speculate_all () =
    List.iter
      (fun ((_, d) as node : T.decl) ->
        at_node node @@ fun () ->
        with_decl_module node @@ fun () ->
        match d with T.DNewtype n -> speculate_newtype env n | T.DType t -> speculate_alias env t | _ -> ())
      decls
  in
  let settled () =
    let known k = match kind_repr k with KVar _ -> 0 | _ -> 1 in
    let rec count k = match kind_repr k with KArrow (a, r) -> known a + count r | _ -> 0 in
    List.fold_left
      (fun acc ((_, d) as node : T.decl) ->
        match d with
        | T.DNewtype n ->
            with_decl_module node @@ fun () ->
            acc + count (Decls.con_kind (intern n.T.nt_name) (List.length n.T.nt_params))
        | T.DType t -> (
            with_decl_module node @@ fun () ->
            match Hashtbl.find_opt Decls.aliases (intern t.T.ta_name) with
            | Some info -> List.fold_left (fun acc k -> acc + known k) acc info.Decls.al_kinds
            | None -> acc)
        | _ -> acc)
      0 decls
  in
  let rec speculate_until_stable prev =
    speculate_all ();
    let now = settled () in
    if now > prev then speculate_until_stable now
  in
  speculate_until_stable (settled ());
  (* パス 1b: newtype のコンストラクタ、effect の操作、type class を登録する。
     相互再帰と前方参照を許す。
     クラスのメソッドの型パラメータの検査は class_checks に保持し、後処理で行う *)
  let class_checks = ref [] in
  let env =
    List.fold_left
      (fun env ((_, d) as node : T.decl) ->
        at_node node @@ fun () ->
        with_decl_module node @@ fun () ->
        match d with
        | T.DNewtype n ->
            register_newtype env n;
            env
        | T.DEffect e ->
            register_effect env e;
            env
        | T.DClass c ->
            let methods, check = register_class env c in
            class_checks := (c, check) :: !class_checks;
            (* 非修飾名は、同じ名前の束縛がすでにあれば登録しない。
               修飾名 Cls.m はそのクラスだけの名前なので、必ず登録する。
               どちらの名前も、参照先の宣言は GMethod Cls.m である。
               評価器は型検査が木に書いた参照先を使うので、型検査と実行が別の宣言を選ぶことはない *)
            List.fold_left
              (fun env (mn, ty) ->
                let q = c.T.cls_name ^ "." ^ mn in
                let env = add_top env q ty (Tree.GMethod q) in
                if SMap.mem mn env.values then env else add_top env mn ty (Tree.GMethod q))
              env methods
        | _ -> env)
      env decls
  in
  (* 1b の後処理: クラスのメソッドの型パラメータの制約に、
     未知のクラスや予約述語がないかを検査する。
     register_class は 1b で宣言順に呼ばれるので、そこで検査すると、
     後ろで宣言されるクラスを制約に書いた形がエラーになる。
     すべてのクラスがクラス表に登録されたこの時点で検査すれば、結果は宣言順に依存しない。
     register_class が返した関数は、制約を付けた型パラメータがメソッドの型に現れることを検査する。
     この関数は、同じクラスの制約に書かれたクラス名を検査した後に呼ぶ。
     束縛の検査と同じく、未知のクラスと予約述語の診断が先に出る *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with
      | T.DClass c ->
          List.iter (fun (v : T.class_val) -> List.iter (fun tp -> ignore (class_names_of tp)) v.T.cv_tparams) c.T.cls_vals;
          Option.iter (fun k -> k ()) (List.assq_opt c !class_checks)
      | T.DType t -> (
          (* エイリアスの本体から、パラメータのカインドを推論する。
             ここで本体をもう一度試しに精緻化し、パラメータのカインドだけを決めて結果は捨てる。
             パス 2 の検査(未知の型、再帰、部分適用)より前に行わないと、
             エイリアスを先に使う宣言があったときに、カインドが宣言順で変わる。
             診断は出さない。
             正式な検査は、パス 2 が同じ本体で行う。
             捕捉する例外は speculate_alias の with 節に並べた 4 つだけで、Panic は捕捉しない。
             本体が途中でエラーになる宣言では、エラーの位置より後の使い方が推論に使われず、
             カインドは Type に既定化される。
             ただし、そのプログラムはパス 2 の同じ箇所でエラーになる *)
          speculate_alias env t)
      | _ -> ())
    decls;
  (* 1b の後処理の 2 つ目のループ: カインドを既定化する。
     1b がすべて終わってから既定化する。
     宣言ごとに既定化すると、相互参照する newtype の間で、
     カインド変数が早すぎる時点で KStar に決まる。
     same_kind が、未解決のカインド変数どうしを片方へのリンクにするからである。
     エイリアスを試しに精緻化する 1 つ目のループより後に行うのは、
     newtype のパラメータのカインドがエイリアスを経由して決まる形
     (newtype A[X] = MkA(Cb[X]) と type Cb[E] = Callback[E])で、
     試行が X のカインドを決める前に X を既定化しないためである。
     型構成子のカインドと dd_params の両方を既定化するのは念のためである。
     両者はセルを共有しているので、通常はどちらか一方で足りる *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with
      | T.DNewtype n -> (
          default_kind (Decls.con_kind (intern n.T.nt_name) (List.length n.T.nt_params));
          match Hashtbl.find_opt Decls.datas (intern n.T.nt_name) with
          | Some dd ->
              List.iter (fun (i : var_info) -> default_kind i.vkind) dd.Decls.dd_params;
              (* 行を返すカインドを検査する。
                 型変数への適用 F[E] を行カインドのパラメータに渡すと、
                 elab_con_args は結果のカインドを構造の一致で調べてエラーにする(§11.5)。
                 ただし、渡す先の newtype が後ろで宣言されていると、1b で本体を読む時点では、
                 渡す先のパラメータのカインドが決まっていない。
                 そのとき same_kind は、F の結果のカインドを渡す先のパラメータのセルにリンクし、
                 渡す先の本体がそのセルを Row に決める。
                 宣言順によらずエラーにするために、すべてのカインドが決まったこの時点で、
                 パラメータのカインドが矢印で、その結果のカインドが Row になっていないかを調べる *)
              let rec codomain k = match kind_repr k with KArrow (_, r) -> codomain r | k -> k in
              List.iter2
                (fun (tp : type_param) (i : var_info) ->
                  match kind_repr i.vkind with
                  | KArrow _ when codomain i.vkind = KRow ->
                      type_error
                        ("newtype " ^ n.T.nt_name ^ " の型パラメータ " ^ tp.tp_name
                       ^ " への適用が行として使われています(行を返す型構成子はありません)")
                  | _ -> ())
                n.T.nt_params dd.Decls.dd_params
          | None -> ())
      | T.DType t -> (
          match Hashtbl.find_opt Decls.aliases (intern t.T.ta_name) with
          | Some info ->
              List.iter default_kind info.Decls.al_kinds;
              (* 行を返すカインドの検査は、エイリアスのパラメータにも行う。
                 1b より前にエイリアスを試しに精緻化するとき、
                 後ろで宣言される newtype に F[E] を渡す本体を読むと、newtype の場合と同じく、
                 F の結果のカインドが渡す先のパラメータのセルにリンクされる *)
              let rec codomain k = match kind_repr k with KArrow (_, r) -> codomain r | k -> k in
              List.iter2
                (fun (tp : type_param) k ->
                  match kind_repr k with
                  | KArrow _ when codomain k = KRow ->
                      type_error
                        ("型エイリアス " ^ t.T.ta_name ^ " の型パラメータ " ^ tp.tp_name
                       ^ " への適用が行として使われています(行を返す型構成子はありません)")
                  | _ -> ())
                info.Decls.al_params info.Decls.al_kinds
          | None -> ())
      | _ -> ())
    decls;
  (* パス 1c: インスタンスの対象の型と、前方参照できる let のシグネチャを登録する。
     前方参照できる let の注釈の条件は §11.36 で述べる *)
  let env =
    List.fold_left
      (fun env ((_, d) as node : T.decl) ->
        at_node node @@ fun () ->
        with_decl_module node @@ fun () ->
        match d with
        | T.DInstance i ->
            register_instance i;
            env
        | T.DLet ((_, b) as bn) -> (
            (* すでに環境にある名前は上書きしない。
               先に登録された 1c のシグネチャ、クラスのメソッド、プレリュードの束縛がその例である。
               前方参照は、その名前を最初に登録した宣言を指す *)
            match (binding_name b, signature_of_binding env b) with
            | Some x, Some ty when not (SMap.mem x env.values) -> add_top env x ty (Tree.GDecl (Tree.oid_of bn, x))
            | _ -> env)
        | T.DLetRec bs ->
            List.fold_left
              (fun env ((_, b) as bn : T.let_binding) ->
                match (binding_name b, signature_of_binding env b) with
                | Some x, Some ty when not (SMap.mem x env.values) -> add_top env x ty (Tree.GDecl (Tree.oid_of bn, x))
                | _ -> env)
              env bs
        | _ -> env)
      env decls
  in
  (* パス 2: 本体を宣言順に推論する *)
  let show_binding env ((_, b) : T.let_binding) =
    match binding_name b with Some x -> emit (Binding (Type.display x ^ " : " ^ Show.show (SMap.find x env.values))) | None -> ()
  in
(* ## 11.40 パス 2 の宣言 1 つ分の処理

   ### 穴を解く時点

   各宣言の終わりに、穴の一覧に残っているすべての穴を解き直す。
   前の宣言で型の決まらなかった穴(一般化しない束縛の弱い型変数の穴)も、
   この宣言で型が決まれば解ける。
   単位(ソースファイル、対話的な実行では 1 入力)の終わりまでに解けない穴は、曖昧性エラーにする。
   構文上の値である式文で、予約述語以外の制約が付いた単一化変数が残るものは一般化し、
   辞書パラメータを `DAbs` に書く。
   対話的な実行で、`show` のような名前だけの入力を受理するためである。
   パス 1c のシグネチャを持つ束縛では、
   シグネチャの制約の並びと束縛の辞書パラメータが、位置とクラスで一致することを検査する。

   `step` は宣言を 1 つ処理して、新しい環境を返す。

   `DLet` / `DLetRec` / `DExp` / `DInstance` では、既定化の直前に、宣言の終わりの曖昧性検査を行う。
   宣言の型から到達できない制約は、この後どの処理でも型が決まらないからである。
   `DExp` も対象なので、式文として値を捨てる式の制約も、曖昧性エラーになる。
   `DType` / `DNewtype` / `DEffect` / `DClass` / `DExtern` では行わない。
   宣言の型に相当するものがなく、到達できる変数の集合を空にして調べると、
   曖昧でない制約まで曖昧と報告するからである。

   宣言の種類ごとの処理は、次のとおりである。

   - `DType`：パス 1a で表に登録してあるので、ここでは検査のためだけに本体を精緻化し、結果を捨てる。
     未知の型、再帰、部分適用をこの時点で報告するので、
     使われないエイリアスの誤りも、報告されずに残ることはない。
     `EffectRow` の注釈がないエイリアスでは、本体のカインドが行でないこともここで検査する
     (`check_alias_body_kind`。`test/kinds.t` の aliasrow)。
     展開した本体が型パラメータそのものであるエイリアス(`type Id[A] = A`、
     `type Id2[A] = Id[A]`)では、この検査を行わない。
     その本体のカインドはパラメータのカインドで、型宣言のグループの中の使い方で決まる。
     たとえば、型パラメータ `X` を `Callback[Id[X]]` の形で行のパラメータへ渡すと、
     `Id` の本体のカインドは行に決まる(`test/kinds.t` の hktrowok)。
   - `DLet` / `DLetRec`：本体を推論し、既定化してから型を表示する。
   - `DExp`：式を推論し、網羅性の警告を出してから型を表示する。
   - `DExtern`：シグネチャだけを登録する。
     実装は第13章の表にある。
     引数のパターン、エフェクトの注釈、返り値の注釈の扱いは束縛と同じで、本体がない点だけが違う。
     同じ名前を 2 度 `extern` で宣言できないのは、
     後の宣言が既存の実装に誤った型を付けられないようにするためである。
   - `DNewtype` / `DEffect` / `DClass`：パス 1 で登録が済んでいる。
   - `DInstance`：本体を検査する(§11.38)。
   - `DModule`：ここには来ない。
     平坦化で取り除かれている(§11.42)。

   警告は、この宣言で新しく増えた分だけを表示する。
   宣言と警告の対応がずれないように、処理の前の警告の個数を記録し、
   処理の後の個数との差を求める。 *)

  let step env ((_, d) as node : T.decl) =
    let wbefore = !warnings_count in
    let env' =
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      let env' =
        match d with
      | T.DType t ->
          (* 未知の型、再帰、部分適用の検査と、本体のカインドの検査をここで行う。結果は捨てる *)
          let info = Hashtbl.find Decls.aliases (intern t.T.ta_name) in
          let lvl = 1 in
          let rigids = make_rigids ~kinds:info.Decls.al_kinds lvl info.Decls.al_params in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          (match info.Decls.al_kind with
          | Some "EffectRow" -> ignore (elab_eff env_ty lvl info.Decls.al_body)
          | _ ->
              let ty = elab_type env_ty lvl info.Decls.al_body in
              (* 展開した本体が型パラメータそのもの(type Id[A] = A、type Id2[A] = Id[A])なら、
                 本体のカインドはパラメータのカインドで、型宣言のグループの中の使い方で決まる。
                 この場合は検査しない *)
              let bare_param =
                match Type.repr ty with
                | TVar r' -> List.exists (fun (_, _, r) -> r == r') rigids
                | _ -> false
              in
              if not bare_param then
                at_node info.Decls.al_body @@ fun () -> check_alias_body_kind (Type.display t.T.ta_name) ty);
          release_rigids rigids;
          env
      | T.DLet b ->
          let env' = elab_binding env 0 eff0 b in
          (match (binding_name (snd b), signature_of_binding env (snd b)) with
          | Some x, Some sg -> check_signature_dicts b (SMap.find x env'.values) sg
          | _ -> ());
          (* トップレベルの束縛子の参照先は、束縛ノードと名前の組(GDecl)で表す *)
          let env' =
            List.fold_left
              (fun e x ->
                let g = Tree.GDecl (Tree.oid_of b, x) in
                Option.iter (Hashtbl.replace top_types g) (SMap.find_opt x e.values);
                { e with tops = SMap.add x g e.tops })
              env' (pat_var_names (snd b).T.lb_name)
          in
          (* 宣言の終わりの曖昧性検査を、all=true で行う。
             宣言の型から到達できない制約は、この後どの処理でも型が決まらないからである。
             既定化の直前に行う。
             順序を逆にすると、予約述語の付いた変数が先になくなるので、
             それを対象外にする判定は不要になるが、Eq や Show だけが付いた変数の検出が遅れる *)
          Unify.check_ambiguity ~all:true ~level:0 [ Tree.get_ty b ];
          Unify.default_numerics () (* 表示の前に、予約述語の付いた弱い型変数を既定化する *);
          show_binding env' b;
          env'
      | T.DLetRec bs ->
          let env' = elab_rec_bindings ~top:true env 0 eff0 bs in
          List.iter
            (fun ((_, b) as bn : T.let_binding) ->
              match (binding_name b, signature_of_binding env b) with
              | Some x, Some sg -> check_signature_dicts bn (SMap.find x env'.values) sg
              | _ -> ())
            bs;
          Unify.check_ambiguity ~all:true ~level:0 (List.map Tree.get_ty bs);
          Unify.default_numerics ();
          List.iter (show_binding env') bs;
          env'
      | T.DExp e ->
          (* 構文上の値である式文で、予約述語以外の制約が付いた単一化変数が残るものは一般化し、
             辞書を受け取る値にする。
             対話的な実行で、show のような名前だけの入力を受理するためである。
             それ以外の式文は一般化しない。
             値を捨てる式の制約は、この後どの処理でも型が決まらない *)
          let hmark = Unify.hole_mark () in
          let mark = Unify.class_mark () in
          let value = is_value e in
          let t = elab_exp env (if value then 1 else 0) eff0 e in
          List.iter warn (Exhaust.drain ~level:0 ~tys:[ t ] ());
          if value && has_constrained_unbound t then (
            Unify.check_ambiguity ~all:false ~level:0 [ t ];
            Unify.generalize 0 t;
            let dps = Unify.dkeys_of t in
            if dps <> [] then Tree.set_dict node (Tree.DAbs dps);
            solve_holes_at ~since:hmark ~params:dps)
          else (
            if value then Unify.lower_levels ~since:mark 0 t;
            Unify.check_ambiguity ~all:true ~level:0 [ t ];
            Unify.default_numerics ());
          emit (Binding ("_ : " ^ Show.show t));
          env
      | T.DExtern ex ->
          (* extern 宣言はシグネチャだけを持ち、実装は builtin.ml の表にある。
             ここでは、リンケージ、二重宣言、プレリュードの名前の再宣言を検査する *)
          if ex.T.ex_abi <> "prim" && ex.T.ex_abi <> "C" then
            type_error ("未知の extern リンケージ: " ^ ex.T.ex_abi ^ "(prim か C を指定してください)");
          (* pub の完全注釈検査。let の検査(§11.28)と同じ規則である *)
          (if ex.T.ex_pub then
            check_pub_annots ~tparams:(List.map (fun (tp : type_param) -> tp.tp_name) ex.T.ex_tparams) ~params:(Some ex.T.ex_params) ~ret:ex.T.ex_ret);
          (* プレリュードの保護は非修飾の実装名で、二重宣言は修飾名で調べる(第6章 §6.2) *)
          Decls.add_extern ~unit:!Decls.current_unit ~prim:ex.T.ex_prim ex.T.ex_name;
          let lvl = 1 in
          let rigids = make_rigids lvl ex.T.ex_tparams in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          let seen = ref [] in
          let param_tys = List.map (fun _ -> new_var lvl) ex.T.ex_params in
          ignore (List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty ex.T.ex_params param_tys);
          let fn_eff =
            match ex.T.ex_eff with
            | Some e -> elab_eff env_ty lvl e
            | None when ex.T.ex_abi = "C" ->
                (* C リンケージで @ を省略すると、`@ Blocking` と読む(sample.kel:496、:798) *)
                TRowExtend (Type.eff_blocking, Type.t_unit, TRowEmpty)
            | None -> new_row_var lvl
          in
          let ret_ty = match ex.T.ex_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> new_var lvl in
          (* C の既知名は、引数と返り値の型をシグネチャの表と照合する(第6章 §6.2b)。
             行は照合しない。
             行は `@ Blocking`(省略した場合を含む)でも行変数でもよく、
             どちらにするかはバインディングを書く人が決める(sample.kel:798-799) *)
          (if ex.T.ex_abi = "C" then
             match Decls.c_known_signature ex.T.ex_prim with
             | None -> ()
             | Some (arg_cons, ret_con, rendered) ->
                 let same_con c t = match repr t with TCon (c', []) -> c' = c | _ -> false in
                 let ok =
                   List.length param_tys = List.length arg_cons
                   && List.for_all2 (fun t c -> same_con c t) param_tys arg_cons
                   && same_con ret_con ret_ty
                 in
                 if not ok then
                   type_error ("extern \"C\" の既知名 " ^ ex.T.ex_prim ^ " の型は " ^ rendered ^ " でなければなりません"));
          let ty = TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff) in
          Unify.generalize 0 ty;
          release_rigids rigids;
          (* 制約を付けた型パラメータは、束縛の型に現れなければならない。
             extern の実装は辞書を使わないので、
             評価器は、この束縛が受け取った辞書を捨てて実装を返す(第14章) *)
          let dps = Unify.dkeys_of ty in
          check_tparam_constraints ~rigids dps;
          if dps <> [] then Tree.set_dict node (Tree.DAbs dps);
          emit (Binding (Type.display ex.T.ex_name ^ " : " ^ Show.show ty));
          add_top env ex.T.ex_name ty (Tree.GDecl (Tree.oid_of node, ex.T.ex_name))
      | T.DNewtype _ -> env (* パス 1 で登録済み。フィールドの型の検査も登録のときに済んでいる *)
      | T.DEffect _ -> env (* パス 1 で登録済み *)
      | T.DClass _ -> env (* パス 1 で登録済み *)
      | T.DInstance i ->
          check_instance_bodies env eff0 node i;
          (* インスタンスの本体にも、宣言の終わりの曖昧性検査を行う。
             値制限で一般化されない本体の let では、all=false の検査が行われない。
             その検査は、一般化する束縛(gen が真)でだけ行うからである。
             ここで検査しないと、宣言の終わりの default_numerics が制約つき変数の一覧を空にするので、
             曖昧な制約が報告されないまま捨てられる。
             到達できる変数は、各メソッドの束縛の型から求める *)
          Unify.check_ambiguity ~all:true ~level:0
            (List.concat_map
               (fun ((_, d) : T.decl) ->
                 match d with
                 | T.DLet b -> [ Tree.get_ty b ]
                 | T.DLetRec bs -> List.map Tree.get_ty bs
                 | _ -> [])
               i.T.ins_body);
          env
      | T.DModule _ ->
          (* 平坦化の後なら、ここには到達しない。到達したら不変条件の違反で、処理系のバグである *)
          bug "module が平坦化されていません(flatten_modules を先に呼んでください)"
      in
      (* 既定化も、宣言の at_node の中で行う。
         DInstance の本体で作った数値リテラルの予約述語は、ここで初めてエラーになることがある。
         at_node の外で行うと、位置のない型エラーになる *)
      Unify.default_numerics ();
      check_pattern_numbers ();
      (* 宣言の終わりに、穴の一覧に残っている穴をすべて解き直す。
         前の宣言で型の決まらなかった穴も、この宣言で型が決まれば解ける *)
      solve_holes_at ~since:0 ~params:[];
      opened_rows := [];
      env'
    in
    (* この宣言が出した警告だけを取り出す。
       warnings は新しい警告を先頭に追加するので、先頭の n 個を取り出して逆順にする。
       個数は warnings_count に持つ。
       宣言のたびに warnings の長さを数え直すと、
       毎回、警告の総数に比例する時間がかかるからである *)
    let fresh = !warnings_count - wbefore in
    let rec take n l = if n = 0 then [] else match l with [] -> [] | x :: tl -> x :: take (n - 1) tl in
    List.iter (fun w -> emit (Warning w)) (List.rev (take fresh !warnings));
    env'
  in
  (* パス 1 でたまった制約つき変数は、宣言ごとの曖昧性の判定に関係しない。
     インスタンスの対象の型やシグネチャを具体化したときに作った変数である。
     Unify.reset で制約つき変数や穴などの一覧を空にしてから、宣言を順に処理する *)
  Unify.reset ();
  let env = List.fold_left step env decls in
  (* 単位(ソースファイル、対話的な実行では 1 入力)の終わりまでに型の決まらない制約は、
     曖昧性エラーにする。
     エラーの位置は、最も古い穴の位置にする *)
  (match List.rev (Unify.unsolved_holes ()) with
  | (_, h) :: _ ->
      raise
        (Type_error_at
           ( h.Tree.h_loc,
             "曖昧な制約: " ^ display_of h.Tree.h_cls
             ^ " を満たす型が決まりません(一般化しない束縛か式文の型変数です。注釈で型を決めてください)" ))
  | [] -> ());
  env

(* ## 11.41 型検査のエントリポイント

   プレリュード(第15章)を先に処理してから、ユーザの宣言の並びを処理する。
   プレリュードの出力は捨て、環境だけを引き継ぐ。

   `Decls.in_prelude` を立てる処理は、`Fun.protect` で囲む。
   プレリュードの処理中に型エラーが発生しても、フラグが立ったままにならないようにするためである。
   立ったままになると、その後のユーザの宣言がプレリュードの宣言として扱われ、
   再宣言の保護にかからなくなる。

   プログラムの型検査は、プログラム全体の初期化と、単位ごとの処理に分かれる。
   `start_program` は、型検査が持つグローバルな状態を空にする。
   空にするのは、警告、`Unify` が持つ一覧(制約つき変数や穴など)、網羅性検査の遅延キュー、
   パターンの数値リテラルの一覧、再帰群のスタック、使用時に開いた行変数の一覧、
   `pub` の規則の検査に使う行のセルの一覧である。
   `check_prelude` は、プレリュードを処理した後の環境を返す。
   `check_unit` は、渡された環境で 1 個の単位の宣言を処理し、その単位の環境を返す。
   宣言ごとの単位は、平坦化が `Decls.decl_unit` に記録している。
   各パスは、その記録から `current_unit` を設定する(§11.39 の `with_decl_module`)。
   `check_unit` も `current_unit` を設定するのは、
   宣言の外で名前を引く処理(スコープを作る処理)のためである。
   ファイルの単位は、プレリュードを処理した後の環境(`check_prelude` の返り値)に、
   その単位が import した名前を追加したものから始める。
   対話的な実行の入力は、前の入力を処理した後の環境から始める。 *)
let start_program () =
  warnings := [];
  warnings_count := 0;
  Unify.reset ();
  Exhaust.reset ();
  pattern_numbers := [];
  group_stack := [];
  opened_rows := [];
  pub_pure_cells := []

let check_prelude prelude =
  Decls.in_prelude := true;
  Fun.protect
    ~finally:(fun () -> Decls.in_prelude := false)
    (fun () -> process_decls (initial_env ()) ~emit:(fun _ -> ()) prelude)

let check_unit ?toplevel_extra ~unit env ~emit decls =
  let saved = !Decls.current_unit in
  Decls.current_unit := unit;
  Fun.protect ~finally:(fun () -> Decls.current_unit := saved) (fun () -> process_decls ?toplevel_extra env ~emit decls)

let type_check_decls ?(prelude = []) decls =
  start_program ();
  let out = current_out in
  out := [];
  (* 先頭に追加して最後に逆順にする。末尾に @ で連結すると、宣言数の 2 乗に比例する時間がかかる *)
  let emit s = out := s :: !out in
  let env = check_prelude prelude in
  let _env = check_unit ~unit:Decls.root_unit env ~emit decls in
  List.rev !out

(* 宣言の並びから、トップレベル(module の外)の値の名前を集める。パターン束縛の束縛子も含む *)
let toplevel_value_names (decls : T.decl list) =
  List.concat_map
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DLet (_, b) -> pat_var_names b.T.lb_name
      | T.DLetRec bs -> List.concat_map (fun ((_, b) : T.let_binding) -> pat_var_names b.T.lb_name) bs
      | T.DExtern ex -> [ ex.T.ex_name ]
      | _ -> [])
    decls

(* ## 11.42 module の平坦化

   Diktor は module を、名前空間としてではなく、**名前を変える規則**として実装する。
   宣言の並びを精緻化に渡す前に平坦化するので、以降のパスは module の入れ子を扱わない。
   ただし、各宣言がどの module にあったかは `Decls.decl_module` に記録してあり、
   `process_decls` のパスは、`with_decl_module` で `current_module` を設定してから宣言を処理する。
   平坦化は宣言の名前を変えるだけで、本体の中の参照は走査せず、名前も変えない。
   本体の中の参照は、別名表で解決する。
   そのため、束縛子を見落として参照の名前を誤って変える、という種類の誤りは起きない。

   - `newtype` / `type`：名前を `M.名前` に変えて登録し、
     module スコープの別名 `(M, 非修飾名) → M.名前` を登録する。
     グローバルな別名表に登録するのは、コンパニオン型(module と同名の型。sample.kel:848)だけである。
     すべての別名をグローバルな表に登録すると、`module M { newtype List[A] = … }` と書くだけで、
     プレリュード自身の型検査が失敗する。
   - `let`：名前を `M.名前` に変え、module スコープの値の別名を登録する。
     module 内の相互参照と `let rec` の自己再帰は、
     環境になかった名前だけを module スコープの別名で引く、という規則で解決できる。
     module 内の値の名前を、トップレベルの値の名前と同じにすることは禁止する。
     これは言語の規則である(LangSpec §15.3)。
     実装の都合による禁止ではない。
     名前を解決するのは elab だけで、評価器は木に書いた参照先を使うので、
     同名を許しても型検査と評価器が別々の宣言を指すことはない。
   - `pub`：可視性の表(第6章の `value_visibility` / `con_visibility`)に記録する。
     検査は名前を使う箇所(§11.3 / §11.11 / §11.8)で行い、可視性の境界は module だけである。
     コンストラクタは、所属する newtype の `pub` に従う。
   - `instance`：そのままトップレベルに出す。
     インスタンスは import で選ばず、どのファイルで宣言したものも 1 つの表から引く(sample.kel:843)。
   - `extern`：`ex_name` を `M.f` に修飾するが、実装名 `ex_prim` は元のままにする(第1章)。
     実装は処理系の側の表にあり、その表は module ごとに分かれていない。
     第6章の登録表は、プレリュードの保護を `ex_prim` で、二重宣言の検査を修飾名で調べる(§6.2)。
     修飾名だけをキーにすると、module の中で宣言すれば保護にかからなくなる。
     実装名だけをキーにすると、別々の module が同じ C のシンボルを、
     それぞれの名前で束縛できなくなる。

   型の別名表は実行時にも使う。
   評価器が別名表を引かないと、module の中の instance の対象の型が実行時に見つからない。
   評価器は、宣言のあった module を `current_module` に設定してから引く(第14章 §14.12)。
   値の名前は、型検査が解決した参照先を木に書き(§11.11)、評価器はそれを使うので、
   評価器は値の別名表を引かない。

   入れ子の module と、module の中の effect / class / 式文は未対応である。
   いったん受理して後の検査でエラーにするのではなく、平坦化の時点で報告し、
   種別は**未実装**(終了コード 4)にする。
   module の中の `let` のパターン束縛だけは、未対応ではなく仕様上の制限なので、
   型エラー(終了コード 1)にする。

   ### 組み込みが登録している名前は宣言できない

   平坦化が作る修飾名 `M.x` は、module ごとの名前空間ではなく、グローバルな値の名前空間に入る。
   そのため、組み込みがすでに登録している名前を module 宣言で作れると、
   組み込みの値はシグネチャごと値環境から見えなくなる。
   そうした名前には、`Ref.new` / `Array.get` / `MutableArray.set` のような組み込みの操作(§6.11)と、
   `Show.show` のようなクラスメソッドの修飾名(§6.13)がある。
   見えなくなったことは、その名前を使う箇所まで分からない。
   宣言の位置で検査しないと、たとえば `module MutableArray { pub let set … }` を書いたプログラムは、
   宣言から離れた、名前を使う箇所でエラーになる。
   そのときの診断は `MutableArray は Integral のインスタンスではありません` のように、
   原因と関係のない内容になる。
   `claim_val` の 3 番目の分岐が、これを宣言の位置でエラーにする。
   組み込みの値の一覧は第6章の `builtin_values` の 1 つだけで、
   ここでは `is_builtin_value` を通してそれを引く。

   この検査は、予約型名を `newtype` で宣言できない(§6.6)のと同じ規則である。
   ただし、module 名そのものは予約しない。
   `module Array { pub let sum(…) }` は型検査に通る。
   型名は型そのものだが、module 名は修飾名の接頭辞にすぎないので、
   型名と同じように予約する理由がない。
   保護するのは、組み込みがすでに登録している名前だけである。
   この分岐に該当するのは 11 件で、`Ref` の 3 操作、`Array` の 3 操作、
   `MutableArray` の 5 操作である。
   組み込みのクラスメソッドの修飾名 12 件は、この分岐ではなく 2 番目の分岐がエラーにする。
   `flatten_modules` の `class_methods` は `Decls.classes` から作るので組み込みのクラスも含み、
   2 番目の分岐が先に該当するからである。
   その診断のメッセージは、`test/visibility.t` の visc が期待出力として検査している。

   非修飾の組み込みの値は保護せず、トップレベルの `let` が診断なしに隠せる。
   該当するのは、`pinned`(§6.11b)と、
   `show` / `add` などのクラスメソッドの非修飾名である。
   これらはユーザのトップレベルの名前と同じ名前空間にある。
   隠せないようにするには、値の名前はグローバルな環境を先に引く、
   という枠組み(第6章 §6.4)から見直す必要がある。
   たとえば `let pinned[A](f: A): Int32 = 0` と書くと、
   `Blocking` を行から取り除く組み込みの `pinned` の型が見えなくなる。

   3 番目の分岐には `in_prelude` を調べる条件がある。
   しかし平坦化は `in_prelude` を立てる前に実行される(第16章)ので、
   この条件によってプレリュードが検査を免れることはない。
   `--prelude` で差し替えたプレリュードも、
   ユーザのプログラムと同じように拒否される(`test/visibility.t` の visbipre)。
   同梱のプレリュードは `module` を含まないので、
   この条件が検査の結果を変えないことは、同梱のプレリュードでは観測できない。
   組み込みの操作をプレリュードのソースへ移す場合は、
   この条件を有効にする箇所(平坦化を呼ぶ第16章の側)を先に決める必要がある。

   平坦化は単位ごとに呼ぶ(§11.45)。
   起点でない単位では、型、コンストラクタ、エフェクト、クラス、module の名前に単位の接頭辞を付け、
   単位の別名を登録する(第6章 §6.4)。
   module の中とトップレベルで同じ名前を禁止する規則は、
   その単位が import した値と型の名前も対象にする。
   この規則の範囲がソースファイルだからである(LangSpec §15.3)。 *)

let flatten_modules ?session_vals ?(imported_vals = []) ?(imported_types = []) ?(unit = Decls.root_unit) (decls : T.decl list)
    : T.decl list =
  (* 起点でない単位では、型、コンストラクタ、エフェクト、クラス、module の名前に単位の接頭辞を付け、
     接頭辞のない名前から内部名を引く別名を、単位の表に登録する(§6.4)。
     トップレベルの値の名前には接頭辞を付けない。
     module の値は、接頭辞の付いた module 名で始まる内部名になる *)
  let marked = Decls.marks_unit unit in
  let spell tbl name =
    let q = Decls.mark_spelling unit name in
    if marked then Hashtbl.replace tbl (unit, intern name) (intern q);
    q
  in
  let qualifier name =
    let q = Decls.mark_spelling unit name in
    if marked then Hashtbl.replace Decls.unit_qualifiers (unit, name) q;
    q
  in
  let spell_ctors (n : T.newtype') =
    match n.T.nt_rhs with
    | T.NtCtors cs ->
        { n with T.nt_rhs = T.NtCtors (List.map (fun (c : T.ctor_decl) -> { c with T.cd_name = spell Decls.unit_ctors c.T.cd_name }) cs) }
  in
  (* トップレベル(module の外)の値の名前を先に集める。
     module 内の値の名前がこれと同じになることを禁止するためである(§6.4)。
     パターン束縛の束縛子もすべて集める。
     binding_name は PVar の名前しか返さないので、それで集めると、
     let (a, b) = … の a が検査から漏れる *)
  let toplevel_vals = Hashtbl.create 32 in
  let rec pat_names ((_, p) : T.pat) =
    match p with
    | T.PVar x -> Hashtbl.replace toplevel_vals x ()
    | T.PAnnot (q, _) -> pat_names q
    | T.PRecord (fs, tail) ->
        List.iter (fun (_, q) -> pat_names q) fs;
        Option.iter pat_names tail
    | T.PCtor (_, args) -> List.iter (fun a -> pat_names a.T.cap_pat) args
    | T.PVariant (_, q) -> pat_names q
    | T.PWildcard | T.PBool _ | T.PNumber _ | T.PText _ -> ()
  in
  (* トップレベルの型名と、クラスのメソッド名も集める。
     次の 2 つを平坦化の時点で拒否するためである。
     1 つは、コンパニオン型のグローバルな別名が、既存の型名を診断なしに置き換えることである。
     これを許すと、module Foo を 1 行追加するだけで newtype Foo が置き換わり、
     名目的な型による抽象が壊れる。
     もう 1 つは、module 名がクラス名と同じときに、修飾名 M.f がクラスメソッドの修飾名と同じになり、
     値環境で区別できなくなることである *)
  let toplevel_types = Hashtbl.create 16 in
  let class_methods : (string, string list) Hashtbl.t = Hashtbl.create 16 in
  Hashtbl.iter
    (fun cname (ci : Decls.class_info) ->
      (* この単位から見えるクラスは、接頭辞のないクラスと、この単位で宣言したクラスである *)
      let s = Type.name_of cname in
      match Decls.unit_of_spelling s with
      | None -> Hashtbl.replace class_methods s (List.map fst ci.Decls.ci_methods)
      | Some u when u = unit -> Hashtbl.replace class_methods (Type.display s) (List.map fst ci.Decls.ci_methods)
      | Some _ -> ())
    Decls.classes;
  List.iter
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DLet (_, b) -> pat_names b.T.lb_name
      | T.DLetRec bs -> List.iter (fun ((_, b) : T.let_binding) -> pat_names b.T.lb_name) bs
      | T.DExtern ex -> Hashtbl.replace toplevel_vals ex.T.ex_name ()
      | T.DNewtype n -> Hashtbl.replace toplevel_types n.T.nt_name ()
      | T.DType t -> Hashtbl.replace toplevel_types t.T.ta_name ()
      | T.DEffect e -> Hashtbl.replace toplevel_types e.T.ef_name ()
      | T.DClass c -> Hashtbl.replace class_methods c.T.cls_name (List.map (fun (v : T.class_val) -> v.T.cv_name) c.T.cls_vals)
      | _ -> ())
    decls;
  (* import した値と型の名前も、module の中の値やコンパニオン型と同名にできない。
     同名を禁止する規則の範囲はソースファイルである(LangSpec §15.3) *)
  List.iter (fun x -> Hashtbl.replace toplevel_vals x ()) imported_vals;
  List.iter (fun x -> Hashtbl.replace toplevel_types x ()) imported_types;
  (* 対話的な実行では、前の入力の名前とも比べる。
     この入力のトップレベルの値が、前の入力の module の中の値と同名でないことを検査する。
     また、前の入力のトップレベルの値の名前を toplevel_vals に追加して、
     この入力の module の中の値と比べる。
     同名の値を持つ module が前の入力に複数あれば、
     名前が辞書順(バイト列の比較)で最も小さい module を報告する。
     報告する module が、表をたどる順序で変わらないようにするためである *)
  (match session_vals with
  | None -> ()
  | Some (prev : (string, unit) Hashtbl.t) ->
      List.iter
        (fun (node : T.decl) ->
          at_node node @@ fun () ->
          List.iter
            (fun x ->
              match
                Hashtbl.fold
                  (fun (m, y) _ acc ->
                    if Type.name_of y <> x then acc
                    else match acc with Some m' when String.compare m' m <= 0 -> acc | _ -> Some m)
                  Decls.module_val_synonyms None
              with
              | Some m ->
                  type_error
                    ("トップレベルの " ^ x ^ " は、前の入力の module " ^ Type.display m ^ " の " ^ x
                   ^ " と同名です(module 内の名前とトップレベル名は同名にできません)")
              | None -> ())
            (toplevel_value_names [ node ]))
        decls;
      Hashtbl.iter (fun x () -> Hashtbl.replace toplevel_vals x ()) prev);
  let record_unit ((data, d') : T.decl) =
    Hashtbl.replace Decls.decl_unit (Tree.oid_of (data, d')) unit;
    (data, d')
  in
  List.concat_map
    (fun ((bdata0, d) as node : T.decl) ->
      at_node node @@ fun () ->
      List.map record_unit
      @@
      match d with
      | T.DNewtype n -> [ (bdata0, T.DNewtype (spell_ctors { n with T.nt_name = spell Decls.unit_synonyms n.T.nt_name })) ]
      | T.DType t -> [ (bdata0, T.DType { t with T.ta_name = spell Decls.unit_synonyms t.T.ta_name }) ]
      | T.DEffect e -> [ (bdata0, T.DEffect { e with T.ef_name = spell Decls.unit_synonyms e.T.ef_name }) ]
      | T.DClass c ->
          ignore (qualifier c.T.cls_name);
          [ (bdata0, T.DClass { c with T.cls_name = spell Decls.unit_classes c.T.cls_name }) ]
      | T.DModule (_, mname, body) ->
          (* mname は表示名、sname は表のキーに使う内部名である *)
          let sname = qualifier mname in
          List.concat_map
            (fun ((bdata, bd) as bnode : T.decl) ->
              at_node bnode @@ fun () ->
              let claim_val x =
                if Hashtbl.mem toplevel_vals x then
                  type_error
                    ("module " ^ mname ^ " の " ^ x ^ " はトップレベルの " ^ x
                   ^ " と同名です(module 内の名前とトップレベル名は同名にできません)")
                else if match Hashtbl.find_opt class_methods mname with Some ms -> List.mem x ms | None -> false then
                  (* 修飾名 M.x が、クラス M のメソッド x の修飾名と同じ名前になり、
                     値環境で区別できない *)
                  type_error
                    ("module " ^ mname ^ " の " ^ x ^ " は型クラス " ^ mname ^ " のメソッド " ^ x
                   ^ " と修飾名が衝突します(module か メソッドを改名してください)")
                else if (not !Decls.in_prelude) && Decls.is_builtin_value (mname ^ "." ^ x) then
                  (* 組み込みの修飾名(Ref.new / MutableArray.set など)は宣言できない。
                     予約型名を newtype で宣言できない(§6.6)のと同じ規則である。
                     診断なしに隠すと、組み込みの値がシグネチャごと見えなくなる *)
                  type_error
                    ("module " ^ mname ^ " の " ^ x ^ " は組み込みの " ^ mname ^ "." ^ x
                   ^ " と同名です(組み込みの名前は宣言できません)")
                else Decls.(Hashtbl.replace module_val_synonyms (sname, intern x) (intern (sname ^ "." ^ x)));
                Decls.add_val_synonym (intern x) (intern (sname ^ "." ^ x))
              in
              let claim_con name pub =
                let qual = sname ^ "." ^ name in
                Decls.(Hashtbl.replace module_con_synonyms (sname, intern name) (intern qual));
                Decls.add_con_hint (intern name) (intern qual);
                (* コンパニオン型(module と同名の型)がトップレベルの型名と衝突するときは、
                   ここで拒否する。
                   許すと、module Foo を 1 行追加するだけでトップレベルの型 Foo が置き換わり、
                   名目的な型による抽象が壊れる。
                   プレリュードの名前との衝突の検査と、グローバルな別名の登録は、
                   パス 1a(§11.39)で行う。
                   プレリュードを平坦化する時点と、平坦化してから型検査する API の経路では、
                   宣言表がまだ空だからである。
                   可視性は pub をそのまま記録する *)
                if name = mname && (Hashtbl.mem toplevel_types name || Hashtbl.mem Decls.reserved_type_names (intern name))
                then
                  type_error
                    ("module " ^ mname ^ " のコンパニオン型 " ^ name ^ " は既存の型 " ^ name
                   ^ " と同名です(module 内の型とトップレベルの型は同名にできません)");
                Hashtbl.replace Decls.con_visibility (intern qual) { Decls.vis_module = sname; vis_pub = pub };
                qual
              in
              let record_module (data, d') =
                Hashtbl.replace Decls.decl_module (Tree.oid_of (data, d')) sname;
                (data, d')
              in
              let vis x pub =
                Hashtbl.replace Decls.value_visibility (intern (sname ^ "." ^ x)) { Decls.vis_module = sname; vis_pub = pub }
              in
              match bd with
              | T.DNewtype n ->
                  let qual = claim_con n.T.nt_name n.T.nt_pub in
                  [ record_module (bdata, T.DNewtype (spell_ctors { n with T.nt_name = qual })) ]
              | T.DType t ->
                  let qual = claim_con t.T.ta_name t.T.ta_pub in
                  [ record_module (bdata, T.DType { t with T.ta_name = qual }) ]
              | T.DLet ((bd2, b) as _bnode2) -> (
                  match snd b.T.lb_name with
                  | T.PVar x ->
                      claim_val x;
                      vis x b.T.lb_pub;
                      [ record_module (bdata, T.DLet (bd2, { b with T.lb_name = (fst b.T.lb_name, T.PVar (sname ^ "." ^ x)) })) ]
                  | _ -> type_error ("module 内の let はパターン束縛にできません: module " ^ mname))
              | T.DLetRec bs ->
                  [
                    record_module
                      ( bdata,
                        T.DLetRec
                          (List.map
                             (fun ((bd2, b) : T.let_binding) ->
                               match snd b.T.lb_name with
                               | T.PVar x ->
                                   claim_val x;
                                   vis x b.T.lb_pub;
                                   ((bd2, { b with T.lb_name = (fst b.T.lb_name, T.PVar (sname ^ "." ^ x)) }) : T.let_binding)
                               | _ -> type_error "module 内の let rec はパターン束縛にできません")
                             bs) );
                  ]
              | T.DInstance _ -> [ record_module (bdata, bd) ]
              | T.DExtern ex ->
                  claim_val ex.T.ex_name;
                  vis ex.T.ex_name ex.T.ex_pub;
                  [ record_module (bdata, T.DExtern { ex with T.ex_name = sname ^ "." ^ ex.T.ex_name }) ]
              | T.DModule _ -> noimpl "module の入れ子(M10)"
              | T.DEffect _ -> noimpl ("module 内の effect 宣言(M10): module " ^ mname)
              | T.DClass _ -> noimpl ("module 内の type class 宣言(M10): module " ^ mname)
              | T.DExp _ -> noimpl ("module 内の式文(M10): module " ^ mname))
            body
      | _ -> [ node ])
    decls

(* ## 11.43 最初の型エラーで型検査を終える

   型検査は、最初の型エラーで終了する。
   エラー回復を実装していないので、2 つ目以降のエラーは 1 つ目の影響を受けた誤ったものになりやすく、
   並べてもユーザの役に立たない。
   ただし、そこまでに確定した出力行は返す。
   そこまでの型が表示されれば、どこまで型検査に通り、どこでエラーになったかが分かる。

   型エラーの位置は、そのエラーを投げた**最も内側**の精緻化ノードの開始位置である。
   `at_node` は、位置なしの `Type_error` と `NotImplemented` にだけ span を付けて
   `Type_error_at` / `NotImplemented_at` に変え、位置つきの例外はそのまま通す。
   この規則があるので、外側の `at_node` が、内側で付けた位置を上書きすることはない。
   `at_node` で囲むのは、`elab_exp`、`elab_check`、`elab_pat`、`elab_type`、`elab_eff`、
   `elab_value_type`、`elab_binding`、`elab_rec_bindings`、`check_resume_static` と、
   newtype のフィールドのカインド検査、インスタンス本体のメソッドごとの包摂、
   `process_decls` の各パスと後処理のループ、`flatten_modules` の宣言ごとの処理である。
   このほか、handle の節の検査、effect の操作の型、クラスのメソッドの型、
   型エイリアスの本体のカインド検査、§11.45 の `check_own_clashes` も、
   それぞれのノードを `at_node` で囲む。
   宣言ごとの `at_node` が最も外側にあるので、
   その中で投げられたエラーには、少なくともその宣言の先頭の位置が付く。

   例外を型付きの返り値に変えるのは、下の `type_check` と、
   §11.44 の `catch_input_errors`、§11.45 の `type_check_units` の 3 か所である。
   どれも同じ 3 種類の例外を捕捉する(`type_check_units` はさらに `Import_error` も捕捉する)。
   `Type_error` / `Type_error_at` は終了コード 1、
   `NotImplemented` / `NotImplemented_at` は終了コード 4 になる。
   残りの 1 種類は、処理系の上限を超えたことを表す `Stack_overflow` / `Out_of_memory` で、
   型エラーと同じ終了コード 1 になる(下の `limit_error`)。
   `Syntax_error_at` を捕捉する節は置かない。
   この例外を投げるのは構文解析だけで、
   第16章の `parse_with` がそれを `Parse_error` に変えてから型検査に入るからである。
   診断は `error` レコード(位置、種別名、終了コード、本文)として返す。
   診断の整形と表示は、第16章(driver.ml)が行う。

   ## 本章が守っている不変条件

   本章が守る不変条件は、次の 5 つである。

   1. **`eff` と `level` は引数で渡す。**
      `eff` は外側の式から内側の式へ渡す。
      どちらもグローバルな状態にしない。
      そのため、レベルを元に戻し忘れるという誤りが起きない。
   2. **本体の推論で作った単一化変数を一般化してよいのは、束縛が関数か構文上の値のときだけである。**
      注釈は、単一化変数を一般化する理由にならない(§11.28)。
   3. **網羅性検査は、一般化より前にすべて処理する。**
      網羅性検査は構造的ヴァリアントの行を閉じることがあり、
      一般化の後では、その行変数が Generic になっていて単一化できない(§11.14)。
   4. **スコーレム定数は、作ったスコープの中でだけ、ほかの型と単一化できない定数として扱う。**
      スコープを出るときに `Generic` に書き換えるが、
      外へ漏れたスコーレム定数は、それより前に `unify` が検出している(§11.27)。
   5. **解決した名前は木に書く。**
      コンストラクタの引数とフィールドの対応、操作の完全な名前、節の種別を木に書き、
      評価器に同じ計算をさせない(§11.8、§11.18、§11.22)。

   第12章からは実行時の処理を扱う。
   本章が木に書き込んだ型と解決結果を、第14章の評価器がそのまま読む。 *)

(* 診断 1 つを表す。位置、種別名、終了コード、本文を持つ。
   表示の整形は第16章が行う。
   e_loc には、at_node が Type_error_at / NotImplemented_at に付けた位置が入る。
   at_node の外で投げられた例外では None になる *)
type error = { e_loc : Location.span option; e_word : string; e_exit : int; e_msg : string }

(* 型検査が処理系の上限を超えたときの診断を作る。
   診断の種別名は `処理系の限度` である。
   入れ子が深すぎる式の推論はスタックを使い切り、Stack_overflow になる。
   これは評価のエラーではなく型検査の段階で起きるので、
   実行時エラーではなく、型エラーと同じ終了コード 1 にする。
   位置は付けない。
   例外が発生した時点では、どのノードの推論が深すぎたかを示す情報が残っていないからである *)
let limit_error = function
  | Out_of_memory -> { e_loc = None; e_word = "処理系の限度"; e_exit = 1; e_msg = "型検査でメモリが不足しました" }
  | _ -> { e_loc = None; e_word = "処理系の限度"; e_exit = 1; e_msg = "型検査で再帰が深すぎます(スタックオーバーフロー)" }

let type_check ?(prelude = []) decls =
  current_out := [];
  try (type_check_decls ~prelude decls, None) with
  | Type_error_at (loc, msg) -> (List.rev !current_out, Some { e_loc = Some loc; e_word = "型エラー"; e_exit = 1; e_msg = msg })
  | Type_error msg -> (List.rev !current_out, Some { e_loc = None; e_word = "型エラー"; e_exit = 1; e_msg = msg })
  (* Syntax_error_at を捕捉する節は置かない。
     この例外を投げるのは構文解析だけで、第16章の parse_with が Parse_error に変えてから型検査に入る。
     ここに来る例外は、Type_error と、未実装の NotImplemented と、
     処理系の限度の 3 種類だけである *)
  | NotImplemented_at (loc, feat) -> (List.rev !current_out, Some { e_loc = Some loc; e_word = "未実装"; e_exit = 4; e_msg = feat })
  | NotImplemented feat -> (List.rev !current_out, Some { e_loc = None; e_word = "未実装"; e_exit = 4; e_msg = feat })
  | (Stack_overflow | Out_of_memory) as ex -> (List.rev !current_out, Some (limit_error ex))

(* ## 11.44 対話的な実行のエントリポイント

   対話的な実行(第16章)は、プレリュードを 1 回だけ処理し、その後は入力ごとに宣言を処理する。
   `start_session` は、プレリュードを処理した後の環境を返す。
   `check_input` は、渡された環境で 1 入力分の宣言を処理して、出力行と新しい環境を返す。
   型エラーと未実装は `Error` で返し、例外を外へ出さない。

   型エラーになった入力が行った書き換えを元に戻すのは、呼び出し元である。
   宣言表は第6章 §6.14 のコピーで戻し、単一化のセルは第1章 §1.5 の書き換えの記録で戻す。
   型検査の状態のうち、そのどちらにもないものは、下の `snapshot` で戻す。
   環境は不変の Map なので、呼び出し元が前の環境を持っていれば、それに戻せる。

   `toplevel_extra` は、トップレベルのエフェクト行に追加するエフェクトの名前である。
   対話的な実行は `Print` を追加し、トップレベルの `println` の出力をそのまま表示する。
   このエフェクト行に入れられるのは、プレリュードが所有する名前だけである
   (§11.30 の `Decls.prelude_owned` の検査)。 *)
let start_session ?(prelude = []) () =
  start_program ();
  check_prelude prelude

let catch_input_errors f =
  try Ok (f ()) with
  | Type_error_at (loc, msg) -> Error { e_loc = Some loc; e_word = "型エラー"; e_exit = 1; e_msg = msg }
  | Type_error msg -> Error { e_loc = None; e_word = "型エラー"; e_exit = 1; e_msg = msg }
  | NotImplemented_at (loc, feat) -> Error { e_loc = Some loc; e_word = "未実装"; e_exit = 4; e_msg = feat }
  | NotImplemented feat -> Error { e_loc = None; e_word = "未実装"; e_exit = 4; e_msg = feat }
  | (Stack_overflow | Out_of_memory) as ex -> Error (limit_error ex)

let start_input () =
  current_out := [];
  warnings := [];
  warnings_count := 0;
  Hashtbl.reset top_types;
  Unify.reset ();
  Exhaust.reset ();
  pattern_numbers := [];
  group_stack := [];
  opened_rows := []

let check_input ?(toplevel_extra = []) ?(unit = Decls.root_unit) env decls =
  start_input ();
  let emit s = current_out := s :: !current_out in
  match catch_input_errors (fun () -> check_unit ~toplevel_extra ~unit env ~emit decls) with
  | Ok env' -> Ok (List.rev !current_out, env')
  | Error e -> Error (List.rev !current_out, e)

(* 式を、let の右辺と同じように 1 つ深いレベルで推論し、let と同じ値制限で一般化した型を返す。
   対話的な実行の :type が使う。
   値でない式の型変数は一般化しないので、弱い型変数として表示される *)
let type_of_expr ?(toplevel_extra = []) env (e : T.exp) =
  start_input ();
  catch_input_errors (fun () ->
      let eff0 = toplevel_eff ~extra:toplevel_extra () in
      let mark = Unify.class_mark () in
      let t = elab_exp env 1 eff0 e in
      List.iter warn (Exhaust.drain ~level:0 ~tys:[ t ] ());
      if is_value e then (
        Unify.check_ambiguity ~all:false ~level:0 [ t ];
        Unify.generalize 0 t)
      else (
        Unify.lower_levels ~since:mark 0 t;
        Unify.check_ambiguity ~all:true ~level:0 [ t ];
        Unify.default_numerics ());
      check_pattern_numbers ();
      t)

(* 参照先の型を引く。対話的な実行が結果の表示に使う。引けるのは、
   直前の check_input の束縛だけである *)
let lookup_top_type g = Hashtbl.find_opt top_types g

(* 型検査の状態のうち、宣言表にも単一化の書き換えの記録にもないものをコピーし、
   コピーした時点の内容に戻すクロージャを返す *)
let snapshot () =
  let cells = !pub_pure_cells in
  fun () -> pub_pure_cells := cells

(* 値環境から名前の型を引く。対話的な実行が :type と結果の表示に使う *)
let lookup_value_type env x = SMap.find_opt x env.values

(* ## 11.45 ファイルの名前空間

   import のあるプログラムは、単位(ソースファイル)の並びとして型検査する。
   単位は依存される側から先に並び、最後が起点である(第16章 §16.3b)。
   各単位は、次の順に処理する。

   1. import の名前を import 先の単位の公開表で引き、import どうしの衝突を検査する。
   2. 単位の宣言を平坦化する。起点でない単位の宣言の名前には、単位の接頭辞が付く(§11.42)。
   3. import した名前と、ファイルのトップレベルの宣言の衝突を検査する。
   4. プレリュードを処理した後の環境に import した名前を追加して、単位のスコープを作る。
      値は、型と参照先を環境に追加する。
      型、コンストラクタ、エフェクト、クラスは単位の別名に登録し、
      module とクラスは修飾名の先頭の要素の表に登録する(第6章 §6.4)。
   5. `check_unit` で宣言を型検査する。
   6. 起点でない単位なら、公開表を作る。

   公開表は、ファイルのトップレベルの宣言の名前から、種類ごとの項目を引く表である。
   公開表に入るのは `pub` を付けた宣言で、`pub module` の項目は、中の `pub` の宣言を持つ。
   `pub` のない module は import できない。
   公開されていない名前と存在しない名前で診断を変えるために、
   トップレベルのすべての宣言の名前も持つ。
   値の参照先は、束縛ノードと名前から作る `GDecl` である。
   値の型は、この参照先をキーにして、型検査が記録した表(`top_types`)から引く。
   名前で環境を引くと、`pub` の束縛の後ろにある同名の非公開の束縛の型が返ってしまう。
   同名の `pub` の値が複数あれば、後のものを公開する。

   名前の衝突の規則は次のとおりである。

   - 別々の宣言を指す 2 つの import が、同じ種類の同じ名前を束縛したらエラーにする。
     同じ宣言を、別のパスや別の import 文で重ねて束縛するのは構わない。
   - import した名前と同じ種類の同じ名前を、ファイルのトップレベルで宣言したらエラーにする。
     ただし、import したクラスのメソッドの非修飾名は、トップレベルの宣言で隠せる。
   - import した型のコンストラクタも、ファイルの中でコンストラクタ名が一意であることの検査に含める。
   - 標準環境の値は、import した値とトップレベルの値が隠す。

   種類は、値、型、コンストラクタ、クラス、module の 5 つである。
   型エイリアスとエフェクトは型に含め、型と 1 つの名前空間を共有する。

   インスタンスは import で指定しない。
   どの単位で宣言したインスタンスも、宣言表の 1 つのインスタンス表から引く。
   孤児規則(§11.35)があるので、インスタンス `C[T]` を使うファイルは、
   `C` と `T` の両方の宣言に依存している。
   そのため `C[T]` の宣言は、そのファイル自身か、
   そのファイルが直接または間接に import するファイルのどこかにある。 *)

type pub_entry =
  | PValue of ty * Tree.gref
  | PType of oid * (string * oid) list (* 型の内部名と、コンストラクタの(名前, 内部名) *)
  | PEffect of oid
  | PClass of oid * (string * ty) list (* クラスの内部名と、メソッドの(名前, 型) *)
  | PModule of string * (string * pub_entry) list * string list (* 内部名、公開のメンバ、全メンバの名前 *)

type unit_table = { t_pub : (string * pub_entry) list; t_all : string list }

let public_table ~unit env (raw : T.decl list) =
  let sp = Decls.mark_spelling unit in
  (* 値は束縛ノードの参照先で引く。
     名前で引くと、pub の束縛の後ろにある同名の非公開の束縛の型が返ってしまう *)
  let value oid x =
    let g = Tree.GDecl (oid, x) in
    match Hashtbl.find_opt top_types g with Some t -> Some (PValue (t, g)) | None -> None
  in
  ignore env;
  let ctors (n : T.newtype') = match n.T.nt_rhs with T.NtCtors cs -> List.map (fun (c : T.ctor_decl) -> (c.T.cd_name, intern (sp c.T.cd_name))) cs in
  (* prefix は、module の中なら内部名の接頭辞(%3.M. など)で、トップレベルなら空である *)
  let rec scan prefix (decls : T.decl list) =
    let ty_spell x = if prefix = "" then sp x else prefix ^ x in
    let binding_entries ((_, b) as bnode : T.let_binding) =
      List.map (fun x -> (b.T.lb_pub, x, value (Tree.oid_of bnode) (prefix ^ x))) (pat_var_names b.T.lb_name)
    in
    List.concat_map
      (fun ((_, d) as node : T.decl) ->
        match d with
        | T.DLet bnode -> binding_entries bnode
        | T.DLetRec bs -> List.concat_map binding_entries bs
        | T.DExtern ex -> [ (ex.T.ex_pub, ex.T.ex_name, value (Tree.oid_of node) (prefix ^ ex.T.ex_name)) ]
        | T.DNewtype n -> [ (n.T.nt_pub, n.T.nt_name, Some (PType (intern (ty_spell n.T.nt_name), ctors n))) ]
        | T.DType t -> [ (t.T.ta_pub, t.T.ta_name, Some (PType (intern (ty_spell t.T.ta_name), []))) ]
        | T.DEffect e -> [ (e.T.ef_pub, e.T.ef_name, Some (PEffect (intern (sp e.T.ef_name)))) ]
        | T.DClass c ->
            let cs = sp c.T.cls_name in
            let methods =
              List.filter_map
                (fun (v : T.class_val) -> Option.map (fun t -> (v.T.cv_name, t)) (SMap.find_opt (cs ^ "." ^ v.T.cv_name) env.values))
                c.T.cls_vals
            in
            [ (c.T.cls_pub, c.T.cls_name, Some (PClass (intern cs, methods))) ]
        | T.DModule (pub, m, body) ->
            let sm = sp m in
            let members = scan (sm ^ ".") body in
            let pubs = List.filter_map (fun (p, x, e) -> match e with Some e when p -> Some (x, e) | _ -> None) members in
            [ (pub, m, Some (PModule (sm, pubs, List.map (fun (_, x, _) -> x) members))) ]
        | T.DInstance _ | T.DExp _ -> [])
      decls
  in
  (* 同じ名前の pub の値が 2 回宣言されていれば、後の宣言を公開する。
     ファイルの中の再束縛と同じで、後の宣言が有効になる *)
  let rec last_values = function
    | [] -> []
    | ((true, x, Some (PValue _)) as e) :: rest ->
        if List.exists (function true, y, Some (PValue _) -> y = x | _ -> false) rest then last_values rest
        else e :: last_values rest
    | e :: rest -> e :: last_values rest
  in
  let entries = last_values (scan "" raw) in
  {
    t_pub = List.filter_map (fun (p, x, e) -> match e with Some e when p -> Some (x, e) | _ -> None) entries;
    t_all = List.map (fun (_, x, _) -> x) entries;
  }

(* import 文の名前を公開表で引き、(束縛する名前, 項目, 位置) のリストを返す。
   束縛する名前は、import 文に書いたパスの最後の要素である *)
let resolve_import_names (tbl : unit_table) (im : Syntax.import_decl) =
  let src = im.Syntax.im_source in
  List.concat_map
    (fun (n : Syntax.import_name) ->
      let fail msg = raise (Import_error (n.Syntax.in_loc, msg)) in
      let pick name pubs all what =
        match List.filter (fun (y, _) -> y = name) pubs with
        | [] ->
            if List.mem name all then fail (src ^ " の " ^ what ^ " は公開されていません")
            else fail (src ^ " に " ^ what ^ " という公開の宣言はありません")
        | es -> List.map (fun (_, e) -> (name, e, n.Syntax.in_loc)) es
      in
      match n.Syntax.in_path with
      | [ x ] -> pick x tbl.t_pub tbl.t_all x
      | [ m; x ] -> (
          match List.find_map (fun (y, e) -> match e with PModule (_, ms, all) when y = m -> Some (ms, all) | _ -> None) tbl.t_pub with
          | None ->
              if List.mem m tbl.t_all then fail (src ^ " の " ^ m ^ " は公開されていません")
              else fail (src ^ " に " ^ m ^ " という公開の宣言はありません")
          | Some (ms, all) -> pick x ms all (m ^ "." ^ x))
      | _ -> bug "import の名前は 2 段まで")
    im.Syntax.im_names

type import_kind = KValue | KType | KCtor | KClass | KModule

let gref_key = function
  | Tree.GBuiltin s -> "b:" ^ s
  | Tree.GMethod q -> "m:" ^ q
  | Tree.GDecl (o, x) -> "d:" ^ string_of_int o ^ ":" ^ x

(* import した名前を種類ごとに記録し、import どうしの衝突を検査する。
   表は、(種類, 名前) から (宣言のキー, import 元, 所属) を引く。
   所属は、コンストラクタでは型の名前、クラスのメソッドでは method で、それ以外は空である *)
let import_claims binds =
  let seen : (import_kind * string, string * string * string) Hashtbl.t = Hashtbl.create 16 in
  let claim loc src kind name key owner =
    match Hashtbl.find_opt seen (kind, name) with
    | Some (k, _, _) when k = key -> ()
    | Some (_, src0, _) -> raise (Import_error (loc, name ^ " は " ^ src0 ^ " からも import しています(別の宣言です)"))
    | None -> Hashtbl.replace seen (kind, name) (key, src, owner)
  in
  let claim_ctors loc src owner cs = List.iter (fun (c, o) -> claim loc src KCtor c (name_of o) owner) cs in
  List.iter
    (fun (x, e, loc, src) ->
      match e with
      | PValue (_, g) -> claim loc src KValue x (gref_key g) ""
      | PType (o, cs) ->
          claim loc src KType x (name_of o) "";
          claim_ctors loc src x cs
      | PEffect o -> claim loc src KType x (name_of o) ""
      | PClass (o, methods) ->
          claim loc src KClass x (name_of o) "";
          (* メソッドの非修飾名も値の名前として記録する。
             同じファイルで 2 つのクラスに同名のメソッドを宣言できないのと同じく、
             別々のクラスの同名のメソッドや、メソッドと同名の値は import できない。
             トップレベルの宣言は、同じファイルで宣言したクラスのメソッドの場合と同じく、
             import したクラスのメソッドの非修飾名を隠せる *)
          List.iter (fun (m, _) -> claim loc src KValue m ("m:" ^ name_of o ^ "." ^ m) "method") methods
      | PModule (sm, members, _) ->
          claim loc src KModule x sm "";
          List.iter
            (fun (y, e) ->
              match e with
              | PType (o, cs) ->
                  (* module と同名の型(コンパニオン型)は、module 名で型として引ける *)
                  if y = x then claim loc src KType x (name_of o) "";
                  claim_ctors loc src y cs
              | _ -> ())
            members)
    binds;
  seen

(* ファイルのトップレベルの宣言が、import した名前と衝突していないことを検査する *)
let check_own_clashes seen (raw : T.decl list) =
  let clash kind name =
    match Hashtbl.find_opt seen (kind, name) with
    | Some (_, _, "method") -> ()
    | Some _ -> type_error (name ^ " は import した名前と同じです")
    | None -> ()
  in
  let clash_ctors (n : T.newtype') =
    match n.T.nt_rhs with
    | T.NtCtors cs ->
        List.iter
          (fun (c : T.ctor_decl) ->
            match Hashtbl.find_opt seen (KCtor, c.T.cd_name) with
            | Some (_, _, owner) ->
                type_error ("コンストラクタ " ^ c.T.cd_name ^ " は import した型 " ^ owner ^ " のコンストラクタと同じ名前です")
            | None -> ())
          cs
  in
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      match d with
      | T.DLet (_, b) -> List.iter (clash KValue) (pat_var_names b.T.lb_name)
      | T.DLetRec bs -> List.iter (fun ((_, b) : T.let_binding) -> List.iter (clash KValue) (pat_var_names b.T.lb_name)) bs
      | T.DExtern ex -> clash KValue ex.T.ex_name
      | T.DNewtype n ->
          clash KType n.T.nt_name;
          clash_ctors n
      | T.DType t -> clash KType t.T.ta_name
      | T.DEffect e -> clash KType e.T.ef_name
      | T.DClass c -> clash KClass c.T.cls_name
      | T.DModule (_, m, body) ->
          clash KModule m;
          List.iter (fun ((_, d) : T.decl) -> match d with T.DNewtype n -> clash_ctors n | _ -> ()) body
      | T.DInstance _ | T.DExp _ -> ())
    raw

(* import した名前を単位のスコープに登録する *)
let apply_imports ~unit env binds =
  let syn tbl x o = Hashtbl.replace tbl (unit, intern x) o in
  let ctors cs = List.iter (fun (c, o) -> syn Decls.unit_ctors c o) cs in
  List.fold_left
    (fun env (x, e, _, _) ->
      match e with
      | PValue (t, g) -> add_top env x t g
      | PType (o, cs) ->
          syn Decls.unit_synonyms x o;
          ctors cs;
          env
      | PEffect o ->
          syn Decls.unit_synonyms x o;
          env
      | PClass (o, methods) ->
          let q = name_of o in
          syn Decls.unit_classes x o;
          Hashtbl.replace Decls.unit_qualifiers (unit, x) q;
          (* メソッドは修飾名と非修飾名の両方で引ける。
             非修飾名は、同じ名前が環境になければ登録する(§11.39 のパス 1b と同じ) *)
          List.fold_left
            (fun env (m, t) ->
              let g = Tree.GMethod (q ^ "." ^ m) in
              let env = add_top env (q ^ "." ^ m) t g in
              if SMap.mem m env.values then env else add_top env m t g)
            env methods
      | PModule (sm, members, _) ->
          Hashtbl.replace Decls.unit_qualifiers (unit, x) sm;
          List.fold_left
            (fun env (y, e) ->
              match e with
              | PValue (t, g) -> add_top env (sm ^ "." ^ y) t g
              | PType (o, cs) ->
                  (* module と同名の型(コンパニオン型)は、module 名だけで型として引ける *)
                  if y = x then syn Decls.unit_synonyms x o;
                  ctors cs;
                  env
              | _ -> env)
            env members)
    env binds

type src_unit = {
  su_id : Decls.unit_id;
  su_imports : (Syntax.import_decl * Decls.unit_id) list; (* import 文と、その解決先の単位 *)
  su_decls : T.decl list;
}

(* 単位の並びを型検査し、(出力行, エラー, 平坦化した単位ごとの宣言の並び) を返す。
   束縛の行は起点のものだけを出力し、警告はどの単位のものも出力する *)
let type_check_units ~prelude (units : src_unit list) =
  current_out := [];
  let out = current_out in
  let emit_all s = out := s :: !out in
  (* 起点でない単位の警告には、先頭にファイルのパスを付ける。
     警告は位置を持たないので、どのファイルの警告かをこれで示す *)
  let emit_warnings unit = function
    | Warning w -> emit_all (Warning (Decls.unit_path unit ^ ": " ^ w))
    | Binding _ -> ()
  in
  let tables : (Decls.unit_id, unit_table) Hashtbl.t = Hashtbl.create 8 in
  let flat = ref [] in
  let fail e = (List.rev !out, Some e, List.rev !flat) in
  try
    start_program ();
    let env_std = check_prelude prelude in
    List.iter
      (fun su ->
        let unit = su.su_id in
        let binds =
          List.concat_map
            (fun ((im : Syntax.import_decl), target) ->
              List.map (fun (x, e, loc) -> (x, e, loc, im.Syntax.im_source)) (resolve_import_names (Hashtbl.find tables target) im))
            su.su_imports
        in
        let seen = import_claims binds in
        let imported_vals = List.filter_map (function x, PValue _, _, _ -> Some x | _ -> None) binds in
        let imported_types = List.filter_map (function x, (PType _ | PEffect _), _, _ -> Some x | _ -> None) binds in
        let decls = flatten_modules ~imported_vals ~imported_types ~unit su.su_decls in
        check_own_clashes seen su.su_decls;
        let env = apply_imports ~unit env_std binds in
        let emit = if unit = Decls.root_unit then emit_all else emit_warnings unit in
        let env' = check_unit ~unit env ~emit decls in
        if unit <> Decls.root_unit then Hashtbl.replace tables unit (public_table ~unit env' su.su_decls);
        flat := decls :: !flat)
      units;
    (List.rev !out, None, List.rev !flat)
  with
  | Type_error_at (loc, msg) -> fail { e_loc = Some loc; e_word = "型エラー"; e_exit = 1; e_msg = msg }
  | Type_error msg -> fail { e_loc = None; e_word = "型エラー"; e_exit = 1; e_msg = msg }
  | Import_error (loc, msg) -> fail { e_loc = Some loc; e_word = "import エラー"; e_exit = 1; e_msg = msg }
  | NotImplemented_at (loc, feat) -> fail { e_loc = Some loc; e_word = "未実装"; e_exit = 4; e_msg = feat }
  | NotImplemented feat -> fail { e_loc = None; e_word = "未実装"; e_exit = 4; e_msg = feat }
  | (Stack_overflow | Out_of_memory) as ex -> fail (limit_error ex)

let () = Show.unit_label := fun o -> Decls.unit_path (Decls.entity_unit o)
