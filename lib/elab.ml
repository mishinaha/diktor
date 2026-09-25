(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第11章 型推論の本体

   本章は Keleut の型検査器を実装する。
   第5章(tree.ml)が用意した精緻化木を受け取り、
   ノードごとに型と解決結果を書き込みながら、第8章(unify.ml)の単一化を呼ぶ。
   名前と宣言の表は第6章(decls.ml)、演算子とランタイムエフェクトの表は第7章(prims.ml)、
   網羅性検査の遅延キューは第10章(exhaust.ml)のものを使う。
   本章が出力するのは、型と解決結果を書き込んだ木である。
   第14章(interp.ml)はその木をたどって評価する。

   本章の関数は、次の 3 つの約束を一貫して守る。

   - eff は下向きに渡す。
     エフェクトの集合を戻り値で持ち上げるのではなく、
     その場所で許されているエフェクト行を引数で配る。
     perform に出会ったら、その行と 1 回単一化するだけで済む。
   - level は常に引数で渡し、大域変数にしない。
     レベルを大域変数に置くと、例外で脱出するたびに元の値へ戻す後始末が要る。
     引数で渡せば、型エラーで大域脱出しても、レベルを戻し損ねることが起こりえない。
   - 推論の結果は木に書く。
     `elab_exp` は型を返すと同時に `set_ty` でノードに型を書き込み、
     コンストラクタ、操作、節の解決結果を `set_resolved` で書き込む。
     評価器はこの解決結果を読むので、名前解決をやり直さない。

   ## 宣言処理のパス構成

   トップレベルの宣言は、1 回の走査では処理しきれない。
   前方参照(sample.kel:456 の `user_names` が後方の `println`(:508)を呼ぶ)と、
   宣言どうしの相互再帰を通すために、宣言列を 4 回走査する。

   | パス | 登録するもの | 独立のパスにする理由 |
   |---|---|---|
   | 1a | エイリアスの表、newtype の頭(名前とカインド) | 型の本体を書く前に、すべての型構成子のカインドを引けるようにする |
   | 1a′ | (登録しない)newtype の本体の投機 | パラメータのカインドを宣言順に依存せず決める |
   | 1b | newtype のコンストラクタ、effect の操作、class のメソッド | 型の本体を書くのでカインドの表が要る。投機が相手のパラメータのカインドを決められない形(§11.31)を除き、宣言順に依存しない |
   | 1c | インスタンスの頭、前方参照できる let の署名 | 頭の検査にクラス表が要る。署名は前方参照に使う |
   | 2 | let / let rec / 式 / extern / インスタンス本体 | 本体を宣言順に推論し、順に型を印字する |

   1a〜1c は宣言の表を埋めるパス、2 は本体を推論するパスである。
   1a′ は独立のパスではなく 1a の後始末で、宣言の表には何も登録しない(§11.39)。
   1b の後にも、同じ形の後始末が 2 つ走る。
   1c が署名を登録するのは、引数と返り値に注釈があり、
   束縛の最外の `@` が省略されていない(または `pub` の)let だけである。
   それ以外の let は登録しないので、その let を参照できるかどうかは宣言順に依存する。
   この線をどこに引くかは §11.36 で述べる。

   ## 主要関数の一覧

   | 関数 | 役目 |
   |---|---|
   | `elab_type` / `elab_eff` | 表層の型式から内部型 / エフェクト行を作る。展開とカインド検査を含む |
   | `expand_alias` | エイリアスの透過展開。非再帰と部分適用の禁止をここで守る |
   | `elab_pat` | パターンを期待型に対して検査し、単相の束縛を足した環境を返す |
   | `is_value` | 値制限の構文判定 |
   | `elab_exp` / `elab_exp'` | 式の型を推論し、木に型を書き込む |
   | `elab_check` | 軽い検査モード。ラムダと引数レコードにだけ期待型を押し込む |
   | `resolve_perform` | 操作名から(エフェクト, 操作, スキーマ)を引く。修飾なしの名前は行の最左を優先する |
   | `at_node` | 位置なしの型エラーに、最も内側のノードの span を付ける |
   | `check_resume_static` | resume が第二級であることの構文検査 |
   | `elab_handle` | handle の節の分類、対象エフェクトの決定、型付け |
   | `elab_binding` / `elab_rec_bindings` | let / let rec。Rigid の生成と解放 |
   | `make_rigids` / `open_explicit_eff` / `release_rigids` | 注釈の skolem 化の 3 つの手順 |
   | `register_newtype` ほか `register_*` | パス 1 の宣言登録 |
   | `fully_effected` / `check_pub_annots` | pub の完全注釈検査 |
   | `signature_of_binding` | パス 1c の前方参照の署名 |
   | `check_instance_bodies` | インスタンス本体の包摂検査 |
   | `process_decls` / `type_check_decls` / `type_check` | 入口 |
   | `flatten_modules` | module の平坦化 |

   本章で繰り返し現れる形は多くない。
   代表的なのは、§11.17 と §11.28 に出てくる次の 3 つの手順である。

   1. レベルを上げる。
   2. 剛定数を作る。
   3. 出口で剛定数が漏れていないかを調べる。 *)

open Aux
open Syntax
open Type
module T = Tree.Tree
module SMap = Map.Make (String)

(* ## 11.1 環境の 3 つのフィールド

   環境は不変の Map で、値として渡す。
   enter / leave のような破壊的なスコープ操作を持たないので、
   スコープを戻し忘れる誤りが起こりえない。
   型エラーで大域脱出しても、呼び出し元が持っている env は変わらない。

   環境のフィールドは 3 つある。
   `values` は変数の型を持つ。
   Generic を含む型がそのまま型スキーマの役を果たし、型スキーマ専用のデータ型は持たない。
   `types` は型パラメータの束縛を持ち、リージョン変数 `h` もここに載る。
   `resume_ty` は、操作節の中でだけ Some になる 2 つ組である。

   resume は第一級の値ではないので、`values` には入れず、
   その型付けに要る型を env の `resume_ty` に置く。
   この設計の代償は §11.21 で述べる。

   警告は溜めておき、後で印字する。
   `current_out` は、型エラーで打ち切られるまでに確定した出力行を持つ。
   型エラーで打ち切られたときは、入口の `type_check`(§11.43)がここまでの行をエラーと一緒に返し、
   第16章のドライバがそれを印字する。

   `closed_item_row` は、引数の型のリストを閉じた `_item` 行に畳むだけの補助関数である。
   関数適用(§11.12)の引数の個数の不一致は、すべてこの閉じた行の単一化が検出する。
   適用の引数を数える専用の検査はない。 *)

type env = {
  values : ty SMap.t;
  types : ty SMap.t; (* 型パラメータの束縛(リージョン変数 h を含む) *)
  resume_ty : (ty * ty) option; (* (操作の返り値型, handle 式全体の型)。操作節の中でだけ Some *)
}

let warnings : string list ref = ref []

let warnings_count = ref 0

(* 先頭に積み、読む側が向きを戻す。末尾に @ で足すと、警告の数の二乗の時間がかかる *)
let warn msg =
  warnings := msg :: !warnings;
  incr warnings_count

(* 出力の 1 行。種別を値で持つ。⚠ の前置などの整形は第16章が受け持ち、
   表示文字列を調べて種別を推測することはしない *)
type out_line = Binding of string | Warning of string

(* 型エラーで打ち切られるまでの出力行(エラー時にもドライバが印字する) *)
let current_out : out_line list ref = ref []

let closed_item_row tys = List.fold_right (fun t acc -> TRowExtend (l_item, t, acc)) tys TRowEmpty

(* 位置なしの Type_error に、例外を投げた最も内側のノードの span を付ける。
   位置つきの Type_error_at は素通りするので、外側の at_node が位置を上書きすることはない。
   最後に訪れたノードを大域変数に持つ方法は採らない。
   eff を下向きに渡し、level を引数で渡すのと同じく、診断でも大域状態を持たないためである *)
let at_node node f =
  try f () with
  | Type_error msg -> raise (Type_error_at (Tree.loc_of node, msg))
  | NotImplemented feat -> raise (NotImplemented_at (Tree.loc_of node, feat))

(* ## 11.2 数値リテラルの型

   Keleut は Int32 / Int64 / Float64 の 3 つの数値型を持つので、
   接尾辞のない `1` の型はその場では決められない。
   Diktor は整数リテラルの型を新しい型変数とし、
   その変数に予約述語 `Integral` をクラス制約として付ける。
   浮動小数のリテラルには、同じく予約述語の `Fractional` を付ける。

   専用のリテラル型も、専用の遅延解決のフェーズも作らない。
   予約述語は、型変数に付いたクラス制約の集合(第8章の `add_class` がすでに扱っているもの)に、
   普通のクラス制約と一緒に入れるだけである。
   たとえば `1 + x` では、`{Integral, Add}` の 2 つの制約が同じ変数に付き、
   単一化のたびに両方が伝播する。
   リテラルの述語のための仕組みを別に持たなくても、既定化とクラスの解決は正しく整合する。

   接尾辞が付いていれば具体型にする。
   Diktor が実行できる数値型は 3 つだけなので、それ以外の幅の接尾辞と型名は、
   構文としては受理したうえで未実装のエラーにする。
   黙って別の幅に丸めることはしない。

   残った `Integral` / `Fractional` は、
   宣言の終わりに `default_numerics` が Int32 / Float64 に落とす(第8章)。
   既定化が表示より先に走るので、通常の型表示にこれらの述語は現れない。 *)

let number_ty level (n : number) : ty =
  match n.n_suffix with
  (* 浮動小数の本体に整数接尾辞が付いたリテラル(1.i32 / 1e3i64)は拒否する。受理すると、
     実行時の Int32.of_string が本体を読めず、型検査を通ったリテラルが実行時に必ず落ちる *)
  | Some (NsInt _ | NsUInt _) when n.n_is_float ->
      type_error ("数値リテラル " ^ Lexer.show_number n ^ " は浮動小数の本体に整数接尾辞が付いています")
  | Some (NsInt 32) -> t_int32
  | Some (NsInt 64) -> t_int64
  | Some (NsFloat 64) -> t_float64
  | Some _ -> noimpl ("数値接尾辞 " ^ Lexer.show_number n ^ "(v0 は i32/i64/f64 のみ)")
  | None ->
      let v = new_var level in
      Unify.add_class v (if n.n_is_float then cls_fractional else cls_integral);
      v

(* 名前だけを受理し、Diktor では実行できない数値型 *)
let unsupported_numeric = [ "Int8"; "Int16"; "UInt8"; "UInt16"; "UInt32"; "UInt64"; "Float32" ]

(* 未束縛の変数の診断。module スコープで解決済みなのに環境に届かないとき
   (前方の module 名)は素の文言にし、スコープ外に候補があるときだけ修飾名を案内する *)
let unbound_value name scoped =
  match scoped with
  | Some _ -> type_error ("未束縛の変数: " ^ name)
  | None -> (
      (* 候補に挙げるのは pub の名前だけ。非 pub の名前を案内すると、そのとおりに書いても
         可視性のエラーになり、従っても直らない助言になる *)
      let pub_only qs =
        List.filter
          (fun q -> match Hashtbl.find_opt Decls.value_visibility q with Some v -> v.Decls.vis_pub | None -> true)
          qs
      in
      match pub_only (Decls.val_synonym_candidates (intern name)) with
      | [] -> type_error ("未束縛の変数: " ^ name)
      | qs ->
          type_error ("未束縛の変数: " ^ name ^ "(" ^ String.concat " か " (List.map name_of qs) ^ " と修飾してください)"))

(* 構文的に反駁できないパターンかどうか。
   関数の引数と return 節の網羅性検査では、
   警告が出ないと分かっている形を queue に積まないための節約に使う。
   この用途では、判定が厳しすぎても安全側に倒れる(queue が正しく判定する)。
   操作節の総和性の検査(§11.23)も同じ判定を使い、そこでは厳しすぎる判定が、
   取りこぼさない節を拒否する側に倒れる。
   newtype Box = MkBox(Int32) と、引数が Box の操作 ask があるとき、
   ask の節が case ask(MkBox(n)) だけのハンドラは、コンストラクタが 1 つしかなくても拒否される *)
let rec irrefutable_pat ((_, p) : T.pat) =
  match p with
  | T.PVar _ | T.PWildcard -> true
  | T.PAnnot (q, _) -> irrefutable_pat q
  | T.PRecord (fields, rest) ->
      List.for_all (fun (_, q) -> irrefutable_pat q) fields
      && (match rest with None -> true | Some rp -> irrefutable_pat rp)
  | T.PCtor _ | T.PVariant _ | T.PBool _ | T.PNumber _ | T.PText _ -> false

(* pub で @ を省略した宣言の、本体の行(Rigid)の vid。
   perform や関数呼び出し(§11.12)がこの行と衝突したとき、単一化の一般的な文言ではなく、
   pub の規則を名指しして案内するため *)
let pub_pure_rows : (oid, unit) Hashtbl.t = Hashtbl.create 8

(* 失敗が行の単一化に由来するかどうか(エラー文言を言い換えるかどうかの判定)。
   引数の型の不一致まで、仕様 §9 の行の話にしないために使う。
   pub の言い換え(§11.12、§11.28)、入れ子の省略 @ の言い換え(§11.12、§11.18)、
   インスタンスメソッドの純粋性の言い換え(§11.38)が共用する *)
let row_failure msg =
  let has sub s =
    let n = String.length sub and m = String.length s in
    let rec go i = i + n <= m && (String.sub s i n = sub || go (i + 1)) in
    go 0
  in
  has "行型ではありません" msg || has "スコープ付きの型" msg || has "ラベル " msg || has "は注釈で固定された行変数" msg

(* @ を省略した let で本体が純粋だと分かったものは、公開するときに本体の行を行変数へ開き直す。
   仕様 §9 の表は、let について
   「本体から推論する。本体が純粋なら行変数として一般化するので、どこからでも呼べる」と定める。
   行が空に固まるのは、本体が @ {} の関数(入れ子の省略 @ を含む)を呼んだときだけである。
   何も呼ばなければ行変数のまま残るので、この後処理が要るのはその場合に限る。
   純粋な関数にどんな行を名乗らせても、起こすエフェクトは増えないので健全である
   (open_explicit_eff がラベル付きの行に対して行うことの、空の行の版にあたる)。
   注釈で @ {} と書いたときは開かず、呼び出し側にも純粋を要求する意図を残す
   (仕様 §9「@ {} だけは両方向に効く」)。
   矢印そのものを組み直すので、Tree.set_ty より前に呼ぶ *)
let reopen_pure_row level ty =
  match repr ty with TArrow (a, r, e) when repr e = TRowEmpty -> TArrow (a, r, new_row_var level) | _ -> ty

(* 最外の @ が書かれているか(reopen_pure_row で開き直すかどうかの判定)。
   関数束縛は lb_eff を見る。値束縛は、注釈の頭が矢印リテラルならその @ を見る。
   頭が矢印リテラルでない注釈(型エイリアスなど)では、展開先の矢印を入れ子として読むので、
   省略した @ は @ {}(両方向に効く)になる。
   そこでこの形は @ が書かれている側に倒し、開き直さない。
   1c の署名(§11.37)も同じ閉じた行を作るので、結果は宣言順に依存しない *)
let outer_eff_written (b : T.let_binding') =
  match b.T.lb_params with
  | Some _ -> b.T.lb_eff <> None
  | None -> ( match b.T.lb_ret with Some (_, T.EArrow (_, _, eff)) -> eff <> None | Some _ -> true | None -> false)

(* 注釈の中のすべての矢印に @ が明示されているか。pub の完全注釈検査
   (check_pub_annots と、§11.31 の pub newtype のフィールド)が使う。
   パス 1c の前方参照の署名は、頭の矢印だけを見る別の判定を使う(§11.36) *)
let rec fully_effected ((_, te) : T.type_exp) =
  match te with
  | T.EArrow (params, ret, eff) -> eff <> None && List.for_all fully_effected params && fully_effected ret
  | T.EApply (f, args) -> fully_effected f && List.for_all fully_effected args
  | T.EBraceRow (elems, ext) ->
      List.for_all
        (function T.BField (_, t) -> fully_effected t | T.BLabel (_, ts) -> List.for_all fully_effected ts)
        elems
      && (match ext with Some t -> fully_effected t | None -> true)
  | T.EVariantCase (_, Some t) -> fully_effected t
  | T.EUnion ts -> List.for_all fully_effected ts
  | T.EVariantCase (_, None) | T.EIdent _ | T.EHole -> true

(* pub の完全注釈検査。引数と返り値に注釈があるだけでなく、注釈の中の矢印にも @ が要る。
   入れ子の矢印の省略 @ は @ {} と読むので、この規則は健全性のためのものではない。
   仕様 §13(sample.kel:815-821)が可読性のために定めた規則で、
   公開 API では、純粋を意図したのか書き忘れたのかを読み手が区別できなければならない。
   pub newtype のフィールド(§11.31)にも同じ規則が掛かる(sample.kel:818-819)。

   値束縛(引数リストを持たない `let`)の注釈の頭の矢印は、この「中の矢印」に入らない。
   頭は束縛の最外だからである。
   仕様 §9 は、「最外の矢印」の指す先を関数束縛と値束縛で書き分けている(sample.kel:484-485)。
   仕様 §13 は入れ子の矢印の `@` も省略できないと定め(sample.kel:815)、
   最外の省略には別の意味を与えている(sample.kel:820-821)。
   本体に純粋を要求し、公開する型を行多相にするという意味である。
   値束縛の頭の矢印も同じ扱いであることは、仕様 §9 の表が定めている(:492)。

   `fully_effected_value_head` と `fully_effected` の違いは、値束縛の頭の矢印の扱いだけである。
   頭が矢印リテラルなら、引数と返り値だけを検査し、頭の `@` の有無は問わない。
   頭が矢印でない注釈(型エイリアスなど)には最外の矢印が無いので、そのまま `fully_effected` に渡す。
   関数束縛の `lb_ret` は返り値の型、つまり入れ子の位置なので、すべての矢印に `@` が要る。

   頭を数えずに済むのは、頭の省略に意味を与える分岐を持つ呼び出し側だけである。
   `let` の値束縛(§11.28)はその分岐を持つが、`let rec` の値束縛は持たない。
   その分岐は、群が Rigid の行を 1 本共有する設計(§11.29)と噛み合わないからである。
   そこで `value_head_outer` を呼び出し側から受け取り、`let rec` では頭にも `@` を要求する。
   ここをまとめて緩めると、`pub let rec k: (Int32) => Int32 = …` が、
   本体の純粋性を問われないまま行多相として公開される。 *)
let fully_effected_value_head ((_, te) as t : T.type_exp) =
  match te with
  | T.EArrow (params, ret, _) -> List.for_all fully_effected params && fully_effected ret
  | _ -> fully_effected t

let check_pub_annots ~value_head_outer ~params ~ret =
  (match params with
  | Some ps ->
      List.iter
        (fun ((_, p) : T.pat) ->
          match p with
          | T.PAnnot (_, te) ->
              if not (fully_effected te) then
                type_error "pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)"
          | _ -> type_error "pub な宣言には完全な型注釈が必要です(引数に型注釈がありません)")
        ps
  | None -> ());
  match ret with
  | None -> type_error "pub な宣言には完全な型注釈が必要です(返り値の型注釈がありません)"
  | Some te ->
      let ok = match params with None when value_head_outer -> fully_effected_value_head te | _ -> fully_effected te in
      if not ok then type_error "pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)"

(* ## 11.3 型式の精緻化

   `elab_type` は表層の型式を第1章の内部型に変換する。
   名前解決、エイリアスの展開、カインドの検査をここで同時に行い、
   カインド検査のための専用のパスは持たない。
   型構成子の適用では、宣言されたパラメータのカインドに合わせて型引数を読み分け、
   読んだ結果のカインドを照合する(`elab_con_args`)。
   行カインドのパラメータの位置ではエフェクト行として読むので、
   `Callback[{}]` の `{}` は空の行、`Callback[{Print}]` はラベル 1 つの閉じた行、
   `Callback[{Print extends E}]` は開いた行になる。
   それ以外の位置では型として読み、`{}` は Unit になる。
   `Box[E]` に行変数を渡すと、使用点で `bind` が内部名を並べて落ちるのではなく、
   宣言のその場で「Type を期待しましたが ς1 は Row です」と落ちる(`test/kinds.t` の kinderr)。

   この読み分けは仕様 §6 が定める規則である(sample.kel:252-255)。
   読み分けが無いと、`pub let mk(): Callback[{}]` が書けない。
   仕様 §13 は `pub` の型注釈を完全に書くことを要求するので、
   `Callback[{}]` と書く手段が無ければ、`Callback` を公開 API に出せなくなる。
   同じ `{}` が、`Callback[{}]` では空の行、`Box[{}]` では Unit になる。
   この違いは印字では見分けられず、値を入れて初めて見える(`test/kinds.t` の rowarg)。

   読み分けの判定には `kind_repr` の構造の一致を使い、照合には `same_kind` を使う。
   カインドは原則として `same_kind` で比べる(第1章 §1.6)が、読み分けの判定はその例外である。
   `same_kind` は `KVar` を張るので、判定に使うと、
   未確定のパラメータがすべて `Row` に固定されてしまう。
   同じ理由で `same_kind` を避ける箇所は、ほかに第6章 §6.4b の `kind_equiv` と、
   §11.6 の `elab_eff` の最後の分岐にある。
   照合の側が `KVar` を張るのはむしろ望ましい。
   パス 1b の中(相互再帰する newtype が互いを参照する形)では、これがカインドの伝播路として働く。

   名前は次の優先順位で引く。

   1. `env.types` にある名前。型パラメータとリージョン変数で、これが最優先である。
      内側の `[A]` は外側の型構成子 `A` を隠す。
   2. 型エイリアス。あれば、その場で展開する(§11.5)。
   3. 宣言表の型構成子。カインドを引いて引数の個数を照合し、
      パラメータのカインドで引数を読み分けて照合する。

   `elab_type` は、型構成子とエイリアスの名前を必ず `Decls.resolve_con` を通して引く。
   module の平坦化(§11.42)の同義語表を引くためである。
   `module Parser` の中で `Parser` と書いても、外から `Parser.Parser` と書いても、
   同じ oid に行き着く。

   `EApply` の頭が型パラメータのときだけは扱いが違う。
   `tapp` で適用を組み立て、カインドは使用時に `kind_of` と `drop_arrows` が決める。
   高階カインド(`F[_]`)の実装は、ほぼこれだけである。
   型レベルのλを持たないので、`f a ~ List Int` は `f ~ List, a ~ Int` に構造的に分解でき、
   単一化は一階のままで済む。
   高階カインドの実装にほかに要るのは、定義域の照合だけである。
   `TCon` の適用は宣言表のカインドと照合するが、
   `TApp` の適用は頭のカインド(`kind_of` が張った `KArrow` の左)と照合する。
   `drop_arrows` は定義域を捨てるので、定義域はここでしか照合できない。
   `let f[F[_], E](x: F[E], g: () => Unit @ E)` では、
   `F[E]` が `E` のカインドを Type に確定させるので、
   宣言は次の `@ E` で落ちる。
   診断の位置が 2 番目の使用点になるのは、`F[E]` の時点では `E` のカインドがまだ決まっておらず、
   照合が通るからである(`test/kinds.t` の hkt)。

   `unsupported_numeric` にある名前は、ここで未実装の数値型として拒否する。
   `Int8` のような名前は、未知の型として報告するより、
   Diktor が実装していない数値型として報告するほうが、利用者が原因を理解しやすい。

   値の型の位置で読んだ型は、カインドが `Type` であることも照合する。

   **値の型の位置**：矢印の引数と返り値、レコードのフィールド、タプルの要素、ヴァリアントの積載、
   および引数の注釈、返り値の注釈、値束縛の注釈。

   照合は `elab_value_type` が `elab_type` の結果に対して行う。
   引数と返り値の注釈も、この `elab_value_type` で読む。
   引数リストを持たない値束縛の注釈だけは `elab_value_type_outer` で読む。
   こちらは最外の省略 `@` を行変数にする `elab_type_outer` で読んでから、同じ照合を掛ける。
   合わなければ、`check_value_kind` が型エラーにする。
   文面は「… の型のカインドが Type ではありません: <型> :: <カインド>」である。
   この照合が無いと、newtype のフィールドの最外の照合(§11.31)だけが残り、
   1 段でも内側に包んだ位置にある行カインドの型パラメータや `EffectRow` エイリアスが、
   値の型のまま宣言表に入る。
   `newtype Bad2[E] = Bad2((E, Int32), () => Unit @ E)` がその例である。
   値の位置に行がある型は値を作る手段が無いので、診断が使用点まで遅れ、
   使用点が無ければ診断が出ない。

   照合には `same_kind` を使う。
   裸のパラメータが 1 つだけの位置(`let f[A](x: A)`)では、`A` のカインドはまだ `KVar` なので、
   照合は、値の位置に現れたことから `A` のカインドを `Type` と推論する働きをする。
   この副作用が診断の位置を決める。
   同じパラメータを行と値の両方で使う宣言では、先に読んだ側がカインドを決め、
   2 番目の使用点で落ちる(§11.4)。

   文面の「… の型」に入る名詞句は位置ごとに違うので、`check_value_kind` の引数として渡す。
   newtype のフィールドの最外の検査もこの補助関数を呼び、
   名詞句にコンストラクタ名を添えて「コンストラクタ X のフィールドの型」とする(§11.31)。
   `test/kinds.t` の valkind / annotkind / rowval / hktval / fieldkind / fieldalias が、
   8 種類の名詞句と落ちる位置を固定している。 *)

(* 値の型の位置とエフェクト位置のカインド照合が共用する診断。what は「… の型」で終わる名詞句。
   カインドの併記を落とす分岐があるのは、未確定の KVar を ?k997 の形で印字すると、
   番号がプレリュードの行数で変わるためである。
   値の型の位置の照合は same_kind なので、KVar は張られて通り、この分岐には届かない。
   届くのは構造の一致で判定するエフェクト位置だけだが、文面を 1 か所に揃えておく *)
let kind_error what ~expected ty =
  let k = kind_repr (Unify.kind_of ty) in
  let annot = match k with KVar _ -> "" | _ -> " :: " ^ show_kind k in
  type_error (what ^ "のカインドが " ^ expected ^ " ではありません: " ^ Show.show ty ^ annot)

let check_value_kind what ty = if not (same_kind (Unify.kind_of ty) KStar) then kind_error what ~expected:"Type" ty

(* newtype の本体の投機(§11.31)の最中だけ真。
   型引数の読み分け(elab_con_args)がこれを見て、型としても行としても読める字面を飛ばす *)
let speculating = ref false

let rec elab_type env level ~expanding ?(outer = false) (((_, te) as t) : T.type_exp) : ty =
  (* 内部の再帰にも at_node を掛ける。入口だけを包むと、入れ子の注釈のどこで落ちても、
     注釈全体の先頭が診断の位置になってしまう *)
  at_node t @@ fun () ->
  match te with
  | T.EIdent (LongId [ n ]) -> (
      match SMap.find_opt n env.types with
      | Some t -> t
      | None ->
          if List.mem n unsupported_numeric then noimpl ("数値型 " ^ n ^ "(v0 は Int32/Int64/Float64 のみ)")
          else
            let oid = Decls.resolve_con (intern n) in
            Decls.check_con_visible oid;
            (match Hashtbl.find_opt Decls.aliases oid with
            | Some info -> expand_alias env level ~expanding info []
            | None ->
                if Hashtbl.mem Decls.con_kinds oid then (
                  match Decls.con_kind oid 0 with
                  | KStar -> TCon (oid, [])
                  | _ -> type_error ("型構成子 " ^ n ^ " には型引数が必要です"))
                else
                  (* スコープ外の module の内部型なら候補を添える。
                     案内するのは pub の型だけで、非 pub の型は従っても直らない *)
                  match
                    List.filter
                      (fun q -> match Hashtbl.find_opt Decls.con_visibility q with Some v -> v.Decls.vis_pub | None -> true)
                      (Decls.con_synonym_candidates oid)
                  with
                  | _ :: _ as cands ->
                      type_error
                        ("未知の型: " ^ n ^ "(" ^ String.concat " か " (List.map name_of cands) ^ " と修飾してください)")
                  | _ -> type_error ("未知の型: " ^ n)))
  | T.EIdent li -> (
      (* 平坦化済みの module の修飾型参照(Parser.Parser など)。
         修飾名でもエイリアスを引く(M.A の形) *)
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
          (* 高階カインドの型変数への適用。カインドは使用時に kind_of / drop_arrows が確定する。
             drop_arrows は定義域を捨てるので、定義域の照合はここでしか書けない。
             acc は畳む前の頭、acc' は tapp の結果(頭が TCon なら畳まれる。§1.7)。
             kind_of acc' を先に呼ぶのは、頭がまだ KVar のときに drop_arrows に
             KArrow(新, 新)を張らせるためで、その後で kind_of acc を見ると定義域を取り出せる *)
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
              else type_error ("未知の型: " ^ n)))
  | T.EApply _ -> type_error "型適用の頭は型名でなければなりません"
(* ## 11.4 矢印、レコード行、ヴァリアント和

   矢印 `(A, B) => R @ E` は `TArrow (引数レコード, 返り値, エフェクト行)` になる。
   引数は閉じた `_item` 行のレコードなので、
   `(A) => R` と `(A, B) => R` は行の長さが違い、別の型になる。

   `@` を省いた矢印の読み方は、矢印の**位置**で決まる(仕様 §9、sample.kel:470-502)。

   | 矢印の位置 | 書いたラベル付きの行 | `@ {}` | `@` 省略 |
   |---|---|---|---|
   | 束縛の最外(`let` / `pub let` / `extern` / クラスメソッド) | 本体には上限、公開する型では行変数で開く(§11.26。クラスメソッドは §11.33) | 閉じたまま(両方向) | `let` は推論、`pub let` は純粋、メソッドは実装が純粋で公開が行多相、`extern` は行変数 |
   | 入れ子(引数の型、返り値の中、newtype のフィールド、レコード型のフィールド、タプル型の要素、effect の操作型の引数、エイリアスの展開先) | 書いたとおり閉じたまま(開かない) | 閉じたまま | `@ {}`(純粋) |

   表の 1 行目の「束縛の最外の矢印」がどれを指すかは、束縛の書き方で変わる。
   関数束縛 `let f(x: T): R @ E` では、返り値の後ろの `@` である。
   値束縛 `let k: (T) => R @ E = …` では、注釈そのものの頭の矢印の `@` である。
   注釈の頭が型エイリアスのときは最外の矢印が無く、エイリアスが展開する矢印を入れ子として読む
   (§11.5 の規則 4)。
   この 3 つは仕様 §9 が定めている(sample.kel:484-486)。

   関数束縛の最外の矢印は、`elab_binding` が `TArrow` を直接組み立てるので、ここには来ない。
   ここに来る矢印のうち最外なのは、`elab_type_outer` が運んでくる 2 つの位置
   (クラスメソッドの型と、引数リストを持たない値束縛の注釈の頭)で、残りはすべて入れ子である。
   そのため `EArrow` の省略 `@` は、`outer` が真のときだけ新しい行変数になり、
   それ以外は閉じた空の行 `TRowEmpty` になる。
   書かれたラベル付きの行を開くかどうかは、この関数では決めない。
   呼び出し側が表層の構文を見て決める(値束縛は §11.28、クラスメソッドは §11.33)。

   入れ子の省略 `@` を新しい行変数と読むと、newtype のフィールドに書いた `() => Int32` が
   何でも起こせる閉包の意味になり、エフェクトつきの閉包を純粋な閉包として取り出せてしまう。
   入れ子の省略は `@ {}` と読むので、この形は型エラーになる(`test/annot_rows.t` の launder)。
   入れ子に書いたラベル付きの行も、書いたとおり閉じたまま読む。
   入れ子の矢印に行を通したいときは、`newtype Callback[E] = Callback(() => Unit @ E)` のように、
   行変数を型パラメータに取る。

   表の 2 行目のうち、レコード型のフィールドとタプル型の要素は、
   仕様 §9 の入れ子の矢印の一覧にも挙がっている(sample.kel:496-498)。
   レコード型のフィールドにも裸の矢印を書ける。
   `{run: () => Unit}` がパースエラーになるのは矢印のせいではなく、
   `run` が予約語(§2.4)で、ラベルの位置に置けないからである。
   フィールド名を変えれば書け、省略した `@` はほかの入れ子と同じく `@ {}` になる
   (`test/annot_rows.t` の nestrec、`test/nonfeatures.t` の kwlabel)。

   `extends` の右は、行そのものとレコード型の 2 通りを受け付ける。
   レコード型なら、行を取り出して splice する。
   `{x: Int32 extends Point}` と書けるのはこのためで、Point の行がその場に展開される。

   矢印、レコード行、ヴァリアントの 3 つの構文は、どれも値の型の位置を持つ(§11.3)。
   そこで読んだ型のカインドが `Type` でなければ、その位置で落とす。

   | 構文 | 値の型の位置 | 値の型の位置ではない部分 |
   |---|---|---|
   | 矢印 `(A, B) => R @ E` | 引数 `A` `B` と返り値 `R` | `@` の右の行 `E` |
   | レコード行 `{a: A}` | 各フィールドの型(`_item` ラベルはタプルの要素) | `extends` の右 |
   | ヴァリアント `#Tag(T)` | 積載 `T` | 和の要素そのもの(行かヴァリアント) |

   落ちる位置は読む順で決まる。
   レコードとタプルの要素は `List.fold_right` で右から読むので、
   `(() => Unit @ E, E)` では第 2 要素の `E` のカインドが先に `Type` に決まり、
   第 1 要素の `@ E` が「行カインドではない型パラメータです」で落ちる(`test/kinds.t` の rowval3)。
   コンストラクタのフィールドは左から読むので(§11.31)、
   同じ形を `newtype Bad2[E] = Bad2((E, Int32), () => Unit @ E)` と書くと、
   落ちるのは第 2 フィールドである。
   どちらも宣言の時点で落ちる点は同じで、位置だけが違う。
   読む順は揃えていない。
   どちらも左から読むようにするには、行を組み立てる順序を変える必要がある。

   ヴァリアント和 `#Even | #Odd | R` は、各要素を行に落として `row_append` で連結する。
   ここでは、開いていてよいのは末尾の要素だけ、という規則を課す。
   途中に開いた行が来ると、連結後にどのラベルがどの尾部に属するのかが決まらない。
   閉じた要素どうしを連結すれば結果も閉じるので、ヴァリアント和は網羅性検査(第10章)と噛み合う。
   たとえば `report`(sample.kel:222-227)は、`case _` なしで網羅と判定される。

   `EHole`(`_`)はインスタンスの頭の `List[_]` 専用である。
   型式の一般の位置に穴を許すと部分適用と同じ問題が起きるので、ここで拒否する。 *)

  | T.EArrow (params, ret, eff_opt) ->
      let param_tys = List.map (fun p -> elab_value_type env level ~expanding "矢印の引数の型" p) params in
      (* 省略された @ の読み方は、矢印の位置で決まる(仕様 §9)。入れ子の矢印(最外以外の
         すべて。引数の型、返り値の中、newtype のフィールド、effect の操作型、型エイリアスが
         展開する矢印)の省略は @ {}(純粋)。最外(outer = true。クラスメソッドの型と、
         引数リストを持たない値束縛の注釈の頭)だけが新しい行変数になる。
         再帰はすべて outer を省き、false で降りる *)
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
            | TRecord row -> row (* {x: T extends Point}: レコード型の行を splice する *)
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
      (* 各要素を行に落として連結する。開いてよいのは末尾の要素だけ *)
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
   表に本体をしまっておき、使われるたびにその場で精緻化して展開する。
   展開後の型に、元がエイリアスだったという痕跡は残らない。
   そのため、型の表示は `IoError | ParseError` ではなく展開後の行になる。

   透過なエイリアスには、次の 5 つの規則を課す。

   1. エイリアスは再帰できない。
   2. エイリアスは部分適用できない。
   3. パラメータの制約は、エイリアスを書いた時点で課す。
   4. エイリアスが展開する矢印は、常に入れ子として読む。
   5. 型引数は、パラメータのカインドに合わせて読む。

   規則 1 は、展開中のエイリアス名の集合 `expanding` を引数で持ち回って守る。
   展開中の名前がもう一度現れたら、そこで打ち切ってエラーにする。
   透過な展開に再帰を許すと、展開が停止しない。

   規則 2 は、単一化の性質を保つための規則である。
   `type P[A] = (A, Int32)` を `P` 単体で書けるようにすると、それは実質的に型レベルのλになる。
   型レベルのλが入ると `f a ~ P Int` の解が一意でなくなり、
   単一化が unitary でなくなって主要型を失う。
   そこで、引数の個数が合わないエイリアスはその場でエラーにする。
   部分適用の禁止は、`expand_alias` の中の引数の個数の比較 1 つで実装している。

   規則 3 は、エイリアスに構築点が無いことから来る。
   `type P[A: Show] = (A, A)` の `Show` は、`P[X]` と書いた時点で `X` に要求される。
   エイリアスは透過なので、制約を効かせられるのは型を書いた時点しかない。
   newtype の制約が値の構築時に効くのと比べると、エイリアスの制約は早い時点で効く。

   規則 4 により、`type Thunk = () => Unit` の省略 `@` は、`Thunk` を最外に書いても `@ {}` になる
   (仕様 §9 は、型エイリアスを展開した矢印を入れ子の側に挙げている)。
   `expand_alias` は本体の精緻化に `outer` を渡さないので、
   この読み方は特別な処理なしに実現される(`test/annot_rows.t` の alias)。
   書かれた行にも同じ規則が掛かる。
   `type F[A] = (A) => Int32 @ Print` を束縛の最外の位置に書いても、
   `{Print}` は開かずに閉じたまま残る。
   開かせたいときは、矢印をリテラルで書く。
   型クラスのメソッドの登録は、最外の行を開く処理を別に持つので、
   `outer` を渡さないだけでは足りない。
   そこでメソッドの登録は、注釈の頭が矢印リテラルのときに限って行を開く
   (§11.33。`test/annot_rows.t` の clsalias3 / clslit)。

   規則 5 も、エイリアスに構築点が無いことから来る。
   newtype なら、`Callback[{Print}]` の `{Print}` を行として読むための情報は、
   宣言表の `dd_params` にある。
   透過なエイリアスは展開後に痕跡を残さない。
   そのため、パラメータのカインドだけは表(`al_kinds`、第6章 §6.5)に残しておかないと、
   使用点で読み分けられない。
   カインドは、1b の後始末が本体を一度投機的に精緻化して決める(§11.39)。
   読み分けと照合の規則は `elab_con_args` と同じで、
   `type Cb[E] = Callback[E]` に対して `Cb[{Print}]` と書ける(`test/kinds.t` の alias)。
   仮に型引数をすべて型として読むと、
   具体的な行は「エフェクトラベルはこの位置(レコード型)では使えません」で落ちてしまう。

   `check_no_hole` も、型レベルのλを避けるための検査である。
   型引数の位置に `_` を書けると、引数を捨てる型関数を書いたのと同じことになるので、
   インスタンスの頭以外では穴を拒否する。

   展開の環境は閉じている。
   エイリアスの本体から見えるのは自分の型パラメータだけで、呼び出し側の `env.types` は引き継がない。
   展開がその場のスコープに依存すると、同じエイリアスが場所によって別の型になってしまう。

   `al_kind` が `EffectRow` のときだけ、本体をエフェクト行として精緻化する。
   Keleut では行変数とエフェクト名が構文上同じ形なので、
   エイリアスの側にカインドの注記が要る(§11.6)。 *)

(* 値の型の位置で読んだ型のカインドが Type であることを確かめる。
   矢印の引数と返り値、レコードのフィールド(タプルの要素を含む)、ヴァリアントの積載、
   そして外側からは引数と返り値の注釈がこれを通る。
   確かめないと、行カインドの型パラメータや EffectRow エイリアスが値の型として表に入り、
   診断が使用点まで遅れて内部名で出る。
   裸のパラメータ 1 個の位置では、same_kind による照合が、
   値の位置に現れたことからカインドを Type と推論する働きをする。
   at_node を部分式に掛け直すのは、注釈全体の先頭ではなく、カインドが合わなかった位置を指すため *)
and elab_value_type env level ~expanding what t =
  let ty = elab_type env level ~expanding t in
  at_node t (fun () -> check_value_kind what ty);
  ty

(* 型引数を、宣言されたパラメータのカインドに合わせて読む(仕様 §6、sample.kel:252-255)。
   Row のパラメータなら elab_eff、そうでなければ elab_type で読む。
   読み終えたらカインドを照合する。不一致をここで落とすほうが、
   subst_params を経て使用点で bind が落とすより早く、診断も読みやすい。
   読み分けの判定は kind_repr の構造の一致で行い、same_kind は使わない。
   same_kind は KVar を張るので、判定に使うと、未確定のパラメータをすべて Row に固定してしまう
   (§1.6 の原則の例外。同じ理由の例外が §6.4b の kind_equiv にある)。
   照合の側は same_kind でよく、パス 1b ではこれがカインドの伝播路になる。
   elab_eff を ~check_row:false で呼ぶのは、行にならなかったことを、
   すぐ下の照合が構成子名と引数の位置を添えて報告するからである。
   抑制しないと、より一般的な「エフェクト位置の型のカインドが Row ではありません」が先に出て、
   どの引数かを位置からしか読み取れなくなる *)
and elab_con_args env level ~expanding cname k args =
  let rec go k i = function
    | [] -> []
    | a :: rest ->
        let pk, kr = match kind_repr k with KArrow (a', r) -> (a', r) | _ -> (new_kind_var (), KStar) in
        let a = check_no_hole a in
        (* 投機の間は、カインドが未確定のパラメータへ渡した要素なしの波括弧({} と
           {extends R})を読まずに飛ばす。この 2 つの形だけが型としても行としても読めるので、
           型として読んで照合すると、相手のパラメータを Type に張ってしまい、
           1b が宣言順に読めば Row に決まるはずの宣言を落とす。飛ばしても失うものは無い。
           1b が、相手のカインドが決まった状態でもう一度読むからである *)
        let ambiguous =
          !speculating && match (kind_repr pk, snd a) with KVar _, T.EBraceRow ([], _) -> true | _ -> false
        in
        let t =
          if ambiguous then t_unit
          else
            match kind_repr pk with KRow -> elab_eff ~check_row:false env level ~expanding a | _ -> elab_type env level ~expanding a
        in
        if (not ambiguous) && not (same_kind pk (Unify.kind_of t)) then
          type_error
            (Printf.sprintf "型構成子 %s の第%d引数のカインドが一致しません: %s を期待しましたが %s は %s です" cname (i + 1)
               (show_kind pk) (Show.show t) (show_kind (Unify.kind_of t)));
        t :: go kr (i + 1) rest
  in
  go k 0 args

and check_no_hole ((_, te) as t : T.type_exp) =
  match te with T.EHole -> type_error "_ はこの位置では使えません(インスタンス頭の List[_] 専用)" | _ -> t

(* 「未知のエフェクト」の言い分け。名前が型として登録されていれば、
   綴りの誤りではなく位置の誤りなので、そう報告する。
   resolve_con は module の同義語をたどるので、
   スコープ外の内部型名にもこちらの文言が出ることがあるが、
   受理と拒否は変わらない *)
and unknown_effect n =
  if Hashtbl.mem Decls.con_kinds (Decls.resolve_con (intern n)) then
    "型 " ^ n ^ " はエフェクトではありません(ここにはエフェクト行が要ります)"
  else "未知のエフェクト: " ^ n

(* エイリアスが開いた行に展開されたときの splice。
   row_append は左が閉じていることを要求するので、展開結果の閉じた前置部分をなぞり、
   残りの要素(acc)を行変数の手前に差し込む。{W[E], Console} は {Print, Console extends E} になる。
   acc も開いていたら行変数が 2 つになるので、型エラーにする *)
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
    type_error ("型エイリアス " ^ name_of info.Decls.al_name ^ " が再帰しています(エイリアスは非再帰)")
  else if List.length args <> List.length info.Decls.al_params then
    type_error
      (Printf.sprintf "型エイリアス %s の引数は %d 個必要です(%d 個与えられました。部分適用は禁止)" (name_of info.Decls.al_name)
         (List.length info.Decls.al_params) (List.length args))
  else
    (* 引数は使用スコープで精緻化する(呼び出し側の module のまま)。
       読み分けは表のカインド(al_kinds)で決める。規則は elab_con_args と同じで、判定は
       kind_repr の構造の一致、照合は same_kind である。al_kinds は構築点で al_params と
       同じ長さに作るので、長さの食い違いは処理系の欠陥である *)
    if List.length info.Decls.al_kinds <> List.length info.Decls.al_params then
      bug ("expand_alias: " ^ name_of info.Decls.al_name ^ " の al_kinds の長さが al_params と違います");
    let arg_tys =
      List.map2
        (fun a pk ->
          let a = check_no_hole a in
          let t =
            match kind_repr pk with
            | KRow -> elab_eff ~check_row:false env level ~expanding a
            | _ -> elab_type env level ~expanding a
          in
          if not (same_kind pk (Unify.kind_of t)) then
            type_error
              ("型エイリアス " ^ name_of info.Decls.al_name ^ " の型引数のカインドが一致しません: " ^ show_kind pk
             ^ " を期待しましたが " ^ Show.show t ^ " は " ^ show_kind (Unify.kind_of t) ^ " です");
          t)
        args info.Decls.al_kinds
    in
    (* パラメータの制約は展開時、つまり型を書いた時点で課す。エイリアスは透過で構築点が無く、
       展開後の型に制約の痕跡も残らないので、その場で調べるしかない。これは newtype より
       早い時点である。newtype の制約は値の構築時に効くので、Box[NoShow] は型として
       書けるが Box(v) で落ちる *)
    List.iter2
      (fun (tp : type_param) t -> List.iter (fun li -> Unify.add_class t (intern (show_long_id li))) tp.tp_classes)
      info.Decls.al_params arg_tys;
    let types =
      List.fold_left2 (fun m tp t -> SMap.add tp.tp_name t m) SMap.empty info.Decls.al_params arg_tys
    in
    (* エイリアスの本体は閉じている。見えるのは型パラメータだけ *)
    let env' = { env with types } in
    let expanding = info.Decls.al_name :: expanding in
    (* 本体は宣言スコープで展開する。module 内のエイリアスが内部型を指しているとき、
       外から使っても壊れないようにするため *)
    let saved = !Decls.current_module in
    Decls.current_module := info.Decls.al_module;
    Fun.protect
      ~finally:(fun () -> Decls.current_module := saved)
      (fun () ->
        match info.Decls.al_kind with
        | Some "EffectRow" -> elab_eff env' level ~expanding info.Decls.al_body
        | _ -> elab_type env' level ~expanding info.Decls.al_body)

(* ## 11.6 エフェクト行の精緻化

   Keleut では、`@ E`(行変数)と `@ Print`(エフェクト名)が構文上まったく同じ形をしている。
   区別できるのは型検査器だけで、その判定を `elab_eff` が行う。

   1. `env.types` にあり、カインドが行なら、行変数である。
   2. `EffectRow` と注記されたエイリアスなら、展開して splice する。
      波括弧の中の要素では、引数があってもなくても、エイリアスを effect の宣言表より先に調べる。
   3. effect の宣言表にあれば、`@ Print` は `@ {Print}` の略記なので、ラベル 1 つの閉じた行にする。

   1 の判定に `same_kind` を使うのは、arity 0 の型パラメータのカインドが、
   宣言時には未定(`KVar`)だからである。
   `[E]` と書いただけでは行なのか型なのか分からず、使われた位置で決まる。
   構造の一致で `KRow` かどうかを調べると、まだ `KVar` のままの行変数を取りこぼす。
   第8章の `rewrite_row` も、同じ理由で `same_kind` を使う(§8.6)。

   カインドを `same_kind` で比べるという原則には、例外が 3 つある。
   §11.3 の `elab_con_args` の読み分け(§11.5 の `expand_alias` も同じ規則で読み分ける)、
   第6章 §6.4b の `kind_equiv`、
   そして下で述べる最後の分岐の照合である。
   どれも、`same_kind` が `KVar` を張ると未確定のカインドが固定されてしまう位置で、
   構造で比べてよい理由をそれぞれの箇所に書いてある。

   ラベルの引数は 1 つまでである(`Heap[h]` のように)。
   ラベルの引数の欄がそのままエフェクトのパラメータで、
   パラメータを持たないエフェクトはそこに `Unit` を置く。
   行変数の中置の合成(`{E1, Print}` の `E1`)は受け付けない。
   行の合成を末尾の `extends` だけに限ると、
   `row_append` の左辺が常に閉じているという不変条件を保てる。
   例外は、開いた行に展開されるエイリアスの splice である。
   この場合は `splice_row` が、展開結果の閉じた前置部分に残りの要素を差し込み、同じ不変条件を守る
   (`{W[E], Console}` は `{Print, Console extends E}` になる。`test/kinds.t` の splice2)。
   行変数が 2 つになる形(`{W[E] extends E2}`)は型エラーである。

   `Heap[h]`(ラベルの引数)と `WithPrint[E]`(パラメータつきの EffectRow エイリアスの適用)は、
   構文上同じ形をしている。
   型名、エフェクト名、エイリアス名は `claim_type_name` の 1 つの名前空間に載っているので、
   名前を引けばどちらなのかが決まる(`test/kinds.t` の splice)。

   「未知のエフェクト」の診断は、綴りの誤りと位置の誤りの 2 通りに言い分ける。
   名前が型として登録されているなら、綴りの誤りではなく位置の誤りなので、
   `Callback[Int32]` には「型 Int32 はエフェクトではありません」と報告する(`unknown_effect`)。

   上の分岐のどれにも当たらなかった型式は、最後の分岐に進む。
   `@` の後(文法の `eff` / `eff_name`)に書いた型式のうち、ここへ届く形は 2 つある。
   module 修飾の名前(`M.T` / `M.W`)と、
   エフェクト名でない頭への適用(`W[E]` / `MutableArray[Int32, Int32]`)である。
   このほか `elab_eff` は、文法では `ty` を取る位置を 3 つ読む。
   `{… extends <ty>}` の右(`parser.mly` の `lbrace EXTENDS ty RBRACE`)、
   EffectRow エイリアスの本体(`type` 宣言の右辺)、
   行カインドのパラメータへの型引数(§11.3 の `elab_con_args` と §11.5 の `expand_alias`)である。
   extends の右は、`EBraceRow` の分岐がその `ty` をそのまま `elab_eff` へ再帰で渡す。
   これらの位置からは、`@ {extends #Tag}` や `type W: EffectRow = #Tag` のように、
   `eff` では書けない型式もここへ届く。
   EffectRow エイリアスの適用はここを通って正しく行になるので、
   この分岐に届いたものを一律に型エラーにするわけにはいかない。
   そこで最後の分岐は、`elab_type` で読んだ結果のカインドを照合し、行でなければ型エラーにする。
   文面は「エフェクト位置の型のカインドが Row ではありません: <型> :: <カインド>」で、
   §11.3 の値の型の位置と同じ `kind_error` から出す。
   照合しないと、`let f(x: Int32): Int32 @ MutableArray[Int32, Int32] = x` が
   `@ {extends MutableArray[Int32, Int32]}` という型で通ってしまう。
   行の尾部に置かれた、カインドが Type の型は何とも単一化しないので、
   その関数は宣言できても呼べない。
   module 修飾の型名(`@ M.T`)と、
   EffectRow エイリアスの本体(`type W: EffectRow = MutableArray[Int32, Int32]`)も、
   この照合で落とす(`test/kinds.t` の effkind 〜 effkind5)。

   `EBraceRow` の分岐には「extends の右は行でなければなりません」という検査があるが、
   この検査には到達しない。
   extends の右は `elab_eff` で読む(`?check_row` は既定の true のまま)ので、
   最後の分岐を通ったものは先に照合を抜けてカインドが `Row` になっており、
   ほかの分岐が返すのも行だからである。
   `@ {extends #Tag}` は「エフェクト位置の型のカインドが Row ではありません: #Tag :: Type」で落ちる。
   到達しない検査は、安全網として残してある。

   この照合だけは `kind_repr` の構造の一致で判定し、`same_kind` を使わない。
   エフェクト位置ではカインドを推論させない、というのが理由である。
   裸の型パラメータは 1 番目の分岐が受け、そこでは `same_kind` で、
   まだ `KVar` の行変数かもしれないものを拾う。
   最後の分岐にも、カインドが未確定のまま届くものがあり、その経路は 2 つある。
   1 つは arity 0 の束縛子への適用(`let f[F, E](x: Int32): Int32 @ F[E]`)で、
   `drop_arrows` が `KArrow (KVar, KVar)` を張った結果の新しい `KVar` が届く。
   もう 1 つは、パラメータのカインドがまだ推論されていない型エイリアスの適用で、
   こちらは `TVar` が返る。
   エイリアスのカインドの推論は 1b の後始末で走るので、
   1b の newtype の本体から見ると、`al_kinds` は `KVar` のままである
   (`type Id[A] = A` と `newtype N[X] = MkN(() => Unit @ Id[X])` を並べると、
   展開結果の `A` が `KVar` のカインドで最後の分岐へ返る)。
   つまり、構造で比べるのは、この分岐に未確定のカインドが来ないからではない。
   未確定のカインドが来るからこそ、構造で比べる。
   ここで `same_kind` を呼ぶと、それは検査ではなく `Row` への既定化になる。
   `F[E]` なら `F` のカインドが「Type を取って Row を返す」に固定されるが、
   そのようなカインドの型構成子は言語に無いので、宣言できても呼べない `f` が残る。
   カインドが未確定のときは、`:: <カインド>` の併記を落とす。
   内部の連番が漏れると、番号がプレリュードの行数で変わり、診断が再現しなくなるからである
   (§11.3 の `kind_error`)。

   この照合は、`?check_row` に false を渡すと行わない。
   false を渡すのは、型引数の読み分けの 2 か所(`elab_con_args` と `expand_alias`)だけである。
   そこでは呼び出し側が、「型構成子 Callback の第1引数のカインドが一致しません」のように、
   構成子名と引数の位置を添えて報告する(`test/kinds.t` の nest2)。
   既定値が `true` なので、`?check_row` を渡さない呼び出しはすべて照合する。

   エフェクト位置に名前や適用形を書き、読んだ結果が行にならなかったときの診断は 3 通りある。
   綴りの誤り(「未知のエフェクト: Nope」)、位置の誤り(「型 Int32 はエフェクトではありません」)、
   読んだ結果のカインドが行でない場合(「エフェクト位置の型のカインドが Row ではありません」)である。
   1 つの文言に揃えるとどれかが事実と合わなくなるので、`test/kinds.t` が 3 つを並べて固定している。
   エフェクト位置で落ちる診断は、この 3 つだけではない。
   行カインドでない型パラメータ(`@ h`)と Type エイリアス(`@ P`)は、
   名前を引いた時点で、手前の分岐が別の文言で落とす。
   前者は「行カインドではない型パラメータです: h」、
   後者は「エフェクト位置に Type エイリアス P は使えません(: EffectRow を付けてください)」である
   (`test/kinds.t` の regionkind / classrow / effkind6)。

   相互再帰の関数群を定義し終えたら、`elab_type` / `elab_value_type` / `elab_eff` を、
   `~expanding` に空リストを渡す同名の関数で覆う。
   以降の呼び出し側は、展開中の名前の集合を意識しない。 *)

and elab_eff ?(check_row = true) env level ~expanding ((_, te) as t : T.type_exp) : ty =
  at_node t @@ fun () ->
  match te with
  | T.EIdent (LongId [ n ]) when SMap.mem n env.types ->
      let tv = SMap.find n env.types in
      if same_kind (Unify.kind_of tv) KRow then tv else type_error ("行カインドではない型パラメータです: " ^ n)
  | T.EIdent (LongId [ n ]) when Hashtbl.mem Decls.aliases (intern n) ->
      let info = Hashtbl.find Decls.aliases (intern n) in
      if info.Decls.al_kind = Some "EffectRow" then expand_alias env level ~expanding info []
      else type_error ("エフェクト位置に Type エイリアス " ^ n ^ " は使えません(: EffectRow を付けてください)")
  | T.EIdent (LongId [ n ]) ->
      (* @ Print = @ {Print} の略記 *)
      if Hashtbl.mem Decls.effects (intern n) then TRowExtend (intern n, t_unit, TRowEmpty)
      else type_error (unknown_effect n)
  | T.EApply ((_, T.EIdent (LongId [ n ])), args) when Hashtbl.mem Decls.effects (intern n) ->
      (* @ Heap[h] = @ {Heap[h]} の略記。sample.kel:467 の略記の規則は、
         引数つきのラベルを除外していない *)
      TRowExtend
        ( intern n,
          (match args with
          | [ a ] -> elab_type env level ~expanding a
          | _ -> type_error "エフェクトラベルの引数は1個までです"),
          TRowEmpty )
  | T.EBraceRow (elems, ext) ->
      let tail =
        match ext with
        | None -> TRowEmpty
        | Some t -> (
            (* extends の右は、文法(parser.mly)が eff ではなく ty を取るので、ここから
               elab_eff へ再帰で読む。これが最後の分岐への経路の 1 つである。下の検査は
               最後の分岐の照合が先に落とすので到達しないが、安全網として残す(§11.6) *)
            let tt = elab_eff env level ~expanding t in
            if same_kind (Unify.kind_of tt) KRow then tt else type_error "extends の右は行でなければなりません")
      in
      List.fold_right
        (fun elem acc ->
          match elem with
          | T.BLabel (LongId [ n ], args) -> (
              (* エイリアスを先に調べ、引数の有無で経路を分けない。エフェクト名と型名は
                 同じ名前空間(claim_type_name)にあるので、Heap[h](ラベルの引数)と
                 WithPrint[E](エイリアスの適用)を取り違えない *)
              match Hashtbl.find_opt Decls.aliases (intern n) with
              | Some info when info.Decls.al_kind = Some "EffectRow" ->
                  splice_row n (expand_alias env level ~expanding info args) acc (* 行を splice する *)
              | Some _ -> type_error ("エフェクト行に Type エイリアス " ^ n ^ " は置けません(: EffectRow を付けてください)")
              | None ->
                  if args = [] && SMap.mem n env.types then
                    (* `{E1, Print}` のような行変数の合成は受け付けない(末尾の extends だけ)。
                       引数つきのときに env.types を見ないのは、型パラメータへの適用が
                       行の要素になれないからである *)
                    type_error ("行変数 " ^ n ^ " は extends の位置にのみ書けます")
                  else if Hashtbl.mem Decls.effects (intern n) then
                    TRowExtend
                      ( intern n,
                        (match args with
                        | [] -> t_unit
                        | [ a ] -> elab_type env level ~expanding a
                        | _ -> type_error "エフェクトラベルの引数は1個までです"),
                        acc )
                  else type_error (unknown_effect n))
          | T.BLabel (li, _) -> noimpl ("モジュール修飾のエフェクト(M10): " ^ show_long_id li)
          | T.BField (l, _) -> type_error ("エフェクト行にフィールド " ^ l ^ " は書けません"))
        elems tail
  | _ ->
      (* 最後の分岐。ここへ通るのは、@ の後に書いた module 修飾の名前とエフェクト名でない
         頭への適用と、文法が ty を取る 3 つの位置(extends の右、EffectRow エイリアスの本体、
         行カインドのパラメータへの型引数)から来る型式である。型引数の経路は
         ~check_row:false を渡すので照合しない。EffectRow エイリアスの適用(W[E] / M.W)は
         ここを通って正しく行になるので、落とすのではなく、読んだ結果のカインドを照合する。
         判定は kind_repr の構造の一致で行い、same_kind は使わない。カインドが未確定の
         まま届く経路があり(F[E] と、カインドが未推論のエイリアスの適用)、same_kind で
         調べると、検査ではなく Row への既定化になる(§11.6) *)
      let ty = elab_type env level ~expanding t in
      if check_row && kind_repr (Unify.kind_of ty) <> KRow then kind_error "エフェクト位置の型" ~expected:"Row" ty;
      ty

(* 束縛の最外の矢印が注釈としてそのまま書かれている位置
   (型クラスのメソッドの型と、引数リストを持たない値束縛の注釈)専用の入口。
   ここでだけ、省略した @ が新しい行変数になる。
   仕様 §9 の表のうち、let を本体から推論する規則と、型クラスのメソッドについて
   インスタンスの実装を純粋とし、公開する型を行多相にする規則は、一般化と包摂検査が担う。
   ~outer:true を渡すのはこの 1 か所だけ *)
let elab_type_outer env level t = at_node t (fun () -> elab_type env level ~expanding:[] ~outer:true t)

let elab_type env level t = at_node t (fun () -> elab_type env level ~expanding:[] t)

(* 注釈の位置(引数、返り値、値束縛の頭)も値の型の位置なので、同じ照合を通す。
   通さないと、EffectRow エイリアスを書いた注釈が束縛の単一化まで残り、
   「カインドが一致しません: _A :: Type と {Print}」と内部名で落ちる。
   引数と返り値の注釈はこの関数で読み、値束縛の頭は下の elab_value_type_outer で読む *)
let elab_value_type env level what t = at_node t (fun () -> elab_value_type env level ~expanding:[] what t)

let elab_value_type_outer env level what t =
  let ty = elab_type_outer env level t in
  at_node t (fun () -> check_value_kind what ty);
  ty

let elab_eff env level t = at_node t (fun () -> elab_eff env level ~expanding:[] t)

(* ## 11.7 パターンの検査

   `elab_pat` はパターンの型を推論せず、期待型に対して検査する。
   上から降りてきた期待型 `expected` をパターンに沿って分解しながら、変数を環境に足していく。

   パターンが束縛する変数は常に単相である。
   パターン変数を一般化しないことはランク 1 多相の一部で、
   ここで一般化すると、`match` の各節が変数を別々の型で使える不健全な体系になる。

   `seen` は、同じパターンの中での変数の重複を拒否するためだけの可変リストである。
   環境そのものは不変の Map で、変数を足しては引数として次へ渡していく。
   例外はコンストラクタパターンでフィールドを走査するところだけで、
   そこは `Array.iteri` の都合で環境を ref に溜める(§11.8)。

   パターンを検査として扱う利点は 2 つある。
   第 1 に、リテラルパターンが `number_ty` を経由するので、
   `case 0 =>` が `Integral` 述語つきの変数として期待型と単一化され、
   整数の幅がスクルティニの側から決まる。
   第 2 に、レコードパターンで `rest` を書いたかどうかが、そのまま行の開閉になる。
   閉じた行はタプルの要素数の検査そのもので、
   `(a, b)` が 3 要素のタプルに当たらないのは、行の長さが合わないからである。
   タプルの要素数を数える専用の検査はない。

   `PAnnot` が読む注釈は値の型の位置なので、
   `elab_value_type` を通してカインドを `Type` と照合する(§11.3)。
   引数の注釈はこの経路で読むので、`let f(x: P)` に `EffectRow` エイリアスを書いた形は、
   期待型との単一化まで進まず、注釈のその場で落ちる(`test/kinds.t` の annotkind)。

   `elab_pat` は、式のノードと同じく、すべてのパターンのノードに期待型を `set_ty` で書き込む。 *)

let rec elab_pat env level seen expected ((_, p) as node : T.pat) : env =
  Tree.set_ty node expected;
  at_node node @@ fun () ->
  match p with
  | T.PWildcard -> env
  | T.PVar x ->
      if List.mem x !seen then type_error ("同じパターン内で変数 " ^ x ^ " が重複しています")
      else (
        seen := x :: !seen;
        { env with values = SMap.add x expected env.values })
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
      Unify.unify expected (number_ty level n);
      env
  | T.PRecord (fields, rest) -> (
      let ftys = List.map (fun (l, _) -> (l, new_var level)) fields in
      match rest with
      | None ->
          (* 閉じた行(タプルの要素数の検査) *)
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
   フィールドの型を `subst_params` で具体化してから部分パターンへ降りていく。

   フィールドは位置引数とラベル指定の 2 通りで指定でき、両者を混ぜて書ける。
   ラベル指定なら欠落を許す(書かなかったフィールドは `_` と同じ)。
   位置引数を使ったときだけ、すべてのフィールドが必要になる。
   ラベル指定で欠落を許すのは、フィールドを増やしたときに既存のパターンを壊さないためである。

   フィールドを実引数に割り付けた結果(フィールドの位置から実引数の位置への配列)を、
   `set_resolved` で木に書く。
   評価器と網羅性検査に同じ計算をさせないためである。
   ラベルの並べ替えを 3 か所で実装すると、3 か所がずれたときに、
   型検査は通るのに値が入れ替わってしまう。

   `dd_opaque` が真の型(`newtype T = ???`)をパターンで分解することをここで拒み、表現を隠す。
   そのような型は型としては使えるが、パターンで中身を見ることはできない。 *)

  | T.PCtor (li, args) -> (
      let (LongId comps) = li in
      let cname = List.nth comps (List.length comps - 1) in
      if not (cname.[0] >= 'A' && cname.[0] <= 'Z') then
        type_error ("未知のコンストラクタパターン: " ^ show_long_id li ^ "(操作節は handle の中でのみ使えます)")
      else
        match Hashtbl.find_opt Decls.ctor_owner (intern cname) with
        | None -> type_error ("未知のコンストラクタ: " ^ show_long_id li)
        | Some dname ->
            let ctor = intern cname in
            Decls.check_ctor_visible ctor dname;
            let dd = Hashtbl.find Decls.datas dname in
            if dd.Decls.dd_opaque then type_error ("newtype " ^ name_of dname ^ " の表現は ??? で隠されています")
            else
              let ct = List.find (fun c -> c.Decls.ct_name = ctor) dd.Decls.dd_ctors in
              let nfields = List.length ct.Decls.ct_fields in
              let field_to_arg = Array.make nfields None in
              let positional = List.filter (fun a -> a.T.cap_label = None) args in
              (* 位置引数があるときは全フィールドが必要。
                 欠落を _ で補うのはラベル指定のパターンだけ *)
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

   `is_value` は純粋に構文的な判定で、式が値なら一般化してよいと決める。
   可変参照がある言語で一般化を無条件に許すと不健全になるので、どこかで線を引く必要がある。
   その線を構文で引くのが、最も安上がりである。

   実装は、値でないときはレベルを上げない、というだけである。
   レベルを上げなければ、その束縛では一般化されない。
   専用のフラグも後処理もない。

   ブロック(`Seq` や `Let` の連鎖)は、保守的に非値とする。
   中身を見れば値と分かるブロックもあるが、中身を見ないと決めておくほうが規則が短く、
   誤ったほうへ倒れない。
   値でないと言いすぎても不健全にはならず、多相性が減るだけである。
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

   `elab_exp` の仕事は 2 つある。
   式の型を返すことと、その型をノードに書き込むことである。
   第14章の評価器は、数値リテラルのノードに書き込まれた型を読んで、
   値を Int32 / Int64 / Float64 のどれで作るかを決める。

   引数は `env` / `level` / `eff` の 3 つである。
   `eff` はその場所で許されているエフェクト行で、下向きにだけ流れる。
   この向きが効くのは perform のところで、
   エフェクトを上向きに集める実装なら必要になる合流と差分の計算が、単一化 1 回に置き換わる(§11.15)。

   リテラルの型はその場で決まる。
   `Hole`(`???`)は新しい型変数を型とし、実行時に評価されると落ちる。 *)

let rec elab_exp env level eff ((_, e) as node : T.exp) : ty =
  let t = at_node node (fun () -> elab_exp' env level eff node e) in
  Tree.set_ty node t;
  t

and elab_exp' env level eff node e =
  match e with
  | T.Bool _ -> t_boolean
  | T.Text _ -> t_string
  | T.Number n -> number_ty level n
(* ## 11.11 変数とラムダ

   変数参照は `instantiate` を呼ぶ主な場所である。
   ほかにも、演算子がクラスのメソッドのスキーマを引くところ(§11.13)、
   perform と操作節が操作のスキーマを引くところ(§11.15、§11.24)、
   インスタンス本体の包摂検査(§11.38)が `instantiate` を呼ぶ。
   どれも、表から引いたスキーマの ∀ を剥がすという同じ用途である。
   ∀ を剥がす操作がこの用途に限られているので、
   型クラスの制約とカインドが複製される場所も、スキーマを引いた直後だけだと分かる(第8章)。

   大文字で始まる名前が値の環境に無ければ、引数のないコンストラクタとしてもう一度探す。
   `Nil()` と書かなくても `Nil` と書けるようにするためである。

   ラムダの本体には、新しい行変数を割り当てる。
   ラムダ式そのものは値なので、周囲の `eff` には何も足さない。
   関数を作ってもエフェクトは起きず、起きるのは関数を呼んだときである。
   呼び出しの扱いは §11.12 で述べる。 *)

  | T.Ident li -> (
      let name = show_long_id li in
      match SMap.find_opt name env.values with
      | Some sch ->
          (* 修飾名で module の値に触るときの可視性検査。module M の値 x の修飾名 M.x が、
             同名のクラス M のメソッド x の修飾名と同じ綴りになる形は、平坦化が拒否する
             (§11.42)。そのため、可視性台帳に載っている名前は必ず module の値であり、
             綴りによる免除は要らない。綴りで免除すると、同名のクラスを 1 行宣言するだけで、
             任意の非 pub の値を外から呼べてしまう *)
          Decls.check_value_visible (intern name);
          Unify.instantiate level sch
      | None -> (
          (* 環境に無かったときだけ、module スコープの値の同義語を引く。フォールバック専用
             なので、局所束縛による遮蔽が自動で効く。スコープの外では解決せず、候補の列
             (診断専用)で修飾名を案内する。素の「未束縛の変数」だけでは、module の同名の
             let が原因だと読み手がたどれない *)
          let scoped =
            match !Decls.current_module with
            | Some m -> Hashtbl.find_opt Decls.module_val_synonyms (m, intern name)
            | None -> None
          in
          match Option.bind scoped (fun q -> SMap.find_opt (name_of q) env.values) with
          | Some sch -> Unify.instantiate level sch
          | None -> (
              match li with
              | LongId comps when comps <> [] && String.length (List.nth comps (List.length comps - 1)) > 0 ->
                  let last = List.nth comps (List.length comps - 1) in
                  if last.[0] >= 'A' && last.[0] <= 'Z' then elab_construct env level node last []
                  else unbound_value name scoped
              | _ -> unbound_value name scoped)))
  | T.Hole -> new_var level
  | T.Lambda { l_params; l_body } ->
      let param_tys = List.map (fun _ -> new_var level) l_params in
      let seen = ref [] in
      let env2 = List.fold_left2 (fun env p t -> elab_pat env level seen t p) env l_params param_tys in
      let body_eff = new_row_var level in
      let tr = elab_exp env2 level body_eff l_body in
      (* 反駁可能な引数パターンは網羅性検査へ送る。let のパターン束縛と同じ扱いで、
         検査しないと、型検査を通ったプログラムが実行時に「パターンに値が一致しません」で落ちる *)
      List.iter2 (fun p t -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) l_params param_tys;
      TArrow (TRecord (closed_item_row param_tys), tr, body_eff)
(* ## 11.12 関数適用

   適用の型付けの骨格は、関数の型を `TArrow (引数レコード, 返り値, eff)` と単一化することである。
   第 3 要素に呼び出し側の `eff` を渡すことで、
   この関数を呼ぶにはこのエフェクトが要る、という情報が呼び出し文脈の行に流れ込む。

   単一化と引数の型付けの順序には意味がある。
   素直に書けば、引数を先に推論してから関数型と単一化するが、`elab_exp'` はそうしない。

   1. 関数を推論する
   2. 先に `TArrow (pvar, tr, eff)` と単一化して、関数型を分解する
   3. 引数を、その `pvar` を期待型として検査する(§11.19)

   この順序が効くのは、引数がラムダで、その本体が `perform` を含むときである。
   修飾なしの操作名の解決は、その時点でエフェクト行にどのラベルが見えているかを見る(§11.20)。
   引数を先に推論すると、ラムダの行はまだ何も決まっていない新しい行変数で、ラベルが 1 つも見えない。
   そのため解決が間に合わない。

   この順序が必要になる例が、sample.kel:616-621 の `copy` である。

   ```
   let copy(src: String, dst: String): Unit @ {Console, Fs} = {
     with _ = with_file(src)
     let text = perform read()                   // 最も左の File は src のもの
     with _ = with_file(dst)
     perform write(text)                         // 最も左の File は dst のもの
   }
   ```

   `with` は呼び出しの末尾に継続を加える構文糖(第3章)なので、
   これは `with_file(src, fn(_) => ...)` に脱糖される。
   `with_file` の宣言は `body: () => A @ {File, Fs extends E}` なので、
   期待型を先に押し込めば、ラムダの行が `{File, Fs extends E}` に確定した状態で、
   ラムダの本体を推論できる。
   すると `write` を解決するときに、行に `File` が見えている。
   順序を入れ替えると、ここは `write` が Console と File の両方にある、という曖昧さのエラーになる。
   関数型を先に分解して引数を期待型で検査するのは、多相のためではなく、
   操作名の解決に必要な行を先に決めるためである。

   単一化が行の不一致で落ちたときは、文言を 3 通りに言い換える。
   `pub` で `@` を省略した宣言の Rigid の行と衝突した形では、pub の規則を名指しする。
   呼び出し先の行が空(純粋な関数)で、それを空でない行の下から呼ぶ形と、
   この位置の行が空(高階の引数の行が `@ {}`)である形では、
   仕様 §9 の、入れ子の矢印で省略した `@` を `@ {}`(純粋)と読む規則を案内する。
   言い換えるのは行に由来する失敗だけで、その判定を `row_failure` が行う。
   引数の型の不一致は言い換えない。
   `callee_pure` を単一化の前に取るのは、単一化が失敗しても、
   呼び出し先の行が書き換わっていることがあるからである。 *)

  | T.Apply (f, arg) ->
      let tf = elab_exp env level eff f in
      (* 単一化の前に、呼び出し先の行を覚えておく(単一化の後では書き換わる)。
         空の行の関数を空でない行から呼ぶ失敗は仕様 §9 の規則そのものなので、
         一般的な文言のかわりに規則を案内する *)
      let callee_pure = match repr tf with TArrow (_, _, e) -> repr e = TRowEmpty | _ -> false in
      let tr = new_var level in
      let pvar = new_var level in
      (* 関数の行を呼び出し側の eff と単一化してから、引数を期待型で検査する(§11.12) *)
      (try Unify.unify tf (TArrow (pvar, tr, eff))
       with Type_error msg ->
         (* pub の @ 省略は純粋を意味する。エフェクトつき関数の呼び出しが Rigid の行と
            衝突する形は perform よりよく起きるのに、一般的な文言「行型ではありません: ς1」では
            原因にたどり着けない。そこで perform の側(§11.15)と同じ言い換えをここにも置く *)
         let pub_pure =
           let _, tail = row_fields eff in
           match repr tail with
           | TVar r -> ( match !r with Rigid i -> Hashtbl.mem pub_pure_rows i.vid | _ -> false)
           | _ -> false
         in
         if pub_pure && row_failure msg then
           type_error ("pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: " ^ msg ^ ")")
         else if row_failure msg && callee_pure then
           type_error
             (msg
            ^ "(呼び出し先の行は空 = 純粋です。行の部分型付けが無いので、空でない行の下からは呼べません。入れ子の矢印の @ 省略は @ {} と読みます — 行を通すなら行変数を型パラメータに取ってください。§9)")
         else if row_failure msg && repr eff = TRowEmpty then
           type_error
             (msg
            ^ "(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)")
         else type_error msg);
      elab_check env level eff arg pvar;
      tr
(* ## 11.13 演算子とレコードの 4 操作

   演算子は AST に `BinOp` として残し、意味は第7章の表から引く。
   `+` は、クラス `Add` のメソッド `add` の呼び出しと同じ型付けをする。
   `method_scheme` がクラス表からメソッドの型スキーマを引き、
   それを `(左辺, 右辺)` の行に対する矢印と単一化するだけで、演算子のためだけの推論規則は持たない。
   この対応には例外が 2 つある。
   `&&` と `||` は短絡するので、両辺を Boolean とする組み込みである。
   `!=` は `Eq.eq` の否定である。
   演算子をノードとして残すのは、この 2 つの例外を表の中に閉じ込めるためで、
   エラーメッセージに演算子の字面を保てるという利点もある。

   レコードの操作は、拡張、選択、制限、更新の 4 つで尽きる。
   更新(`{r with l = v}`)は、制限してから拡張するのと同じ型付けで、フィールドの型が変わってよい。
   行に載っている古い型は捨て、新しい型で拡張し直す。

   `RecordEmpty` の型が Unit なのは Keleut の設計である。
   Unit は空のレコードであり、専用の型ではない。

   構造的ヴァリアント `#Foo(v)` は、ラベル 1 つと新しい行変数からなる行を作る。
   尾部が開いているので、`#Foo(1)` はそのまま `#Foo | #Bar` の文脈にも渡せる。
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
          Unify.unify (Unify.instantiate level scheme) (TArrow (TRecord (closed_item_row [ tl; tr ]), ret, eff));
          ret)
  | T.Not e ->
      Unify.unify (elab_exp env level eff e) t_boolean;
      t_boolean
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
      (* 制限してから拡張するのと同じ型付け。フィールドの型は変わってよい *)
      let told = new_var level in
      let rest = new_row_var level in
      Unify.unify (elab_exp env level eff r) (TRecord (TRowExtend (intern l, told, rest)));
      TRecord (TRowExtend (intern l, elab_exp env level eff v, rest))
  | T.Variant (s, v) -> TVariant (TRowExtend (intern s, elab_exp env level eff v, new_row_var level))
(* ## 11.14 ブロック、let、match、コンストラクタ

   ブロックは各文を同じ `eff` で推論し、末尾の式の型を返す。
   文が無ければ Unit である。
   let と let rec は、環境を足して本体へ進むだけで、主な処理は `elab_binding` の側にある(§11.28)。

   match はスクルティニを推論し、各節のパターンをその型に対して検査し、
   ガードを Boolean と、本体を共通の結果型と単一化する。
   スクルティニが 1 つだけなのは、Keleut が後置の `v match {...}` しか持たないからである。
   タプルはレコードなので、`(a, b) match` が複数のスクルティニと同じ表現力を与える。

   網羅性検査はここでは走らせず、パターンの列と型を遅延キューに積むだけである。
   検査は構造的ヴァリアントの行を閉じて型を書き換えることがあるので、
   できるだけ遅く走らせる(第10章 §10.13)。
   ただし、キューに積んだ検査は一般化より前に処理し終えなければならない。
   `close_variant_rows` が Generic になった行変数に単一化をかけると、内部エラーになるからである。
   `Exhaust.drain` でキューを処理する場所は 1 か所ではないが、どれも一般化より前にある。
   束縛群(`elab_binding` / `elab_rec_bindings`)では `generalize` の直前、
   トップレベルの式(`DExp`)では推論の直後である(§11.28、§11.40)。

   コンストラクタの適用は `elab_construct` に任せる(§11.18)。 *)

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
   名前を解決し(§11.20)、完全名を木に書き、引数を操作スキーマの引数行と単一化し、
   最後に次の単一化を行う。

   ```
   unify eff (TRowExtend (エフェクト名, Unit, 新しい行変数))
   ```

   perform の位置でそのエフェクトを起こしてよいかどうかは、この 1 行の単一化だけで検査する。
   `eff` が開いていればラベルが追加され、
   閉じていれば単一化が失敗して「ここでは実行できません」になる。
   エフェクト集合の包含の判定も差分の計算も、どこにも書いていない。
   行の単一化がそれを兼ねる。

   行に載るラベルは、操作名ではなくエフェクト名である。
   `perform write(...)` の行に立つのは `write` ではなく `File` である。
   ハンドラが捕まえる単位がエフェクトだからである。

   木に書き込む解決結果は、完全名 `Effect.op` の oid である。
   評価器は名前解決をやり直さず、この oid でハンドラを探す(第14章)。 *)

  | T.Perform (li, arg) ->
      let eff_name, op, scheme = resolve_perform eff li in
      Tree.set_resolved node (Tree.ROp (intern (name_of eff_name ^ "." ^ name_of op)));
      let args_row, op_ret =
        match repr (Unify.instantiate level scheme) with
        | TArrow (a, r, _) -> (a, r)
        | _ -> bug "操作スキーマが矢印型ではありません"
      in
      Unify.unify (elab_exp env level eff arg) args_row;
      (try Unify.unify eff (TRowExtend (eff_name, t_unit, new_row_var level))
       with Type_error msg ->
         (* pub で @ を省略した宣言の本体の行は、純粋を表す Rigid である。その行と
            衝突したときだけ、規則を名指しで案内する(一般の文言
            「行型ではありません: ς1」では原因に結びつかない) *)
         let pub_pure =
           let _, tail = row_fields eff in
           match repr tail with
           | TVar r -> ( match !r with Rigid i -> Hashtbl.mem pub_pure_rows i.vid | _ -> false)
           | _ -> false
         in
         if pub_pure then type_error "pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください)"
         else type_error ("エフェクト " ^ name_of eff_name ^ " をここでは実行できません(" ^ msg ^ ")"));
      op_ret
(* ## 11.16 環境に置く resume の型

   `resume` の型付けは、`env.resume_ty` が `Some` のときだけ通る。
   `Some` が入るのは操作節の中だけなので、resume を操作節の中でしか書けないことが、
   環境の形だけで保証される。

   2 つ組の中身は、操作の返り値型と handle 式全体の型である。
   `resume(v)` は `v` を操作の返り値型と単一化し、handle 式全体の型を返す。
   これは深いハンドラの型付けそのものである。
   resume を呼ぶと残りの計算が同じハンドラの下で最後まで走り、その最終結果が返ってくることを、
   この型が表している。

   引数の省略は、操作の返り値型が Unit のときだけ許す(sample.kel:545)。
   `Unit` と単一化するだけなので、規則は 1 行で済む。

   resume を値の環境に入れず `env` のフィールドにするのは、
   値として束縛できないようにするためである。
   値として束縛できると、節を抜けた後に呼べる継続が作れてしまい、
   cancel による自動の巻き戻しが成り立たなくなる。
   環境の形だけでは防げない閉包への閉じ込めは、§11.21 の 2 段の検査で扱う。 *)

  | T.Handle (body, clauses) -> elab_handle env level eff clauses body
  | T.Resume arg -> (
      match env.resume_ty with
      | None -> type_error "resume は操作節の中でのみ使えます"
      | Some (op_ret, tres) ->
          (match arg with
          | Some e -> Unify.unify (elab_exp env level eff e) op_ret
          | None ->
              (* 引数省略は操作の返り値型が Unit のときだけ(sample.kel:545) *)
              Unify.unify t_unit op_ret);
          tres)
(* ## 11.17 run

   `run h { ... }` はスコープ付きの可変状態である。
   中で作った `Ref` を外に持ち出せないことを、ランク 2 多相を入れずに保証する。
   実装は次の 3 つの手順からなる。

   1. 結果用の変数を、スコープの外のレベル L で作る
   2. 剛定数 `h` を、1 つ深いレベル L+1 で作る。これがリージョンの名前になる
   3. 本体をレベル L+1 と行 `{Heap[h] | eff}` で推論し、最後に結果用の変数と単一化する

   手順 3 の単一化で `occurs_adjust` が走り、本体の型に残るレベル L+1 の変数を調べる。
   未定変数なら、レベルを L に下げて済む。
   剛定数はレベルを下げられないので、脱出検査がエラーにする(§8.3)。
   この検査が働くのは、結果用の変数をスコープの外のレベル L で作るからである。
   L+1 で作ると、`occurs_adjust` は L+1 の剛定数を漏れとみなさず、剛定数が検査を素通りする。
   Diktor はレベルを大域状態に持たず、引数で渡す。
   そのため脱出検査に効くのは、2 つの変数を作る順序ではなく、それぞれを作るレベルである。

   同じ形は、注釈の型パラメータの扱いにも現れる。
   §11.25 の `make_rigids` と §11.28 の `lvl = level + 1` は、
   注釈の型パラメータを剛定数にして本体を検査する。
   その剛定数は、スコープを出るところで Generic に変える。
   名前が違うだけで、行っていることは run と同じである。

   `Ref[h, A]` という型に加えてエフェクト行にも `Heap[h]` を置くのは、
   `run h { let r = Ref.new(0); fn() => Ref.get(r) }` のような式があるからである。
   返る関数の型に `h` は現れず、`h` はエフェクト行にだけ残る。
   行を調べなければ、この関数はリージョンの外へ逃げる。

   `h` のカインドは `Type` である(仕様 §10)。
   `new_rigid` を既定のカインドで呼ぶからで、リージョン専用のカインドは持たない。
   帰結は 2 つある。
   行の位置に書いた `@ h` は「行カインドではない型パラメータです: h」で落ちる。
   値の型の位置に書いた `(h) => Int32` は通る。
   値の型の位置が要求するのはカインド `Type` だからである(§11.3)。
   `test/kinds.t` の regionkind / regionkind2 が、この 2 つを確かめる。

   リージョン専用のカインドを設けても、得られるのは値の型の位置に `h` と書けなくなることだけである。
   値の型の位置に `h` を書けても、`h` の値を作る手段はどこにも無いので、健全性は破れない。
   一方、専用のカインドを設けるには、第1章のカインドの定義、`same_kind` と `kind_of`、宣言表、
   `show_kind`、組み込みスキーマを書き換える必要がある。

   入れ子の run の内側で外側の `Ref` を読めないのは仕様どおりで、
   Haskell の ST と同じリージョン安全性である。
   単一化は、これを第8章 §8.7 が述べる剛定数どうしの不一致として報告する。 *)

  | T.Run (h, body) ->
      (* 結果用の変数はスコープの外の level で、Rigid は level+1 で作り、
         本体を level+1 と Heap[h] の行で推論する *)
      let result = new_var level in
      let heap = new_rigid (level + 1) in
      let env2 = { env with types = SMap.add h heap env.types } in
      let t = elab_exp env2 (level + 1) (TRowExtend (eff_heap, heap, eff)) body in
      Unify.unify result t;
      result

(* ## 11.18 コンストラクタの適用

   式でのコンストラクタの適用は、パターン側(§11.8)と対になる処理である。
   違いは 2 つある。

   - 式では全フィールドが必須である。
     パターンでは欠落を `_` と読むが、値を作るときに欠けたフィールドを黙って埋める意味はない。
   - 割り付けの向きが逆である。
     パターンは「フィールド → 実引数」、式は「実引数 → フィールド」の配列を木に書く。
     評価器が引数をソースの順に評価しながら、
     その値をこの配列でフィールドの位置へ書き込めるようにするためである。

   `eff` が要るのは、引数を推論するときだけである。
   引数の無いコンストラクタは `elab_exp` の `Ident` の経路からも来るので、
   `eff` を省略可能な引数にしている。
   引数があるのに `eff` が無いのは呼び出し側の誤りなので、`bug` で落とす。
   型検査器の内部の矛盾は、利用者のプログラムの誤りではない。

   newtype のフィールドの矢印は書いたとおりに読み、`@` の省略は `@ {}` と読む(仕様 §9)。
   コンストラクタの引数の単一化が行の不一致で落ちたときは、エラーにこの規則を添える。
   たとえば、エフェクトつきの閉包を newtype に入れて純粋な関数として取り出そうとする形は、
   この単一化で落ち、この規則を添えたエラーになる。
   行に由来する失敗かどうかは、§11.12 と同じ `row_failure` で判定する。 *)

and elab_construct env level node cname ?eff args =
  let ctor = intern cname in
  match Hashtbl.find_opt Decls.ctor_owner ctor with
  | None -> type_error ("未知のコンストラクタ: " ^ cname)
  | Some dname ->
      (* コンストラクタの可視性は、所属する newtype の pub に従う *)
      Decls.check_ctor_visible ctor dname;
      let dd = Hashtbl.find Decls.datas dname in
      if dd.Decls.dd_opaque then type_error ("newtype " ^ name_of dname ^ " の表現は ??? で隠されています")
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
            (* エフェクトつきの閉包を newtype に入れる形はここで落ちるので、
               行に由来する失敗だけを §9 の規則で言い換える *)
            try Unify.unify ety fty
            with Type_error msg when row_failure msg ->
              type_error
                (msg ^ "(コンストラクタ " ^ cname
               ^ " のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)"))
          args;
        TCon (dname, List.map snd subst)

(* ## 11.19 検査モード

   §11.12 で述べた、引数を期待型で検査する処理(軽い双方向化)は、`elab_check` が実装する。
   期待型を押し込むのは、ラムダとレコード拡張(呼び出しの引数レコードはこの形に脱糖される)の 2 種類だけで、
   それ以外は通常どおり型を合成してから単一化する。
   合わない形に出会ったら黙って `fallback` に落ちるので、
   検査モードが失敗して全体が落ちることはない。

   ラムダの分岐は、期待型が矢印で、引数が閉じた `_item` 行で、個数が一致するときだけ働く。
   このとき本体は、期待型のエフェクト行 `eexp` で推論する。
   そのため、ラムダの本体に入る前に行のラベルが確定する。

   呼び出しの引数リストは、`_item` の `RecordExtend` の連なりに脱糖されている(第3章)。
   そのため、レコード拡張の分岐も要る。
   期待型の行から `rewrite_row` でフィールドを 1 つ取り出し、その型で値を検査し、
   残りを再帰的に検査する。
   この連鎖があるので、期待型が第 2 引数のラムダまで届く。
   `rewrite_row` が失敗する(そのラベルが無い)場合も `fallback` に落とし、
   エラーは通常の経路の単一化に報告させる。

   検査に成功したノードにも、`set_ty` で型を書く。
   期待型を押し込んだノードは `elab_exp` を通らないので、ここで書かないと、
   木に型の無いノードが残る。 *)

and elab_check env level eff ((_, e) as node : T.exp) expected =
  at_node node @@ fun () ->
  let fallback () = Unify.unify (elab_exp env level eff node) expected in
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
            elab_check env2 level eexp l_body rexp;
            (* 検査モードのラムダも、引数パターンを網羅性検査のキューに積む。注釈の
               ある高階関数の引数に渡したラムダはこちらを通るので、推論側だけで積むと、
               最も普通のラムダが検査を素通りする。本体の後に積むのは、本体の中の
               let の drain に食われて行が早く閉じないようにするため *)
            List.iter2 (fun p (_, t) -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) l_params fields)
          else fallback ()
      | _ -> fallback ())
  | T.RecordExtend (rest, l, v), TRecord row -> (
      match Unify.rewrite_row row (intern l) with
      | fty, rest_row ->
          Tree.set_ty node expected;
          elab_check env level eff v fty;
          elab_check env level eff rest (TRecord rest_row)
      | exception Type_error _ -> fallback ())
  | _ -> fallback ()

(* ## 11.20 操作名の解決

   Keleut は操作名の重複を許す。
   仕様の sample.kel 自身が `Console.write`(:464)と `File.write`(:590)を両方宣言しているので、
   操作名が大域で一意だとは仮定できない。

   修飾された操作名は、宣言表を直接引く。
   修飾されていない操作名は、次の 2 段の規則で解決する。

   1. 操作名を宣言しているエフェクトが 1 つなら、行に現れているかどうかを問わず、それに解決する。
      候補が 1 つなら推測の余地が無い。
      注釈の無い `let` の行は新しい変数なので、その中の perform の行には候補が 1 つも現れない。
      1 段目でも候補が行に現れることを求めると、
      そうした perform はすべて修飾しなければならなくなる。
   2. 候補が 2 つ以上のときだけ、現在の `eff` 行に現れる候補のうち、最左のものを採る。

   `test/typecheck_m6.t` の onecand / twocand が、この 2 段の振る舞いを確かめる。
   宣言が先の候補を選ぶ、という規則は採らない。
   それでは解決が宣言の順序に依存し、書き手の意図と違う操作に解決しうる。

   2 段目で最左を採るのは、行に現れるかどうかだけでは候補を 1 つに絞れないからである。
   §11.12 の `copy` では、行に `File` も `Console` も見えていて、`write` が両方に該当する。

   行が handle の入れ子から推論で組み立てられる場合、最左は最も内側のハンドラである。
   §11.24 は本体の行を `TRowExtend (label, …, outer)` と積むので、
   内側のハンドラのラベルほど左に来る。
   そのため、この規則は Scoped Labels の最左一致とも、
   実行時に最も内側のハンドラが捕まえることとも一致する。
   `copy` の `write` が `File.write` になるのは、`with_file` が積んだ `File` が `Console` より内側、
   つまり行の左にあるからである。
   これは、直近に開いたファイルに書くという、人が読んだときの直感とも一致する。

   ただし、行を注釈に明示的に書いたときは、最左は書かれた順序で決まり、入れ子の順序とは限らない。
   同じ名前の操作を持つ `E1` / `E2` について、`@ {E1, E2}` の関数の `perform op` は、
   `E2` のハンドラが内側にあっても `E1` に解決される。
   型は `test/typecheck_m6.t` の leftmost.kel が、
   実行との一致は `test/eval.t` の leftmostrun.kel が確かめる。
   推論された行の最左が最も内側のハンドラになるのも、正確には、
   その式に至る文の並びが handle の入れ子と同じ順序である場合に限る。
   行は、本体の推論が触れた順に伸びるからである。
   それでも、静的な解決と実行時の捕捉は食い違わない。
   perform は解決済みの完全名の oid を運ぶので、`E2` のハンドラが `E1.op` を捕まえることはない。
   `E1.op` は `E2` のハンドラを素通りして、`E1` のハンドラに届く。

   2 段目で行に候補が 1 つも現れないときは、推測せず、`File.write` のように修飾するよう案内する。

   行の並びは解決にだけ使い、型の等価性には使わない。
   順序だけが違う行どうしは単一化できる(`test/typecheck_m6.t` の roworder)。 *)

and resolve_perform eff li =
  match li with
  | LongId [ ename; op ] -> (
      let e = intern ename in
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
          (* 現在の eff 行に現れる候補のうち、最左を採る。推論された行では最左が
             最も内側のハンドラ、注釈された行では書かれた順で最左が決まる(§11.20) *)
          let labels = List.map fst (fst (row_fields eff)) in
          let pos e =
            let rec go i = function [] -> None | l :: tl -> if l = e then Some i else go (i + 1) tl in
            go 0 labels
          in
          let ranked = List.filter_map (fun e -> Option.map (fun i -> (i, e)) (pos e)) many in
          match List.sort compare ranked with
          | (_, e) :: _ -> (e, opo, List.assoc opo (Option.get (Decls.find_effect e)).Decls.ef_ops)
          | [] ->
              type_error
                ("操作 " ^ op ^ " は複数のエフェクト("
                ^ String.concat ", " (List.map name_of many)
                ^ ")に属します。" ^ name_of (List.hd many) ^ "." ^ op ^ " のように修飾してください")))
  | li -> type_error ("不正な操作名です: " ^ show_long_id li)

(* ## 11.21 resume の第二級性

   resume は専用の構文木のノード(`Resume`)で、名前ではないので、
   変数に束縛することも値として渡すこともできない。
   それでも、構文だけでは第二級性は保証されない。

   ```
   case print(m) => { let f = fn() => resume(); f() }
   ```

   この節は書ける。
   `resume` 自体は値になっていないが、それを含む閉包が値になっており、節の外へ持ち出せる。

   そこで、次の 2 段で第二級性を守る。

   1. 静的な検査：`check_resume_static` が節の本体を走査し、ラムダの内側の `Resume` をエラーにする。
   2. 動的な検査：節が終わるときに継続の生死のフラグ(第14章の `r_alive`)を下ろし、
      その後の resume の呼び出しを実行時エラーにする。

   静的な検査がラムダとして扱うのは、ラムダ式(`Lambda` のノード)だけである。
   節の中のローカルな関数束縛(`let f() = resume(41)`)の本体は、
   `Let` / `LetRec` の分岐が外側と同じ `in_lambda` のまま走査するので、
   そこに書いた resume は静的な検査を通る。
   その関数を節の外へ持ち出して呼ぶと、
   動的な検査が「resume を節の外で呼び出しました(second-class)」で止める。

   走査の途中で内側の `Handle` に出会ったら、その本体は走査し、節には入らない。
   内側のハンドラの節は、その節自身が検査を受けるときに、自分の文脈で調べられるからである。
   ここで節に入ると、内側の resume を外側の resume と取り違える。

   2 段の検査により、継続は節の外で呼べない。
   そのため、節を抜ける時点で継続の生死が確定し、
   cancel による自動の巻き戻しが成り立つ(sample.kel:542-545)。
   継続がどこかの閉包に生き残っている可能性があると、巻き戻しの時点を決められない。 *)

and check_resume_static ?(in_lambda = false) (((_, e) as node) : T.exp) =
  at_node node @@ fun () ->
  let go = check_resume_static ~in_lambda in
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
  | T.Not v -> go v
  | T.Let ((_, b), rest) ->
      go b.T.lb_body;
      go rest
  | T.LetRec (bs, rest) ->
      List.iter (fun ((_, b) : T.let_binding) -> go b.T.lb_body) bs;
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

(* ## 11.22 handle の節を 3 種類に分ける

   handle の節は、エフェクト名ではなく操作名で書く。
   パーサから見ればどれもコンストラクタパターンなので、意味づけはここで行う。

   | 節の形 | 種別 | 意味 |
   |---|---|---|
   | `case print(m) =>` | 操作節 | 小文字始まりの名前は操作。`Print.print` と修飾もできる |
   | `case return(x) =>` | return 節 | 本体が値を返し切ったときの後処理。1 つまで。修飾できない |
   | `case cancel =>` | cancel 節 | 巻き戻されたときの後始末。1 つまで。修飾できない |

   `return` と `cancel` は予約語ではなく、この分類器が名前で区別しているだけである。
   `cancel` は引数を取らない形だけを受け付ける。
   `cancel(reason)` の形は Diktor が実装しておらず、`noimpl` で報告する。
   操作節は 1 つ以上必要である。
   操作を 1 つも扱わない handle は、書き手の誤りとみなす。

   修飾できるのは操作節だけである(sample.kel:514-515)。
   `return` と `cancel` は操作名ではなく handle の節の名前なので、修飾先を書いても、
   対象エフェクトの決定には何も寄与しない(§11.23)。
   分類器は `List.rev comps` の先頭、つまり修飾名の末尾の部分で節を分類する。
   そのため、修飾された `return` / `cancel` は専用の分岐で捕まえ、修飾を外すよう促してエラーにする。
   この分岐は、`cancel` / `return` の分岐より前に置く必要がある。
   後ろに置くと、末尾の部分だけを見る分岐が先に一致し、
   `case File.return(x)` の `File.` が黙って捨てられる。
   `test/typecheck_m6.t` の qualret / qualcancel が、この振る舞いを確かめる。

   操作節は、同じ操作に対して複数書ける。
   書き手は絞り込みパターンやガードで場合を分け、
   評価器は実行時に match と同じフォールスルーで節を選ぶ。
   総和的な節(ガードが無く、引数パターンがすべて反駁不能な節)より後ろに同じ操作の節を書くと、
   その節には到達しないので、警告を出す(§11.24)。

   分類の結果は、`set_resolved` で木に書く。
   評価器が節の種別を判定し直さないようにするためで、§11.8 と同じ方針である。 *)

and elab_handle env level eff clauses body =
  let classify ((_, c) as cnode : T.clause) =
    match snd c.T.cl_pat with
    | T.PVar "cancel" -> `Cancel cnode
    | T.PCtor (LongId comps, args) -> (
        match List.rev comps with
        (* return / cancel は操作名ではないので修飾できない。この分岐を
           `cancel` / `return` の分岐より前に置かないと、修飾名の末尾だけを見る
           後続の分岐が先に一致し、修飾が黙って捨てられる *)
        | (("return" | "cancel") as kw) :: _ :: _ ->
            type_error (kw ^ " 節は修飾できません(" ^ kw ^ " は操作名ではなく handle の節の名前です。修飾を外してください)")
        | "cancel" :: _ ->
            if args <> [] then noimpl "cancel(reason)(v0 は case cancel のみ)" else `Cancel cnode
        | "return" :: _ -> (
            match args with
            | [ { T.cap_label = None; cap_pat } ] -> `Return (cap_pat, cnode)
            | _ -> type_error "return 節は case return(x) の形で書いてください")
        | op :: quals when op <> "" && op.[0] >= 'a' && op.[0] <= 'z' ->
            `Op (intern op, (match quals with [] -> None | _ -> Some (intern (String.concat "." (List.rev quals)))), args, cnode)
        | _ -> type_error ("handle の節は操作名 / return / cancel で始めてください: " ^ show_long_id (LongId comps)))
    | _ -> type_error "handle の節は操作名 / return / cancel で始めてください"
  in
  let classified = List.map classify clauses in
  let ops = List.filter_map (function `Op (op, q, args, cnode) -> Some (op, q, args, cnode) | _ -> None) classified in
  let rets = List.filter_map (function `Return (p, cnode) -> Some (p, cnode) | _ -> None) classified in
  let cancels = List.filter_map (function `Cancel cnode -> Some cnode | _ -> None) classified in
  (if List.length rets > 1 then type_error "return 節は1つまでです");
  (if List.length cancels > 1 then type_error "cancel 節は1つまでです");
  (if ops = [] then type_error "handle には少なくとも1つの操作節が必要です");
(* ## 11.23 対象エフェクトの決定

   節は操作名で書くので、このハンドラがどのエフェクトを消すのかを決める必要がある。
   規則は 2 段である。
   仕様 §9 は、修飾のない操作名の解決規則を perform と handle で書き分けている(sample.kel:517-527)。
   この 2 段は、そのうち handle の側にあたる。

   操作節が 1 つでも修飾されていれば、その修飾先が対象である。
   修飾されていない節は、そのエフェクトの操作として読む。
   修飾先が 2 つ以上に割れていれば、エラーにする(sample.kel:526-527)。
   実装は下の `List.sort_uniq compare quals` の 1 行である。
   要素が 1 つなら対象が決まり、2 つ以上ならエラーになり、空なら次の段へ進む。
   材料は操作節の修飾だけである。
   修飾された `return` / `cancel` は §11.22 が先に落とすので、ここへは届かない。
   曖昧な節を 1 つ修飾したら、残りの節もすべて修飾しなければならない、という読み方は採らない。
   修飾は曖昧さを解消する手段であって、書式の要求ではないからである。
   `test/typecheck_m6.t` の qual1〜qual4b が、この段を確かめる。
   qual4 と qual4b は、同じ handle を修飾して書いたものと修飾せずに書いたものの対である。
   2 つの診断の違いが、修飾が対象の決定に効いていることを示す。

   どの節も修飾されていなければ、次の手順で絞る。

   1. すべての操作名を宣言しているエフェクトを集める(`holds_all`)
   2. そのうち、自分の全操作がこの handle に書かれているものだけを残す(`covered`)
   3. ちょうど 1 つなら、それが対象である。0 個なら網羅漏れ、2 個以上なら曖昧としてエラーにする

   手順 1 は、書いた操作名のどれかを宣言していないエフェクトを外す。
   たとえば `Console` と `File` は、操作名 `write` が重なる。
   それでも `read` と `write` の両方を書けば、
   `read` を宣言しない `Console` は手順 1 の条件を満たさない。
   手順 2 は、書いた操作をすべて宣言したうえで、ほかの操作も持つエフェクトを外す。
   `File` のほかに `read` / `write` / `close` を持つエフェクトがあっても、
   `read` と `write` の節だけを書けば `File` に決まる。

   ランタイムが提供するエフェクト(プレリュードの `Console` / `Async` / `Fs`)はハンドルできない。
   これらは手順 1 の候補からも外す。
   `Console` を候補に残すと、`write` 節だけを書いた handle は、
   全操作が書かれている `Console` に手順 2 で決まる。
   候補から外すので、この handle は `Console` には決まらず、
   「File の read が漏れています」で落ちる。
   `File` のつもりで `write` 節だけを書いた誤りは、この診断でそのまま分かる。
   `File` を意図していたなら、`File.write` と修飾するか、`read` 節も書けばよい。
   `Fs` は操作を持たないので候補には現れず、修飾して名指ししたときだけ、
   ハンドルできないという診断になる。
   網羅漏れのエラーになるのは、どの候補も自分の全操作を覆えていないときである。
   2 つの操作を持つエフェクトの片方だけを書いた場合などが、これにあたる。

   修飾されたエフェクトが実在するかどうかは、対象を決める時点で調べる。
   調べないと、後段の `Option.get` が `None` を受け取り、
   型エラーとして報告すべきものが OCaml の例外としてそのまま外に出る。

   対象が決まったら、逆向きの検査を 2 つ行う。
   対象の全操作が節にあるかどうかと、すべての節が対象に属するかどうかである。
   網羅を要求するのは、handle 式の行から対象エフェクトを除く型付けにしているからである(§11.24)。
   網羅を先に調べるので、両方の誤りを含む入力では網羅漏れを報告する。
   `test/typecheck_m6.t` の qual5 が、この順序を確かめる。 *)

  (* 対象エフェクトは、全節が属し全操作が網羅される候補として一意に決まらなければならない *)
  let quals = List.filter_map (fun (_, q, _, _) -> q) ops in
  let op_names = List.map (fun (op, _, _, _) -> op) ops in
  (* ランタイムが提供するエフェクトはハンドルさせない。仕様 sample.kel:534 が
     Console / Async / Fs の 3 つを名指しで定める(Async については :724 にも
     「スケジューラを利用者に書かせない」とある)。許すと、出力を黙って消す
     恒等ハンドラが書け、File.write のつもりの case write(s) が Console を
     消すことも起きる。判定は、ランタイムの名簿に名前があり、かつプレリュードが
     宣言したものであること。--no-prelude で利用者が自分の effect Console / Fs を
     宣言した場合は禁止しない。修飾された節では、この判定が
     「操作 X はエフェクト Y に属しません」より先に走る。Heap / Blocking は名簿に
     無いので禁止されない。名簿に入れると case Blocking.nope() の診断がこちらに
     すり替わる(第7章 §7.3)。Fs は操作を持たないので、修飾しなければ候補に
     挙がらず、修飾したときだけここに届く *)
  let runtime_provided e = List.mem (name_of e) Prims.runtime_effects && Decls.prelude_owned "effect" e in
  let runtime_msg e =
    match name_of e with
    | "Console" ->
        "エフェクト Console はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:464, :534)。出力先を変えたいときは Print をハンドルしてください(プレリュードの with_stdout が Print を Console へ翻訳します)"
    | "Fs" ->
        "エフェクト Fs はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:465, :534)。ファイル操作を差し替えたいときは File のような自前のエフェクトをハンドルしてください(仕様 sample.kel:600 の with_file が見本)"
    | n -> "エフェクト " ^ n ^ " はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:724。スケジューラは書けません)"
  in
  let target =
    match List.sort_uniq compare quals with
    | [ e ] ->
        (* 修飾されたエフェクトが実在するかを調べる(調べないと後段の Option.get で落ちる) *)
        if Decls.find_effect e = None then type_error ("未知のエフェクト: " ^ name_of e)
        else if runtime_provided e then type_error (runtime_msg e)
        else e
    | _ :: _ -> type_error "handle の節の修飾エフェクトが一致しません"
    | [] -> (
        let declares e op = List.mem_assoc op (Option.get (Decls.find_effect e)).Decls.ef_ops in
        let candidates = List.sort_uniq compare (List.concat_map Decls.op_candidates op_names) in
        (* ランタイムが提供するエフェクトを候補から外す。case write(s) 1 本の
           handle は Console ではなく「File の read が漏れています」に落ち、
           意図の取り違えがそのまま診断になる。候補がすべてランタイムの提供する
           ものだったときだけ、その旨を名指しで伝える *)
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
                  ("ハンドラが操作を網羅していません: " ^ name_of e ^ " の "
                  ^ String.concat ", " (List.map (fun (op, _) -> name_of op) missing)
                  ^ " が漏れています")
            | [] -> type_error ("この操作の組を宣言するエフェクトがありません: " ^ String.concat ", " (List.map name_of op_names)))
        | es ->
            type_error
              ("handle の対象エフェクトが曖昧です(" ^ String.concat ", " (List.map name_of es)
             ^ ")。" ^ name_of (List.hd es) ^ "." ^ name_of (List.hd op_names) ^ " のように修飾してください"))
  in
  let target_info = Option.get (Decls.find_effect target) in
  (* 対象が決まったら、全操作の網羅と、全節の所属を調べる *)
  List.iter
    (fun (op, _) ->
      if not (List.mem op op_names) then
        type_error ("ハンドラが操作を網羅していません: " ^ name_of target ^ " の " ^ name_of op ^ " が漏れています"))
    target_info.Decls.ef_ops;
  List.iter
    (fun (op, _, _, _) ->
      if not (List.mem_assoc op target_info.Decls.ef_ops) then
        type_error ("操作 " ^ name_of op ^ " はエフェクト " ^ name_of target ^ " に属しません"))
    ops;
  (* 総和性の検査。各操作に、ガードが無く全引数パターンが反駁不能な節が
     1 つ以上要る。実行時の節の選択は match と同じフォールスルー(第14章)だが、
     ハンドラの外への後送り(re-perform)は無いので、すべての節が外れうる形は
     ここで拒否する。実行時に取りこぼしうるプログラムを型検査で通さない *)
  (* 反駁不能の判定は、関数の引数や return 節の網羅性検査と同じ irrefutable_pat を使う *)
  let total (_, _, args, ((_, c) : T.clause)) =
    c.T.cl_guard = None && List.for_all (fun (a : T.ctor_arg_pat) -> irrefutable_pat a.T.cap_pat) args
  in
  List.iter
    (fun (op, _) ->
      if not (List.exists (fun ((o, _, _, _) as cl) -> o = op && total cl) ops) then
        type_error
          ("操作 " ^ name_of op
         ^ " の節が取りこぼします(ガードや絞り込みパターンだけの節は v0 では後送りできません)。変数パターンでガードの無い case "
         ^ name_of op ^ "(...) を最後に置いてください"))
    target_info.Decls.ef_ops;
  (* 到達不能な操作節の警告。総和的な節より後ろにある同じ操作の節は走らない。
     この検出は match の useful 判定(第10章)より弱く、絞り込みの節の集まりで
     網羅済みでも警告は出ない。第10章の検査につなぐには、操作節から合成の
     match のノードを作る必要があり、Diktor はそれをしない。健全性は総和性検査が
     守るので、弱いのは警告の網羅性だけである *)
  let rec dead_scan seen_total = function
    | [] -> ()
    | ((o, _, _, _) as cl) :: rest ->
        if List.mem o seen_total then
          warn ("操作 " ^ name_of o ^ " の節は到達しません(前の節が既に取りこぼしません)");
        dead_scan (if total cl && not (List.mem o seen_total) then o :: seen_total else seen_total) rest
  in
  dead_scan [] ops;
(* ## 11.24 本体と各節の型付け

   handle の型付けの規則は次のとおりである。

   ```
     Γ ⊢ e : α ! {E | ε}
     Γ, x : α ⊢ r : R ! ε                        -- return 節
     Γ, x : A_op, resume : B_op -> R ⊢ b : R ! ε  -- 操作節
     ---------------------------------------------
     Γ ⊢ e handle { ... } : R ! ε
   ```

   本体だけは、対象エフェクトを積んだ内側の行で推論する。
   return 節、cancel 節、操作節は、すべて外側の `eff` で推論する。

   return 節と cancel 節は、自分のハンドラが外れた文脈で走る(第14章 §14.10)。
   内側の行で型付けると、型が許したエフェクトを実行時には起こせないという食い違いが生じる。

   操作節を外側の行で推論するのは、深いハンドラだからである。
   節の本体は、ハンドラの外側と同じ文脈で走る。

   節ごとの細部は次のとおりである。

   - resume の型は「操作の返り値型 → handle 式全体の型」である。
     これを `resume_ty` に入れて節の本体を推論する(§11.16)。
     return 節と cancel 節では `None` に戻す。そこに継続は存在しない。
   - cancel 節の値は捨てられるので、Unit と単一化する。
   - 操作節の引数はラベルで書けず、位置引数だけである。
     操作の引数は宣言の並びで意味が決まるので、並べ替えを許す理由がない。
   - return 節と cancel 節にはガードを書けない。
     節の構文(clause)は汎用なのでパーサは受け付けるが、ここで拒否する。
     この 2 つは 1 つのハンドラに 1 節までなので(§11.22)、ガードが偽のときに落ちる先がない。
     第14章の `retc` / `run_cancel` はガードを読まないので、受理すると、
     型検査を通った条件式が実行時に黙って無視される。
     `case return(x) if c => a` と書きたいときは、節の本体で `c` を match すれば同じことを書ける。
   - 操作節のガードは受理するが、`resume` の無い環境で推論する。
     第14章はガードを resume の無い環境で評価するので、ここで resume を許すと、
     型は付くのに実行時に落ちるプログラムを通してしまう。
     §11.21 の静的な検査は節の本体しか走査しないので、ガードの resume はここで防ぐ。
   - 操作節には総和性検査がある(§11.23 の網羅の検査の直後)。
     各操作に、ガードが無く全引数パターンが反駁不能な節が 1 つ以上要る。
     実行時の節の選択はフォールスルーだが、ハンドラの外への後送り(re-perform)は無いので、
     すべての節が外れうる形はここで拒否する。
     総和的な節より後ろにある同じ操作の節は到達しないので、警告を出す。
     `--strict-exhaustive` を付けると、この警告はエラーになる。

   `check_resume_static` は、操作節の本体を推論する直前に呼ぶ(§11.21)。 *)

  (* 本体は対象エフェクトを積んだ行で推論する *)
  let body_ty = elab_exp env level (TRowExtend (target, t_unit, eff)) body in
  let tres = new_var level in
  (* return 節と cancel 節は外側の eff で推論する(retc / exnc は、自分のハンドラが
     外れた文脈で走る) *)
  (match rets with
  | [ (p, ((_, c) as cnode)) ] ->
      Tree.set_resolved cnode Tree.RReturnClause;
      if c.T.cl_guard <> None then type_error "return 節にガードは書けません";
      let seen = ref [] in
      let env2 = elab_pat { env with resume_ty = None } level seen body_ty p in
      Unify.unify (elab_exp env2 level eff c.T.cl_body) tres;
      (* return 節の反駁可能なパターンも、節の本体を推論した後で網羅性検査のキューに
         積む。先に積むと、節の本体の中の let の drain に食われて行が早く閉じる *)
      if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] body_ty
  | _ -> Unify.unify body_ty tres);
  (match cancels with
  | [ ((_, c) as cnode) ] ->
      Tree.set_resolved cnode Tree.RCancelClause;
      if c.T.cl_guard <> None then type_error "cancel 節にガードは書けません";
      let env2 = { env with resume_ty = None } in
      (* cancel 節の値は捨てられるので、Unit と単一化する *)
      Unify.unify (elab_exp env2 level eff c.T.cl_body) t_unit
  | _ -> ());
  (* 操作節 *)
  List.iter
    (fun (op, _, args, ((_, c) as cnode)) ->
      Tree.set_resolved cnode (Tree.ROp (intern (name_of target ^ "." ^ name_of op)));
      let scheme = List.assoc op target_info.Decls.ef_ops in
      let args_row, op_ret =
        match repr (Unify.instantiate level scheme) with
        | TArrow (a, r, _) -> (a, r)
        | _ -> bug "操作スキーマが矢印型ではありません"
      in
      let param_tys = match repr args_row with TRecord row -> List.map snd (fst (row_fields row)) | _ -> [] in
      if List.length args <> List.length param_tys then
        type_error
          (Printf.sprintf "操作 %s は %d 引数です(節には %d 個書かれています)" (name_of op) (List.length param_tys)
             (List.length args));
      List.iter (fun (a : T.ctor_arg_pat) -> if a.T.cap_label <> None then type_error "操作節の引数にラベルは書けません") args;
      let seen = ref [] in
      let env2 =
        List.fold_left2
          (fun env (a : T.ctor_arg_pat) t -> elab_pat env level seen t a.T.cap_pat)
          env args param_tys
      in
      (* ガードは resume 無しで推論する。第14章はガードを resume = None で
         評価するので、ここで Some にすると、型は付くのに実行時に落ちる
         プログラムを通してしまう。§11.21 の静的な検査は本体しか走査しないので、
         ガードの resume はここで防ぐ *)
      (match c.T.cl_guard with
      | Some g -> Unify.unify (elab_exp { env2 with resume_ty = None } level eff g) t_boolean
      | None -> ());
      (* 操作節では resume が使える。本体は外側の eff で推論する *)
      let env2 = { env2 with resume_ty = Some (op_ret, tres) } in
      check_resume_static c.T.cl_body;
      Unify.unify (elab_exp env2 level eff c.T.cl_body) tres)
    ops;
  tres

and method_scheme cls m =
  match Decls.find_class (intern cls) with
  | Some ci -> (
      match List.assoc_opt m ci.Decls.ci_methods with
      | Some t -> t
      | None -> bug ("組み込みクラス " ^ cls ^ " にメソッド " ^ m ^ " がありません"))
  | None -> bug ("組み込みクラス " ^ cls ^ " が未登録です")

(* ## 11.25 束縛の準備と剛定数

   `let f[A](x: A): A = ...` の `[A]` を新しい未定変数にすると、
   `fn x => x + 1` を `[A] (A) => A` と注釈しても通ってしまう。
   注釈は、少なくともこれだけ多相であることを要求するものなので、それでは注釈が意味をなさない。

   そこで、型パラメータを剛定数(Rigid)にして本体を検査する(skolem 化)。
   剛定数は代入先になれないので、`A` を Int32 に決めようとした時点で単一化が落ちる。
   §11.17 の run の 3 つの手順と同じ仕組みで、`make_rigids` が 2 番目の手順(剛定数を作る)を担う。

   カインドは、`F[_]` と書かれていればその場で確定し、
   `[A]` や `[E]` のように括弧が無ければカインド変数にしておく。
   Keleut では、型パラメータが型なのか行なのかを字句で区別できず、
   使われた位置(`extends` の右か `@` の右か)でしか決まらないからである。
   未解決のまま残ったカインドは、
   剛定数を解放するとき(§11.27 の `release_rigids`)に `KStar` へ既定化する。

   剛定数は次の 3 段を経る。

   1. `make_rigids` が、束縛のレベル + 1 で作る
   2. 本体の検査の間、代入されないことと外へ漏れないことを、単一化が見張る
   3. スコープを出たら、`release_rigids` が Generic に書き換える(§11.27)

   この 3 段により、注釈つきの束縛の型は、本体の検査では剛定数を含む型として、
   環境の中では多相な型として働く。
   そのため、型スキーマ専用のデータ型は 1 つも要らない。

   制約に書かれたクラス名は、剛定数を作るこの時点で `class_names_of` が検証する。
   未知のクラスを使用点の `add_class`(§8.4)まで持ち越すと、
   `let f[A: Bogus](x: A): A = x` という宣言が通ってしまう。
   その宣言は `f : [A: Bogus] (A) => A` と印字され、呼んだ場所で初めて「未知のクラス」になる。
   これでは、どこが悪いのか利用者に分からない。 *)

(* 型パラメータに書かれたクラス名を oid にする。宣言済みでなければその場で
   落とす(§11.25)。文言は add_class と一字一句そろえる *)
and class_names_of tp =
  List.map
    (fun li ->
      let c = intern (show_long_id li) in
      if Decls.find_class c = None then type_error ("未知のクラス: " ^ show_long_id li);
      (* 予約述語は制約にも書けない。書けると [A: Integral] の A が既定化の
         対象に見え、数値リテラルが解決されないまま実行に到達する *)
      if Decls.reserved_predicate c then
        type_error (show_long_id li ^ " は予約されたリテラル述語です(制約には書けません、D8)");
      c)
    tp.tp_classes

and make_rigids ?kinds level tparams =
  (* kinds は型エイリアスの表のセル(al_kinds)。長さが合わないときは黙って
     作り直す。構築する箇所で長さは一致するので、ここは保険である *)
  let kinds =
    match kinds with
    | Some ks when List.length ks = List.length tparams -> ks
    | _ -> List.map (fun (tp : type_param) -> if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var ()) tparams
  in
  List.map2
    (fun tp kind ->
      let classes = class_names_of tp in
      let r = new_rigid_ref ~kind ~classes level in
      (tp.tp_name, TVar r, r))
    tparams kinds

(* ## 11.26 明示的なエフェクト注釈を開く

   `@ Print` をラベル 1 つの閉じた行と読むと、sample.kel:546 が型付かない。

   ```
   println(msg) handle {
     case print(message) => resume(perform write(message))
   }
   ```

   `println : (String) => Unit @ Print` の本体は `perform print(...)` である。
   しかし、この handle の下で `println` を呼ぶときは、
   行が `{Print}` ではなく `{Print, Console}` でなければならない。
   閉じた行のままでは、このハンドラの下で呼べない。

   そこで、最外の矢印に書かれた、ラベルのある閉じた行の注釈を開く。
   開くかどうかは、注釈の位置で決まる(仕様 §9、sample.kel:470-502)。

   | 位置と注釈 | 本体の検査で | 公開スキーマで |
   |---|---|---|
   | 最外 `@ Print` / `@ {A, B}` | 尾部に Rigid を足して開く(本体の上限) | 尾部を Generic にして開く |
   | 最外 `@ {}` | 閉じたまま | 閉じたまま(純粋。両方向に効く) |
   | 最外 `@` 省略(`let`) | 新しい行変数(初めから開いている) | 一般化する。本体が空に固まっていれば開き直す |
   | 最外 `@` 省略(`pub`) | Rigid の行(perform を拒む。純粋) | Generic にして開く |
   | 入れ子の `@ Print` / `@ {A, B}` | 書いたとおり閉じたまま | 開かない |
   | 入れ子の `@` 省略 | `@ {}` と同じ(純粋) | 閉じたまま |

   4 行目は、1 行目と同じ非対称(本体には剛く、公開には寛く)を、空の行にも当てはめたものである。
   仕様 §13 も、この省略では本体が純粋でなければならず、
   公開される型は行多相になると定める(sample.kel:815-821)。
   省略を閉じた空の行と読むと、sample.kel 自身が型付かない。
   `Db.query` が `handle_request` から呼べなくなる。
   4 行目の読みでは、`pub let f(): Unit`(省略)と `pub let f(): Unit @ {}`(明示)は別の型になる。
   後ろの 2 行(入れ子)は、§11.4 の表と同じ規則である。

   pub の `@` 省略には、次の制限がある。
   その本体が、一般化されていないトップレベルの束縛(パターン束縛や非値の束縛)を呼ぶと、
   本体が純粋でも、その束縛の単相な行変数を Rigid に結ぼうとして落ちる。
   診断は pub の規則を名指しして元の報告を添えるので、利用者は直し方にたどり着ける。
   直し方は、束縛を関数として宣言し直すか、`@` を明示することである。
   また、通常の行と同じく、Rigid の行から `@ {}` の関数を呼ぶこともできない。
   これは行の部分型付けを持たない設計の帰結である。

   本体の検査で尾部を剛定数にするのは、注釈の約束を守らせるためである。
   未定変数で開くと、本体が注釈に書いていないエフェクトを起こしたときに、
   それが尾部に足されて通ってしまう。
   剛定数には何も足せないので、そうした本体は単一化で落ちる。
   スコープを出るところで Generic に変えるので、呼び出し側は好きな行を尾部に継ぎ足せる。

   `@ {}` は閉じたままにするので、
   純粋を強制する意図は書ける(sample.kel:481「`@ {}` だけは両方向に効く」)。
   `@ Print` は、最外なら Print を含む上限を表し(sample.kel:476-479)、
   入れ子なら書いたとおり Print だけの閉じた行を表す(sample.kel:496-498)。

   空に固まった行は公開の前に開き直すが、書かれた `@ {}` は開かない(sample.kel:490-491)。
   `@` を省略した `let` の行は、最初は行変数である。
   しかし本体が `@ {}` の関数(入れ子の省略 `@` を含む)を呼ぶと、単一化で空に固まる。
   入れ子の省略 `@` を `@ {}` と読むので、これは普通に起きる。
   そのままでは、`count_if` のような関数が、エフェクトのある文脈から呼べない関数になる。
   そこで `reopen_pure_row` が、公開の直前に、空に固まった最外の行を新しい行変数に組み直す。
   行が空に固まったことは、本体がエフェクトを起こさないことの証明なので、
   開き直しても健全である(`test/annot_rows.t` の val1 / val2 / rec2 / alval)。

   開き直しには 3 つのガードがある。

   - 値制限：一般化しない束縛の行を開くと、`run` の剛定数が漏れる経路に乗る。
   - 明示の `@`：`let k: (Int32) => Int32 @ {}` を開くと、`@ {}` が両方向に効くという約束が破れ、
     `k(1)` が `@ Console` の文脈から通ってしまう。
   - `pub`：pub の省略 `@` には Rigid の行を置く別の経路があるので、開き直しの対象から外す。
     Rigid の行は空に固まらないので、このガードが効く形は無く、保険である。

   頭が型エイリアスの値束縛も開き直さない。
   展開先の矢印は入れ子なので、省略は `@ {}` と読み、書かれた `@ {}` は両方向に効く。
   パス 1c の署名(§11.37)も同じ閉じた行を公開するので、公開される型は宣言の順序に依存しない。

   ### 表の 1 行目と 4 行目は値束縛にも当てはまる

   値束縛(引数リストを持たない `let`)の注釈の頭の矢印も、
   束縛の最外として扱う(sample.kel:485 と :492)。
   そのため、`let kf(x: Int32): Int32 @ Print` と `let k: (Int32) => Int32 @ Print` は、
   どちらも開いた行 `{Print extends R1}` を公開し、`{Print, Log}` の文脈から呼べる。
   仕様 §9 は、公開される型では行変数で行を開くと定めており(sample.kel:478)、
   引数リストの有無で扱いを分ける理由はない。

   `open_explicit_eff` を呼ぶのは、次の 8 か所である。

   - 値束縛以外の 5 か所：関数束縛、`let rec` の関数束縛、パス 1c の関数束縛の署名、
     クラスメソッドの型、`extern`
   - 値束縛の 3 か所：`elab_binding` と `elab_rec_bindings` の値束縛の分岐、
     パス 1c の `signature_of_binding`(§11.37)の値束縛の分岐

   値束縛の 3 か所は、注釈の頭が矢印リテラルかどうかを表層の構文(`snd t`)で調べてから開く。
   頭が型エイリアスなら、展開先の矢印は入れ子なので開かない。
   クラスメソッドが `snd v.T.cv_ty` を調べるのと同じ規則である(§11.33)。

   表の 4 行目の `pub` の省略 `@` では、本体を検査する `elab_binding` と、
   本体を見ないパス 1c の署名とで、行に置くものが違う。
   `elab_binding` は、`pub_pure_rows` に載せた Rigid を置いて本体に純粋を要求し、
   公開のときに Generic へ解放する。
   値束縛でその Rigid が載るのは注釈の頭の矢印の行なので、純粋を要求されるのも頭の矢印の本体である。
   初期化式そのものは、束縛の外側の行で推論する(§11.28)。
   パス 1c の署名は、値束縛では行変数をそのまま置き、
   `Unify.generalize 0` がそれを Generic に変える。
   関数束縛の署名では、`pub_pure_rows` に載せない Rigid を置き、
   `release_rigids` ですぐ Generic に変える。
   `let rec` の値束縛では、`elab_rec_bindings` が頭の矢印の行に `pub_pure_rows` の Rigid を置かず、
   頭の `@` の省略を `check_pub_annots` が拒否する(§11.29)。

   関数束縛と値束縛では、注釈の行で上限を掛ける仕組みが違う。
   関数束縛では、注釈の行が本体を検査する行になるので、本体が起こすエフェクトがそこへ足される。
   値束縛では、注釈の型と本体の型を単一化するので、本体の行が閉じたまま固まっていると、
   尾部の Rigid と一致しない。
   `type F = (Int32) => Int32 @ Console` を注釈にして束縛した関数 `g` を、
   `let k: (Int32) => Int32 @ Console = g` へ入れ直す形がこれにあたる。
   同じ `g` を関数束縛の本体から呼んでも同じ理由で落ちるので、
   この点で値束縛と関数束縛の振る舞いは同じである。
   これも行の部分型付けを持たない設計の帰結である。
   注釈をエイリアスで書けば、入れ子の読みになって通る(`test/annot_rows.t` の valclosed / valclosedfn / valclosedok)。 *)

and open_explicit_eff lvl eff =
  let fields, tail = row_fields eff in
  match repr tail with
  | TRowEmpty when fields <> [] ->
      let r = new_rigid_ref ~kind:KRow lvl in
      (row_append eff (TVar r), [ ("", TVar r, r) ])
  | _ -> (eff, [])

(* ## 11.27 剛定数の解放

   束縛のスコープを出るとき、`release_rigids` はこの束縛が作った剛定数を Generic に書き換える。
   これが注釈の一般化である。
   書き換えはその場で行う。
   木にはすでに `set_ty` 済みの型が入っていて、それとの共有を切らないためである。

   安全性の根拠は、書き換える側ではなく検査する側にある。
   剛定数が外へ漏れていれば、ここに至るまでに `unify` と `occurs_adjust` が捕まえている(第8章)。
   ここまで来たなら剛定数は漏れていないので、無条件に Generic にしてよい。
   ただし `let rec` の群では、相手の束縛をまだ検査していない時点でここへ来る経路があるので、
   相手に入り込んだ剛定数の解放を群の終わりまで遅らせる(§11.29)。

   カインドの既定化もここで行う。
   `[E]` と書かれたきりどこにも使われなかった型パラメータは、カインドが `KVar` のまま残る。
   `release_rigids` は、それを `KStar` に既定化する。 *)

and release_rigids rigids =
  List.iter
    (fun (_, _, r) ->
      match !r with
      | Rigid i ->
          default_kind i.vkind (* 未解決のカインドは KStar に既定化する *);
          r := Generic i
      | _ -> ())
    rigids

(* ## 11.28 let 束縛

   束縛の処理は、レベルを 1 つ上げ、型パラメータを剛定数にし、注釈を精緻化し、本体を推論し、
   注釈と単一化し、一般化して、剛定数を解放する。
   run と同じ 3 つの手順の形を、ここでは注釈のために使う。

   ### 一般化してよいのは、関数か構文的な値のとき

   ```
   let gen = is_fun || is_value b.T.lb_body
   ```

   この 1 行が値制限のすべてである。
   注釈が書いてあることは、一般化の条件に含めない。
   次の束縛は注釈を持つが、右辺の `Ref.new(...)` は関数の適用で値ではないので、一般化しない。

   ```
   let slot: Ref[h, T] = Ref.new(...)
   ```

   注釈は、多相にしてよいことの証明にならない。
   多相にしてよいことを示すのは、値であることだけである。
   一般に、非値の束縛の型に残った未定変数を一般化すると、可変参照を通じて不健全になる。

   同じ理由で、非値の束縛に型パラメータを書くことも拒否する。
   型パラメータを書くことは多相化の要求であり、値制限に反する。

   一方、本体が純粋であることは、行を多相にしてよいことの証明になる(§11.26 の `reopen_pure_row`)。
   値であることが型の多相の根拠であるのに対し、こちらは行の多相の根拠である。
   ただし、行を開き直すのも一般化する束縛に限る(§11.26 の 1 つ目のガード)。

   ### 一般化しないときはレベルを上げない

   `lvl = if gen then level + 1 else level` の 1 行で済む。
   レベルを上げなければ `generalize` は何も一般化しないので、フラグも後処理も要らない。

   ### 注釈の精緻化は 1 回で済む

   注釈は 1 回だけ精緻化する。
   `release_rigids` が剛定数をその場で Generic に書き換えるので(§11.27)、
   同じ型が、本体の検査では剛定数を含む型として、環境への登録では多相な型として、順に働く。
   木に `set_ty` 済みの型との共有も切れない。

   返り値の注釈があれば本体の型と単一化し、失敗を「注釈された返り値型を満たしません」に言い換える。
   値束縛でも同じことをする。
   どちらも、注釈が書かれているときだけ言い換える。
   単一化を try で包み、エラーを注釈や宣言の側から述べ直す箇所は、この 2 つのほかに次の 4 つがある。

   - 適用の単一化(§11.12)
   - perform の行の単一化(§11.15)
   - コンストラクタの引数の単一化(§11.18)
   - インスタンス本体の包摂(§11.38)

   いずれも包むのは `Unify.unify` だけなので、`Type_error_at` を調べる必要はない。

   ### 値束縛の注釈は、頭の矢印だけ扱いが違う

   値束縛の注釈は `elab_value_type_outer` で読む。
   頭の矢印は束縛の最外なので、そこに書いたラベルのある行は開き、
   `pub` の省略 `@` には Rigid の行を置く(表は §11.26)。
   開くかどうかは、`elab_value_type_outer` の結果ではなく、
   注釈の表層の構文 `snd t` が矢印リテラルかどうかで決める。
   頭が型エイリアスなら、展開先の矢印は入れ子で、書いた行は閉じたまま読むからである。
   開き直しのガード `outer_eff_written` と、クラスメソッド側の判定(§11.33)も、同じ構文を調べる。

   注釈と本体の単一化が落ちたとき、`pub` で頭の `@` を省略した値束縛だけは、
   言い換えをもう 1 段詳しくする。
   その形で行の単一化が落ちる原因は、本体が純粋でないことである。
   そこで関数束縛(§11.12)と同じく、`pub` の規則を名指しして元の報告を添える。
   行に由来する失敗かどうかは、`row_failure` で判定する。

   ここでいう本体は、注釈の頭の矢印の本体である。
   値束縛の初期化式そのものは `eff`(束縛の外側の行)で推論するので、
   そこに書いたエフェクトはこの検査に掛からない。
   `pub let g: () => Int32 = { echo(s); fn() => 1 }` は通り、
   宣言を読み込むときに 1 度 Console を起こす。
   同じことを関数束縛で書いた `pub let g(): Int32 = { echo(s); 1 }` は落ちる。
   こちらの `{ … }` は、頭の矢印の本体そのものだからである。
   両者の違いは、呼び出しのたびにエフェクトを起こすか、初期化時に 1 度だけ起こすかである。
   `pub` が約束する純粋さは、呼び出しのたびに起こすエフェクトについてだけである。

   ### 網羅性の drain

   網羅性の遅延キューを drain するのは、`generalize` の直前である(§11.14)。
   パターン束縛(`let (a, b) = ...`)は、節が 1 つだけの match と同じく扱う。
   単相に束縛し、網羅性検査のキューに積む。
   この経路には一般化が無いので、キューに積んだ直後にそのまま drain する。 *)

and elab_binding env level eff ((_, b) as node : T.let_binding) : env =
  at_node node @@ fun () ->
  (* pub の完全注釈検査。注釈が無ければ、@ の省略を純粋と読む約束も
     立てられない。検査は冒頭で、本体を見る前に行う *)
  (if b.T.lb_pub then check_pub_annots ~value_head_outer:true ~params:b.T.lb_params ~ret:b.T.lb_ret);
  let is_fun = b.T.lb_params <> None in
  (* 値制限。一般化してよいのは関数定義か値だけ(§11.28) *)
  let gen = is_fun || is_value b.T.lb_body in
  if (not gen) && b.T.lb_tparams <> [] then
    type_error "非値の束縛に型パラメータは付けられません(値制限。関数にするか値を束縛してください)";
  let lvl = if gen then level + 1 else level in
  let extra_rigids = ref [] in
  let rigids = make_rigids lvl b.T.lb_tparams in
  let env_ty = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types rigids } in
  let fn_ty =
    match b.T.lb_params with
    | Some params ->
        let seen = ref [] in
        let param_tys = List.map (fun _ -> new_var lvl) params in
        let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
        let fn_eff, eff_rigids =
          match b.T.lb_eff with
          | Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e)
          | None when b.T.lb_pub ->
              (* pub の @ 省略は純粋を表す。閉じた空の行にすると sample.kel 自身が
                 落ちる(Db.query が handle_request から呼べない)。本体には Rigid を
                 見せて perform を拒み、公開スキーマでは Generic に解放して、どんな
                 行の文脈からも呼べるようにする。open_explicit_eff が空でない行に
                 することを、空の行にもする形である *)
              let r = new_rigid_ref ~kind:KRow lvl in
              (match !r with Rigid i -> Hashtbl.replace pub_pure_rows i.vid () | _ -> ());
              (TVar r, [ ("", TVar r, r) ])
          | None -> (new_row_var lvl, [])
        in
        extra_rigids := eff_rigids @ !extra_rigids;
        let ret_ty = match b.T.lb_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> new_var lvl in
        let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
        (* 言い換えは注釈が書かれているときだけ行う(値束縛の側と同じガード)。
           lb_ret = None でここが落ちる経路は現状無いが、あれば、注釈を書いて
           いない相手に注釈の話をすることになる *)
        (try Unify.unify ret_ty body_ty
         with Type_error msg when b.T.lb_ret <> None -> type_error ("注釈された返り値型を満たしません(" ^ msg ^ ")"));
        List.iter2 (fun p t -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) params param_tys;
        TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
    | None ->
        (* 値束縛の注釈の頭の矢印は、束縛の最外である。ラベルのある閉じた行を
           書いたときは関数束縛と同じく、本体には Rigid を足して開き、公開
           スキーマでは Generic にする(§11.26 の表の 1 行目)。書かれた @ {} と、
           pub でない束縛の省略された @ には触らない。注釈は
           elab_value_type_outer で読み、値の型の位置のカインドの照合を先に
           掛けてから、その結果の型に行の開き方を掛ける *)
        let vty =
          match b.T.lb_ret with
          | None -> new_var lvl
          | Some t -> (
              let ty = elab_value_type_outer env_ty lvl "型注釈" t in
              match (snd t, repr ty) with
              | T.EArrow (_, _, Some _), TArrow (a, r, e) ->
                  let e', eff_rigids = open_explicit_eff lvl e in
                  extra_rigids := eff_rigids @ !extra_rigids;
                  TArrow (a, r, e')
              | T.EArrow (_, _, None), TArrow (a, r, _) when b.T.lb_pub ->
                  (* pub の省略 @ は、本体は純粋、公開は行多相と読む(仕様 §13。
                     関数束縛の lb_eff = None と同じ扱い) *)
                  let rr = new_rigid_ref ~kind:KRow lvl in
                  (match !rr with Rigid i -> Hashtbl.replace pub_pure_rows i.vid () | _ -> ());
                  extra_rigids := ("", TVar rr, rr) :: !extra_rigids;
                  TArrow (a, r, TVar rr)
              | _ -> ty)
        in
        (* 値束縛の初期化式は外側の eff で推論する *)
        let body_ty = elab_exp env_ty lvl eff b.T.lb_body in
        (try Unify.unify vty body_ty
         with Type_error msg when b.T.lb_ret <> None ->
           (* pub の省略 @ の値束縛では、失敗の原因は本体が純粋でないこと。
              関数束縛(§11.12)と同じ言い換えをここでも置く *)
           if b.T.lb_pub && (not (outer_eff_written b)) && row_failure msg then
             type_error ("pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: " ^ msg ^ ")")
           else type_error ("注釈された型を満たしません(" ^ msg ^ ")"));
        vty
  in
  (* @ を省略した let の行が本体で空に固まったら、公開のときに開き直す
     (§11.26)。明示の @ と pub(Rigid の経路)は対象外。値束縛は、注釈の頭の
     矢印リテラルに @ が書かれていないときだけ開き直す。
     let k: (Int32) => Int32 @ {} の @ {} を開くと、両方向に効くという約束が
     破れる。頭がエイリアスなら展開先は入れ子なので開かない(outer_eff_written) *)
  let fn_ty = if gen && (not (outer_eff_written b)) && not b.T.lb_pub then reopen_pure_row lvl fn_ty else fn_ty in
  Tree.set_ty node fn_ty;
  let rigids = rigids @ !extra_rigids in
  (* 網羅性の遅延キューは generalize の直前に drain する *)
  match snd b.T.lb_name with
  | T.PVar x ->
      List.iter warn (Exhaust.drain ());
      if gen then (
        (* 一般化の直前に曖昧性を調べる。generalize より前でなければならない。
           後では Unbound が Generic に変わっていて判定できない *)
        Unify.check_ambiguity ~all:false ~level [ fn_ty ];
        Unify.generalize level fn_ty);
      release_rigids rigids;
      { env with values = SMap.add x fn_ty env.values }
  | T.PWildcard ->
      List.iter warn (Exhaust.drain ());
      if gen then (
        Unify.check_ambiguity ~all:false ~level [ fn_ty ];
        Unify.generalize level fn_ty);
      release_rigids rigids;
      env
  | _ ->
      (* パターン束縛は単相(節が 1 つだけの match と同じ扱い)。網羅性の警告に乗せる *)
      release_rigids rigids;
      let seen = ref [] in
      let env' = elab_pat env level seen fn_ty b.T.lb_name in
      Exhaust.queue [ (b.T.lb_name, false) ] fn_ty;
      List.iter warn (Exhaust.drain ());
      env'

(* ## 11.29 let rec

   手順は 4 つある。
   名前を単相の新しい変数で先に束縛し、本体を推論し、その変数と単一化し、最後に一般化する。
   この順序なので、再帰呼び出しは単相で、多相再帰はできない。
   多相再帰には型注釈が要り、そこまで踏み込むと推論が決定不能に近づく。

   右辺は関数でなければならない。
   これは型の都合ではなく、評価器の都合である。
   関数でない右辺(`let rec x = x + 1`)を許すと、型検査を通ったプログラムが実行時に必ず落ちる。
   Diktor は、そうしたプログラムを型検査の段階で拒否する。

   束縛の名前をパターンにできないのも、同じ理由による。
   相互再帰の前方参照には名前が要る。

   一般化するのは、すべての右辺を推論し終えてからで、束縛群として一括で行う。
   片方だけ先に一般化すると、相互再帰の相手が見ている変数がすでに一般化されていて、
   単一化に失敗する。

   値束縛の注釈の頭にラベルのある行を書いたときの開き方は、`let` と同じである(§11.26)。
   `pub` の省略 `@` だけは扱いが違い、`let rec` の値束縛には Rigid の行を置く分岐が無い。
   群では Rigid の行を 1 本共有し、束縛ごとに頭から Rigid を作る経路とは噛み合わないからである。
   そのため、頭の矢印の `@` を省略した `pub let rec` の値束縛は、
   `check_pub_annots` が拒否する(頭に `@` を書けば受理する)。
   この拒否は仕様と食い違わない。
   仕様は、`let rec` の値束縛を認める形を書いていない。

   ### 剛定数の解放は、相手に入り込んだものだけ群の終わりに行う

   束縛が作った剛定数(型パラメータと、書かれた `@` を開いた行)のうち、
   群のほかの束縛の `pre`(名前を先に束縛した単相の変数)に入り込んだものだけを、
   群の終わりに解放する。
   入り込んでいないものは、単独の `let` と同じく束縛ごとに解放する(§11.27)。
   入り込んだかどうかは `mentions` で判定する。
   `mentions` は、相手の `pre` の型をたどって、同じ `ref` が現れるかどうかを調べる。

   このように分けるのは、どちらか一方にそろえると壊れる形があるからである。

   束縛ごとに解放すると、相手が `pre` 越しに掴んでいる型の中で、剛定数が Generic に変わる。
   その後で走る相手の単一化はその Generic 変数に出会い、
   第8章の `unify` が `[BUG] 単一化中に Generic 変数が現れました` で異常終了する。
   次の束縛群が、この形にあたる。

   ```
   let rec f: (Int32) => Int32 @ Console = fn(x) => g(x)
   and g: (Int32) => Int32 = fn(x) => x
   ```

   `Panic` は、利用者のプログラムがどう書かれていても出てはならない(§1.18 の表)。
   しかもこの形は受理すべきプログラムなので、型エラーに変えるだけでは足りない。
   関数束縛で書いた同じ形も、同じ経路を通る。
   型パラメータが相手の型へ入り込む形(`let rec f[A](x: A): A = g(x) and g(y) = y`)も同じである。

   逆に、すべてを群の終わりに回すと、注釈つきの先行する束縛を、後続の束縛が多相に使う形が落ちる。

   ```
   let rec f[A](x: A): A = x
   and g(n: Int32): Int32 = f(n)
   ```

   `f` の `A` は相手の `pre` に入り込まない。
   解放を遅らせると、`g` の本体が `f` を呼ぶ時点で `A` がまだ Rigid なので、`Int32` と一致せず、
   「スコープ付きの型が一致しません」で落ちる。
   入り込んだかどうかで分ければ、この 2 つを同時に満たせる。
   `test/annot_rows.t` の recand / recandfn / recandtp が前者を、
   recandpoly / recandeff が後者を確かめる。

   群には制限が 1 つ残る。
   2 本以上の束縛が最外の矢印に `@` をリテラルで書き、先行する束縛が後続の束縛を呼ぶと、通らない。
   開いた行の尾部が、束縛の本数だけ別々の剛定数になるからである。
   先行する束縛の本体が後続を呼ぶと、後続の `pre` は先行の剛定数を掴む。
   後続の番が来ると、後続の注釈が作った別の剛定数とその `pre` を単一化しようとして、
   「スコープ付きの型が一致しません」で落ちる。
   通るかどうかは呼ぶ向きで決まり、落ちるのは互いを呼び合う形に限らない。
   後続が先行を呼ぶだけの形は通る。
   先行の剛定数はすでに Generic に解放されていて、呼び出しのたびに具体化されるからである。
   これは値束縛でも関数束縛でも同じである。
   `pub` の省略 `@` は群で 1 本の行を共有する(`shared_pub_row`)が、
   明示された `@` は書いた本数だけ別々の行を表すので、共有にはできない。
   `test/annot_rows.t` の recandboth / recandbothfn が互いを呼び合う形を、
   recandfwd / recandfwdfn が先行が後続を呼ぶだけの形を、
   recandeff / recandback が通る向きを確かめる。 *)

and elab_rec_bindings env level eff bs : env =
  (* 事前に割り当てた単相の変数で束縛 → 本体を推論 → unify → 一般化。多相再帰はできない *)
  let lvl = level + 1 in
  let names =
    List.map
      (fun (_, b) ->
        (* let rec の右辺は関数でなければならない(評価器が構造上そう要求する。
           関数でないものを許すと、型検査を通って実行時に必ず落ちる) *)
        (match (b.T.lb_params, snd b.T.lb_body) with
        | None, T.Lambda _ | Some _, _ -> ()
        | None, _ -> type_error "let rec の右辺は関数でなければなりません");
        match snd b.T.lb_name with
        | T.PVar x -> (x, new_var lvl)
        | _ -> type_error "let rec の束縛はパターンにできません")
      bs
  in
  let env_rec = { env with values = List.fold_left (fun m (x, t) -> SMap.add x t m) env.values names } in
  (* pub の @ 省略の Rigid の行は、群で 1 本を共有する。束縛ごとに別の Rigid を
     作ると、相互再帰の呼び出しが 2 本の Rigid を単一化しようとして
     「スコープ付きの型が一致しません: R1 と ς1」で落ちる。pub を外せば通る、
     意味の同じ宣言が落ちることになる。群は全体として純粋なので、同じ行で
     よい。解放も群の終わりに 1 度だけ行う *)
  let shared_pub_row = ref None in
  (* 注釈が作った剛定数(型パラメータと、書かれた @ を開いた行)のうち、群のほかの
     束縛の pre に入り込んだものは群の終わりに、それ以外は束縛ごとに解放する(§11.29) *)
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
  let pub_pure_row lvl =
    match !shared_pub_row with
    | Some (t, r) -> (t, [ ("", t, r) ])
    | None ->
        let r = new_rigid_ref ~kind:KRow lvl in
        (match !r with Rigid i -> Hashtbl.replace pub_pure_rows i.vid () | _ -> ());
        shared_pub_row := Some (TVar r, r);
        (TVar r, [ ("", TVar r, r) ])
  in
  List.iter2
    (fun ((_, b) as bnode) (_, pre) ->
      at_node bnode @@ fun () ->
      (* pub の完全注釈検査と、関数束縛の @ の省略を純粋と読む規則は、let(§11.28)と同じ。
         ただし完全注釈検査では値束縛の頭を最外として扱わない(値束縛に pub の省略 @ の
         分岐が無いため。§11.29) *)
      (if b.T.lb_pub then check_pub_annots ~value_head_outer:false ~params:b.T.lb_params ~ret:b.T.lb_ret);
      let rigids = make_rigids lvl b.T.lb_tparams in
      let env_ty = { env_rec with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env_rec.types rigids } in
      let extra_rigids = ref [] in
      let fn_ty =
        match b.T.lb_params with
        | Some params ->
            let seen = ref [] in
            let param_tys = List.map (fun _ -> new_var lvl) params in
            let env2 = List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty params param_tys in
            let fn_eff, eff_rigids =
              match b.T.lb_eff with
              | Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e)
              | None when b.T.lb_pub ->
                  (* 共有 Rigid は群の終わりに解放するので、束縛ごとの
                     解放リストには入れない *)
                  (fst (pub_pure_row lvl), [])
              | None -> (new_row_var lvl, [])
            in
            extra_rigids := eff_rigids;
            let ret_ty = match b.T.lb_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> new_var lvl in
            let body_ty = elab_exp env2 lvl fn_eff b.T.lb_body in
            Unify.unify ret_ty body_ty;
            (* 引数パターンの網羅性検査の項目は、群のすべての本体の後に積む(下)。
               ここで積むと、後続の束縛の本体の中の let の drain に食われて行が
               早く閉じ、受理すべきプログラムが型エラーになる *)
            rec_arg_queue := (params, param_tys) :: !rec_arg_queue;
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None ->
            (* 値束縛の注釈の頭の矢印は最外である(§11.28 と同じ)。注釈は、値の型の
               位置のカインドの照合を通してから読む。pub の分岐は入れない。群が
               共有の Rigid の行を持つ設計と噛み合わないため(§11.29) *)
            let vty =
              match b.T.lb_ret with
              | None -> new_var lvl
              | Some t -> (
                  let ty = elab_value_type_outer env_ty lvl "型注釈" t in
                  match (snd t, repr ty) with
                  | T.EArrow (_, _, Some _), TArrow (a, r, e) ->
                      let e', eff_rigids = open_explicit_eff lvl e in
                      extra_rigids := eff_rigids @ !extra_rigids;
                      TArrow (a, r, e')
                  | _ -> ty)
            in
            Unify.unify vty (elab_exp env_ty lvl eff b.T.lb_body);
            vty
      in
      Unify.unify pre fn_ty;
      Tree.set_ty bnode fn_ty;
      let shared, own =
        List.partition
          (fun (_, _, r) -> List.exists (fun (_, other) -> other != pre && mentions r other) names)
          (rigids @ !extra_rigids)
      in
      release_rigids own;
      group_rigids := shared @ !group_rigids)
    bs names;
  release_rigids !group_rigids;
  (match !shared_pub_row with Some (t, r) -> release_rigids [ ("", t, r) ] | None -> ());
  (* @ を省略した let rec も、本体が純粋だと分かったら、公開の行を開き直す
     (§11.26 と同じ規則。群のうち @ を書いた束縛と pub は対象外)。本体の
     再帰呼び出しが見ていた pre は古い矢印のままだが、本体はすでに {} で
     検査し終えており、単相再帰の具体化が {} だっただけなので食い違わない *)
  let names =
    List.map2
      (fun (((_, b) as bnode) : T.let_binding) (x, t) ->
        if (not (outer_eff_written b)) && not b.T.lb_pub then (
          let t' = reopen_pure_row lvl t in
          if t' != t then Tree.set_ty bnode t';
          (x, t'))
        else (x, t))
      bs names
  in
  List.iter
    (fun (params, param_tys) ->
      List.iter2 (fun p t -> if not (irrefutable_pat p) then Exhaust.queue [ (p, false) ] t) params param_tys)
    (List.rev !rec_arg_queue);
  List.iter warn (Exhaust.drain ());
  (* 群として一括で曖昧性を調べる。相互再帰の制約は、群のどれかの型から
     到達できればよい *)
  Unify.check_ambiguity ~all:false ~level (List.map snd names);
  List.iter (fun (_, t) -> Unify.generalize level t) names;
  { env with values = List.fold_left (fun m (x, t) -> SMap.add x t m) env.values names }

(* ## 11.30 トップレベルで許されるエフェクト

   トップレベルの初期エフェクト行は、ランタイムが提供する**閉じた**行である。
   中身は `{Console, Async, Fs, Blocking}` の 4 つで、名簿は第7章の `toplevel_effects` にある。
   4 つがこの行にある理由は、それぞれ異なる。

   - `Console`：出力の最終的な行き先である。
     ランタイムが実装を持ち、利用者はハンドルできない(§11.23)。
   - `Async`：sample.kel:772 の `crunch` が、
     `@ Async` を持ったままトップレベルから呼ばれるからである。
     `yield_` は型検査を通り、実行時には何もしない。
     Diktor はこの振る舞いを、`Async` をランタイムが提供するエフェクトとして行に置くことで表している。
   - `Fs`：4 つのファイルプリミティブが `@ Fs` を課すので、
     トップレベルから `__open` を呼べるように置く。
     操作は持たない。
   - `Blocking`：操作を持たないので、行に残っていても `perform` で起こせるものが無い。
     仕様 §12 は、`Blocking` を締め出す役目を `pinned` に任せている。
     ハンドル禁止の名簿(`runtime_effects`)には入れない。
     操作が無いので禁じる場面が無く、入れると診断が変わる(第7章 §7.3)。

   `Heap` がこの名簿に無いのは、引数を取るラベルだからである(sample.kel:656-657)。
   下の `toplevel_eff` はラベルの引数に `t_unit` を置くので、`Heap` を名簿に足しても、
   行に載るのは `Heap[Unit]` である。
   これは、`run h` が導入する剛定数 `h` を持つ `Heap[h]` とは単一化しない。

   4 つのうち、`--no-prelude` でも行に残るのは `Blocking` だけである。
   ほかの 3 つはプレリュードが宣言する名前で、下の `toplevel_eff` の所有のガードは、
   利用者が同じ名前を宣言してもそれを行に載せない。
   `Fs` もその 3 つに入るので、`--no-prelude` のもとでは、
   `effect Fs = {}` と `@ Fs` を持つ `extern` を自前で書いても、
   トップレベルからその `extern` を呼ぶ手段が無い(`test/fs_effect.t` の npfs)。
   `--prelude` で差し替えたプレリュードが `Fs` を宣言するなら、`Fs` はプレリュードの所有になり、
   行に載る(`test/fs_effect.t` の withpre)。
   この非対称は、宣言の場所の違いから来る。
   `Blocking` は §6.12 の組み込み登録が宣言し、`Fs` は第15章のプレリュードが宣言する。

   行が閉じているので、`perform print(...)` をトップレベルに書くと、
   「エフェクト Print をここでは実行できません」で落ちる。
   Print は利用者が宣言したエフェクトで、ハンドラを書かない限り誰も解釈しないので、
   この挙動は正しい。

   初期の値環境は、第6章の組み込み表から作る。 *)

let toplevel_eff () =
  (* トップレベルの行に載せるのは、名簿 toplevel_effects のうちプレリュードが所有するものだけ。
     名前だけで載せると、--no-prelude やプレリュードを差し替えた環境で利用者が自分の
     effect Console を宣言したとき、型は利用者の署名、実行はランタイムの実装になり、
     型検査を通ったプログラムが実行時に落ちる。所有でなければその名前は行に載らず、
     perform write は「ここでは実行できません」で静的に落ちる。
     Blocking がこのガードを通るのは、§6.12 の register_builtins が in_prelude を
     立てた下で add_effect するからである(reset でも同じ経路を通る)。
     register_ref_array の呼び出しがその外へ出ると、Blocking は黙ってトップレベルの行から
     外れる。test/blocking_top.t の btop がこれを見張っている *)
  List.fold_right
    (fun n acc -> if Decls.prelude_owned "effect" (intern n) then TRowExtend (intern n, t_unit, acc) else acc)
    Prims.toplevel_effects TRowEmpty

let initial_env () =
  {
    values = List.fold_left (fun m (n, t) -> SMap.add n t m) SMap.empty (Decls.builtin_values ());
    types = SMap.empty;
    resume_ty = None;
  }

(* ## 11.31 newtype の登録

   データ宣言は型言語を変えない。
   名目的な `TCon` が 1 つ増え、宣言表にコンストラクタとフィールド型が載るだけである。

   フィールド型の中の型パラメータは `Generic` で束縛する。
   つまり宣言表に置くのはスキーマで、使うたびに `subst_params` で具体化する(§11.8、§11.18)。
   組み込みメソッドのスキーマと同じ形なので、使う側のコードは 1 つで済む。

   パラメータのカインドは、本体での使われ方から推論する(仕様 §6、sample.kel:246-247)。
   たとえば `newtype Callback[E] = Callback(() => Unit @ E)` では、`E` が矢印の `@` に現れるので、
   行カインドに決まる。
   使われ方が無ければ、`Type` に既定化される。

   本体で決まったカインドを頭にも反映するため、頭と本体は同じカインドのセルを共有する。
   パス 1a が頭にパラメータごとのカインド変数を積み、
   パス 1b の `register_newtype` がそれを剥がして `dd_params` の `vkind` に据える。
   本体の精緻化がそのセルを `same_kind` で張れば、頭にも反映される。
   頭と本体で別のセルを作ると、本体で決まったカインドが、1a で登録した頭のカインドと食い違う。
   プレリュード所有名の再宣言では 1a が頭を差し替えないので、
   剥がすのはプレリュードが決めたカインドになり、利用者の宣言はそれを引き継ぐ。
   この場合に別のセルを作ると、`data_match` の照合で `KVar` と `KStar` が食い違う。

   カインドを決める材料は、自分の宣言の本体に限らない。
   宣言群の中の型の本体すべてが材料になる(sample.kel:246-249)。
   値の本体(`let` の右辺)は数えない。
   これは、頭と本体が 1 つのセルを共有し、既定化が 1b の後始末まで遅れる(次の段落)ことの帰結である。
   自分の本体では使っていないパラメータ(`newtype Ph[E] = MkPh(Int32)` の `E`)でも、
   同じ宣言群の別の宣言がそれを行として使えば行カインドになる。
   例は `test/kinds.t` の phantomrow / phantomtype にある。
   宣言を 1 つ消すとカインドが変わることがあるのも、このためである。

   既定化は宣言ごとではなく、1b の後始末で宣言群の全部を処理し終えてから行う(§11.39)。
   `same_kind` は未解決のカインド変数どうしを片方に張る。
   そのため、先に処理した newtype を宣言ごとに既定化すると、
   まだ本体を読んでいない相手のカインドまで `KStar` に固定してしまい、
   相互参照する newtype の受理が宣言順に依存する(`test/kinds.t` の mutual / mutual2)。
   `register_newtype` を呼ぶ側が、既定化の責任を負う。

   この仕組みだけでは、宣言順に依存する形が 1 つ残る。
   行カインドのパラメータへ、具体的な行を前方参照つきで渡す形である。
   たとえば `newtype A[X] = MkA(B[{Print extends X}])` を `B` より前に置く。
   1b で `A` を処理する時点で `B` がまだ 1b を通っていないと、
   `B` のパラメータのカインドは `KVar` のままである。
   すると §11.3 の読み分けは `{…}` を型として読み、
   「エフェクトラベルはこの位置(レコード型)では使えません」で落ちる。
   行変数を渡す形(`B[X]`)は宣言順に依存しない。
   `KVar` のまま読んでも行変数がそのまま返り、あとから `same_kind` で張られるからである。

   Diktor はこの形を**投機**で扱う。
   パス 1a の直後に宣言列をもう一度なめ、
   newtype の本体を一度だけ読んでパラメータのカインドを決めてから、1b に入る。
   この処理は `speculate_newtype` が行う(§11.39)。
   1b に着いた時点で `B` のパラメータが行だと分かっているので、読み分けは `{…}` を行として読む。
   `test/kinds.t` の fwdrow / fwdrow2 が両方の宣言順を確かめ、
   fwdrow3 と fwdrowmod / fwdrowmod2 が連鎖と module の中の形を確かめる。
   投機は宣言順に 1 周するだけだが、連鎖にも届く。
   `same_kind` はカインドのセルどうしを張るので、連鎖の末端で行が決まれば、
   手前まで一度に伝わるからである。

   投機を 1b の前に走らせても安全なのは、次の 2 つの理由による。
   第一に、投機は `elab_type` を呼ぶだけで、コンストラクタを登録しない。
   `Decls.add_data` も `Unify.generalize` も `pub` の完全注釈検査も呼ばないので、
   残る副作用は `elab_type` がカインドのセルに張る単一化だけで、それが投機の目的である。
   第二に、上の形で投機が失敗しても、残る張りは正しい答えになっている。
   `A` の投機は `B[{Print extends X}]` を型として読み、
   `extends` の右は行かレコード型でなければならないので、
   `same_kind` が `X` を `Type` ではなく `Row` に張る。
   そのあと `BLabel` の分岐が落ち、投機は診断を捨てるが、`X` に残った張りは正しい。

   投機には手当てが 2 つ要る。
   どちらも、effect の操作の登録が 1b で行われることに由来する。
   投機の時点では、利用者が宣言したエフェクトラベルはすべて未知である。
   そのため、`() => Unit @ {Log}` のような普通のフィールドが、
   投機の中では「未知のエフェクト: Log」で落ちる。

   1 つ目の手当てとして、例外をフィールドごとに握り潰す。
   本体全体を 1 つの `try` で包むと、
   たとえば newtype `B` のフィールドが 1 つ落ちただけで、`B` の残りのフィールドが読まれず、
   `B` のパラメータ `E` のカインドが `KVar` のまま 1b に入る。
   このとき、`B` より前に置いた宣言が `B[{}]` を渡すと、
   1b でその宣言を読む時点で `elab_con_args` の照合が `E` を `Type` に張り、
   `B` 自身が「行カインドではない型パラメータです: E」で落ちる。
   フィールドごとに握り潰せば、手前のフィールドが落ちても、後続のフィールドがカインドを決める
   (`test/kinds.t` の specfield / specfield2)。
   前方参照の連鎖(specfwd)でも、後続のフィールドが連鎖でカインドを決める。

   1 つ目の手当てでは救えない形もある。
   1 つのフィールドの中で先にラベルへ当たる形である。
   タプルやレコードの要素は右から読むので、
   `MkB((() => Unit @ E, () => Unit @ {Log}))` は右端の `{Log}` で落ち、`E` に届かない。
   `E` が `KVar` のまま残るので、別の宣言が `B[{}]` を渡すと、その宣言の投機が `{}` を型として読み、
   `elab_con_args` の照合が `E` を `Type` に張ってしまう。
   張るのが投機の中なので、`B` を先に宣言した形でも落ちる。
   そこで 2 つ目の手当てとして、投機の間だけ、
   要素なしの波括弧(`{}` と `{extends R}` の 2 つの形)を読まずに飛ばす。
   飛ばすのは、カインドが未確定のパラメータへ渡したものに限る。
   飛ばす対象をこの 2 つの形に限るのは、型としても行としても読めるのがこれだけだからである。
   ラベルが 1 つでもあれば型として読むほうが失敗するので、張りは残らない。
   飛ばしても失うものは無い。
   相手のカインドが決まった状態で、
   1b が同じ字面をもう一度読むからである(`test/kinds.t` の specinner / specinner2)。

   `newtype A[X] = MkA(B[{}], () => Unit @ X)` を `B` より前に置く形も、
   この 2 つの手当てで通る(`test/kinds.t` の specunit)。
   要素なしの波括弧を前方参照で渡す形が通らないのは、
   相手の投機がそのパラメータのカインドを決められない場合だけである。
   飛ばすのは投機の間だけなので、相手のカインドが `KVar` のまま 1b に入ると、
   1b では `{}` を空レコードとして読むことに成功してしまい、
   `elab_con_args` の照合が相手のパラメータを `Type` に張る(`test/kinds.t` の specunit2)。

   型引数にラベルを 1 つでも書けばどちらの順でも通る、というわけではない。
   投機が相手のパラメータに届かない形では、
   `B[{Log extends X}]` と書いても宣言順に依存する(`test/kinds.t` の speclab / speclab2)。
   ラベルの有無が決めるのは失敗した読みが張りを残すかどうかだけで、
   相手のカインドが決まるかどうかとは関係しない。
   これらの形も通すには、投機の中だけ `elab_con_args` の `same_kind` を止めて、
   投機を張らない読みにする必要がある。

   `newtype T = ???`(`NtHole`)は表現を隠す。
   コンストラクタを持たない不透明なデータ型として登録するので、構築も分解もできない。

   フィールド型の精緻化はこの登録時に済ませるので、
   パス 2 で newtype に出会っても何もすることがない。
   未知の型を書けば、この時点でエラーになる。

   `pub newtype` のフィールドには完全な型注釈を要求する(仕様 §13)。
   入れ子の矢印で省略した `@` は `@ {}` を意味するが、公開 API では、
   純粋を意図したのか書き忘れたのかを読み手が区別できなければならない、というのが仕様の理由である。
   判定には、`let` の `check_pub_annots` と同じ `fully_effected` を使う(`test/pub.t` の pubnt)。
   sample.kel の `Parser` が `@ {}` を明示しているのは、そのためである。

   フィールドの型のカインドが `Type` であることも、ここで確かめる。
   確かめないと、行カインドのパラメータや `EffectRow` エイリアスがそのまま値の型になり、
   構築点まで落ちない。
   `newtype Bad[E] = Bad(() => Unit @ E, E)` は、第 1 フィールドで `E` が行に決まり、
   第 2 フィールドで落ちる。
   判定には `same_kind` を使うので、判定は推論も兼ねる。
   裸のパラメータ 1 つのフィールド(`newtype Id[A] = Id(A)`)では `A` のカインドがまだ未解決で、
   判定が `A` のカインドを `Type` に決める(`test/kinds.t` の fieldkind)。

   この検査は、値の型の位置に対する一般の検査(§11.3)を、
   コンストラクタのフィールドに当てはめたものである。
   照合そのものは §11.3 の `check_value_kind` が行い、
   ここでは名詞句にコンストラクタ名を添えるだけである。
   フィールドの最外でカインドが合わないときの文面が、
   「コンストラクタ X のフィールドの型のカインドが Type ではありません」になるのはそのためで、
   どのフィールドかを名指しできるのはこの位置だけである(`test/kinds.t` の fieldkind / fieldalias)。

   フィールドの内側に包んだ形は、§11.3 の照合が包んだ位置ごとに落とす。
   `newtype Bad2[E] = Bad2((E, Int32), () => Unit @ E)` は、
   第 1 フィールドのタプルで `E` が `Type` に決まり、第 2 フィールドの `@ E` で落ちる。
   `newtype Bad3[E] = Bad3(() => Unit @ E, {a: E})` は逆の順なので、
   レコードのフィールド `a` の側で落ちる。
   文面は「レコードのフィールド a の型のカインドが Type ではありません: R1 :: Row」である。
   位置ごとに照合しないと、どちらも受理され、
   行カインドのパラメータを値の型に持つスキーマが宣言表に入る。
   `test/kinds.t` の rowval / rowval2 / rowval3 / hktval が、この照合を確かめている。 *)

(* 1a が頭に積んだカインドのセルをそのまま剥がして、パラメータの型環境を作る。
   頭と本体で別のセルを作ると、本体で決まったカインドが頭に反映されない。
   プレリュード所有名の再宣言では 1a が頭を差し替えないので、
   ここで剥がすのはプレリュードが決めたカインドになる。
   利用者の宣言はそれを引き継ぐ。
   このときも別のセルを作ると、data_match の kind_equiv で KVar と KStar が食い違う。
   register_newtype と、1a の後の投機が同じセルを共有するための共通部分である *)
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
        let classes = List.map (fun li -> intern (show_long_id li)) tp.tp_classes in
        { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes })
      n.T.nt_params head_kinds
  in
  let types =
    List.fold_left2
      (fun m (tp : type_param) i -> SMap.add tp.tp_name (TVar (ref (Generic i))) m)
      env.types n.T.nt_params params
  in
  (params, { env with types })

(* newtype の本体を 1b より前に一度だけ投機的に読み、パラメータのカインドだけを決める(§11.31)。
   型エイリアスの投機(§11.39)と同じ道具を使い、コンストラクタの登録も pub の注釈検査も
   generalize もせず、elab_type の副作用であるカインドの張りだけを残す。
   診断は捨てる(握り潰す節として 4 つの例外だけを捕まえ、Panic は捕まえない)。
   投機が要るのは、行カインドのパラメータへ具体的な行を前方参照つきで渡す形があるからである。
   たとえば `newtype A[X] = MkA(B[{Print extends X}])` を `B` より前に置くと、
   1b が B のパラメータのカインドをまだ知らないので、
   §11.3 の読み分けが `{…}` を型として読む(`test/kinds.t` の fwdrow) *)
let speculate_newtype env (n : T.newtype') =
  match n.T.nt_rhs with
  | T.NtHole -> ()
  | T.NtCtors ctors ->
      let _, env' = newtype_param_env env n in
      (* 例外はフィールドごとに握り潰す。effect の操作の登録は 1b なので、投機の時点では
         利用者が宣言したエフェクトラベルがすべて未知で、() => Unit @ {Log} のような
         普通のフィールドが落ちる。本体全体を 1 つの try で包むと、後続のフィールドの
         張りまで失う *)
      let speculate (f : T.field_decl) =
        try ignore (elab_type env' 1 f.T.fd_ty)
        with Type_error _ | Type_error_at _ | NotImplemented _ | NotImplemented_at _ -> ()
      in
      speculating := true;
      Fun.protect
        ~finally:(fun () -> speculating := false)
        (fun () -> List.iter (fun (c : T.ctor_decl) -> List.iter speculate c.T.cd_fields) ctors)

let register_newtype env (n : T.newtype') =
  (* newtype のパラメータのカインドは、本体での使われ方から推論する。
     F[_] と書いてあればその場で確定する。既定化は 1b の後始末で行う *)
  let params, env' = newtype_param_env env n in
  match n.T.nt_rhs with
  | T.NtHole ->
      Decls.add_data { Decls.dd_name = intern n.T.nt_name; dd_params = params; dd_ctors = []; dd_opaque = true }
  | T.NtCtors ctors ->
      let ctors =
        List.map
          (fun (c : T.ctor_decl) ->
            {
              Decls.ct_name = intern c.T.cd_name;
              ct_fields =
                List.map
                  (fun (f : T.field_decl) ->
                    (* pub の完全注釈検査(仕様 §13)は、フィールドの矢印にも及ぶ。
                       省略の意味は @ {} に決まっているが、公開 API では、純粋を
                       意図したのか書き忘れたのかを読み手が区別できなければならない
                       (sample.kel:815-821。フィールドへの適用は :818-819 に
                       明記されている) *)
                    (if n.T.nt_pub && not (fully_effected f.T.fd_ty) then
                       type_error "pub な newtype のフィールドには完全な型注釈が必要です(注釈の中の矢印に @ がありません)");
                    let ty = elab_type env' 1 f.T.fd_ty in
                    (* フィールドの型のカインドは Type。値の型の位置に対する一般の検査
                       (§11.3)をフィールドに当てはめたものなので、照合そのものは
                       check_value_kind に任せ、ここでは名詞句にコンストラクタ名を添えるだけ。
                       フィールドの最外を見る枝はここに置く。どのフィールドかを名指しできるのは
                       ここだけで、内側に包んだ形は elab_value_type が位置ごとに落とす *)
                    at_node f.T.fd_ty (fun () -> check_value_kind ("コンストラクタ " ^ c.T.cd_name ^ " のフィールドの型") ty);
                    (* 省略された @ など、束縛されなかった変数はスキーマでは Generic にする *)
                    Unify.generalize 0 ty;
                    { Decls.fi_label = Option.map intern f.T.fd_label; fi_ty = ty })
                  c.T.cd_fields;
            })
          ctors
      in
      Decls.add_data { Decls.dd_name = intern n.T.nt_name; dd_params = params; dd_ctors = ctors; dd_opaque = false }

(* ## 11.32 effect の登録

   エフェクト宣言は、操作名から矢印のスキーマへの表である。
   操作の型が矢印でなければならないのは、`perform` が引数と返り値を必要とするからである。

   effect 宣言には型パラメータを書けない(sample.kel §9)。
   エフェクトのパラメータは、ラベルの引数欄として行に載る。
   この仕組みは、`Heap[h]` のように組み込みのエフェクトが使っている。
   利用者が宣言するエフェクトにこれを許すと、操作の型が真に多相になり、
   ハンドラの節が多相な継続を受け取ることになるので、ランク 2 の型が要る。
   ランク 1 の範囲で扱えるのは、エフェクトのパラメータを組み込みのエフェクトにだけ許す形までである。

   操作の型の引数に現れる矢印は、入れ子の矢印として読む(仕様 §9)。
   `spawn: (() => Unit @ Async) => Unit` の `@ Async` が暗黙に多相化しないのは、
   実装の都合ではなく仕様の規則である(`test/annot_rows.t` の opsig / opsig2)。
   操作の型の頭の矢印で省略した `@` も `TRowEmpty` になる。
   ただし、`perform` も `handle` も操作のスキーマの行を捨てるので、この行は観測されない。

   同じエフェクトの中での操作名の重複は拒否する。
   別のエフェクトとの重複は許す。
   §11.20 の非修飾の操作名の解決は、
   別のエフェクトどうしで操作名が重複しうることを前提にしている。 *)

let register_effect env (e : T.effect') =
  if e.T.ef_params <> [] then type_error "effect 宣言に型パラメータは書けません(sample.kel §9)";
  (* return / cancel は、handle の節の分類(§11.22)が名前で先に取るので、
     操作名としては宣言できない。受理すると、その操作を含む effect は、
     修飾しても節を書きようがなく、ハンドルできない *)
  List.iter
    (fun (op, _) ->
      if op = "return" || op = "cancel" then
        type_error ("操作名 " ^ op ^ " は予約されています(handle の " ^ op ^ " 節と衝突するため宣言できません)");
      (* 節の分類器(§11.22)が操作節として読むのは、英小文字で始まる名前だけ。
         _ で始まる名前を受理すると、ハンドルできない effect になる *)
      if String.length op = 0 || not (op.[0] >= 'a' && op.[0] <= 'z') then
        type_error ("操作名 " ^ op ^ " は英小文字で始めてください(handle の節が操作名として読めません)"))
    e.T.ef_ops;
  let ops =
    List.map
      (fun (op, te) ->
        match snd te with
        | T.EArrow _ ->
            let ty = elab_type env 1 te in
            Unify.generalize 0 ty;
            (intern op, ty)
        | _ -> type_error ("操作 " ^ op ^ " の型は矢印型でなければなりません"))
      e.T.ef_ops
  in
  (* 同じ effect の中での操作名の重複を拒否する *)
  let rec dup = function
    | [] -> ()
    | (op, _) :: rest -> if List.mem_assoc op rest then type_error ("操作 " ^ name_of op ^ " が二重に宣言されています") else dup rest
  in
  dup ops;
  Decls.add_effect { Decls.ef_name = intern e.T.ef_name; ef_ops = ops }

let binding_name (b : T.let_binding') = match snd b.T.lb_name with T.PVar x -> Some x | _ -> None

(* ## 11.33 type class の登録

   クラスのパラメータは 1 つだけである。
   仕様は多パラメータ型クラスを明示的に除いており(sample.kel:356)、そのおかげで、
   型スキーマ専用のデータ型も制約ストアも持たずに済む。
   `Generic` の印だけで多相を表せるのは、パラメータが 1 つだからである。

   パラメータは、個数だけでなくカインドも決まっている。
   `tp_arity` が 0 なら `KStar`、`F[_]` なら `[_] Type` である。
   一般には、`tp_arity` 個の `Type` を取って `Type` を返すカインドになる。
   newtype の束縛子と違い、クラスのパラメータは `KVar` を経由しない(§1.12)。
   クラスのパラメータに `EffectRow` を取れないのは、カインドをこう固定しているからである。
   カインドを固定する理由は、インスタンス表のキー(§11.34)にある。
   インスタンスの選択は型構成子のタグ 1 つで決まるので、
   ラベルの集合でしかない行は選択のキーにならない。
   仕様 §8 がこれを定めている(sample.kel:358-360)。

   クラスのパラメータのカインドが固定されていても、エフェクト多相なクラスが書けないわけではない。
   メソッドの型パラメータは `KVar` を作るので、行カインドになれる。
   `val run_[E]: (A, () => Unit @ E) => Unit @ E` は通る。
   エフェクトで量化したいクラスは、クラスのパラメータではなく、
   メソッドの型パラメータに行変数を取る(sample.kel:361-362)。
   仕様 §8 の `Functor` の `map` がその例で、
   `test/kinds.t` の classrow / classrow2 / classrowok がこの形を確かめている。

   メソッドの型は、スキーマとして表に置く。
   `val map[A, B, E]:` のようにメソッドは自分の型パラメータを持てるので、
   このスキーマでは、クラスのパラメータとメソッド固有の型パラメータの両方を `Generic` にする。
   クラスのパラメータには `vcls` としてクラス名が付いており、
   これが後で「この変数はこのクラスのインスタンスでなければならない」という制約になる。
   メソッドの型パラメータに書かれた制約のクラス名の検証だけは、ここでは行わず、
   パス 1b の後に回す(§11.39)。
   クラスどうしの宣言順に依存させないためである。

   `Integral` と `Fractional` は利用者が宣言できない。
   リテラルの述語のために予約された名前である(§11.2)。
   どの名前が予約されているかの表は第6章(`Decls.reserved_predicate`)が持ち、
   ここはそれを引くだけである。
   インスタンス宣言の側の入口にも、同じ表を引く検査がある(§6.12)。

   組み込みと同名のクラスを利用者が宣言したときは、組み込みの宣言と照合して受理し、
   実体は組み込みを使う。
   照合は第6章の `add_class_decl` が行い、パラメータのカインド、`derive structural` の有無、
   メソッド名の集合、各メソッドの型がすべて一致することを求める。
   組み込みの `Ord` の 4 つのメソッドのうち `lt` だけを書いた宣言は、
   「メソッドが違います」で落ちる。
   sample.kel 自身がプレリュード相当の宣言を含んでいるので、それを受理するための扱いである。

   ### 最外の行を開くのは、注釈の頭が矢印リテラルのときだけ

   メソッドの注釈の最外にラベル付きの行を書いたときは、
   その行を開く(値束縛と同じく `Rigid` を `Generic` に変える)。
   仕様 §9 は、束縛の最外に型クラスのメソッドを数える(sample.kel:476)。
   そして、そこに書いた行は本体への上限として働き、
   公開される型では行変数で開かれると定めている(sample.kel:477-478)。
   開かないと、`val f: (T) => Int32 @ Console` のメソッドがどの文脈からも呼べなくなる。

   開くのは、注釈の頭が矢印リテラルのときに限る。
   頭が型エイリアスなら、展開先の矢印は入れ子である(§11.5 の規則 4)。
   入れ子の矢印に書いた行は閉じたまま読むので、ここで開くと読みが食い違う。
   `type F[A] = (A) => Int32 @ Print` の行が、値束縛では閉じ、クラスメソッドでは開くことになる。
   `elab_type_outer` の結果が矢印かどうかで判定すると、この食い違いが実際に起きる。
   `test/annot_rows.t` の clsalias3 / clslit が、注釈の頭で判定する読みを固定している。

   判定は表層の構文 `snd v.T.cv_ty` を見る。
   値束縛も同じ規律に従い、注釈 `snd t` を見て開くかどうかを決め(§11.26)、
   開き直しのガード `outer_eff_written` は `lb_ret` を見る(§11.28)。
   同じ問いに答える判定がこのように分かれているので、どれかを変えるときは、
   残りも合わせて変える必要がある。
   脱糖が変わると黙って効かなくなる種類の判定なので、
   cram のテストが見張っている(`test/annot_rows.t` の clsalias3 / clslit と valopen / alval)。

   エイリアスで書いたメソッドは、ラベル付きの行を持つと呼びにくい。
   公開される型が閉じた `{Print}` なので、利用者は、
   呼び出し側で `@` を省略して行を推論させるか(clsalias3ok)、
   メソッドの型を矢印リテラルで書き直すか(clslit)のどちらかを選ぶ。
   値束縛(alval4)と同じ結果で、仕様が定めた読みからそのまま導かれる。

   ### スーパークラスは持たない

   クラスのパラメータへの制約 `type class Ord[A: Eq]` は拒否する。
   仕様 §8 は、スーパークラスを導入しないと定めている。
   制約の含意を持たないほうが、署名に書いた制約だけで解決が決まり、規則が単純になるからである。
   `Ord` は `Eq` を含意しないので、両方が要る場面では `[A: Eq + Ord]` と並べて書く。
   診断もそう案内する(`test/classes.t` の super / ordeq / ordeq2)。
   含意が無いことは、次の形で確かめられる。
   `[A: Ord]` だけで `==` を使うと、「Eq のインスタンスではありません」で落ちる。

   ### クラスパラメータが引数の頭に現れること

   Diktor は、メソッドの宣言に次の条件を課す。
   メソッドの引数の少なくとも 1 つで、クラスのパラメータが型の**頭**に現れていなければならない。
   どの引数でも頭に現れないメソッドは宣言できない。

   理由は実行時にある。
   型クラスのディスパッチは辞書渡しではなく、値のタグを見る動的ディスパッチである(第14章)。
   実行時に見えるのは値の頭のコンストラクタだけなので、
   `(List[A]) => ...` のようにパラメータが引数の内側に埋もれていると、`A` のインスタンスを選べない。
   頭に現れるという条件は、その引数でタグによるディスパッチができる、という意味である。

   実行時のディスパッチは、パラメータが頭に現れる引数位置だけを見る(§14.6)。
   引数を左から走査して、最初にインスタンスを持つ値で決めると、
   `(Int32, A) => Int32` のようなメソッドが第 1 引数の `Int32` で誤ってディスパッチするからである。
   宣言の条件は、その位置が少なくとも 1 つあることを保証する。
   条件を「引数のどこかに現れる」に緩めると、
   `(Int32, List[A]) => Int32` のようなメソッドが宣言できてしまう。
   パラメータが頭に現れる位置が 1 つも無いので、実行時はすべての引数を走査し、
   第 1 引数の `Int32` で誤ってディスパッチする。
   静的な宣言の条件と動的な選択の規則は、同じ述語を見ている。

   その代わり、`pure : (A) => F[A]` のようなメソッドは宣言できない。
   返り値の位置にしかパラメータが現れないからである。
   仕様は Monad / Applicative をプレリュードに置かないと明言しているので(sample.kel:451-455)、
   この制約は仕様のプレリュードと衝突しない。

   ### 非修飾名の所有者は高々 1 クラス

   ここでは、非修飾のメソッド名の所有者は高々 1 クラス、という不変条件も守る。
   同名のメソッドを持つクラスが 2 つあると、非修飾名の勝者を elab と実行時が別の規則で選ぶ。
   elab の非修飾名の解決はパス 1b の先勝ちで、先に宣言したクラスが勝つ。
   第14章の登録(`register_class_methods`)はクラス名の順の後勝ちで、名前が後ろのクラスが勝つ。
   2 つの規則が食い違うのは、先に宣言したクラスが、
   クラス名の順で後に宣言したクラスより前にあるときである。
   このとき型検査と実行が別のクラスを選び、型検査が選んだ実体と違う実装が黙って走るか、
   偽の「インスタンスが見つかりません」が出る。
   §14.6 が述べるとおり、ディスパッチの規約は、
   宣言を受理する側と実行する側で同じ 1 つでなければならない。
   そこで、衝突そのものを宣言の時点で拒否する。
   どちらかに後勝ちの規則を与える方法は、同じ順序の規則を 2 か所に実装することになるので採らない。
   検査は既存のクラスをすべて走査するが、不変条件が帰納的に保たれるので、衝突の相手は高々 1 つで、
   エラーの文言も決定的である。

   この検査が扱うのは、クラスどうしの衝突だけである。
   クラスメソッドと同名のトップレベルの `let` / `extern` との衝突は拒否せず、**先勝ち**で解決する。
   非修飾名の勝者は、最初にその名前を持った側である。
   プレリュードの `echo` がある状態で利用者のクラスが `echo` メソッドを宣言しても、
   非修飾の `echo` はプレリュードのままである(メソッドは `Cls.echo` と修飾すれば呼べる)。
   逆に、クラスより後に書いた同名の `let` は、パス 2 の逐次的な束縛によって、
   その `let` 以降のコードにだけ見える。
   この規則を選ぶのは、実行時と一致させるためである。
   実行時は、起動時に置いたメソッドのラッパを後の束縛が版複製(§14.13)で覆うので、
   再束縛より前に作られた閉包は元の実体を見続ける。
   elab が後勝ちだと、前方参照する関数だけ、型検査と実行が別の実体を選ぶ。 *)

(* クラスパラメータが引数の頭に現れるという宣言の条件(§11.33)があるので、
   返り値からしか決まらないクラス(Read のようなもの)は宣言できない。
   そのため、曖昧性検査のテストは、
   同じ型を持つ普通の多相 let(let read_[A: Show](s: String): A = ???)で代用している *)
let register_class env (c : T.class_decl') =
  let cls = intern c.T.cls_name in
  (if Decls.reserved_predicate cls then
     type_error (c.T.cls_name ^ " は予約されたリテラル述語です(ユーザ宣言不可、D8)"));
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
  List.iter
    (fun d -> if d <> "structural" then type_error ("未知の導出規則: " ^ d ^ "(v0 は derive structural のみ)"))
    c.T.cls_derives;
  (* derive structural は、利用者が新しく宣言するクラスには書けない。sample.kel:383 は
     「利用者には書かせない。コヒーレンスを守るため、組み込みの自動導出だけがインスタンスを与える」
     と定める。受理すると、elab は任意のクラスで閉じた行に構造的導出を認めるのに、
     実行時の構造的フォールバック(§14.7)は Eq.eq に決め打ちなので、
     型検査を通ったプログラムが実行時に落ちる。
     プレリュード所有のクラスの再宣言は照合の対象なので、ここでは弾かない。
     導出の指定が一致するかは add_class_decl が見る。この検査はカインドの検査より先に置く。
     逆の順だと、新しいクラスに、カインドを直せという直しようのない案内が出る
     (直すと、今度はこちらの検査に当たる) *)
  (if List.mem "structural" c.T.cls_derives && (not !Decls.in_prelude) && not (Hashtbl.mem Decls.classes cls) then
     type_error "derive structural はユーザ宣言のクラスには書けません(構造的な型へのインスタンスは組み込みの自動導出のみが与えます)");
  (* derive structural のカインドの検査。sample.kel:397-399 は、derive structural を
     書けるのはパラメータのカインドが Type のクラスだけで、カインドで判別できるので宣言の
     時点でエラーにする、と定める。構造的導出はレコードやヴァリアントの各フィールドへ制約を
     配る規則なので、Type のクラスにしか意味が無い。上の全面的な拒否があるので、この検査が
     単独で効くのは、プレリュード(--prelude で差し替えたものを含む)を処理している間と、
     クラス表に既にある名前でクラスを宣言したときだけ *)
  (if List.mem "structural" c.T.cls_derives && not (same_kind param_kind KStar) then
     type_error
       ("derive structural は Type のクラスにしか付けられません(" ^ c.T.cls_name ^ " のパラメータは "
      ^ show_kind param_kind ^ " です)"));
  let methods =
    List.map
      (fun (v : T.class_val) ->
        let mt_params =
          List.map
            (fun tp ->
              (* カインドは使われた位置から推論し、メソッドの型を一般化した直後に
                 KStar へ既定化する(第1章 §1.6) *)
              let kind = if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var () in
              let classes = List.map (fun li -> intern (show_long_id li)) tp.tp_classes in
              (tp.tp_name, TVar (ref (Generic { vid = new_oid (); vlevel = 0; vkind = kind; vcls = classes }))))
            v.T.cv_tparams
        in
        let types = List.fold_left (fun m (n, t) -> SMap.add n t m) (SMap.add param.tp_name pvar env.types) mt_params in
        let ty = elab_type_outer { env with types } 1 v.T.cv_ty in
        (* 最外のラベル付きの行は開く(§11.26 の値束縛と同じく、Rigid を Generic に変える)。
           仕様 §9 は、束縛の最外に型クラスのメソッドを数える(sample.kel:476)。
           開かないと、val f: (T) => Int32 @ Console のメソッドがどの文脈からも呼べない。
           開くのは注釈の頭が矢印リテラルのときだけで、頭が型エイリアスなら、展開先の
           矢印は入れ子なので、書いた行を閉じたまま読む(§11.5 の規則 4)。値束縛の
           outer_eff_written(§11.28)と同じく構文を見る判定で、こちらは cv_ty を見る。
           どちらかを変えるときは、両方を合わせる *)
        let ty, eff_rigids =
          match (snd v.T.cv_ty, repr ty) with
          | T.EArrow _, TArrow (a, r, e) ->
              let e', rig = open_explicit_eff 1 e in
              (TArrow (a, r, e'), rig)
          | _ -> (ty, [])
        in
        Unify.generalize 0 ty;
        release_rigids eff_rigids;
        List.iter (fun (_, t) -> match repr t with TVar r -> default_kind (Unify.var_info_of r).vkind | _ -> ()) mt_params;
        (* クラスパラメータが少なくとも 1 つの引数の頭に現れることを要求する(§11.33)。
           実行時のディスパッチ(tycon_of_value)は値の頭のコンストラクタしか見ないので、
           List[A] のようにパラメータが引数の内側に埋もれた形は選べない。頭に現れる
           ことは、その引数でタグによるディスパッチができることを保証する *)
        let head_is_param t =
          match repr (fst (app_spine t)) with TVar r -> ( match !r with Generic i -> i.vid = pinfo.vid | _ -> false) | _ -> false
        in
        (match repr ty with
        | TArrow (args, _, _) -> (
            match repr args with
            | TRecord row when List.exists (fun (_, t) -> head_is_param t) (fst (row_fields row)) -> ()
            | _ ->
                type_error
                  ("メソッド " ^ v.T.cv_name ^ " はクラスパラメータが引数の頭に現れないため v0 では宣言できません(実行時タグディスパッチの前提、§7.4)"))
        | _ -> type_error ("メソッド " ^ v.T.cv_name ^ " の型は矢印型でなければなりません"));
        (v.T.cv_name, ty))
      c.T.cls_vals
  in
  (* 同じクラスの中でのメソッドの重複を拒否する(register_effect の操作の重複と同じ)。
     素通しにすると、elab の修飾名の型は最後の宣言で決まり、インスタンス本体の照合は
     最初の宣言を見るので、型検査を通ったプログラムが実行時に型やアリティの食い違いで壊れる *)
  let rec dup = function
    | [] -> ()
    | (m, _) :: rest -> if List.mem_assoc m rest then type_error ("メソッド " ^ m ^ " が二重に宣言されています") else dup rest
  in
  dup methods;
  (* 非修飾名の所有者は高々 1 クラス、という不変条件をここで守る。破れると、elab(宣言順の先勝ち)と
     interp(クラス名の順の後勝ち)が別の規則で勝者を選ぶ。両者が別のクラスを選ぶと、
     誤った実体を呼ぶか、偽の「インスタンスが見つかりません」を出す。組み込みと同名の
     クラスの再宣言は同じ oid なので素通しになる。不変条件が帰納的に保たれるので、
     候補は高々 1 つで、文言も決定的 *)
  List.iter
    (fun (m, _) ->
      Hashtbl.iter
        (fun _ (other : Decls.class_info) ->
          if other.Decls.ci_name <> cls && List.mem_assoc m other.Decls.ci_methods then
            type_error
              ("メソッド名 " ^ m ^ " は型クラス " ^ name_of other.Decls.ci_name
             ^ " が既に宣言しています(非修飾名が衝突するため、v0 では同名メソッドを複数のクラスに宣言できません)"))
        Decls.classes)
    methods;
  match
    Decls.add_class_decl
      {
        Decls.ci_name = cls;
        ci_param = pinfo;
        ci_param_kind = param_kind;
        ci_derive_structural = List.mem "structural" c.T.cls_derives;
        ci_builtin = false;
        ci_methods = methods;
      }
  with
  | `Added -> methods
  | `Builtin prev ->
      (* 組み込みと同名のクラス。構造の照合は第6章の add_class_decl が済ませている。
         実体は組み込みを使う *)
      prev.Decls.ci_methods

(* ## 11.34 インスタンスの頭

   インスタンスの頭は、`Int32` か `List[_]` の形しか受けない。
   `List[Int32]` のような具体的な頭は書けない。
   `_` は位置を表す。
   前提つきインスタンス(仕様 §8)の束縛子は、この位置へ左から順に対応する(sample.kel:412-413)。
   型パラメータのリストを `instance` の直後に書くことと、
   `instance` と `[` の間の空白や改行の置き方が自由であることも、
   仕様の同じ段落の 1 行目に書かれている(sample.kel:410)。

   束縛子が左から順に穴を埋め、埋まらなかった穴はカインドの矢印として残る。
   同じ `List[_]` でも、表すものは束縛子の個数で変わる。
   `Functor[List[_]]` では、未適用の `List` を表す(束縛子 0 個、カインド `[_] Type`)。
   `type instance[A: Eq] Eq[List[_]]` では、`List[A]` を表す(束縛子 1 個、カインド `Type`)。
   頭のカインドは、束縛子の個数だけ適用した後のカインドで、2 つの例はこの 1 つの規則の両端である。
   束縛子の個数は、`_` の個数を超えられない。
   対応しなかった右側の `_` が未適用のまま残ることも仕様が規則として書いており、
   `Eq[List[_]]` と `Functor[List[_]]` の両端も条文に挙がっている(sample.kel:414-416)。

   `_` の個数そのものは、型構成子のアリティと一致していなければならない(sample.kel:411)。
   この照合が無いと、`Functor[List[_, _, _]]` も、穴なしの `Functor[List]` も受理してしまう。
   表に載っている構成子では、`con_kind` が `holes` を捨てるからである。

   インスタンス表のキーは(クラス, 型構成子の頭)の 2 つ組で、前提はキーに入らない。
   探索は表を 1 回引くだけである。
   重なり合うインスタンスは存在しないので、
   コヒーレンスは「同じキーを 2 度登録したらエラー」という 1 つの規則で保証できる(sample.kel:357)。
   組み込みのキーに対する利用者の 1 度目の宣言は、受理するが採用しない(§6.9)。
   そのため、組み込みのキーでエラーになるのは、利用者の 2 度目の宣言からである。
   この数え方は、第6章の `builtin_redecls` 表が持つ。

   頭のカインドは、クラスのパラメータのカインドと一致していなければならない(sample.kel:400)。
   `Functor` は `[_] Type` のクラスなので、`Functor[Int32]` はここで落ちる。
   束縛子つきなら、束縛子のカインドも、
   頭の構成子がその位置に要求するカインドと一致していなければならない(sample.kel:417)。
   たとえば `[F[_]: C]` を `List[_]` の穴には置けない。

   行カインドのパラメータを持つ型も、この照合で落ちる。
   `newtype Callback[E]` の頭のカインドは `EffectRow -> Type` なので、
   `Functor[F[_]]` が要求する `Type -> Type` と合わず、
   `type instance Functor[Callback[_]]` は宣言の時点で落ちる(`test/kinds.t` の nofunctor)。
   仕様 §8 はこれを、`derive structural` を Type のクラスに限る規則(sample.kel:397-399)と並べて、
   同じカインドの規律から出る帰結として書いている(sample.kel:400-402)。
   条文の主語は「インスタンスの頭部のカインド」で、上の段落の照合そのものである。
   利用者から見えるのは `Callback` を `Functor` にできないという制限だけだが、
   仕様がこれを書いているので、この制限は実装の都合ではなく言語の規則である。 *)

let instance_head (i : T.instance_decl') =
  let cls = intern i.T.ins_class in
  let head =
    match i.T.ins_args with
    | [ h ] -> h
    | _ -> type_error "type instance の型引数は1個です(D11)"
  in
  let con, holes =
    (* 修飾名 M.T も受ける。受けないと、module の外からその pub 型にインスタンスを書く
       手段が無い。可視性の検査も、型注釈と同じように通す。通さないと、名前で触れる
       ことも許されない非 pub の型に外からインスタンスを付けられ、module 自身の
       コヒーレンスの枠まで横取りされる(型名を oid に落とす経路は、すべて同じ検査を通る) *)
    match snd head with
    | T.EIdent (LongId comps) -> (Decls.resolve_con (intern (String.concat "." comps)), 0)
    | T.EApply ((_, T.EIdent (LongId comps)), args) ->
        List.iter (fun (a : T.type_exp) -> match snd a with T.EHole -> () | _ -> type_error "インスタンス頭の型引数は _ だけです(List[_] の形)") args;
        (Decls.resolve_con (intern (String.concat "." comps)), List.length args)
    | _ -> type_error "インスタンス頭は 型構成子 か 型構成子[_, ...] の形で書いてください"
  in
  Decls.check_con_visible con;
  (* 頭の _ の個数は、構成子のアリティと一致していなければならない。
     これを見ないと、Functor[List[_, _, _]] が通る *)
  let rec kind_arity k = match kind_repr k with KArrow (_, r) -> 1 + kind_arity r | _ -> 0 in
  let arity = kind_arity (Decls.con_kind con holes) in
  if holes <> arity then
    type_error
      ("インスタンス頭 " ^ name_of con ^ " は型引数を " ^ string_of_int arity ^ " 個取りますが、_ が "
     ^ string_of_int holes ^ " 個書かれています");
  (* 前提の束縛子は、頭の _ へ左から順に対応する。余った _ は未適用のまま残り、
     カインドの矢印になる(Functor[List[_]] が束縛子 0 個で通る形) *)
  let np = List.length i.T.ins_tparams in
  if np > holes then
    type_error
      ("インスタンスの型パラメータが " ^ string_of_int np ^ " 個ありますが、頭 " ^ name_of con ^ " の _ は "
     ^ string_of_int holes ^ " 個です");
  (cls, con, holes)

(* ## 11.35 インスタンスの登録

   パス 1c では、インスタンスの頭とメソッド名と、束縛子から組んだ前提だけを登録し、
   本体の検査はパス 2 に回す(§11.38)。
   本体の推論には、値環境が揃っている必要があるからである。
   前提は `class_names_of` を通して(引数位置, クラス)の組にするので、
   未知のクラスや予約述語の拒否が、束縛子の位置でもそのまま効く(`test/premise.t` の pr8 / pr9)。
   第8章 §8.4 の `TCon` の分岐は、インスタンス表に載ったこの前提を使う。

   ここでは 2 方向の照合を行う。
   宣言していないメソッドを書いていないか(過剰)と、クラスのメソッドをすべて書いたか(網羅)である。
   片方だけでは足りない。
   過剰を許すと綴りの誤りが黙って無視され、網羅を確かめないと実行時にメソッドが見つからない。

   インスタンス本体に書けるのは、`let` と `let rec` だけである。
   `Functor[List[_]]` の `map` は自分自身を再帰呼び出しするので、
   `let rec` が要る(sample.kel:441-444)。 *)

let register_instance (i : T.instance_decl') =
  let cls, con, holes = instance_head i in
  (* 予約述語は、頭を見た時点で拒否する。add_instance にも同じ検査があるが、そちらは
     未知の構成子、カインド、網羅の検査より後なので、頭の書き方によっては、予約述語とは
     別の理由のエラーが先に出てしまう *)
  (if Decls.reserved_predicate cls then
     type_error (i.T.ins_class ^ " は予約されたリテラル述語です(インスタンスは宣言できません、D8)"));
  let ci = match Decls.find_class cls with Some ci -> ci | None -> type_error ("未知のクラス: " ^ i.T.ins_class) in
  if not (Hashtbl.mem Decls.con_kinds con) then type_error ("未知の型構成子: " ^ name_of con);
  (* 頭のカインドは、束縛子の個数だけ適用した後のカインドである。同時に、束縛子の
     カインドが、頭の構成子がその位置に要求するカインドと一致することを確かめる
     ([F[_]: C] を List[_] の穴には置けない) *)
  let rec head_kind k tps =
    match tps with
    | [] -> k
    | tp :: rest -> (
        match kind_repr k with
        | KArrow (a, r) ->
            let kb = if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var () in
            if not (same_kind a kb) then
              type_error
                ("インスタンスの型パラメータ " ^ tp.tp_name ^ " のカインドが頭 " ^ name_of con ^ " の引数と一致しません");
            head_kind r rest
        | _ -> bug "instance: 束縛子が頭のアリティを超えています(D96 の検査が先に落とすはず)")
  in
  if not (same_kind ci.Decls.ci_param_kind (head_kind (Decls.con_kind con holes) i.T.ins_tparams)) then
    type_error
      ("インスタンス頭 " ^ name_of con ^ " のカインドがクラス " ^ i.T.ins_class ^ " のパラメータと一致しません");
  (* 前提は(引数位置, クラス)の組。束縛子 i は頭の引数位置 i に対応するので恒等写像。
     class_names_of を通すので、未知のクラスや予約述語の拒否が束縛子の位置でも効く *)
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
  (* メソッドの網羅と過剰 *)
  List.iter
    (fun (m, _) ->
      if not (List.exists (fun (m2, _) -> intern m2 = m) ci.Decls.ci_methods) then
        type_error ("クラス " ^ i.T.ins_class ^ " にメソッド " ^ name_of m ^ " はありません"))
    methods;
  List.iter
    (fun (m, _) ->
      if not (List.mem_assoc (intern m) methods) then
        type_error ("インスタンスがメソッドを網羅していません: " ^ m ^ " が漏れています"))
    ci.Decls.ci_methods;
  Decls.add_instance ~builtin:false ~methods ~cls ~con premises

(* ## 11.36 前方参照できる束縛の条件

   パス 1c で登録する、注釈が完全な `let` の署名は、前方参照を通すためのものである。
   sample.kel:456 の `user_names` が、後ろで定義される `println`(:508)を呼べるのは、
   この署名があるからである。

   「完全」をどう定義するかで、前方参照の健全性が決まる。
   本体を見ずに作る署名は、決まっていない部分を含んではならない。
   注釈の頭の矢印で `@` を省略すると、束縛自身の行は本体からしか決まらない。
   本体を推論するときは、この行が呼び出し側の `eff` に結ばれるが、
   本体を見ずに署名だけを作ると、この行は何にも縛られない行変数のまま一般化される。
   するとその関数はどんなエフェクトでも起こしてよいことになり、
   エフェクト検査が抜けるかどうかが宣言順で変わる。
   前方参照した呼び出しは通り、同じ呼び出しを定義の後ろに書くと落ちる。

   入れ子の矢印で省略した `@` は、`@ {}` に確定する(仕様 §9)。
   こちらは本体を見なくても決まっているので、署名を作る妨げにならない。
   残る自由度は束縛自身の行だけなので、条件は次のようになる。

   前方参照の署名に使えるのは、注釈の**頭の矢印**で `@` を省略していない束縛か、
   `pub` の束縛だけである。
   関数束縛では、束縛自身の `@` が明示されているか、束縛が `pub` であることを求める。
   値束縛では、注釈の頭が矢印なら、その `@` が明示されているか、束縛が `pub` であることを求める。
   どちらも、引数と返り値に型注釈があることが前提である(§11.37)。

   判定は `signature_of_binding`(§11.37)の `full` が行う。
   関数束縛では束縛自身の `@`(`lb_eff`)を見て、値束縛では注釈の頭の矢印を `head_effected` で見る。
   どちらも入れ子の矢印は見ないので、
   `let helper[E](f: () => Unit @ E, g: (Int32) => Int32): Int32 @ {Console extends E}` は、
   `g` の `@` を省略していても署名になる(`test/typecheck_m6.t` の fwdsig)。
   入れ子の矢印にまで `@` を要求すると、
   この 1 つの省略だけで前方参照が「未束縛の変数: helper」で落ち、受理が宣言順に依存する。
   注釈の中のすべての矢印に `@` を求める `fully_effected` は、pub の完全注釈検査(§11.31)が使う。

   値束縛でも、`pub` なら、`@` を省略した注釈から署名を作る。
   `pub` で省略した `@` は、本体は純粋で公開される型は行多相、という意味に確定しているので、
   関数束縛と同じ理由で、本体を見ずに署名を作れる。
   これを認めないと、`pub let k: (Int32) => Int32` を前方参照した呼び出しだけが、
   「未束縛の変数」で落ち、受理が宣言順に依存する。
   注釈の頭の矢印で `@` を省略した、`pub` でない値束縛には、署名を作らない。
   行が本体からしか決まらないので、
   この形は前方参照できない(前方参照を許すには本体を見る必要がある)。

   もう 1 つの規則は先勝ちである。
   1c は、環境にまだ無い名前についてだけ署名を登録する。
   同名の `let` が 2 つあれば、1 つ目の署名だけが前方参照に使われる。
   プレリュードの束縛やクラスメソッドと同名の `let` は署名を登録せず、
   その名前の前方参照は既存の実体の型で検査する。
   実行時の版複製(§14.13)は、前方参照する関数に、最初にその名前を持った側の実体を見せる。
   後勝ちにすると、型検査が選ぶ実体がこれと逆になり、同名の `let` 2 つと前方参照を含むプログラムが、
   型検査を通ったうえで黙って別の型の値を返す。 *)

(* ## 11.37 署名の構築

   条件を満たした束縛について、本体を見ずに型を組み立てる。
   型パラメータを剛定数にし、注釈を精緻化し、一般化してから剛定数を解放する。
   剛定数の扱いは、§11.25 の 3 段の手順そのものである。

   関数束縛では、引数パターンがすべて `PAnnot`(注釈つき)であることも要求する。
   注釈のない引数があれば、その型は本体からしか分からない。

   `signature_of_binding` は例外を握り潰して `None` を返す。
   このパスの目的は、登録できる署名を登録することで、エラーを報告することではない。
   ここで落ちる型注釈は、パス 2 で本体を推論するときにもう一度精緻化され、
   そのとき正しい文脈で正しいエラーになる。
   1c で先に報告すると、エラーの出る位置が宣言順に依存する。

   握り潰す節には `Type_error_at` も並べる。
   位置つきの例外だけを素通りさせると、1c が黙って諦めるはずの注釈のエラーをその場で報告してしまい、
   避けたい宣言順への依存が、位置つきで現れる。
   この形の回帰は、`test/errloc.t` の sig.kel が見張っている。 *)

let signature_of_binding env (b : T.let_binding') : ty option =
  let params_annotated =
    match b.T.lb_params with
    | None -> true
    | Some ps -> List.for_all (fun (_, p) -> match p with T.PAnnot _ -> true | _ -> false) ps
  in
  (* 注釈の頭の矢印にだけ @ を要求する(§11.36)。入れ子の省略 @ は @ {} に確定するので、
     本体を見なくても決まっている。残る自由度は束縛自身の行だけで、関数束縛には lb_eff を、
     値束縛には注釈の頭が矢印ならその @ を要求する。どちらも pub なら省略してよい。
     pub の省略 @ は、本体は純粋で公開される型は行多相、という意味に確定しているから *)
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
            let fn_eff, eff_rigids =
              match b.T.lb_eff with
              | Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e)
              | None ->
                  (* ここに来るのは pub のときだけ(full の条件)。本体の側と同じく、
                     Rigid を Generic に変える *)
                  let r = new_rigid_ref ~kind:KRow lvl in
                  (TVar r, [ ("", TVar r, r) ])
            in
            let ret_ty = match b.T.lb_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> assert false in
            release_rigids eff_rigids;
            TArrow (TRecord (closed_item_row param_tys), ret_ty, fn_eff)
        | None -> (
            (* 1c の署名も、パス 2 と同じ読みをする。開かないと、前方参照の有無で値束縛の
               行の開き方が変わる。値の型の位置のカインドの照合(§11.3)も通す *)
            match b.T.lb_ret with
            | Some t -> (
                let ty = elab_value_type_outer env_ty lvl "型注釈" t in
                match (snd t, repr ty) with
                | T.EArrow (_, _, Some _), TArrow (a, r, e) ->
                    let e', eff_rigids = open_explicit_eff lvl e in
                    release_rigids eff_rigids;
                    TArrow (a, r, e')
                | T.EArrow (_, _, None), TArrow (a, r, _) when b.T.lb_pub ->
                    (* pub の省略 @ は、公開の側で行多相。1c は本体を見ないので、
                       新しい行変数を置き、一般化で Generic にする *)
                    TArrow (a, r, new_row_var lvl)
                | _ -> ty)
            | None -> assert false)
      in
      Unify.generalize 0 ty;
      release_rigids rigids;
      Some ty
    with Type_error _ | Type_error_at _ | NotImplemented _ | NotImplemented_at _ -> None

(* ## 11.38 インスタンス本体の検査

   インスタンスのメソッド本体が、クラス宣言の型を満たしているかを確かめる。
   期待型は、クラス宣言のメソッド型にインスタンスの頭型を代入したものである。
   `Functor` の `map : (F[A], (A) => B @ E) => F[B] @ E` に `F := List` を代入すると、
   `(List[A], (A) => B @ E) => List[B] @ E` になる。
   代入は `map_generics_with` にメモを 1 つ仕込むだけで、
   `tapp` の正規化が `F[A]` を `List[A]` に畳む(第1章)。

   検査は単一化ではなく**包摂**である。
   次の表のとおり、2 つの側で扱いが逆になる。

   | 側 | 操作 | 意図 |
   |---|---|---|
   | 推論された型 | `instantiate` | どんな型にでもなれるので、柔らかい変数にする |
   | 期待型 | `skolemize` | どの型でも通らなければならないので、剛定数にする |

   そのうえで単一化する。
   推論された型のほうが期待型より多相であれば通り、
   足りなければ剛定数に具体型を代入しようとして落ちる。
   これが、実装は宣言と同じか、それより一般的でなければならない、という検査である。
   両方を `instantiate` すると、たまたま一致する具体型があるだけで通ってしまい、
   両方を `skolemize` すると何も通らない。

   最外の行だけは、表の 2 つの操作とは別に扱う。
   引数と返り値を先に単一化し、そのあとで実装の最外の行を見る。
   実装の行が空なら、宣言の行とは単一化せずに受理する。
   純粋な実装はどの行の下からでも呼べるので、公開される型として行多相を名乗ってよい。
   引数と返り値を先に単一化するのは、メソッドの引数に `@` を省略した矢印があると、
   引数の単一化で実装の行が `{}` に固まるからである(入れ子の矢印で省略した `@` は `@ {}` を意味する)。
   固まった行は本体が何も起こさないことの証明で、空の行は行の最小元なので、
   そこから一般化しても嘘にならない。
   仕様 §9 は、型クラスのメソッドは実装が純粋で、公開される型は行多相であると定めており、
   この扱いは、それを包摂の側で実現する。
   空の行をこう扱わないと、引数の矢印の `@` を省略したメソッドが、
   宣言できるのに実装できないものになる。
   `val fmap2[X, Y]: (F[X], (X) => Y) => F[Y]` がその例である(`test/classes.t` の clsrow)。

   実装が純粋でなければ、包摂は失敗する。
   最外の行の単一化で失敗したときは、診断がその規則を名指しする。

   ```
   型エラー: 型クラスのメソッドの実装は純粋でなければなりません(公開される型は行多相 — 仕様 §9)。
   インスタンスメソッド size の本体がエフェクトを起こしています。元の報告: (単一化の報告)
   ```

   名指しするかどうかは、宣言の側の行を見て決める。
   宣言の行がラベル 0 個の裸の行変数なら、宣言はどの行でも名乗れるとしか言っていないので、
   失敗の理由は、実装が何かを起こしたことだけである。
   最外の `@` を省略した形(clsimpure)も、
   メソッドの型パラメータに行変数を取って `@ E` と書いた形(clsbarerow)も、名指しの対象になる。
   宣言が `@ Print` のようにラベルを書いていれば、
   失敗はそのラベルと実装が起こしたラベルの食い違いで、純粋性の問題ではない。
   そのときは「クラス宣言の型を満たしません」の文言で落とす(clsmismatch)。
   失敗が行に由来するかどうかの判定には、`pub` の言い換え(§11.12)と共用の `row_failure` を使う。

   この言い分けのために、`subsume` は最外の行の単一化だけを別の `try` で包む。
   引数と返り値の単一化の失敗は、`wrap` を通って「クラス宣言の型を満たしません」の文言になる。
   `pub` の側が `pub_pure_rows` という台帳を持つのに対し、ここは台帳を持たない。
   名指しの判定に要る材料は宣言の側の行 `se` だけで、包摂のこの 1 か所で揃うからである。
   台帳を増やせば、そのぶんリセット漏れ(§11.41 の `Hashtbl.reset`)の危険も増える。

   判定の材料が宣言の側だけなので、名指しは本来の対象より少し広く働く。
   実装が自分の注釈に `@ Print` と書き、その本体は何も起こしていないときも、
   宣言が裸の行なら同じ文言で落ちる。
   この形で実際に起きているのは、実装の最外の行が空でないことで、
   文言の後半の「本体がエフェクトを起こしています」は字義どおりには成り立たない。
   それでも、直し方(実装の側の注釈を外す)には辿り着けるので、本実装はこの文言を使う。

   名指しが届かない形もある。
   メソッドが `(T, () => Unit @ E) => Unit @ E` のように高階の引数を取り、
   実装の本体がその引数を呼ぶと、本体の行が引数の行へ流れ込む。
   すると先に行う引数の単一化のほうが失敗し、`wrap` の文言になる(clsargcall)。
   本体が引数を呼ばなければ、最外の行の単一化まで届く(clsargpure)。
   同じ宣言でも実装によって文言が変わるが、落ちること自体はどちらも同じである。

   裸の行かどうかの判定は、`skolemize` が届ける行の形に依存している。
   最外の `@` を省略したメソッドの行は、`elab_type_outer` が行変数を作り、
   `generalize` が `Generic` に変え、`skolemize` が `Rigid` に戻して届く。
   この経路のどこかが変わると名指しが黙って働かなくなるので、
   clsimpure と clsbarerow がこれを見張っている。

   前提つきインスタンスでは、頭型が部分適用の形になる。
   `type instance[A: Eq] Eq[List[_]]` の頭型は `List[A]` で、
   `A` は `make_rigids` が作る剛定数である。
   この剛定数の `vcls` には、前提の `Eq` が載っている。
   この前提が無いと、包摂は本体の推論結果(`Eq` 制約つきの弱い変数)をこの剛定数へ束縛しようとして、
   §8.4 の `Rigid` の分岐で落ちる。
   その結果、正しい実装が「`[A: Eq]` のように制約を書いてください」と拒否される。
   `skolemize` は `Generic` しか写さないので、頭の `Rigid` はそのまま残り、
   前提は期待型の側に剛定数の要求として載る。
   `expected_of` と `subsume` には、前提つきインスタンスのための処理が無い。
   `tapp` の正規化が `F[A]` を `List[A]` に畳むからである。
   束縛子の名前は本体の型スコープにも入るので、
   メソッドに `xs: List[A]` と注釈を書ける(sample.kel:418-419)。
   メソッド自身の型パラメータが同名なら、内側が勝つ。
   この遮蔽の向きも、仕様の同じ箇所(sample.kel:418-419)に書かれている。

   本体は普通の `elab_binding` / `elab_rec_bindings` で推論する。
   そのため、注釈つきのメソッドも `let rec` のメソッドも同じ経路で通る(sample.kel:441-444)。 *)

let check_instance_bodies env (i : T.instance_decl') =
  let cls, con, _holes = instance_head i in
  let ci = match Decls.find_class cls with Some ci -> ci | None -> bug "instance: class 未登録" in
  (* 前提つきインスタンスの頭型は、部分適用の形。束縛子を剛定数にして vcls に前提を載せる。
     束縛子が 0 個なら頭型は TCon (con, [])。束縛子の名前は本体の型スコープに入る *)
  let head_rigids = make_rigids 1 i.T.ins_tparams in
  let head_ty = TCon (con, List.map (fun (_, t, _) -> t) head_rigids) in
  let env = { env with types = List.fold_left (fun m (n, t, _) -> SMap.add n t m) env.types head_rigids } in
  let expected_of mname =
    match List.assoc_opt mname ci.Decls.ci_methods with
    | Some scheme ->
        let memo = Hashtbl.create 8 in
        Hashtbl.add memo ci.Decls.ci_param.vid head_ty;
        Unify.map_generics_with memo (fun info -> TVar (ref (Generic info))) scheme
    | None -> bug "instance: メソッドスキーマ未登録"
  in
  let subsume mname inferred =
    let lvl = 1 in
    let skol = Unify.skolemize lvl (expected_of mname) in
    let inf = Unify.instantiate lvl inferred in
    (* 包摂が失敗したときの既定の文言。最外の行の単一化だけは別に包んで純粋性の規則を
       名指しするので、包む単位をここで関数に切り出す。引数と返り値の失敗はこの文言になる *)
    let wrap f = try f () with Type_error msg -> type_error ("インスタンスメソッド " ^ mname ^ " がクラス宣言の型を満たしません(" ^ msg ^ ")") in
    (* 最外の行は最後に見る。仕様 §9 は、型クラスのメソッドは実装が純粋で、
       公開される型は行多相であると定める。引数と返り値を先に合わせたあと、
       実装の行が空(純粋)なら、宣言の行(剛定数)と単一化せずに受理する。
       純粋な実装はどの行の下からでも呼べるので、公開の型として行多相を名乗ってよい。
       pub の @ 省略は Rigid を Generic に変えて同じ非対称を作るが、ここではそれを
       推論された空の行に対して行う。メソッドの引数に @ を省略した矢印があると、
       実装の行は {} に固まるので、この扱いが無いと、宣言できるのに実装できない
       メソッドが生じる *)
    match (repr inf, repr skol) with
    | TArrow (ia, ir, ie), TArrow (sa, sr, se) ->
        wrap (fun () -> Unify.unify ia sa);
        wrap (fun () -> Unify.unify ir sr);
        if repr ie = TRowEmpty then ()
        else
          (* 宣言の側の行がラベル 0 個の裸の行変数(メソッドの最外の @ を省略した形など)
             のときだけ、規則を名指しする。単一化の一般の文言
             「行 ς1 は注釈で固定された行変数なので」では、純粋性が規則だと読み手に伝わらない。
             宣言が @ Console と書いていればラベルの食い違いなので、
             クラス宣言の型を満たさないという文言のままにする *)
          let bare = match row_fields se with [], tail -> ( match repr tail with TVar _ -> true | _ -> false) | _ -> false in
          (try Unify.unify ie se
           with Type_error msg ->
             if bare && row_failure msg then
               type_error
                 ("型クラスのメソッドの実装は純粋でなければなりません(公開される型は行多相 — 仕様 §9)。インスタンスメソッド " ^ mname
                ^ " の本体がエフェクトを起こしています。元の報告: " ^ msg)
             else type_error ("インスタンスメソッド " ^ mname ^ " がクラス宣言の型を満たしません(" ^ msg ^ ")"))
    | _ -> wrap (fun () -> Unify.unify inf skol)
  in
  List.iter
    (fun ((_, d) : T.decl) ->
      match d with
      | T.DLet ((_, b) as bnode) ->
          let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
          let env2 = elab_binding env 0 (new_row_var 0) bnode in
          (* 包摂のエラーは、そのメソッドの束縛を指す。宣言の先頭を指すと、複数のメソッドの
             どれが悪いかを位置から読めない *)
          at_node bnode (fun () -> subsume mname (SMap.find mname env2.values))
      | T.DLetRec bs ->
          let env2 = elab_rec_bindings env 0 (new_row_var 0) bs in
          List.iter
            (fun (((_, b) as bnode) : T.let_binding) ->
              let mname = match binding_name b with Some x -> x | None -> bug "instance: 名前なし" in
              at_node bnode (fun () -> subsume mname (SMap.find mname env2.values)))
            bs
      | _ -> type_error "インスタンス本体には let だけが書けます")
    i.T.ins_body;
  release_rigids head_rigids

(* ## 11.39 宣言列を 4 回なめる

   `process_decls` が、章の冒頭の表を実装する。
   ここでは、パスの順序の理由をコードに即して述べる。

   **1a**：エイリアスと newtype の頭を登録する。
   型の本体を精緻化するには、その中に出てくるすべての型構成子のカインドが引けなければならない。
   そこで、名前とカインドだけを先に登録する。
   プレリュードが持っている名前を利用者が再宣言したときは、プレリュードの側を残す。

   **1a の後始末**：newtype の本体を投機する。
   1a が終わった直後に宣言列をもう一度なめ、newtype の本体を一度だけ投機的に精緻化する。
   目的は、パラメータのカインドを宣言順に依存せずに決めることだけで、
   `speculate_newtype` はフィールドの型を `elab_type` に渡すほかは何もしない。
   1b の `register_newtype` と違って、コンストラクタを登録しない。
   `Decls.add_data` も `Unify.generalize` も `pub` の完全注釈検査も呼ばないので、
   残る副作用は `elab_type` がカインドのセルに張る単一化だけである。
   走っている間だけ `speculating` を立て、§11.3 の読み分けがそれを見て、
   型としても行としても読める字面(要素なしの波括弧)を飛ばす(§11.31)。

   下で述べるエイリアスの投機と、道具は同じである。
   どちらも診断を捨て、`Panic` は捕まえない。
   捕まえるのは、握り潰す節に並べた 4 つの例外
   (`Type_error` / `Type_error_at` / `NotImplemented` / `NotImplemented_at`)だけである。
   違いは 2 つある。
   1 つ目は走る位置で、エイリアスの投機が 1b の後に来るのに対し、newtype の投機は 1b の前に置く。
   1b の読み分けが相手のパラメータのカインドを見るので、それより前に済ませる必要がある(§11.31)。
   2 つ目は握り潰す単位で、newtype の投機はフィールドごとに握り潰す。
   エイリアスは本体が 1 つなので差が出ないが、newtype で本体全体を 1 つの `try` に包むと、
   投機の時点では未知のエフェクトラベルを含むフィールドで例外が飛び、
   後続のフィールドの張りまで失う(§11.31)。
   投機と既定化は、newtype の投機(1a の後)、1b、エイリアスの投機(1b の後始末の 1 周目)、
   既定化(2 周目)の順に並ぶ。

   newtype の投機のループも `with_decl_module` で包む。
   module の中の newtype のフィールド型は module の内部型を非修飾で参照するので、
   包み忘れたパスだけが「未知の型」になる。
   これを見張るのは `test/kinds.t` の fwdrowmod2 で、module の中の深さ 2 の連鎖である。
   fwdrowmod は内部型を参照しない `B6` の投機だけで通るので、包みを外しても通ってしまい、
   見張りにならない。

   **1b**：コンストラクタ、操作、メソッドを登録する。
   型の本体を精緻化して宣言表に登録するのは、このパスである。
   1a とその後始末が終わっているので、原則として宣言の順序に依存しない。
   newtype どうしが互いを参照しても、effect が後ろの newtype を使っても通る。
   例外は、§11.31 で述べた、投機が相手のパラメータのカインドを決められない形へ、
   波括弧で書いた行を前方参照で渡す場合である。
   クラスのメソッドは、非修飾名(`map`)と修飾名(`Functor.map`)の両方で値環境に登録する。
   どちらでも書けるという仕様を、環境に 2 つ入れるという最も単純な方法で実現している。

   1b の後始末として、宣言列をもう一度なめる小さなループが 2 つ走る。
   仕事は 3 つある。
   1 つ目は、クラスメソッド、newtype、型エイリアスの型パラメータの制約に、
   未知のクラスや予約述語が無いかを確かめることである。
   1b の中で確かめると、後ろで宣言されるクラスを制約に書いた形が落ちるので、
   クラス表が出揃うのを待つ。
   2 つ目は、型エイリアスの本体を一度投機的に精緻化して、パラメータのカインドを推論することである。
   3 つ目は、newtype とエイリアスのパラメータのカインドを既定化することである。

   2 つ目の処理を投機と呼ぶのは、診断を捨てるからである。
   本物の検査(未知の型、再帰、部分適用)はパス 2 が同じ本体でやり直すので、ここで落とすと、
   §11.43 の「最初の 1 つ」がどのエラーになるかが変わる。
   捕まえる例外は newtype の投機と同じ 4 つだけで、`Panic` は捕まえない。

   既定化を 2 つ目のループに置くのは、宣言ごとに既定化すると、
   相互参照する newtype の間で早すぎる時点に `KStar` が固定されるからである(§11.31)。
   newtype のパラメータのカインドが、エイリアス経由で決まる形がある。
   `newtype A[X] = MkA(Cb[X])` と `type Cb[E] = Callback[E]` の `X` がその例である。
   既定化を投機より後に置くのは、この形で、投機が届く前に `X` を固定しないためである。
   表に新しく登録するものは無く、既定化は表のセルを書き換えるだけである。

   既定化がパス 2 より前に済むので、値の本体と使用点はカインドの材料にならない。
   宣言群を読み終えた時点のカインドがそのまま残り、
   `let f[E](x: Ph[E], c: Callback[E])` のような使用点が、
   `Ph` のパラメータを後から行に変えることはない。
   この形で落ちるのは `let` 自身の `E` のほうで、`Ph[E]` が先に `E` を `Type` に決める。

   既定化の直後には、`check_row_constraints` が、
   行カインドになったパラメータに型クラスの制約が書かれていないかを確かめる。
   型クラスは Type のクラスなので、行には要求できない。
   宣言の位置で確かめないと、エイリアスでは使用点ごとに落ち、
   newtype では構築点が行を見ないので素通りする。

   **1c**：インスタンスの頭と、前方参照の署名を登録する。
   頭のカインドの検査にクラス表が要るので、1b の後に置く。
   署名の登録は、本体を推論するパス 2 より前に済ませる(§11.36、§11.37)。

   **2**：本体を推論する。
   宣言順に推論し、束縛ごとに型を印字する。
   印字の前に `default_numerics` を呼ぶ。
   述語つきの弱い変数が残ったまま印字すると、利用者には意味のない内部の述語が見えるからである。

   プレリュードも同じ `process_decls` を通す。
   違いは、何もしない `emit` を渡して出力を捨てることと、
   `Decls.in_prelude` を立てて処理すること(§11.41)である。 *)

(* コンパニオン型の大域の同義語を登録する(sample.kel:838)。
   平坦化ではなく、パス 1a で行う。
   プレリュードの宣言表は、利用者の平坦化の時点ではまだ空なので、
   平坦化の時点で登録すると既存の名前との照合が働かず、
   module List { pub newtype List } のような宣言がプレリュード自身の型検査を壊す *)
let register_companion tyname =
  match !Decls.current_module with
  | Some m when tyname = m ^ "." ^ m ->
      if
        Hashtbl.mem Decls.con_kinds (intern m)
        || Hashtbl.mem Decls.aliases (intern m)
        || Hashtbl.mem Decls.reserved_type_names (intern m)
      then
        type_error
          ("module " ^ m ^ " のコンパニオン型 " ^ m ^ " は既存の型 " ^ m
         ^ " と同名です(module 内の型とトップレベルの型は同名にできません)")
      else Decls.add_con_synonym (intern m) (intern tyname)
  | _ -> ()

(* 宣言の出身 module を current_module に立てて処理する。
   process_decls で宣言列をなめるループは、すべてこれで包む。
   1b の newtype のフィールド型や、1c の signature_of_binding も、
   module 内の型を非修飾で参照するので、包み忘れたパスだけが「未知の型」になる。
   §11.41 の in_prelude と同じく、Fun.protect で元に戻す *)
let with_decl_module node f =
  let saved = !Decls.current_module in
  Decls.current_module := Hashtbl.find_opt Decls.decl_module (Tree.oid_of node);
  Fun.protect ~finally:(fun () -> Decls.current_module := saved) f

(* 行カインドのパラメータには、型クラスの制約を書けない。
   型クラスは Type のクラスなので、行に要求しても満たす手段が無い。
   宣言の位置で拒否しないと、エイリアスでは使用点ごとに落ち、
   newtype では構築点が行を見ないので素通りする。
   カインドが決まった後(1b の後始末の 2 周目)に、宣言の位置で確かめる *)
let check_row_constraints (tparams : type_param list) (kinds : kind list) =
  if List.length tparams = List.length kinds then
    List.iter2
      (fun (tp : type_param) k ->
        match kind_repr k with
        | KRow when tp.tp_classes <> [] ->
            type_error
              ("型パラメータ " ^ tp.tp_name ^ " は行カインドなので、型クラス "
              ^ String.concat ", " (List.map show_long_id tp.tp_classes)
              ^ " の制約は書けません(型クラスは Type のクラス)")
        | _ -> ())
      tparams kinds

let process_decls env ~emit decls =
  let eff0 = toplevel_eff () in
  (* パス 1a: 型エイリアスの登録と newtype の頭(カインド) *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with
      | T.DType t ->
          register_companion t.T.ta_name;
          Decls.add_alias
            {
              Decls.al_name = intern t.T.ta_name;
              al_params = t.T.ta_params;
              (* パラメータのカインドのセル。F[_] と書いてあればその場で確定し、
                 それ以外は 1b の後始末が本体から推論する *)
              al_kinds =
                List.map
                  (fun (tp : type_param) -> if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var ())
                  t.T.ta_params;
              al_kind = t.T.ta_kind;
              al_body = t.T.ta_body;
              al_module = !Decls.current_module;
            }
      | T.DNewtype n ->
          (* 型の名前空間の主張はここ(宣言順)で行う。add_data も add_effect も 1b なので、
             種別の交差の検出を各 add に任せると、1a の add_alias が常に先回りし、後に
             書かれたエイリアスが、先に書かれた newtype を再宣言として逆向きに咎める *)
          Decls.claim_type_name "newtype" (intern n.T.nt_name);
          register_companion n.T.nt_name;
          if not (Decls.prelude_owned "data" (intern n.T.nt_name)) || !Decls.in_prelude then
            (* 頭のカインドは、パラメータごとにカインド変数を積む。1b の register_newtype が
               このセルを剥がして dd_params の vkind に据えるので、本体で決まったカインドが
               そのまま頭に反映される *)
            Hashtbl.replace Decls.con_kinds (intern n.T.nt_name)
              (List.fold_right
                 (fun (tp : type_param) acc -> KArrow ((if tp.tp_arity > 0 then k_arrow tp.tp_arity else new_kind_var ()), acc))
                 n.T.nt_params KStar)
      | T.DEffect e -> Decls.claim_type_name "effect" (intern e.T.ef_name)
      | _ -> ())
    decls;
  (* パス 1a の後始末: newtype の本体の投機。宣言順に依存せずにパラメータのカインドを
     決めるため、登録の前に本体を一度読んで捨てる *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with T.DNewtype n -> speculate_newtype env n | _ -> ())
    decls;
  (* パス 1b: newtype のコンストラクタ、effect、type class の登録(相互再帰と前方参照を許す) *)
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
            let methods = register_class env c in
            {
              env with
              values =
                (* 非修飾名は先勝ち(既存の束縛は上書きしない)。実行時は、プレリュードの
                   let / extern の再束縛が register_class_methods のラッパを版複製で覆う
                   ので、非修飾名の勝者は先にいた側になる。elab も同じ側を選ばないと、
                   型検査と実行が別の実体を選び、echo や println のようなプレリュードの
                   名前をクラスメソッドが乗っ取る。修飾名 Cls.m はクラスの所有なので、
                   常に登録する *)
                List.fold_left
                  (fun m (mn, ty) ->
                    let m = SMap.add (c.T.cls_name ^ "." ^ mn) ty m in
                    if SMap.mem mn m then m else SMap.add mn ty m)
                  env.values methods;
            }
        | _ -> env)
      env decls
  in
  (* 1b の後始末: クラスメソッドと newtype の型パラメータの制約に、未知のクラスや予約述語が
     無いかを確かめる。register_class / register_newtype は 1b で宣言順に走るので、そこで
     確かめると、後ろのクラスを制約に書いた形が落ちる。クラス表が出揃ったここで確かめれば、
     宣言順に依存しない *)
  List.iter
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      match d with
      | T.DClass c ->
          List.iter (fun (v : T.class_val) -> List.iter (fun tp -> ignore (class_names_of tp)) v.T.cv_tparams) c.T.cls_vals
      | T.DNewtype n -> List.iter (fun tp -> ignore (class_names_of tp)) n.T.nt_params
      (* DType もここで確かめる。プレリュード所有名の再宣言は add_alias が黙って捨てるので、
         パス 2 の make_rigids には AST が届かない。AST の側で確かめないと、
         type Unit[A: Bogus] = A が素通りする *)
      | T.DType t -> (
          List.iter (fun tp -> ignore (class_names_of tp)) t.T.ta_params;
          (* エイリアス本体のカインドの推論。ここで一度、本体を投機的に精緻化し、
             パラメータのカインドだけを決めて結果は捨てる。パス 2 の実在検査より前に
             行わないと、エイリアスを先に使う宣言があったときに、カインドが宣言順で変わる。
             診断は出さない。本物の検査は、パス 2 が同じ本体でやり直す。
             捕まえる例外は with 節に並べた 4 つだけで、Panic は捕まえない。
             本体が途中で落ちる宣言では、落ちた先の使われ方が推論に届かず Type に
             既定化されるが、そのプログラムはどのみちパス 2 の同じ箇所で落ちる。
             プレリュード所有名の再宣言では、表にプレリュードの本体が残っているので、
             読むのもそちら *)
          match Hashtbl.find_opt Decls.aliases (intern t.T.ta_name) with
          | None -> ()
          | Some info -> (
              try
                let rigids = make_rigids ~kinds:info.Decls.al_kinds 1 info.Decls.al_params in
                let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
                ignore
                  (match info.Decls.al_kind with
                  | Some "EffectRow" -> elab_eff env_ty 1 info.Decls.al_body
                  | _ -> elab_type env_ty 1 info.Decls.al_body)
              with Type_error _ | Type_error_at _ | NotImplemented _ | NotImplemented_at _ -> ()))
      | _ -> ())
    decls;
  (* 1b の後始末の 2 周目: カインドの既定化。1b がすべて終わってから既定化する。宣言ごとに
     既定化すると、相互参照する newtype の間で、カインド変数が早すぎる時点で KStar に固定される
     (same_kind は未解決どうしを片方に張る)。エイリアスの投機(1 周目)より後に置くのは、
     newtype のパラメータのカインドがエイリアス経由で決まる形(newtype A[X] = MkA(Cb[X]) と
     type Cb[E] = Callback[E])で、投機が届く前に X を固定しないため。頭と dd_params の
     両方を既定化するのは念のためで、セルを共有しているので、通常はどちらか一方で足りる *)
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
              check_row_constraints n.T.nt_params (List.map (fun (i : var_info) -> i.vkind) dd.Decls.dd_params)
          | None -> ())
      | T.DType t -> (
          match Hashtbl.find_opt Decls.aliases (intern t.T.ta_name) with
          | Some info ->
              List.iter default_kind info.Decls.al_kinds;
              check_row_constraints t.T.ta_params info.Decls.al_kinds
          | None -> ())
      | _ -> ())
    decls;
  (* パス 1c: インスタンスの頭の登録と、注釈が完全な let の署名の登録 *)
  let env =
    List.fold_left
      (fun env ((_, d) as node : T.decl) ->
        at_node node @@ fun () ->
        with_decl_module node @@ fun () ->
        match d with
        | T.DInstance i ->
            register_instance i;
            env
        | T.DLet (_, b) -> (
            (* 先勝ち: 既に環境にある名前(先行する 1c の署名、クラスメソッド、プレリュードの
               束縛)は上書きしない。実行時の版複製(§14.13)は、再束縛より前に作られた閉包に
               古い実体を見せるので、前方参照の勝者も、最初にその名前を持った側になる。
               後勝ちにすると、前方参照する関数だけ型検査と実行が別の実体を選び、同名の
               let 2 つと前方参照を含むプログラムが、黙って別の型の値を返す *)
            match (binding_name b, signature_of_binding env b) with
            | Some x, Some ty when not (SMap.mem x env.values) -> { env with values = SMap.add x ty env.values }
            | _ -> env)
        | T.DLetRec bs ->
            List.fold_left
              (fun env ((_, b) : T.let_binding) ->
                match (binding_name b, signature_of_binding env b) with
                | Some x, Some ty when not (SMap.mem x env.values) -> { env with values = SMap.add x ty env.values }
                | _ -> env)
              env bs
        | _ -> env)
      env decls
  in
  (* パス 2: 本体の推論(宣言順) *)
  let show_binding env ((_, b) : T.let_binding) =
    match binding_name b with Some x -> emit (Binding (x ^ " : " ^ Show.show (SMap.find x env.values))) | None -> ()
  in
(* ## 11.40 パス 2 の 1 歩

   `step` は宣言を 1 つ処理して、新しい環境を返す。

   `DLet` / `DLetRec` / `DExp` / `DInstance` では、既定化の直前に、宣言の終わりの曖昧性検査を行う。
   宣言の型から到達できない制約は、もう誰にも決められないからである。
   `DExp` も対象なので、文の位置に捨てられた式の制約も、曖昧として落ちる。
   `DType` / `DNewtype` / `DEffect` / `DClass` / `DExtern` では行わない。
   宣言の型に相当するものが無く、空の到達集合で掃くと偽陽性になるからである。

   宣言の種類ごとの処理は、次のとおりである。

   - `DType`：パス 1a で表に入っているので、ここでは検査のためだけに本体を精緻化し、結果を捨てる。
     未知の型、再帰、部分適用がこの時点で報告されるので、
     使われないエイリアスの誤りも黙って残らない。
   - `DLet` / `DLetRec`：本体を推論し、既定化してから型を印字する。
   - `DExp`：式を推論し、網羅性の警告を流してから型を印字する。
   - `DExtern`：署名だけを登録する。
     実装は第13章の表にある。
     引数パターン、エフェクト注釈、返り値注釈の扱いは束縛と同じで、本体が無いぶん短いだけである。
     同じ名前を 2 度 `extern` できないのは、
     後の宣言が既存の実装に嘘の型を被せられないようにするためである。
   - `DNewtype` / `DEffect` / `DClass`：パス 1 で済んでいる。
   - `DInstance`：本体を検査する(§11.38)。
   - `DModule`：ここには来ない。
     平坦化で消えている(§11.42)。

   警告は、この宣言で新しく増えたぶんだけを印字する。
   宣言と警告の対応が崩れないように、処理の前後で警告の個数を覚えておく。 *)

  let step env ((_, d) as node : T.decl) =
    let wbefore = !warnings_count in
    let env' =
      at_node node @@ fun () ->
      with_decl_module node @@ fun () ->
      let env' =
        match d with
      | T.DType t ->
          (* 実在検査(未知の型、再帰、部分適用)をここで走らせる。結果は捨てる *)
          let info = Hashtbl.find Decls.aliases (intern t.T.ta_name) in
          let lvl = 1 in
          let rigids = make_rigids ~kinds:info.Decls.al_kinds lvl info.Decls.al_params in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          ignore
            (match info.Decls.al_kind with
            | Some "EffectRow" -> elab_eff env_ty lvl info.Decls.al_body
            | _ -> elab_type env_ty lvl info.Decls.al_body);
          release_rigids rigids;
          env
      | T.DLet b ->
          let env' = elab_binding env 0 eff0 b in
          (* 宣言の終わりの曖昧性検査(all=true。宣言の型から到達できない制約は、誰にも
             決められない)。既定化の直前に行う。逆の順だと、述語つきの変数が先に消えて
             免除の判定が要らなくなる代わりに、Eq / Show だけが乗った変数の検出が遅れる *)
          Unify.check_ambiguity ~all:true ~level:0 [ Tree.get_ty b ];
          Unify.default_numerics () (* 印字の前に、述語つきの弱い変数を既定化する *);
          show_binding env' b;
          env'
      | T.DLetRec bs ->
          let env' = elab_rec_bindings env 0 eff0 bs in
          Unify.check_ambiguity ~all:true ~level:0 (List.map Tree.get_ty bs);
          Unify.default_numerics ();
          List.iter (show_binding env') bs;
          env'
      | T.DExp e ->
          let t = elab_exp env 0 eff0 e in
          List.iter warn (Exhaust.drain ());
          (* 文の位置の式も検査する。捨てられる値の制約は、誰にも決められない *)
          Unify.check_ambiguity ~all:true ~level:0 [ t ];
          Unify.default_numerics ();
          emit (Binding ("_ : " ^ Show.show t));
          env
      | T.DExtern ex ->
          (* extern 宣言は署名だけ(実装は builtin.ml の表)。重複とプレリュード保護を確かめる *)
          if ex.T.ex_abi <> "prim" && ex.T.ex_abi <> "C" then
            type_error ("未知の extern リンケージ: " ^ ex.T.ex_abi ^ "(prim か C を指定してください)");
          (* pub の完全注釈検査。let の側(§11.28)と同じ規則 *)
          (if ex.T.ex_pub then check_pub_annots ~value_head_outer:true ~params:(Some ex.T.ex_params) ~ret:ex.T.ex_ret);
          (* プレリュード保護は実装名(非修飾)で、二重宣言の検査は修飾名で行う(§6.2) *)
          Decls.add_extern ~prim:ex.T.ex_prim ex.T.ex_name;
          let lvl = 1 in
          let rigids = make_rigids lvl ex.T.ex_tparams in
          let env_ty = { env with types = List.fold_left (fun m (n, ty, _) -> SMap.add n ty m) env.types rigids } in
          let seen = ref [] in
          let param_tys = List.map (fun _ -> new_var lvl) ex.T.ex_params in
          ignore (List.fold_left2 (fun env p t -> elab_pat env lvl seen t p) env_ty ex.T.ex_params param_tys);
          let fn_eff, eff_rigids =
            match ex.T.ex_eff with Some e -> open_explicit_eff lvl (elab_eff env_ty lvl e) | None -> (new_row_var lvl, [])
          in
          let ret_ty = match ex.T.ex_ret with Some t -> elab_value_type env_ty lvl "返り値の型注釈" t | None -> new_var lvl in
          (* C の既知名は、型の契約を照合する(第6章 §6.2b)。行は照合しない。
             @ Blocking を付けるかは、バインディングを書く側の判断である(sample.kel:794) *)
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
          release_rigids (rigids @ eff_rigids);
          emit (Binding (ex.T.ex_name ^ " : " ^ Show.show ty));
          { env with values = SMap.add ex.T.ex_name ty env.values }
      | T.DNewtype _ -> env (* パス 1 で登録済み。フィールド型の検査も登録時に済んでいる *)
      | T.DEffect _ -> env (* パス 1 で登録済み *)
      | T.DClass _ -> env (* パス 1 で登録済み *)
      | T.DInstance i ->
          check_instance_bodies env i;
          (* インスタンス本体にも、宣言の終わりの曖昧性検査を掛ける。値制限で一般化されない
             本体の let は all=false の検査(gen のガード)を通らないので、ここで掛けないと、
             曖昧な制約が台帳ごと捨てられる。到達集合は、各メソッドの束縛の型 *)
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
          (* 平坦化を通っていれば到達しない。来たら不変条件の違反で、処理系の欠陥である *)
          bug "module が平坦化されていません(flatten_modules を先に呼んでください)"
      in
      (* 既定化も宣言の包みの中で走らせる。DInstance の本体で作られた数値リテラルの述語は、
         ここで初めて落ちることがある。包みの外で走らせると、位置なしの型エラーになる *)
      Unify.default_numerics ();
      env'
    in
    (* この宣言が出した警告だけを拾う。warnings は逆順に積んであるので、先頭の n 個を
       反転して出す。全体を数え直す O(総警告数) の走査を、宣言ごとに繰り返さない *)
    let fresh = !warnings_count - wbefore in
    let rec take n l = if n = 0 then [] else match l with [] -> [] | x :: tl -> x :: take (n - 1) tl in
    List.iter (fun w -> emit (Warning w)) (List.rev (take fresh !warnings));
    env'
  in
  (* パス 1 で溜まった制約つき変数(インスタンスの頭や署名の instantiate)は、宣言ごとの
     曖昧性の判定に関係しない。台帳だけを空にしてから畳み込む *)
  Unify.reset ();
  List.fold_left step env decls

(* ## 11.41 型検査の入口

   プレリュード(第15章)を先に処理してから、利用者の宣言列を処理する。
   プレリュードの出力は捨て、環境だけを引き継ぐ。

   `Decls.in_prelude` を立てる処理は、`Fun.protect` で囲む。
   プレリュードの処理中に型エラーが飛んでも、フラグが立ったままにならないようにするためである。
   立ったままになると、以降の利用者の宣言がプレリュードとして扱われ、再宣言の保護をすり抜ける。 *)

let type_check_decls ?(prelude = []) decls =
  warnings := [];
  warnings_count := 0;
  Unify.reset ();
  Exhaust.reset ();
  Hashtbl.reset pub_pure_rows;
  let out = current_out in
  out := [];
  (* 先頭に積んで最後に反転する。末尾に @ で連結すると、宣言数の二乗の時間がかかる *)
  let emit s = out := s :: !out in
  let env0 = initial_env () in
  Decls.in_prelude := true;
  let env =
    Fun.protect
      ~finally:(fun () -> Decls.in_prelude := false)
      (fun () -> process_decls env0 ~emit:(fun _ -> ()) prelude)
  in
  let _env = process_decls env ~emit decls in
  List.rev !out

(* ## 11.42 module の平坦化

   Diktor の module は、名前空間ではなく**改名の規則**である。
   宣言列を精緻化に渡す前に平坦化し、以降のパスは module の入れ子を扱わない。
   ただし、各宣言の出身 module は `Decls.decl_module` に記録してあり、`process_decls` のパスは、
   `with_decl_module` で `current_module` を立てて宣言を処理する。
   平坦化は宣言の名前を改名するだけで、
   本体の中の参照は走査も改名もしない(本体の参照は同義語表で解決する)。
   そのため、束縛子を見落として誤って改名する、という種類の誤りは起きない。

   - `newtype` / `type`：`M.名前` に改名して登録し、
     module スコープの同義語 `(M, 非修飾名) → M.名前` を張る。
     大域に張るのは、コンパニオン(module 名と同名の型。sample.kel:838)だけである。
     すべての同義語を大域に張ると、`module M { newtype List[A] = … }` と書くだけで、
     プレリュード自身の型検査が壊れる。
   - `let`：`M.名前` に改名し、module スコープの値の同義語を張る。
     module 内の相互参照と `let rec` の自己再帰は、
     フォールバック(環境に無かったときだけスコープの同義語を引く)で通る。
     module 内の値の名前が、トップレベルの値の名前と同じになることは禁止する。
     elab は宣言時点の環境を、評価器は呼び出し時点の環境を見るので、同名を許すと、
     フォールバックが働くかどうかが両者で食い違い、黙って別の実体を選ぶ。
     この禁止が、2 つの名前解決が一致するための前提である。
   - `pub`：可視性の台帳(第6章の `value_visibility` / `con_visibility`)へ写す。
     検査は使用点(§11.3 / §11.11 / §11.8)で行い、可視性の境界は module だけである。
     コンストラクタは、所属する newtype の `pub` に従う。
   - `instance`：そのまま大域に出す。
     インスタンスは常に大域から見え、import で見え方が変わるものではない(sample.kel:833)。
   - `extern`：`ex_name` を `M.f` に修飾するが、実装名 `ex_prim` は元のままにする(第1章)。
     実装は処理系の側の表にあり、module はその表を切り分けない。
     第6章の登録簿は、プレリュード保護を `ex_prim` で、二重宣言の検査を修飾名で見る(§6.2)。
     修飾名だけを鍵にすると、保護を module の中から迂回でき、実装名だけを鍵にすると、
     別々の module が同じ C シンボルを包めなくなる。

   同義語表は実行時にも使う。
   評価器が同義語表を引かないと、module の中の instance が実行時に見つからない。
   型検査が使う名前解決の経路は、評価器も同じものを通る必要がある。
   評価器の側で `current_module` にあたるのは環境の `mod_scope` で、
   module の中で作られた閉包が出身を持ち歩く(§14.13)。

   入れ子の module と、module の中の effect / class / 式は未対応である。
   受理してから落とすのではなく、平坦化の時点で報告し、種別は**未実装**(終了コード 4)とする。
   module の中の `let` のパターン束縛だけは、未対応ではなく仕様上の制限なので、
   型エラー(終了コード 1)にする。

   ### 組み込みが置いた綴りは奪えない

   平坦化が作る修飾名 `M.x` は、module ごとの名前空間ではなく、大域の値の名前空間に入る。
   そのため、組み込みが既にそこへ置いている綴りを module 宣言で作れてしまうと、
   覆われた側の署名ごと値環境から消える。
   そうした綴りには、`Ref.new` / `Array.get` / `MutableArray.set` のような組み込みの操作(§6.11)と、
   `Show.show` のようなクラスメソッドの修飾名(§6.13)がある。
   消えたことは、使用点まで分からない。
   宣言の位置で検査しないと、たとえば `module MutableArray { pub let set … }` を置いたプログラムは、
   宣言から離れた使用点で落ちる。
   そのときの診断は「MutableArray は Integral のインスタンスではありません」のように、
   原因と関係のない語を使う。
   `claim_val` の 3 番目の分岐が、これを宣言の位置で落とす。
   名簿は第6章の `builtin_values` 1 つで、ここが引くのは問い合わせ口の `is_builtin_value` である。

   この検査は、予約型名を `newtype` で奪えない(§6.6)のと同じ規律に従う。
   ただし、module 名そのものは予約しない。
   `module Array { pub let sum(…) }` は通る。
   型名は型そのものだが、module 名は修飾名の接頭辞にすぎないので、同じ強さで閉じる根拠が無い。
   守るのは、組み込みが既に置いている綴りだけである。
   該当するのは 11 件で、`Ref` の 3 操作、`Array` の 3 操作、`MutableArray` の 5 操作である。
   クラスメソッドの修飾名 10 件には、この分岐は効かない。
   `flatten_modules` の `class_methods` は `Decls.classes` から種を取るので組み込みのクラスも含み、
   2 番目の分岐が先に拾うからである。
   その診断の文言は、`test/visibility.t` の visc が固定している。

   非修飾の組み込みの値は守らず、トップレベルの `let` が黙って覆える。
   該当するのは、`par` / `par_map` / `pinned`(§6.11b)と、
   `show` / `add` などのクラスメソッドの非修飾名である。
   これらは利用者のトップレベルの名前と同じ名前空間を共有しており、覆えないようにするには、
   値の名前は大域で先勝ち、という枠組みごと見直す必要がある。
   たとえば `let pinned[A](f: A): Int32 = 0` と書くと、
   `Blocking` を行から取り除く組み込みの `pinned` の型が見えなくなる。

   3 番目の分岐には `in_prelude` を見る条件がある。
   しかし平坦化は `in_prelude` が立つ前に走る(第16章)ので、
   この条件がプレリュードを免除する経路は無い。
   `--prelude` で差し替えたプレリュードも、
   利用者のプログラムと同じように拒否される(`test/visibility.t` の visbipre)。
   `module` を含まない同梱のプレリュードでは、この条件が効かないことを観測できない。
   組み込みの操作をプレリュードのソースへ移す場合は、
   この条件を効かせる場所(平坦化を呼ぶ第16章の側)を先に決める必要がある。 *)

let flatten_modules (decls : T.decl list) : T.decl list =
  (* トップレベル(module の外)の値の名前を先に集める。module 内の値の名前がこれと同名に
     なるのを禁止するため(§6.4)。禁止しないと、宣言順と呼び出し時刻の組み合わせで、
     elab と評価器のフォールバックが働くかどうかが食い違い、黙って別の実体を選ぶ。
     パターン束縛の束縛子もすべて拾う。binding_name(PVar だけ)で集めると、
     let (a, b) = … の a が検査をすり抜け、同じ食い違いが起きる *)
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
  (* トップレベルの型名と、クラスのメソッド名も集める。コンパニオン型の大域の同義語が既存の
     型名を黙って乗っ取る形(module Foo を 1 行足すだけで newtype Foo の名目型が破れる)と、
     module 名がクラス名と同じときに、修飾名 M.f がクラスメソッドの修飾名と衝突して値環境で
     区別できなくなる形を、どちらも平坦化の時点で拒否するため *)
  let toplevel_types = Hashtbl.create 16 in
  let class_methods : (string, string list) Hashtbl.t = Hashtbl.create 16 in
  Hashtbl.iter
    (fun cname (ci : Decls.class_info) -> Hashtbl.replace class_methods (Type.name_of cname) (List.map fst ci.Decls.ci_methods))
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
  List.concat_map
    (fun ((_, d) as node : T.decl) ->
      at_node node @@ fun () ->
      match d with
      | T.DModule (_, mname, body) ->
          List.concat_map
            (fun ((bdata, bd) as bnode : T.decl) ->
              at_node bnode @@ fun () ->
              let claim_val x =
                if Hashtbl.mem toplevel_vals x then
                  type_error
                    ("module " ^ mname ^ " の " ^ x ^ " はトップレベルの " ^ x
                   ^ " と同名です(module 内の名前とトップレベル名は同名にできません)")
                else if match Hashtbl.find_opt class_methods mname with Some ms -> List.mem x ms | None -> false then
                  (* 修飾名 M.x が、クラス M のメソッド x の修飾名と同じ綴りになり、
                     値環境で区別できない *)
                  type_error
                    ("module " ^ mname ^ " の " ^ x ^ " は型クラス " ^ mname ^ " のメソッド " ^ x
                   ^ " と修飾名が衝突します(module か メソッドを改名してください)")
                else if (not !Decls.in_prelude) && Decls.is_builtin_value (mname ^ "." ^ x) then
                  (* 組み込みの修飾名(Ref.new / MutableArray.set など)は奪えない。
                     予約型名を newtype で奪えない(§6.6)のと同じ規律で、黙って覆うと、
                     組み込みの署名ごと消える *)
                  type_error
                    ("module " ^ mname ^ " の " ^ x ^ " は組み込みの " ^ mname ^ "." ^ x
                   ^ " と同名です(組み込みの名前は宣言できません)")
                else Decls.(Hashtbl.replace module_val_synonyms (mname, intern x) (intern (mname ^ "." ^ x)));
                Decls.add_val_synonym (intern x) (intern (mname ^ "." ^ x))
              in
              let claim_con name pub =
                let qual = mname ^ "." ^ name in
                Decls.(Hashtbl.replace module_con_synonyms (mname, intern name) (intern qual));
                Decls.add_con_hint (intern name) (intern qual);
                (* コンパニオン(module 名と同名の型)とトップレベルの型名の衝突は、ここで
                   拒否する。黙って許すと、module Foo を 1 行足すだけでトップレベルの型 Foo が
                   乗っ取られ、名目型の抽象が破れる。プレリュードの名前との衝突の検査と、
                   大域の同義語の登録はパス 1a(§11.39)で行う。プレリュードの宣言表は
                   平坦化の時点ではまだ空だからである。可視性は pub をそのまま写す *)
                if name = mname && (Hashtbl.mem toplevel_types name || Hashtbl.mem Decls.reserved_type_names (intern name))
                then
                  type_error
                    ("module " ^ mname ^ " のコンパニオン型 " ^ name ^ " は既存の型 " ^ name
                   ^ " と同名です(module 内の型とトップレベルの型は同名にできません)");
                Hashtbl.replace Decls.con_visibility (intern qual) { Decls.vis_module = mname; vis_pub = pub };
                qual
              in
              let record_module (data, d') =
                Hashtbl.replace Decls.decl_module (Tree.oid_of (data, d')) mname;
                (data, d')
              in
              let vis x pub =
                Hashtbl.replace Decls.value_visibility (intern (mname ^ "." ^ x)) { Decls.vis_module = mname; vis_pub = pub }
              in
              match bd with
              | T.DNewtype n ->
                  let qual = claim_con n.T.nt_name n.T.nt_pub in
                  [ record_module (bdata, T.DNewtype { n with T.nt_name = qual }) ]
              | T.DType t ->
                  let qual = claim_con t.T.ta_name t.T.ta_pub in
                  [ record_module (bdata, T.DType { t with T.ta_name = qual }) ]
              | T.DLet ((bd2, b) as _bnode2) -> (
                  match snd b.T.lb_name with
                  | T.PVar x ->
                      claim_val x;
                      vis x b.T.lb_pub;
                      [ record_module (bdata, T.DLet (bd2, { b with T.lb_name = (fst b.T.lb_name, T.PVar (mname ^ "." ^ x)) })) ]
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
                                   ((bd2, { b with T.lb_name = (fst b.T.lb_name, T.PVar (mname ^ "." ^ x)) }) : T.let_binding)
                               | _ -> type_error "module 内の let rec はパターン束縛にできません")
                             bs) );
                  ]
              | T.DInstance _ -> [ record_module (bdata, bd) ]
              | T.DExtern ex ->
                  claim_val ex.T.ex_name;
                  vis ex.T.ex_name ex.T.ex_pub;
                  [ record_module (bdata, T.DExtern { ex with T.ex_name = mname ^ "." ^ ex.T.ex_name }) ]
              | T.DModule _ -> noimpl "module の入れ子(M10)"
              | T.DEffect _ -> noimpl ("module 内の effect 宣言(M10): module " ^ mname)
              | T.DClass _ -> noimpl ("module 内の type class 宣言(M10): module " ^ mname)
              | T.DExp _ -> noimpl ("module 内の式文(M10): module " ^ mname))
            body
      | _ -> [ node ])
    decls

(* ## 11.43 最初の 1 つで打ち切る

   型エラーは最初の 1 つで打ち切る。
   エラー回復を実装していないので、2 つ目以降のエラーは 1 つ目の影響を受けた誤ったものになりやすく、
   並べても読み手の役に立たない。
   ただし、そこまでに確定した出力行は返す。
   そこまでの型が見えれば、どこまで通ってどこで止まったかが分かる。

   型エラーの位置は、そのエラーを投げた**最内**の精緻化ノードの開始位置である。
   `at_node` は位置なしの `Type_error` と `NotImplemented` にだけ span を貼り
   (それぞれ `Type_error_at` / `NotImplemented_at` にする)、位置つきの例外は素通りさせる。
   この 1 つの規則で、外側の包みが内側の位置を上書きしない。
   `at_node` が包むのは、`elab_exp`、`elab_check`、`elab_pat`、`elab_type`、`elab_eff`、
   `elab_value_type`、`elab_binding`、`elab_rec_bindings`、`check_resume_static` と、
   newtype のフィールドのカインド検査、インスタンス本体のメソッドごとの包摂、
   `process_decls` の各パスと後始末のループ、`flatten_modules` の宣言の単位である。
   宣言の単位の包みが最後の受け手なので、どのエラーにも、少なくともその宣言の先頭の位置が付く。

   例外を型付きの返り値に変えるのは、下の `type_check` の 1 か所だけである。
   受けるのは 2 系統だけで、`Type_error` / `Type_error_at` は終了コード 1、
   `NotImplemented` / `NotImplemented_at` は終了コード 4 になる。
   `Syntax_error` の節は置かない。
   `Syntax_error` を投げるのは parser.mly だけで、
   第16章の `parse_with` がそれをすべて `Parse_error` に包み直してから型検査に入るからである。
   診断は `error` レコード(位置、種別の語、終了コード、本文)として返す。
   そこから先の整形と印字は、第16章(driver.ml)が行う。

   ## この章が守っている不変条件

   本章が守る不変条件を、5 つ挙げる。

   1. **`eff` は下向き、`level` は引数。**
      どちらも大域状態にしない。
      そのため、レベルを戻し忘れるという誤りが起きない。
   2. **一般化してよいのは、関数か構文的な値のときだけ。**
      注釈は一般化の理由にならない(§11.28)。
   3. **網羅性検査は、一般化より前に流し切る。**
      一般化のあとでは、閉じるべき行がもう凍っている(§11.14)。
   4. **剛定数は、作ったスコープの中でだけ硬い。**
      出口で `Generic` に変える前に、漏れは `unify` が捕まえている(§11.27)。
   5. **解決した名前は木に書く。**
      コンストラクタの並べ替え、操作の完全名、節の種別を木に書き、
      評価器に同じ計算をさせない(§11.8、§11.18、§11.22)。

   第12章からは実行時を扱う。
   本章が木に書き込んだ型と解決結果を、第14章の評価器がそのまま読む。 *)

(* 診断 1 つ。位置、種別の語、終了コード、本文を値で持つ。
   表示の整形は第16章が受け持つ。
   e_loc には、at_node が Type_error_at / NotImplemented_at に貼った位置が入る
   (包みの外で投げられた例外では None) *)
type error = { e_loc : Location.span option; e_word : string; e_exit : int; e_msg : string }

let type_check ?(prelude = []) decls =
  current_out := [];
  try (type_check_decls ~prelude decls, None) with
  | Type_error_at (loc, msg) -> (List.rev !current_out, Some { e_loc = Some loc; e_word = "型エラー"; e_exit = 1; e_msg = msg })
  | Type_error msg -> (List.rev !current_out, Some { e_loc = None; e_word = "型エラー"; e_exit = 1; e_msg = msg })
  (* Syntax_error の節は置かない。投げるのは parser.mly だけで、第16章の parse_with が
     すべて Parse_error に包み直してから型検査に入る。届く例外は、Type_error と、未実装の
     NotImplemented の 2 系統だけ *)
  | NotImplemented_at (loc, feat) -> (List.rev !current_out, Some { e_loc = Some loc; e_word = "未実装"; e_exit = 4; e_msg = feat })
  | NotImplemented feat -> (List.rev !current_out, Some { e_loc = None; e_word = "未実装"; e_exit = 4; e_msg = feat })
