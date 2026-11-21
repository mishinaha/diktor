(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第9章 型の表示

   型検査器がユーザに見せるものは 2 種類ある。
   検査に通ったときの `name : type` の一覧と、通らなかったときのエラーメッセージである。
   どちらも型を文字列にしなければ書けないので、
   型検査器の出力のほとんどは本章のプリティプリンタを通る。

   本章の役目は、型を内部表現ではなく Keleut の表層構文で見せることである。
   第1章(syntax.ml)の `ty` は、行と `_item` ラベルで統一した内部表現で、ユーザが書く形とは違う。
   ユーザが書くのは `(Int32, String) => Boolean` であって、
   `TArrow (TRecord (TRowExtend (_item, ...)), ...)` ではない。

   表示の方針は次のとおりである。

   1. `Generic` は `A, B, C…`、`Unbound` は `_A, _B…`、
      `Rigid`(スコーレム定数。§9.2)は `ς1, ς2…` と書く
   2. カインドごとに名前のプールを変える(`Type` は `A..E`、`F[_]` は `F..H`)。
      リージョンの位置に現れる変数は `h, h1…` と書く
   3. 矢印のエフェクト行が行変数だけのときは、`@` ごと省く。
      閉じた空の行は `@ {}` と書く(§9.6)
   4. エフェクトラベルの引数がユニットなら、ラベル名だけを書く
   5. 制約の付いた変数があれば、その制約を型の前に角括弧で書く(§9.7)

   さらに、記号は表層構文に合わせる。
   矢印は `=>`、エフェクトは `@`、型引数は角括弧、開いた行の末尾は `extends` で書く。

   Keleut はタプルを `_item` ラベルの行の糖衣構文として表し、
   型にも構文木にも値にもタプル専用の表現を持たない。
   そこで、表示するときに `(A, B)` の表記へ戻す(§9.3)。

   本章は第8章(unify.ml)の `is_predicate` を使う。

   本章の表示関数をほかの章が使う経路は 2 つある。
   1 つは関数を直接呼ぶ経路で、第11章(elab.ml)が束縛ごとに `Show.show` を呼び、
   `--type-check` を指定したときに出力する `name : type` の行を作る。
   `test/typecheck*.t` の期待出力は、この行を並べたものである。
   もう 1 つは、ファイル末尾で `show`、`show2`、`show_pair` を、
   `Unify.show_ref`、`Unify.show2_ref`、`Unify.show_pair_ref` に代入する経路で、
   第8章のエラーメッセージはこの経路で型を表示する。 *)

open Aux
open Syntax
open Type

(* ## 9.1 複数の型をまとめて表示する show_all

   単一化が失敗したときに出したいのは、
   「型が一致しません: `(A) => A` と `(B) => Int32`」というメッセージである。
   型を 1 つずつ独立に文字列にすると、どちらの型でも最初に採番した変数が `A` になり、
   「型が一致しません: `(A) => A` と `(A) => Int32`」になってしまう。
   これでは、ユーザには何が起きたのか分からない。

   そこで本体は複数の型をまとめて受け取る `show_all` とし、
   採番表(`names`)と制約の一覧(`constrained`)を型のあいだで共有する。
   `show` は 1 要素のリストを、`show2` と `show_pair` は 2 要素のリストを `show_all` に渡す薄いラッパである。

   採番表のキーは `vid`(第1章の oid)である。
   同じ変数は何度現れても同じ名前になり、違う変数は必ず違う名前になる。

   ### 名前のプール

   カインドごとにプールを分けるのは、読みやすさのためである。
   `[F: Functor] (F[A]) => F[B]` を見れば、`F` が型構成子で、`A` と `B` が型だとすぐに分かる。
   すべてを `A B C` から採ると `(A[B]) => A[C]` になり、`A` が何なのかを考えないと分からない。
   行変数だけは `R1, R2` と連番にする。
   行はプールを使い切りやすく、`R` の連番なら何番目の行変数かがそのまま読めるからである。

   `pick` はプールを使い切ると、名前に番号を付ける(`A, B, …, E, A1, B1, …`)。

   ### リージョンの名前

   リージョン変数のカインドは値の型と同じ `Type` である(第6章 §6.11)。
   カインドだけで名前を選ぶと、
   `let use[h, A](r: Ref[h, A]): A @ Heap[h] = Ref.get(r)` の型は `(Ref[A, B]) => B @ {Heap[A]}` と表示され、
   どれがリージョンでどれが値の型かを、ユーザは `Ref` の引数の順から思い出さなければならない。
   そこで、`Ref` と `MutableArray` の第 1 引数か、エフェクト行の `Heap` ラベルの引数に現れる変数は、
   `Type` のプールではなく `h` のプールから名前を採る。
   1 個目は `h`、2 個目以降は `h1, h2…` で、`(Ref[h, A]) => A @ {Heap[h]}` のように、
   仕様のシグネチャ一覧と同じ表記になる。
   弱い変数(一般化されていない `Unbound` の変数)には、
   ほかの変数と同じく名前の前に下線を付ける(`_h`)。
   スコーレム定数は §9.2 のとおり `ς` で書き、このプールを使わない。

   構造的ヴァリアントのコンストラクタ `#Heap` のラベルも `eff_heap` と同じ名前になるが、
   その引数は値の型である。
   そこで `collect` は、`TRecord` か `TVariant` の直下の行を走査するときに `structural` を真にし、
   `structural` が真の行では、`Heap` ラベルの引数をリージョンの位置に数えない。
   `structural` の値は行の残りへ引き継ぎ、フィールドの型の中へは引き継がない。

   変数がリージョンかどうかは、表示の前に型を走査して、リージョンの位置に現れたかどうかで決める。
   型の表現には、リージョンを区別する情報がないからである。
   同じ変数が値の型の位置にも現れるとき(`(h, Ref[h, Int32]) => Int32`)も、リージョンの名前を使う。
   1 か所でもリージョンの位置に現れた変数は、型検査の上ではリージョンとして使われている。
   リージョンの位置に現れたかどうかは、採番表と同じく、`show_all` に渡したすべての型を通して調べる。
   型構成子が `Ref` か `MutableArray` か、ラベルが `Heap` かは、
   それぞれの名前を `intern` で引いた値(`ty_ref`、`ty_mutable_array`、`eff_heap`)と比べて判定する。
   そのため、module の中で同名の型を宣言しても、その型の引数はリージョンとして扱わない。
   ユーザの newtype の型引数も、リージョンを包んでいるかどうかを問わず、
   リージョンの位置として扱わない。
   `newtype Box[k] = Box(Ref[k, Int32])` の `k` は、
   同じ `show_all` の呼び出しの中で `Ref[k, Int32]` のようにリージョンの位置にも現れれば `h` と書き、
   `Box[k]` の引数としてだけ現れれば `Type` のプールの名前(`A` など)で書く。

   ### 弱い変数の下線

   `Unbound` の変数には、名前の前に `_` を付ける。
   OCaml の `'_weak1` と同じく、値制限で一般化されなかった変数であることがすぐに分かる。
   `let r = Ref.new(0)` のような束縛の型に `_A` が出ていたら、
   その型はまだ決まっていないが、決まったら 1 つに固定される、という意味である。
   逆に、弱い変数であるべき変数が下線なしで出ていたら、過剰な一般化を疑える。

   ### 制約の一覧

   `record_cs` は名前を返すときに、その変数の制約を一覧に追加する。
   このとき、予約述語 `Integral` / `Fractional` は取り除き、一覧に入れない。
   通常は既定化(defaulting。第8章(unify.ml)の §8.9)が一般化より先に行われるので、
   予約述語の付いた変数が表示されることはない。
   しかしエラーの経路では、既定化の前の型を表示することがある。
   その型を `[A: Integral] A` のように表示すると、制約に書けないクラス名をユーザに見せることになる。

   一覧も採番表も、`show_all` を呼ぶたびに作り直す。
   表示の途中で単一化は実行されないので、同じ変数に表示の途中で制約が加わることはない。
   `List.mem_assoc` の検査は同じ変数を 2 度入れないためのもので、
   先に入れた値を守るためのものではない。

   一覧を `list ref` にして `@` で末尾に追加するのは、出現順を保つためである。
   `Hashtbl` にすると `[B: Eq, A: Add]` のように型の中の順序と逆に出ることがあり、
   ユーザが型と見比べにくくなる。
   型は短いので、線形探索のコストは問題にならない。 *)

(* 名前(oid)から、それを宣言したファイルの表示用のパスを求める関数を持つ。
   第11章(elab.ml)が、第6章(decls.ml)の単位の表を引く関数を代入する *)
let unit_label : (oid -> string) ref = ref (fun _ -> "?")

let show_all ts =
  (* 表示名が同じで宣言が別のもの(別々のファイルの同名の型やエフェクト)が 1 回の show_all に並ぶときだけ、
     その名前にファイルを添えて T(lib/a.kel) と書く。それ以外は表示名だけを書く *)
  let seen : (string, oid list) Hashtbl.t = Hashtbl.create 16 in
  let note n =
    let d = display_of n in
    let prev = Option.value ~default:[] (Hashtbl.find_opt seen d) in
    if not (List.mem n prev) then Hashtbl.replace seen d (n :: prev)
  in
  let regions : (oid, unit) Hashtbl.t = Hashtbl.create 8 in
  let region t =
    match repr t with TVar { contents = Unbound i | Generic i } -> Hashtbl.replace regions i.vid () | _ -> ()
  in
  (* structural は、現在走査している行がレコードかヴァリアントの行であることを表す。
     ヴァリアントのコンストラクタ #Heap のラベルも eff_heap と同じ名前なので、
     Heap ラベルの引数をリージョンとして数えるのはそれ以外の行に限る *)
  let rec collect t = collect_in ~structural:false t
  and collect_in ~structural t =
    match repr t with
    | TCon (n, args) ->
        note n;
        (match args with r :: _ when n = ty_ref || n = ty_mutable_array -> region r | _ -> ());
        List.iter collect args
    | TApp (f, a) ->
        collect f;
        collect a
    | TArrow (p, r, e) ->
        collect p;
        collect r;
        collect e
    | TRecord row | TVariant row -> collect_in ~structural:true row
    | TRowExtend (l, f, rest) ->
        note l;
        if l = eff_heap && not structural then region f;
        collect f;
        collect_in ~structural rest
    | TRowEmpty | TVar _ -> ()
  in
  List.iter collect ts;
  let con_name n =
    match Hashtbl.find_opt seen (display_of n) with
    | Some (_ :: _ :: _) -> display_of n ^ "(" ^ !unit_label n ^ ")"
    | _ -> display_of n
  in
  let names : (oid, string) Hashtbl.t = Hashtbl.create 16 in
  let constrained : (string * cls) list ref = ref [] in
  let star_pool = "ABCDE" in
  let arrow_pool = "FGH" in
  let star_count = ref 0 in
  let region_count = ref 0 in
  let arrow_count = ref 0 in
  let row_count = ref 0 in
  let rigid_count = ref 0 in
  let pick pool i =
    String.make 1 pool.[i mod String.length pool] ^ if i >= String.length pool then string_of_int (i / String.length pool) else ""
  in
  let record_cs name cs =
    let cs = List.filter (fun c -> not (Unify.is_predicate c)) cs in
    (* 同じクラスの重複は、出現順を保ったまま取り除く。add_class も追加するときに
       List.mem で重複を防ぐが、表示する側でも取り除いておく *)
    let cs = List.fold_left (fun acc c -> if List.mem c acc then acc else acc @ [ c ]) [] cs in
    if cs <> [] && not (List.mem_assoc name !constrained) then constrained := !constrained @ [ (name, cs) ];
    name
  in
  let name_of_var i ~generic =
    let n =
      match Hashtbl.find_opt names i.vid with
      | Some n -> n
      | None ->
          let base =
            match kind_repr i.vkind with
            | KRow ->
                incr row_count;
                "R" ^ string_of_int !row_count
            | KArrow _ ->
                let n = !arrow_count in
                incr arrow_count;
                pick arrow_pool n
            | _ when Hashtbl.mem regions i.vid ->
                let n = !region_count in
                incr region_count;
                pick "h" n
            | _ ->
                let n = !star_count in
                incr star_count;
                pick star_pool n
          in
          let base = if generic then base else "_" ^ base in
          Hashtbl.add names i.vid base;
          base
    in
    record_cs n i.vcls
  in

  (* 採番は副作用なので、リストの要素に関数を適用する順序も固定する(§9.4)。
     標準ライブラリの List.map は現在の実装では先頭から適用するが、その順序は
     保証されていない。List.fold_left の適用順は標準ライブラリの文書が明記している *)
  let map_ordered f xs = List.rev (List.fold_left (fun acc x -> f x :: acc) [] xs) in

(* ## 9.2 スコーレム定数は ς で書く

   スコーレム定数は、注釈の型パラメータや `run` のリージョン変数を、
   そのスコープの中で固定した定数として表すもので、コードでは `Rigid` である。
   `Rigid` にだけ別のプールを与え、`ς1` `ς2` と番号を振る。
   ギリシャ文字を使うのは、ユーザが書ける型ではないことを示すためである。
   `A` や `_A` はまだ決まっていない型を表すが、
   `ς1` は決まっていて、しかも導入したスコープの外には存在しない型を表す。
   意味が正反対なので、見た目も変えておく。

   `ς` が画面に出る典型的な場合は 2 つある。
   1 つは `run` のリージョンから `Ref` を持ち出そうとしたとき(§8.3 の脱出検査)で、
   もう 1 つは本体が注釈の型パラメータより具体的すぎたとき(スコーレム化の検査)である。
   どちらのエラーも、ユーザが `A` と書いたその `A` が、
   その位置では任意の型になれないことを指摘する。
   `ς` と表示することで、その `A` が固定された型であることを示す。

   スコーレム定数の制約は、制約の一覧に入れない。
   §9.7 の角括弧は、ユーザがそのまま束縛子へ書き写せる形式である。
   スコーレム定数の制約を入れると `[ς1: Add] ς1` と表示され、そこに書き写せない名前が混ざる。
   スコーレム定数に制約が足りないときは、
   それを報告するエラーメッセージ自身が、`[A: Add]` のように制約を書くよう案内する(§8.4)。
   同じ情報を、書き写せない形式でもう一度見せることはしない。

   なお、`name_of_var` は、カインドが未確定(`KVar`)の変数を、
   `kind_repr` による場合分けの `KRow` でも `KArrow` でもない分岐で、`Type` の変数と同じように扱う。
   カインドが未確定のまま表示される変数のカインドは、
   後で既定の `KStar` に決まる(第1章の `default_kind`。時期は §1.6)。
   そこで、先回りして `Type` のプールから名前を採る。
   ただし、リージョンの位置に現れた変数は、
   カインドが `Type` でも未確定でも `h` のプールから名前を採る。 *)

  let rigid_name i =
    (* スコーレム定数は制約の一覧に入れない。ς はユーザが書ける名前ではないので、
       型の前の角括弧に出すと書き写せる制約に見えてしまう(§9.2 / §9.7)。
       直し方は、制約の不足を報告するメッセージ自身が述べている *)
    match Hashtbl.find_opt names i.vid with
    | Some n -> n
    | None ->
        incr rigid_count;
        let n = "ς" ^ string_of_int !rigid_count in
        Hashtbl.add names i.vid n;
        n
  in

(* ## 9.3 タプルの表記に戻す

   Keleut のタプルは、`_item` ラベルを並べた行を持つレコードである。
   `(Int32, String)` の内部表現は次のとおりである。

   ```
   TRecord (TRowExtend (_item, Int32, TRowExtend (_item, String, TRowEmpty)))
   ```

   この表現は、Scoped Labels が重複ラベルを許す(§8.6)ので成り立つ。
   タプルは単一化、パターン、網羅性、値のすべてでレコードと同じ経路で処理され、
   タプル専用のコードは必要ない。
   その代わり、表示するときにはタプルの表記へ戻す必要があり、本節がそれを行う。

   タプルと判定する条件は 2 つある。
   行が閉じていることと、すべてのフィールドのラベルが `_item` であることである。
   開いた行はタプルではない。
   `{_item: A extends R}` は sample.kel:195 の `fst` の引数の型で、
   先頭が `A` である任意のレコードを表し、1 要素のタプルではない。
   行が閉じているという条件を外すと、`fst` の引数が `(A,)` と表示され、
   行多相であることが読み取れなくなる。

   1 要素のときだけ `(A,)` と末尾にカンマを書くのは、
   `(A)` がグループ化の括弧と区別できないからである。
   この書き方は表層構文の規則に合わせている。
   第12章 §12.7(実行時の値)と第10章 §10.12(網羅性の反例)も同じ規則に従う。
   2 要素以上、1 要素、空の 3 つの形は、
   `test/typecheck.t` の resugar / resugar2 がゴールデンテスト(期待出力との比較)で固定している。 *)

  let is_tuple_row fields tail =
    (match repr tail with TRowEmpty -> true | _ -> false) && List.for_all (fun (l, _) -> l = l_item) fields
  in

(* ## 9.4 型を Keleut の構文に戻す

   `go` が型 1 つを文字列にする。
   `go` は演算子の優先順位を表す引数を取らない。
   Keleut の矢印は引数を常に括弧で囲んで並べる(`(A) => B`)ので、
   `(A => B) => C` のような曖昧さが構文の上で起きないからである。
   その代わり、`go_args` が引数の閉じた `_item` 行を、括弧で囲んだ並びに戻す。
   返り値が矢印で、外側の矢印のエフェクト行を表示するときは、返り値の矢印を括弧で囲む。
   `@` は最も内側の矢印に付くので、囲まないと外側の行が返り値の矢印のものに読まれるからである。
   外側の行が行変数だけのときは `@` を表示しないので、括弧も付かない。

   ### 文字列連結の評価順

   `go` には、初めて見た型変数に名前を採番するという副作用がある。
   一方、OCaml の `^` は関数適用なので、引数の評価順は規定されていない。
   実際の処理系は、ネイティブコードでもバイトコードでも、おおむね右から評価する。

   そのため、`go_args p ^ 矢印 ^ go r ^ eff_suffix e` と 1 つの式につないで書くと、
   返り値やエフェクト行の変数が先に採番され、
   `(B) => A` のように、返り値が引数より先に名前を取る。
   型としては正しいのに、読みにくい表示になる。
   `TArrow` の分岐は、3 つの部分を `let` で順に評価してから連結し、採番の順序を固定する。

   `TRecord` の開いた行の分岐にも同じ問題がある。
   `^` でつなぐと、`{x: {y: A extends R2} extends R1}` のように、
   外側の行の末尾の行変数が、フィールドの中の行変数より若い番号を取る。
   そこで、フィールドを `let` で先に評価してから行の末尾を評価する。
   `TApp` の分岐も、先頭の型構成子を `let` で先に評価してから引数を評価する。

   採番を伴う関数をリストの各要素に適用するときは、`map_ordered` を使う。
   `map_ordered` は、適用順が OCaml の標準ライブラリの文書で保証されている `List.fold_left` で書いてある。
   `List.map` は現在の実装では先頭から適用するが、この順序は文書では保証されていない。

   ### レコードとヴァリアント

   レコードは 4 通りに書き分ける。
   空の閉じた行は `{}`、フィールドのない開いた行は `{extends R1}`、
   閉じた行は `{x: A, y: B}`、開いた行は `{x: A extends R1}` と書く。
   `extends` は Keleut の表層構文そのままである。

   ヴァリアントは `#Even | #Odd` の形で書く。
   ペイロードがユニットならラベルだけを書き、そうでなければ `#Foo(A)` と書く。
   末尾の行変数は、最後のケースとして並べる(`#Even | #Odd | R1`)。
   sample.kel:210 の `describe` の型は、この形で表示される。
   フィールドも末尾の行変数もない行は `#|` と書く。
   `#|` はケースが 0 個であることを示す記号で、値を持たない型(`Never` に相当する型)を表す。

   `is_unit` が空レコードかどうかを調べるのは、
   Keleut の `Unit` が名目的な型ではなく空レコードだからである(sample.kel:59, :167)。
   `Unit` という名前は、プレリュードの型エイリアスとしてだけ存在する。 *)

  let rec go t =
    match repr t with
    | TVar v -> (
        match !v with
        | Unbound i -> name_of_var i ~generic:false
        | Generic i -> name_of_var i ~generic:true
        | Rigid i -> rigid_name i
        | Link t -> go t)
    | TCon (n, []) -> con_name n
    | TCon (n, args) -> con_name n ^ "[" ^ String.concat ", " (map_ordered go args) ^ "]"
    | TApp _ as t ->
        let h, args = app_spine t in
        (* 先頭の型構成子を先に採番する。^ は右辺を先に評価することがあるので、let で順序を固定する(§9.4) *)
        let hs = go h in
        hs ^ "[" ^ String.concat ", " (map_ordered go args) ^ "]"
    | TArrow (p, r, e) ->
        (* ^ の右辺が先に評価されると採番の順が逆になるので、let で順序を固定する *)
        let ps = go_args p in
        let rs = go r in
        let es = eff_suffix e in
        (* @ は最も内側の矢印に付くので、外側の矢印の @ を書くときは、返り値の矢印を括弧で囲む *)
        let rs = match repr r with TArrow _ when es <> "" -> "(" ^ rs ^ ")" | _ -> rs in
        ps ^ " => " ^ rs ^ es
    | TRecord row -> (
        let fields, tail = row_fields row in
        if is_tuple_row fields tail && fields <> [] then
          "(" ^ String.concat ", " (map_ordered (fun (_, t) -> go t) fields) ^ if List.length fields = 1 then ",)" else ")"
        else
          match (fields, repr tail) with
          | [], TRowEmpty -> "{}"
          | [], tail -> "{extends " ^ go tail ^ "}"
          | fields, TRowEmpty -> "{" ^ String.concat ", " (map_ordered field fields) ^ "}"
          | fields, tail ->
              (* ^ の右辺が先に評価されると、末尾の行変数がフィールドの中の
                 行変数より先に採番され、若い番号を取る(§9.4) *)
              let fs = String.concat ", " (map_ordered field fields) in
              let ts = go tail in
              "{" ^ fs ^ " extends " ^ ts ^ "}")
    | TVariant row -> (
        let fields, tail = row_fields row in
        let case (l, t) = if is_unit t then "#" ^ display_of l else "#" ^ display_of l ^ "(" ^ go t ^ ")" in
        let parts = map_ordered case fields in
        let parts = match repr tail with TRowEmpty -> parts | tail -> parts @ [ go tail ] in
        match parts with [] -> "#|" (* 空ヴァリアント(Never 相当) *) | _ -> String.concat " | " parts)
    | TRowEmpty -> "{}"
    | TRowExtend _ as row -> eff_row row (* 型の位置に単独で現れた行は、エフェクト行の書式で表示する *)
  and field (l, t) = display_of l ^ ": " ^ go t
  and is_unit t = match repr t with TRecord r -> ( match repr r with TRowEmpty -> true | _ -> false) | _ -> false

(* ## 9.5 引数の行を括弧で囲んだ並びに戻す

   `TArrow` の第 1 要素は、閉じた `_item` 行のレコードである。
   `(Int32, String) => Boolean` の引数は 2 個ではなく、レコード 1 個である。
   引数の個数の不一致を行の単一化で検出できるのは、この表現による(§8.7)。

   `go_args` は、その行をタプルの表記に戻す。
   §9.4 の `go` は、`TRecord` をタプルとして表示する条件として、
   `is_tuple_row` に加えて `fields <> []` を要求する。
   空の行を許すと、ユニットの型 `{}` が `()` と表示されてしまうからである。
   `go_args` は `is_tuple_row` だけを使い、`fields <> []` を要求しないので、
   引数のない関数は `() => A` と表示される。
   `go_args` が扱うのは矢印の左側だけなので、この条件を外してよい。

   引数の行が閉じていないか、`_item` 以外のラベルを含むときは、
   タプルの表記を使わず、`TRecord` としてそのまま表示する。
   本来ありえない形だが、推論の途中で壊れた型も表示するのがプリティプリンタの役目なので、
   ここで例外を投げるわけにはいかない。
   エラーメッセージを出そうとした表示関数が例外で異常終了すると、
   ユーザには元のエラーが伝わらない。 *)

  and go_args p =
    (* TArrow の引数は閉じた _item 行である。開いていても例外を投げずに表示する *)
    match repr p with
    | TRecord row ->
        let fields, tail = row_fields row in
        if is_tuple_row fields tail then "(" ^ String.concat ", " (map_ordered (fun (_, t) -> go t) fields) ^ ")"
        else go (TRecord row)
    | t -> go t

(* ## 9.6 エフェクト行の表示と省略

   矢印のエフェクト行は、形によって 3 通りに表示する。

   | 行の形 | 表示 | 意味 |
   |---|---|---|
   | `TRowEmpty` | ` @ {}` | 純粋(`@ {}`) |
   | 行変数だけの行 | 何も出さない | エフェクト多相(最も外側の `@` の省略、または明示した行変数)か、弱い行変数 |
   | ラベルを含む行 | ` @ {Console, ...}` | 具体的なエフェクト |

   行変数だけの行を省くのは、ほとんどの関数の行がこの形であり、
   すべての型に `@ R1` が付くと読みにくいからである。
   行が一般化された行変数だけである関数は、呼び出す側がエフェクトを気にしなくてよい。
   一般化されない弱い行変数は別で、最初に呼び出した位置の行に決まる。

   閉じた空の行は ` @ {}` と表示する。
   閉じた行は書いたとおりに型に残り、使うときに行の末尾を開く(使用時に行を開く規則。第11章 §11.26)。
   そのため、閉じた空の行の関数も、行変数だけの行の関数と同じく、どの行の文脈からも呼べる。
   それでも表示を分けるのは、型として違うからである。
   閉じた空の行は関数がエフェクトを起こさないことを表し、
   仮引数の型の中の `@ {}` は、そこに渡せる関数を純粋なものに限る。
   閉じた空の行を持つのは、最も外側に `@ {}` と書いた束縛、`pub` で `@` を省略した束縛、
   `@` を省略した型クラスのメソッド、入れ子の矢印の行、注釈の先頭が型エイリアスである値束縛の行、
   一般化されない束縛で空に決まった行などである。
   表示を分けたうえで、区別が必要な診断では、エラーメッセージにも説明を加える。
   たとえば第11章 §11.12 は、行が `@ {}` の高階の引数(`@ {}` のコールバックなど)の中で
   エフェクトのある関数を呼んだときに、
   その位置の行が空で純粋であることを説明する文を加える。
   ただし、その位置に `perform` を直接書いたとき(§11.15)は、この文を加えない。

   入れ子の矢印で省略した `@` は `@ {}` と読むので、`(f: () => Unit)` は `(() => {} @ {}) => {}`、
   `[E](f: () => Unit @ E)` は `(() => {}) => {}` と表示される(`test/annot_rows.t` の nested1)。

   表示が同じで意味が違う組には、たとえば次のものがある。

   - 行カインドのパラメータに渡した空の行 `Callback[{}]` と、型としての `Unit` `{}`。
     どちらも `{}` と表示される。
   - 一般化されていない弱い行変数と、一般化された行変数。
     矢印のエフェクト行が行変数だけなら、弱い変数でも何も表示しないので、§9.1 の下線は現れない。
     たとえば `id` を恒等関数として、`let c = id(fn() => 1)` の `c` は値制限で一般化されず、
     `let c2 = fn() => 1` の `c2` と同じ `() => Int32` と表示される。
     `c2` の行は使うたびに新しい行変数になるが、`c` の行は最初に呼び出した位置の行に決まる。

   ラベルは引数を 1 つ取れる。
   引数がユニットならラベル名だけ(`Console`)を書き、そうでなければ `Heap[ς1]` のように角括弧で書く。
   リージョンの取り違えを報告するエラーメッセージに `ς` が現れるのは、この書式による。

   `eff_row` は、型の位置に単独で現れた行(`go` に `TRowExtend` が直接渡された場合)の表示にも使う。
   Keleut で行が単独で型の位置に現れるのはエフェクト行のときだけなので、この書式で足りる。 *)

  and eff_row row =
    let fields, tail = row_fields row in
    let label (l, t) = if is_unit t then con_name l else con_name l ^ "[" ^ go t ^ "]" in
    let parts = map_ordered label fields in
    let ext = match repr tail with TRowEmpty -> "" | tail -> (if parts = [] then "extends " else " extends ") ^ go tail in
    "{" ^ String.concat ", " parts ^ ext ^ "}"
  and eff_suffix e =
    (* 行変数だけの行は表示せず、閉じた空の行は @ {} と表示する(§9.6) *)
    match repr e with
    | TRowEmpty -> " @ {}"
    | TVar _ -> ""
    | row -> " @ " ^ eff_row row
  in

(* ## 9.7 制約を型の前の角括弧に書く

   すべての型を文字列にし終えてから、一覧にたまった制約を型の前に書く。
   形は `[A: Add + Mul, F: Functor] (F[A]) => A` で、
   これは Keleut の型パラメータの束縛子の構文そのものである。
   ユーザは表示された制約を、そのまま `let f[A: Add + Mul]...` と書き写せる。
   そのため、角括弧に書くのは `Generic` と `Unbound` の変数だけである(§9.2)。

   `strs` を作ってから `ctx` を作るという順序は入れ替えられない。
   どの変数に名前が付き、どの制約が実際に現れたかは、
   すべての型に `go` を適用し終えるまで確定しないからである。
   §9.4 と同じく、ここでも採番の副作用が評価の順序を決めている。

   1 つの変数のクラス名は `List.sort compare` で並べる。
   `vcls` の順(`add_class` が追加した順、つまり単一化の順)をそのまま出すと、
   意味的に同じ型が推論の経路によって違う文字列になり、ゴールデンテストの期待出力と合わなくなる。

   ### show2 と show_pair は制約を書かない

   `show2` は `ctx` を捨てる。
   `show2` の返り値は「型が一致しません: `X` と `Y`」という文の中に埋め込まれるので、
   その前に `[A: Add]` を書くと、第 1 引数だけに掛かるように読めてしまう。
   2 つの型を別々の文字列で返す `show_pair` も、同じ理由で `ctx` を捨てる。
   制約を見せたい診断は、型を 1 つずつ `show` で出す形に組み直す。

   ### 第8章の変数に表示関数を代入する

   ファイル末尾の `let () = ...` は、
   第8章(unify.ml)の `show_ref`、`show2_ref`、`show_pair_ref` に本章の関数を代入する。
   これで、モジュールの循環参照を避けたまま、単一化のエラーメッセージが実際の型を表示できる。
   show.ml がリンクされず、この初期化が実行されなければ、型エラーの本文には `<型>` が並ぶ(§8.2)。 *)

  let strs = map_ordered go ts in
  let ctx =
    match !constrained with
    | [] -> ""
    | cs ->
        "["
        ^ String.concat ", "
            (List.map (fun (n, cls) -> n ^ ": " ^ String.concat " + " (List.sort compare (List.map display_of cls))) cs)
        ^ "] "
  in
  (strs, ctx)

let show t =
  let strs, ctx = show_all [ t ] in
  ctx ^ List.hd strs

let show2 a b =
  (* ctx は捨てる。文の中に埋め込むので、
     制約を前に書くと第 1 引数だけに掛かるように読める(§9.7) *)
  let strs, _ = show_all [ a; b ] in
  match strs with [ x; y ] -> x ^ " と " ^ y | _ -> bug "show2"

let show_pair a b =
  (* ctx は捨てる。2 つの型を別々の文に埋め込むので、show2 と同じく制約を前に書かない *)
  let strs, _ = show_all [ a; b ] in
  match strs with [ x; y ] -> (x, y) | _ -> bug "show_pair"

let () =
  Unify.show_ref := show;
  Unify.show2_ref := show2;
  Unify.show_pair_ref := show_pair
