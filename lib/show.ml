(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第9章 型の表示

   型検査器が利用者に見せるものは 2 種類ある。
   検査が通ったときの `name : type` の一覧と、通らなかったときのエラーメッセージである。
   どちらも型を印字しなければ書けないので、型検査器の出力のほとんどは本章のプリティプリンタを通る。

   本章の役目は、型を内部表現ではなく Keleut の表層構文で見せることである。
   第1章(syntax.ml)の `ty` は、行と `_item` ラベルで統一した内部表現で、利用者が書く形とは違う。
   利用者が書くのは `(Int32, String) => Boolean` であって、
   `TArrow (TRecord (TRowExtend (_item, ...)), ...)` ではない。

   印字の方針は次のとおりである。

   1. `Generic` は `A, B, C…`、`Unbound` は `_A, _B…`、`Rigid` は `ς1, ς2…` と書く
   2. カインドごとに名前のプールを変える(`Type` は `A..E`、`F[_]` は `F..H`)
   3. エフェクト行が空または裸の行変数のときは表示しない
   4. エフェクトラベルの引数がユニットなら、裸のラベル名を書く
   5. 制約つき変数があれば、その制約を前置する

   さらに、記号は表層構文に合わせる。
   矢印は `=>`、エフェクトは `@`、型引数は角括弧、行の伸びは `extends` で書く。

   また、タプルを再糖衣化する(§9.3)。
   Keleut はタプルを `_item` ラベルの行の糖衣として表し、
   型にも構文木にも値にも専用のタプルを持たない。
   そのため、表示するときにタプルの形へ戻す必要がある。

   本章は第8章(unify.ml)の `is_predicate` を使う。

   本章の印字関数をほかの章が使う経路は 2 つある。
   1 つは名前による呼び出しで、第11章(elab.ml)が束縛ごとに `Show.show` を呼び、
   `--type-check` を指定したときに出力する `name : type` の行を作る。
   `test/typecheck*.t` のゴールデンは、この行の並びでできている。
   もう 1 つは、ファイル末尾で `show` / `show2` を `Unify.show_ref` / `Unify.show2_ref` に差し込む経路で、
   第8章のエラーメッセージはこの経路で型を印字する。 *)

open Aux
open Syntax
open Type

(* ## 9.1 複数の型をまとめて印字する show_all

   単一化が失敗したときに出したいのは、
   「型が一致しません: `A => A` と `B => Int32`」というメッセージである。
   型を 1 つずつ独立に印字すると、どちらの型でも最初に採番した変数が `A` になり、
   「型が一致しません: `A => A` と `A => Int32`」になってしまう。
   これでは、利用者には何が起きたのか分からない。

   そこで本体は複数の型をまとめて受け取る `show_all` とし、
   採番表(`names`)と制約台帳(`constrained`)を型のあいだで共有する。
   `show` は 1 要素のリストを、`show2` は 2 要素のリストを `show_all` に渡す薄い包みである。

   採番表の鍵は `vid`(第1章の oid)である。
   同じ変数は何度現れても同じ名前になり、違う変数は必ず違う名前になる。

   ### 名前のプール

   カインドごとにプールを分けるのは、読みやすさのためである。
   `[F: Functor] (F[A]) => F[B]` を見れば、`F` が型構成子で、`A` と `B` が型だとすぐに分かる。
   すべてを `A B C` から採ると `A[B] => A[C]` になり、`A` が何なのかを考えないと分からない。
   行変数だけは `R1, R2` と連番にする。
   行はプールを使い切りやすく、`R` の連番なら何番目の行変数かがそのまま読めるからである。

   `pick` はプールを使い切ると添字を足す(`A, B, …, E, A1, B1, …`)。

   ### 弱い変数の下線

   `Unbound` の変数には `_` を前置する。
   OCaml の `'_weak1` と同じく、値制限で一般化されなかった変数であることがすぐに分かる。
   `let r = Ref.new(0)` のような束縛の型に `_A` が出ていたら、
   その型はまだ決まっていないが、決まったら 1 つに固定される、という意味である。
   逆に、弱い変数であるべき変数が下線なしで出ていたら、過剰な一般化を疑える。

   ### 制約台帳

   `record_cs` は名前を返すついでに、その変数の制約を台帳へ積む。
   このとき、予約述語 `Integral` / `Fractional` は台帳に積まずに落とす。
   通常は既定化(第8章(unify.ml)の §8.9)が一般化より先に走るので、予約述語は表示に届かない。
   しかしエラーの経路では、既定化の前の型を印字することがある。
   その型を `[A: Integral] A` のように表示すると、制約に書けないクラス名を利用者に見せることになる。

   台帳も採番表も、`show_all` を呼ぶたびに作り直す。
   印字の最中に単一化は走らないので、同じ変数の制約集合が印字の途中に増えることはない。
   `List.mem_assoc` の検査は同じ変数を 2 度載せないためのもので、
   先に載せた値を守るためのものではない。

   台帳を `list ref` にして `@` で末尾に追加するのは、出現順を保つためである。
   `Hashtbl` にすると `[B: Eq, A: Add]` のように型の中の並びと逆に出ることがあり、
   利用者が型と照合しにくくなる。
   型は短いので、線形探索の費用は問題にならない。 *)

let show_all ts =
  let names : (oid, string) Hashtbl.t = Hashtbl.create 16 in
  let constrained : (string * cls) list ref = ref [] in
  let star_pool = "ABCDE" in
  let arrow_pool = "FGH" in
  let star_count = ref 0 in
  let arrow_count = ref 0 in
  let row_count = ref 0 in
  let rigid_count = ref 0 in
  let pick pool i =
    String.make 1 pool.[i mod String.length pool] ^ if i >= String.length pool then string_of_int (i / String.length pool) else ""
  in
  let record_cs name cs =
    let cs = List.filter (fun c -> not (Unify.is_predicate c)) cs in
    (* 同じクラスの重複は落とす(出現順は保つ)。add_class が追加時に
       List.mem で重複を防いでいるが、印字の側でも念のため落とす *)
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

  (* 採番は副作用なので、写像の評価順も固定する(§9.4)。
     stdlib の List.map は現在の実装では先頭から適用するが、その順序は
     保証されていない。List.fold_left の適用順は stdlib の文書が明記している *)
  let map_ordered f xs = List.rev (List.fold_left (fun acc x -> f x :: acc) [] xs) in

(* ## 9.2 剛定数は ς で書く

   `Rigid` にだけ別のプールを与え、`ς1` `ς2` と番号を振る。
   ギリシャ文字を使うのは、利用者が書ける型ではないことを示すためである。
   `A` や `_A` はまだ決まっていない型を表すが、
   `ς1` は決まっていて、しかも導入したスコープの外には存在しない型を表す。
   意味が正反対なので、見た目も変えておく。

   `ς` が画面に出る典型的な場合は 2 つある。
   1 つは `run` のリージョンから `Ref` を持ち出そうとしたとき(§8.3 の脱出検査)で、
   もう 1 つは本体が注釈の型パラメータより具体的すぎたとき(skolem 化の検査)である。
   どちらも、利用者が `A` と書いたその `A` はここでは何にでもなれるわけではない、という指摘である。
   `ς` という見た目が、その `A` が固定された型であることを伝える。

   剛定数の制約は台帳に載せない。
   §9.7 の角括弧は、利用者がそのまま束縛子へ書き写せる形式である。
   剛定数の制約を載せると `[ς1: Add] ς1` と表示され、そこに書き写せない名前が混ざる。
   剛定数に足りない制約の直し方は、
   それを報告するエラーメッセージ自身が「[A: Ord] のように」と述べている。
   同じ情報を、書き写せない形式でもう一度見せることはしない。

   なお、`name_of_var` は、カインドが未確定(`KVar`)の変数を、
   `kind_repr` による場合分けの最後の `_` の分岐で `Type` と同じに扱う。
   カインドが未確定のまま印字される変数は、
   後で `KStar` へ既定化される(第1章の `default_kind`。時期は §1.6)。
   そこで、先回りして `Type` のプールから名前を採る。 *)

  let rigid_name i =
    (* 剛定数は制約台帳に載せない。ς は利用者が書ける名前ではないので、
       角括弧の前置に出すと書き写せる制約に見えてしまう(§9.2 / §9.7)。
       直し方は、制約の不足を報告するメッセージ自身が述べている *)
    match Hashtbl.find_opt names i.vid with
    | Some n -> n
    | None ->
        incr rigid_count;
        let n = "ς" ^ string_of_int !rigid_count in
        Hashtbl.add names i.vid n;
        n
  in

(* ## 9.3 タプルの再糖衣化

   Keleut のタプルは、`_item` ラベルを並べた行を持つレコードである。
   `(Int32, String)` の内部表現は次のとおりである。

   ```
   TRecord (TRowExtend (_item, Int32, TRowExtend (_item, String, TRowEmpty)))
   ```

   この表現は、Scoped Labels が重複ラベルを許す(§8.6)ので成り立つ。
   タプルは単一化、パターン、網羅性、値のすべてでレコードと同じ経路で処理され、
   タプル専用のコードは要らない。
   その代わり、表示するときにはタプルの形へ戻す必要があり、本節がそれを行う。

   タプルと判定する条件は 2 つある。
   行が閉じていることと、すべてのフィールドのラベルが `_item` であることである。
   開いた行はタプルではない。
   `{_item: A extends R}` は sample.kel:195 の `fst` の引数の型で、
   先頭が `A` である任意のレコードを表し、1 要素のタプルではない。
   行が閉じているという条件を外すと、`fst` の引数が `(A,)` と表示され、
   行多相であることが読み取れなくなる。

   1 要素のときだけ `(A,)` と末尾にカンマを打つのは、`(A)` がただの括弧と区別できないからである。
   この書き方は表層構文の規約に合わせている。
   第12章 §12.7(実行時の値)と第10章 §10.12(網羅性の反例)も同じ規則に従う。
   2 要素以上、1 要素、空の 3 つの形は、
   `test/typecheck.t` の resugar / resugar2 がゴールデンとして固定している。 *)

  let is_tuple_row fields tail =
    (match repr tail with TRowEmpty -> true | _ -> false) && List.for_all (fun (l, _) -> l = l_item) fields
  in

(* ## 9.4 型を Keleut の構文に戻す

   `go` が型 1 つを文字列にする。
   `go` は演算子の優先順位を表す引数を取らない。
   Keleut の矢印は引数を常に括弧つきの並びで書く(`(A) => B`)ので、
   `(A => B) => C` のような曖昧さが構文の上で起きないからである。
   その代わり、`go_args` が引数の閉じた `_item` 行を括弧の並びに戻す。

   ### 文字列連結の評価順

   `go` には、初めて見た型変数に名前を採番するという副作用がある。
   一方、OCaml の `^` は関数適用なので、引数の評価順は規定されていない。
   実際の処理系は、ネイティブコードでもバイトコードでも、おおむね右から評価する。

   そのため、`go_args p ^ 矢印 ^ go r ^ eff_suffix e` と 1 つの式につないで書くと、
   返り値やエフェクト行の変数が先に採番され、
   `(B) => A` のように、返り値が引数より先に名前を取る。
   型としては正しいのに、読みにくい表示になる。
   `TArrow` の分岐は、3 つの部分を `let` で順に評価してから連結し、採番の順序を固定する。

   `TRecord` の尾部つきの分岐にも同じ問題がある。
   `^` でつなぐと、`{x: {y: A extends R2} extends R1}` のように、
   外側の行の尾部が、フィールドの中の行変数より若い番号を取る。
   そこで、フィールドを `let` で先に評価してから尾部を評価する。
   `TApp` の分岐も、頭を `let` で先に評価してから引数を評価する。

   採番を伴う写像には `map_ordered` を使う。
   `map_ordered` は、適用順が OCaml の標準ライブラリの文書で保証されている `List.fold_left` で書いてある。
   `List.map` は現在の実装では先頭から適用するが、この順序は文書では保証されていない。

   ### レコードとヴァリアント

   レコードは 4 通りに書き分ける。
   空の閉じた行は `{}`、フィールドのない開いた行は `{extends R1}`、
   閉じた行は `{x: A, y: B}`、開いた行は `{x: A extends R1}` と書く。
   `extends` は Keleut の表層構文そのままである。

   ヴァリアントは `#Even | #Odd` の形で書く。
   ペイロードがユニットならラベルだけを書き、そうでなければ `#Foo(A)` と書く。
   尾部の行変数は、最後の選択肢として並べる(`#Even | #Odd | R1`)。
   sample.kel:210 の `describe` の型は、この形で表示される。
   フィールドも尾部もない行は `#|` と書く。
   `#|` は選択肢がゼロ個であることを示す記号で、値が存在しない型(`Never` に相当する型)を表す。

   `is_unit` が空レコードかどうかを調べるのは、
   Keleut の `Unit` が名目型ではなく空レコードだからである(sample.kel:59, :167)。
   `Unit` という名前は、プレリュードの型エイリアスとしてだけ存在する。 *)

  let rec go t =
    match repr t with
    | TVar v -> (
        match !v with
        | Unbound i -> name_of_var i ~generic:false
        | Generic i -> name_of_var i ~generic:true
        | Rigid i -> rigid_name i
        | Link t -> go t)
    | TCon (n, []) -> name_of n
    | TCon (n, args) -> name_of n ^ "[" ^ String.concat ", " (map_ordered go args) ^ "]"
    | TApp _ as t ->
        let h, args = app_spine t in
        (* 頭を先に採番する。^ は右辺を先に評価しうるので、let で順序を固定する(§9.4) *)
        let hs = go h in
        hs ^ "[" ^ String.concat ", " (map_ordered go args) ^ "]"
    | TArrow (p, r, e) ->
        (* ^ の右辺が先に評価されると採番の順が逆になるので、let で順序を固定する *)
        let ps = go_args p in
        let rs = go r in
        let es = eff_suffix e in
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
              (* ^ の右辺が先に評価されると、尾部の行変数がフィールドの中の
                 行変数より先に採番され、若い番号を取る(§9.4) *)
              let fs = String.concat ", " (map_ordered field fields) in
              let ts = go tail in
              "{" ^ fs ^ " extends " ^ ts ^ "}")
    | TVariant row -> (
        let fields, tail = row_fields row in
        let case (l, t) = if is_unit t then "#" ^ name_of l else "#" ^ name_of l ^ "(" ^ go t ^ ")" in
        let parts = map_ordered case fields in
        let parts = match repr tail with TRowEmpty -> parts | tail -> parts @ [ go tail ] in
        match parts with [] -> "#|" (* 空ヴァリアント(Never 相当) *) | _ -> String.concat " | " parts)
    | TRowEmpty -> "{}"
    | TRowExtend _ as row -> eff_row row (* 裸の行はエフェクト行の書式で印字する *)
  and field (l, t) = name_of l ^ ": " ^ go t
  and is_unit t = match repr t with TRecord r -> ( match repr r with TRowEmpty -> true | _ -> false) | _ -> false

(* ## 9.5 引数の行を括弧の並びに戻す

   `TArrow` の第 1 要素は、閉じた `_item` 行のレコードである。
   `(Int32, String) => Boolean` の引数は 2 個ではなく、レコード 1 個である。
   引数の個数の不一致が行の単一化から検出されるのは、この表現による(§8.7)。

   `go_args` は、その行をタプルの書式に戻す。
   §9.4 の `go` は、`TRecord` をタプルとして表示する条件として、
   `is_tuple_row` に加えて `fields <> []` を要求する。
   空の行を許すと、ユニットの型 `{}` が `()` と表示されてしまうからである。
   `go_args` は `is_tuple_row` だけを使い、`fields <> []` を要求しないので、
   引数のない関数は `() => A` と表示される。
   `go_args` が扱うのは矢印の左側だけなので、この条件を外してよい。

   閉じていない引数の行に出会ったら、タプルの書式をあきらめて `TRecord` としてそのまま表示する。
   本来ありえない形だが、推論の途中で壊れた型も印字するのがプリティプリンタの役目なので、
   ここで例外を投げるわけにはいかない。
   エラーメッセージを出そうとした印字関数がエラーで落ちると、利用者には元のエラーが届かない。 *)

  and go_args p =
    (* TArrow の引数は閉じた _item 行。開いていても落ちずに印字する *)
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
   | `TRowEmpty` | 何も出さない | 純粋(`@ {}`) |
   | 裸の行変数 | 何も出さない | エフェクト多相(最外の `@` の省略、または明示した行変数)か、弱い行変数 |
   | ラベルを含む行 | ` @ {Console, ...}` | 具体的なエフェクト |

   前の 2 つを省くのは、ほとんどの関数がこのどちらかであり、
   すべての型に `@ {}` や `@ R1` が付くと読みにくいからである。
   この省略は、どちらも呼び出す側がエフェクトを気にしなくてよい関数だ、という近似に基づく。

   ただし、純粋(閉じた `@ {}`)と多相(裸の行変数)は、表示が同じでも挙動が違う。
   行の部分型付け(サブエフェクティング)がないので、
   純粋な側の関数はエフェクトのある文脈から呼べない。
   表示から両者を区別する方法はない。
   区別が要る診断は、エラーメッセージの文言で補う。
   たとえば第11章 §11.12 は、行が空の関数を空でない行の下から呼んだときに、
   呼び出し先の行が空で純粋であることを説明する文言を加える。
   逆に、`par` のコールバックのように、
   行が `@ {}` の高階の引数の中でエフェクトのある関数を呼んだときは、
   その位置の行が空で純粋であることを説明する文言を加える。
   ただし、その位置に `perform` を直接書いたとき(§11.15)は、この文言を加えない。

   表示が同じで意味が違う組には、たとえば次のものがある。

   - 入れ子の矢印に明示した行変数 `@ E` と `@ {}`。
     入れ子の矢印で省略した `@` は `@ {}` と読む。
     そのため、`(f: () => Unit)` と `[E](f: () => Unit @ E)` は意味が違うが、
     どちらも `(() => {}) => {}` と表示される(`test/annot_rows.t` の nested1)。
   - 最外の矢印で `@` を省略した `let`(行変数に一般化する)と、`@ {}` と書いた `let`(行が閉じる)。
     たとえば、`@` を省略した `sum` と `@ {}` と書いた `sum2` は、
     同じ `(Array[Int32]) => Int32` と表示されるが、
     `Console` の下から呼べるのは `sum` だけである(`test/spec_gaps.t` の sumgen / sumclosed)。
   - 行カインドのパラメータに渡した空の行 `Callback[{}]` と、型としての `Unit` `{}`。
     どちらも `{}` と表示される。
   - 一般化されていない弱い行変数と、一般化された行変数。
     矢印のエフェクト行が裸の行変数なら、弱い変数でも何も表示しないので、§9.1 の下線は現れない。
     たとえば `id` を恒等関数として、`let c = id(fn() => 1)` の `c` は値制限で一般化されず、
     `let c2 = fn() => 1` の `c2` と同じ `() => Int32` と表示される。
     `c2` の行は使うたびに新しい行変数になるが、`c` の行は最初に呼び出した位置の行に固まる。

   ラベルは引数を 1 つ取れる。
   引数がユニットなら裸の名前(`Console`)で書き、そうでなければ `Heap[ς1]` のように角括弧で書く。
   リージョンの取り違えを報告するエラーメッセージに `ς` が現れるのは、この書式による。

   `eff_row` は、裸の行(`TRowExtend` が直接来た場合)の印字にも使う。
   Keleut で行が単独で型の位置に現れるのはエフェクト行のときだけなので、この書式で足りる。 *)

  and eff_row row =
    let fields, tail = row_fields row in
    let label (l, t) = if is_unit t then name_of l else name_of l ^ "[" ^ go t ^ "]" in
    let parts = map_ordered label fields in
    let ext = match repr tail with TRowEmpty -> "" | tail -> (if parts = [] then "extends " else " extends ") ^ go tail in
    "{" ^ String.concat ", " parts ^ ext ^ "}"
  and eff_suffix e =
    (* 空の行と裸の行変数は表示しない(§9.6) *)
    match repr e with
    | TRowEmpty -> ""
    | TVar _ -> ""
    | row -> " @ " ^ eff_row row
  in

(* ## 9.7 制約を角括弧で前置する

   すべての型を印字し終えてから、台帳に溜まった制約を前置する。
   形は `[A: Add + Mul, F: Functor] (F[A]) => A` で、
   これは Keleut の型パラメータの束縛子の構文そのものである。
   利用者は表示された制約を、そのまま `let f[A: Add + Mul]...` と書き写せる。
   そのため、前置に載せるのは `Generic` と `Unbound` の変数だけである(§9.2)。

   `strs` を作ってから `ctx` を作るという順序は入れ替えられない。
   どの変数に名前が付き、どの制約が実際に現れたかは、
   すべての型に `go` を走らせ終えるまで確定しないからである。
   §9.4 と同じく、ここでも採番の副作用が評価の順序を縛っている。

   クラス名は `List.sort compare` で並べる。
   台帳の順(`add_class` が合併した順、つまり単一化の順)をそのまま出すと、
   意味的に同じ型が推論の経路によって違う文字列になり、ゴールデンテストの結果が揺れる。

   ### show2 は前置しない

   `show2` は `ctx` を捨てる。
   `show2` の返り値は「型が一致しません: `X` と `Y`」という文の中に埋め込まれるので、
   そこに `[A: Add]` を前置すると、第 1 引数だけに掛かるように読めてしまう。
   制約を見せたい診断は、型を 1 つずつ `show` で出す形に組み直す。

   ### 第8章の穴を埋める

   ファイル末尾の `let () = ...` は、第8章(unify.ml)の `show_ref` / `show2_ref` の穴を埋める。
   これで、モジュールの循環を避けたまま、単一化のエラーメッセージが実際の型を印字できる。
   show.ml がリンクされず、この初期化が走らなければ、型エラーの本文は `<型>` だらけになる(§8.2)。 *)

  let strs = map_ordered go ts in
  let ctx =
    match !constrained with
    | [] -> ""
    | cs ->
        "["
        ^ String.concat ", "
            (List.map (fun (n, cls) -> n ^ ": " ^ String.concat " + " (List.sort compare (List.map name_of cls))) cs)
        ^ "] "
  in
  (strs, ctx)

let show t =
  let strs, ctx = show_all [ t ] in
  ctx ^ List.hd strs

let show2 a b =
  (* ctx は捨てる。文の中に埋め込むので、
     前置すると第 1 引数だけに掛かるように読める(§9.7) *)
  let strs, _ = show_all [ a; b ] in
  match strs with [ x; y ] -> x ^ " と " ^ y | _ -> bug "show2"

let () =
  Unify.show_ref := show;
  Unify.show2_ref := show2
