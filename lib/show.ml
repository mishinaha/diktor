(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第9章 — 型の表示

   型検査器がユーザに見せるものは、突き詰めると 2 種類しかありません。
   通ったときの `name : type` の一覧と、通らなかったときのエラーメッセージ
   です。どちらも型を印字しなければ 1 行も書けないので、型のプリティ
   プリンタは「おまけ」ではなく、推論器の顔そのものにあたります。

   本章の義務は 1 つに尽きます。**内部表現ではなく Keleut の表層構文で見せる**
   こと。第1章 (syntax.ml) の `ty` は行と `_item` ラベルで統一された
   都合のよい表現ですが、ユーザはそんなものを書いていません。
   ユーザが書いたのは `(Int32, String) => Boolean` であって
   `TArrow (TRecord (TRowExtend (_item, ...)), ...)` ではない。
   その距離を埋め戻すのがここです。

   お手本は MiniLang §4 (pretty printer) で、方針は 5 つとも
   そのまま受け継ぎます。

   1. `Generic` は `A, B, C…`、`Unbound` は `_A, _B…`、`Rigid` は `ς1, ς2…`
   2. カインドごとに名前のプールを変える (`Type` は `A..E`、`F[_]` は `F..H`)
   3. エフェクト行が空または裸の行変数のときは表示しない
   4. エフェクトラベルは引数を取れる。引数がユニットなら裸のラベル名
   5. 制約つき変数があれば前置する

   Keleut 版で足したのは 2 つです。表層構文への寄せ (矢印は `=>`、
   エフェクトは `@`、型引数は角括弧、行の伸びは `extends`) と、
   **タプルの再糖衣化**。D4 でタプルを型からも AST からも値からも全廃し、
   `_item` ラベルの行の糖衣にしたので、その糖衣をここで着せ直す義務が
   生じました。計画 §7.7 が「追加義務、約20行」と書いているのがこれです。

   > 内部表現を統一した分の借金は、プリティプリンタが返す。

   前章 (第8章 unify.ml) からは `is_predicate` を借ります。渡すほうは
   2 経路あります。1 つは名指しの依存で、第11章 (elab.ml) が束縛ごとに
   `Show.show` を呼び、`--type-check` が並べる `name : type` の行を作ります。
   test/typecheck*.t のゴールデンは、この行の並びでできています。
   もう 1 つはファイル末尾で `Unify.show_ref` / `Unify.show2_ref` に自分を
   差し込む経路で、こちらは第8章のエラーメッセージに後ろから貼りつきます。
   表向きは地味ですが、型検査器の出力はほぼ全部この章を通ります。 *)

open Aux
open Syntax
open Type

(* ## 9.1 なぜ本体が show ではなく show_all なのか

   単一化が失敗したとき、出したいのは「`A => A` と `B => Int32` が
   一致しません」です。ところが型を 1 つずつ独立に印字すると、
   どちらの変数も最初に採番されて `A` になり、
   「`A => A` と `A => Int32` が一致しません」になります。
   読み手には何が起きたのか分かりません。

   だから本体は複数の型をまとめて受ける `show_all` にして、
   採番表 (`names`) と制約台帳 (`constrained`) を型のあいだで共有します。
   `show` は 1 要素のリストを渡す薄い包み、`show2` は 2 要素です。

   採番表の鍵は `vid` (第1章の oid) です。同じ変数は何度出てきても
   同じ名前になり、違う変数は必ず違う名前になります。

   ### 名前のプール

   カインドごとにプールを分けるのは読みやすさのためです。
   `[F: Functor] (F[A]) => F[B]` を見たとき、`F` が型構成子で
   `A` `B` が型だと一目で分かります。全部 `A B C` から採ると
   `A[B] => A[C]` になり、`A` が何なのか考えないと分からない。
   行変数だけは `R1, R2` と連番にします。行はプールを使い切りやすく、
   `R` の並びなら何番目かがそのまま読めるからです。

   `pick` はプールを使い切ったら添字を足します (`A, B, …, E, A1, B1, …`)。

   ### 弱変数の下線

   `Generic` でない `Unbound` には `_` を前置します。OCaml の `'_weak1` と
   同じで、**値制限で一般化されなかった変数**が一目で分かります。
   `let r = Ref.new(0)` のような束縛の型に `_A` が出ていたら、
   それは「まだ型が決まっていないが、決まったら 1 つに固定される」の意味です。
   逆にいえば、weak であるべき変数が下線なしで出ていたら過剰一般化を疑えます。
   敵対的検証で見つかった健全性欠陥 2 — 注釈付き非値が値制限を迂回して
   `run` の剛定数を持ち出せた件 — は、まさにその形で表に出ました。

   ### 制約台帳

   `record_cs` は名前を返すついでに、その変数の制約を台帳へ積みます。
   ここで**予約述語 `Integral` / `Fractional` を落とす**のが D8 の後始末です。
   通常なら既定化 (第8章 (unify.ml) の §8.9) が一般化より先に走るので
   述語は表示に届きませんが、エラー経路では既定化前の型を印字することが
   あります。そこで `[A: Integral] A` などと出ると、ユーザは書けない
   クラス名を見せられて途方に暮れます。だから印字の直前で捨てます。

   台帳が `list ref` で `@` による末尾追加になっているのは、
   **出現順を保つ**ためです。`Hashtbl` にすると `[B: Eq, A: Add]` のように
   型の中の並びと逆に出ることがあり、読み手が型と照合できなくなります。
   型は短いので線形探索の費用は問題になりません。 *)

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

  (* 採番は副作用なので、写像の評価順も固定する(§9.4)。stdlib の
     List.map は現状左から評価するが、仕様として保証されてはいない。
     List.fold_left の適用順は仕様が明記している(M19 / G4b) *)
  let map_ordered f xs = List.rev (List.fold_left (fun acc x -> f x :: acc) [] xs) in

(* ## 9.2 剛定数は ς で書く

   `Rigid` にだけ別のプールを与え、`ς1` `ς2` と番号を振ります。
   ギリシャ文字を使うのは、**これはユーザが書ける型ではない**という
   合図です。`A` や `_A` は「まだ決まっていない」ですが、`ς1` は
   「決まっていて、しかもこのスコープの外には存在しない」。
   意味が正反対なので、見た目も揃えないほうが親切です。

   実際に `ς` が画面に出る典型は 2 つです。`run` のリージョンから
   `Ref` を持ち出そうとしたとき (§8.3 の脱出検査) と、
   注釈の型パラメータより本体が具体的すぎたとき (skolem 化の検査)。
   どちらも「あなたが `A` と書いたその `A` は、ここでは
   何にでもなれるわけではない」という話なので、`ς` の見え方が効きます。

   剛定数の制約は台帳に載せません (M19 / G4c)。載せると `[ς1: Add] ς1`
   と出て、§9.7 の角括弧 — ユーザがそのまま束縛子へ書き写せる形式 — に
   書き写せない名前が混ざります。剛定数に足りない制約の直し方は、それを
   報告するメッセージ自身が「[A: Ord] のように」と述べています。
   **同じ情報を、書き写せない形式でもう一度見せない。**

   なお `kind_repr` の分岐で `KVar` が `_` (最後の枝) に落ちて `Type` 扱いに
   なる点は意図どおりです。カインドが未確定のまま印字に来た変数は、
   宣言終了時に `KStar` へ既定化される運命 (D7) なので、
   先回りして `Type` のプールから名前を採ります。 *)

  let rigid_name i =
    (* 剛定数は制約台帳に載せない(M19 / G4c)。ς はユーザが書ける名前では
       ないので、角括弧の前置に出すと「書き写せる制約」に見える
       (§9.2 / §9.7)。直し方は報告メッセージ自身が述べている *)
    match Hashtbl.find_opt names i.vid with
    | Some n -> n
    | None ->
        incr rigid_count;
        let n = "ς" ^ string_of_int !rigid_count in
        Hashtbl.add names i.vid n;
        n
  in

(* ## 9.3 タプルの再糖衣化

   D4 でタプルは `_item` ラベルの行になりました。`(Int32, String)` の内部表現は
   `TRecord (TRowExtend (_item, Int32, TRowExtend (_item, String, TRowEmpty)))` です。
   Scoped Labels が重複ラベルを許す (§8.6) からこそ成立する表現で、
   おかげでタプルは単一化・パターン・網羅性・値のすべてでレコードの経路に
   乗り、専用コードがどこにも要りません。その代金をここで払います。

   判定は 2 条件です。**行が閉じている**ことと、**全フィールドが `_item`**
   であること。開いた行はタプルではありません — `{_item: A extends R}` は
   sample.kel:130 の `fst` の引数型で、これは「先頭が A である何か」であって
   1 要素タプルではないからです。ここを緩めると `fst` のシグネチャが
   `(A)` と表示され、行多相であることが読み取れなくなります。

   1 要素のときだけ `(A,)` と末尾コンマを打つのは、`(A)` が
   ただの括弧と区別できないからです。表層構文の側の規約に合わせています。 *)

  let is_tuple_row fields tail =
    (match repr tail with TRowEmpty -> true | _ -> false) && List.for_all (fun (l, _) -> l = l_item) fields
  in

(* ## 9.4 本体 — 型を Keleut の構文に戻す

   `go` が型 1 つを文字列にします。MiniLang の `go` と違って優先順位の
   引数を取りません。Keleut の矢印は引数を必ず括弧付きの並びで書くので
   (`(A) => B`)、`(A => B) => C` のような曖昧さが構文レベルで起きないからです。
   その代わり `go_args` が「引数の閉じた `_item` 行」を括弧の並びに戻します。

   ### 文字列連結の評価順という罠

   `TArrow` のケースだけ `let` で 3 つに分けてあります。これは趣味ではなく、
   実際に表示順が壊れた事故の跡です。OCaml の `^` は関数適用なので、
   引数の評価順は**未規定**であり、実装 (ネイティブ・バイトコードとも) は
   おおむね**右から**評価します。ところが `go` は副作用を持ちます —
   初めて見た型変数に名前を採番する、という副作用です。

   つまり `go_args p ^ 矢印 ^ go r ^ eff_suffix e` と 1 本につないで書くと、
   返り値やエフェクト行の変数が先に採番され、`(B) => A` のように
   **引数より返り値のほうが若い名前になる**。型は読めるのに読みにくい、
   という最悪の壊れ方をします。`let` で順序を固定すれば直ります。
   `TArrow` と `TRecord` の尾部つきの枝がそう書いてあります。

   > 副作用のある関数を `^` で並べない。名前の採番は副作用である。

   `TArrow` だけでなく `TRecord` の尾部つきの枝も同じ壊れ方をして
   いました — `{x: {y: A extends R2} extends R1}` のように、行尾が
   フィールドより若い番号を取る逆順が実機で出ていたのを M19 (G4b) で
   直しました。あわせて、採番を伴う写像は `map_ordered`(適用順が仕様で
   保証されている `List.fold_left` に落とす)に寄せてあります —
   stdlib の `List.map` は現状先頭から適用しますが、仕様としての保証は
   ありません。

   ### レコードとヴァリアント

   レコードは 4 通りに書き分けます。空の閉じた行は `{}`、
   フィールドなしの開いた行は `{extends R1}`、閉じていれば `{x: A, y: B}`、
   開いていれば `{x: A extends R1}`。`extends` は Keleut の表層構文
   そのままです。

   ヴァリアントは `#Even | #Odd` の形。ペイロードがユニットならラベルだけ、
   そうでなければ `#Foo(A)`。尾部の行変数は最後の選択肢として並べます
   (`#Even | #Odd | R1`)。これが sample.kel:145 の `describe` の型の姿です。
   フィールドも尾部も無い行は `#|` と出します。Never 相当 —
   「値が存在しない型」で、選択肢がゼロ個であることを示す記号です。

   `is_unit` が「空レコードかどうか」を見ているのは、Keleut の Unit が
   名目型ではなく空レコードだからです (sample.kel:41,112)。
   `Unit` という名前はプレリュードの型エイリアスとしてしか存在しません。 *)

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
        go h ^ "[" ^ String.concat ", " (map_ordered go args) ^ "]"
    | TArrow (p, r, e) ->
        (* ^ の右辺が先に評価されると命名順が逆になるので let で順序を固定する *)
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
              (* ^ の右辺が先に評価されると尾部の行変数が先に採番される(§9.4。
                 実測で R2 → R1 の逆順が出ていた — M19 / G4b) *)
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
    | TRowExtend _ as row -> eff_row row (* 裸の行はエフェクト行の書式で *)
  and field (l, t) = name_of l ^ ": " ^ go t
  and is_unit t = match repr t with TRecord r -> ( match repr r with TRowEmpty -> true | _ -> false) | _ -> false

(* ## 9.5 引数の行を括弧の並びに戻す

   `TArrow` の第 1 要素は、D5 により**閉じた `_item` 行のレコード**です。
   `(Int32, String) => Boolean` の引数はレコード 1 個であって 2 個ではない、
   というのが Keleut の関数の正体で、arity 検査が行の単一化から出るのは
   このおかげでした (§8.7)。

   ここではその行をタプルの書式に戻します。§9.3 の `is_tuple_row` を
   使いますが、条件を 1 つ緩めています。`fields <> []` を要求しないので、
   引数ゼロの関数が `() => A` と出ます。§9.3 のタプル判定でこれを許すと
   ユニット値 `{}` が `()` になってしまうので、そこでは弾いていました。
   ここは矢印の左だと分かっているので緩められます。

   閉じていない引数行に出会ったら、諦めて `TRecord` としてそのまま出します。
   本来ありえない形ですが、**推論の途中で壊れた型を印字するのが
   プリティプリンタの仕事**なので、ここで例外を投げるわけにはいきません。
   エラーメッセージを出そうとしてエラーで落ちる推論器ほど困るものはありません。 *)

  and go_args p =
    (* TArrow の引数は閉じた _item 行(D5)。開いていても壊れずに出す *)
    match repr p with
    | TRecord row ->
        let fields, tail = row_fields row in
        if is_tuple_row fields tail then "(" ^ String.concat ", " (List.map (fun (_, t) -> go t) fields) ^ ")"
        else go (TRecord row)
    | t -> go t

(* ## 9.6 エフェクト行を隠すとき、見せるとき

   矢印のエフェクト行は 3 通りに扱います。

   | 行の形 | 表示 | 意味 |
   |---|---|---|
   | `TRowEmpty` | 何も出さない | 純粋 (`@ {}`) |
   | 裸の行変数 | 何も出さない | エフェクト多相 (`@` 省略) |
   | ラベルを含む行 | ` @ {Console, ...}` | 具体的なエフェクト |

   前の 2 つを省くのは Koka が total effect を書かない慣習と同じで、
   理由も同じです。ほとんどの関数はこのどちらかであり、全部に `@ {}` や
   `@ R1` が付いた型は読めません。省いても情報は落ちません — 出ていない
   のは「純粋か、多相か」のどちらかで、どちらも「気にしなくてよい」
   という同じ結論に落ちるからです。

   ラベルは引数を 1 つ取れます。引数がユニットなら裸の名前 (`Console`)、
   そうでなければ `Heap[ς1]` のように角括弧で見せます。
   リージョンの取り違えを説明するときに `ς` が見える形になっているのは、
   ここがそう書いてあるからです。

   `eff_row` は裸の行 (`TRowExtend` が直接来た場合) の印字にも使い回されます。
   Keleut では行が単独で型の位置に立つのはエフェクト行のときだけなので、
   これで困りません。 *)

  and eff_row row =
    let fields, tail = row_fields row in
    let label (l, t) = if is_unit t then name_of l else name_of l ^ "[" ^ go t ^ "]" in
    let parts = map_ordered label fields in
    let ext = match repr tail with TRowEmpty -> "" | tail -> (if parts = [] then "extends " else " extends ") ^ go tail in
    "{" ^ String.concat ", " parts ^ ext ^ "}"
  and eff_suffix e =
    (* 空行・裸の行変数は省略(計画 §7.7) *)
    match repr e with
    | TRowEmpty -> ""
    | TVar _ -> ""
    | row -> " @ " ^ eff_row row
  in

(* ## 9.7 制約を角括弧で前置する

   全部の型を印字し終えてから、台帳に溜まった制約を前置します。
   `[A: Add + Mul, F: Functor] (F[A]) => A` の形で、これは Keleut の
   型パラメータ束縛子の構文そのものです。ユーザは制約を見たら
   そのまま `let f[A: Add + Mul]...` と書き写せます(だから前置に
   載るのは Generic と Unbound の変数だけです — §9.2)。

   ここも印字が最後に走る点が重要です。`go` を先に全部走らせないと、
   どの変数に名前が付き、どの制約が実際に登場したかが確定しません。
   だから `strs` を作ってから `ctx` を作る、というこの順序は
   入れ替えられません。§9.4 の評価順の罠と同じ話が、
   もう一段大きな粒度でここにも出ています。

   クラス名は `List.sort compare` で並べます。台帳の順 (= `add_class` が
   合併した順、つまり単一化の順) をそのまま出すと、意味的に同じ型が
   推論の経路によって違う文字列になり、ゴールデンテストが揺れます。
   **表示は決定的でなければテストできない。**

   ### 最後に窓を塞ぐ

   ファイル末尾の `let () = ...` が、第8章 (unify.ml) が開けておいた
   `show_ref` / `show2_ref` の穴を埋めます。これでモジュールの循環を
   避けたまま、単一化のエラーメッセージが本物の型を印字できるようになります。
   このトップレベル副作用がリンクされなければ、型エラーの本文は
   `<型>` だらけになります (§8.2)。 *)

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
  let strs, _ = show_all [ a; b ] in
  match strs with [ x; y ] -> x ^ " と " ^ y | _ -> bug "show2"

let () =
  Unify.show_ref := show;
  Unify.show2_ref := show2
