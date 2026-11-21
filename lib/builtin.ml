(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第13章 プリミティブと組み込み実行環境

   第12章(value.ml)は値の表現を定めた。
   本章は、その値を実際に操作する最も下の層で、次の 3 つを持つ。

   - `__*` プリミティブの実装表。
     加算も文字列の連結もゼロ除算の検査も、最後はここの OCaml 関数に行き着く
   - 組み込み型に対するクラスメソッドの実装(`Add[Int32]` の `add` が何をするか)
   - `with_runtime`。最も外側に 1 つだけ置くエフェクトハンドラ

   本章は、第12章の値の表現とレコード演算、`Op` の宣言を使う。
   第14章(interp.ml)は本章の次の 6 つの名前を使う。

   - 引数レコードから値を取り出す `arg_values` / `arg1` と、値を Boolean として読む `as_bool`(§13.1)
   - `extern` 宣言に実装を結びつける `find_extern`(§13.4)
   - 組み込みメソッドを引く `builtin_method`(§13.5)
   - 最も外側のハンドラ `with_runtime`(§13.6)

   プリミティブは、実装と型を別々の場所に置く。
   実装は本章に置き、型は `lib/prelude.kel` の `extern` 宣言(第15章)に置く。
   プレリュードに `__int32_add` の引数の型と返り値の型を書いた `extern` 宣言が 1 行あれば、
   型検査器はほかの外部関数の宣言と同じ仕組みでそれを読む。
   そのため本章のコードは型を一切扱わず、プレリュードも本章に何が実装されているかを知らない。
   両者をつなぐのは名前の文字列だけである。
   宣言の名前が本章の表にないときは、
   第14章の `DExtern` の分岐が、呼ばれた時点で `未実装のプリミティブ` の実行時エラーにする。 *)
open Syntax
open Value

(* ## 13.1 引数レコードを位置で読む

   Keleut の関数は複数の引数を取って 1 個の値を返し、
   引数の個数(arity)は矢印型の一部である(sample.kel:273-275)。
   呼び出し規約もこれに合わせ、引数を並べたレコードを 1 個渡す形に統一してある。
   ユーザ関数もプリミティブも同じ形で呼ぶ(第12章 §12.2)。

   そのため `arg_values` はラベルを捨て、値だけを順に取り出す。
   呼び出し元(第14章の `Apply`)が引数をソースの順に並べたレコードを作るので、
   位置と引数は一対一に対応する。
   `extern` 宣言に書く引数名は型を与えるためだけのもので、実行時には使わない。

   `as_i32` などの検査は、型検査の健全性が破れたときに備えるものである。
   型検査に通ったプログラムなら、`__int32_add` に文字列が渡ることはない。
   しかし健全性が破れると、その影響を最初に受けるのはこの層である。
   たとえば `__int32_add` を、第 1 引数が String の関数として `extern` で再宣言できれば、
   偽の型で型検査に通して、ここに文字列を渡せる。
   第6章(decls.ml)の登録簿はこの再宣言を拒否するが、この層の検査も残しておく。

   この検査で検出できるのは、値の種類が実装の期待と違う場合だけである。
   返り値の型を偽る宣言(Boolean を返す実装を Int32 と偽るなど)では、値が検査を受けずにそのまま返り、
   型検査が Int32 とした式が実行時に false と表示される。
   この種の誤りを防ぐのはこの層の検査ではなく、第6章の登録簿と、
   第15章 §15.5 の `extern` 一覧が実装表のすべての名前を宣言していることである。 *)

let arg_values v = List.map snd (record_fields v)

let arg1 v = match arg_values v with [ a ] -> a | _ -> runtime_error "プリミティブの引数が1個ではありません"

let arg2 v = match arg_values v with [ a; b ] -> (a, b) | _ -> runtime_error "プリミティブの引数が2個ではありません"

let as_i32 = function VInt32 n -> n | v -> runtime_error ("Int32 ではありません: " ^ show v)

let as_i64 = function VInt64 n -> n | v -> runtime_error ("Int64 ではありません: " ^ show v)

let as_f64 = function VFloat64 f -> f | v -> runtime_error ("Float64 ではありません: " ^ show v)

let as_text = function VText s -> s | v -> runtime_error ("String ではありません: " ^ show v)

let as_bool = function VBool b -> b | v -> runtime_error ("Boolean ではありません: " ^ show v)

(* ## 13.2 Float64 の表示器 `float_repr`

   Float64 の表示器 `float_repr` は、第12章 §12.7 にある。
   診断用の表示(§12.7 の `show`)と、
   ユーザに見える `Show[Float64]`(§13.5)が同じ表示器を使うためである。
   そのため、Float64 の値が診断と `show` で違う表記になることはない。
   本章からは `open Value` を通して `float_repr` が見える。

   `float_repr` は値を丸めずに表示する。
   絶対値が 1e16 未満の整数値は小数点表記で出し、
   それ以外の有限値は、読み戻して同じ値になる表記のうち、有効数字の桁数が最も少ないものを出す。
   §12.7 は、出力を `float_of_string` で読み戻すと元の値になることと、
   有限値を Keleut の Float64 リテラルとして読み戻せることの 2 つの要件に加えて、
   非有限値の表示と NaN の符号の扱いを述べている。 *)

(* ## 13.3 C リンケージの既知名

   C リンケージの `extern` はダミーである。
   Diktor は本物の C FFI を実装せず、§13.4 の `c_prims` 表にある既知名だけを実装している。
   既知名は sin / cos / sqrt / exp / log の 5 つである。

   prim リンケージのプリミティブと違って、C の既知名にはプレリュードが型を与えられない。
   sample.kel が C リンケージの `sin` を自分で宣言するので、
   プレリュードが先に宣言すると、再宣言が拒否されて、仕様が型検査に通らなくなる。
   そこで、既知名 5 つの型は、第11章の `DExtern` の分岐が第6章 §6.2b のシグネチャと比べる。
   表にない未知の名前の宣言は、比べずに受理する。
   本物の C FFI の宣言が正しいかどうかは、処理系には確かめられないからである。

   `@ Blocking` を付けたか `@` を省略した既知名は、トップレベルから直接呼べる(仕様 §12、
   `test/blocking_top.t`、`test/extern_c_blocking.t`)。
   行を注釈で閉じた文脈へ持ち込むときは、`pinned`(§6.11b / §14.10)で `Blocking` を取り除く。
   `Blocking` を取り除くのは型の上だけの操作で、
   実行時の `pinned` は引数の関数を呼び、その結果をそのまま返すだけである。 *)

(* ## 13.4 プリミティブ表

   表の実装は単純である。
   `(名前, 引数レコード -> 値)` の連想リストが、リンケージごとに 1 つある。
   prim リンケージの `prims` と、C リンケージの `c_prims` である。
   引数を 2 つ取り出し、型を検査し、結果を値に包み直すという定型の処理は、
   `i32_bin` などのコンビネータが行う。
   そのため、表の各行には演算そのものだけを書けばよい。

   表を 2 つに分けるのは、リンケージによって結びつく実装を変えるためである。
   1 つの表を `extern` の ABI を見ずに引くと、C リンケージの宣言が `__string_le` の実装に、
   prim リンケージの宣言が C の既知名 `cos` の実装に結びついてしまう。
   `find_extern ~abi` は宣言の ABI で表を選ぶので、選んだ表に名前がない宣言は、
   呼ばれた時点で `未実装のプリミティブ` の実行時エラーになる。
   ABI の文字列そのものの検査(prim と C 以外の拒否)は、第11章の `DExtern` の分岐にある。

   この表には、数値と文字列の扱いについての次の規則が現れる。

   ゼロ除算は実行時エラーにし、整数のオーバーフローは折り返す(wrap-around)。
   折り返すと、2 の補数で下位のビットだけが残る。
   前者は `div_check_*` / `rem_check_*` が実装し、
   後者は `Int32.add` などをそのまま使う行が実装する。
   オーバーフローを折り返すのは仕様でも暫定の扱いで(sample.kel:120)、
   検査付きの算術に変えるなら、この表の数行を差し替えるだけで済む。

   Float64 の等価と比較は、どちらも IEEE 754 に従う。
   OCaml の多相の `compare` は、NaN を全順序の最小の値として扱い、自分自身と等しいとみなす。
   そのまま使うと、`nan == nan` が真になり、`nan < 1.0` も真になる。
   そこで等価(`__float64_eq`)はコンビネータを使わずに浮動小数の `=` を直接使い、
   比較(`f64_cmp`)は先頭で NaN を調べる。
   どちらかが NaN なら、lt / le / gt / ge の 4 つはすべて偽になる。
   NaN を除いた範囲では `compare` は IEEE の順序と一致し、
   ±0.0 についても `compare` が 0 を返すので、`le` / `ge` が真になって IEEE とそろう。
   等価と比較を同じ規則にそろえるのは、片方だけが IEEE に従うと矛盾が生じるからである。
   等価だけを IEEE に従わせて比較を `compare` のままにすると、
   `nan == nan` が偽なのに `nan <= nan` が真になる。

   その結果、Float64 の順序は全順序ではない。
   `nan <= nan` も偽なので反射律が成り立たず、`<=` は厳密には半順序でもない。
   `<` は狭義半順序で、`<=` は NaN を除いた部分集合の上でだけ全前順序である。
   NaN は、自分自身を含むすべての値と比較できない。
   `Ord` クラスは順序の公理を何も保証しない。

   全順序が必要な場面の書き方は、仕様でも未定である。
   仕様は §14(sample.kel:868-873)で、
   `Ord[Float64]` と `Eq[Float64]` と NaN の扱いを未決の課題として 2 つの案に整理している。
   案(1)は「newtype で包んだ TotalFloat64 だけが Ord と Eq を実装する」で、
   sample.kel:259 の `newtype TotalFloat64(Float64)` がその例である。
   ただし仕様は、`TotalFloat64` に `Ord` を実装するかどうかを未定と注記している(sample.kel:259)。
   仕様が `Eq[Float64]` も並べて挙げているのは、等価でも反射律が成り立たないからである。
   構造的な `Eq` はフィールドへ再帰するので、
   `Float64` のフィールドを 1 つ持つレコードも反射律を失う(sample.kel:870)。
   たとえば `{x = 0.0 / 0.0}` は自分自身と等しくない。

   `__string_sub` は、範囲外の指定を実行時エラーにする。
   OCaml の `Invalid_argument` をそのまま外へ出すと、
   第16章(driver.ml)の終了コードの規約から外れた例外がユーザに見えてしまう。
   同じ理由で、`__panic` は `Runtime_error` を投げる。

   Float64 から整数への変換は、表現できる値がなければ実行時エラーにする。
   `Int32.of_float` / `Int64.of_float` は、範囲外や NaN に対する結果が未規定で、
   x86 では黙って INT_MIN を返す。
   整数算術の折り返しと扱いを分けるのは、算術は常に表現できる値を返すのに対し、
   変換には返せる値がない場合があるからである。
   この扱いは、ゼロ除算や範囲外の数値リテラル(第14章)の扱いとそろえている。
   `f64_to_int` が上限を、変換先の型の最小値の符号を反転した値より小さいかどうかで判定するのは、
   `Int64.to_float Int64.max_int` が最も近い値の 2^63 に丸められ、上限の境界に使えないからである。
   切り捨てた後の値は整数なので、2^31 未満という条件は 2^31 - 1 以下と同じになる。
   Int64 から Int32 への変換 `__i64_to_i32` は折り返しのままで、整数算術の扱いにそろえている。
   変換 6 つのすべて、整数算術のオーバーフロー、String がバイト列であること、`Char` がないことは、
   `test/numeric.t` のゴールデンテストが固定している。
   変換 6 つのうち、失敗することがあるのは `__f64_to_i32` と `__f64_to_i64` の 2 つである。

   プリミティブ表は連想リストなので、引くたびに線形探索になる。
   表を引くのは、`extern` 宣言に実装を結びつけるとき(`find_extern`。宣言 1 つにつき 1 回)と、
   §13.5 のメソッド表を起動時に解決するとき(`find_prim`)だけである。
   演算のたびの探索は、§13.5 のハッシュ表と、
   第14章の辞書のキャッシュ(`closed_cache`。§14.6)が行う。 *)

  (* ---- __* プリミティブ表(名前 → 実装)。型は prelude.kel の extern が与える ---- *)

let i32_bin f = fun v -> let a, b = arg2 v in VInt32 (f (as_i32 a) (as_i32 b))

let i64_bin f = fun v -> let a, b = arg2 v in VInt64 (f (as_i64 a) (as_i64 b))

let f64_bin f = fun v -> let a, b = arg2 v in VFloat64 (f (as_f64 a) (as_f64 b))

let i32_cmp f = fun v -> let a, b = arg2 v in VBool (f (Int32.compare (as_i32 a) (as_i32 b)) 0)

let i64_cmp f = fun v -> let a, b = arg2 v in VBool (f (Int64.compare (as_i64 a) (as_i64 b)) 0)

(* IEEE 754 に従い、どちらかが NaN なら lt/le/gt/ge は 4 つとも偽にする。
   OCaml の多相の compare は NaN を全順序の最小の値として扱うので、
   そのまま使うと nan < 1.0 が真になる *)
let f64_cmp f =
 fun v ->
  let a, b = arg2 v in
  let x = as_f64 a and y = as_f64 b in
  VBool ((not (Float.is_nan x)) && (not (Float.is_nan y)) && f (compare x y) 0)

let div_check_i32 a b = if b = 0l then runtime_error "ゼロ除算です" else Int32.div a b

let div_check_i64 a b = if b = 0L then runtime_error "ゼロ除算です" else Int64.div a b

let rem_check_i32 a b = if b = 0l then runtime_error "ゼロ除算です" else Int32.rem a b

let rem_check_i64 a b = if b = 0L then runtime_error "ゼロ除算です" else Int64.rem a b

(* Float64 から整数への変換は、表現できる値がなければ実行時エラーにする(§13.4)。
   lo は変換先の型の最小値を float にした値である。
   上限を -.lo より小さいと書くのは、Int64.to_float Int64.max_int が
   最も近い値の 2^63 に丸められ、上限の境界に使えないからである。
   切り捨てた後の t は整数値なので、最大値以下という条件と同じになる *)
let f64_to_int name lo f =
  if Float.is_nan f then runtime_error (name ^ ": NaN は整数に変換できません")
  else
    let t = Float.trunc f in
    if t >= lo && t < -.lo then t else runtime_error (name ^ ": 変換結果が範囲外です: " ^ float_repr f)

let prims : (string * (t -> t)) list =
  [
    ("__int32_add", i32_bin Int32.add);
    ("__int32_sub", i32_bin Int32.sub);
    ("__int32_mul", i32_bin Int32.mul);
    ("__int32_div", i32_bin div_check_i32);
    ("__int32_rem", i32_bin rem_check_i32);
    ("__int32_neg", fun v -> VInt32 (Int32.neg (as_i32 (arg1 v))));
    ("__int32_eq", i32_cmp ( = ));
    ("__int32_lt", i32_cmp ( < ));
    ("__int32_le", i32_cmp ( <= ));
    ("__int32_gt", i32_cmp ( > ));
    ("__int32_ge", i32_cmp ( >= ));
    ("__int64_add", i64_bin Int64.add);
    ("__int64_sub", i64_bin Int64.sub);
    ("__int64_mul", i64_bin Int64.mul);
    ("__int64_div", i64_bin div_check_i64);
    ("__int64_rem", i64_bin rem_check_i64);
    ("__int64_neg", fun v -> VInt64 (Int64.neg (as_i64 (arg1 v))));
    ("__int64_eq", i64_cmp ( = ));
    ("__int64_lt", i64_cmp ( < ));
    ("__int64_le", i64_cmp ( <= ));
    ("__int64_gt", i64_cmp ( > ));
    ("__int64_ge", i64_cmp ( >= ));
    ("__float64_add", f64_bin ( +. ));
    ("__float64_sub", f64_bin ( -. ));
    ("__float64_mul", f64_bin ( *. ));
    ("__float64_div", f64_bin ( /. ));
    ("__float64_neg", fun v -> VFloat64 (-.as_f64 (arg1 v)));
    ("__float64_eq", fun v -> let a, b = arg2 v in VBool (as_f64 a = as_f64 b) (* IEEE: NaN <> NaN *));
    ("__float64_lt", f64_cmp ( < ));
    ("__float64_le", f64_cmp ( <= ));
    ("__float64_gt", f64_cmp ( > ));
    ("__float64_ge", f64_cmp ( >= ));
    ("__string_concat", fun v -> let a, b = arg2 v in VText (as_text a ^ as_text b));
    ("__string_eq", fun v -> let a, b = arg2 v in VBool (String.equal (as_text a) (as_text b)));
    ("__string_lt", fun v -> let a, b = arg2 v in VBool (String.compare (as_text a) (as_text b) < 0));
    ("__string_le", fun v -> let a, b = arg2 v in VBool (String.compare (as_text a) (as_text b) <= 0));
    ("__string_gt", fun v -> let a, b = arg2 v in VBool (String.compare (as_text a) (as_text b) > 0));
    ("__string_ge", fun v -> let a, b = arg2 v in VBool (String.compare (as_text a) (as_text b) >= 0));
    ("__string_length", fun v -> VInt32 (Int32.of_int (String.length (as_text (arg1 v)))));
    ( "__string_sub",
      fun v ->
        match arg_values v with
        | [ s; pos; len ] -> (
            try VText (String.sub (as_text s) (Int32.to_int (as_i32 pos)) (Int32.to_int (as_i32 len)))
            with Invalid_argument _ -> runtime_error "__string_sub: 範囲外です")
        | _ -> runtime_error "__string_sub の引数が3個ではありません" );
    ("__i32_to_i64", fun v -> VInt64 (Int64.of_int32 (as_i32 (arg1 v))));
    ("__i32_to_f64", fun v -> VFloat64 (Int32.to_float (as_i32 (arg1 v))));
    ("__i64_to_i32", fun v -> VInt32 (Int64.to_int32 (as_i64 (arg1 v))));
    ("__i64_to_f64", fun v -> VFloat64 (Int64.to_float (as_i64 (arg1 v))));
    ("__f64_to_i32", fun v -> VInt32 (Int32.of_float (f64_to_int "__f64_to_i32" (Int32.to_float Int32.min_int) (as_f64 (arg1 v)))));
    ("__f64_to_i64", fun v -> VInt64 (Int64.of_float (f64_to_int "__f64_to_i64" (Int64.to_float Int64.min_int) (as_f64 (arg1 v)))));
    ("__show_int32", fun v -> VText (Int32.to_string (as_i32 (arg1 v))));
    ("__panic", fun v -> runtime_error ("panic: " ^ as_text (arg1 v)));
  ]

(* extern C の既知名の表。Diktor は本物の C FFI を実装していない。
   prim 表と分けるのは、リンケージによって結びつく実装を変えるためである。
   既知名のシグネチャは第6章 §6.2b の表にある。
   実装だけ追加してシグネチャを忘れると、その名前は §6.2b の表にない名前と同じく、
   シグネチャと比べずに受理され、型を偽った宣言でも実装に結びつく。
   §13.1 の検査で検出できるのは、値の種類の違いだけである。
   シグネチャだけ追加して実装を忘れると、
   呼んだ時点で「未実装のプリミティブ」の実行時エラーになる *)
let c_prims : (string * (t -> t)) list =
  [
    ("sin", fun v -> VFloat64 (sin (as_f64 (arg1 v))));
    ("cos", fun v -> VFloat64 (cos (as_f64 (arg1 v))));
    ("sqrt", fun v -> VFloat64 (sqrt (as_f64 (arg1 v))));
    ("exp", fun v -> VFloat64 (exp (as_f64 (arg1 v))));
    ("log", fun v -> VFloat64 (log (as_f64 (arg1 v))));
  ]

(* prim 表だけを引く。§13.5 の組み込みメソッド表を作るときに使う *)
let find_prim name = List.assoc_opt name prims

(* extern 宣言に実装を結びつけるときはこちらを使う。
   宣言の ABI で表を選ぶので、選んだ表に名前がない宣言
   (C リンケージの __* や、prim リンケージの sin)は None になり、
   呼ばれた時点で「未実装のプリミティブ」の実行時エラーになる *)
let find_extern ~abi name =
  match abi with "prim" -> List.assoc_opt name prims | "C" -> List.assoc_opt name c_prims | _ -> None

(* ## 13.5 組み込みインスタンスの実装

   `builtin_method` は (クラス名, 型構成子名, メソッド名) から実装を引く。
   第14章の `select_method` は、辞書の (クラス, 型構成子) でユーザが宣言したインスタンスの表を引き、
   なければここを引く(§14.6)。
   組み込みを後に引くこの順序は意図したものだが、順序だけでは組み込みの実装を守れない。

   仮にユーザが `type instance Add[Int32]` を再宣言して実装を差し替えられたとすると、
   型検査(elab)は組み込みの `Add[Int32]` で型を付けるのに、実行時にはユーザの実装が使われる。
   たとえば `add` を引き算として宣言すれば、`2 + 3` が `-1` になってしまう。
   そこで第6章は、組み込みのキーと同じ (クラス, 型構成子) のインスタンス宣言を、
   宣言の時点で標準環境のインスタンスの再宣言として拒否する。
   つまり組み込みの実装は、本節の表を引くときではなく、インスタンスを登録する段階で守る。

   `Show` の分岐が呼ぶ `float_repr` は、第12章 §12.7 の表示器である(§13.2)。
   診断用の表示(§12.7 の `show`)も同じ表示器を使うので、Float64 については、
   ユーザに見える `show(x)` と実行時エラーの中の値の表示が食い違わない。
   ほかの型では食い違う。
   String の診断は引用符で囲んでエスケープした表記を出すが、ユーザの `show` は文字列をそのまま返す。
   ユーザが `Show` のインスタンスを与えた型でも、診断は値の構造をそのまま表示する。
   この食い違いは役割の違いによる。
   診断は値の構造を示し、`show` はユーザに見せるための文字列を返す。

   表は 44 行を明示的に書き、名前を組み立てる規則を置かない。
   仮にメソッド名をワイルドカードで受けて、`__int32_ ^ m` のようにプリミティブ名を組み立てるとする。
   すると、`Ord` に別の名前のメソッドが来たとき、
   同じ名前のプリミティブがたまたまあれば、それが選ばれてしまう。
   名前を組み立てる行が誤ったプリミティブを選ばないかどうかは、
   ほかの 3 つのファイルの不変条件がすべて成り立つかどうかで決まる。

   `builtin_method_table` は起動時に作るハッシュ表である。
   `builtin_method_prims` の 39 行はプリミティブ名で書いてあり、
   表に入れる前にプリミティブ表を引いて実装に解決する。
   `builtin_method_direct` の 5 行は OCaml で直接書いた実装で、そのまま表に入れる。
   そのため、プリミティブ名の書き誤りは最初の起動で `[BUG]` のエラーになり、
   呼び出しは表の中の位置に依存しない 1 回の検索で済む。
   キー(クラス名、型構成子名、メソッド名)の書き誤りは起動時には検査しない。
   キーを書き誤った行のメソッドを呼ぶと、第14章の `select_method` は本節の表から実装を引けない。
   組み込みの (クラス, 型構成子) は第6章のインスタンス表に登録してあるので、
   `select_method` は、ユーザのインスタンスを宣言より前の位置で使ったときと同じ実行時エラーを出す(§14.6)。
   そのエラーのメッセージからは、表の書き誤りが原因であることは分からない。 *)

  (* ---- 組み込みクラスメソッドの実装表: (クラス, 型構成子, メソッド) → 実装 ---- *)

(* 組み込みインスタンスの実装を (クラス, 型構成子, メソッド) で引く表。
   名前を組み立てる規則は置かず、下の builtin_method_direct と合わせて
   44 行をすべて書く。この 44 行は、第6章の組み込みインスタンスの
   (クラス, 型構成子, メソッド) の組(Add 4 / Sub 3 / Mul 3 / Div 3 / Rem 2 /
   Neg 3 / Eq 5 / Ord 16 / Show 5 = 44)と一致させる *)
let builtin_method_prims : ((string * string * string) * string) list =
  [
    (("Add", "Int32", "add"), "__int32_add");
    (("Add", "Int64", "add"), "__int64_add");
    (("Add", "Float64", "add"), "__float64_add");
    (("Add", "String", "add"), "__string_concat");
    (("Sub", "Int32", "sub"), "__int32_sub");
    (("Sub", "Int64", "sub"), "__int64_sub");
    (("Sub", "Float64", "sub"), "__float64_sub");
    (("Mul", "Int32", "mul"), "__int32_mul");
    (("Mul", "Int64", "mul"), "__int64_mul");
    (("Mul", "Float64", "mul"), "__float64_mul");
    (("Div", "Int32", "div"), "__int32_div");
    (("Div", "Int64", "div"), "__int64_div");
    (("Div", "Float64", "div"), "__float64_div");
    (("Rem", "Int32", "rem"), "__int32_rem");
    (("Rem", "Int64", "rem"), "__int64_rem");
    (("Neg", "Int32", "neg"), "__int32_neg");
    (("Neg", "Int64", "neg"), "__int64_neg");
    (("Neg", "Float64", "neg"), "__float64_neg");
    (("Eq", "Int32", "eq"), "__int32_eq");
    (("Eq", "Int64", "eq"), "__int64_eq");
    (("Eq", "Float64", "eq"), "__float64_eq");
    (("Eq", "String", "eq"), "__string_eq");
    (("Ord", "Int32", "lt"), "__int32_lt");
    (("Ord", "Int32", "le"), "__int32_le");
    (("Ord", "Int32", "gt"), "__int32_gt");
    (("Ord", "Int32", "ge"), "__int32_ge");
    (("Ord", "Int64", "lt"), "__int64_lt");
    (("Ord", "Int64", "le"), "__int64_le");
    (("Ord", "Int64", "gt"), "__int64_gt");
    (("Ord", "Int64", "ge"), "__int64_ge");
    (("Ord", "Float64", "lt"), "__float64_lt");
    (("Ord", "Float64", "le"), "__float64_le");
    (("Ord", "Float64", "gt"), "__float64_gt");
    (("Ord", "Float64", "ge"), "__float64_ge");
    (("Ord", "String", "lt"), "__string_lt");
    (("Ord", "String", "le"), "__string_le");
    (("Ord", "String", "gt"), "__string_gt");
    (("Ord", "String", "ge"), "__string_ge");
    (* Show[Int32] は、プレリュードが extern で宣言する __show_int32 と同じ実装を使う *)
    (("Show", "Int32", "show"), "__show_int32");
  ]

(* プリミティブ名を持たない実装は OCaml で直接書く *)
let builtin_method_direct : ((string * string * string) * (t -> t)) list =
  [
    (("Eq", "Boolean", "eq"), fun v -> let a, b = arg2 v in VBool (as_bool a = as_bool b));
    (("Show", "Int64", "show"), fun v -> VText (Int64.to_string (as_i64 (arg1 v))));
    (("Show", "Float64", "show"), fun v -> VText (float_repr (as_f64 (arg1 v))));
    (("Show", "String", "show"), fun v -> VText (as_text (arg1 v)));
    (("Show", "Boolean", "show"), fun v -> VText (string_of_bool (as_bool (arg1 v))));
  ]

(* 起動時に 1 度だけプリミティブ名を解決し、ハッシュ表に格納する。
   プリミティブ名の書き誤りは、最初の起動で [BUG] のエラーにする。
   キーの書き誤りは検査しない。組み込みのインスタンスは第6章の表にあるので、
   書き誤ったメソッドを呼ぶと、select_method は宣言より前の使用と同じ実行時エラーを出す *)
let builtin_method_table : (string * string * string, t -> t) Hashtbl.t =
  let tbl = Hashtbl.create 64 in
  List.iter
    (fun (key, prim) ->
      match find_prim prim with
      | Some f -> Hashtbl.replace tbl key f
      | None -> raise (Aux.Panic ("[BUG] 組み込みメソッド表のプリミティブ名が解決できません: " ^ prim)))
    builtin_method_prims;
  List.iter (fun (key, f) -> Hashtbl.replace tbl key f) builtin_method_direct;
  tbl

let builtin_method cls con meth : (t -> t) option = Hashtbl.find_opt builtin_method_table (cls, con, meth)

(* ## 13.6 最も外側のハンドラ `with_runtime`

   Keleut のトップレベルは純粋ではない。
   プログラムは、ランタイムが提供するエフェクトを起こせる状態で実行される(第7章(prims.ml)の一覧)。
   そのうち操作を持つのは `Console` だけである。
   `Blocking` は操作を持たないので、このハンドラには届かない。
   ランタイムが提供するエフェクトを実際に処理するのは、第14章の評価の全体を囲むこのハンドラである。

   `Effect.Deep.match_with` の 3 つのフィールドのうち、`retc` は恒等関数で、
   `exnc` は受け取った例外をそのまま投げ直す。
   つまりこのハンドラは値と例外をそのまま通し、自分の知っている操作だけを受け取る。
   ただし、これは `retc` と `exnc` についての話で、`effc` の中で起きた例外は別に扱う。
   第14章 §14.9 の 3 つの経路の規約は、この最も外側のハンドラにも同じく当てはまる。
   `sink` への書き込みが例外を投げたら、`discontinue` を使って、破棄する継続にその例外を届ける。
   `discontinue` を使わずに `raise` すると、破棄した継続の中の cancel 節が実行されない。
   第14章で、節の本体が resume だけである場合の短い経路が、
   引数の評価で起きた例外を `discontinue` するのと同じ理由である。

   `sink` が実際に例外を投げるのは、標準出力への書き込みが失敗したときである。
   このとき cancel 節の出力は同じ壊れた標準出力へ行くので観測できないが、
   cancel 節の例外は抑制の記録(stderr)に出る。
   `test/eval.t` のゴールデンテストは、この抑制の記録を観測点にしている。
   標準出力を閉じてバッファをあふれさせ、cancel 節の `__panic` が抑制の記録に現れることを確かめる。
   記録が出れば、例外が fiber へ届いたこと、
   つまり `discontinue` が実行されたことの直接の証拠になる。

   未知の `Op` には `None` を返して外へ通す。
   その外側にはハンドラがないので、`Effect.Unhandled` になる。
   この例外を、操作名を含むメッセージに変えるのは第16章(driver.ml)である。
   既定の例外の表示は `Op` の内容を出さないので、
   driver は `Effect.Unhandled (Op (op, _))` という形を直接照合し、そこから操作名を取り出す。
   `Printexc.register_printer` で表示関数を登録することはしない。
   照合する箇所が 1 か所しかないなら、グローバルに表示関数を登録するより、
   その 1 か所でパターンを書くほうが小さく済む。

   - `Console.write` の文字列は `sink` へ送る。
     出力先を引数にしたのは、テストが第16章の `eval_string ~sink` を通して出力を受け取れるようにするためである。
     コマンドラインからの実行では `print_string` を渡す。
     `Console` はユーザが `handle` で処理できないエフェクトで、
     第11章はプレリュードが所有する `Console` に対する `case Console.write(s) => ...` を型エラーにする。
     内側の `handle` が先に受け取ることを許すと、
     出力を黙って捨てるハンドラが書けてしまうからである。
     そのため、プレリュードが所有する `Console.write` は必ずこのハンドラに届く。
     出力先をプログラムの側で差し替えたいときは、ユーザがハンドルできる `Print` にハンドラを書く。
     プレリュードの `with_stdout` が `Print.print` を `Console.write` に置き換える
   - 対話的な実行(第16章 §16.6b)では、引数 `print` を真にして、
     `Print.print` の文字列も `sink` へ送る。
     トップレベルの `println` をハンドラなしで出力するためである。
     ユーザの `handle` と `with_stdout` は内側で先に `Print` を受け取るので、意味は変わらない

   本章は操作名を `Type.intern` した `oid` で持つので、`effc` の中では整数の比較しかしない。
   非修飾の `write` を `Console.write` へ解決するのは第11章なので、ここで名前を解決する必要はない。

   本節は、エフェクトのプロトコル(`Op` と `Unwind`)を使う側である。
   宣言は第12章 §12.5 にある。
   節の 3 つの経路、`discontinue` が必要な理由、cancel の LIFO、ハンドラの起動の id は、
   ハンドラの実装を説明する第14章で扱う。 *)

  (* ---- ランタイムエフェクトのハンドラ(最も外側に 1 つだけ置く) ---- *)

let op_console_write = Type.intern "Console.write"

let op_print_print = Type.intern "Print.print"

(* print が真なら、Print.print も Console.write と同じく sink へ送る(対話的な実行。第16章) *)
let with_runtime ?(print = false) ~(sink : string -> unit) (f : unit -> t) : t =
  Effect.Deep.match_with f ()
    {
      retc = Fun.id;
      exnc = raise;
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Op (op, args) when op = op_console_write || (print && op = op_print_print) ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  (* 第14章 §14.9 の 3 つの経路と同じ規約。sink が例外を投げても、
                     破棄する継続に例外を届ける。continue は値の分岐にあり、
                     例外を捕捉する範囲の外なので、末尾呼び出しのままになる *)
                  match sink (as_text (arg1 args)) with
                  | () -> Effect.Deep.continue k unit
                  | exception ex -> Effect.Deep.discontinue k ex)
          | _ -> None);
    }
