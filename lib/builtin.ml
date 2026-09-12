(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第13章 — プリミティブと組み込み実行環境

   第12章 (value.ml) が値の形を決めました。本章はその値を実際に動かす
   **一番下の層**です。三つのものが入っています。

   - `__*` プリミティブの実装表。加算も文字列連結もゼロ除算の検査も、
     結局はここの OCaml 関数に落ちます
   - 組み込み型に対するクラスメソッドの実体
     (`Add[Int32]` の `add` が何をするか)
   - `with_runtime` — 最外周に 1 枚だけ敷くエフェクトハンドラ

   受け取るもの: 第12章の値表現とレコード演算、そして `Op` の宣言。
   渡すもの: 第14章 (interp.ml) が使う面はいくつかあります。引数レコードの
   取り出し (`arg_values` / `arg1` / `as_bool`、§13.1)、プリミティブ表を引く
   `find_prim`、組み込みメソッドを引く `builtin_method`、張りぼてファイル
   システムの `fs` / `handles`(§13.3)、そして最外周ハンドラ `with_runtime`。
   数え上げると 8 つの名前で、いちばん多く呼ばれるのは地味な `as_bool` です。

   本章を貫く方針は分業です。**プリミティブの実装はここ、型は
   `lib/prelude.kel` の `extern` 宣言**(計画 §8.6。第15章)。
   prelude に `__int32_add` の引数型と返り値型を書いた `extern` 宣言が
   1 行あれば、型検査器は他の外部宣言と同じ機構でそれを読みます。
   おかげでこのファイルは型を一切知りません。逆に prelude はここに何が
   実装されているかを知りません。**両者を繋いでいるのは名前の文字列だけ**で、
   繋ぎ損ねたときは第14章の `DExtern` の枝が
   「未実装のプリミティブ」という実行時エラーにします。

   > 型と実装を別のファイルに置くなら、繋ぎ目に必ずエラー経路を用意する。 *)
open Syntax
open Value

(* ## 13.1 引数はいつもレコード、読むのは位置

   Keleut の関数は多値を取り単値を返し、arity は矢印型の一部です
   (sample.kel:235-237)。呼び出し規約はそれをそのまま写して
   「引数を並べたレコードを 1 個渡す」に統一されており、ユーザ関数も
   プリミティブも同じ形で呼ばれます(第12章 §12.2)。

   だから `arg_values` は**ラベルを捨てて値だけを順に取り出します**。
   乱暴に見えますが、呼び出し側(第14章の `Apply`)が引数をソース順に
   並べたレコードを作るので、位置と引数は一対一です。`extern` 宣言に
   書いてある引数名は型を与えるためだけにあり、実行時には使いません。

   `as_i32` などの検査も同じ性格です。型検査を通ったプログラムなら
   `__int32_add` に文字列が来ることはありません — **来ないはずです**。
   それでも検査を残すのは、この層が型検査の外から呼ばれうるからです。
   実際、260829-2b の敵対的検証では
   `__int32_add` を第 1 引数が String の関数として `extern` 再宣言する、という
   嘘の型でここに文字列を届かせることができました。穴は登録簿での再宣言拒否
   (第6章 (decls.ml))で塞ぎましたが、**型検査の健全性が破れたときに
   最初に踏まれる床**がここである以上、床は張ったままにしておきます。

   ただし床が受け止められるのは「値の形が違う」場合だけです。返り値の型を
   偽る宣言 — Boolean を返す実装を Int32 と偽るなど — では値がそのまま
   通り抜け、型検査が Int32 と言った式が実行時に false と表示されるところ
   まで実測しました。頼るべきは床ではなく、第6章の登録簿と第15章 §15.5 の
   一覧の完備性です。 *)

let arg_values v = List.map snd (record_fields v)

let arg1 v = match arg_values v with [ a ] -> a | _ -> runtime_error "プリミティブの引数が1個ではありません"

let arg2 v = match arg_values v with [ a; b ] -> (a, b) | _ -> runtime_error "プリミティブの引数が2個ではありません"

let as_i32 = function VInt32 n -> n | v -> runtime_error ("Int32 ではありません: " ^ show v)

let as_i64 = function VInt64 n -> n | v -> runtime_error ("Int64 ではありません: " ^ show v)

let as_f64 = function VFloat64 f -> f | v -> runtime_error ("Float64 ではありません: " ^ show v)

let as_text = function VText s -> s | v -> runtime_error ("String ではありません: " ^ show v)

let as_bool = function VBool b -> b | v -> runtime_error ("Boolean ではありません: " ^ show v)

(* ## 13.2 `float_repr` — 表示は丸めではない(実装は第12章へ)

   もとはこの場所に Float64 の表示器がありました。260829-2b の敵対的検証で
   `string_of_float`(`%.12g` 相当)が `0.1 + 0.2` を `0.3` と表示する —
   表示器が嘘をつく — という欠陥を見つけ、最短往復表現に直した現場です。

   いまは実装ごと第12章 §12.7 へ移してあります。診断用の印字(§12.7 の
   `show`)とユーザに見える `Show[Float64]`(§13.5)が**同じ表示器**を
   使うためです (D27)。この章から `float_repr` が見えるのは `open Value`
   経由。要件の全文 — `float_of_string` に対する往復、有限値は Keleut の
   Float64 リテラルとして読み戻せること、非有限値の表示と NaN の符号の
   扱い — も §12.7 にまとまっています。節番号は詰めずに、この節を
   道しるべとして残します。

   > 表示は丸めではない。読み戻して同じ値になる最短の字面が正しい。 *)

(* ## 13.3 ファイルは張りぼてである

   `__open` / `__read` / `__write` / `__close` は本物のファイルを触りません。
   メモリ上のハッシュ表 2 枚 — パス から 内容 への `fs` と、
   ハンドル から パス への `handles` — がその正体です。

   なぜこれで足りるか。これらのプリミティブが存在する理由は
   sample.kel:525-530 の `with_file` を**動かして見せる**ことであって、
   ファイル入出力そのものではないからです。示したいのは
   「ハンドラが資源を握り、正常終了なら `return` 節で、外側が継続を捨てたなら
   `cancel` 節で `__close` が走る」という制御の筋(sample.kel:529-530)であって、
   その筋はダミーでも本物と同じに走ります。

   代わりに正直であることを選びます。**これは張りぼてです。**
   `__read` は書いた覚えのないパスに空文字列を返しますし、
   ハンドルは単調増加で再利用されず、閉じたハンドルの再利用は
   無効ハンドルのエラーになります。本物の C FFI は計画 §2.1 §12 で
   延期しており、C リンケージの `extern` も §13.4 の `c_prims` 表
   (sin/cos/sqrt/exp/log)にある既知名だけの張りぼてです。
   prim 側と違いプレリュードが型を与えられない(sample.kel が C リンケージの
   `sin` を自分で宣言するため、プレリュードが先に置くと再宣言拒否で
   仕様が落ちる)ので、既知名 5 本の型は第6章 §6.2b が**契約として照合**
   します。表に無い未知名の宣言は従来どおり素通りです — 本物の C FFI は
   本質的に検証不能な宣言であり、その線引きは意図的なものです。
   `@ Blocking` の付いた既知名は、トップレベルから直接呼べます(仕様 §12、
   D88。`test/blocking_top.t`)。行を注釈で閉じた文脈へ持ち込むときは
   `pinned`(§6.11b / §14.11)で落とします — Blocking を落とすのは型の上の
   行為だけで、実行は恒等です。

   第14章の `run` は実行のたびに `reset_fs` で状態を戻します。戻すのは
   表 2 枚と `next_handle` の **3 つ**で、1 つの関数にまとめてあるのは
   呼び出し側に数え漏れをさせないためです — かつて run は表 2 枚だけを
   戻していて、ハンドル番号が再入 API では実行回数に依存していました。
   実行の中では単調増加、実行の間では 0 に戻る、が正しい姿です。

   > 張りぼてを置くのは構わない。張りぼてだと書かないのが害である。 *)

  (* ---- テスト用のメモリ上ダミーファイルシステム(計画 §8.6) ---- *)

let fs : (string, string) Hashtbl.t = Hashtbl.create 8

let handles : (int32, string) Hashtbl.t = Hashtbl.create 8

let next_handle = ref 0l

(* 実行のたびに張りぼてを空にする(C14)。3 枚まとめて戻すのは、呼び出し側に
   数え漏れをさせないため — かつて run は fs と handles だけを戻し、
   next_handle が漏れていた(再入 API でハンドル番号が実行回数に依存する) *)
let reset_fs () =
  Hashtbl.reset fs;
  Hashtbl.reset handles;
  next_handle := 0l

(* ## 13.4 プリミティブ表 — 名前から実装への連想リスト

   表の作りは単純です。`(名前, 引数レコード -> 値)` の連想リストが、
   リンケージごとに 1 本 — 「prim」の `prims` と「C」の `c_prims`。
   `i32_bin` などのコンビネータが「引数を 2 つ取り出し、型を検査し、
   結果を包み直す」定型を吸収するので、各行は演算そのものだけになります。

   2 枚に割ってあるのは、**リンケージを実装バインドに効かせる**ためです。
   かつては 1 本の表を `extern` の ABI を見ずに引いていたので、
   C リンケージで `__string_le` の実装に、prim リンケージで C 既知名
   `cos` の実装に、それぞれ届いてしまいました(実測)。いまは
   `find_extern ~abi` が宣言の ABI で表を選び、届かない組は呼ばれた時点で
   「未実装のプリミティブ」に落ちます。ABI 文字列そのものの検査
   (prim / C 以外の拒否)は第11章の `DExtern` 枝にあります。

   ここに現れる裁定をいくつか。

   **ゼロ除算は実行時エラー、整数の桁あふれは wrap-around。**
   `div_check_*` / `rem_check_*` が前者、`Int32.add` などの素通しが後者です。
   後者は暫定の裁定で(計画 §8.6)、検査付き算術に変えるならこの表の
   数行を差し替えるだけで済みます。

   **Float64 の等価と比較は、どちらも IEEE 754 を守ります。**
   OCaml の多相 `compare` は NaN を全順序の最小・自分自身と等しいものと
   して扱うので、素通しにすると `nan == nan` が真、`nan < 1.0` も真に
   なります。だから等価 (`__float64_eq`) はコンビネータを使わず浮動小数の
   `=` を直に使い、比較 (`f64_cmp`) は NaN ガードを先頭に置きます —
   どちらかが NaN なら lt / le / gt / ge は 4 つとも偽 (D23)。NaN を除いた
   領域では `compare` は IEEE の順序と一致し、±0.0 も `compare` が 0 を
   返すので `le` / `ge` が真になって揃います。帰結として Float64 の順序は
   **全順序ではありません** — それどころか `nan <= nan` も偽なので反射律が
   破れ、`<=` は厳密には半順序ですらありません(`<` は狭義半順序、`<=` は
   NaN を除いた部分集合の上でだけ全前順序)。NaN は自分自身を含む
   すべての値と比較不能です。全順序が要る場面は sample.kel:221 の
   `newtype TotalFloat64(Float64)` のように包んで自前のインスタンスを
   与える設計で、`Ord` クラスは順序の公理を何も約束しません。改訂後の
   仕様は §14(sample.kel:767-771)で `Ord[Float64]` と NaN を保留のまま
   2 案に整理し、`TotalFloat64` を案 (1)「包んだ型だけが `Ord` を実装する」の
   見本と位置づけました — 実装するかは未定と注記つきです。かつては等価だけを
   直して比較を `compare` のままにしていて、`nan == nan` が偽なのに
   `nan <= nan` が真という自己矛盾がありました。

   > 同じ型の等価と順序を別々の道具で書くと、片方だけ直した状態が生まれる。

   **`__string_sub` は範囲外を捕まえます。** OCaml の `Invalid_argument` を
   そのまま外へ出すと、第16章 (driver.ml) の終了コード規約から外れた
   例外がユーザに見えます。260829-2b の頑健性の検証でこの種の素通しを
   まとめて塞ぎました。同じ理由で `__panic` は `Runtime_error` を投げます。

   **Float64 → 整数の変換は、表現できる値が無ければ実行時エラーです。**
   `Int32.of_float` / `Int64.of_float` は範囲外や NaN で結果が未規定で、
   x86 では黙って INT_MIN を返していました。整数算術の wrap-around と扱いを
   分けるのは、算術は必ず表現できる値を返すのに対し、**変換には返せる値が
   無いことがある**からです。ゼロ除算や範囲外の数値リテラル(第14章)と
   同じ側に倒します。`f64_to_int` の範囲判定が上限を「目標型の最小値の
   符号反転の**未満**」と書いているのは、`Int64.to_float Int64.max_int` が
   2^63 に丸め上がって上限側の境界に使えないためです(切り捨て後の値は
   整数なので、2^31 未満は 2^31 - 1 以下と同値)。逆向きの `__i64_to_i32` は
   wrap-around のまま — あちらは整数算術の裁定に揃えています。変換 6 本の
   全部(落ちうる `__f64_to_i32` / `__f64_to_i64` の 2 本と、落ちない 4 本)、
   整数算術の桁あふれ、String がバイト列で
   あること、`Char` が無いことは `test/numeric.t` がゴールデンにしています
   (M21 / F-B7)。

   最後に性能の話を。`find_prim` は連想リストの線形探索のままですが、
   引かれるのは **extern のバインド(宣言 1 回につき 1 回)と、§13.5 の
   メソッド表の起動時解決だけ**になりました(D37)。演算のたびの探索は、
   §13.5 のハッシュ表と第14章の解決キャッシュが受け持ちます。かつては
   `builtin_method` 経由で演算のたびに線形探索が走り、当たる位置で
   1 回あたり 105ns〜370ns(3.5 倍差)を払っていました — 計画 §8.5 の
   静的焼き込みは、v1 の HKT が「値タグから決まらないメソッド」を要求する
   までこのキャッシュで足ります。 *)

  (* ---- __* プリミティブ表(名前 → 実装)。型は prelude.kel の extern が与える ---- *)

let i32_bin f = fun v -> let a, b = arg2 v in VInt32 (f (as_i32 a) (as_i32 b))

let i64_bin f = fun v -> let a, b = arg2 v in VInt64 (f (as_i64 a) (as_i64 b))

let f64_bin f = fun v -> let a, b = arg2 v in VFloat64 (f (as_f64 a) (as_f64 b))

let i32_cmp f = fun v -> let a, b = arg2 v in VBool (f (Int32.compare (as_i32 a) (as_i32 b)) 0)

let i64_cmp f = fun v -> let a, b = arg2 v in VBool (f (Int64.compare (as_i64 a) (as_i64 b)) 0)

(* IEEE 754: どちらかが NaN なら lt/le/gt/ge は 4 つとも偽(D23)。
   OCaml の多相 compare は NaN を全順序の最小として扱うので、
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

(* Float64 → 整数の変換は、表現できる値が無ければ実行時エラーにする(上の
   §13.4 の 4 つ目の裁定)。lo は目標型の最小値を float にしたもの。上限を
   -.lo の未満と書くのは、Int64.to_float Int64.max_int が 2^63 に丸め上がって
   上限側の境界に使えないため(切り捨て後の t は整数値なので同値) *)
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
    ( "__open",
      fun v ->
        let path = as_text (arg1 v) in
        next_handle := Int32.add !next_handle 1l;
        Hashtbl.replace handles !next_handle path;
        VInt32 !next_handle );
    ( "__read",
      fun v ->
        let h = as_i32 (arg1 v) in
        let path = try Hashtbl.find handles h with Not_found -> runtime_error "__read: 無効なハンドルです" in
        VText (Option.value ~default:"" (Hashtbl.find_opt fs path)) );
    ( "__write",
      fun v ->
        let h, s = arg2 v in
        let path = try Hashtbl.find handles (as_i32 h) with Not_found -> runtime_error "__write: 無効なハンドルです" in
        Hashtbl.replace fs path (Option.value ~default:"" (Hashtbl.find_opt fs path) ^ as_text s);
        unit );
    ( "__close",
      fun v ->
        Hashtbl.remove handles (as_i32 (arg1 v));
        unit );
  ]

(* extern C の既知名テーブル(M10。真の C FFI は延期、計画 §2.1 §12)。
   prim 表と分けてあるのは、リンケージが実装バインドに効くようにするため。
   既知名の型契約は第6章 §6.2b の表にある。実装だけ足して契約を忘れると
   検査が効かないだけ、契約だけ足すと呼んだ時点で未実装 — 縮退は安全側 *)
let c_prims : (string * (t -> t)) list =
  [
    ("sin", fun v -> VFloat64 (sin (as_f64 (arg1 v))));
    ("cos", fun v -> VFloat64 (cos (as_f64 (arg1 v))));
    ("sqrt", fun v -> VFloat64 (sqrt (as_f64 (arg1 v))));
    ("exp", fun v -> VFloat64 (exp (as_f64 (arg1 v))));
    ("log", fun v -> VFloat64 (log (as_f64 (arg1 v))));
  ]

(* prim 表専用の探索(§13.5 の組み込みメソッド表の構築が使う) *)
let find_prim name = List.assoc_opt name prims

(* extern 宣言の実装バインドはこちら。宣言の ABI で表を選ぶので、
   届かない組(C リンケージで __* や、prim リンケージで sin)は None に
   なり、呼ばれた時点で「未実装のプリミティブ」に落ちる *)
let find_extern ~abi name =
  match abi with "prim" -> List.assoc_opt name prims | "C" -> List.assoc_opt name c_prims | _ -> None

(* ## 13.5 組み込みインスタンスの実体

   `builtin_method` は (クラス名, 型構成子名, メソッド名) から実装を引きます。
   第14章の `dispatch` は、まず値のタグで**ユーザ宣言のインスタンス**を探し、
   無ければここへ落ちてきます。組み込みが後ろにいるこの順序は
   意図したものですが、順序だけでは足りないことが分かっています。

   260829-2b の健全性の検証で、`type instance Add[Int32]` をユーザが
   再宣言すると `2 + 3` が `-1` になりました。組み込みのキーと同じ
   (クラス, 型構成子) をユーザが差し替えられたためです。修正は第14章側で、
   **組み込みキーと同じ組み合わせは実体を差し替えない**という規則を
   インスタンス登録に入れました。ここが最後の砦になるのではなく、
   ここへ辿り着く前に守るのが正しい形です。

   `Show` の枝が呼ぶ `float_repr` は第12章 §12.7 の表示器です(§13.2)。
   診断用の印字(§12.7 の `show`)も同じ表示器を使うので、**Float64 に
   ついては**ユーザに見える `show(x)` と実行時エラーの中の値表示が
   食い違いません。他の型はそうではありません — String の診断は引用符と
   エスケープを通した字面(ユーザの `show` は生の文字列)、ユーザが
   `Show` インスタンスを与えた型でも診断は構造の印字のままです。
   診断は値の**構造**を、`show` は値の**表示**を返す、という役割の差です。

   表は**明示の 39 行**です(D37)。名前の組み立て規則は 1 つも置きません。
   かつて `Ord` の 4 行はメソッド名 `m` をワイルドカードで受けて
   `__int32_ ^ m` を組み立てており、`Ord` に別名のメソッドが来ると、
   たまたま同名のプリミティブがあればそれが選ばれる形でした — その行の
   安全は隣のファイル 3 つの不変条件の積に寄りかかっていました(C2)。
   いまは起動時に全行をプリミティブ表に対して解決してハッシュ表に焼くので、
   書き写しのタイプミスは最初の起動で `[BUG]` として落ち、呼び出しは
   位置に依存しない 1 引きです。 *)

  (* ---- 組み込みクラスメソッドの実装表: (クラス, 型構成子, メソッド) → 実装 ---- *)

(* 組み込みインスタンスの実体は (クラス, 型構成子, メソッド) の明示表
   (D37)。名前の組み立て規則は置かない — 39 行すべて書き切る。かつて
   Ord の 4 行はメソッド名 m をワイルドカードで受けて __int32_ ^ m を
   組み立てており、その行の安全は隣のファイル 3 つの不変条件の積に
   寄りかかっていた(C2)。表の網羅は第6章の組み込みクラス × インスタンス
   の積(Add 4 / Sub 3 / Mul 3 / Div 3 / Eq 5 / Ord 16 / Show 5 = 39)と
   一致させる *)
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
    (* C9: 実装表で死んでいた __show_int32 をここで生かす(入口は 1 つ) *)
    (("Show", "Int32", "show"), "__show_int32");
  ]

(* プリミティブ名を持たない実体は OCaml で直接書く *)
let builtin_method_direct : ((string * string * string) * (t -> t)) list =
  [
    (("Eq", "Boolean", "eq"), fun v -> let a, b = arg2 v in VBool (as_bool a = as_bool b));
    (("Show", "Int64", "show"), fun v -> VText (Int64.to_string (as_i64 (arg1 v))));
    (("Show", "Float64", "show"), fun v -> VText (float_repr (as_f64 (arg1 v))));
    (("Show", "String", "show"), fun v -> VText (as_text (arg1 v)));
    (("Show", "Boolean", "show"), fun v -> VText (string_of_bool (as_bool (arg1 v))));
  ]

(* 起動時に 1 度だけプリミティブ名を解決してハッシュ表に焼く(D37)。
   書き写しのタイプミスは最初の起動で bug として落ちる — 実行時の
   「そのメソッドだけインスタンスが見つかりません」に化けさせない *)
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

(* ## 13.6 `with_runtime` — 一番外側の 1 枚

   Keleut のトップレベルは純粋ではありません。プログラムはランタイムが
   提供するエフェクトの下で走ります(第7章 (prims.ml) の `runtime_effects`。
   v0 では `Console` と `Async`)。その「提供する」を実際にやるのが、
   第14章の評価の全体をくるむこの 1 枚のハンドラです。

   `Effect.Deep.match_with` の 3 つの欄のうち、`retc` は恒等、`exnc` は
   そのまま再送出です。つまりこのハンドラは**値と例外に対しては透明**で、
   自分の知っている操作だけを横から捕まえます。ただしそれは retc / exnc の
   話で、`effc` の**中で**起きた例外は別です — 第14章 §14.10 の 3 径路の
   規約は最外周のこの 1 枚にも同じく効きます。`sink` の書き込みが落ちたら
   `discontinue` で捨てる継続に知らせます(B6。素の raise だと捨てた継続の
   中の cancel が走らない — 第14章の速い経路と同型の穴でした)。sink が
   落ちる現実の経路は標準出力の書き込み失敗で、cancel 節の**出力**は同じ
   壊れた標準出力へ行くので観測できませんが、cancel 節の**例外**は抑制
   ログ(stderr)に出ます。そこを観測点にしたゴールデンが test/eval.t に
   あります — stdout を閉じてバッファを溢れさせ、cancel 節の `__panic` が
   抑制ログに現れることを見る。ログが出た = 例外が fiber へ配送された =
   `discontinue` が走った、という直接の証拠です(当初「エンドツーエンドの
   テストは書けない」と記録しましたが、敵対的検証が反証しました)。

   知らない `Op` には `None` を
   返して外へ通し、その先には誰もいないので `Effect.Unhandled` になります。
   これを操作名込みのメッセージに翻訳するのは第16章 (driver.ml) の仕事です。
   既定の例外表示は `Op` の中身を出さないので、driver は
   `Effect.Unhandled (Op (op, _))` という形を構造で直接照合し、そこから
   操作名を取り出します。計画 §8.4 は `Printexc.register_printer` が要ると
   書いていましたが、実装では登録していません — 照合する場所が 1 箇所しか
   ないなら、大域に printer を足すより、その 1 箇所でパターンを書くほうが
   小さく済みます。

   - `Console.write` は `sink` へ。**出力先を引数にした**のは、
     第16章の `eval_string ~sink` がテストから出力を受け取れるように
     するためです(コマンドラインからの実行では `print_string` が入ります)。
     `Console` はユーザにハンドルさせないエフェクトで、M20 (I4 / D63) から
     第11章がそれを**強制**します — プレリュード所有の `Console` への
     `case Console.write(s) => ...` は型エラーです。だからプレリュード所有の
     `Console.write` は「必ずこの 1 枚まで登ってくる」と言えるように
     なりました(かつては内側の `handle` が横取りでき、出力を握り潰せる
     ことを実測で確認していました)。
     出力先をプログラム側で差し替えたいときにユーザ層の `Print` へハンドラを
     書き、prelude の `with_stdout` が `Print.print` を `Console.write` へ
     翻訳する、というのが意図された道です
   - `Async.yield_` と `Async.sleep` は即 `continue`。**型は本物、実行は
     no-op** です(計画 §2.1 §11)。並行実行は v0 の範囲外です。
     `par` / `par_map` は逐次に実装されています(§14.11)— 純粋な
     コールバックしか受け取らない(行が `@ {}` に閉じている)ので、
     並列実行と観測同値です。sample.kel が型検査を通ることと、
     `yield_` を書いたプログラムが止まらずに走ることの両方を、
     嘘をつかずに満たす最小の実装がこれです

   操作名を `Type.intern` した `oid` で持ち、`effc` の中では整数の比較しか
   しません。第11章が非修飾の `write` を `Console.write` へ解決済みなので
   (計画 D22)、ここで名前を解く必要はもうありません。

   この節はプロトコルの**利用者側**です。`Op` と `Unwind` の宣言は
   第12章 §12.5 にあり、ハンドラの本体 — 節の 3 径路、`discontinue` の
   必然性、cancel の LIFO、活性化 id — は第14章で語ります。 *)

  (* ---- ランタイムエフェクトハンドラ(最外周の1枚、計画 §8.4) ---- *)

let op_console_write = Type.intern "Console.write"

let op_async_yield = Type.intern "Async.yield_"

let op_async_sleep = Type.intern "Async.sleep"

let with_runtime ~(sink : string -> unit) (f : unit -> t) : t =
  Effect.Deep.match_with f ()
    {
      retc = Fun.id;
      exnc = raise;
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Op (op, args) when op = op_console_write ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  (* 第14章 §14.10 の 3 径路と同じ規約(B6)。sink が落ちても
                     捨てる継続に知らせる。continue は値の枝(trap の外)に
                     あるので末尾発行のまま *)
                  match sink (as_text (arg1 args)) with
                  | () -> Effect.Deep.continue k unit
                  | exception ex -> Effect.Deep.discontinue k ex)
          | Op (op, _) when op = op_async_yield || op = op_async_sleep ->
              (* v0: 型 + 実行時 no-op(計画 §2.1 §11) *)
              Some (fun k -> Effect.Deep.continue k unit)
          | _ -> None);
    }
