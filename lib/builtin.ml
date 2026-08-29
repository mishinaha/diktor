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
   (sample.kel:198-200)。呼び出し規約はそれをそのまま写して
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
   最初に踏まれる床**がここである以上、床は張ったままにしておきます。 *)

let arg_values v = List.map snd (record_fields v)

let arg1 v = match arg_values v with [ a ] -> a | _ -> runtime_error "プリミティブの引数が1個ではありません"

let arg2 v = match arg_values v with [ a; b ] -> (a, b) | _ -> runtime_error "プリミティブの引数が2個ではありません"

let as_i32 = function VInt32 n -> n | v -> runtime_error ("Int32 ではありません: " ^ show v)

let as_i64 = function VInt64 n -> n | v -> runtime_error ("Int64 ではありません: " ^ show v)

let as_f64 = function VFloat64 f -> f | v -> runtime_error ("Float64 ではありません: " ^ show v)

let as_text = function VText s -> s | v -> runtime_error ("String ではありません: " ^ show v)

let as_bool = function VBool b -> b | v -> runtime_error ("Boolean ではありません: " ^ show v)

(* ## 13.2 `float_repr` — 表示は丸めではない

   これは 260829-2b の敵対的検証で見つけて直した欠陥です。
   もとの実装は OCaml の `string_of_float`、つまり `%.12g` 相当でした。
   12 桁で切ると、`0.1 + 0.2` が **`0.3` と表示されます**。
   加算の結果はもちろん 0.3 ではありません。表示器が嘘をついていました。

   浮動小数の表示に求められるのは丸めではなく**往復**です。
   出した字面を読み戻したら元の値に戻ること。桁を落とせば見た目は綺麗に
   なりますが、その綺麗さは「同じ値だ」という誤った情報を伝えます。
   `0.1 + 0.2` が `0.30000000000000004` と出るのは正しい仕事です。

   アルゴリズムは素朴です。`%.1g` から桁を 1 つずつ上げ、
   `float_of_string` で読み戻して一致したところで止める。
   IEEE binary64 は 17 桁あれば必ず往復するので、17 で打ち切ります。
   最短表現を求める専用アルゴリズム(Ryu や Grisu)を持ち込まないのは、
   毎回最大 17 回の `sprintf` で足りるからです。表示は評価の内側ループでは
   ありません。

   整数値だけ `%.1f` で別扱いにしているのは、**型を見せるため**です。
   `%g` は 1.0 を `1` と印字しますが、Keleut の `1` は既定化 (D8) で Int32 に
   なる別の値です。`Show[Float64]` が `1` を返したら、`Show[Int32]` の
   出力と区別がつきません。小数点を強制すれば `1.0`、
   `123456789012345.0` はそのままの姿で出ます
   (`test/verify_fixes.t` にこの 3 例を固定してあります)。
   1e16 で切っているのは、それ以上は `%.1f` の桁数が延々と伸びるためで、
   大きい側は指数表記の最短往復に任せます。

   正直な注記を 1 つ。ここでいう往復は `float_of_string` に対する往復です。
   出した字面を Keleut のソースに貼り戻したときに数値リテラルの字句が
   それを受けるかは別問題で、実装記録 260829-2 の未修正項に残っています。

   > 表示は丸めではない。読み戻して同じ値になる最短の字面が正しい。 *)

(* Float64 の最短往復可能表現(string_of_float の %.12g は精度を落とす)。
   %.NNg を桁を上げながら試し、読み戻して一致する最小桁を採る *)
let float_repr f =
  if Float.is_integer f && Float.abs f < 1e16 then Printf.sprintf "%.1f" f
  else
    let rec go p =
      if p > 17 then Printf.sprintf "%.17g" f
      else
        let s = Printf.sprintf "%.*g" p f in
        if float_of_string s = f then s else go (p + 1)
    in
    go 1

(* ## 13.3 ファイルは張りぼてである

   `__open` / `__read` / `__write` / `__close` は本物のファイルを触りません。
   メモリ上のハッシュ表 2 枚 — パス から 内容 への `fs` と、
   ハンドル から パス への `handles` — がその正体です。

   なぜこれで足りるか。これらのプリミティブが存在する理由は
   sample.kel:401-406 の `with_file` を**動かして見せる**ことであって、
   ファイル入出力そのものではないからです。示したいのは
   「ハンドラが資源を握り、正常終了なら `return` 節で、外側が継続を捨てたなら
   `cancel` 節で `__close` が走る」という制御の筋(sample.kel:405-406)であって、
   その筋はダミーでも本物と同じに走ります。

   代わりに正直であることを選びます。**これは張りぼてです。**
   `__read` は書いた覚えのないパスに空文字列を返しますし、
   ハンドルは単調増加で再利用されず、閉じたハンドルの再利用は
   無効ハンドルのエラーになります。本物の C FFI は計画 §2.1 §12 で
   延期しており、C リンケージの `extern` も下の表
   (sin/cos/sqrt/exp/log)にある既知名だけの張りぼてです。

   第14章の `run` は実行のたびにこの 2 枚を `Hashtbl.reset` します。
   ゴールデンテストの間で状態が漏れないのはそのおかげです。

   > 張りぼてを置くのは構わない。張りぼてだと書かないのが害である。 *)

  (* ---- テスト用のメモリ上ダミーファイルシステム(計画 §8.6) ---- *)

let fs : (string, string) Hashtbl.t = Hashtbl.create 8

let handles : (int32, string) Hashtbl.t = Hashtbl.create 8

let next_handle = ref 0l

(* ## 13.4 プリミティブ表 — 名前から実装への連想リスト

   表の作りは単純です。`(名前, 引数レコード -> 値)` の連想リスト 1 本。
   `i32_bin` などのコンビネータが「引数を 2 つ取り出し、型を検査し、
   結果を包み直す」定型を吸収するので、各行は演算そのものだけになります。

   ここに現れる裁定をいくつか。

   **ゼロ除算は実行時エラー、整数の桁あふれは wrap-around。**
   `div_check_*` / `rem_check_*` が前者、`Int32.add` などの素通しが後者です。
   後者は暫定の裁定で(計画 §8.6)、検査付き算術に変えるならこの表の
   数行を差し替えるだけで済みます。

   **`__float64_eq` だけコンビネータを使いません。**
   ここは IEEE の意味論を守るための例外です。OCaml の多相 `compare` は
   NaN を全順序の最小として扱うので、`compare nan nan` は 0 になります。
   それで等価を書くと NaN が自分自身と等しくなってしまう。だから等価だけは
   浮動小数の `=` を直に使い、NaN が自分と等しくならないようにしています。
   **裏を返せば、比較 (`f64_cmp`) のほうは `compare` のままです。**
   `nan < 1.0` が真になるという IEEE との食い違いがここに残っています。
   等価だけ直して順序を直していないのは、正直に言えば片手落ちです。

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
   wrap-around のまま — あちらは整数算術の裁定に揃えています。

   最後に性能の正直な話を。`find_prim` は連想リストの線形探索で、しかも
   §13.5 の `builtin_method` 経由で**演算のたびに**引かれます。ただし
   走査量は名前が表のどこに並んでいるかで決まります。`__int32_add` は
   たまたま表の先頭なので `2 + 3` は比較 1 回で当たり、`__close` のような
   末尾側の名前を引くと数十要素をなめます。**当たる位置に依存する探索**である
   ことに変わりはなく、最悪ケースは表の長さに比例します。v0 はこれで足りて
   います(10 万回 println の回帰テストが通る)が、速くしたいなら表をハッシュ表に
   変えるか、elab が解決済みのインスタンスを呼び出し地点に注記して表引き
   自体を消すか(計画 §8.5 の将来案)のどちらかです。後者のほうが筋は良く、
   動的ディスパッチをフォールバックに残したまま段階的に移行できます。 *)

  (* ---- __* プリミティブ表(名前 → 実装)。型は prelude.kel の extern が与える ---- *)

let i32_bin f = fun v -> let a, b = arg2 v in VInt32 (f (as_i32 a) (as_i32 b))

let i64_bin f = fun v -> let a, b = arg2 v in VInt64 (f (as_i64 a) (as_i64 b))

let f64_bin f = fun v -> let a, b = arg2 v in VFloat64 (f (as_f64 a) (as_f64 b))

let i32_cmp f = fun v -> let a, b = arg2 v in VBool (f (Int32.compare (as_i32 a) (as_i32 b)) 0)

let i64_cmp f = fun v -> let a, b = arg2 v in VBool (f (Int64.compare (as_i64 a) (as_i64 b)) 0)

let f64_cmp f = fun v -> let a, b = arg2 v in VBool (f (compare (as_f64 a) (as_f64 b)) 0)

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
    (* extern "C" の既知名テーブル(M10。真の C FFI は延期、計画 §2.1 §12) *)
    ("sin", fun v -> VFloat64 (sin (as_f64 (arg1 v))));
    ("cos", fun v -> VFloat64 (cos (as_f64 (arg1 v))));
    ("sqrt", fun v -> VFloat64 (sqrt (as_f64 (arg1 v))));
    ("exp", fun v -> VFloat64 (exp (as_f64 (arg1 v))));
    ("log", fun v -> VFloat64 (log (as_f64 (arg1 v))));
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

let find_prim name = List.assoc_opt name prims

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

   `Show` の枝が `float_repr` を呼ぶのが §13.2 の出口です。
   第12章 §12.7 の `show` は診断用の別の関数で、ユーザに見えるのはこちらです。

   `Ord` の 4 行だけ、メソッド名 `m` をそのまま型ごとの接頭辞に連結しています。
   `lt` / `le` / `gt` / `ge` がプリミティブ名と 1 対 1 に対応するので 4 行で
   済みますが、ここだけは表の項目ではなく**名前の組み立て規則**です。
   `Ord` に別のメソッド名が来ると、対応するプリミティブが無ければ `None`、
   たまたま同じ名前のプリミティブがあれば**それが選ばれてしまいます**。
   `Ord` のメソッド集合は第6章 (decls.ml) の組み込みクラス表が固定しており、
   ユーザ再宣言も照合の上でしか受理しないので今は塞がっていますが、
   この行の安全は隣のファイルの不変条件に寄りかかっています。 *)

  (* ---- 組み込みクラスメソッドの実装表: (クラス, 型構成子, メソッド) → 実装 ---- *)

let builtin_method cls con meth : (t -> t) option =
  let p name = find_prim name in
  match (cls, con, meth) with
  | "Add", "Int32", "add" -> p "__int32_add"
  | "Add", "Int64", "add" -> p "__int64_add"
  | "Add", "Float64", "add" -> p "__float64_add"
  | "Add", "String", "add" -> p "__string_concat"
  | "Sub", "Int32", "sub" -> p "__int32_sub"
  | "Sub", "Int64", "sub" -> p "__int64_sub"
  | "Sub", "Float64", "sub" -> p "__float64_sub"
  | "Mul", "Int32", "mul" -> p "__int32_mul"
  | "Mul", "Int64", "mul" -> p "__int64_mul"
  | "Mul", "Float64", "mul" -> p "__float64_mul"
  | "Div", "Int32", "div" -> p "__int32_div"
  | "Div", "Int64", "div" -> p "__int64_div"
  | "Div", "Float64", "div" -> p "__float64_div"
  | "Eq", "Int32", "eq" -> p "__int32_eq"
  | "Eq", "Int64", "eq" -> p "__int64_eq"
  | "Eq", "Float64", "eq" -> p "__float64_eq"
  | "Eq", "String", "eq" -> p "__string_eq"
  | "Eq", "Boolean", "eq" -> Some (fun v -> let a, b = arg2 v in VBool (as_bool a = as_bool b))
  | "Ord", "Int32", m -> p ("__int32_" ^ m)
  | "Ord", "Int64", m -> p ("__int64_" ^ m)
  | "Ord", "Float64", m -> p ("__float64_" ^ m)
  | "Ord", "String", m -> p ("__string_" ^ m)
  | "Show", "Int32", "show" -> Some (fun v -> VText (Int32.to_string (as_i32 (arg1 v))))
  | "Show", "Int64", "show" -> Some (fun v -> VText (Int64.to_string (as_i64 (arg1 v))))
  | "Show", "Float64", "show" -> Some (fun v -> VText (float_repr (as_f64 (arg1 v))))
  | "Show", "String", "show" -> Some (fun v -> VText (as_text (arg1 v)))
  | "Show", "Boolean", "show" -> Some (fun v -> VText (string_of_bool (as_bool (arg1 v))))
  | _ -> None

(* ## 13.6 `with_runtime` — 一番外側の 1 枚

   Keleut のトップレベルは純粋ではありません。プログラムはランタイムが
   提供するエフェクトの下で走ります(第7章 (prims.ml) の `runtime_effects`。
   v0 では `Console` と `Async`)。その「提供する」を実際にやるのが、
   第14章の評価の全体をくるむこの 1 枚のハンドラです。

   `Effect.Deep.match_with` の 3 つの欄のうち、`retc` は恒等、`exnc` は
   そのまま再送出です。つまりこのハンドラは**値と例外に対しては透明**で、
   自分の知っている操作だけを横から捕まえます。知らない `Op` には `None` を
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
     `Console` は**仕様の約束として**ユーザにハンドルさせないエフェクトです
     (第15章)。ただし v0 の実装にその禁止検査はありません。ユーザが
     `case Console.write(s) => ...` と書けば内側の `handle` が操作を捕まえ、
     この 1 枚までは登ってきません(実測で確認済み。出力を握り潰すことも
     できてしまいます)。ここで言えるのは「**登ってきた** `write` を受けるのは
     この 1 枚だけ」であって、「必ず登ってくる」ではありません。
     出力先をプログラム側で差し替えたいときにユーザ層の `Print` へハンドラを
     書き、prelude の `with_stdout` が `Print.print` を `Console.write` へ
     翻訳する、というのが意図された道です
   - `Async.yield_` と `Async.sleep` は即 `continue`。**型は本物、実行は
     no-op** です(計画 §2.1 §11)。並行実行は v0 の範囲外で、
     `par` / `par_map` も逐次のままです。sample.kel が型検査を通ることと、
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
                  sink (as_text (arg1 args));
                  Effect.Deep.continue k unit)
          | Op (op, _) when op = op_async_yield || op = op_async_sleep ->
              (* v0: 型 + 実行時 no-op(計画 §2.1 §11) *)
              Some (fun k -> Effect.Deep.continue k unit)
          | _ -> None);
    }
