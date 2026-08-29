数値・浮動小数の一貫性(計画 260829-4 ワークストリーム A)。

Float64 → 整数の変換は NaN と範囲外を実行時エラーにする(A9。かつては
Int32.of_float / Int64.of_float 素通しで、黙って INT_MIN を返していた):

  $ printf 'echoln(show(__f64_to_i32(2.7)))\necholn(show(__f64_to_i32(0.0 - 2.7)))\n' > cvok.kel
  $ diktor cvok.kel
  2
  -2

  $ printf 'echoln(show(__f64_to_i32(0.0 / 0.0)))\n' > cvnan.kel
  $ diktor cvnan.kel
  実行時エラー: __f64_to_i32: NaN は整数に変換できません
  [3]

  $ printf 'echoln(show(__f64_to_i32(1.0e20)))\n' > cvbig.kel
  $ diktor cvbig.kel
  実行時エラー: __f64_to_i32: 変換結果が範囲外です: 1e+20
  [3]

  $ printf 'echoln(show(__f64_to_i32(1.0 / 0.0)))\n' > cvinf.kel
  $ diktor cvinf.kel
  実行時エラー: __f64_to_i32: 変換結果が範囲外です: inf
  [3]

境界: Int32 の最大・最小はちょうど変換でき、最大 + 1 は落ちる:

  $ printf 'echoln(show(__f64_to_i32(2147483647.0)))\necholn(show(__f64_to_i32(0.0 - 2147483648.0)))\n' > cvedge.kel
  $ diktor cvedge.kel
  2147483647
  -2147483648

  $ printf 'echoln(show(__f64_to_i32(2147483648.0)))\n' > cvover.kel
  $ diktor cvover.kel
  実行時エラー: __f64_to_i32: 変換結果が範囲外です: 2147483648.0
  [3]

Int64 → Int32 は従来どおり wrap-around(整数算術の裁定に揃える):

  $ printf 'echoln(show(__i64_to_i32(__f64_to_i64(2147483648.0))))\n' > cvwrap.kel
  $ diktor cvwrap.kel
  -2147483648

Ord[Float64] は IEEE 754(NaN が絡む 4 比較はすべて偽。A1 / D23):

  $ cat > nan_ord.kel <<'KEL'
  > let nan(): Float64 = 0.0 / 0.0
  > echoln(show(nan() < 1.0))
  > echoln(show(nan() <= 1.0))
  > echoln(show(nan() > 1.0))
  > echoln(show(nan() >= 1.0))
  > echoln(show(1.0 < nan()))
  > echoln(show(1.0 >= nan()))
  > echoln(show(nan() <= nan()))
  > echoln(show(nan() >= nan()))
  > echoln(show(nan() == nan()))
  > echoln(show(1.0 < 2.0))
  > echoln(show(1.0 <= 1.0))
  > echoln(show(0.0 <= -0.0))
  > echoln(show(0.0 < -0.0))
  > KEL
  $ diktor nan_ord.kel
  false
  false
  false
  false
  false
  false
  false
  false
  false
  true
  true
  true
  false

有限の Float64 は必ず読み戻せる字面で表示する(A7):

  $ cat > big.kel <<'KEL'
  > echoln(show(1.0e16))
  > echoln(show(12345678901234568.0))
  > echoln(show(1.0e300))
  > echoln(show(1.0e-5))
  > echoln(show(0.0 - 1.0e16))
  > KEL
  $ diktor big.kel
  1e+16
  12345678901234568.0
  1e+300
  1e-05
  -1e+16

出した字面をそのまま貼り戻せる:

  $ cat > roundtrip.kel <<'KEL'
  > let a: Float64 = 12345678901234568.0
  > let b: Float64 = 1e+16
  > let c: Float64 = 1e-05
  > echoln(show(a))
  > echoln(show(b))
  > echoln(show(c))
  > KEL
  $ diktor roundtrip.kel
  12345678901234568.0
  1e+16
  1e-05

非有限値の表示(Keleut のリテラルにはならないので、そう表示すると
決める。NaN の符号は環境で割れるので落とす。A8 / D27):

  $ cat > infnan.kel <<'KEL'
  > echoln(show(1.0 / 0.0))
  > echoln(show(0.0 - 1.0 / 0.0))
  > echoln(show(0.0 / 0.0))
  > echoln(show(0.0 - 0.0 / 0.0))
  > KEL
  $ diktor infnan.kel
  inf
  -inf
  nan
  nan

診断用の印字も最短往復表現を使う(A2。実行時エラー内の Float64。
警告の反例が witness であることは A6):

  $ cat > nomatch.kel <<'KEL'
  > let f(x: Float64): Int32 = x match {
  >   case 0.0 => 1
  > }
  > echoln(show(f(0.1 + 0.2)))
  > KEL
  $ diktor nomatch.kel
  ⚠ match が非網羅的です。例えば 1.0 が漏れています
  実行時エラー: match のどの節にも一致しません: 0.30000000000000004
  [3]

浮動小数パターンの重複判定は値の単射な鍵で行う(A3 / D24。
偽の冗長警告を出さない):

  $ cat > fdup.kel <<'KEL'
  > let f(x: Float64): Int32 = x match {
  >   case 1.0              => 1
  >   case 1.0000000000001  => 2
  >   case _                => 3
  > }
  > echoln(show(f(1.0)))
  > echoln(show(f(1.0000000000001)))
  > KEL
  $ diktor fdup.kel
  1
  2
  $ diktor --type-check --strict-exhaustive fdup.kel > /dev/null; echo "exit: $?"
  exit: 0

+0.0 と -0.0 は同じパターン(実行時の = に合わせる):

  $ cat > zdup.kel <<'KEL'
  > let g(x: Float64): Int32 = x match {
  >   case 0.0  => 1
  >   case -0.0 => 2
  >   case _    => 3
  > }
  > echoln(show(g(-0.0)))
  > echoln(show(g(0.0)))
  > KEL
  $ diktor zdup.kel
  ⚠ 第 2 節は到達不能です(冗長)
  1
  1

Int64 の 16 進リテラルは値で区別される(A10。63 ビットの int_of_string は
0x7FFFFFFFFFFFFFFF を -1 に折り返し、偽の冗長警告を出していた):

  $ cat > idup.kel <<'KEL'
  > let f(x: Int64): Int32 = x match {
  >   case -1                  => 1
  >   case 0x7FFFFFFFFFFFFFFF  => 2
  >   case _                   => 3
  > }
  > echoln(show(f(0i64 - 1i64)))
  > echoln(show(f(0x7FFFFFFFFFFFFFFF)))
  > KEL
  $ diktor idup.kel
  1
  2
  $ diktor --type-check --strict-exhaustive idup.kel > /dev/null; echo "exit: $?"
  exit: 0

基数が違っても同じ値なら 1 つのパターン(乖離 11 / D24 の回帰):

  $ cat > radix.kel <<'KEL'
  > let g(n: Int32): Int32 = n match {
  >   case 1    => 1
  >   case 0x1  => 2
  >   case _    => 3
  > }
  > KEL
  $ diktor --type-check --no-prelude radix.kel
  g : (Int32) => Int32
  ⚠ 第 2 節は到達不能です(冗長)

反例は具体的な値を出す(A6。文字列は空文字列から、浮動小数は 0.0 から
探し、整数は従来どおり。かつては文字列が _、Float64 は既に覆われた 0):

  $ cat > cx.kel <<'KEL'
  > let g(s: String): Int32 = s match {
  >   case "a" => 1
  >   case "b" => 2
  > }
  > let h(x: Float64): Int32 = x match {
  >   case 0.0 => 1
  >   case 1.0 => 2
  > }
  > let k(n: Int32): Int32 = n match {
  >   case 0 => 1
  >   case 1 => 2
  > }
  > let e(s: String): Int32 = s match {
  >   case "" => 1
  > }
  > KEL
  $ diktor --type-check --no-prelude cx.kel
  g : (String) => Int32
  ⚠ match が非網羅的です。例えば "" が漏れています
  h : (Float64) => Int32
  ⚠ match が非網羅的です。例えば 2.0 が漏れています
  k : (Int32) => Int32
  ⚠ match が非網羅的です。例えば 2 が漏れています
  e : (String) => Int32
  ⚠ match が非網羅的です。例えば "a" が漏れています
