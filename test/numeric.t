数値の変換、比較、表示、リテラル、パターンの動作を固定する。

Float64 から整数への変換は、NaN と範囲外の値を実行時エラーにする。
範囲内の値は、小数部を 0 の方向に切り捨てる:

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
  実行時エラー: __f64_to_i32: 変換結果が範囲外です: 1e20
  [3]

  $ printf 'echoln(show(__f64_to_i32(1.0 / 0.0)))\n' > cvinf.kel
  $ diktor cvinf.kel
  実行時エラー: __f64_to_i32: 変換結果が範囲外です: inf
  [3]

境界値を確かめる。Int32 の最大値と最小値はちょうど変換でき、最大値 + 1 は実行時エラーになる:

  $ printf 'echoln(show(__f64_to_i32(2147483647.0)))\necholn(show(__f64_to_i32(0.0 - 2147483648.0)))\n' > cvedge.kel
  $ diktor cvedge.kel
  2147483647
  -2147483648

  $ printf 'echoln(show(__f64_to_i32(2147483648.0)))\n' > cvover.kel
  $ diktor cvover.kel
  実行時エラー: __f64_to_i32: 変換結果が範囲外です: 2147483648.0
  [3]

Int64 から Int32 への変換は、整数演算のオーバーフローと同じく折り返す(下位 32 ビットだけが残る):

  $ printf 'echoln(show(__i64_to_i32(__f64_to_i64(2147483648.0))))\n' > cvwrap.kel
  $ diktor cvwrap.kel
  -2147483648

Ord[Float64] は IEEE 754 に従う(NaN を含む <、<=、>、>= の比較はすべて偽になる):

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

有限の Float64 は、読み戻すと同じ値になる表記で表示する:

  $ cat > big.kel <<'KEL'
  > echoln(show(1.0e16))
  > echoln(show(12345678901234568.0))
  > echoln(show(1.0e300))
  > echoln(show(1.0e-5))
  > echoln(show(0.0 - 1.0e16))
  > KEL
  $ diktor big.kel
  1e16
  12345678901234568.0
  1e300
  1e-5
  -1e16

「最短」は有効数字の桁数についての規則であり、固定小数点表記と指数表記のどちらを
選ぶかには関わらない(sample.kel の §2、sample.kel:112-113)。小さい側の境界は
指数 -4 にあり、0.0001 は固定小数点表記で、0.00001 は指数表記で表示する。下の出力の
うち 0.000123 は 1.23e-4、100000.0 は 1e5、1000000000000000.0 は 1e15 の
ほうが短いが、どれも使わない:

  $ cat > short.kel <<'KEL'
  > echoln(show(0.0001))
  > echoln(show(0.00001))
  > echoln(show(0.000123))
  > echoln(show(100000.0))
  > echoln(show(1.0e15))
  > KEL
  $ diktor short.kel
  0.0001
  1e-5
  0.000123
  100000.0
  1000000000000000.0

show の結果は、そのままソースに書ける:

  $ cat > roundtrip.kel <<'KEL'
  > let a: Float64 = 12345678901234568.0
  > let b: Float64 = 1e16
  > let c: Float64 = 1e-5
  > echoln(show(a))
  > echoln(show(b))
  > echoln(show(c))
  > KEL
  $ diktor roundtrip.kel
  12345678901234568.0
  1e16
  1e-5

非有限値は nan、inf、-inf と表示する。これらは Keleut のリテラルではないので、表記を規則として決めている。
NaN の符号は環境によって違うので、符号付きの NaN も nan と表示する:

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

実行時エラーの中の Float64 も、読み戻すと同じ値になる最短の表記で表示する。
警告が示す反例(1.0)は、実際にどの節にも一致しない値である:

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

浮動小数のパターンが重複しているかどうかは、値ごとに異なるキーで判定する。
近いが異なる値の節を、冗長と誤って警告しない:

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

+0.0 と -0.0 は同じパターンとして扱う(実行時の == の結果に合わせる):

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

Int64 の 16 進リテラルのパターンは、64 ビットの値で区別する。
0x7FFFFFFFFFFFFFFF を -1 と同じ値とみなして、冗長と誤って警告することはない:

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

基数が違っても、値が同じなら同じパターンとして扱う:

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

反例には、節が扱っていない具体的な値を出す。文字列は空文字列、a、aa の順に、
Float64 は 0.0 から、整数は 0 から順に探し、節にない最初の値を出す:

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

i32、i64、f64 以外の接尾辞は言語にないので、型エラーとして拒否し、終了コード 1 で終了する
(LangSpec §4.2、§15.5)。
診断は、ソースに書いたとおりの表記でリテラルと接尾辞を示す。
幅の大きすぎる接尾辞 i9999 も、ほかの接尾辞と同じ診断になる:

  $ printf 'echoln(show(1u8))\n' > u8.kel
  $ diktor u8.kel
  ! u8.kel:1:13: 型エラー: 数値リテラル 1u8 の接尾辞 u8 はありません(接尾辞は i32、i64、f64 だけです)
  [1]

  $ printf 'echoln(show(1i9999))\n' > w9999.kel
  $ diktor w9999.kel
  ! w9999.kel:1:13: 型エラー: 数値リテラル 1i9999 の接尾辞 i9999 はありません(接尾辞は i32、i64、f64 だけです)
  [1]

先頭に 0 のある接尾辞も、トークンはソースの表記のままである(1i032 は 1i32 にならない):

  $ printf 'let x = 1i032\n' > lead0.kel
  $ diktor --dump-tokens lead0.kel | tail -2
     1  1i032
     2  <EOF>

意味を持つ接尾辞は i32、i64、f64 の 3 つだけで、同じ値に読める別の表記(i032、f064)は
ほかの接尾辞と同じく受理しない(LangSpec §4.2、付録 A.2):

  $ diktor lead0.kel
  ! lead0.kel:1:9: 型エラー: 数値リテラル 1i032 の接尾辞 i032 はありません(接尾辞は i32、i64、f64 だけです)
  [1]
  $ printf 'echoln(show(7f064))\n' > lead0f.kel
  $ diktor lead0f.kel
  ! lead0f.kel:1:13: 型エラー: 数値リテラル 7f064 の接尾辞 f064 はありません(接尾辞は i32、i64、f64 だけです)
  [1]

基数付きのリテラル、浮動小数のリテラルの接尾辞、パターンの位置、対話的な実行でも同じ型エラーになる:

  $ printf 'let x = 0xffu8\n' > hexu8.kel
  $ diktor hexu8.kel
  ! hexu8.kel:1:9: 型エラー: 数値リテラル 0xffu8 の接尾辞 u8 はありません(接尾辞は i32、i64、f64 だけです)
  [1]
  $ printf 'let x = 1.5f32\n' > f32.kel
  $ diktor f32.kel
  ! f32.kel:1:9: 型エラー: 数値リテラル 1.5f32 の接尾辞 f32 はありません(接尾辞は i32、i64、f64 だけです)
  [1]
  $ cat > patsfx.kel <<'EOF'
  > let f(n: Int32): Int32 = n match {
  >   case 1i8 => 0
  >   case _ => 1
  > }
  > EOF
  $ diktor patsfx.kel
  ! patsfx.kel:2:8: 型エラー: 数値リテラル 1i8 の接尾辞 i8 はありません(接尾辞は i32、i64、f64 だけです)
  [1]
  $ printf '1u8\n1 + 1\n' | diktor --repl
  ! <stdin>:1:1: 型エラー: 数値リテラル 1u8 の接尾辞 u8 はありません(接尾辞は i32、i64、f64 だけです)
  _ : Int32 = 2

浮動小数の本体に整数の接尾辞を付けたリテラルは、接尾辞の幅を調べる前に、本体のエラーとして報告する:

  $ printf 'let x = 1.5i8\n' > floati8.kel
  $ diktor floati8.kel
  ! floati8.kel:1:9: 型エラー: 数値リテラル 1.5i8 は浮動小数の本体に整数接尾辞が付いています
  [1]

Int8 は言語にない数値型の名前なので、宣言のない通常の型名として解決する。
int8.kel は型引数のない Int8 を型の位置に書く。宣言がないので未知の型になり、
診断に数値型の一覧が付く。
int8user.kel は、ユーザが同じ名前の型を宣言すれば使えることを示す:

  $ printf 'let f(x: Int8): Int8 = x\n' > int8.kel
  $ diktor int8.kel
  ! int8.kel:1:10: 型エラー: 未知の型: Int8(数値型は Int32、Int64、Float64 だけです)
  [1]
  $ cat > int8user.kel <<'EOF'
  > newtype Int8 = Int8(Int32)
  > let f(x: Int8): Int8 = x
  > echoln("ok")
  > EOF
  $ diktor int8user.kel
  ok

小数部を省いた浮動小数リテラル(1.、2.e3、1.f64)も書ける:

  $ cat > dotlit.kel <<'KEL'
  > let x: Float64 = 1.
  > let y = 2.e3
  > let z = 1.f64
  > echoln(show(x))
  > echoln(show(y))
  > echoln(show(z))
  > KEL
  $ diktor dotlit.kel
  1.0
  2000.0
  1.0

照合対象が Int32 のとき、10 進の 4294967295 は Int32 として読めない。同じビット列になる
16 進の 0xFFFFFFFF の節と並べても、宣言の終わりに型エラーになる(LangSpec §4.2):

  $ cat > mask.kel <<'KEL'
  > let f(x: Int32): Int32 = x match {
  >   case 4294967295 => 1
  >   case 0xFFFFFFFF => 2
  >   case _          => 3
  > }
  > echoln(show(f(0 - 1)))
  > KEL
  $ diktor --type-check mask.kel
  f : (Int32) => Int32
  ! mask.kel:2:8: 型エラー: 数値リテラルのパターン 4294967295 は Int32 の範囲を超えるので、どの値にも一致しません
  [1]

照合対象が Int64 のとき、0xFFFFFFFF と -1 は別の値なので、網羅性検査は両方の節を
残し、-1 の節を冗長と報告しない(Int32 として読めば、どちらも同じ -1 になる):

  $ cat > mask64.kel <<'KEL'
  > let f(x: Int64): Int32 = x match {
  >   case 0xFFFFFFFF => 1
  >   case -1 => 2
  >   case _ => 3
  > }
  > echoln(show(f(-1i64)) + show(f(4294967295i64)))
  > KEL
  $ diktor mask64.kel
  21
  $ diktor --type-check --strict-exhaustive mask64.kel
  f : (Int64) => Int32
  _ : {}

パターンの整数リテラルは、宣言の終わりに照合対象の型で読み、読めなければ
そのリテラルを指す型エラーにする(LangSpec §4.2)。読める範囲は、10 進では符号付きの範囲、
16 進ではビット幅で決まる。入れ子のパターン、操作節の引数、型が既定化で
Int32 に決まる注釈なしの引数でも同じである:

  $ cat > litpat.kel <<'KEL'
  > let a(x: Int32): Int32 = x match { case 0x1FFFFFFFF => 1  case _ => 2 }
  > KEL
  $ diktor litpat.kel
  ! litpat.kel:1:41: 型エラー: 数値リテラルのパターン 0x1FFFFFFFF は Int32 の範囲を超えるので、どの値にも一致しません
  [1]
  $ printf 'let b(x: Int64): Int32 = x match { case 9223372036854775808 => 1  case _ => 2 }\n' > lit64.kel
  $ diktor lit64.kel
  ! lit64.kel:1:41: 型エラー: 数値リテラルのパターン 9223372036854775808 は Int64 の範囲を超えるので、どの値にも一致しません
  [1]
  $ printf 'let c(o: Option[Int32]): Int32 = o match { case Some(4294967295) => 1  case _ => 2 }\n' > litnest.kel
  $ diktor litnest.kel
  ! litnest.kel:1:54: 型エラー: 数値リテラルのパターン 4294967295 は Int32 の範囲を超えるので、どの値にも一致しません
  [1]
  $ printf 'let d = fn(x) => x match { case 4294967295 => 1i32  case _ => 2i32 }\n' > litdef.kel
  $ diktor litdef.kel
  ! litdef.kel:1:33: 型エラー: 数値リテラルのパターン 4294967295 は Int32 の範囲を超えるので、どの値にも一致しません
  [1]
  $ cat > litop.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = { perform ask(7) } handle {
  >   case ask(4294967295) => resume(1)
  >   case ask(_) => resume(2)
  >   case return(v) => v
  > }
  > KEL
  $ diktor litop.kel
  ! litop.kel:3:12: 型エラー: 数値リテラルのパターン 4294967295 は Int32 の範囲を超えるので、どの値にも一致しません
  [1]

型の境界値のリテラルと、その型で読めるリテラルは受理する。ローカルの束縛で、網羅性検査の後に
照合対象の型が Int64 に決まる形も、Int64 で読んで受理する:

  $ cat > litok.kel <<'KEL'
  > let f(x: Int32): Int32 = x match {
  >   case 2147483647 => 1
  >   case -2147483648 => 2
  >   case 0xFFFFFFFF => 3
  >   case _ => 4
  > }
  > let id[A](y: A): A = y
  > let g(n: Int64): Int32 = {
  >   let k = id(fn(x) => x match { case 4294967295 => 1  case _ => 2 })
  >   k(n)
  > }
  > echoln(show(f(0 - 1)) + show(g(4294967295i64)))
  > KEL
  $ diktor litok.kel
  31

浮動小数の本体に整数の接尾辞は書けない。小数部を省いた形(1.)と指数の付いた形(1e0)に
整数の接尾辞を付けたリテラルも、型エラーで拒否する:

  $ printf 'let x = 1.i32\n' > fi.kel
  $ diktor --type-check fi.kel
  ! fi.kel:1:9: 型エラー: 数値リテラル 1.i32 は浮動小数の本体に整数接尾辞が付いています
  [1]

  $ printf 'let y = 1e0i64\n' > fe.kel
  $ diktor --type-check fe.kel
  ! fe.kel:1:9: 型エラー: 数値リテラル 1e0i64 は浮動小数の本体に整数接尾辞が付いています
  [1]

注釈のない引数(型は既定化の前で、Fractional の制約を持つ型変数である)でも、反例を浮動小数の表記で出す:

  $ cat > wit.kel <<'KEL'
  > let h = fn(x) => x match {
  >   case 0.0 => 1i32
  >   case 1.0 => 2i32
  > }
  > KEL
  $ diktor --type-check wit.kel
  h : (Float64) => Int32
  ⚠ match が非網羅的です。例えば 2.0 が漏れています

残りの 3 つの変換(__i32_to_i64、__i32_to_f64、__i64_to_f64)は、どの入力にも結果が
あるので、実行時エラーにならない。__i64_to_f64 は、仮数部に収まらない値を丸める:

  $ cat > conv3.kel <<'KEL'
  > echoln(show(__i32_to_i64(2147483647)))
  > echoln(show(__i32_to_f64(2147483647)))
  > echoln(show(__i64_to_f64(9007199254740993i64)))
  > KEL
  $ diktor conv3.kel
  2147483647
  2147483647.0
  9007199254740992.0

整数演算のオーバーフローは折り返す(LangSpec §4.3)。sample.kel の §2 と §14 は、この動作を暫定としている。
変換の実行時エラーと扱いが違うのは、整数演算が必ずその型で表現できる値を返すためである:

  $ cat > wrap.kel <<'KEL'
  > let maxi = 2147483647
  > let mini = 0 - maxi - 1
  > echoln(show(maxi + 1))
  > echoln(show(mini - 1))
  > echoln(show(maxi * 2))
  > echoln(show(9223372036854775807i64 + 1i64))
  > KEL
  $ diktor wrap.kel
  -2147483648
  2147483647
  -2
  -9223372036854775808

String は UTF-8 のバイト列である(sample.kel の §2)。長さも部分文字列もバイト単位で数える。Char 型はない:

  $ cat > utf8.kel <<'KEL'
  > echoln(show(__string_length("あ")))
  > echoln(__string_sub("あい", 0, 3))
  > KEL
  $ diktor utf8.kel
  3
  あ

  $ printf 'let c: Char = 1\n' > nochar.kel
  $ diktor --type-check nochar.kel
  ! nochar.kel:1:8: 型エラー: 未知の型: Char
  [1]

非有限値のリテラルはない。文字列化した表記 nan と inf は読み戻せない(sample.kel の §14 の TODO):

  $ printf 'let x: Float64 = nan\n' > nanlit.kel
  $ diktor --type-check nanlit.kel
  ! nanlit.kel:1:18: 型エラー: 未束縛の変数: nan
  [1]
