前置の - と % は、演算子クラス Neg と Rem のメソッドを呼ぶ(LangSpec §4.2、§4.3、§12.4)。
Neg は Int32、Int64、Float64 に、Rem は Int32 と Int64 にインスタンスを持つ。

前置の - は変数、呼び出し、括弧の式に付けられる(乗除より強く結合することは、
下の dump.kel の木で確かめる)。-2i64 と -1.5 は負のリテラルで、Neg は呼ばない:

  $ cat > neg.kel <<'EOF'
  > let x: Int32 = 7
  > let f(n: Int32): Int32 = n
  > echoln(show(-x))
  > echoln(show(-2i64 * 3))
  > echoln(show(-1.5))
  > echoln(show(- -x))
  > echoln(show(-(x + 1)))
  > echoln(show(-x * 2))
  > echoln(show(2 - -x))
  > echoln(show(-f(3)))
  > echoln(show(Neg.neg(4)))
  > let y: Int64 = 5i64
  > echoln(show(-y))
  > EOF
  $ diktor neg.kel
  -7
  -6
  -1.5
  7
  -8
  -14
  9
  -3
  -4
  -5

% は * と / と同じ優先順位で左結合し、整数の除算と同じくゼロ方向に切り捨てた商の余りを返す:

  $ cat > rem.kel <<'EOF'
  > let x: Int32 = 7
  > echoln(show(x % 3))
  > echoln(show(-x % 3))
  > echoln(show(x % -3))
  > echoln(show(17i64 % 5))
  > echoln(show(1 + 7 % 4 * 2))
  > echoln(show(Rem.rem(9, 4)))
  > echoln(show(2 * 7 % 4))
  > echoln(show(7 % 5 % 3))
  > EOF
  $ diktor rem.kel
  1
  -1
  1
  2
  7
  1
  2
  2

括弧で囲まない数値リテラルに付いた - は、負のリテラルに畳む。そのため最小値を書ける。
括弧で囲むと Neg.neg の呼び出しになり、リテラルの範囲の検査を先に受ける:

  $ cat > minlit.kel <<'EOF'
  > echoln(show(-2147483648))
  > echoln(show(-9223372036854775808i64))
  > EOF
  $ diktor minlit.kel
  -2147483648
  -9223372036854775808
  $ echo 'echoln(show(-(2147483648)))' > minparen.kel
  $ diktor minparen.kel
  実行時エラー: 数値リテラルが範囲外です: 2147483648
  [3]
  $ printf 'let a = -1\nlet b = -a\nlet c = -(1)\nlet d = a %% 2\nlet e = -a * 2\nlet f = -a %% 3\n' > dump.kel
  $ diktor --dump-ast dump.kel
  (dlet (binding a = -1))
  (dlet (binding b = (- a)))
  (dlet (binding c = (- 1)))
  (dlet (binding d = (% a 2)))
  (dlet (binding e = (* (- a) 2)))
  (dlet (binding f = (% (- a) 3)))

インスタンスの無い型は型エラーになる。Float64 に Rem は無く、String に Neg は無い:

  $ echo 'echoln(show(1.5 % 2.0))' > remf.kel
  $ diktor remf.kel
  ! remf.kel:1:1: 型エラー: Float64 は Rem のインスタンスではありません
  [1]
  $ echo 'echoln(-"abc")' > negs.kel
  $ diktor negs.kel
  ! negs.kel:1:8: 型エラー: String は Neg のインスタンスではありません
  [1]

整数のゼロによる剰余は実行時エラーになる:

  $ printf 'let z: Int32 = 0\necholn(show(5 %% z))\n' > remz.kel
  $ diktor remz.kel
  実行時エラー: ゼロ除算です
  [3]

制約 [A: Neg] で、前置の - を多相に使える:

  $ cat > negpoly.kel <<'EOF'
  > let neg2[A: Neg](a: A): A = -a
  > echoln(show(neg2(5)))
  > echoln(show(neg2(2.5)))
  > EOF
  $ diktor negpoly.kel
  -5
  -2.5

- で始まる行は、前の行の二項の - として続く(LangSpec §2.3):

  $ printf 'let a: Int32 = 1\nlet b: Int32 = 2\nlet c = a\n-b\necholn(show(c))\n' > asi.kel
  $ diktor asi.kel
  -1
