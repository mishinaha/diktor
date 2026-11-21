@ を省略した extern "C" は、@ Blocking と書いたものと同じ型になる。pub extern でも同じである:

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

  $ cat > cdef.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > module Math { pub extern "C" let cos(x: Float64): Float64 }
  > KEL
  $ diktor --type-check cdef.kel
  sqrt : (Float64) => Float64 @ {Blocking}
  Math.cos : (Float64) => Float64 @ {Blocking}

extern "prim" で @ を省略すると、使うたびに新しい行変数になるので、@ {} と注釈した関数の本体から呼び出せる:

  $ cat > pdef.kel <<'KEL'
  > extern "prim" let __int32_add(x: Int32, y: Int32): Int32
  > let f(x: Int32): Int32 @ {} = __int32_add(x, 1)
  > KEL
  $ diktor --type-check --no-prelude pdef.kel
  __int32_add : (Int32, Int32) => Int32
  f : (Int32) => Int32 @ {}

Blocking はトップレベルに残せるので、@ を省略した sqrt をトップレベルから呼び出せる:

  $ cat > ctop.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > let root = sqrt(9.0)
  > echoln(show(root))
  > KEL
  $ diktor ctop.kel
  3.0

@ {} と注釈した関数の本体からは、@ を省略した sqrt を直接は呼び出せない:

  $ cat > cclosed.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > let f(x: Float64): Float64 @ {} = sqrt(x)
  > KEL
  $ diktor --type-check cclosed.kel
  sqrt : (Float64) => Float64 @ {Blocking}
  ! cclosed.kel:2:35: 型エラー: ラベル Blocking がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

pinned で囲めば Blocking が取り除かれ、同じ呼び出しが型検査に通る。最も外側の @ {} は、使うときに
行の末尾を開くので、f はトップレベルから呼び出せる:

  $ cat > cpin.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > let f(x: Float64): Float64 @ {} = pinned(fn() => sqrt(x))
  > echoln(show(f(4.0)))
  > KEL
  $ diktor cpin.kel
  2.0

最も外側の @ を省略した pub let の本体は純粋でなければならないので、その中から @ を省略した sqrt は呼び出せない:

  $ cat > cpub.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > pub let r(x: Float64): Float64 = sqrt(x)
  > KEL
  $ diktor --type-check cpub.kel
  sqrt : (Float64) => Float64 @ {Blocking}
  ! cpub.kel:2:34: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Blocking がありません(行は閉じています))
  [1]

ブロックしない外部関数は @ {} と書く(sin)。行変数を明示してもよい(cos)。閉じた行は、
使うときに行の末尾を開き、行変数はそのまま一致するので、@ {} と注釈した関数の本体、
@ Console の本体、@ を省略した pub let の本体のどれからも呼び出せる:

  $ cat > cpure.kel <<'KEL'
  > extern "C" let sin(x: Float64): Float64 @ {}
  > pub extern "C" let cos[E](x: Float64): Float64 @ E
  > let pure(x: Float64): Float64 @ {} = sin(x)
  > let loud(x: Float64): Float64 @ Console = { echo("x "); cos(x) }
  > pub let wrap(x: Float64): Float64 = sin(x) + cos(x)
  > echoln(show(pure(0.0)))
  > echoln(show(loud(0.0)))
  > echoln(show(wrap(0.0)))
  > KEL
  $ diktor --type-check cpure.kel
  sin : (Float64) => Float64 @ {}
  cos : (Float64) => Float64
  pure : (Float64) => Float64 @ {}
  loud : (Float64) => Float64 @ {Console}
  wrap : (Float64) => Float64 @ {}
  _ : {}
  _ : {}
  _ : {}
  $ diktor cpure.kel
  0.0
  x 1.0
  1.0

@ {} の sin を、@ Console の本体から直接呼び出す:

  $ cat > cpure2.kel <<'KEL'
  > extern "C" let sin(x: Float64): Float64 @ {}
  > let loud(x: Float64): Float64 @ Console = { echo("x "); sin(x) }
  > echoln(show(loud(0.0)))
  > KEL
  $ diktor --type-check cpure2.kel
  sin : (Float64) => Float64 @ {}
  loud : (Float64) => Float64 @ {Console}
  _ : {}
  $ diktor cpure2.kel
  x 0.0
