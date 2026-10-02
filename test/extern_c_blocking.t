注釈のない extern "C" は @ Blocking と書いたものと同じ型になる。pub extern でも同じ:

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

  $ cat > cdef.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > module Math { pub extern "C" let cos(x: Float64): Float64 }
  > KEL
  $ diktor --type-check cdef.kel
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  Math.cos : (Float64) => Float64 @ {Blocking extends R1}

"prim" の省略は従来どおり行多相で、@ {} の本体から呼べる:

  $ cat > pdef.kel <<'KEL'
  > extern "prim" let __int32_add(x: Int32, y: Int32): Int32
  > let f(x: Int32): Int32 @ {} = __int32_add(x, 1)
  > KEL
  $ diktor --type-check --no-prelude pdef.kel
  __int32_add : (Int32, Int32) => Int32
  f : (Int32) => Int32

Blocking はトップレベルに残せるので、注釈のない sqrt をトップレベルから呼べる:

  $ cat > ctop.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > let root = sqrt(9.0)
  > echoln(show(root))
  > KEL
  $ diktor ctop.kel
  3.0

par_map のコールバックの行は @ {} なので、注釈のない sqrt を直接は呼べない:

  $ cat > cpar.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > let arr(): Array[Float64] = run h { MutableArray.freeze(MutableArray.new(2, 4.0)) }
  > let ys = par_map(arr(), fn(x) => sqrt(x))
  > KEL
  $ diktor --type-check cpar.kel
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  arr : () => Array[Float64]
  ! cpar.kel:3:34: 型エラー: ラベル Blocking がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

@ {} と注釈した関数の本体からも、注釈のない sqrt を直接は呼べない(par_map を使わない形):

  $ cat > cclosed.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > let f(x: Float64): Float64 @ {} = sqrt(x)
  > KEL
  $ diktor --type-check cclosed.kel
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  ! cclosed.kel:2:35: 型エラー: ラベル Blocking がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

pinned で包めば Blocking が除かれ、同じ呼び出しが通る:

  $ cat > cpin.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > let arr(): Array[Float64] = run h { MutableArray.freeze(MutableArray.new(2, 4.0)) }
  > let ys = par_map(arr(), fn(x) => pinned(fn() => sqrt(x)))
  > echoln(show(Array.get(ys, 0)))
  > KEL
  $ diktor cpin.kel
  2.0

@ を省略した pub let の本体は純粋でなければならないので、注釈のない sqrt を呼べない:

  $ cat > cpub.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > pub let r(x: Float64): Float64 = sqrt(x)
  > KEL
  $ diktor --type-check cpub.kel
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  ! cpub.kel:2:34: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: 行 ς1 は注釈で固定された行変数なので、ラベル Blocking を足せません(注釈側に Blocking を(必要なら引数つきで)書き足してください))
  [1]

ブロックしない外部関数は、行変数を明示して行多相にする。par_map のコールバック、
@ Console の本体、@ を省略した pub let の本体のどれからも呼べる:

  $ cat > cpure.kel <<'KEL'
  > extern "C" let sin[E](x: Float64): Float64 @ E
  > pub extern "C" let cos[E](x: Float64): Float64 @ E
  > let arr(): Array[Float64] = run h { MutableArray.freeze(MutableArray.new(2, 0.0)) }
  > let ys = par_map(arr(), fn(x) => sin(x))
  > let loud(x: Float64): Float64 @ Console = { echo("x "); cos(x) }
  > pub let wrap(x: Float64): Float64 = sin(x) + cos(x)
  > echoln(show(Array.get(ys, 0)))
  > echoln(show(loud(0.0)))
  > echoln(show(wrap(0.0)))
  > KEL
  $ diktor --type-check cpure.kel
  sin : (Float64) => Float64
  cos : (Float64) => Float64
  arr : () => Array[Float64]
  ys : Array[Float64]
  loud : (Float64) => Float64 @ {Console extends R1}
  wrap : (Float64) => Float64
  _ : {}
  _ : {}
  _ : {}
  $ diktor cpure.kel
  0.0
  x 1.0
  1.0
