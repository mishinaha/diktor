真正末尾呼び出し(仕様 §5.7)。OCAMLRUNPARAM=l=100k でスタックの上限を
10 万語に絞り、末尾位置の呼び出しと末尾の resume を 10 万回続けても
Stack_overflow にならないことを確かめる。

対照：末尾でない再帰は、同じ上限と同じ回数でスタックを使い尽くす。
この上限が効いていることを、このブロックで確かめる:

  $ cat > nontail.kel <<'KEL'
  > let rec sum(n: Int32): Int32 = (n == 0) match { case true => 0 case false => n + sum(n - 1) }
  > echoln(show(sum(100000)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor nontail.kel
  実行時エラー: スタックオーバーフロー(再帰が深すぎます)
  [3]

match の腕からの自己再帰:

  $ cat > self.kel <<'KEL'
  > let rec loop(n: Int32, acc: Int32): Int32 =
  >   (n == 0) match { case true => acc case false => loop(n - 1, acc + 1) }
  > echoln(show(loop(100000, 0)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor self.kel
  100000

&& と || の右辺を通る相互再帰:

  $ cat > mutual.kel <<'KEL'
  > let rec even(n: Int32): Boolean = n == 0 || odd(n - 1)
  > and odd(n: Int32): Boolean = n != 0 && even(n - 1)
  > echoln(show(even(100000)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor mutual.kel
  true

ブロックの let の後の、ガード付きの腕:

  $ cat > block.kel <<'KEL'
  > let rec loop(n: Int32): Unit = {
  >   let m = n - 1
  >   (n == 0) match { case true => () case false if m >= 0 => loop(m) case false => () }
  > }
  > loop(100000)
  > echoln("ok")
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor block.kel
  ok

with が作る呼び出しと、無名関数の本体:

  $ cat > with.kel <<'KEL'
  > let call[A](x: Int32, k: (Int32) => A): A = k(x)
  > let rec loop(n: Int32): Unit = {
  >   with m = call(n - 1)
  >   (n == 0) match { case true => () case false => loop(m) }
  > }
  > loop(100000)
  > echoln("ok")
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor with.kel
  ok

高階関数の引数として渡した関数の呼び出し:

  $ cat > hof.kel <<'KEL'
  > let apply_to[A, B, E](f: (A) => B @ E, x: A): B @ E = f(x)
  > let rec loop(n: Int32): Unit = (n == 0) match { case true => () case false => apply_to(loop, n - 1) }
  > loop(100000)
  > echoln("ok")
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor hof.kel
  ok

型クラスのメソッドの呼び出し:

  $ cat > method.kel <<'KEL'
  > type class Step[A] { val step: (A, Int32) => Int32 }
  > newtype W = W(Int32)
  > type instance Step[W] { let step(w, n) = (n == 0) match { case true => 0 case false => step(w, n - 1) } }
  > echoln(show(step(W(1), 100000)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor method.kel
  0

末尾位置にある handle 式の return 節の本体:

  $ cat > retc.kel <<'KEL'
  > effect Tick = { tick: () => Unit }
  > let rec loop(n: Int32): Unit =
  >   (n == 0) match {
  >     case true => ()
  >     case false => { perform tick() } handle { case tick() => resume() case return(x) => loop(n - 1) }
  >   }
  > loop(100000)
  > echoln("ok")
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor retc.kel
  ok

操作節の末尾の resume。節が resume だけの形、文の後の resume、
match の腕の resume、run の本体の resume、&& の右辺の resume:

  $ cat > resume.kel <<'KEL'
  > effect Tick = { tick: () => Unit }
  > effect Ask = { ask: (Int32) => Int32 }
  > effect Test = { test: () => Boolean }
  > let rec ticks(n: Int32): Unit @ Tick = (n == 0) match { case true => () case false => { perform tick(); ticks(n - 1) } }
  > let rec asks(n: Int32, acc: Int32): Int32 @ Ask =
  >   (n == 0) match { case true => acc case false => asks(n - 1, acc + perform ask(n)) }
  > let rec tests(n: Int32): Boolean @ Test = (n == 0) match { case true => true case false => perform test() && tests(n - 1) }
  > ticks(100000) handle { case tick() => resume() }
  > echoln("bare")
  > let total = run h {
  >   let c = Ref.new(0)
  >   ticks(100000) handle { case tick() => { Ref.set(c, Ref.get(c) + 1); resume() } }
  >   Ref.get(c)
  > }
  > echoln(show(total))
  > echoln(show(asks(100000, 0) handle { case ask(x) => (x > 0) match { case true => resume(1) case false => resume(0) } }))
  > ticks(100000) handle { case tick() => run h { let r = Ref.new(()); resume(Ref.get(r)) } }
  > echoln("run")
  > echoln(show(tests(100000) handle { case test() => { let t = true; t && resume(true) } }))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor resume.kel
  bare
  100000
  100000
  run
  true

プレリュードの with_stdout(節が resume だけの形)の中のループ:

  $ cat > stdout.kel <<'KEL'
  > let rec loop(n: Int32): Unit @ Print = (n == 0) match { case true => () case false => { perform print(""); loop(n - 1) } }
  > with_stdout(fn() => loop(100000))
  > echoln("ok")
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor stdout.kel
  ok

末尾でない resume は保証の対象外で、この実装では resume のたびにスタックを使う:

  $ cat > nontail_resume.kel <<'KEL'
  > effect Tick = { tick: () => Unit }
  > let rec ticks(n: Int32): Unit @ Tick = (n == 0) match { case true => () case false => { perform tick(); ticks(n - 1) } }
  > ticks(100000) handle { case tick() => { let u = resume(); u } }
  > echoln("ok")
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor nontail_resume.kel
  実行時エラー: スタックオーバーフロー(再帰が深すぎます)
  [3]
