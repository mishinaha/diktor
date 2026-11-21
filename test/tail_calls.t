末尾呼び出し(LangSpec §5.7)。OCAMLRUNPARAM=l=100k で OCaml のスタックの上限を
102400 ワードに絞り、末尾呼び出しと末尾 resume を 10 万回続けても
スタックオーバーフローにならないことを確かめる。

対照として、非末尾の再帰は、同じ上限と同じ回数でスタックを使い切る。
この上限が有効であることを、このブロックで確かめる:

  $ cat > nontail.kel <<'KEL'
  > let rec sum(n: Int32): Int32 = (n == 0) match { case true => 0 case false => n + sum(n - 1) }
  > echoln(show(sum(100000)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor nontail.kel
  実行時エラー: スタックオーバーフロー(再帰が深すぎます)
  [3]

match の節からの自己再帰:

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

ブロックの let の後にある、ガード付きの節:

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

操作節の末尾 resume。節が resume だけの形、文の後の resume、
match の節の resume、run の本体の resume、&& の右辺の resume:

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

末尾位置にない resume は保証の対象外で、この実装では resume のたびにスタックを使う:

  $ cat > nontail_resume.kel <<'KEL'
  > effect Tick = { tick: () => Unit }
  > let rec ticks(n: Int32): Unit @ Tick = (n == 0) match { case true => () case false => { perform tick(); ticks(n - 1) } }
  > ticks(100000) handle { case tick() => { let u = resume(); u } }
  > echoln("ok")
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor nontail_resume.kel
  実行時エラー: スタックオーバーフロー(再帰が深すぎます)
  [3]

制約付きの多相関数の自己再帰と、Eq の制約を持つ相互再帰。
辞書を渡す呼び出しも末尾位置に置ける:

  $ cat > dict.kel <<'KEL'
  > let rec go[A: Add](n: Int32, x: A, acc: A): A = (n == 0) match { case true => acc case false => go(n - 1, x, acc + x) }
  > echoln(show(go(100000, 1, 0)))
  > let rec ev(n: Int32, a) = n == 0 || od(n - 1, a)
  > and od(n: Int32, a) = n != 0 && a == a && ev(n - 1, a)
  > echoln(show(ev(100000, "x")))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor dict.kel
  100000
  true

再開しない操作(返り値の型が Never。LangSpec §13.1)の節の本体。処理系は継続を捨ててから
本体をハンドラ式の末尾位置で評価する(§5.7、§13.6)ので、節から再帰で書いた再試行は、
回数が増えてもメモリが増えない。同じ形を再開する操作で書くと、節の本体は末尾位置にないので
(§5.7)、この実装では小さい上限でスタックオーバーフローになる(回数が少なければ通るので、原因は深さである):

  $ cat > retry.kel <<'KEL'
  > effect Fail = { throw: (String) => Never }
  > let rec retry(n: Int32): Int32 =
  >   (if n == 0 then 0 else perform throw("again")) handle {
  >     case throw(e) => retry(n - 1)
  >   }
  > echoln(show(retry(100000)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor retry.kel
  0
  $ cat > retryresume.kel <<'KEL'
  > effect Again = { again: () => Unit }
  > let rec retry(n: Int32): Int32 =
  >   (if n == 0 then 0 else { perform again(); 1 }) handle {
  >     case again() => retry(n - 1)
  >   }
  > echoln(show(retry(1000)))
  > echoln(show(retry(100000)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor retryresume.kel
  0
  実行時エラー: スタックオーバーフロー(再帰が深すぎます)
  [3]

cancel 節から起こした再開しない操作による破棄が抑制された後に、ハンドラの本体の中で
評価される節の本体も、末尾位置にある(§5.7、§13.6)。外側のハンドラ宛ての、抑制される破棄を cancel 節が直接起こす形
(retrycancel)でも、cancel 節が起こした再開する操作の節が起こす形(retrycancelvia)でも、
破棄の宛先が、破棄を進めているそのハンドラ自身である形(retrycancelsame)でも、再試行の回数が増えてもメモリが増えない。
抑制のたびに、同じ診断が 1 行記録される:

  $ cat > retrycancel.kel <<'KEL'
  > effect Fail = { throw: (String) => Never }
  > effect Stop = { stop: () => Never }
  > effect Res = { use: () => Unit }
  > let rec loop(n: Int32): Int32 =
  >   if n == 0 then 0 else
  >   ({ perform use(); perform stop(); 1 }) handle {
  >     case use() => resume()
  >     case cancel => perform throw("from cancel")
  >   } handle {
  >     case stop() => loop(n - 1)
  >   }
  > let r = loop(100000) handle {
  >   case throw(e) => { echoln("caught " + e); 1 }
  > }
  > echoln(show(r))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor retrycancel.kel 2> err.txt
  0
  $ sort err.txt | uniq -c | sed 's/^ *//'
  100000 cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました
  $ cat > retrycancelvia.kel <<'KEL'
  > effect Fail = { throw: (String) => Never }
  > effect Ask = { ask: () => Int32 }
  > effect Stop = { stop: () => Never }
  > effect Res = { use: () => Unit }
  > let rec loop(n: Int32): Int32 =
  >   if n == 0 then 0 else
  >   ({ perform use(); perform stop(); 1 }) handle {
  >     case use() => resume()
  >     case cancel => { let a = perform ask(); () }
  >   } handle {
  >     case stop() => loop(n - 1)
  >   }
  > let r = (loop(100000) handle {
  >   case ask() => perform throw("from ask")
  > }) handle {
  >   case throw(e) => { echoln("caught " + e); 1 }
  > }
  > echoln(show(r))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor retrycancelvia.kel 2> err.txt
  0
  $ sort err.txt | uniq -c | sed 's/^ *//'
  100000 cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました
  $ cat > retrycancelsame.kel <<'KEL'
  > effect Fail = { throw: (String) => Never }
  > effect Res = { use: () => Unit }
  > let rec loop(n: Int32): Int32 =
  >   if n == 0 then 0 else
  >   ({ perform use(); perform throw("first") }) handle {
  >     case use() => resume()
  >     case cancel => perform throw("from cancel")
  >   } handle {
  >     case throw(e) => loop(n - 1)
  >   }
  > echoln(show(loop(100000)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor retrycancelsame.kel 2> err.txt
  0
  $ sort err.txt | uniq -c | sed 's/^ *//'
  100000 cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました

破棄が抑制された外側のハンドラの return 節も末尾位置にあり(§5.7)、return 節から再帰しても、
回数が増えてもメモリが増えない:

  $ cat > retcancelret.kel <<'KEL'
  > effect Fail = { throw: (String) => Never }
  > effect Stop = { stop: () => Never }
  > effect Res = { use: () => Unit }
  > let rec loop(n: Int32): Int32 =
  >   if n == 0 then 0 else
  >   (({ perform use(); perform stop(); 1 }) handle {
  >     case use() => resume()
  >     case cancel => perform throw("from cancel")
  >   } handle {
  >     case stop() => 5
  >   }) handle {
  >     case throw(e) => { echoln("caught " + e); 1 }
  >     case return(x) => loop(n - 1)
  >   }
  > echoln(show(loop(100000)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor retcancelret.kel 2> err.txt
  0
  $ sort err.txt | uniq -c | sed 's/^ *//'
  100000 cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました

再開しない操作の節の値が、同じハンドラの末尾位置にない resume の返り値になる形(§5.7 の
但し書き)。節の値を受け取った resume(1) の後ろの計算が残るので、節の本体は末尾位置に
ならず、この実装では小さい上限でスタックオーバーフローになる:

  $ cat > retryresumepath.kel <<'KEL'
  > effect E = { throw: (String) => Never, ask: () => Int32 }
  > effect Res = { use: () => Unit }
  > let rec retry(n: Int32, acc: Int32): Int32 =
  >   (if n == 0 then acc else ({ perform use(); perform throw("again") }) handle {
  >     case use() => resume()
  >     case cancel => { let a = perform ask(); () }
  >   }) handle {
  >     case throw(e) => retry(n - 1, acc + 1)
  >     case ask() => { let x = resume(1); x }
  >   }
  > echoln(show(retry(100000, 0)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor retryresumepath.kel
  実行時エラー: スタックオーバーフロー(再帰が深すぎます)
  [3]
