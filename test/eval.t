評価器(第14章)のゴールデンテストである。期待出力を変えるときは、差分を目で確かめてから dune promote で更新する。

基本の評価(リテラルの既定化、レコード、タプル、newtype、run と MutableArray と freeze、構造的な等値比較):

  $ cat > basics.kel <<'EOF'
  > echoln("hello, keleut")
  > let x = 1 + 2
  > echoln(show(x * 10))
  > let (a, b) = (10, "ten")
  > echoln(b + "=" + show(a))
  > let r = {x = 1, y = 2}
  > echoln(show(r.x + r.y))
  > let upd = {r with x = 100}
  > echoln(show(upd.x + upd.y))
  > let t = (1, "two", true)
  > echoln(t._1)
  > newtype MyList[A] = MyNil | MyCons(A, tail: MyList[A])
  > let rec sum_l(xs: MyList[Int32]): Int32 = xs match {
  >   case MyNil => 0
  >   case MyCons(h, t) => h + sum_l(t)
  > }
  > echoln(show(sum_l(MyCons(1, MyCons(2, MyCons(3, MyNil))))))
  > let frozen = run h {
  >   let a = MutableArray.new(3, 0)
  >   MutableArray.set(a, 0, 10)
  >   MutableArray.set(a, 2, 30)
  >   MutableArray.freeze(a)
  > }
  > echoln(show(Array.get(frozen, 0) + Array.get(frozen, 2)))
  > echoln(show((1, "a") == (1, "a")))
  > echoln(show({p = 1, q = 2} == {q = 2, p = 1}))
  > echoln(show(1.5 + 2.5))
  > echoln(show(7 / 2))
  > EOF
  $ diktor basics.kel
  hello, keleut
  30
  ten=10
  3
  102
  two
  6
  40
  true
  true
  4.0
  3

エフェクトの実行。sample.kel §9 の capture と try_、標準環境の with_stdout を使い、
巻き戻しのときに cancel 節を内側から外側の順に実行することを with_res で確かめる:

  $ cat > effects.kel <<'EOF'
  > let capture[A, E](body: () => A @ {Print extends E}): {value: A, output: String} @ E =
  >   body() handle {
  >     case print(message) => {
  >       let {value, output} = resume()
  >       {value, output = message + output}
  >     }
  >     case return(x) => {value = x, output = ""}
  >   }
  > effect Fail = { throw: (String) => Never }
  > let try_[A, E](body: () => A @ {Fail extends E}): #Ok(A) | #Err(String) @ E =
  >   body() handle {
  >     case throw(e)  => #Err(e)
  >     case return(x) => #Ok(x)
  >   }
  > let captured = capture(fn() => { println("one"); println("two"); 42 })
  > echo("output=" + captured.output)
  > echoln("value=" + show(captured.value))
  > let ok = try_(fn() => 1 + 1)
  > echoln(ok match { case #Ok(v) => "ok " + show(v) case #Err(e) => "err " + e })
  > let bad = try_(fn() => { perform throw("boom"); 1 })
  > echoln(bad match { case #Ok(v) => "ok " + show(v) case #Err(e) => "err " + e })
  > with_stdout(fn() => println("translated"))
  > effect Res = { use: (String) => Unit }
  > let with_res[A, E](name: String, body: () => A @ {Res, Console extends E}): A @ {Console extends E} = {
  >   echoln("open " + name)
  >   body() handle {
  >     case use(s)    => resume(echoln(name + " uses " + s))
  >     case return(x) => { echoln("close " + name); x }
  >     case cancel    => echoln("cancel " + name)
  >   }
  > }
  > let res = try_(fn() => {
  >   with _ = with_res("outer")
  >   with _ = with_res("inner")
  >   perform use("both")
  >   perform throw("abort")
  >   0
  > })
  > echoln(res match { case #Ok(v) => "ok " + show(v) case #Err(e) => "err " + e })
  > let normal = try_(fn() => {
  >   with _ = with_res("n1")
  >   perform use("x")
  >   7
  > })
  > echoln(normal match { case #Ok(v) => "ok " + show(v) case #Err(e) => "err " + e })
  > EOF
  $ diktor effects.kel
  output=one
  two
  value=42
  ok 2
  err boom
  translated
  open outer
  open inner
  inner uses both
  cancel inner
  cancel outer
  err abort
  open n1
  n1 uses x
  close n1
  ok 7

cancel 節は、自分のハンドラの外側で実行する(LangSpec §13.6)。cancel 節の中で起こした
操作は、自分の操作節ではなく、外側にある同じエフェクトのハンドラが受け取る。型検査が
cancel 節を外側の行で推論する(第11章 §11.24)のは、この動作に合わせるためである:

  $ cat > cancelouter.kel <<'EOF2'
  > effect Stop = { stop: () => {} }
  > effect Log = { note: (String) => {} }
  > let inner[E](): Int32 @ {Log, Stop, Console extends E} =
  >   { perform stop(); 1 } handle {
  >     case note(s) => { echo("INNER:" + s + "\n"); resume({}) }
  >     case cancel => { perform note("from-cancel"); () }
  >     case return(x) => x
  >   }
  > let mid[E](): Int32 @ {Stop, Console extends E} = inner() handle {
  >   case note(s) => { echo("MID:" + s + "\n"); resume({}) }
  >   case return(x) => x
  > }
  > let go[E](): Int32 @ {Console extends E} = mid() handle {
  >   case stop() => 99
  >   case return(x) => x
  > }
  > echoln(show(go()))
  > EOF2
  $ diktor cancelouter.kel
  MID:from-cancel
  99

その操作を受け取ったハンドラが resume せずに節を抜けても、その巻き戻しは cancel 節の中で抑制して
ログに記録するだけで、外へは伝えない(LangSpec §13.6):

  $ cat > cancelnores.kel <<'EOF2'
  > effect Stop = { stop: () => {} }
  > effect Log = { note: (String) => {} }
  > let inner[E](): Int32 @ {Log, Stop, Console extends E} =
  >   { perform stop(); 1 } handle {
  >     case note(s) => { echo("INNER:" + s + "\n"); resume({}) }
  >     case cancel => { perform note("from-cancel"); echo("AFTER\n") }
  >     case return(x) => x
  >   }
  > let mid[E](): Int32 @ {Stop, Console extends E} = inner() handle {
  >   case note(s) => { echo("MID:" + s + "\n"); 7 }
  >   case return(x) => x
  > }
  > let go[E](): Int32 @ {Console extends E} = mid() handle {
  >   case stop() => 99
  >   case return(x) => x
  > }
  > echoln(show(go()))
  > EOF2
  $ diktor cancelnores.kel
  MID:from-cancel
  cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました
  99

cancel 節の中で例外が起きると、その cancel 節の実行はそこで終わり、後ろの文は実行しない。
脱出は外へ伝えずに抑制してログに記録し、外側のハンドラの cancel 節と後続の文は続けて実行する
(sample.kel:585、LangSpec §13.6):

  $ cat > cancelabort.kel <<'EOF2'
  > effect A = { a: () => Unit }
  > effect B = { b: () => Unit }
  > effect Fail = { fail: () => Unit }
  > let r = ((perform fail() handle {
  >     case a() => resume()
  >     case cancel => { echoln("inner cancel start"); __panic("boom"); echoln("inner cancel rest") }
  >   }) handle {
  >   case b() => resume()
  >   case cancel => echoln("outer cancel")
  > }) handle {
  >   case fail() => echoln("caught")
  > }
  > echoln("after")
  > EOF2
  $ diktor cancelabort.kel
  caught
  inner cancel start
  cancel 節で例外が抑制されました: panic: boom
  outer cancel
  after

深いハンドラは再開した後の操作も受け取り、操作は最も内側のハンドラが受け取る。resume の返り値の型は handle 式全体の型である:

  $ cat > deep.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let inner = (perform ask() + perform ask()) handle {
  >   case ask() => resume(1)
  >   case return(x) => x
  > }
  > echoln(show(inner))
  > let nested = ((perform ask()) handle {
  >   case ask() => resume(10)
  >   case return(x) => x
  > }) handle {
  >   case ask() => resume(20)
  >   case return(x) => x
  > }
  > echoln(show(nested))
  > EOF
  $ diktor deep.kel
  2
  10

ユーザ定義のインスタンスのメソッドの呼び出し:

  $ cat > dispatch.kel <<'EOF'
  > newtype Meters(Int32)
  > type instance Add[Meters] {
  >   let add(a, b) = (a, b) match { case (Meters(x), Meters(y)) => Meters(x + y) }
  > }
  > let m = Meters(3) + Meters(4)
  > echoln(m match { case Meters(v) => show(v) })
  > type class MyShow[A] { val myshow: (A) => String }
  > type instance MyShow[Meters] {
  >   let myshow(m) = m match { case Meters(v) => show(v) + "m" }
  > }
  > echoln(myshow(Meters(7)))
  > EOF
  $ diktor dispatch.kel
  7
  7m

実行時エラー(終了コード 3)。??? への到達、resume を 2 回呼ぶアフィン違反、ゼロ除算を確かめる。
操作節の中の ??? でも、捨てた継続の中の cancel 節を実行する(第14章 §14.9 の、節が例外で脱出した経路):

  $ cat > hole.kel <<'EOF'
  > echoln("before")
  > let f = fn() => ???
  > echoln(show(f() + 1))
  > EOF
  $ diktor hole.kel
  before
  実行時エラー: ??? に到達しました
  [3]

  $ cat > affine.kel <<'EOF'
  > effect E1 = { get1: () => Int32 }
  > let r = (perform get1() + 1) handle {
  >   case get1() => { let a = resume(1); let b = resume(2); a + b }
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF
  $ diktor affine.kel
  実行時エラー: resume は高々1回しか呼べません(アフィン)
  [3]

  $ cat > divzero.kel <<'EOF'
  > echoln(show(1 / 0))
  > EOF
  $ diktor divzero.kel
  実行時エラー: ゼロ除算です
  [3]

  $ cat > holecancel.kel <<'EOF'
  > effect Res = { use: (String) => Unit }
  > effect Boom = { boom: () => Unit }
  > let with_res[A, E](name: String, body: () => A @ {Res, Console extends E}): A @ {Console extends E} =
  >   body() handle {
  >     case use(s)    => resume(echoln(name + " uses " + s))
  >     case return(x) => { echoln("close " + name); x }
  >     case cancel    => echoln("cancel " + name)
  >   }
  > let r = {
  >   with _ = with_res("r1")
  >   perform use("a")
  >   perform boom()
  >   0
  > } handle {
  >   case boom() => ???
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF
  $ diktor holecancel.kel
  r1 uses a
  cancel r1
  実行時エラー: ??? に到達しました
  [3]

性能の回帰テスト。10 万回の println を、節の本体が resume だけのときの短い経路で最後まで実行できる(第14章 §14.9):

  $ cat > perf.kel <<'EOF'
  > let rec loop(n: Int32): Unit @ Print =
  >   (n == 0) match {
  >     case true => ()
  >     case false => { println("x"); loop(n - 1) }
  >   }
  > with_stdout(fn() => loop(100000))
  > EOF
  $ diktor perf.kel | wc -l
  100000

プログラムを実行するときも、網羅性の警告は標準エラーに出る:

  $ cat > warn.kel <<'EOF'
  > newtype Opt2[A] = None2 | Some2(A)
  > let f = fn(o) => o match { case Some2(x) => x }
  > echoln("ran")
  > EOF
  $ diktor warn.kel
  ⚠ match が非網羅的です。例えば None2 が漏れています
  ran

節の本体が resume だけのときの短い経路でも、引数の評価で例外が起きれば継続を discontinue で捨てる(第14章 §14.9)。
捨てた継続の中の cancel 節と、自分の cancel 節の両方を実行する:

  $ cat > tailresume.kel <<'EOF2'
  > effect Res = { use: (String) => Unit }
  > effect Boom = { boom: () => Unit }
  > let with_res[A, E](name: String, body: () => A @ {Res, Console extends E}): A @ {Console extends E} =
  >   body() handle {
  >     case use(s)    => resume(echoln(name + " uses " + s))
  >     case return(x) => { echoln("close " + name); x }
  >     case cancel    => echoln("cancel " + name)
  >   }
  > let r = {
  >   with _ = with_res("r1")
  >   perform use("a")
  >   perform boom()
  >   0
  > } handle {
  >   case boom() => resume(???)
  >   case return(x) => x
  >   case cancel    => echoln("cancel outer")
  > }
  > echoln(show(r))
  > EOF2
  $ diktor tailresume.kel
  r1 uses a
  cancel r1
  cancel outer
  実行時エラー: ??? に到達しました
  [3]

再開する操作の節が resume を呼ぶ前に実行時エラーで脱出すると、継続はまだ生きているので、
その節のハンドラ自身の cancel 節も実行する(LangSpec §13.6)。clauseerr では、捨てた継続の中にある
Res のハンドラの cancel 節を先に、Ask のハンドラ自身の cancel 節を後に実行する:

  $ cat > clauseerr.kel <<'EOF2'
  > effect Res = { use: () => Unit }
  > effect Ask = { ask: () => Int32 }
  > let r = ({ perform use(); perform ask() + 1 }) handle {
  >   case use() => resume()
  >   case cancel => echoln("cancel res")
  > } handle {
  >   case ask() => { echoln("ask clause"); 1 / 0 }
  >   case cancel => echoln("cancel ask")
  > }
  > echoln(show(r))
  > EOF2
  $ diktor clauseerr.kel
  ask clause
  cancel res
  cancel ask
  実行時エラー: ゼロ除算です
  [3]

resume が戻った後の脱出では、継続は消費済みなので、ハンドラ自身の cancel 節は実行しない。
再開した計算の中のハンドラは、return 節で正常に終了している:

  $ cat > clauseresumed.kel <<'EOF2'
  > effect Res = { use: () => Unit }
  > effect Ask = { ask: () => Int32 }
  > let r = ({ perform use(); perform ask() + 1 }) handle {
  >   case use() => resume()
  >   case return(x) => { echoln("close res"); x }
  >   case cancel => echoln("cancel res")
  > } handle {
  >   case ask() => { let v = resume(1); echoln("resumed " + show(v)); v / 0 }
  >   case cancel => echoln("cancel ask")
  > }
  > echoln(show(r))
  > EOF2
  $ diktor clauseresumed.kel
  close res
  resumed 2
  実行時エラー: ゼロ除算です
  [3]

resumeinner は、ask(1) の節の resume で再開した計算の中で、同じハンドラの ask(0) の節が
自分の resume から戻った後に v / n で失敗する形である。ask(1) の節から見れば再開した
計算の中のエラーだが、評価中の ask(0) の節から見れば resume が戻った後なので、ハンドラ
自身の cancel 節は実行しない:

  $ cat > resumeinner.kel <<'EOF2'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1) + perform ask(0)) handle {
  >   case ask(n) => { echoln("clause " + show(n)); let v = resume(1); echoln("after " + show(n)); v / n }
  >   case cancel => echoln("cancel ask")
  > }
  > echoln(show(r))
  > EOF2
  $ diktor resumeinner.kel
  clause 1
  clause 0
  after 0
  実行時エラー: ゼロ除算です
  [3]

resumeinnerdeep は、ask(1) と ask(0) の 2 つの節がどちらも自分の resume の中にいる間に、
ハンドラの本体の 10 / 0 で失敗する形である。評価中の節はどれも自分の resume で再開した
計算の中にいるので、再開した計算の中のエラーとして、ハンドラ自身の cancel 節を 1 回実行する:

  $ cat > resumeinnerdeep.kel <<'EOF2'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1) + perform ask(0) + 10 / 0) handle {
  >   case ask(n) => { echoln("clause " + show(n)); let v = resume(1); echoln("after " + show(n)); v }
  >   case cancel => echoln("cancel ask")
  > }
  > echoln(show(r))
  > EOF2
  $ diktor resumeinnerdeep.kel
  clause 1
  clause 0
  cancel ask
  実行時エラー: ゼロ除算です
  [3]

resumeinnerpre は resumeinner と同じ並びで、ask(0) の節が resume の引数 10 / n の評価中、
つまり自分の resume を呼ぶ前に失敗する形である。評価中の ask(0) の節から見て継続は
まだ生きているので、ハンドラ自身の cancel 節を 1 回実行する:

  $ cat > resumeinnerpre.kel <<'EOF2'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1) + perform ask(0)) handle {
  >   case ask(n) => { echoln("clause " + show(n)); let v = resume(10 / n); v }
  >   case cancel => echoln("cancel ask")
  > }
  > echoln(show(r))
  > EOF2
  $ diktor resumeinnerpre.kel
  clause 1
  clause 0
  cancel ask
  実行時エラー: ゼロ除算です
  [3]

resumeret は、ask(1) の節の resume で再開した計算の中で、同じハンドラの return 節が
x / 0 で失敗する形である。この場合もハンドラ自身の cancel 節は実行しない:

  $ cat > resumeret.kel <<'EOF2'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1)) handle {
  >   case ask(n) => { echoln("clause " + show(n)); let v = resume(1); echoln("after " + show(n)); v }
  >   case return(x) => { echoln("return"); x / 0 }
  >   case cancel => echoln("cancel ask")
  > }
  > echoln(show(r))
  > EOF2
  $ diktor resumeret.kel
  clause 1
  return
  実行時エラー: ゼロ除算です
  [3]

resumestop は、ask(1) の節の resume で再開した計算の中で、同じハンドラの再開しない操作
stop の節の本体が失敗する形である。ハンドラ自身の cancel 節は実行しない:

  $ cat > resumestop.kel <<'EOF2'
  > effect Ask = { ask: (Int32) => Int32, stop: () => Never }
  > let r = (perform ask(1) + perform stop()) handle {
  >   case ask(n) => { echoln("clause " + show(n)); let v = resume(1); echoln("after " + show(n)); v }
  >   case stop() => { echoln("stop"); 1 / 0 }
  >   case cancel => echoln("cancel ask")
  > }
  > echoln(show(r))
  > EOF2
  $ diktor resumestop.kel
  clause 1
  stop
  実行時エラー: ゼロ除算です
  [3]

resumeguard は、ask(1) の節の resume で再開した計算の中で、ask(0) の節を選ぶときに、同じ
ハンドラの節のガード 10 / n > 0 が失敗する形である。ハンドラ自身の cancel 節を 1 回実行する:

  $ cat > resumeguard.kel <<'EOF2'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1) + perform ask(0)) handle {
  >   case ask(n) if 10 / n > 0 => { echoln("clause " + show(n)); let v = resume(1); echoln("after " + show(n)); v }
  >   case ask(n) => resume(0)
  >   case cancel => echoln("cancel ask")
  > }
  > echoln(show(r))
  > EOF2
  $ diktor resumeguard.kel
  clause 1
  cancel ask
  実行時エラー: ゼロ除算です
  [3]

resume を呼ぶ前に節の本体から操作を起こし、外側のハンドラが resume せずに継続を捨てた
場合も、ハンドラ自身の cancel 節を実行する。外側の節は再開する操作の節なので、破棄はその節の
値が決まった後に起き、cancel 節はその後で実行する:

  $ cat > clausestop.kel <<'EOF2'
  > effect Ask = { ask: () => Int32 }
  > effect Stop = { stop: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() => { echoln("ask clause"); perform stop() }
  >   case cancel => echoln("cancel ask")
  > } handle {
  >   case stop() => { echoln("stop: no resume"); 7 }
  > }
  > echoln(show(r))
  > EOF2
  $ diktor clausestop.kel
  ask clause
  stop: no resume
  cancel ask
  7

ガードが成り立たない操作節は、match と同じ規則で、同じハンドラの次の節に進む:

  $ cat > guardop.kel <<'EOF2'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1) + perform ask(2)) handle {
  >   case ask(n) if n == 1 => resume(100)
  >   case ask(n)           => resume(n * 10)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor guardop.kel
  120

絞り込みの節(一致しない引数があるパターンを書いた操作節)も、パターンが一致しなければ次の節に進む:

  $ cat > patop.kel <<'EOF2'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1) + perform ask(2)) handle {
  >   case ask(1) => resume(100)
  >   case ask(n) => resume(n)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor patop.kel
  102

ガードがなく、どんな引数にも一致する節より後ろにある、同じ操作の節には、到達不能の警告を出す:

  $ cat > deadop.kel <<'EOF2'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1)) handle {
  >   case ask(n) => resume(n)
  >   case ask(n) => resume(99)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor deadop.kel
  ⚠ 操作 ask の節は到達しません(前の節が既に取りこぼしません)
  1

コンストラクタが 1 つしかない newtype を分解し、引数が変数だけの操作節は、
どんな引数にも一致する節に数える(sample.kel:516)。絞り込みの節 MkBox(0) に一致しなかった値は、変数だけの節 MkBox(n) が受け取る:

  $ cat > soleop.kel <<'EOF2'
  > newtype Box = MkBox(Int32)
  > effect Ask = { ask: (Box) => Int32 }
  > let r = (perform ask(MkBox(0)) + perform ask(MkBox(5))) handle {
  >   case ask(MkBox(0)) => resume(100)
  >   case ask(MkBox(n)) => resume(n)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor soleop.kel
  105

コンストラクタが 1 つしかない newtype を分解し、引数が変数だけの節より後ろにある、
同じ操作の節には、到達不能の警告を出す:

  $ cat > soledead.kel <<'EOF2'
  > newtype Box = MkBox(Int32)
  > effect Ask = { ask: (Box) => Int32 }
  > let r = perform ask(MkBox(41)) handle {
  >   case ask(MkBox(n)) => resume(n + 1)
  >   case ask(b) => resume(0)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor soledead.kel
  ⚠ 操作 ask の節は到達しません(前の節が既に取りこぼしません)
  42

Int32 を 1 つ持つ newtype の引数にリテラルを書いた節と、Option を 1 つ持つ newtype の
引数に Some(n) を書いた節は、どんな引数にも一致する節には数えない:

  $ cat > solelit.kel <<'EOF2'
  > newtype Box = MkBox(Int32)
  > effect Ask = { ask: (Box) => Int32 }
  > let r = perform ask(MkBox(0)) handle {
  >   case ask(MkBox(0)) => resume(1)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor solelit.kel
  ! solelit.kel:3:9: 型エラー: 操作 ask には、ガードがなく、どんな引数にも一致する節がありません(どの節にも一致しなかった操作を外側のハンドラへ回す規則はありません)。ガードの無い case ask(_) を最後に置いてください
  [1]
  $ cat > soleopt.kel <<'EOF2'
  > newtype OBox = MkO(Option[Int32])
  > effect Ask = { ask: (OBox) => Int32 }
  > let r = perform ask(MkO(Some(1))) handle {
  >   case ask(MkO(Some(n))) => resume(n)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor soleopt.kel
  ! soleopt.kel:3:9: 型エラー: 操作 ask には、ガードがなく、どんな引数にも一致する節がありません(どの節にも一致しなかった操作を外側のハンドラへ回す規則はありません)。ガードの無い case ask(_) を最後に置いてください
  [1]

ラベルが 1 つの閉じた構造的ヴァリアントを分解し、引数が変数だけの節も、どんな引数にも一致する節に数える。
ラベルが 2 つある型では、1 つのラベルを選ぶ節だけでは、一致しない引数が残る:

  $ cat > solevar.kel <<'EOF2'
  > effect Ask = { ask: (#A(Int32)) => Int32 }
  > let r = perform ask(#A(3)) handle {
  >   case ask(#A(n)) => resume(n)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor solevar.kel
  3
  $ cat > solevar2.kel <<'EOF2'
  > type AB = #A(Int32) | #B
  > effect Ask = { ask: (AB) => Int32 }
  > let r = perform ask(#A(3)) handle {
  >   case ask(#A(n)) => resume(n)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor solevar2.kel
  ! solevar2.kel:3:9: 型エラー: 操作 ask には、ガードがなく、どんな引数にも一致する節がありません(どの節にも一致しなかった操作を外側のハンドラへ回す規則はありません)。ガードの無い case ask(_) を最後に置いてください
  [1]

絞り込みの節を複数合わせると引数を網羅できる場合も、
どんな引数にも一致する節が 1 つもなければ拒否する(sample.kel:516):

  $ cat > opcover.kel <<'EOF2'
  > effect Ask = { ask: (Option[Int32]) => Int32 }
  > let r = perform ask(Some(1)) handle {
  >   case ask(Some(n)) => resume(n)
  >   case ask(None) => resume(0)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor opcover.kel
  ! opcover.kel:2:9: 型エラー: 操作 ask には、ガードがなく、どんな引数にも一致する節がありません(どの節にも一致しなかった操作を外側のハンドラへ回す規則はありません)。ガードの無い case ask(_) を最後に置いてください
  [1]

拒否の診断が案内する節は、その操作の最初の節の引数の個数だけ `_` を並べた形である。
opnone0 は、引数のない操作 ask にガード付きの節だけを書いた形で、診断は case ask() を案内する。
opnone2 は、2 引数の操作 pair に絞り込みの節だけを書いた形で、診断は case pair(_, _) を案内する。
opnone2ok は、opnone2 の最後に、案内のとおりガードのない case pair(_, _) を追加した形で、
型検査に通って 1 を出力する:

  $ cat > opnone0.kel <<'EOF2'
  > effect Ask = { ask: () => Int32 }
  > let flag = true
  > let r = perform ask() handle {
  >   case ask() if flag => resume(1)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor opnone0.kel
  ! opnone0.kel:3:9: 型エラー: 操作 ask には、ガードがなく、どんな引数にも一致する節がありません(どの節にも一致しなかった操作を外側のハンドラへ回す規則はありません)。ガードの無い case ask() を最後に置いてください
  [1]
  $ cat > opnone2.kel <<'EOF2'
  > effect Pair = { pair: (Int32, Boolean) => Int32 }
  > let r = perform pair(1, true) handle {
  >   case pair(n, true) => resume(n)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor opnone2.kel
  ! opnone2.kel:2:9: 型エラー: 操作 pair には、ガードがなく、どんな引数にも一致する節がありません(どの節にも一致しなかった操作を外側のハンドラへ回す規則はありません)。ガードの無い case pair(_, _) を最後に置いてください
  [1]
  $ cat > opnone2ok.kel <<'EOF2'
  > effect Pair = { pair: (Int32, Boolean) => Int32 }
  > let r = perform pair(1, true) handle {
  >   case pair(n, true) => resume(n)
  >   case pair(_, _) => resume(0)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor opnone2ok.kel
  1

操作節の引数パターンのエラーは、どんな引数にも一致する節がないエラーより先に報告する。tell には絞り込みの節
tell(0) しかないが、報告するのは、その後ろにある ask の節の未知のコンストラクタである:

  $ cat > opunk.kel <<'EOF2'
  > newtype Box = MkBox(Int32)
  > effect Ask = { tell: (Int32) => Unit, ask: (Box) => Int32 }
  > let r = perform ask(MkBox(41)) handle {
  >   case tell(0) => resume(())
  >   case ask(Foo(n)) => resume(n)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor opunk.kel
  ! opunk.kel:5:12: 型エラー: 未知のコンストラクタ: Foo
  [1]

操作節の引数パターンのエラーは、handle の本体のエラーより先に報告する。本体の + "x" より
後ろの行にある、節のパターンのフィールドの個数のエラーを報告する:

  $ cat > oporder.kel <<'EOF2'
  > newtype Box = MkBox(Int32)
  > effect Ask = { ask: (Box) => Int32 }
  > let r = (perform ask(MkBox(41)) + "x") handle {
  >   case ask(MkBox(n, m)) => resume(n)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF2
  $ diktor oporder.kel
  ! oporder.kel:4:12: 型エラー: コンストラクタ MkBox のパターンは 1 個のフィールドを取ります(2 個与えられました)
  [1]

操作節のガードで起きた例外にも、3 つの経路の規約(第14章 §14.9)を適用する。継続を discontinue で
捨てるので、捨てた継続の中の cancel 節と、ハンドラ自身の cancel 節を実行する:

  $ cat > gexc.kel <<'EOF2'
  > effect Res = { use: (String) => Unit }
  > effect Ask = { ask: (Int32) => Int32 }
  > let with_res[A, E](name: String, body: () => A @ {Res, Console extends E}): A @ {Console extends E} =
  >   body() handle {
  >     case use(s)    => resume(echoln(name + " uses " + s))
  >     case return(x) => { echoln("close " + name); x }
  >     case cancel    => echoln("cancel " + name)
  >   }
  > let main() = {
  >   with _ = with_res("r1")
  >   perform use("a")
  >   let n = perform ask(1)
  >   echoln("got " + show(n))
  > } handle {
  >   case ask(n) if ??? => resume(n)
  >   case ask(n) => resume(n * 10)
  >   case return(x) => x
  >   case cancel => echoln("cancel outer")
  > }
  > main()
  > EOF2
  $ diktor gexc.kel
  r1 uses a
  cancel r1
  cancel outer
  実行時エラー: ??? に到達しました
  [3]

ガードから起こした操作で外側のハンドラが継続を捨てた場合も、巻き戻しはガードを通過し、cancel 節を実行する(第14章 §14.9):

  $ cat > gdrop.kel <<'EOF2'
  > effect Res = { use: (String) => Unit }
  > effect Esc = { esc: () => Boolean }
  > effect Ask = { ask: (Int32) => Int32 }
  > let with_res[A, E](name: String, body: () => A @ {Res, Console extends E}): A @ {Console extends E} =
  >   body() handle {
  >     case use(s)    => resume(echoln(name + " uses " + s))
  >     case return(x) => { echoln("close " + name); x }
  >     case cancel    => echoln("cancel " + name)
  >   }
  > let inner() = {
  >   with _ = with_res("r1")
  >   perform use("a")
  >   let n = perform ask(1)
  >   echoln("got " + show(n))
  > } handle {
  >   case ask(n) if perform esc() => resume(n)
  >   case ask(n) => resume(n * 10)
  >   case return(x) => x
  >   case cancel => echoln("cancel inner")
  > }
  > let outer() = {
  >   inner()
  >   echoln("after inner")
  > } handle {
  >   case esc() => { echoln("esc: continuation dropped"); {} }
  >   case return(x) => x
  >   case cancel => echoln("cancel outer")
  > }
  > outer()
  > echoln("done")
  > EOF2
  $ diktor gdrop.kel
  r1 uses a
  esc: continuation dropped
  cancel r1
  cancel inner
  done

標準出力への書き込みが失敗したときも、継続を discontinue で捨てる(第13章 §13.6)。標準出力を閉じて
バッファをいっぱいにすると、cancel 節の例外を抑制した記録が標準エラーに出る。この記録が出れば、
書き込みの例外が継続に届いて、cancel 節を実行したと分かる:

  $ cat > sinkfail.kel <<'EOF2'
  > effect Res = { use: (String) => Unit }
  > let with_res[A, E](name: String, body: () => A @ {Res, Console extends E}): A @ {Console extends E} =
  >   body() handle {
  >     case use(s)    => resume(echoln(name + " uses " + s))
  >     case return(x) => { echoln("close " + name); x }
  >     case cancel    => __panic("cancel of " + name + " blew up")
  >   }
  > let rec loop(n: Int32): Unit @ Console = (n == 0) match {
  >   case true => {}
  >   case false => { echoln("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"); loop(n - 1) }
  > }
  > let main() = {
  >   with _ = with_res("r1")
  >   perform use("a")
  >   loop(100000)
  > }
  > main()
  > EOF2
  $ diktor sinkfail.kel >&-
  cancel 節で例外が抑制されました: panic: cancel of r1 blew up
  diktor: 標準出力に書き出せません: Bad file descriptor
  [74]

トップレベルで名前を再束縛しても、先に定義した関数は、定義した時点の束縛を参照し続ける。
評価器は、名前を呼び出しの時点で探すのではなく、型検査が解決した参照先の宣言を使う
(第14章 §14.4):

  $ cat > shadow.kel <<'EOF2'
  > let f(): String = show(42)
  > let show(x: Int32): String = "SHADOW"
  > echoln(f())
  > echoln(show(1))
  > EOF2
  $ diktor shadow.kel
  42
  SHADOW

パス 1c が登録したシグネチャを使う前方参照は、参照元と宣言の間に別の名前の再束縛があっても、後ろの宣言を指す:

  $ cat > fwd5.kel <<'EOF2'
  > let f[E](): Int32 @ E = g(1)
  > let show(x: Int32): String = "SHADOW"
  > let g[E](x: Int32): Int32 @ E = x + 1
  > echoln(f() match { case 2 => "two" case _ => "other" })
  > EOF2
  $ diktor fwd5.kel
  two

組み込みのクラスと同じ名前の module が、そのクラスのメソッドと同じ名前の値を持つ形は、宣言の位置で
拒否する。修飾名 Add.add が、値の環境でクラスのメソッドの修飾名と同じ名前になり、区別できないからである。
受理するなら、クラスのメソッドの修飾名と同じ名前を可視性の検査から外す必要がある。外すと、同じ名前の
クラスを宣言するだけで、module の pub でない値を外から呼び出せてしまう:

  $ cat > k3.kel <<'EOF2'
  > let f(): Int32 = Add.add(1, 2)
  > module Add { extern "prim" let add(x: String, y: String): String }
  > echoln(show(f()))
  > EOF2
  $ diktor k3.kel
  ! k3.kel:2:14: 型エラー: module Add の add は型クラス Add のメソッド add と修飾名が衝突します(module か メソッドを改名してください)
  [1]

同じ名前の let が 2 つあるとき、前方参照は 1 つ目の束縛を指す(第11章 §11.36)。パス 1c は
1 つ目のシグネチャだけを登録するので、型検査と実行は同じ束縛を使う。fwd6 では、f の g("s") を
1 つ目の g の型で検査するので、型エラーになる:

  $ cat > fwd6.kel <<'EOF2'
  > let f[E](): String @ E = g("s")
  > let g[E](x: Int32): Int32 @ E = 7
  > let g[E](x: String): String @ E = "STR"
  > echoln(show(f()))
  > EOF2
  $ diktor fwd6.kel
  ! fwd6.kel:1:28: 型エラー: 型が一致しません: String と Int32
  [1]

クラスのメソッドと同じ名前のトップレベルの let を前方参照するときも、先にあるメソッドを指す。型検査は
プレリュードの show の型で検査し、実行でも同じ show を呼び出す:

  $ cat > fwd7.kel <<'EOF2'
  > let f(): String = show(42)
  > let show[E](x: Int32): String @ E = "SHADOW"
  > echoln(f())
  > echoln(show(42))
  > EOF2
  $ diktor fwd7.kel
  42
  SHADOW

  $ cat > fwd8.kel <<'EOF2'
  > let f(): Int32 = show(42)
  > let show[E](x: Int32): Int32 @ E = 99
  > echoln(Show.show(f() + 1))
  > EOF2
  $ diktor fwd8.kel
  ! fwd8.kel:1:5: 型エラー: 注釈された返り値型を満たしません(型が一致しません: Int32 と String)
  [1]

プレリュードの extern と同じ名前のクラスのメソッドを宣言したときも、非修飾名は、先にある
プレリュードの束縛を指す。型検査はプレリュードの束縛の型で検査し、実行でも同じプリミティブを
呼び出すので、型検査と実行が一致する:

  $ cat > fwd9.kel <<'EOF2'
  > type class W[A] { val __string_length: (A) => Int32 }
  > type instance W[String] { let __string_length(x) = 999 }
  > echoln(show(__string_length("abcdefgh")))
  > EOF2
  $ diktor fwd9.kel
  8

修飾した操作は、その完全な名前のエフェクトのハンドラだけが受け取る。E2 のハンドラが内側に
あっても、E1.op はそれを通り過ぎて、外側の h1 が受け取る:

  $ cat > leftmostrun.kel <<'EOF2'
  > effect E1 = { op: (String) => {} }
  > effect E2 = { op: (String) => {} }
  > let f[E](): {} @ {E1, E2 extends E} = perform E1.op("f")
  > let h1[A, E](b: () => A @ {E1, Console extends E}): A @ {Console extends E} =
  >   b() handle {
  >     case E1.op(s) => resume(echo("E1:" + s + "\n"))
  >     case return(x) => x
  >   }
  > let h2[A, E](b: () => A @ {E2, Console extends E}): A @ {Console extends E} =
  >   b() handle {
  >     case E2.op(s) => resume(echo("E2:" + s + "\n"))
  >     case return(x) => x
  >   }
  > h1(fn() => h2(fn() => f()))
  > EOF2
  $ diktor leftmostrun.kel
  E1:f

評価は正格である(LangSpec §5.1)。関数を呼び出す前にすべての引数を評価するので、
使わない引数も評価する。let の右辺とレコードのフィールドは束縛するときに評価し、
fn の本体は呼び出すまで評価しない(使うたびに評価する値束縛は LangSpec §6.4):

  $ cat > strict.kel <<'KEL'
  > let ignore2(a: Int32, b: Int32): Int32 = a
  > let noisy(n: Int32): Int32 @ Console = { echoln("eval " + show(n)); n }
  > let r = ignore2(noisy(1), noisy(2))
  > let unused = noisy(3)
  > let rec_ = {a = noisy(4), b = noisy(5)}
  > let lazy = fn() => noisy(6)
  > echoln("end " + show(r))
  > KEL
  $ diktor strict.kel
  eval 1
  eval 2
  eval 3
  eval 4
  eval 5
  end 1

with _ と with (_) は引数のない無名関数を、with _x は 1 引数の関数を渡す(LangSpec §6.5)。
この _ は、ほかの位置の _ と意味が異なる。1 引数の関数を要求する関数に with _ を使うと、型エラーになる:

  $ cat > with1.kel <<'KEL'
  > let zero[A, E](body: () => A @ E): A @ E = body()
  > let one[A, E](body: (Int32) => A @ E): A @ E = body(5)
  > let a(): Int32 = {
  >   with _ = zero()
  >   1
  > }
  > let b(): Int32 = {
  >   with _x = one()
  >   2
  > }
  > let c(): Int32 = {
  >   with (_) = zero()
  >   3
  > }
  > echoln(show(a() + b() + c()))
  > KEL
  $ diktor with1.kel
  6
  $ cat > with2.kel <<'KEL'
  > let one[A, E](body: (Int32) => A @ E): A @ E = body(5)
  > let b(): Int32 = {
  >   with _ = one()
  >   2
  > }
  > KEL
  $ diktor --type-check with2.kel
  one : ((Int32) => A) => A
  ! with2.kel:3:3: 型エラー: 引数の個数が一致しません: () => _A と (Int32) => _B(引数は 0 個と 1 個です)
  [1]
