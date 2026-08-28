M8(評価器)のゴールデン。変更時は dune promote で更新し、必ず目視レビューすること。

基本の評価(リテラル既定化・レコード・タプル・newtype・run/Array・構造的等価):

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
  > let arr = run h {
  >   let a = Array.new(3, 0)
  >   Array.set(a, 0, 10)
  >   Array.set(a, 2, 30)
  >   Array.get(a, 0) + Array.get(a, 2)
  > }
  > echoln(show(arr))
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
  4.
  3

エフェクトの実行(sample.kel §9 相当: capture / try_ / with_stdout /
cancel の LIFO 自動巻き戻し):

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

深いハンドラと最内一致・resume の返り値 = handle 式全体の型:

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

ユーザ定義インスタンスの実行時ディスパッチ(D3):

  $ cat > dispatch.kel <<'EOF'
  > newtype Meters(Int32)
  > type class Add[A] { val add: (A, A) => A }
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

実行時エラー(exit 3): ??? 到達、resume のアフィン違反、ゼロ除算。
ハンドラ節内の ??? でも内側の cancel は走る(例外経路の discontinue、§8.4):

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

性能回帰: 10万回の println が末尾 resume 最適化で完走する(§8.4):

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

Run モードでも網羅性警告は stderr に出る:

  $ cat > warn.kel <<'EOF'
  > newtype Opt2[A] = None2 | Some2(A)
  > let f = fn(o) => o match { case Some2(x) => x }
  > echoln("ran")
  > EOF
  $ diktor warn.kel
  ⚠ match が非網羅的です。例えば None2 が漏れています
  ran
