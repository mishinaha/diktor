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
  4.0
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

末尾 resume 経路でも引数の例外で discontinue が走る(B1 / §14.10。
捨てた継続の cancel と自分の cancel の両方):

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

ガード付き操作節は同じハンドラの次の節へ落ちる(B2 / D28。match と同じ規則):

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

操作節の絞り込みパターンも次の節へ落ちる:

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

総和的な節より後ろの同じ操作の節には到達不能警告(B8):

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

ハンドル番号は 1 から単調増加(C14 の観測点。リセット漏れが入ると
再入 API で番号が実行回数に依存する):

  $ cat > handle.kel <<'EOF2'
  > let h = __open("a.txt")
  > echoln(show(h))
  > let _ = __close(h)
  > let h2 = __open("b.txt")
  > echoln(show(h2))
  > EOF2
  $ diktor handle.kel
  1
  2

操作節のガードで起きた例外も 3 径路の規約に乗る(260829-5 M13 検証修正。
かつては素の raise で cancel が一切走らなかった):

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

ガードの perform で外側が継続を捨てても cancel が走る(Unwind の通過):

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

sink の故障でも discontinue が走る(B6 の観測点。stdout を閉じてバッファを
溢れさせると、cancel 節の例外が抑制ログ = stderr に出る。ログが出た =
例外が fiber へ配送された = discontinue が走った証拠):

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

トップレベルの再束縛は定義時点の実体を守る(V1。かつては評価器が
呼び出し時に globals を引くため、先に定義した関数まで新しい実体を見て
黙って別の値を返した):

  $ cat > shadow.kel <<'EOF2'
  > let f(): String = show(42)
  > let show(x: Int32): String = "SHADOW"
  > echoln(f())
  > echoln(show(1))
  > EOF2
  $ diktor shadow.kel
  42
  SHADOW

前方参照(1c 署名)は途中に再束縛があっても新しい名前として届く:

  $ cat > fwd5.kel <<'EOF2'
  > let f[E](): Int32 @ E = g(1)
  > let show(x: Int32): String = "SHADOW"
  > let g[E](x: Int32): Int32 @ E = x + 1
  > echoln(f() match { case 2 => "two" case _ => "other" })
  > EOF2
  $ diktor fwd5.kel
  two

module 内 extern による組み込み修飾名の上書きも、先に定義済みの関数には
届かない(M14 検証 k3 の再現の解消):

  $ cat > k3.kel <<'EOF2'
  > let f(): Int32 = Add.add(1, 2)
  > module Add { extern "prim" let add(x: String, y: String): String }
  > echoln(show(f()))
  > EOF2
  $ diktor k3.kel
  3
