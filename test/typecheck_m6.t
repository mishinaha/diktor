エフェクト行、perform、handle、run、スコーレム定数の型検査のゴールデンテストである。
期待出力を変えるときは、差分を目で確かめてから dune promote で更新する。

sample.kel §9 の中心となる例(println、capture、try_、with_file、copy)。ファイル操作は、
ここで宣言した effect Fs と、@ Fs を付けた prim で書く(sample.kel は extern "C" と
@ Blocking で書く)。
write は Console と File の両方が宣言しているが、with_file の handle の対象は、
すべての節が属し、すべての操作を節が網羅する File に決まる。
copy の 2 つ目の perform は、行に Console と File の両方が現れるので
File.write と修飾する(下の ambigrow.kel):

  $ cat > eff9.kel <<'EOF'
  > type Unit = {}
  > effect Print   = { print: (String) => Unit }
  > effect Console = { write: (String) => Unit }
  > let println(message: String): Unit @ Print = perform print(message + "\n")
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
  > effect File = {
  >   read:  () => String,
  >   write: (String) => Unit,
  > }
  > effect Fs = {}
  > extern "prim" let __open(path: String): Int32 @ Fs
  > extern "prim" let __read(h: Int32): String @ Fs
  > extern "prim" let __write(h: Int32, s: String): Unit @ Fs
  > extern "prim" let __close(h: Int32): Unit @ Fs
  > let with_file[A, E](path: String, body: () => A @ {File, Fs extends E}): A @ {Fs extends E} = {
  >   let h = __open(path)
  >   body() handle {
  >     case read()    => resume(__read(h))
  >     case write(s)  => resume(__write(h, s))
  >     case return(x) => { __close(h); x }
  >     case cancel    => __close(h)
  >   }
  > }
  > let copy(src: String, dst: String): Unit @ {Console, Fs} = {
  >   with _ = with_file(src)
  >   let text = perform read()
  >   with _ = with_file(dst)
  >   perform File.write(text)
  > }
  > let echo_test[E](): Unit @ {Console extends E} =
  >   println("test") handle {
  >     case print(message) => resume(perform Console.write(message))
  >     case return(x) => x
  >   }
  > let captured = capture(fn() => println("test"))
  > EOF
  $ diktor --type-check --no-prelude eff9.kel
  println : (String) => {} @ {Print}
  capture : (() => A @ {Print extends R1}) => {value: A, output: String}
  try_ : (() => A @ {Fail extends R1}) => #Ok(A) | #Err(String)
  __open : (String) => Int32 @ {Fs}
  __read : (Int32) => String @ {Fs}
  __write : (Int32, String) => {} @ {Fs}
  __close : (Int32) => {} @ {Fs}
  with_file : (String, () => A @ {File, Fs extends R1}) => A @ {Fs extends R1}
  copy : (String, String) => {} @ {Console, Fs}
  echo_test : () => {} @ {Console extends R1}
  captured : {value: {}, output: String}

EffectRow の型エイリアスを行の中に展開する(sample.kel:652):

  $ cat > effrow.kel <<'EOF'
  > type Unit = {}
  > effect ReqId  = { req_id: () => String }
  > effect Logger = { log: (String) => Unit }
  > type Request: EffectRow = {ReqId, Logger}
  > let logged(): Unit @ Request = perform log(perform req_id())
  > EOF
  $ diktor --type-check --no-prelude effrow.kel
  logged : () => {} @ {ReqId, Logger}

操作名が複数のエフェクトに属するときは修飾を求め、修飾した操作名は解決できる:

  $ cat > ambig.kel <<'EOF'
  > type Unit = {}
  > effect A1 = { op1: (String) => Unit }
  > effect A2 = { op1: (String) => Unit }
  > let bad(): Unit = perform op1("x")
  > EOF
  $ diktor --type-check --no-prelude ambig.kel
  ! ambig.kel:4:19: 型エラー: 操作 op1 は複数のエフェクト(A1, A2)に属します。A1.op1 のように修飾してください
  [1]

  $ cat > qual.kel <<'EOF'
  > type Unit = {}
  > effect A1 = { op1: (String) => Unit }
  > effect A2 = { op1: (String) => Unit }
  > let ok(): Unit @ A2 = perform A2.op1("x")
  > EOF
  $ diktor --type-check --no-prelude qual.kel
  ok : () => {} @ {A2}

候補が 1 個なら、行を調べずに解決する(LangSpec §13.3)。行を調べるのは候補が
2 個以上のときだけである。候補が 1 個のときにも行に現れることを求めると、
注釈のない let の perform のすべてに修飾が必要になってしまう:

  $ cat > onecand.kel <<'EOF'
  > type Unit = {}
  > effect A1 = { op1: (String) => Unit }
  > let f() = perform op1("x")
  > EOF
  $ diktor --type-check --no-prelude onecand.kel
  f : () => {} @ {A1 extends R1}

候補が 2 個以上で、行にその候補が 1 つも現れないときも、修飾を求める(2 つ以上現れるときは下の ambigrow.kel):

  $ cat > twocand.kel <<'EOF'
  > type Unit = {}
  > effect A1 = { op1: (String) => Unit }
  > effect A2 = { op1: (String) => Unit }
  > let f() = perform op1("x")
  > EOF
  $ diktor --type-check --no-prelude twocand.kel
  ! twocand.kel:4:11: 型エラー: 操作 op1 は複数のエフェクト(A1, A2)に属します。A1.op1 のように修飾してください
  [1]

handle の節の修飾(LangSpec §13.4、sample.kel:530-531)。操作節の名前は修飾しても
しなくてもよく、両方が混ざっていてもよい。修飾のない case write(s) を対象の
エフェクトの操作として扱ったことは、網羅の検査に通ったことで分かる(File は read と
write の 2 つを宣言している):

  $ cat > qual1.kel <<'EOF'
  > type Unit = {}
  > effect File = { read: () => String, write: (String) => Unit }
  > effect Sink = { write: (String) => Unit, flush: () => Unit }
  > let prog(): String @ File = perform read()
  > let h(): String = prog() handle {
  >   case File.read() => resume("x")
  >   case write(s) => resume(())
  > }
  > EOF
  $ diktor --type-check --no-prelude qual1.kel
  prog : () => String @ {File}
  h : () => String

修飾が後ろの節にあっても同じである。Sink は write と flush を宣言していて、先に
書いた修飾のない write も、その網羅の対象に数える:

  $ cat > qual2.kel <<'EOF'
  > type Unit = {}
  > effect File = { read: () => String, write: (String) => Unit }
  > effect Sink = { write: (String) => Unit, flush: () => Unit }
  > let prog(): Unit @ Sink = { perform write("a"); perform flush() }
  > let h(): Unit = prog() handle {
  >   case write(s) => resume(())
  >   case Sink.flush() => resume(())
  > }
  > EOF
  $ diktor --type-check --no-prelude qual2.kel
  prog : () => {} @ {Sink}
  h : () => {}

節の修飾が 2 つ以上のエフェクトを指していれば、エラーになる:

  $ cat > qual3.kel <<'EOF'
  > type Unit = {}
  > effect File = { read: () => String, write: (String) => Unit }
  > effect Sink = { write: (String) => Unit, flush: () => Unit }
  > let prog(): String @ File = perform read()
  > let h(): String = prog() handle {
  >   case File.read() => resume("x")
  >   case Sink.write(s) => resume(())
  > }
  > EOF
  $ diktor --type-check --no-prelude qual3.kel
  prog : () => String @ {File}
  ! qual3.kel:5:19: 型エラー: handle の節の修飾エフェクトが一致しません
  [1]

修飾のない節の操作が、修飾の指すエフェクトに属さなければエラーになる。File.read の
修飾で対象が File に決まるので、Sink の操作である flush の節は対象に属さない。同じ handle から
File. の修飾だけを外すと対象が決まらなくなり、診断が変わる。この 2 つの入力で、
修飾が対象の決定に使われていることを確かめる:

  $ cat > qual4.kel <<'EOF'
  > type Unit = {}
  > effect File = { read: () => String, write: (String) => Unit }
  > effect Sink = { write: (String) => Unit, flush: () => Unit }
  > let prog(): String @ File = perform read()
  > let h(): String = prog() handle {
  >   case File.read() => resume("x")
  >   case write(s) => resume(())
  >   case flush() => resume(())
  > }
  > EOF
  $ diktor --type-check --no-prelude qual4.kel
  prog : () => String @ {File}
  ! qual4.kel:8:8: 型エラー: 操作 flush はエフェクト File に属しません
  [1]

  $ cat > qual4b.kel <<'EOF'
  > type Unit = {}
  > effect File = { read: () => String, write: (String) => Unit }
  > effect Sink = { write: (String) => Unit, flush: () => Unit }
  > let prog(): String @ File = perform read()
  > let h(): String = prog() handle {
  >   case read() => resume("x")
  >   case write(s) => resume(())
  >   case flush() => resume(())
  > }
  > EOF
  $ diktor --type-check --no-prelude qual4b.kel
  prog : () => String @ {File}
  ! qual4b.kel:5:19: 型エラー: この操作の組を宣言するエフェクトがありません: read, write, flush
  [1]

qual4 から case write(s) を取り除くと、File の write の網羅漏れと、flush が File に
属さないことの両方が成り立つ。対象が決まった後の検査は、節の所属を先に調べるので、
flush の節が File に属さないことを報告する:

  $ cat > qual5.kel <<'EOF'
  > type Unit = {}
  > effect File = { read: () => String, write: (String) => Unit }
  > effect Sink = { write: (String) => Unit, flush: () => Unit }
  > let prog(): String @ File = perform read()
  > let h(): String = prog() handle {
  >   case File.read() => resume("x")
  >   case flush() => resume(())
  > }
  > EOF
  $ diktor --type-check --no-prelude qual5.kel
  prog : () => String @ {File}
  ! qual5.kel:7:8: 型エラー: 操作 flush はエフェクト File に属しません
  [1]

qual5 から flush の節も取り除くと、残るエラーは網羅漏れだけになり、それを
報告する:

  $ cat > qual5w.kel <<'EOF'
  > type Unit = {}
  > effect File = { read: () => String, write: (String) => Unit }
  > effect Sink = { write: (String) => Unit, flush: () => Unit }
  > let prog(): String @ File = perform read()
  > let h(): String = prog() handle {
  >   case File.read() => resume("x")
  > }
  > EOF
  $ diktor --type-check --no-prelude qual5w.kel
  prog : () => String @ {File}
  ! qual5w.kel:5:19: 型エラー: ハンドラが操作を網羅していません: File の write が漏れています
  [1]

修飾できるのは操作節だけで、return 節と cancel 節は修飾できない
(LangSpec §13.4、§13.6、sample.kel:518-519)。
return と cancel を修飾しても対象のエフェクトの決定には使わないので、受理すると、
書いた修飾を黙って捨てることになる:

  $ cat > qualret.kel <<'EOF'
  > type Unit = {}
  > effect File = { read: () => String, write: (String) => Unit }
  > let prog(): String @ File = perform read()
  > let h(): String = prog() handle {
  >   case File.read() => resume("x")
  >   case write(s) => resume(())
  >   case File.return(x) => x
  > }
  > EOF
  $ diktor --type-check --no-prelude qualret.kel
  prog : () => String @ {File}
  ! qualret.kel:7:8: 型エラー: return 節は修飾できません(return は操作名ではなく handle の節の名前です。修飾を外してください)
  [1]

  $ cat > qualcancel.kel <<'EOF'
  > type Unit = {}
  > effect File = { read: () => String, write: (String) => Unit }
  > let prog(): String @ File = perform read()
  > let h(): String = prog() handle {
  >   case File.read() => resume("x")
  >   case write(s) => resume(())
  >   case File.cancel => ()
  > }
  > EOF
  $ diktor --type-check --no-prelude qualcancel.kel
  prog : () => String @ {File}
  ! qualcancel.kel:7:8: 型エラー: cancel 節は修飾できません(cancel は操作名ではなく handle の節の名前です。修飾を外してください)
  [1]

処理されないエフェクト、操作の網羅漏れ、resume の誤用のエラー:

  $ cat > efferr.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > let bad(): Unit @ {} = perform print("x")
  > EOF
  $ diktor --type-check --no-prelude efferr.kel
  ! efferr.kel:3:24: 型エラー: エフェクト Print をここでは実行できません(ラベル Print がありません(行は閉じています))(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を伝えるなら行変数を型パラメータに取ってください。§9)
  [1]

  $ cat > efferr2.kel <<'EOF'
  > type Unit = {}
  > effect File2 = { read2: () => String, write2: (String) => Unit }
  > let bad = fn(body) => body() handle {
  >   case read2() => resume("")
  >   case return(x) => x
  > }
  > EOF
  $ diktor --type-check --no-prelude efferr2.kel
  ! efferr2.kel:3:23: 型エラー: ハンドラが操作を網羅していません: File2 の write2 が漏れています
  [1]

  $ cat > efferr3.kel <<'EOF'
  > let bad = resume(1)
  > EOF
  $ diktor --type-check --no-prelude efferr3.kel
  ! efferr3.kel:1:11: 型エラー: resume は操作節の中でのみ使えます
  [1]

  $ cat > efferr4.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > let bad = fn(body) => body() handle {
  >   case print(m) => fn() => resume(())
  >   case return(x) => x
  > }
  > EOF
  $ diktor --type-check --no-prelude efferr4.kel
  ! efferr4.kel:4:28: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]

run と脱出検査。型検査に通る 3 例と、エラーになる 3 例:

  $ cat > st.kel <<'EOF'
  > let ok1 = run h { let r = Ref.new(0); Ref.set(r, 42); Ref.get(r) }
  > let ok2 = run h { let x = run h2 { Ref.get(Ref.new(1)) }; x + 1 }
  > let poly = fn(u) => Ref.new(0)
  > EOF
  $ diktor --type-check --no-prelude st.kel
  ok1 : Int32
  ok2 : Int32
  poly : (A) => Ref[h, Int32] @ {Heap[h] extends R1}

  $ cat > stbad1.kel <<'EOF'
  > let bad = run h { Ref.new(0) }
  > EOF
  $ diktor --type-check --no-prelude stbad1.kel
  ! stbad1.kel:1:11: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

  $ cat > stbad2.kel <<'EOF'
  > let bad = run h { let r = Ref.new(0); fn(u) => Ref.get(r) }
  > EOF
  $ diktor --type-check --no-prelude stbad2.kel
  ! stbad2.kel:1:11: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

  $ cat > stbad3.kel <<'EOF'
  > let bad = run h { let r = Ref.new(0); run h2 { Ref.get(r) } }
  > EOF
  $ diktor --type-check --no-prelude stbad3.kel
  ! stbad3.kel:1:56: 型エラー: ほかのリージョンの Ref を使おうとしています(スコープ付きの型が一致しません: ς1 と ς2)
  [1]

run の中の値制限。無名関数を入れた Ref の型は一般化しないので、n + 1 を返す関数を入れた後は、Add のインスタンスでない Boolean に適用できない:

  $ cat > stvr.kel <<'EOF'
  > type Unit = {}
  > let bad = run h {
  >   let r = Ref.new(fn(x) => x)
  >   Ref.set(r, fn(n) => n + 1)
  >   Ref.get(r)(true)
  > }
  > EOF
  $ diktor --type-check --no-prelude stvr.kel
  ! stvr.kel:5:14: 型エラー: Boolean は Add のインスタンスではありません
  [1]

スコーレム定数の行変数にラベルを追加しようとしたときの診断は、
その行変数が注釈で固定されていることを示す。高階関数のエフェクトの注釈を
書き間違えると、最初にこの診断が出る:

  $ cat > rigidrow.kel <<'KEL'
  > type Unit = {}
  > effect E1 = { op: (String) => Unit }
  > effect C = { wr: (String) => Unit }
  > let h1[A, E](b: () => A @ {E1 extends E}): A @ {C extends E} =
  >   b() handle {
  >     case op(s) => resume(perform wr(s))
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check --no-prelude rigidrow.kel
  ! rigidrow.kel:5:3: 型エラー: 行 ς1 は注釈で固定された行変数なので、ラベル C を追加できません(注釈側に C を(必要なら引数つきで)書き足してください)
  [1]

修飾のない操作名は、行の中の位置では選ばない。行に候補が 2 つ現れると、
ラベルの順序によらず修飾を求める(LangSpec §13.3):

  $ cat > ambigrow.kel <<'KEL'
  > type Unit = {}
  > effect E1 = { op: (String) => Unit }
  > effect E2 = { op: (String) => Unit }
  > let f(): Unit @ {E1, E2} = perform op("f")
  > KEL
  $ diktor --type-check --no-prelude ambigrow.kel
  ! ambigrow.kel:4:28: 型エラー: 操作 op は、この位置の行に現れる複数のエフェクト(E1, E2)に属します。E1.op、E2.op のどれかに修飾してください
  [1]
  $ cat > ambigrow2.kel <<'KEL'
  > type Unit = {}
  > effect E1 = { op: (String) => Unit }
  > effect E2 = { op: (String) => Unit }
  > let g(): Unit @ {E2, E1} = perform op("g")
  > KEL
  $ diktor --type-check --no-prelude ambigrow2.kel
  ! ambigrow2.kel:4:28: 型エラー: 操作 op は、この位置の行に現れる複数のエフェクト(E1, E2)に属します。E1.op、E2.op のどれかに修飾してください
  [1]

候補の一部だけが行に現れるときは、行に現れる候補だけを宣言の順に示す:

  $ cat > ambigrow3.kel <<'KEL'
  > type Unit = {}
  > effect E1 = { op: (String) => Unit }
  > effect E2 = { op: (String) => Unit }
  > effect E3 = { op: (String) => Unit }
  > let f(): Unit @ {E3, E1} = perform op("f")
  > KEL
  $ diktor --type-check --no-prelude ambigrow3.kel
  ! ambigrow3.kel:5:28: 型エラー: 操作 op は、この位置の行に現れる複数のエフェクト(E1, E3)に属します。E1.op、E3.op のどれかに修飾してください
  [1]

行に現れる候補が 1 つなら、それに解決する。同じエフェクトが 2 回現れても 1 つと数える:

  $ cat > onerow.kel <<'KEL'
  > type Unit = {}
  > effect E1 = { op: (String) => Unit }
  > effect E2 = { op: (String) => Unit }
  > let f(): Unit @ {E1, E1, E2} = perform E2.op("x")
  > let g(): Unit @ {E1, E1} = perform op("g")
  > let h[E](): Unit @ {E2 extends E} = perform op("h")
  > KEL
  $ diktor --type-check --no-prelude onerow.kel
  f : () => {} @ {E1, E1, E2}
  g : () => {} @ {E1, E1}
  h : () => {} @ {E2 extends R1}

@ {} の関数は、エフェクトのある位置から呼べる。エフェクト行に部分型の関係はないが、
最も外側の矢印の @ {} には、使用時に行を開く規則が適用される(LangSpec §13.2):

  $ cat > noSub.kel <<'KEL'
  > effect Logger = { log: (String) => Unit }
  > let pure_f(x: Int32): Int32 @ {} = x + 1
  > let impure(x: Int32): Int32 @ {Logger} = { perform log("hi"); pure_f(x) }
  > KEL
  $ diktor --type-check noSub.kel
  pure_f : (Int32) => Int32 @ {}
  impure : (Int32) => Int32 @ {Logger}

異なるラベルの順序は、型が一致するかどうかの判定に使わない(LangSpec §3.4)。操作名の解決に
使わないことは上の ambigrow.kel が、同じラベルどうしの順序を区別することは下の
doublestack.kel が確かめる。開いた行でも閉じた行でも、順序だけが違う行は単一化できる:

  $ cat > roworder.kel <<'EOF'
  > type Unit = {}
  > effect E1 = { op1: () => Unit }
  > effect E2 = { op2: () => Unit }
  > let a[E](k: () => Unit @ {E1, E2 extends E}): Unit @ {E1, E2 extends E} = k()
  > let b[E](k: () => Unit @ {E2, E1 extends E}): Unit @ {E1, E2 extends E} = a(k)
  > newtype Cb = Cb(() => Unit @ {E1, E2})
  > let mk(k: () => Unit @ {E2, E1}): Cb = Cb(k)
  > EOF
  $ diktor --type-check --no-prelude roworder.kel
  a : (() => {} @ {E1, E2 extends R1}) => {} @ {E1, E2 extends R1}
  b : (() => {} @ {E2, E1 extends R1}) => {} @ {E1, E2 extends R1}
  mk : (() => {} @ {E2, E1}) => Cb

同じエフェクトのハンドラを二重に重ねると、操作は修飾の有無によらず内側のハンドラにだけ届く
(LangSpec §13.4)。sample.kel の copy が src を読んでから dst を開くのは、このためである:

  $ cat > doublestack.kel <<'KEL'
  > effect Tag = { tag: (String) => {} }
  > let with_tag[A, E](name: String, body: () => A @ {Tag, Console extends E}): A @ {Console extends E} =
  >   body() handle {
  >     case tag(s) => resume(echo(name + ":" + s + "\n"))
  >     case return(x) => x
  >   }
  > let go(): {} @ {Console} = {
  >   with _ = with_tag("outer")
  >   with _ = with_tag("inner")
  >   perform tag("hi")
  > }
  > go()
  > KEL
  $ diktor doublestack.kel
  inner:hi

修飾しても同じである(LangSpec §13.4):

  $ sed 's/perform tag/perform Tag.tag/' doublestack.kel > doublestack2.kel
  $ diktor doublestack2.kel
  inner:hi

前方参照できる完全なシグネチャには、注釈の最も外側の矢印に @ があれば足りる(LangSpec §6.4)。
入れ子の矢印で省略した @ は @ {} に決まるので、
g の @ を省略していても、user は helper を前方参照できる:

  $ cat > fwdsig.kel <<'KEL'
  > let user(): Int32 @ Console = helper(fn() => (), fn(n) => n)
  > let helper[E](f: () => Unit @ E, g: (Int32) => Int32): Int32 @ {Console extends E} = ???
  > KEL
  $ diktor --type-check fwdsig.kel
  user : () => Int32 @ {Console}
  helper : (() => {}, (Int32) => Int32 @ {}) => Int32 @ {Console extends R1}
