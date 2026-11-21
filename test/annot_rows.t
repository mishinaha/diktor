注釈に書いたエフェクト行の読み方をテストする(sample.kel §9、LangSpec §13.2)。内側の矢印で省略した @ は @ {} と読む。
最も外側の矢印に書いた閉じた行は、@ {} も含めて、そのまま束縛の型になる。@ を省略した let が推論した閉じた行も同じである。
閉じた行を持つ関数は、呼び出すとき、名前で参照するとき、関数型を要求する位置に置くときに、行の末尾を開く
(LangSpec §13.2 の、使用時に行を開く規則)。閉じた空の行は @ {} と表示され、行変数だけの行は表示されないので、型の表示だけでは区別できない性質は、
型検査に通るかどうかでも固定する。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

内側の矢印(診断では「入れ子の矢印」)で省略した @ は @ {}、つまり純粋と読む。行を伝えるには、行変数を型パラメータに取る(sample.kel §9):

  $ cat > nested1.kel <<'KEL'
  > type Unit = {}
  > effect A = { opa: () => Unit }
  > let call_pure(f: () => Unit): Unit = f()
  > let call_a[E](f: () => Unit @ E): Unit @ E = f()
  > let mk_a(): Unit @ A = perform opa()
  > KEL
  $ diktor --type-check --no-prelude nested1.kel
  call_pure : (() => {} @ {}) => {}
  call_a : (() => {}) => {}
  mk_a : () => {} @ {A}

  $ cat > nested2.kel <<'KEL'
  > type Unit = {}
  > effect A = { opa: () => Unit }
  > let call_pure(f: () => Unit): Unit = f()
  > let bad(): Unit @ A = call_pure(fn() => perform opa())
  > KEL
  $ diktor --type-check --no-prelude nested2.kel
  call_pure : (() => {} @ {}) => {}
  ! nested2.kel:4:41: 型エラー: エフェクト A をここでは実行できません(ラベル A がありません(行は閉じています))(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

レコード型のフィールドとタプル型の要素に書いた矢印も内側の矢印である。省略した @ は @ {} と読むので、
エフェクトを起こすクロージャは渡せない。@ で書いた行は、閉じたまま型に残る:

  $ cat > nestrec.kel <<'KEL'
  > let use(r: {go: () => Unit}): Unit = r.go()
  > let pair(p: (() => Unit, Int32)): Int32 = p._1
  > let mk(): {go: () => Unit @ Console} = {go = fn() => echoln("hi")}
  > let mkt(): (() => Unit @ Console, Int32) = (fn() => echoln("hi"), 1)
  > KEL
  $ diktor --type-check nestrec.kel
  use : ({go: () => {} @ {}}) => {}
  pair : ((() => {} @ {}, Int32)) => Int32
  mk : () => {go: () => {} @ {Console}}
  mkt : () => (() => {} @ {Console}, Int32)

  $ cat > nestrec2.kel <<'KEL'
  > let use(r: {go: () => Unit}): Unit = r.go()
  > let main(): Unit @ Console = use({go = fn() => echoln("x")})
  > KEL
  $ diktor --type-check nestrec2.kel
  use : ({go: () => {} @ {}}) => {}
  ! nestrec2.kel:2:48: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

タプル型の要素でも同じである。上の pair の表示が @ {} であることに加えて、エフェクトを起こす関数を渡すと型エラーになることを固定する:

  $ cat > nestrec3.kel <<'KEL'
  > let pair(p: (() => Unit, Int32)): Int32 = p._1
  > let main(): Int32 @ Console = pair((fn() => echoln("x"), 1))
  > KEL
  $ diktor --type-check nestrec3.kel
  pair : ((() => {} @ {}, Int32)) => Int32
  ! nestrec3.kel:2:45: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

内側の矢印に書いたラベル付きの行も、書いたとおりに読む。受け取った関数の行を自分の行に伝えるには、行変数を明示する。
閉じた行を持つ関数は呼び出すときに行の末尾を開くので、本体の行がそのラベルを含んでいれば呼び出せる:

  $ cat > nested3.kel <<'KEL'
  > type Unit = {}
  > effect A = { opa: () => Unit }
  > let call(f: () => Unit @ A): Unit @ A = f()
  > KEL
  $ diktor --type-check --no-prelude nested3.kel
  call : (() => {} @ {A}) => {} @ {A}

本体の行のほうが広くても同じで、@ {A, B} の本体から、@ A の引数 f と関数 g を呼び出せる:

  $ cat > nested3wide.kel <<'KEL'
  > type Unit = {}
  > effect A = { opa: () => Unit }
  > effect B = { opb: () => Unit }
  > let g(): Unit @ A = perform opa()
  > let call(f: () => Unit @ A): Unit @ {A, B} = { f(); g(); perform opb() }
  > KEL
  $ diktor --type-check --no-prelude nested3wide.kel
  g : () => {} @ {A}
  call : (() => {} @ {A}) => {} @ {A, B}

型エイリアスを展開して現れる矢印も内側の矢印として読む(sample.kel §9、第11章 §11.5 の規則 4):

  $ cat > alias.kel <<'KEL'
  > type Unit = {}
  > effect A = { opa: () => Unit }
  > type Thunk = () => Unit
  > let pure_ok(t: Thunk): Unit = t()
  > let bad(): Thunk = fn() => perform opa()
  > KEL
  $ diktor --type-check --no-prelude alias.kel
  pure_ok : (() => {} @ {}) => {}
  ! alias.kel:5:5: 型エラー: 注釈された返り値型を満たしません(ラベル A がありません(行は閉じています))
  [1]

effect の操作の型の引数に書いた矢印も内側の矢印として読む(LangSpec §13.2):

  $ cat > opsig.kel <<'KEL'
  > type Unit = {}
  > effect Async2 = { yield2: () => Unit }
  > effect Nur  = { spawn:  (() => Unit @ Async2) => Unit }
  > effect NurP = { spawnp: (() => Unit) => Unit }
  > let ok(f: () => Unit @ Async2): Unit @ Nur = perform spawn(f)
  > KEL
  $ diktor --type-check --no-prelude opsig.kel
  ok : (() => {} @ {Async2}) => {} @ {Nur}
  $ cat > opsig2.kel <<'KEL'
  > type Unit = {}
  > effect Async2 = { yield2: () => Unit }
  > effect NurP = { spawnp: (() => Unit) => Unit }
  > let bad(f: () => Unit @ Async2): Unit @ NurP = perform spawnp(f)
  > KEL
  $ diktor --type-check --no-prelude opsig2.kel
  ! opsig2.kel:4:63: 型エラー: ラベル Async2 がありません(行は閉じています)(操作 spawnp の引数の型が求める関数の行は空 = 純粋です。操作の型の矢印は書いたとおりに読み、@ の省略は @ {} と読みます。エフェクトを起こす関数を通すなら、操作の型のその矢印に @ で行を書いてください。§9)
  [1]

操作の型は型パラメータを持たないので、その中の矢印の行は、型エイリアスを展開した後の
操作の型に書いた行で決まる。opsigresume は resume の引数に f を渡す形である。
f の行 Async2 が、操作の返り値の型にある矢印の行(@ を省略したので空である)と一致しないので、
上の opsig2 と同じ案内が診断に付く:

  $ cat > opsigresume.kel <<'KEL'
  > type Unit = {}
  > effect Async2 = { yield2: () => Unit }
  > effect Mk = { mk: () => (() => Unit) }
  > let g(f: () => Unit @ Async2): Unit = (perform mk())() handle {
  >   case mk() => resume(f)
  >   case return(x) => x
  > }
  > KEL
  $ diktor --type-check --no-prelude opsigresume.kel
  ! opsigresume.kel:5:23: 型エラー: ラベル Async2 がありません(行は閉じています)(操作の返り値の型が求める関数の行は空 = 純粋です。操作の型の矢印は書いたとおりに読み、@ の省略は @ {} と読みます。エフェクトを起こす関数を通すなら、操作の型のその矢印に @ で行を書いてください。§9)
  [1]

空の行のエイリアス P を使って @ P と書いた操作の型の矢印も、展開すると @ {} なので、
同じ案内が付く:

  $ cat > opsigalias.kel <<'KEL'
  > type P: EffectRow = {}
  > effect Reg = { reg: (() => Unit @ P) => Unit }
  > let use(f: () => Unit @ Console): Unit @ Reg = perform reg(f)
  > KEL
  $ diktor --type-check opsigalias.kel
  ! opsigalias.kel:3:60: 型エラー: ラベル Console がありません(行は閉じています)(操作 reg の引数の型が求める関数の行は空 = 純粋です。操作の型の矢印は書いたとおりに読み、@ の省略は @ {} と読みます。エフェクトを起こす関数を通すなら、操作の型のその矢印に @ で行を書いてください。§9)
  [1]

操作の型の、行が空である矢印の位置に無名関数を直接渡すと、本体はその空の行を有効な
エフェクト行として推論する。そのため本体の perform は、閉じた空の行のもとで操作を起こすものとして
拒否され、この位置の行が空、つまり純粋であることの案内が付く:

  $ cat > opsiglam.kel <<'KEL'
  > type Unit = {}
  > effect Async2 = { yield2: () => Unit }
  > effect NurP = { spawnp: (() => Unit) => Unit }
  > let bad(): Unit @ {NurP, Async2} = perform spawnp(fn() => perform yield2())
  > KEL
  $ diktor --type-check --no-prelude opsiglam.kel
  ! opsiglam.kel:4:59: 型エラー: エフェクト Async2 をここでは実行できません(ラベル Async2 がありません(行は閉じています))(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

引数の型の不一致は行の不一致より先に報告するので、案内は付かない:

  $ cat > opsigargty.kel <<'KEL'
  > type Unit = {}
  > effect Async2 = { yield2: () => Unit }
  > effect NurP = { spawnp: ((Int32) => Unit) => Unit }
  > let bad(f: (String) => Unit @ Async2): Unit @ NurP = perform spawnp(f)
  > KEL
  $ diktor --type-check --no-prelude opsigargty.kel
  ! opsigargty.kel:4:69: 型エラー: 型が一致しません: String と Int32
  [1]

操作の型の矢印の行が空でないときの行の不一致は、@ の省略とは関係がないので、
案内は付かない:

  $ cat > opsigrow.kel <<'KEL'
  > type Unit = {}
  > effect Async2 = { yield2: () => Unit }
  > effect Nur = { spawn: (() => Unit @ Async2) => Unit }
  > effect Other = { o: () => Unit }
  > let bad(f: () => Unit @ Other): Unit @ Nur = perform spawn(f)
  > KEL
  $ diktor --type-check --no-prelude opsigrow.kel
  ! opsigrow.kel:5:60: 型エラー: ラベル Other がありません(行は閉じています)
  [1]

内側の矢印で省略した @ を使って、エフェクトを隠すことはできない。ここでは newtype Cb のフィールドの
矢印を @ {} と読むので、Console を起こす関数を Cb に入れる wrap が型エラーになる:

  $ cat > launder.kel <<'KEL'
  > let pmap[A, B](xs: Array[A], f: (A) => B @ {}): Array[B] = ???
  > newtype Cb = Cb((Int32) => Int32)
  > let wrap(f: (Int32) => Int32 @ Console): Cb = Cb(f)
  > let unwrap(c: Cb): (Int32) => Int32 @ {} = c match { case Cb(f) => f }
  > let go(c: Cb): Int32 = run h {
  >   let a = MutableArray.freeze(MutableArray.new(3, 7))
  >   let b = pmap(a, unwrap(c))
  >   Array.get(b, 0)
  > }
  > echoln(show(go(wrap(fn(x) => { echo("side!"); x + 1 }))))
  > KEL
  $ diktor --type-check launder.kel
  pmap : (Array[A], (A) => B @ {}) => Array[B]
  ! launder.kel:3:47: 型エラー: ラベル Console がありません(行は閉じています)(コンストラクタ Cb のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

行を伝えるには、sample.kel §9 の Callback[E] のように行変数を型パラメータに取る。E のカインドは推論で EffectRow に決まる:

  $ cat > spec9.kel <<'KEL'
  > newtype Callback[E] = Callback(() => Unit @ E)
  > let make[E](f: () => Unit @ E): Callback[E] = Callback(f)
  > let fire[E](c: Callback[E]): Unit @ E = c match { case Callback(f) => f() }
  > fire(make(fn() => echo("fired\n")))
  > KEL
  $ diktor --type-check spec9.kel
  make : (() => {}) => Callback[R1]
  fire : (Callback[R1]) => {}
  _ : {}
  $ diktor spec9.kel
  fired

@ を省略した値束縛の行は本体から推論し、そのまま束縛の型になる(sample.kel §9。下の sumgen と rec2 も同じである)。
@ {} と明示したときも、閉じたまま束縛の型になり、呼び出すときに行の末尾を開く:

  $ cat > val2.kel <<'KEL'
  > let k: (Int32) => Int32 = fn(x) => x
  > let use(): Int32 @ Console = k(1)
  > KEL
  $ diktor --type-check val2.kel
  k : (Int32) => Int32
  use : () => Int32 @ {Console}

  $ cat > val1.kel <<'KEL'
  > let k: (Int32) => Int32 @ {} = fn(x) => x
  > let use(): Int32 @ Console = k(1)
  > KEL
  $ diktor --type-check val1.kel
  k : (Int32) => Int32 @ {}
  use : () => Int32 @ {Console}

@ を省略した sum の行は、本体から推論した行変数のままなので、(Array[Int32]) => Int32 と表示される。
@ {} と書いた sum2 は (Array[Int32]) => Int32 @ {} と表示される。sum2 は呼び出すときに行の末尾を
開くので、どちらも Console を含む行の本体から呼び出せる(LangSpec §13.2):

  $ cat > sumgen.kel <<'KEL'
  > let sum(xs: Array[Int32]): Int32 = run h {
  >   let acc = Ref.new(0)
  >   Array.each(xs, fn(x) => Ref.set(acc, Ref.get(acc) + x))
  >   Ref.get(acc)
  > }
  > let effectful(xs: Array[Int32]): Int32 @ {Console} = { echoln("go"); sum(xs) }
  > let pure_ok(xs: Array[Int32]): Int32 @ {} = sum(xs)
  > KEL
  $ diktor --type-check sumgen.kel
  sum : (Array[Int32]) => Int32
  effectful : (Array[Int32]) => Int32 @ {Console}
  pure_ok : (Array[Int32]) => Int32 @ {}

  $ cat > sumclosed.kel <<'KEL'
  > let sum2(xs: Array[Int32]): Int32 @ {} = 1
  > let effectful(xs: Array[Int32]): Int32 @ {Console} = { echoln("go"); sum2(xs) }
  > KEL
  $ diktor --type-check sumclosed.kel
  sum2 : (Array[Int32]) => Int32 @ {}
  effectful : (Array[Int32]) => Int32 @ {Console}

型注釈の先頭が型エイリアスである値束縛では、展開して現れる矢印を内側の矢印として読む。そのため、
@ を省略すれば @ {} になり、@ {} と書いた場合も閉じたまま束縛の型になる。閉じた行は呼び出すときに行の末尾を
開くので、エフェクトのある文脈からも呼び出せる。前方参照のためのシグネチャ(第11章 §11.37)も同じ閉じた行を
作るので、宣言の順序を入れ替えても結果は同じである:

  $ cat > alval.kel <<'KEL'
  > type F = (Int32) => Int32
  > let k: F = fn(x) => x
  > let user(): Int32 @ Console = k(1)
  > KEL
  $ diktor --type-check alval.kel
  k : (Int32) => Int32 @ {}
  user : () => Int32 @ {Console}
  $ cat > alval2.kel <<'KEL'
  > type F = (Int32) => Int32
  > let user(): Int32 @ Console = k(1)
  > let k: F = fn(x) => x
  > KEL
  $ diktor --type-check alval2.kel
  user : () => Int32 @ {Console}
  k : (Int32) => Int32 @ {}
  $ cat > alval3.kel <<'KEL'
  > type F = (Int32) => Int32
  > let k: F = fn(x) => x
  > let pure_use(): Int32 @ {} = k(1)
  > KEL
  $ diktor --type-check alval3.kel
  k : (Int32) => Int32 @ {}
  pure_use : () => Int32 @ {}
  $ cat > alval4.kel <<'KEL'
  > type G = (Int32) => Int32 @ {}
  > let k: G = fn(x) => x
  > let user(): Int32 @ Console = k(1)
  > KEL
  $ diktor --type-check alval4.kel
  k : (Int32) => Int32 @ {}
  user : () => Int32 @ {Console}

型クラスのメソッドの型注釈も、同じ規則で読む。先頭が型エイリアスなら、展開して現れる矢印は
内側の矢印なので、書いた行は閉じたまま残る。閉じた行は呼び出すときに行の末尾を開くので、
エイリアスで書いたメソッドも、その行のラベルを含む文脈から呼び出せる。下の 2 つの入力は、
メソッドの型をエイリアス F[T] で書くか矢印で直接書くかだけが違う。
インスタンスの本体と use の定義は同じで、結果も同じになる:

  $ cat > clsalias3.kel <<'KEL'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > effect Log = { log: (String) => Unit }
  > newtype Box = Box(Int32)
  > type F[A] = (A) => Int32 @ Print
  > type class Sz[T] { val size: F[T] }
  > type instance Sz[Box] { let size(b) = b match { case Box(x) => { perform print("e"); x } } }
  > let use(b: Box): Int32 @ {Print, Log} = { perform log("l"); size(b) }
  > KEL
  $ diktor --type-check --no-prelude clsalias3.kel
  use : (Box) => Int32 @ {Print, Log}

メソッドの型を矢印で直接書いても、同じ use が型検査に通る:

  $ cat > clslit.kel <<'KEL'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > effect Log = { log: (String) => Unit }
  > newtype Box = Box(Int32)
  > type class Sz[T] { val size: (T) => Int32 @ Print }
  > type instance Sz[Box] { let size(b) = b match { case Box(x) => { perform print("e"); x } } }
  > let use(b: Box): Int32 @ {Print, Log} = { perform log("l"); size(b) }
  > KEL
  $ diktor --type-check --no-prelude clslit.kel
  use : (Box) => Int32 @ {Print, Log}

エイリアスで書いたメソッドを、@ を省略した関数から呼び出すと、その関数の行は本体から推論される
(推論した行は {Print extends R1} と表示される):

  $ cat > clsalias3ok.kel <<'KEL'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Box = Box(Int32)
  > type F[A] = (A) => Int32 @ Print
  > type class Sz[T] { val size: F[T] }
  > type instance Sz[Box] { let size(b) = b match { case Box(x) => { perform print("e"); x } } }
  > let use(b: Box): Int32 = size(b)
  > KEL
  $ diktor --type-check --no-prelude clsalias3ok.kel
  use : (Box) => Int32 @ {Print extends R1}

let rec も同じで、@ を省略した束縛では、推論した行がそのまま束縛の型になる:

  $ cat > rec2.kel <<'KEL'
  > let rec loop(f: (Int32) => Int32, n: Int32): Int32 = n match { case 0 => 0 case m => loop(f, m - 1) + f(m) }
  > let r(): Int32 @ Console = loop(fn(x) => x, 3)
  > KEL
  $ diktor --type-check rec2.kel
  loop : ((Int32) => Int32 @ {}, Int32) => Int32
  r : () => Int32 @ {Console}

値束縛の型注釈の先頭に書いた矢印も、束縛の最も外側の矢印として読む(sample.kel §9)。ラベル付きの行を書くと、
その行は本体が起こせるエフェクトの上限になり、閉じたまま束縛の型になる。呼び出すときに行の末尾を開くので、
関数束縛と同じく、そのラベルを含む文脈から呼び出せる:

  $ cat > valopen.kel <<'KEL'
  > let k: (Int32) => Int32 @ Console = fn(x) => { echoln("v"); x }
  > let use(): Int32 @ {Console, Print} = { println("p"); k(1) }
  > with_stdout(fn() => use())
  > KEL
  $ diktor --type-check valopen.kel
  k : (Int32) => Int32 @ {Console}
  use : () => Int32 @ {Console, Print}
  _ : Int32
  $ diktor valopen.kel
  p
  v

行の末尾を開いても行のラベルが消えるわけではないので、@ {} の文脈からは呼び出せない:

  $ cat > valopen2.kel <<'KEL'
  > let k: (Int32) => Int32 @ Console = fn(x) => { echo("v"); x }
  > let pure_use(): Int32 @ {} = k(1)
  > KEL
  $ diktor --type-check valopen2.kel
  k : (Int32) => Int32 @ {Console}
  ! valopen2.kel:2:30: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

前方参照のためのシグネチャも、型注釈の先頭の矢印を最も外側の矢印として読む。そのため、呼び出し元の束縛を先に書いても
型検査に通り、k の型は上の valopen と同じになる:

  $ cat > valfwd.kel <<'KEL'
  > let user(): Int32 @ {Console, Print} = { println("p"); k(1) }
  > let k: (Int32) => Int32 @ Console = fn(x) => { echoln("v"); x }
  > KEL
  $ diktor --type-check valfwd.kel
  user : () => Int32 @ {Console, Print}
  k : (Int32) => Int32 @ {Console}

本体の行が閉じた行に決まっていても、型注釈の先頭の矢印に書いた閉じた行と一致すれば、型検査に通る。
下の valclosed と valclosedfn は、値束縛で書くか関数束縛で書くかだけが違う。valclosedok のように型注釈を
エイリアスで書いても、書いた閉じた行がそのまま束縛の型になり、矢印を直接書いたときと同じ表示になる:

  $ cat > valclosed.kel <<'KEL'
  > type F = (Int32) => Int32 @ Console
  > let g: F = fn(x) => { echo("v"); x }
  > let k: (Int32) => Int32 @ Console = g
  > KEL
  $ diktor --type-check valclosed.kel
  g : (Int32) => Int32 @ {Console}
  k : (Int32) => Int32 @ {Console}
  $ cat > valclosedfn.kel <<'KEL'
  > type F = (Int32) => Int32 @ Console
  > let g: F = fn(x) => { echo("v"); x }
  > let kf(x: Int32): Int32 @ Console = g(x)
  > KEL
  $ diktor --type-check valclosedfn.kel
  g : (Int32) => Int32 @ {Console}
  kf : (Int32) => Int32 @ {Console}
  $ cat > valclosedok.kel <<'KEL'
  > type F = (Int32) => Int32 @ Console
  > let g: F = fn(x) => { echo("v"); x }
  > let k: F = g
  > KEL
  $ diktor --type-check valclosedok.kel
  g : (Int32) => Int32 @ {Console}
  k : (Int32) => Int32 @ {Console}

pub の値束縛も最も外側の @ を省略でき、省略した @ は @ {} と読む。閉じた行は呼び出すときに行の末尾を開くので、
Console の文脈から呼び出せる:

  $ cat > pubval.kel <<'KEL'
  > module M {
  >   pub let k: (Int32) => Int32 = fn(x) => x
  > }
  > let use(): Int32 @ Console = { echo("p"); M.k(1) }
  > KEL
  $ diktor --type-check pubval.kel
  M.k : (Int32) => Int32 @ {}
  use : () => Int32 @ {Console}

前方参照のためのシグネチャは pub の値束縛にも作るので、この形も宣言の順序に依存しない。module M の
宣言より前で M.k を呼び出しても型検査に通り、束縛の型は上の pubval と同じになる:

  $ cat > pubvalfwd.kel <<'KEL'
  > let use(): Int32 @ Console = { echo("p"); M.k(1) }
  > module M {
  >   pub let k: (Int32) => Int32 = fn(x) => x
  > }
  > KEL
  $ diktor --type-check pubvalfwd.kel
  use : () => Int32 @ {Console}
  M.k : (Int32) => Int32 @ {}

@ を省略したときに純粋でなければならないのは、型注釈の先頭の矢印に対応する本体、つまり fn の本体である。
本体がエフェクトを起こすと、pub の規則を明記した型エラーになる:

  $ cat > pubvalerr.kel <<'KEL'
  > module M {
  >   pub let k: (Int32) => Int32 = fn(x) => { echo("no"); x }
  > }
  > KEL
  $ diktor --type-check pubvalerr.kel
  ! pubvalerr.kel:2:11: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]

初期化式そのものは、束縛の外側の行で評価する。そのため、初期化式が fn の外で起こすエフェクトは、
この検査の対象にならない。下の M.g は純粋な型で公開されるが、宣言を評価するときに
1 度だけ init を出力する:

  $ cat > pubvalinit.kel <<'KEL'
  > module M {
  >   pub let g: () => Int32 = { echoln("init"); fn() => 1 }
  > }
  > let use(): Int32 @ Console = M.g()
  > with_stdout(fn() => use())
  > KEL
  $ diktor --type-check pubvalinit.kel
  M.g : () => Int32 @ {}
  use : () => Int32 @ {Console}
  _ : Int32
  $ diktor pubvalinit.kel
  init

省略できるのは型注釈の先頭の矢印の @ だけで、その内側の矢印には pub の規則のとおり @ が必要である:

  $ cat > pubvalnest.kel <<'KEL'
  > module M {
  >   pub let k: (Int32) => (Int32) => Int32 = fn(x) => fn(y) => x
  > }
  > KEL
  $ diktor --type-check pubvalnest.kel
  ! pubvalnest.kel:2:11: 型エラー: pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]

let rec の値束縛も、型注釈の先頭の矢印を最も外側の矢印として読む。pub の値束縛で先頭の @ を省略すると、let と同じく
@ {} と読み、本体が純粋なら受理する(第11章 §11.29):

  $ cat > recval.kel <<'KEL'
  > let rec k: (Int32) => Int32 @ Console = fn(n) => n match { case 0 => 0 case m => { echo("."); k(m - 1) } }
  > let use(): Int32 @ {Console, Print} = { println("p"); k(3) }
  > KEL
  $ diktor --type-check recval.kel
  k : (Int32) => Int32 @ {Console}
  use : () => Int32 @ {Console, Print}

  $ cat > pubrecval.kel <<'KEL'
  > module M {
  >   pub let rec k: (Int32) => Int32 = fn(n) => n match { case 0 => 0 case m => k(m - 1) }
  > }
  > KEL
  $ diktor --type-check pubrecval.kel
  M.k : (Int32) => Int32 @ {}

再帰群(let rec … and …)では、型注釈から作ったスコーレム定数のうち、再帰群のほかの束縛の型に現れるものを、
束縛ごとではなく再帰群の終わりに解放する(第11章 §11.29)。そのため、型注釈のある先頭の値束縛が
後ろの束縛を呼び出す形が型検査に通る。
再帰群の 2 つの束縛はどちらも、閉じた行 {Console} が束縛の型になる(f は型注釈の行、g は推論した行である)。
どちらも呼び出すときに行の末尾を開くので、Print を追加した文脈から呼び出せる:

  $ cat > recand.kel <<'KEL'
  > let rec f: (Int32) => Int32 @ Console = fn(x) => g(x)
  > and g: (Int32) => Int32 = fn(x) => { echoln("g"); x }
  > let use(): Int32 @ {Console, Print} = { println("p"); f(1) + g(2) }
  > with_stdout(fn() => use())
  > KEL
  $ diktor --type-check recand.kel
  f : (Int32) => Int32 @ {Console}
  g : (Int32) => Int32 @ {Console}
  use : () => Int32 @ {Console, Print}
  _ : Int32
  $ diktor recand.kel
  p
  g
  g

同じ形を関数束縛で書いても型検査に通る。スコーレム定数の解放を再帰群の終わりまで遅らせる規則は、
関数束縛にも同じように適用される:

  $ cat > recandfn.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = { echoln("a"); b(n) }
  > and b(n: Int32): Int32 = n
  > let use(): Int32 @ {Console, Print} = { println("p"); a(1) + b(2) }
  > KEL
  $ diktor --type-check recandfn.kel
  a : (Int32) => Int32 @ {Console}
  b : (Int32) => Int32 @ {Console}
  use : () => Int32 @ {Console, Print}

解放を遅らせる対象は、行のスコーレム定数だけではない。型パラメータのスコーレム定数が再帰群のほかの束縛の型に
現れる形も、同じ規則で型検査に通る:

  $ cat > recandtp.kel <<'KEL'
  > let rec f[A](x: A): A = g(x)
  > and g(y) = y
  > KEL
  $ diktor --type-check recandtp.kel
  f : (A) => A
  g : (A) => A

再帰群のほかの束縛の型に現れないスコーレム定数は、束縛ごとに解放する(第11章 §11.29)。型注釈のある
前の束縛を、後ろの束縛が多相に使う形がこの場合である。recandpoly の f は A のまま一般化されるので、再帰群の後で
String にも使える。recandeff の b は、a より広い行を型注釈に書ける:

  $ cat > recandpoly.kel <<'KEL'
  > let rec f[A](x: A): A = x
  > and g(n: Int32): Int32 = f(n)
  > let s: String = f("s")
  > KEL
  $ diktor --type-check recandpoly.kel
  f : (A) => A
  g : (Int32) => Int32
  s : String
  $ cat > recandeff.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = { echo("a"); n }
  > and b(n: Int32): Int32 @ {Console, Print} = a(n)
  > KEL
  $ diktor --type-check recandeff.kel
  a : (Int32) => Int32 @ {Console}
  b : (Int32) => Int32 @ {Console, Print}

再帰群の 2 つ以上の束縛が、最も外側の矢印に同じ閉じた行を書いていれば、互いを呼び出せる。値束縛でも
関数束縛でも同じである:

  $ cat > recandboth.kel <<'KEL'
  > let rec f: (Int32) => Int32 @ Console = fn(x) => g(x)
  > and g: (Int32) => Int32 @ Console = fn(x) => f(x)
  > KEL
  $ diktor --type-check recandboth.kel
  f : (Int32) => Int32 @ {Console}
  g : (Int32) => Int32 @ {Console}
  $ cat > recandbothfn.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = b(n)
  > and b(n: Int32): Int32 @ Console = a(n)
  > KEL
  $ diktor --type-check recandbothfn.kel
  a : (Int32) => Int32 @ {Console}
  b : (Int32) => Int32 @ {Console}

前の束縛が後ろの束縛を呼び出すときは、再帰群の中の単相の変数を参照する。後ろの束縛の型注釈の行は、再帰群のどの本体
よりも前に環境に置いてある。閉じた行は呼び出すときに行の末尾を開くので、行が違っていても、そのラベルが
呼び出し元の行に含まれていれば、束縛を書いた順序によらず型検査に通る。後ろの束縛が前の束縛を呼び出すときも
同じである(上の recandeff もこの形である):

  $ cat > recandfwd.kel <<'KEL'
  > let rec a: (Int32) => Int32 @ Console = fn(n) => b(n)
  > and b: (Int32) => Int32 @ Console = fn(n) => { echo("b"); n }
  > KEL
  $ diktor --type-check recandfwd.kel
  a : (Int32) => Int32 @ {Console}
  b : (Int32) => Int32 @ {Console}
  $ cat > recandfwdfn.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = b(n)
  > and b(n: Int32): Int32 @ Console = { echo("b"); n }
  > KEL
  $ diktor --type-check recandfwdfn.kel
  a : (Int32) => Int32 @ {Console}
  b : (Int32) => Int32 @ {Console}
  $ cat > recandfwddiff.kel <<'KEL'
  > let rec b(n: Int32): Int32 @ {Console, Print} = a(n)
  > and a(n: Int32): Int32 @ Console = { echo("a "); n }
  > KEL
  $ diktor --type-check recandfwddiff.kel
  b : (Int32) => Int32 @ {Console, Print}
  a : (Int32) => Int32 @ {Console}
  $ cat > recandback.kel <<'KEL'
  > let rec a: (Int32) => Int32 @ Console = fn(n) => { echo("a"); n }
  > and b: (Int32) => Int32 @ Console = fn(n) => a(n)
  > KEL
  $ diktor --type-check recandback.kel
  a : (Int32) => Int32 @ {Console}
  b : (Int32) => Int32 @ {Console}

ここからは、使用時に行を開く規則(LangSpec §13.2)をテストする。閉じた行を持つ関数は、呼び出すとき、名前で参照する
とき、関数型を要求する位置に置くときに、行の末尾を開く。関数型を要求する位置とは、型注釈が関数型である値束縛の初期化式、
返り値の型注釈が関数型である関数束縛の本体、仮引数の型が関数型である実引数である。
そのため、関数の行のラベルが、要求する側の行に含まれていれば型検査に通る。以下のテストは、この規則で型検査に通る形と
通らない形を固定する。

最初は呼び出しである。@ {} の仮引数、newtype のフィールドから取り出した関数、構文上の値で
ない初期化式で束縛した関数、高階関数の引数が返した関数を、より広い行の文脈から呼び出せる:

  $ cat > usecallparam.kel <<'KEL'
  > let twice(f: () => Unit): Unit @ Console = { f(); f(); echoln("x") }
  > twice(fn() => ())
  > KEL
  $ diktor --type-check usecallparam.kel
  twice : (() => {} @ {}) => {} @ {Console}
  _ : {}
  $ cat > usecallfield.kel <<'KEL'
  > newtype Cb = Cb(go: () => Unit @ Print)
  > let use(c: Cb): Unit @ {Print, Console} = c match { case Cb(go = r) => { r(); echoln("done") } }
  > KEL
  $ diktor --type-check usecallfield.kel
  use : (Cb) => {} @ {Print, Console}
  $ cat > usecallnonval.kel <<'KEL'
  > let mk(): (Int32) => Int32 = fn(x) => x + 1
  > let k = mk()
  > let use(): Int32 @ Console = k(1)
  > KEL
  $ diktor --type-check usecallnonval.kel
  mk : () => (Int32) => Int32 @ {}
  k : (Int32) => Int32 @ {}
  use : () => Int32 @ {Console}
  $ cat > usecallnested.kel <<'KEL'
  > let a(): Unit @ {} = ()
  > let app[E](mk: () => () => Unit @ E): Unit @ E = { let g = mk(); g() }
  > let use(): Unit @ Console = app(fn() => a)
  > KEL
  $ diktor --type-check usecallnested.kel
  a : () => {} @ {}
  app : (() => (() => {}) @ {}) => {}
  use : () => {} @ {Console}

行の末尾を開いても、ラベルが消えるわけではない。@ {} の仮引数にエフェクトのある無名関数を
渡す形、@ {} の本体から @ Console のローカル関数を呼び出す形、@ {} の本体から extern "C" の
関数(@ Blocking)を呼び出す形は、型エラーになる:

  $ cat > userejparam.kel <<'KEL'
  > let twice(f: () => Unit): Unit @ Console = { f(); f(); echoln("x") }
  > twice(fn() => echoln("y"))
  > KEL
  $ diktor --type-check userejparam.kel
  twice : (() => {} @ {}) => {} @ {Console}
  ! userejparam.kel:2:15: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > userejcall.kel <<'KEL'
  > let bad(): Unit @ {} = {
  >   let g: () => Unit @ Console = fn() => echoln("x")
  >   g()
  > }
  > KEL
  $ diktor --type-check userejcall.kel
  ! userejcall.kel:3:3: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > userejblock.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > let p(): Float64 @ {} = sqrt(4.0)
  > KEL
  $ diktor --type-check userejblock.kel
  sqrt : (Float64) => Float64 @ {Blocking}
  ! userejblock.kel:2:25: 型エラー: ラベル Blocking がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

閉じた行を持つ関数を名前で渡すと、受け取る側の行に合わせて行の末尾を開く。@ Print の仮引数に
@ {} の関数を渡す形、同じ行変数 E を持つ 2 つの仮引数に行の違う関数を渡す形、返り値の型の
行変数の位置に @ {} の関数を返す形、行変数を持つ高階関数に組み込みのメソッド show を
渡す形、pub で @ を省略した関数(@ {})を渡す形が、型検査に通る:

  $ cat > passpure.kel <<'KEL'
  > let pure_fn(): Unit @ {} = ()
  > let call_p(f: () => Unit @ Print): Unit @ Print = f()
  > let t(): Unit @ Print = call_p(pure_fn)
  > KEL
  $ diktor --type-check passpure.kel
  pure_fn : () => {} @ {}
  call_p : (() => {} @ {Print}) => {} @ {Print}
  t : () => {} @ {Print}
  $ cat > passtwice.kel <<'KEL'
  > let twice2[E](f: () => Unit @ E, g: () => Unit @ E): Unit @ E = { f(); g() }
  > let pure_fn(): Unit @ {} = ()
  > let printer(): Unit @ Console = echoln("p")
  > let t(): Unit @ Console = twice2(pure_fn, printer)
  > KEL
  $ diktor --type-check passtwice.kel
  twice2 : (() => {}, () => {}) => {}
  pure_fn : () => {} @ {}
  printer : () => {} @ {Console}
  t : () => {} @ {Console}
  $ cat > passret.kel <<'KEL'
  > let pure_fn(): Unit @ {} = ()
  > let mk[E](): () => Unit @ E = pure_fn
  > KEL
  $ diktor --type-check passret.kel
  pure_fn : () => {} @ {}
  mk : () => () => {}
  $ cat > passmethod.kel <<'KEL'
  > let rec map_l[A, B, E](xs: List[A], f: (A) => B @ E): List[B] @ E = xs match {
  >   case Nil => Nil
  >   case Cons(x, t) => Cons(f(x), map_l(t, f))
  > }
  > let t(): Unit @ Console = {
  >   let ys = map_l(Cons(1, Nil), show)
  >   echoln("x")
  > }
  > KEL
  $ diktor --type-check passmethod.kel
  map_l : (List[A], (A) => B) => List[B]
  t : () => {} @ {Console}
  $ cat > passpub.kel <<'KEL'
  > pub let inc(x: Int32): Int32 = x + 1
  > let t(xs: Array[Int32]): Unit @ Console = run h {
  >   Array.each(xs, fn(x) => echoln(show(inc(x))))
  > }
  > let rec map_l[A, B, E](xs: List[A], f: (A) => B @ E): List[B] @ E = xs match {
  >   case Nil => Nil
  >   case Cons(x, tl) => Cons(f(x), map_l(tl, f))
  > }
  > let u(): List[Int32] @ Console = map_l(Cons(1, Nil), inc)
  > KEL
  $ diktor --type-check passpub.kel
  inc : (Int32) => Int32 @ {}
  t : (Array[Int32]) => {} @ {Console}
  map_l : (List[A], (A) => B) => List[B]
  u : () => List[Int32] @ {Console}

ユーザが宣言した型クラスのメソッドも、先頭の矢印で省略した @ は @ {} と読む。高階関数に
渡しても、Console の文脈から直接呼び出しても、型検査に通る:

  $ cat > passumeth.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Sz[T] { val sz: (T) => Int32 }
  > type instance Sz[Box] { let sz(b) = b match { case Box(x) => x } }
  > let app[A, B, E](f: (A) => B @ E, x: A): B @ E = f(x)
  > let use(b: Box): Int32 @ Console = { echo("x"); app(sz, b) + sz(b) }
  > KEL
  $ diktor --type-check passumeth.kel
  app : ((A) => B, A) => B
  use : (Box) => Int32 @ {Console}

名前で参照した関数は、関数型を要求しない位置に置いても行の末尾を開く。@ {} の関数を名前で
レコードのフィールド、タプルの要素、match の節(返り値の型注釈がある形とない形)、
コンストラクタの引数、perform と resume の引数に置いても、@ Console の関数と同じ型に
できる:

  $ cat > noheadrecord.kel <<'KEL'
  > let a(): Int32 @ {} = 1
  > let use(): Int32 @ Console = {
  >   let r: {go: () => Int32 @ Console} = {go = a}
  >   r.go()
  > }
  > KEL
  $ diktor --type-check noheadrecord.kel
  a : () => Int32 @ {}
  use : () => Int32 @ {Console}
  $ cat > noheadtuple.kel <<'KEL'
  > let a(): Int32 @ {} = 1
  > let b(): Int32 @ Console = 2
  > let use(): Int32 @ Console = {
  >   let p = (a, b)
  >   let q: (() => Int32 @ Console, Int32) = (a, 1)
  >   0
  > }
  > KEL
  $ diktor --type-check noheadtuple.kel
  a : () => Int32 @ {}
  b : () => Int32 @ {Console}
  use : () => Int32 @ {Console}
  $ cat > noheadmatch.kel <<'KEL'
  > let a(): Int32 @ {} = 1
  > let b(): Int32 @ Console = 2
  > let pick(c: Boolean): () => Int32 @ Console = c match { case true => a case false => b }
  > KEL
  $ diktor --type-check noheadmatch.kel
  a : () => Int32 @ {}
  b : () => Int32 @ {Console}
  pick : (Boolean) => () => Int32 @ {Console}
  $ cat > noheadmatchunann.kel <<'KEL'
  > let a(): Int32 @ {} = 1
  > let b(): Int32 @ Console = 2
  > let pick(c: Boolean) = c match { case true => a case false => b }
  > KEL
  $ diktor --type-check noheadmatchunann.kel
  a : () => Int32 @ {}
  b : () => Int32 @ {Console}
  pick : (Boolean) => () => Int32 @ {Console extends R1}
  $ cat > noheadctor.kel <<'KEL'
  > newtype Cb = Cb(go: () => Unit @ Console)
  > let a(): Unit @ {} = ()
  > let mk(): Cb = Cb(a)
  > KEL
  $ diktor --type-check noheadctor.kel
  a : () => {} @ {}
  mk : () => Cb
  $ cat > noheadperform.kel <<'KEL'
  > effect Reg = { reg: (() => Unit @ Console) => Unit }
  > let a(): Unit @ {} = ()
  > let use(): Unit @ Reg = perform reg(a)
  > KEL
  $ diktor --type-check noheadperform.kel
  a : () => {} @ {}
  use : () => {} @ {Reg}
  $ cat > noheadresume.kel <<'KEL'
  > effect Get = { get: () => () => Unit @ Console }
  > let a(): Unit @ {} = ()
  > let use(): Unit @ Console = {
  >   let g = perform get()
  >   g()
  > } handle {
  >   case get() => resume(a)
  > }
  > KEL
  $ diktor --type-check noheadresume.kel
  a : () => {} @ {}
  use : () => {} @ {Console}

名前の参照でない式も、perform の引数では、操作の型の対応する部分が関数型
なら、閉じた行の末尾を開いてから単一化する。呼び出しの結果 mk() を、1 引数の操作と
2 引数の操作に渡す形は受理する:

  $ cat > nnperform.kel <<'KEL'
  > effect Reg = { reg: (() => Unit @ Console) => Unit }
  > effect Reg2 = { reg2: (() => Unit @ Console, Int32) => Unit }
  > let a(): Unit @ {} = ()
  > let mk(): () => Unit @ {} = a
  > let use(): Unit @ Reg = perform reg(mk())
  > let use2(): Unit @ Reg2 = perform reg2(mk(), 1)
  > KEL
  $ diktor --type-check nnperform.kel
  a : () => {} @ {}
  mk : () => () => {} @ {}
  use : () => {} @ {Reg}
  use2 : () => {} @ {Reg2}

perform の引数に直接書いたタプル式の要素と、フィールドの選択 r.go も、同じように
行の末尾を開く:

  $ cat > nnperformtup.kel <<'KEL'
  > effect Reg = { reg: ((() => Unit @ Console, Int32)) => Unit }
  > effect Reg2 = { reg2: (() => Unit @ Console) => Unit }
  > let a(): Unit @ {} = ()
  > let mk(): () => Unit @ {} = a
  > let use(): Unit @ Reg = perform reg((mk(), 1))
  > let use2(r: {go: () => Unit @ {}}): Unit @ Reg2 = perform reg2(r.go)
  > KEL
  $ diktor --type-check nnperformtup.kel
  a : () => {} @ {}
  mk : () => () => {} @ {}
  use : () => {} @ {Reg}
  use2 : ({go: () => {} @ {}}) => {} @ {Reg2}

resume の引数も、操作の返り値の型が関数型なら行の末尾を開く:

  $ cat > nnresume.kel <<'KEL'
  > effect Get = { get: () => () => Unit @ Console }
  > let a(): Unit @ {} = ()
  > let mk(): () => Unit @ {} = a
  > let use(): Unit @ Console = {
  >   let g = perform get()
  >   g()
  > } handle {
  >   case get() => resume(mk())
  > }
  > KEL
  $ diktor --type-check nnresume.kel
  a : () => {} @ {}
  mk : () => () => {} @ {}
  use : () => {} @ {Console}

perform の引数に直接書いた無名関数の本体は、操作の型の矢印の行を有効なエフェクト行として
推論する。reg の引数の型は () => Unit @ File なので、外側の行に Console が
あっても、本体の修飾しない write は File.write に解決される。内側のハンドラがこの操作を
受け取って x を出力する:

  $ cat > lamperform.kel <<'KEL'
  > effect File = { write: (String) => Unit }
  > effect Reg = { reg: (() => Unit @ File) => Unit }
  > let main(): Unit @ Console = {
  >   perform reg(fn() => perform write("x"))
  > } handle {
  >   case reg(f) => {
  >     { f() } handle { case write(s) => { echoln(s); resume() } }
  >     resume()
  >   }
  > }
  > main()
  > KEL
  $ diktor --type-check lamperform.kel
  main : () => {} @ {Console}
  _ : {}
  $ diktor lamperform.kel
  x

resume の引数に直接書いた無名関数の本体も、操作の返り値の型の矢印の行を有効なエフェクト行
として推論する。use の行には File と Console があるが、本体の write は
File.write に解決される:

  $ cat > lamresume.kel <<'KEL'
  > effect File = { write: (String) => Unit }
  > effect Get = { get: () => () => Unit @ File }
  > let use(): Unit @ {File, Console} = {
  >   let g = perform get()
  >   g()
  > } handle {
  >   case get() => resume(fn() => perform write("x"))
  > }
  > KEL
  $ diktor --type-check lamresume.kel
  use : () => {} @ {File, Console}

無名関数がタプル式の要素や別の無名関数の本体の中にあっても、操作の型の
対応する部分の矢印の行を有効なエフェクト行として推論する:

  $ cat > lamnest.kel <<'KEL'
  > effect File = { write: (String) => Unit }
  > effect Reg = { reg: ((() => Unit @ File, Int32)) => Unit }
  > effect Reg2 = { reg2: (() => () => Unit @ File) => Unit }
  > let use(): Unit @ {Reg, Console} = perform reg((fn() => perform write("x"), 1i32))
  > let use2(): Unit @ {Reg2, Console} = perform reg2(fn() => fn() => perform write("x"))
  > KEL
  $ diktor --type-check lamnest.kel
  use : () => {} @ {Reg, Console}
  use2 : () => {} @ {Reg2, Console}

操作の型の矢印の行に、修飾しない操作名を宣言するエフェクトが 2 つ現れる
ときは、その行の中で曖昧なので拒否する:

  $ cat > lamambig.kel <<'KEL'
  > effect File = { write: (String) => Unit }
  > effect Reg = { reg: (() => Unit @ {File, Console}) => Unit }
  > let use(): Unit @ {Reg} = perform reg(fn() => perform write("x"))
  > KEL
  $ diktor --type-check lamambig.kel
  ! lamambig.kel:3:47: 型エラー: 操作 write は、この位置の行に現れる複数のエフェクト(Console, File)に属します。Console.write、File.write のどれかに修飾してください
  [1]

修飾しない操作名は、無名関数の本体の行、つまり操作の型の矢印の行 {Console, File}
の中で解決する。本体が先に Console を起こしていても、write を宣言する
エフェクトがその行に 2 つあることは変わらないので、拒否する。lamambigq は、perform の
引数の本体が先に perform Console.write を書く形である。lamambigqr は、resume の引数の
本体が先に echoln を呼び出す形である。lamambigqc は、lamambigq と同じ本体を、仮引数の
型が同じ矢印である関数の呼び出しの実引数に書いた形で、関数呼び出しの実引数でも
同じように拒否することを示す:

  $ cat > lamambigq.kel <<'KEL'
  > effect File = { read: () => String, write: (String) => Unit }
  > effect Reg = { reg: (() => Unit @ {Console, File}) => Unit }
  > let use(): Unit @ {Reg} = perform reg(fn() => { perform Console.write("a"); perform write("b") })
  > KEL
  $ diktor --type-check lamambigq.kel
  ! lamambigq.kel:3:77: 型エラー: 操作 write は、この位置の行に現れる複数のエフェクト(Console, File)に属します。Console.write、File.write のどれかに修飾してください
  [1]
  $ cat > lamambigqr.kel <<'KEL'
  > effect File = { read: () => String, write: (String) => Unit }
  > effect G = { get: () => () => Unit @ {Console, File} }
  > let use(): Unit = { let f = perform get(); () } handle { case get() => resume(fn() => { echoln("a"); perform write("b") }) }
  > KEL
  $ diktor --type-check lamambigqr.kel
  ! lamambigqr.kel:3:102: 型エラー: 操作 write は、この位置の行に現れる複数のエフェクト(Console, File)に属します。Console.write、File.write のどれかに修飾してください
  [1]
  $ cat > lamambigqc.kel <<'KEL'
  > effect File = { read: () => String, write: (String) => Unit }
  > let call(g: () => Unit @ {Console, File}): Unit = ()
  > let use(): Unit = call(fn() => { perform Console.write("a"); perform write("b") })
  > KEL
  $ diktor --type-check lamambigqc.kel
  call : (() => {} @ {Console, File}) => {}
  ! lamambigqc.kel:3:62: 型エラー: 操作 write は、この位置の行に現れる複数のエフェクト(Console, File)に属します。Console.write、File.write のどれかに修飾してください
  [1]

操作の型の矢印の行が空なら、無名関数の本体はその空の行を有効なエフェクト行として推論する。
そのため、本体で Console の関数を呼び出すと、関数呼び出しの実引数に書いたときと同じ案内の付いた
型エラーになる:

  $ cat > lampure.kel <<'KEL'
  > effect Reg = { reg: (() => Unit @ {}) => Unit }
  > let use(): Unit @ {Reg, Console} = perform reg(fn() => echoln("x"))
  > KEL
  $ diktor --type-check lampure.kel
  ! lampure.kel:2:56: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

@ {} の関数と @ Console の関数を同じリストに入れて順に呼び出す形は、実行結果まで確かめる:

  $ cat > noheadrun.kel <<'KEL'
  > let a(): Unit @ {} = echoln_never()
  > let echoln_never(): Unit @ {} = ()
  > let b(): Unit @ Console = echoln("b")
  > let rec run_all(fs: List[() => Unit @ Console]): Unit @ Console = fs match {
  >   case Nil => ()
  >   case Cons(f, t) => { f(); run_all(t) }
  > }
  > run_all(Cons(a, Cons(b, Cons(a, Nil))))
  > echoln("done")
  > KEL
  $ diktor --type-check noheadrun.kel
  a : () => {} @ {}
  echoln_never : () => {} @ {}
  b : () => {} @ {Console}
  run_all : (List[() => {} @ {Console}]) => {} @ {Console}
  _ : {}
  _ : {}
  $ diktor noheadrun.kel
  b
  done

条件式の 2 つの節でも同じで、行の違う 2 つの関数を名前で置き、その結果を束縛してから呼び出せる:

  $ cat > noheadif.kel <<'KEL'
  > let pure_f(): Unit @ {} = ()
  > let print_f(): Unit @ Console = echoln("p")
  > let run_it(b: Boolean): Unit @ Console = {
  >   let g = if b then pure_f else print_f
  >   g()
  > }
  > run_it(false)
  > KEL
  $ diktor --type-check noheadif.kel
  pure_f : () => {} @ {}
  print_f : () => {} @ {Console}
  run_it : (Boolean) => {} @ {Console}
  _ : {}
  $ diktor noheadif.kel
  p

型が型変数である仮引数に行の違う 2 つの関数を並べて渡す形、Ref に入れた @ {} の関数を
@ Console の関数で置き換える形、返り値のレコード型のフィールドに @ {} の関数を置く
形も、型検査に通る:

  $ cat > noheadpoly.kel <<'KEL'
  > let a(): Int32 @ {} = 1
  > let b(): Int32 @ Console = 2
  > let pick[A](c: Boolean, x: A, y: A): A = c match { case true => x case false => y }
  > let use(): Int32 @ Console = pick(true, a, b)()
  > KEL
  $ diktor --type-check noheadpoly.kel
  a : () => Int32 @ {}
  b : () => Int32 @ {Console}
  pick : (Boolean, A, A) => A
  use : () => Int32 @ {Console}
  $ cat > noheadref.kel <<'KEL'
  > let a(): Unit @ {} = ()
  > let b(): Unit @ Console = echoln("b")
  > let use(): Unit @ Console = run h {
  >   let r = Ref.new(a)
  >   Ref.set(r, b)
  >   Ref.get(r)()
  > }
  > KEL
  $ diktor --type-check noheadref.kel
  a : () => {} @ {}
  b : () => {} @ {Console}
  use : () => {} @ {Console}
  $ cat > noheadret.kel <<'KEL'
  > let a(): Int32 @ {} = 1
  > let mk(): {go: () => Int32 @ Console} = {go = a}
  > KEL
  $ diktor --type-check noheadret.kel
  a : () => Int32 @ {}
  mk : () => {go: () => Int32 @ {Console}}

ユーザが宣言したクラスのメソッドも、名前で参照すると行の末尾を開くので、エフェクトのある無名関数と同じ
リストに入れられる:

  $ cat > noheadmethod.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Sz[T] { val sz: (T) => Int32 }
  > type instance Sz[Box] { let sz(b) = b match { case Box(x) => x } }
  > let xs = Cons(sz, Cons(fn(b: Box) => { echo("y"); 1 }, Nil))
  > KEL
  $ diktor --type-check noheadmethod.kel
  xs : List[(Box) => Int32 @ {Console extends R1}]

pub で @ を省略した関数は @ {} と読み、宣言より前で参照しても後で参照しても、
同じ閉じた行として扱われる。下の 2 つは宣言の順序だけが違い、どちらも型検査に通る:

  $ cat > pubfwdlist.kel <<'KEL'
  > let use(): Int32 @ Console = {
  >   let xs = Cons(a, Cons(fn() => { echoln("x"); 2 }, Nil))
  >   0
  > }
  > pub let a(): Int32 = 1
  > KEL
  $ diktor --type-check pubfwdlist.kel
  use : () => Int32 @ {Console}
  a : () => Int32 @ {}
  $ cat > pubbacklist.kel <<'KEL'
  > pub let a(): Int32 = 1
  > let use(): Int32 @ Console = {
  >   let xs = Cons(a, Cons(fn() => { echoln("x"); 2 }, Nil))
  >   0
  > }
  > KEL
  $ diktor --type-check pubbacklist.kel
  a : () => Int32 @ {}
  use : () => Int32 @ {Console}

名前の参照でない式(ここでは呼び出しの結果)は、関数型を要求する位置に置いたときに行の末尾を開く。
実引数に直接書いたレコード式のフィールド、返り値の型注釈が関数型である本体、仮引数の
型が関数型である実引数に mkp() を置くと、型検査に通る:

  $ cat > nonnamearg.kel <<'KEL'
  > let mkp(): () => Int32 = fn() => 1
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let take(r: {go: () => Int32 @ Console}): Int32 @ Console = r.go()
  > let use(): Int32 @ Console = take({go = mkp()})
  > KEL
  $ diktor --type-check nonnamearg.kel
  mkp : () => () => Int32 @ {}
  b : () => Int32 @ {Console}
  take : ({go: () => Int32 @ {Console}}) => Int32 @ {Console}
  use : () => Int32 @ {Console}
  $ cat > nonnameret.kel <<'KEL'
  > let mkp(): () => Int32 = fn() => 1
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let f(): () => Int32 @ Console = mkp()
  > let twice(g: () => Int32 @ Console): Int32 @ Console = g() + g()
  > let use(): Int32 @ Console = twice(mkp())
  > KEL
  $ diktor --type-check nonnameret.kel
  mkp : () => () => Int32 @ {}
  b : () => Int32 @ {Console}
  f : () => () => Int32 @ {Console}
  twice : (() => Int32 @ {Console}) => Int32 @ {Console}
  use : () => Int32 @ {Console}

関数型を要求しない位置に置いた、名前の参照でない式は、行の末尾を開かない(LangSpec §13.2 の 1 つ目の
制限)。コンストラクタの引数に mkp() を置くと、@ Console の b と同じ型にできず、
型エラーになる:

  $ cat > nonnamelist.kel <<'KEL'
  > let mkp(): () => Int32 = fn() => 1
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let xs = Cons(mkp(), Cons(b, Nil))
  > KEL
  $ diktor --type-check nonnamelist.kel
  mkp : () => () => Int32 @ {}
  b : () => Int32 @ {Console}
  ! nonnamelist.kel:3:10: 型エラー: ラベル Console がありません(行は閉じています)
  [1]

無名関数で包めば型検査に通る(1 つ目の制限を避ける書き方)。mkp()() は呼び出しなので行の末尾を開き、
包んだ無名関数の行は本体から推論される:

  $ cat > nonnameeta.kel <<'KEL'
  > let mkp(): () => Int32 = fn() => 1
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let xs = Cons(fn() => mkp()(), Cons(b, Nil))
  > KEL
  $ diktor --type-check nonnameeta.kel
  mkp : () => () => Int32 @ {}
  b : () => Int32 @ {Console}
  xs : List[() => Int32 @ {Console extends R1}]

再帰群では、最も外側の矢印に書いた行、pub の関数で省略した行(@ {})、値束縛の型注釈を、
再帰群のどの本体よりも前に環境に置く(LangSpec §6.3)。そのため、前の束縛から、行の違う後ろの
束縛を呼び出せる。pub の再帰群、後ろの束縛が型パラメータを持つ形、両方が持つ形、pub で両方が
持つ形、リージョンの型パラメータを持つ形、値束縛の形を固定する:

  $ cat > recfwdpub.kel <<'KEL'
  > pub let rec f(): Unit @ Print = { println("a"); g() }
  > and g(): Unit = ()
  > KEL
  $ diktor --type-check recfwdpub.kel
  f : () => {} @ {Print}
  g : () => {} @ {}
  $ cat > recfwdtp.kel <<'KEL'
  > let rec f(n: Int32): Int32 @ Print = { println("a"); g(n) }
  > and g[A](n: Int32): Int32 @ {} = n
  > KEL
  $ diktor --type-check recfwdtp.kel
  f : (Int32) => Int32 @ {Print}
  g : (Int32) => Int32 @ {}
  $ cat > recfwdtp2.kel <<'KEL'
  > let rec f[A](x: A, n: Int32): Int32 @ Print = { println("a"); g(n) }
  > and g[B](n: Int32): Int32 @ {} = n
  > KEL
  $ diktor --type-check recfwdtp2.kel
  f : (A, Int32) => Int32 @ {Print}
  g : (Int32) => Int32 @ {}
  $ cat > recfwdpubtp.kel <<'KEL'
  > module M {
  >   pub let rec f[A](x: A, n: Int32): Int32 @ Print = { println("a"); g(n) }
  >   and g[B](n: Int32): Int32 = n
  > }
  > KEL
  $ diktor --type-check recfwdpubtp.kel
  M.f : (A, Int32) => Int32 @ {Print}
  M.g : (Int32) => Int32 @ {}
  $ cat > recfwdheap.kel <<'KEL'
  > let rec f[h](r: Ref[h, Int32], n: Int32): Int32 @ {Heap[h], Print} = { println("a"); g(n) }
  > and g[k](n: Int32): Int32 @ {} = n
  > KEL
  $ diktor --type-check recfwdheap.kel
  f : (Ref[h, Int32], Int32) => Int32 @ {Heap[h], Print}
  g : (Int32) => Int32 @ {}
  $ cat > recfwdval.kel <<'KEL'
  > let rec a: (Int32) => Int32 @ {Console, Print} = fn(n) => b(n)
  > and b: (Int32) => Int32 @ Console = fn(n) => { echo("b"); n }
  > KEL
  $ diktor --type-check recfwdval.kel
  a : (Int32) => Int32 @ {Console, Print}
  b : (Int32) => Int32 @ {Console}

行の末尾を開いて一致するのは、閉じた行のラベルが呼び出し元の行に含まれるときだけである。@ Print と @ {} の
束縛が互いを呼び出す形は、型パラメータの有無によらず、@ {} の束縛の本体で型エラーになる:

  $ cat > recrejmutual.kel <<'KEL'
  > let rec f(n: Int32): Unit @ Print = { println("a"); g(n) }
  > and g(n: Int32): Unit @ {} = f(n)
  > KEL
  $ diktor --type-check recrejmutual.kel
  ! recrejmutual.kel:2:30: 型エラー: ラベル Print がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > recrejmutualtp.kel <<'KEL'
  > let rec f[A](x: A): A @ Print = { println("a"); g(x) }
  > and g[B](y: B): B @ {} = f(y)
  > KEL
  $ diktor --type-check recrejmutualtp.kel
  ! recrejmutualtp.kel:2:26: 型エラー: ラベル Print がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

再帰群の中で前の束縛から後ろの束縛への参照は単相である。そのため、前の束縛が、自分の型パラメータの
型の値を、後ろの束縛の型パラメータの位置に渡す形は型エラーになる。これは多相再帰を認めない規則
(LangSpec §6.3)から導かれる。2 つの束縛を逆の順に書けば、上の recandpoly と同じく型検査に通る(下の
rectpflowrev):

  $ cat > recrejtpflow.kel <<'KEL'
  > let rec f[A](x: A): Unit @ Print = { println("f"); g(x) }
  > and g[A](x: A): Unit @ {} = ()
  > with_stdout(fn() => f(1))
  > KEL
  $ diktor --type-check recrejtpflow.kel
  ! recrejtpflow.kel:2:5: 型エラー: スコープ付きの型が一致しません: ς1 と ς2(再帰群の中で、前にある束縛から後ろにある束縛への参照は単相です。f の型パラメータ A が g の型に入り込んでいます。前にある束縛の本体が後ろの束縛の型パラメータを何かの型に決める形は、型検査に通りません。§6.3)
  [1]
  $ cat > rectpflowrev.kel <<'KEL'
  > let rec g[A](x: A): Unit @ {} = ()
  > and f[A](x: A): Unit @ Print = { println("f"); g(x) }
  > with_stdout(fn() => f(1))
  > KEL
  $ diktor --type-check rectpflowrev.kel
  g : (A) => {} @ {}
  f : (A) => {} @ {Print}
  _ : {}

行変数も型パラメータなので、同じ制限を受ける。前の束縛から後ろの束縛を参照するとき、
後ろの束縛の行変数は具体化されないので、その行変数を何かの行に決める形は型エラーになる。recrowfwd と
recrowclosed は、最も外側の行に行変数を書いた後ろの束縛 b を、行を注釈した前の束縛 a の
本体で呼び出す形である。呼び出しが b の行変数を a の行に決めるので、型エラーになる(a の行は、recrowfwd
では自分の行変数 E を含み、recrowclosed では閉じている)。recrowrev は recrowfwd を
逆の順に書いた形で、型検査に通る。recrowmutual と recrowmutualrev は、最も外側の行に行変数を
書いた 2 つの束縛が本体で互いを呼び出す形を、2 通りの順序で書いたものである。どちらも、前の束縛からの
呼び出しが後ろの束縛の行変数を決めるので、型エラーになる:

  $ cat > recrowfwd.kel <<'KEL'
  > let rec a[E](n: Int32): Int32 @ {Console extends E} = b(n)
  > and b[F](n: Int32): Int32 @ {Console extends F} = { echo("b"); n }
  > KEL
  $ diktor --type-check recrowfwd.kel
  ! recrowfwd.kel:1:55: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
  [1]
  $ cat > recrowclosed.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = b(n)
  > and b[F](n: Int32): Int32 @ {Console extends F} = { echo("b"); n }
  > KEL
  $ diktor --type-check recrowclosed.kel
  ! recrowclosed.kel:1:40: 型エラー: 行 ς1 は注釈で固定された行変数なので、空の行と一致させられません
  [1]
  $ cat > recrowrev.kel <<'KEL'
  > let rec b[F](n: Int32): Int32 @ {Console extends F} = { echo("b"); n }
  > and a[E](n: Int32): Int32 @ {Console extends E} = b(n)
  > KEL
  $ diktor --type-check recrowrev.kel
  b : (Int32) => Int32 @ {Console extends R1}
  a : (Int32) => Int32 @ {Console extends R1}
  $ cat > recrowmutual.kel <<'KEL'
  > let rec b[F](n: Int32): Int32 @ {Console extends F} = n match { case 0 => 0 case m => a(m - 1) }
  > and a[E](n: Int32): Int32 @ {Console extends E} = b(n)
  > KEL
  $ diktor --type-check recrowmutual.kel
  ! recrowmutual.kel:1:87: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
  [1]
  $ cat > recrowmutualrev.kel <<'KEL'
  > let rec a[E](n: Int32): Int32 @ {Console extends E} = b(n)
  > and b[F](n: Int32): Int32 @ {Console extends F} = n match { case 0 => 0 case m => a(m - 1) }
  > KEL
  $ diktor --type-check recrowmutualrev.kel
  ! recrowmutualrev.kel:1:55: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
  [1]

recrowclosedmut は、行変数を取る a を前に、閉じた行の b を後ろに書いて互いを呼び出す形で、
型検査に通る。recrowclosedmutrev は同じ 2 つの束縛を逆の順に書いた形で、b からの呼び出しが a の
行変数を決めるので型エラーになる。recrowone と recrowonerev は、行変数を取る a と、行を注釈
しない b が互いを呼び出す形を、2 通りの順序で書いたもので、どちらも型検査に通る。recrowoneprint は、
recrowone の b の本体が、a の行にない Print を起こす形で、型エラーになる。recrowonews では、
a が本体で b を呼び出すので、a の行変数が b の推論した型に現れ、この行変数は再帰群の終わりまで
一般化されない。b から a を参照してもこの行変数は具体化されない。with_stdout の中の呼び出しが
この行変数に Print を追加しようとするので、型エラーになる。a が b を呼び出さない recrowonewsnocall は型検査に通る:

  $ cat > recrowclosedmut.kel <<'KEL'
  > let rec a[E](n: Int32): Int32 @ {Console extends E} = n match { case 0 => 0 case m => b(m - 1) }
  > and b(n: Int32): Int32 @ Console = { echo("b"); a(n) }
  > KEL
  $ diktor --type-check recrowclosedmut.kel
  a : (Int32) => Int32 @ {Console extends R1}
  b : (Int32) => Int32 @ {Console}
  $ cat > recrowclosedmutrev.kel <<'KEL'
  > let rec b(n: Int32): Int32 @ Console = { echo("b"); a(n) }
  > and a[E](n: Int32): Int32 @ {Console extends E} = n match { case 0 => 0 case m => b(m - 1) }
  > KEL
  $ diktor --type-check recrowclosedmutrev.kel
  ! recrowclosedmutrev.kel:1:53: 型エラー: 行 ς1 は注釈で固定された行変数なので、空の行と一致させられません
  [1]
  $ cat > recrowone.kel <<'KEL'
  > let rec a[E](n: Int32): Int32 @ {Console extends E} = n match { case 0 => 0 case m => b(m - 1) }
  > and b(n: Int32) = { echo("b"); a(n) }
  > let use(): Int32 @ {Console, Print} = { println("p"); a(1) + b(2) }
  > KEL
  $ diktor --type-check recrowone.kel
  a : (Int32) => Int32 @ {Console extends R1}
  b : (Int32) => Int32 @ {Console extends R1}
  use : () => Int32 @ {Console, Print}
  $ cat > recrowonerev.kel <<'KEL'
  > let rec b(n: Int32) = { echo("b"); a(n) }
  > and a[E](n: Int32): Int32 @ {Console extends E} = n match { case 0 => 0 case m => b(m - 1) }
  > let use(): Int32 @ {Console, Print} = { println("p"); a(1) + b(2) }
  > KEL
  $ diktor --type-check recrowonerev.kel
  b : (Int32) => Int32 @ {Console extends R1}
  a : (Int32) => Int32 @ {Console extends R1}
  use : () => Int32 @ {Console, Print}
  $ cat > recrowoneprint.kel <<'KEL'
  > let rec a[E](n: Int32): Int32 @ {Console extends E} = n match { case 0 => 0 case m => b(m - 1) }
  > and b(n: Int32) = { println("b"); a(n) }
  > KEL
  $ diktor --type-check recrowoneprint.kel
  ! recrowoneprint.kel:2:35: 型エラー: 行 ς1 は注釈で固定された行変数なので、ラベル Print を足せません(注釈側に Print を(必要なら引数つきで)書き足してください)
  [1]
  $ cat > recrowonews.kel <<'KEL'
  > let rec a[E](n: Int32): Int32 @ {Console extends E} = n match { case 0 => 0 case m => b(m - 1) }
  > and b(n: Int32) = with_stdout(fn() => a(n))
  > KEL
  $ diktor --type-check recrowonews.kel
  ! recrowonews.kel:2:39: 型エラー: 行 ς1 は注釈で固定された行変数なので、ラベル Print を足せません(注釈側に Print を(必要なら引数つきで)書き足してください)
  [1]
  $ cat > recrowonewsnocall.kel <<'KEL'
  > let rec a[E](n: Int32): Int32 @ {Console extends E} = n
  > and b(n: Int32) = with_stdout(fn() => a(n))
  > KEL
  $ diktor --type-check recrowonewsnocall.kel
  a : (Int32) => Int32 @ {Console extends R1}
  b : (Int32) => Int32 @ {Console extends R1}

recrowargpure、recrowargeff、recrowargext、recrowargown では、後ろの束縛 b が、行変数 F を
引数の関数型の行に書く。recrowargpure は、エフェクトを起こさない無名関数を渡すので F を
決めず、型検査に通る。recrowargeff は、Console を起こす無名関数を渡して F に Console を求めるので、
型エラーになる。recrowargext は引数の行を {Console extends F} にした形で、Console を起こす
無名関数を渡しても F を決めないので型検査に通る。recrowargown は、a が自分の行変数 E を持つ
関数を渡して F を E に決めるので、型エラーになる。recrowlam は、最も外側の行に F を書いた b を、型を注釈しない
無名関数の中で呼び出し、その無名関数を呼び出さない形で、F を決めないので型検査に通る。その無名関数を
呼び出す recrowlamcall と、行を Console と注釈した引数に渡す recrowlamkeep は、F を a の
行や引数の行に決めるので型エラーになる。行を {Console extends R} と注釈した引数に渡す
recrowlamkeepopen は型検査に通る:

  $ cat > recrowargpure.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = b(fn() => n)
  > and b[F](f: () => Int32 @ F): Int32 @ Console = { echo("b"); 0 }
  > KEL
  $ diktor --type-check recrowargpure.kel
  a : (Int32) => Int32 @ {Console}
  b : (() => Int32) => Int32 @ {Console}
  $ cat > recrowargeff.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = b(fn() => { echo("x"); n })
  > and b[F](f: () => Int32 @ F): Int32 @ Console = { echo("b"); 0 }
  > KEL
  $ diktor --type-check recrowargeff.kel
  ! recrowargeff.kel:2:5: 型エラー: 行 ς1 は注釈で固定された行変数なので、ラベル Console を足せません(注釈側に Console を(必要なら引数つきで)書き足してください)
  [1]
  $ cat > recrowargext.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = b(fn() => { echo("x"); n })
  > and b[F](f: () => Int32 @ {Console extends F}): Int32 @ Console = { echo("b"); 0 }
  > KEL
  $ diktor --type-check recrowargext.kel
  a : (Int32) => Int32 @ {Console}
  b : (() => Int32 @ {Console extends R1}) => Int32 @ {Console}
  $ cat > recrowargown.kel <<'KEL'
  > let rec a[E](f: () => Int32 @ E): Int32 @ E = b(f)
  > and b[F](g: () => Int32 @ F): Int32 = 0
  > KEL
  $ diktor --type-check recrowargown.kel
  ! recrowargown.kel:2:5: 型エラー: スコープ付きの型が一致しません: ς1 と ς2(再帰群の中で、前にある束縛から後ろにある束縛への参照は単相です。a の型パラメータ E が b の型に入り込んでいます。前にある束縛の本体が後ろの束縛の型パラメータを何かの型に決める形は、型検査に通りません。§6.3)
  [1]
  $ cat > recrowlam.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = { let g = fn() => b(n); n }
  > and b[F](n: Int32): Int32 @ {Console extends F} = { echo("b"); n }
  > KEL
  $ diktor --type-check recrowlam.kel
  a : (Int32) => Int32 @ {Console}
  b : (Int32) => Int32 @ {Console extends R1}
  $ cat > recrowlamcall.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = { let g = fn() => b(n); g() }
  > and b[F](n: Int32): Int32 @ {Console extends F} = { echo("b"); n }
  > KEL
  $ diktor --type-check recrowlamcall.kel
  ! recrowlamcall.kel:1:64: 型エラー: 行 ς1 は注釈で固定された行変数なので、空の行と一致させられません
  [1]
  $ cat > recrowlamkeep.kel <<'KEL'
  > let keep(f: () => Int32 @ Console): Int32 = 0
  > let rec a(n: Int32): Int32 @ Console = keep(fn() => b(n))
  > and b[F](n: Int32): Int32 @ {Console extends F} = { echo("b"); n }
  > KEL
  $ diktor --type-check recrowlamkeep.kel
  keep : (() => Int32 @ {Console}) => Int32
  ! recrowlamkeep.kel:2:53: 型エラー: 行 ς1 は注釈で固定された行変数なので、空の行と一致させられません
  [1]
  $ cat > recrowlamkeepopen.kel <<'KEL'
  > let keep[R](f: () => Int32 @ {Console extends R}): Int32 = 0
  > let rec a(n: Int32): Int32 @ Console = keep(fn() => b(n))
  > and b[F](n: Int32): Int32 @ {Console extends F} = { echo("b"); n }
  > KEL
  $ diktor --type-check recrowlamkeepopen.kel
  keep : (() => Int32 @ {Console extends R1}) => Int32
  a : (Int32) => Int32 @ {Console}
  b : (Int32) => Int32 @ {Console extends R1}

pub let rec の値束縛で、型注釈の先頭の @ を省略すると @ {} と読む(上の pubrecval)。本体が
エフェクトを起こすと、let の値束縛と同じく、pub の規則を明記した型エラーになる:

  $ cat > pubrecvalimpure.kel <<'KEL'
  > module M {
  >   pub let rec k: (Int32) => Int32 = fn(n) => { echo("x"); n }
  > }
  > KEL
  $ diktor --type-check pubrecvalimpure.kel
  ! pubrecvalimpure.kel:2:15: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]

値束縛 k は、初期化式が構文上の値でなく、型注釈の最も外側の @ を省略している。組み込みの Show のインスタンスで、
この k をメソッドの本体から呼び出す形と、同じ形の値束縛でメソッド show そのものを書く形も、型検査に通る。
k の行は、初期化式の閉じた行 {} に決まる。組み込みの Show のメソッドの行も
閉じた {} である:

  $ cat > instmonorow.kel <<'KEL'
  > newtype N = N(Int32)
  > let mk(d: Int32): (N) => String @ {} = fn(x) => "n"
  > let k: (N) => String = mk(0)
  > type instance Show[N] { let show(x: N): String = k(x) }
  > echoln(show(N(1)))
  > KEL
  $ diktor --type-check instmonorow.kel
  mk : (Int32) => (N) => String @ {}
  k : (N) => String @ {}
  _ : {}
  $ cat > instmonorowval.kel <<'KEL'
  > newtype N = N(Int32)
  > let mk(d: Int32): (N) => String @ {} = fn(x) => "n"
  > type instance Show[N] { let show: (N) => String = mk(0) }
  > echoln(show(N(1)))
  > KEL
  $ diktor --type-check instmonorowval.kel
  mk : (Int32) => (N) => String @ {}
  _ : {}

使用時に行を開く規則で開いた行の末尾が、一般化しない束縛の型の最も外側の行として、束縛の終わりまで
どの行とも一致しないまま残ったときは、閉じた行に戻す。型注釈の最も外側の @ を省略した、初期化式が構文上の値でない
値束縛 k も、型注釈のない k も、初期化式の閉じた行 {} が束縛の型になり、行の違う 2 つの
文脈から呼び出せる:

  $ cat > recloseann.kel <<'KEL'
  > newtype N = N(Int32)
  > let mk(d: Int32): (N) => String @ {} = fn(x) => "n"
  > let k: (N) => String = mk(0)
  > let a(): String @ Console = k(N(1))
  > let b(): String @ Print = k(N(1))
  > KEL
  $ diktor --type-check recloseann.kel
  mk : (Int32) => (N) => String @ {}
  k : (N) => String @ {}
  a : () => String @ {Console}
  b : () => String @ {Print}
  $ cat > recloseplain.kel <<'KEL'
  > newtype N = N(Int32)
  > let mk(d: Int32): (N) => String @ {} = fn(x) => "n"
  > let k = mk(0)
  > let a(): String @ Console = k(N(1))
  > let b(): String @ Print = k(N(1))
  > KEL
  $ diktor --type-check recloseplain.kel
  mk : (Int32) => (N) => String @ {}
  k : (N) => String @ {}
  a : () => String @ {Console}
  b : () => String @ {Print}

そのような k を呼び出す、型注釈のない関数 u の行も、k の閉じた行に決まるので一般化され、u を
2 つの文脈から呼び出せる。パターンで取り出した関数を束縛する形も同じである:

  $ cat > reclosefn.kel <<'KEL'
  > newtype N = N(Int32)
  > let mk(d: Int32): (N) => String @ {} = fn(x) => "n"
  > let k: (N) => String = mk(0)
  > let u(x: N) = k(x)
  > let a(): String @ Console = u(N(1))
  > let b(): String @ Print = u(N(1))
  > echoln(a())
  > KEL
  $ diktor reclosefn.kel
  n
  $ cat > reclosepat.kel <<'KEL'
  > newtype Box = Box(go: (Int32) => Int32)
  > let pk(x: Int32): Int32 @ {} = x
  > let k = Box(pk) match { case Box(f) => f }
  > let u(x: Int32) = k(x)
  > let u1(): Int32 @ Console = u(1)
  > let u2(): Int32 @ Print = u(2)
  > echoln(show(u1()))
  > KEL
  $ diktor reclosepat.kel
  1

インスタンスの実装の最も外側の行が閉じていれば、行の末尾を開いてから宣言の行と一致させる。
宣言の行 {Print, Console} に含まれる Print だけを起こす実装を、閉じた行の注釈で書ける:

  $ cat > instrowsub.kel <<'KEL'
  > let pp(x: Int32): Int32 @ Print = { println("p"); x }
  > type class C[T] { val m: (T) => Int32 @ {Print, Console} }
  > type instance C[Int32] { let m(x: Int32): Int32 @ Print = pp(x) }
  > let u(): Unit @ {Print, Console} = echoln(show(m(1)))
  > with_stdout(fn() => u())
  > KEL
  $ diktor instrowsub.kel
  p
  1

effect の操作の型の**先頭**の矢印に書いた @ は受理するが、型検査の結果には影響しない(LangSpec §13.2)。
操作を perform した文脈の行はハンドラの側で決まるので、ここに書いた行を使う箇所がない。
下の op は先頭の矢印に @ Print と書いているが、f の行に Print は現れない。
行そのものは精緻化するので、未知のラベルを書くと宣言の位置で型エラーになる。
Diktor はこの位置の @ を宣言の時点で拒否しないので、
ophead.kel は型検査に通る:

  $ cat > ophead.kel <<'KEL'
  > effect Weird = { op: (String) => Unit @ Print }
  > let f(): Unit @ Weird = perform op("a")
  > KEL
  $ diktor --type-check ophead.kel
  f : () => {} @ {Weird}

  $ printf 'effect Weird = { op: (String) => Unit @ Undeclared }\n' > ophead2.kel
  $ diktor --type-check ophead2.kel
  ! ophead2.kel:1:41: 型エラー: 未知のエフェクト: Undeclared
  [1]
