注釈した行の読み方(仕様 §9、M26 / D75〜D78)。入れ子の矢印の省略 @ は @ {}。
最外の矢印に書いた閉じた行は @ {} を含めてそのまま束縛の型になり、@ を省略した let の
推論した閉じた行もそのままである。閉じた行の関数は、呼び出すとき、名前で参照するとき、
関数型を要求する位置に置くときに尾部を開く(使用時の開き。LangSpec §13.2)。閉じた空の
行は @ {} と表示され、行変数だけの行は表示されないので、ゴールデンは「通る / 通らない」でも書く。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

入れ子の省略 @ は @ {}(純粋)。行を通したいなら行変数を型パラメータに取る(§9):

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
  ! nested2.kel:4:41: 型エラー: エフェクト A をここでは実行できません(ラベル A がありません(行は閉じています))
  [1]

レコード型のフィールドとタプル型の要素の矢印も入れ子(裁定 D115)。省略した @ は
@ {} と読むので、そこへエフェクトつきの閉包は渡せない。書いた行は閉じたまま残る:

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

タプル型の要素でも同じ(上の pair の表示の @ {} に加えて、渡して落ちることで固定する):

  $ cat > nestrec3.kel <<'KEL'
  > let pair(p: (() => Unit, Int32)): Int32 = p._1
  > let main(): Int32 @ Console = pair((fn() => echoln("x"), 1))
  > KEL
  $ diktor --type-check nestrec3.kel
  pair : ((() => {} @ {}, Int32)) => Int32
  ! nestrec3.kel:2:45: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

入れ子のラベル付き行も書いたとおりに読む(I8 の提案は仕様が却下した。正道は行変数の明示)。
閉じた行の関数は呼ぶときに尾部を開くので、本体の行にそのラベルが含まれていれば呼べる:

  $ cat > nested3.kel <<'KEL'
  > type Unit = {}
  > effect A = { opa: () => Unit }
  > let call(f: () => Unit @ A): Unit @ A = f()
  > KEL
  $ diktor --type-check --no-prelude nested3.kel
  call : (() => {} @ {A}) => {} @ {A}

本体の行がより広くても同じで、@ {A, B} の本体から @ A の引数と関数を呼べる:

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

型エイリアスが展開する矢印も入れ子(§9。§11.5 の規則 4):

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

effect の操作型の引数の矢印も入れ子(D44 の対象外という裁定が、仕様の規則になった):

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
  ! opsig2.kel:4:48: 型エラー: ラベル Async2 がありません(行は閉じています)
  [1]

V14(高階位置の省略 @ によるエフェクト洗浄)が閉じたこと。改訂前は
`side!side!side!8` を印字して通った(実測):

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

正道(§9 の Callback[E]。M23 のカインド推論が前提):

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

@ を省略した値束縛の行は本体から推論し、そのまま束縛の型になる(§9。D76。下の sumgen と
rec2 も同じ)。@ {} と**書いた**ときも閉じたまま束縛の型になり、呼ぶときに尾部を開く:

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

@ を省略した sum の行は本体から推論した行変数のまま (Array[Int32]) => Int32 と表示され、
@ {} と書いた sum2 は (Array[Int32]) => Int32 @ {} と表示される。sum2 は呼ぶときに尾部を
開くので、どちらも Console の下から呼べる(LangSpec §13.2。旧 spec_gaps.t の sumgen と sumclosed):

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

注釈の頭が型エイリアスの値束縛は、展開先の矢印を入れ子として読むので(D75)、省略は
@ {}、書かれた @ {} も閉じたまま束縛の型になる。閉じた行は呼び出すときに尾部を開く
ので、エフェクトのある文脈からも呼べる。パス 1c の署名(§11.37)も同じ閉じた行を作る
ので、宣言順のどちらでも同じ結果になる:

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

型クラスのメソッドの注釈も同じ規律で読む(D121 / P27)。頭が型エイリアスなら
展開先の矢印は入れ子なので、書いた行は閉じたまま残る。閉じた行は呼び出すときに
開くので、エイリアスで書いたメソッドも、その行のラベルを含む文脈から呼べる。下の
2 つの入力はメソッドの型の書き方だけが違い(エイリアス F[T] か矢印リテラルか)、
インスタンスの本体と use の字面は同じで、結果も同じになる:

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

矢印リテラルで書いたメソッドでも、同じ use が通る:

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

エイリアスで書いたメソッドを、@ を省略した呼び出し側から呼ぶと、行は本体から推論される
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

let rec も同じで、@ を省略した束縛の推論した行はそのまま束縛の型になる:

  $ cat > rec2.kel <<'KEL'
  > let rec loop(f: (Int32) => Int32, n: Int32): Int32 = n match { case 0 => 0 case m => loop(f, m - 1) + f(m) }
  > let r(): Int32 @ Console = loop(fn(x) => x, 3)
  > KEL
  $ diktor --type-check rec2.kel
  loop : ((Int32) => Int32 @ {}, Int32) => Int32
  r : () => Int32 @ {Console}

値束縛の注釈の頭の矢印も束縛の最外として読む(§9 / D116)。ラベル付きの行を書いたら
本体に対する上限として効き、閉じたまま束縛の型になる。呼ぶときに尾部を開くので、
関数束縛と同じく、そのラベルを含む文脈から呼べる:

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

尾部を開いても行のラベルが消えるわけではないので、@ {} の文脈からは呼べない:

  $ cat > valopen2.kel <<'KEL'
  > let k: (Int32) => Int32 @ Console = fn(x) => { echo("v"); x }
  > let pure_use(): Int32 @ {} = k(1)
  > KEL
  $ diktor --type-check valopen2.kel
  k : (Int32) => Int32 @ {Console}
  ! valopen2.kel:2:30: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

パス 1c の署名も頭を最外として読むので、呼び出す側を先に書いても通り、k の型は
上の valopen と同じ形になる:

  $ cat > valfwd.kel <<'KEL'
  > let user(): Int32 @ {Console, Print} = { println("p"); k(1) }
  > let k: (Int32) => Int32 @ Console = fn(x) => { echoln("v"); x }
  > KEL
  $ diktor --type-check valfwd.kel
  user : () => Int32 @ {Console, Print}
  k : (Int32) => Int32 @ {Console}

本体の行が閉じたまま固まっていても、頭の注釈の閉じた行と一致すれば通る。
下の 2 つは値束縛と関数束縛の書き分けだけが違う。注釈をエイリアスで書いても
書いた閉じた行がそのまま束縛の型になり、頭の矢印リテラルと同じ表示になる:

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

pub な値束縛も最外の @ を省略でき、@ {} と読む。閉じた行は呼ぶときに尾部を開くので、
Console の文脈から呼べる:

  $ cat > pubval.kel <<'KEL'
  > module M {
  >   pub let k: (Int32) => Int32 = fn(x) => x
  > }
  > let use(): Int32 @ Console = { echo("p"); M.k(1) }
  > KEL
  $ diktor --type-check pubval.kel
  M.k : (Int32) => Int32 @ {}
  use : () => Int32 @ {Console}

パス 1c が pub の値束縛にも署名を作るので、この形も宣言順に依存しない。module M の
宣言より前に M.k を呼んでも通り、束縛の型は上の pubval と同じになる:

  $ cat > pubvalfwd.kel <<'KEL'
  > let use(): Int32 @ Console = { echo("p"); M.k(1) }
  > module M {
  >   pub let k: (Int32) => Int32 = fn(x) => x
  > }
  > KEL
  $ diktor --type-check pubvalfwd.kel
  use : () => Int32 @ {Console}
  M.k : (Int32) => Int32 @ {}

省略したとき純粋を要求されるのは頭の矢印の本体、つまり fn の中身である。破ると
pub の規則を名指しして落ちる:

  $ cat > pubvalerr.kel <<'KEL'
  > module M {
  >   pub let k: (Int32) => Int32 = fn(x) => { echo("no"); x }
  > }
  > KEL
  $ diktor --type-check pubvalerr.kel
  ! pubvalerr.kel:2:11: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]

初期化式そのものは束縛の外側の行で評価されるので、そこに書いたエフェクトは
この検査に掛からない。下の M.g は純粋な型で公開されるが、宣言を読み込むときに
1 度だけ出力する:

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

省略してよいのは注釈の頭の矢印で、注釈の中の矢印には従来どおり @ が要る:

  $ cat > pubvalnest.kel <<'KEL'
  > module M {
  >   pub let k: (Int32) => (Int32) => Int32 = fn(x) => fn(y) => x
  > }
  > KEL
  $ diktor --type-check pubvalnest.kel
  ! pubvalnest.kel:2:11: 型エラー: pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]

let rec の値束縛も頭を最外として読む。pub で頭の @ を省略した値束縛は、let と同じく
@ {} と読み、本体が純粋なら受理する(§11.29):

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

群(let rec … and …)では、注釈が作った剛定数のうち相手の pre に入り込んだものを
束縛ごとではなく群の終わりに解放する(§11.29)。そうするまで、先頭の注釈つき値束縛が
後続を呼ぶ形は [BUG] 単一化中に Generic 変数が現れました(終了コード 3)で落ちていた。
いまは群の 2 本とも閉じた行 {Console}(f は注釈、g は推論)が束縛の型になり、呼ぶときに
尾部を開くので、Print を足した文脈からどちらも呼べる:

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

同じ形を関数束縛で書いたものも通る。こちらは D116 が値束縛をこの経路へ載せる前から
同じ [BUG] で落ちていた:

  $ cat > recandfn.kel <<'KEL'
  > let rec a(n: Int32): Int32 @ Console = { echoln("a"); b(n) }
  > and b(n: Int32): Int32 = n
  > let use(): Int32 @ {Console, Print} = { println("p"); a(1) + b(2) }
  > KEL
  $ diktor --type-check recandfn.kel
  a : (Int32) => Int32 @ {Console}
  b : (Int32) => Int32 @ {Console}
  use : () => Int32 @ {Console, Print}

遅らせる対象は行の剛定数だけではない。型パラメータの剛定数が相手の型へ入り込む形も
同じ [BUG] で落ちていた:

  $ cat > recandtp.kel <<'KEL'
  > let rec f[A](x: A): A = g(x)
  > and g(y) = y
  > KEL
  $ diktor --type-check recandtp.kel
  f : (A) => A
  g : (A) => A

相手へ入り込んでいない剛定数は、従来どおり束縛ごとに解放する(§11.29)。注釈つきの
先行束縛を後続が多相に使う形がその側で、f は A のまま一般化されて後から String でも
使え、b は a より広い行を名乗れる:

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

群の 2 本以上が最外の矢印に同じ閉じた行を書けば、互いを呼び合える(値束縛でも
関数束縛でも同じ):

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

先行が後続を呼ぶときは、群の中の単相の変数を通る。後続の注釈した行は群のどの本体
よりも前に置いてあり、閉じた行は呼び出すときに尾部を開くので、行が違ってもラベルが
呼ぶ側の行に含まれていれば、関数を書いた順序によらず通る。後続が先行を呼ぶときも
同じである(上の recandeff も同じ):

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

使用時の開き(LangSpec §13.2)。閉じた行を持つ関数は、呼び出すとき、名前で参照する
とき、関数型を要求する位置(型注釈が関数型である値束縛の初期化式、返り値の型注釈が
関数型である関数束縛の本体、仮引数の型が関数型である実引数)に置くときに尾部を開くので、
行のラベルが要求する側の行に含まれていれば通る。以下はこの規則で通る形と通らない形を
固定する。

まず呼び出し。@ {} の仮引数、newtype のフィールドから取り出した関数、構文上の値で
ない初期化式で束縛した関数、高階の引数が返した関数を、行の広い文脈から呼べる:

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

尾部を開いてもラベルが消えるわけではない。@ {} の仮引数にエフェクトのある無名関数を
渡す形、@ {} の本体から @ Console の局所関数を呼ぶ形、@ {} の本体から extern "C"
の関数(@ Blocking)を呼ぶ形は落ちる:

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

閉じた行の関数を名前で渡すと、受け取る側の行に合わせて開く。@ Print の仮引数に
@ {} の関数を渡す形、同じ行変数 E を持つ 2 つの仮引数に行の違う関数を渡す形、返り値の
行変数の位置に @ {} の関数を返す形、行変数を持つ高階関数に組み込みのメソッド show を
渡す形、pub で @ を省略した関数(@ {})を渡す形が通る:

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

利用者が宣言した型クラスのメソッドも、頭の @ の省略は @ {} と読む。高階関数に
渡しても、Console の文脈から直接呼んでも通る:

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

名前で参照した関数は、関数型を要求しない位置に置いても開く。@ {} の関数を名前で
レコードのフィールド、タプルの要素、match の節(返り値の注釈がある形とない形)、
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

@ {} の関数と @ Console の関数を同じリストに入れて順に呼ぶ形は、実行まで確かめる:

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

条件式の 2 つの節でも同じで、名前で置いた行の違う 2 つの関数を束縛してから呼べる:

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

型変数の仮引数に行の違う 2 つの関数を並べて渡す形、Ref に入れた @ {} の関数を
@ Console の関数で置き換える形、返り値のレコード型のフィールドに @ {} の関数を置く
形も通る:

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

利用者のクラスのメソッドも名前の参照で開くので、エフェクトのある無名関数と同じ
リストに入れられる:

  $ cat > noheadmethod.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Sz[T] { val sz: (T) => Int32 }
  > type instance Sz[Box] { let sz(b) = b match { case Box(x) => x } }
  > let xs = Cons(sz, Cons(fn(b: Box) => { echo("y"); 1 }, Nil))
  > KEL
  $ diktor --type-check noheadmethod.kel
  xs : List[(Box) => Int32 @ {Console extends R1}]

pub で @ を省略した関数は @ {} と読み、宣言より前から参照しても後から参照しても
同じ閉じた行を見る。下の 2 つは宣言の順序だけが違い、どちらも通る:

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

名前の参照でない式(呼び出しの結果)は、関数型を要求する位置に置いたときに開く。
実引数に直接書いたレコード式のフィールド、返り値の型注釈が関数型である本体、仮引数の
型が関数型である実引数に mkp() を置くと通る:

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

関数型を要求しない位置に置いた名前の参照でない式は開かない(LangSpec §13.2 の制限の
1 つ目)。コンストラクタの引数に mkp() を置くと、@ Console の b と同じ型にできずに
落ちる:

  $ cat > nonnamelist.kel <<'KEL'
  > let mkp(): () => Int32 = fn() => 1
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let xs = Cons(mkp(), Cons(b, Nil))
  > KEL
  $ diktor --type-check nonnamelist.kel
  mkp : () => () => Int32 @ {}
  b : () => Int32 @ {Console}
  ! nonnamelist.kel:3:10: 型エラー: ラベル Console がありません(行は閉じています)(コンストラクタ Cons のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

無名関数で包めば通る(制限の 1 つ目の回避)。mkp()() は呼び出しなので尾部を開き、
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

再帰群では、最外の矢印に書いた行、pub の関数の省略した行(@ {})、値束縛の型注釈を、
群のどの本体よりも前に置く(LangSpec §6.3)。そのため、前の束縛から行の違う後ろの
束縛を呼べる。pub の群、後ろの束縛が型パラメータを持つ形、両方が持つ形、pub で両方が
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
  f : (Ref[A, Int32], Int32) => Int32 @ {Heap[A], Print}
  g : (Int32) => Int32 @ {}
  $ cat > recfwdval.kel <<'KEL'
  > let rec a: (Int32) => Int32 @ {Console, Print} = fn(n) => b(n)
  > and b: (Int32) => Int32 @ Console = fn(n) => { echo("b"); n }
  > KEL
  $ diktor --type-check recfwdval.kel
  a : (Int32) => Int32 @ {Console, Print}
  b : (Int32) => Int32 @ {Console}

開くのは閉じた行のラベルが呼ぶ側の行に含まれるときだけなので、@ Print と @ {} の
束縛が互いを呼ぶ形は、型パラメータの有無によらず @ {} の側で落ちる:

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

群の中で前の束縛から後ろの束縛への参照は単相なので、前の束縛が自分の型パラメータの
型の値を後ろの束縛の型パラメータの位置に渡す形は落ちる(多相再帰を認めないことの帰結。
LangSpec §6.3)。2 つの束縛を逆の順に書けば、上の recandpoly と同じく通る(下の
rectpflowrev):

  $ cat > recrejtpflow.kel <<'KEL'
  > let rec f[A](x: A): Unit @ Print = { println("f"); g(x) }
  > and g[A](x: A): Unit @ {} = ()
  > with_stdout(fn() => f(1))
  > KEL
  $ diktor --type-check recrejtpflow.kel
  ! recrejtpflow.kel:2:5: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
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

pub let rec の値束縛で頭の @ を省略すると @ {} と読む(上の pubrecval)。本体が
エフェクトを起こすと、let の値束縛と同じく pub の規則を名指しして落ちる:

  $ cat > pubrecvalimpure.kel <<'KEL'
  > module M {
  >   pub let rec k: (Int32) => Int32 = fn(n) => { echo("x"); n }
  > }
  > KEL
  $ diktor --type-check pubrecvalimpure.kel
  ! pubrecvalimpure.kel:2:15: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]

組み込みの Show のインスタンスで、構文上の値でない初期化式を持ち注釈の最外の @ を
省略した値束縛 k をメソッドの本体から呼ぶ形と、同じ形の値束縛でメソッド show そのものを
書く形も通る。k の行は初期化式の閉じた {} に決まるので、組み込みのメソッドの行変数と
単一化しても剛定数のスコープの外に漏れない:

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

使用時の開きで足した尾部が、一般化しない束縛の型の最外の行として、束縛の終わりまで
何にも一致しないまま残ったときは、閉じた行に戻る。注釈の最外の @ を省略した値でない
値束縛 k も、注釈の無い k も、初期化式の閉じた行 {} が束縛の型になり、行の違う 2 つの
文脈から呼べる:

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

そのような k を呼ぶ注釈のない関数 u の行も、k の閉じた行に決まるので一般化され、u を
2 つの文脈から呼べる。パターンで取り出した関数を束縛する形も同じである:

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

インスタンスの実装の最外の行が閉じていれば、尾部を開いてから宣言の行と一致させる。
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

effect の操作型の**頭**の矢印に書いた @ は、受理されるが型付けに効かない(D120)。
操作を perform した文脈の行は handle 側が決めるので、ここに書いた行を読む側が
いない — 下の op は頭に @ Print と書いてあるのに、f の行に Print は現れない。
行そのものは精緻化されるので、未知のラベルはその場で落ちる。この位置を書けなく
するか意味を与えるかは D120 が保留し、申し送り P35 として親に送った(diktor は
宣言時の拒否を入れていないので、現状は通る):

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
