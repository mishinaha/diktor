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

let rec の値束縛も頭を最外として読む。pub の省略 @ の枝だけは入れていないので
(§11.29 / P34)、pub let rec の値束縛は頭にも @ を要求する:

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
  ! pubrecval.kel:2:15: 型エラー: pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]

群(let rec … and …)では、注釈が作った剛定数のうち相手の pre に入り込んだものを
束縛ごとではなく群の終わりに解放する(§11.29)。そうするまで、先頭の注釈つき値束縛が
後続を呼ぶ形は [BUG] 単一化中に Generic 変数が現れました(終了コード 3)で落ちていた。
いまは群の 2 本とも注釈した閉じた行 {Console} が束縛の型になり、呼ぶときに尾部を
開くので、Print を足した文脈からどちらも呼べる:

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
