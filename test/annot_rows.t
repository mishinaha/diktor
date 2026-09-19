注釈した行の読み方(仕様 §9 の改訂、M26 / D75〜D78)。入れ子の矢印の省略 @ は
@ {}、純粋と判明した let の行は公開で開き直す。型表示では改訂の前後で 1 文字も
変わらないので(空行と裸の行変数はどちらも表示されない)、ゴールデンは必ず
「通る / 通らない」で書く。

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
  call_pure : (() => {}) => {}
  call_a : (() => {}) => {}
  mk_a : () => {} @ {A extends R1}

  $ cat > nested2.kel <<'KEL'
  > type Unit = {}
  > effect A = { opa: () => Unit }
  > let call_pure(f: () => Unit): Unit = f()
  > let bad(): Unit @ A = call_pure(fn() => perform opa())
  > KEL
  $ diktor --type-check --no-prelude nested2.kel
  call_pure : (() => {}) => {}
  ! nested2.kel:4:41: 型エラー: エフェクト A をここでは実行できません(ラベル A がありません(行は閉じています))
  [1]

入れ子のラベル付き行は開かない(I8 の提案は仕様が却下した。正道は行変数の明示):

  $ cat > nested3.kel <<'KEL'
  > type Unit = {}
  > effect A = { opa: () => Unit }
  > let call(f: () => Unit @ A): Unit @ A = f()
  > KEL
  $ diktor --type-check --no-prelude nested3.kel
  ! nested3.kel:3:41: 型エラー: 行 ς1 は注釈で固定された行変数なので、この行と一致させられません(注釈を extends 付きの形にしてください)
  [1]

型エイリアスが展開する矢印も入れ子(§9。§11.5 の規則 4):

  $ cat > alias.kel <<'KEL'
  > type Unit = {}
  > effect A = { opa: () => Unit }
  > type Thunk = () => Unit
  > let pure_ok(t: Thunk): Unit = t()
  > let bad(): Thunk = fn() => perform opa()
  > KEL
  $ diktor --type-check --no-prelude alias.kel
  pure_ok : (() => {}) => {}
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
  ok : (() => {} @ {Async2}) => {} @ {Nur extends R1}
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
  > newtype Cb = Cb((Int32) => Int32)
  > let wrap(f: (Int32) => Int32 @ Console): Cb = Cb(f)
  > let unwrap(c: Cb): (Int32) => Int32 @ {} = c match { case Cb(f) => f }
  > let go(c: Cb): Int32 = run h {
  >   let a = MutableArray.freeze(MutableArray.new(3, 7))
  >   let b = par_map(a, unwrap(c))
  >   Array.get(b, 0)
  > }
  > echoln(show(go(wrap(fn(x) => { echo("side!"); x + 1 }))))
  > KEL
  $ diktor --type-check launder.kel
  ! launder.kel:2:47: 型エラー: ラベル Console がありません(行は閉じています)(コンストラクタ Cb のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
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

@ を省略した let の行が本体で空に固まっても、公開の型は行多相(§9 の
「純粋な本体なら行変数として一般化される」— D76)。@ {} と**書いた**ときは開かない:

  $ cat > val2.kel <<'KEL'
  > let k: (Int32) => Int32 = fn(x) => x
  > let use(): Int32 @ Console = k(1)
  > KEL
  $ diktor --type-check val2.kel
  k : (Int32) => Int32
  use : () => Int32 @ {Console extends R1}

  $ cat > val1.kel <<'KEL'
  > let k: (Int32) => Int32 @ {} = fn(x) => x
  > let use(): Int32 @ Console = k(1)
  > KEL
  $ diktor --type-check val1.kel
  k : (Int32) => Int32
  ! val1.kel:2:30: 型エラー: ラベル Console がありません(行は閉じています)(呼び出し先の行は空 = 純粋です。行の部分型付けが無いので、空でない行の下からは呼べません。入れ子の矢印の @ 省略は @ {} と読みます — 行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

注釈の頭が型エイリアスの値束縛は開き直さない — 展開先の矢印は入れ子(D75)なので
省略は @ {}、書かれた @ {} は両方向。パス 1c の署名(§11.37)も同じ閉じた行を
作るので、宣言順のどちらでも同じ結果になる(M26 の検証で、パス 2 だけが開いて
宣言順で受理 / 拒否が割れる食い違いが見つかった):

  $ cat > alval.kel <<'KEL'
  > type F = (Int32) => Int32
  > let k: F = fn(x) => x
  > let user(): Int32 @ Console = k(1)
  > KEL
  $ diktor --type-check alval.kel
  k : (Int32) => Int32
  ! alval.kel:3:31: 型エラー: ラベル Console がありません(行は閉じています)(呼び出し先の行は空 = 純粋です。行の部分型付けが無いので、空でない行の下からは呼べません。入れ子の矢印の @ 省略は @ {} と読みます — 行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > alval2.kel <<'KEL'
  > type F = (Int32) => Int32
  > let user(): Int32 @ Console = k(1)
  > let k: F = fn(x) => x
  > KEL
  $ diktor --type-check alval2.kel
  ! alval2.kel:2:31: 型エラー: ラベル Console がありません(行は閉じています)(呼び出し先の行は空 = 純粋です。行の部分型付けが無いので、空でない行の下からは呼べません。入れ子の矢印の @ 省略は @ {} と読みます — 行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > alval3.kel <<'KEL'
  > type F = (Int32) => Int32
  > let k: F = fn(x) => x
  > let pure_use(): Int32 @ {} = k(1)
  > KEL
  $ diktor --type-check alval3.kel
  k : (Int32) => Int32
  pure_use : () => Int32
  $ cat > alval4.kel <<'KEL'
  > type G = (Int32) => Int32 @ {}
  > let k: G = fn(x) => x
  > let user(): Int32 @ Console = k(1)
  > KEL
  $ diktor --type-check alval4.kel
  k : (Int32) => Int32
  ! alval4.kel:3:31: 型エラー: ラベル Console がありません(行は閉じています)(呼び出し先の行は空 = 純粋です。行の部分型付けが無いので、空でない行の下からは呼べません。入れ子の矢印の @ 省略は @ {} と読みます — 行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

型クラスのメソッドの注釈も同じ規律で読む(D121 / P27)。頭が型エイリアスなら
展開先の矢印は入れ子なので開かず、書いた行は閉じたまま残る。下の 2 つの入力は
メソッドの型の書き方だけが違い(エイリアス F[T] か矢印リテラルか)、インスタンスの
本体と use の字面は同じである:

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
  ! clsalias3.kel:8:61: 型エラー: ラベル Log がありません(行は閉じています)
  [1]

矢印リテラルで書いたメソッドは最外として開くので、同じ use が通る:

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
  use : (Box) => Int32 @ {Print, Log extends R1}

エイリアスで書いたメソッドにも呼び方はある。呼び出し側が @ を省略すれば行が
推論され、公開される型は閉じた {Print} になる:

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
  use : (Box) => Int32 @ {Print}

let rec も同じ(群のうち @ を書いた束縛と pub は対象外):

  $ cat > rec2.kel <<'KEL'
  > let rec loop(f: (Int32) => Int32, n: Int32): Int32 = n match { case 0 => 0 case m => loop(f, m - 1) + f(m) }
  > let r(): Int32 @ Console = loop(fn(x) => x, 3)
  > KEL
  $ diktor --type-check rec2.kel
  loop : ((Int32) => Int32, Int32) => Int32
  r : () => Int32 @ {Console extends R1}

値束縛の注釈の頭の矢印も束縛の最外として読む(§9 / D116)。ラベル付きの行を書いたら
本体に対する上限として効き、公開される型では行変数で開かれる — 関数束縛と同じ
非対称である:

  $ cat > valopen.kel <<'KEL'
  > let k: (Int32) => Int32 @ Console = fn(x) => { echoln("v"); x }
  > let use(): Int32 @ {Console, Print} = { println("p"); k(1) }
  > with_stdout(fn() => use())
  > KEL
  $ diktor --type-check valopen.kel
  k : (Int32) => Int32 @ {Console extends R1}
  use : () => Int32 @ {Console, Print extends R1}
  _ : Int32
  $ diktor valopen.kel
  p
  v

開いても行が消えるわけではないので、@ {} の文脈からは呼べない:

  $ cat > valopen2.kel <<'KEL'
  > let k: (Int32) => Int32 @ Console = fn(x) => { echo("v"); x }
  > let pure_use(): Int32 @ {} = k(1)
  > KEL
  $ diktor --type-check valopen2.kel
  k : (Int32) => Int32 @ {Console extends R1}
  ! valopen2.kel:2:30: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

パス 1c の署名も頭を最外として読むので、呼び出す側を先に書いても通り、k の型は
上の valopen と同じ形になる:

  $ cat > valfwd.kel <<'KEL'
  > let user(): Int32 @ {Console, Print} = { println("p"); k(1) }
  > let k: (Int32) => Int32 @ Console = fn(x) => { echoln("v"); x }
  > KEL
  $ diktor --type-check valfwd.kel
  user : () => Int32 @ {Console, Print extends R1}
  k : (Int32) => Int32 @ {Console extends R1}

上限は単一化で掛けるので、本体の行が閉じたまま固まっていると頭の注釈と合わない。
下の 2 つは値束縛と関数束縛の書き分けだけが違い、どちらも同じ理由で落ちる(行の
部分型付けを持たない設計の帰結)。注釈をエイリアスで書けば入れ子の読みになって通る:

  $ cat > valclosed.kel <<'KEL'
  > type F = (Int32) => Int32 @ Console
  > let g: F = fn(x) => { echo("v"); x }
  > let k: (Int32) => Int32 @ Console = g
  > KEL
  $ diktor --type-check valclosed.kel
  g : (Int32) => Int32 @ {Console}
  ! valclosed.kel:3:5: 型エラー: 注釈された型を満たしません(行 ς1 は注釈で固定された行変数なので、この行と一致させられません(注釈を extends 付きの形にしてください))
  [1]
  $ cat > valclosedfn.kel <<'KEL'
  > type F = (Int32) => Int32 @ Console
  > let g: F = fn(x) => { echo("v"); x }
  > let kf(x: Int32): Int32 @ Console = g(x)
  > KEL
  $ diktor --type-check valclosedfn.kel
  g : (Int32) => Int32 @ {Console}
  ! valclosedfn.kel:3:37: 型エラー: 行 ς1 は注釈で固定された行変数なので、この行と一致させられません(注釈を extends 付きの形にしてください)
  [1]
  $ cat > valclosedok.kel <<'KEL'
  > type F = (Int32) => Int32 @ Console
  > let g: F = fn(x) => { echo("v"); x }
  > let k: F = g
  > KEL
  $ diktor --type-check valclosedok.kel
  g : (Int32) => Int32 @ {Console}
  k : (Int32) => Int32 @ {Console}

pub な値束縛も最外の @ を省略できる。公開される型は行多相なので、Console の
文脈から呼べる:

  $ cat > pubval.kel <<'KEL'
  > module M {
  >   pub let k: (Int32) => Int32 = fn(x) => x
  > }
  > let use(): Int32 @ Console = { echo("p"); M.k(1) }
  > KEL
  $ diktor --type-check pubval.kel
  M.k : (Int32) => Int32
  use : () => Int32 @ {Console extends R1}

省略した側の本体は純粋でなければならず、破ると pub の規則を名指しして落ちる:

  $ cat > pubvalerr.kel <<'KEL'
  > module M {
  >   pub let k: (Int32) => Int32 = fn(x) => { echo("no"); x }
  > }
  > KEL
  $ diktor --type-check pubvalerr.kel
  ! pubvalerr.kel:2:11: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: 行 ς1 は注釈で固定された行変数なので、ラベル Console を足せません(注釈側に Console を(必要なら引数つきで)書き足してください))
  [1]

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
(群が Rigid の行を 1 本共有する設計。§11.29 / P34)、pub の値束縛は従来どおり
頭にも @ を要求する:

  $ cat > recval.kel <<'KEL'
  > let rec k: (Int32) => Int32 @ Console = fn(n) => n match { case 0 => 0 case m => { echo("."); k(m - 1) } }
  > let use(): Int32 @ {Console, Print} = { println("p"); k(3) }
  > KEL
  $ diktor --type-check recval.kel
  k : (Int32) => Int32 @ {Console extends R1}
  use : () => Int32 @ {Console, Print extends R1}

  $ cat > pubrecval.kel <<'KEL'
  > module M {
  >   pub let rec k: (Int32) => Int32 = fn(n) => n match { case 0 => 0 case m => k(m - 1) }
  > }
  > KEL
  $ diktor --type-check pubrecval.kel
  ! pubrecval.kel:2:15: 型エラー: pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]
