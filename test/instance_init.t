インスタンスのメソッドを値束縛で書いたときの初期化式(LangSpec §12.2、§6.4)。
処理系は、本体の束縛を新しい行のもとで推論し、シグネチャとの包摂を調べた後で、その行のラベルを「許す行」と比べる。
許す行は、前提のないインスタンスの初期化式ではトップレベルの行で、前提付きインスタンスの初期化式では空の行である。
シグネチャの行と比べるのは、初期化式の値である関数の行である。
初期化式そのものが起こすエフェクトは、その比較に含まれない。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

前提のないインスタンスの初期化式は、トップレベルの行にある Console を起こせる。
init は宣言を実行したときに、その後の echoln("b") より前に 1 回だけ出力される。
show を 2 回使っても、init は繰り返し出力されない:

  $ cat > instinitcon.kel <<'KEL'
  > newtype Foo = Foo
  > type instance Show[Foo] {
  >   let show: (Foo) => String = { echoln("init"); fn(x) => "foo" }
  > }
  > echoln("b")
  > echoln(show(Foo))
  > echoln(show(Foo))
  > KEL
  $ diktor instinitcon.kel
  init
  b
  foo
  foo

idf(...) は構文上の値でない初期化式なので、一般化されない。
idf(...) が返す無名関数の行は、決まっていない行変数のまま包摂の検査を受ける。
包摂の検査は、この行変数を空の行に決めてからシグネチャの行と比べる。
そのため、組み込みの Show のメソッド(instweakrow)も、ユーザのクラスで @ E と書いたメソッド(instweakrowuser)も、受理して実行する:

  $ cat > instweakrow.kel <<'KEL'
  > newtype Foo = Foo
  > let idf[A](x: A): A = x
  > type instance Show[Foo] {
  >   let show: (Foo) => String = idf(fn(x) => "foo")
  > }
  > echoln(show(Foo))
  > KEL
  $ diktor instweakrow.kel
  foo
  $ cat > instweakrowuser.kel <<'KEL'
  > type class Sz[A] { val sz[E]: (A) => Int32 @ E }
  > newtype Foo = Foo
  > let idf[A](x: A): A = x
  > type instance Sz[Foo] {
  >   let sz = idf(fn(x: Foo) => 1i32)
  > }
  > echoln(show(sz(Foo)))
  > KEL
  $ diktor instweakrowuser.kel
  1

初期化式の中のハンドラが処理した Ask は初期化式の行に残らないので、受理する:

  $ cat > instinithandled.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > newtype Foo = Foo
  > type instance Show[Foo] {
  >   let show = { let n = perform ask(); fn(x: Foo) => "foo" } handle { case ask() => resume(1i32) }
  > }
  > echoln(show(Foo))
  > KEL
  $ diktor instinithandled.kel
  foo

memo はエフェクト多相の関数で、初期化式で呼ぶと、その行変数 E を、初期化式の行と、初期化式が返す関数の行が共有する。
memo に渡す fn(x) => 7i32 はエフェクトを起こさないので、この形の instinitpoly は型検査に通り、7 を出力する。
instinitpolylocal は、memo の結果を初期化式の中のローカルの束縛 m に置き、返す関数の本体から m を呼ぶ形である。
この形も受理する:

  $ cat > instinitpoly.kel <<'KEL'
  > type class Sz[A] { val sz: (A) => Int32 }
  > newtype Foo = Foo
  > let memo[E](f: (Foo) => Int32 @ E): (Foo) => Int32 @ E = { let v = f(Foo); fn(x) => v }
  > type instance Sz[Foo] {
  >   let sz = memo(fn(x) => 7i32)
  > }
  > echoln(show(sz(Foo)))
  > KEL
  $ diktor instinitpoly.kel
  7
  $ cat > instinitpolylocal.kel <<'KEL'
  > type class Sz[A] { val sz: (A) => Int32 }
  > newtype Foo = Foo
  > newtype Bar = Bar
  > let memo[E](f: (Foo) => Int32 @ E): (Foo) => Int32 @ E = { let v = f(Foo); fn(x) => v }
  > type instance Sz[Bar] {
  >   let sz = { let m = memo(fn(x) => 3i32); fn(x: Bar) => m(Foo) }
  > }
  > echoln(show(sz(Bar)))
  > KEL
  $ diktor instinitpolylocal.kel
  3

Ask と Heap はトップレベルの行にない。
処理系は、初期化式で perform ask() を起こす instinitask と、Ref.new を起こす instinitheap を、エフェクトの名前とメソッドの名前を挙げた型エラーで拒否する。
診断の位置は、perform や Ref.new の式ではなく、メソッドの束縛である:

  $ cat > instinitask.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > type class Sz[A] { val sz: (A) => Int32 }
  > newtype Foo = Foo
  > type instance Sz[Foo] {
  >   let sz: (Foo) => Int32 = { let n = perform ask(); fn(x) => n }
  > }
  > echoln(show(sz(Foo)))
  > KEL
  $ diktor instinitask.kel
  ! instinitask.kel:5:7: 型エラー: エフェクト Ask をインスタンスメソッド sz の初期化式では実行できません(初期化式が起こせるのはトップレベルの評価と同じエフェクトです)
  [1]
  $ cat > instinitheap.kel <<'KEL'
  > type class Sz[A] { val sz: (A) => Int32 }
  > newtype Foo = Foo
  > type instance Sz[Foo] {
  >   let sz: (Foo) => Int32 = { let r = Ref.new(0i32); fn(x) => 1i32 }
  > }
  > echoln(show(sz(Foo)))
  > KEL
  $ diktor instinitheap.kel
  ! instinitheap.kel:4:7: 型エラー: エフェクト Heap をインスタンスメソッド sz の初期化式では実行できません(初期化式が起こせるのはトップレベルの評価と同じエフェクトです)
  [1]

前提 [A: Sz] を持つインスタンスの初期化式は、メソッドを使うたびに評価するので、許す行は空の行である。
トップレベルの行にある Console も拒否する:

  $ cat > instinitperuse.kel <<'KEL'
  > type class Sz[A] { val sz: (A) => Int32 }
  > newtype Box[A] = Box(A)
  > type instance Sz[Int32] { let sz(x: Int32) = x }
  > type instance[A: Sz] Sz[Box[_]] {
  >   let sz = { echoln("init"); fn(b: Box[A]) => b match { case Box(x) => sz(x) } }
  > }
  > let pure(n: Int32): Int32 @ {} = sz(Box(n))
  > echoln("start")
  > let k = pure(5i32)
  > echoln(show(k))
  > KEL
  $ diktor instinitperuse.kel
  ! instinitperuse.kel:5:7: 型エラー: エフェクト Console をインスタンスメソッド sz の初期化式では実行できません(メソッドを使うたびに評価する初期化式は、エフェクトを起こせません)
  [1]

ゼロ除算はエフェクト行に現れないので、初期化式に書いても型検査に通る。
前提のないインスタンスでは、インスタンス宣言を実行した時点で実行時エラーになる(LangSpec §6.4):

  $ cat > inidiv.kel <<'KEL'
  > newtype N = N(Int32)
  > let z = 0
  > echoln("a")
  > type instance Show[N] { let show: (N) => String = { let q = 1 / z; fn(x) => "n" } }
  > echoln("b")
  > KEL
  $ diktor inidiv.kel
  a
  実行時エラー: ゼロ除算です
  [3]

前提付きインスタンスでは、メソッドを使うたびに初期化式を評価する。
そのため、実行時エラーはメソッドを使った時点で起きる(LangSpec §6.4):

  $ cat > inipremdiv.kel <<'KEL'
  > newtype Box[A] = Box(A)
  > let z = 0
  > echoln("a")
  > type instance [A: Show] Show[Box[_]] {
  >   let show: (Box[A]) => String = { let q = 1 / z; fn(b) => "box" }
  > }
  > echoln("b")
  > echoln(show(Box(1)))
  > KEL
  $ diktor inipremdiv.kel
  a
  b
  実行時エラー: ゼロ除算です
  [3]

組み込みの Show のインスタンスで、エフェクトを起こさないが構文上の値でもない初期化式
{ let k = 1 + 2; ... } を受理する:

  $ cat > inipure.kel <<'KEL'
  > newtype N = N(Int32)
  > let pre = "n"
  > type instance Show[N] { let show: (N) => String = { let k = 1 + 2; fn(v) => pre + Show.show(k) } }
  > echoln(show(N(0)))
  > KEL
  $ diktor inipure.kel
  n3

対話的な実行ではトップレベルの行が Print を含むので、perform print を起こす初期化式を受理する。
init は宣言を実行したときに、次の入力の echoln("x") より前に出力される。
memo の結果をローカルの束縛に置く instinitpolylocal の形も受理する:

  $ diktor --repl <<'EOF2'
  > type class Sz[A] { val sz: (A) => Int32 }
  > newtype Foo = Foo
  > type instance Sz[Foo] { let sz = { perform print("init"); fn(x: Foo) => 1i32 } }
  > echoln("x")
  > echoln(show(sz(Foo)))
  > let memo[E](f: (Foo) => Int32 @ E): (Foo) => Int32 @ E = { let v = f(Foo); fn(x) => v }
  > newtype Bar = Bar
  > type instance Sz[Bar] { let sz = { let m = memo(fn(x) => 3i32); fn(x: Bar) => m(Foo) } }
  > echoln(show(sz(Bar)))
  > EOF2
  initx
  1
  memo : ((Foo) => Int32) => (Foo) => Int32 = <fn>
  3
