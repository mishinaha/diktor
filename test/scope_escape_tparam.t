剛定数がスコープの外に漏れたときの脱出の報告に、処理系が剛定数を型パラメータの名前と
結び付けていれば、ς1 がどの型パラメータかと、外側の型と共有された変数に入れようとした
ことを添える。escval、esctop、escshared、escrow は関数の型パラメータが漏れる形で、注記が
付く。esccls と escrun は名前と結び付けない剛定数が漏れる形で、注記は付かない。

関数 f の型パラメータ A を、外側の無名関数の注釈の無い引数 y の型に入れる。
f の中の値束縛 z の注釈で落ち、報告は A を名指しする:

  $ cat > escval.kel <<'KEL'
  > let bad = fn(y) => {
  >   let f[A](x: A): A = {
  >     let z: A = y
  >     x
  >   }
  >   f
  > }
  > KEL
  $ diktor --type-check escval.kel
  ! escval.kel:3:9: 型エラー: 注釈された型を満たしません(スコープ付きの型 ς1 がスコープの外に漏れています(ς1 は型パラメータ A です。A のスコープの外の型と共有された、型の決まっていない変数(注釈の無い引数の型や、一般化されない束縛の型など)に A を入れようとしています))
  [1]

トップレベルの一般化されない束縛 k を、型パラメータの値で呼ぶ形(esctop)にも、同じ注記が付く:

  $ cat > esctop.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let k = idf(fn(x) => x)
  > let f[A](x: A): A = k(x)
  > KEL
  $ diktor --type-check esctop.kel
  idf : (A) => A
  k : (_A) => _A
  ! esctop.kel:3:23: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています(ς1 は型パラメータ A です。A のスコープの外の型と共有された、型の決まっていない変数(注釈の無い引数の型や、一般化されない束縛の型など)に A を入れようとしています)
  [1]

f の中で作った変数でも、外側の引数 y の型と単一化されると共有される。
q の型は f の中で作られるが、y(r) で y の引数の型と共有され、r(x) で落ちる。
y(r) の行を外した escnoy は受理する:

  $ cat > escshared.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let bad = fn(y) => {
  >   let f[A](x: A): A = {
  >     let r = idf(fn(q) => q)
  >     let _ = y(r)
  >     r(x)
  >   }
  >   f
  > }
  > KEL
  $ diktor --type-check escshared.kel
  idf : (A) => A
  ! escshared.kel:6:7: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています(ς1 は型パラメータ A です。A のスコープの外の型と共有された、型の決まっていない変数(注釈の無い引数の型や、一般化されない束縛の型など)に A を入れようとしています)
  [1]
  $ cat > escnoy.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let bad = fn(y) => {
  >   let f[A](x: A): A = {
  >     let r = idf(fn(q) => q)
  >     r(x)
  >   }
  >   f
  > }
  > KEL
  $ diktor --type-check escnoy.kel
  idf : (A) => A
  bad : (A) => (B) => B

行の型パラメータ E を外側の引数 y に渡す形(escrow)でも、注記は E を名指しする:

  $ cat > escrow.kel <<'KEL'
  > let bad = fn(y) => {
  >   let f[E](go: () => Unit @ E): Unit @ E = { y(go); go() }
  >   f
  > }
  > KEL
  $ diktor --type-check escrow.kel
  ! escrow.kel:2:46: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています(ς1 は型パラメータ E です。E のスコープの外の型と共有された、型の決まっていない変数(注釈の無い引数の型や、一般化されない束縛の型など)に E を入れようとしています)
  [1]

クラスのメソッドの型パラメータ B を、インスタンスのメソッドの本体から一般化されない
束縛 k に渡す形(esccls)には、注記を添えない。インスタンスのメソッドをクラス宣言の型と
照合するときに作る剛定数を、処理系は型パラメータの名前と結び付けないからである:

  $ cat > esccls.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let k = idf(fn(x) => x)
  > type class C[A] { val m[B]: (A, B) => B }
  > type instance C[Int32] { let m(a, b) = k(b) }
  > KEL
  $ diktor --type-check esccls.kel
  idf : (A) => A
  k : (_A) => _A
  ! esccls.kel:4:30: 型エラー: インスタンスメソッド m がクラス宣言の型を満たしません(スコープ付きの型 ς1 がスコープの外に漏れています)
  [1]

run のリージョン変数の脱出(escrun)には、注記を添えない:

  $ cat > escrun.kel <<'KEL'
  > let esc = run h { Ref.new(0) }
  > KEL
  $ diktor --type-check escrun.kel
  ! escrun.kel:1:11: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]
