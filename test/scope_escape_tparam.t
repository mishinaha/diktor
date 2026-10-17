型パラメータの剛定数がスコープの外に漏れると、脱出の報告の後ろに、ς1 がどの型パラメータかと、
外側の型と共有された変数に入れようとしたことを添える。

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
q の型は f の中で作られるが、y(r) で y の引数の型と共有され、r(x) で落ちる:

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

run のリージョン変数の脱出(escrun)には、注記を添えない:

  $ cat > escrun.kel <<'KEL'
  > let esc = run h { Ref.new(0) }
  > KEL
  $ diktor --type-check escrun.kel
  ! escrun.kel:1:11: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]
