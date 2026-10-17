接尾辞の無い数値リテラルの型は、宣言の終わりか束縛の一般化で Int32 か Float64 に決まる
(LangSpec §4.2)。決まった型がほかの制約を満たさないときの型エラーは、
その制約を持ち込んだ演算子や参照の位置に出る。
1.5 % 2.0 の Rem は % の式の位置(リテラルの 1.5 と同じ列)に出る:

  $ cat > remlit.kel <<'KEL'
  > let a = 0
  > let b = 1.5 % 2.0
  > KEL
  $ diktor remlit.kel
  ! remlit.kel:2:9: 型エラー: Float64 は Rem のインスタンスではありません
  [1]

演算子が引数の側から離れていても、演算子の位置に出る。
ラムダの中の % と、引数の 1.5 では、% の式の位置(2:19)になる:

  $ cat > lamlit.kel <<'KEL'
  > let a = 0
  > let h = (fn(x) => x % x)(1.5)
  > KEL
  $ diktor lamlit.kel
  ! lamlit.kel:2:19: 型エラー: Float64 は Rem のインスタンスではありません
  [1]

整数と小数のリテラルが同じ型になる形では、Int32 に決まり、小数のリテラルの位置に出る:

  $ cat > mixlit.kel <<'KEL'
  > let a = 0
  > let z = 1 + 1.5
  > KEL
  $ diktor mixlit.kel
  ! mixlit.kel:2:13: 型エラー: Int32 は Fractional のインスタンスではありません
  [1]

利用者のクラスでも同じで、メソッドの参照の位置に出る:

  $ cat > clslit.kel <<'KEL'
  > type class C[A] { val f: (A) => A }
  > type instance C[Int32] { let f(x) = x }
  > let z = f(1.5)
  > KEL
  $ diktor clslit.kel
  ! clslit.kel:3:9: 型エラー: Float64 は C のインスタンスではありません
  [1]

インスタンスの前提から伝わった制約は、外側の制約を持ち込んだ参照の位置に出る:

  $ cat > premlit.kel <<'KEL'
  > type class C[A] { val c: (A) => Int32 }
  > type instance C[Int32] { let c(x) = x }
  > newtype Box[A] = Box(A)
  > type instance[A: C] C[Box[_]] { let c(b) = 0 }
  > let z = c(Box(1.5))
  > KEL
  $ diktor premlit.kel
  ! premlit.kel:5:9: 型エラー: Float64 は C のインスタンスではありません
  [1]

一般化しない束縛を経由して前の宣言から伝わった制約は、前の宣言の位置ではなく、
既定の型を決めたいまの宣言のリテラルの位置に出る。
2 行目の g は受理され、7 行目の 1.5(7:15)を指す:

  $ cat > weaklit.kel <<'KEL'
  > type class C[A] { val c: (A) => Int32 }
  > type instance C[Int32] { let c(x) = x }
  > newtype Box[A] = Box(A)
  > type instance[A: C] C[Box[_]] { let c(b) = 0 }
  > let ident[T](x: T): T = x
  > let g = ident(fn(y) => c(y))
  > let k = g(Box(1.5))
  > KEL
  $ diktor --type-check weaklit.kel
  ident : (A) => A
  g : [_A: C] (_A) => Int32 @ {}
  ! weaklit.kel:7:15: 型エラー: Float64 は C のインスタンスではありません
  [1]

同じ宣言に既定化の失敗が 2 つあるときは、先に書いた方を報告する:

  $ cat > orderlit.kel <<'KEL'
  > let g(n: Int32): Int32 = {
  >   let u = 1 + 1.5
  >   let w = 2.5 % 3.0
  >   n
  > }
  > KEL
  $ diktor --type-check orderlit.kel
  ! orderlit.kel:2:15: 型エラー: Int32 は Fractional のインスタンスではありません
  [1]

一般化する関数の本体と、関数の本体の中の一般化しない束縛でも、演算子の位置に出る:

  $ cat > genlit.kel <<'KEL'
  > let f() = 1.5 % 2.0
  > let g(n: Int32): Int32 = {
  >   let u = 1.5 % 2.0
  >   n
  > }
  > KEL
  $ diktor --type-check genlit.kel
  ! genlit.kel:1:11: 型エラー: Float64 は Rem のインスタンスではありません
  [1]
  $ sed -i 1d genlit.kel
  $ diktor --type-check genlit.kel
  ! genlit.kel:2:11: 型エラー: Float64 は Rem のインスタンスではありません
  [1]

インスタンスのメソッドの本体の中でも同じ:

  $ cat > instlit.kel <<'KEL'
  > type class D[A] { val d: (A) => Float64 }
  > type instance D[Int32] {
  >   let d(x) = {
  >     let k = 1.5 % 2.0
  >     k
  >   }
  > }
  > KEL
  $ diktor --type-check instlit.kel
  ! instlit.kel:4:13: 型エラー: Float64 は Rem のインスタンスではありません
  [1]

対話的な実行でも同じ位置に出る:

  $ diktor --repl <<'KEL'
  > let b = 1.5 % 2.0
  > echoln(show(1 + 1.5))
  > KEL
  ! <stdin>:1:9: 型エラー: Float64 は Rem のインスタンスではありません
  ! <stdin>:2:17: 型エラー: Int32 は Fractional のインスタンスではありません
