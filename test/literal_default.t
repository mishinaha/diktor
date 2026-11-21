接尾辞のない数値リテラルの型が文脈から決まらないときは、宣言の終わりか束縛の一般化の時点で、型を Int32 か Float64 に決める(既定化、LangSpec §4.2)。
既定の型がほかの制約を満たさないときは型エラーになり、既定化はエラーを報告する位置を次の順に探す。
まず、現在の宣言の中で、その制約の証拠(どのインスタンスの辞書を使うかを表す項)がまだ決まっていない箇所を探し、その位置を使う。
以下では、この箇所(制約を持ち込んだ演算子や参照)を穴と呼ぶ。
穴が見つからなければ、その制約を付けたリテラルの位置を使う。
それも見つからなければ、既定の型を選ぶもとになった予約述語(Integral か Fractional)を付けたリテラルの位置を使う。
remlit の 1.5 % 2.0 では、Rem の穴を持つ % の式の位置(リテラル 1.5 と同じ列)を報告する:

  $ cat > remlit.kel <<'KEL'
  > let a = 0
  > let b = 1.5 % 2.0
  > KEL
  $ diktor remlit.kel
  ! remlit.kel:2:9: 型エラー: Float64 は Rem のインスタンスではありません
  [1]

演算子と引数が離れていても、演算子の位置を報告する。
無名関数の中の % に引数 1.5 を渡す場合は、% の式の位置(2:19)になる:

  $ cat > lamlit.kel <<'KEL'
  > let a = 0
  > let h = (fn(x) => x % x)(1.5)
  > KEL
  $ diktor lamlit.kel
  ! lamlit.kel:2:19: 型エラー: Float64 は Rem のインスタンスではありません
  [1]

mixlit の 1 + 1.5 では、型を Int32 に決めるので、Fractional を満たせない。
Fractional には穴がないので、Fractional を付けたリテラル 1.5 の位置(2:13)を報告する:

  $ cat > mixlit.kel <<'KEL'
  > let a = 0
  > let z = 1 + 1.5
  > KEL
  $ diktor mixlit.kel
  ! mixlit.kel:2:13: 型エラー: Int32 は Fractional のインスタンスではありません
  [1]

ユーザ定義のクラスでも同じで、メソッドを参照した位置を報告する:

  $ cat > clslit.kel <<'KEL'
  > type class C[A] { val f: (A) => A }
  > type instance C[Int32] { let f(x) = x }
  > let z = f(1.5)
  > KEL
  $ diktor clslit.kel
  ! clslit.kel:3:9: 型エラー: Float64 は C のインスタンスではありません
  [1]

インスタンスの前提から伝わった制約が満たされないときは、そのもとになった外側の制約を持ち込んだ参照の位置を報告する:

  $ cat > premlit.kel <<'KEL'
  > type class C[A] { val c: (A) => Int32 }
  > type instance C[Int32] { let c(x) = x }
  > newtype Box[A] = Box(A)
  > type instance[A: C] C[Box[_]] { let c(b) = 0 }
  > let z = c(Box(1.5))
  > KEL
  $ diktor premlit.kel
  ! premlit.kel:5:9: 型エラー: Float64 は C のインスタンスではありません。Box[Float64] が C であるための前提として要求されました
  [1]

weaklit では、制約 C を持ち込んだ c の参照は 6 行目の g の宣言にある。
g の右辺は関数の適用なので一般化されず、C は 7 行目の宣言に伝わる。
7 行目の宣言には、C の穴も、C を付けたリテラルも見つからない。
そのため、既定の型を選ぶもとになった Fractional を付けた、7 行目の 1.5 の位置(7:15)を報告する。
6 行目の g は受理されるので、g の型を表示する行が出力される:

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
  ! weaklit.kel:7:15: 型エラー: Float64 は C のインスタンスではありません。Box[Float64] が C であるための前提として要求されました
  [1]

orderlit は、関数の本体に一般化しない束縛 u と w を並べ、どちらも既定化に失敗する。
2 つのリテラルの型変数は宣言の終わりの既定化まで残り、そこでは先に作った型変数から順に調べるので、
2 行目の 1.5 の位置(2:15)を報告する。
w を関数 w() に変えると、w の本体の型変数は w を一般化する時点で既定化される。
この既定化は宣言の終わりより先に行われるので、3 行目の % の式の位置(3:13)を報告する:

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
  $ sed -i 's/let w =/let w() =/' orderlit.kel
  $ diktor --type-check orderlit.kel
  ! orderlit.kel:3:13: 型エラー: Float64 は Rem のインスタンスではありません
  [1]

一般化する関数の本体でも、関数の本体の中の一般化しない束縛でも、演算子の位置を報告する:

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

インスタンスのメソッドの本体の中でも同じである:

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

対話的な実行でも同じ位置を報告する:

  $ diktor --repl <<'KEL'
  > let b = 1.5 % 2.0
  > echoln(show(1 + 1.5))
  > KEL
  ! <stdin>:1:9: 型エラー: Float64 は Rem のインスタンスではありません
  ! <stdin>:2:17: 型エラー: Int32 は Fractional のインスタンスではありません
