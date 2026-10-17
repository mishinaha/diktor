引数の個数の不一致は、関数の呼び出し、perform、関数型どうしの単一化の
どれでも「引数の個数が一致しません」と報告する(LangSpec §3.4)。

呼び出しの実引数が仮引数より少ないときと多いとき。呼び出す関数の
仮引数の個数と渡した個数を述べる:

  $ cat > call0.kel <<'KEL'
  > let f(x: Int32): Int32 = x
  > let b(): Int32 = f()
  > KEL
  $ diktor --type-check call0.kel
  f : (Int32) => Int32
  ! call0.kel:2:18: 型エラー: 引数の個数が一致しません: 呼び出す関数は 1 個の引数を取りますが、0 個を渡しています
  [1]
  $ cat > call2.kel <<'KEL'
  > let f(x: Int32): Int32 = x
  > let b(): Int32 = f(1, 2)
  > KEL
  $ diktor --type-check call2.kel
  f : (Int32) => Int32
  ! call2.kel:2:18: 型エラー: 引数の個数が一致しません: 呼び出す関数は 1 個の引数を取りますが、2 個を渡しています
  [1]

perform の引数の個数も同じく調べる:

  $ cat > perf0.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let f(): Int32 @ Ask = perform ask()
  > KEL
  $ diktor --type-check perf0.kel
  ! perf0.kel:2:24: 型エラー: 引数の個数が一致しません: 操作 ask は 1 個の引数を取りますが、0 個を渡しています
  [1]

1 引数の関数を求める位置に 0 引数のラムダを渡す形。with _ は引数のない
無名関数を渡す(LangSpec §6.5)ので同じ報告になり、2 つの矢印と個数を述べる:

  $ cat > lam.kel <<'KEL'
  > let one[A, E](body: (Int32) => A @ E): A @ E = body(5)
  > let b(): Int32 = one(fn() => 2)
  > KEL
  $ diktor --type-check lam.kel
  one : ((Int32) => A) => A
  ! lam.kel:2:22: 型エラー: 引数の個数が一致しません: () => _A と (Int32) => _B(引数は 0 個と 1 個です)
  [1]
  $ cat > withw.kel <<'KEL'
  > let one[A, E](body: (Int32) => A @ E): A @ E = body(5)
  > let b(): Int32 = {
  >   with _ = one()
  >   2
  > }
  > KEL
  $ diktor --type-check withw.kel
  one : ((Int32) => A) => A
  ! withw.kel:3:3: 型エラー: 引数の個数が一致しません: () => _A と (Int32) => _B(引数は 0 個と 1 個です)
  [1]

注釈の矢印と初期化式の矢印の個数が違う形:

  $ cat > ann.kel <<'KEL'
  > let g: (Int32) => Int32 = fn() => 2
  > KEL
  $ diktor --type-check ann.kel
  ! ann.kel:1:5: 型エラー: 注釈された型を満たしません(引数の個数が一致しません: (Int32) => Int32 と () => _A(引数は 1 個と 0 個です))
  [1]

ラベル付きの引数を含む呼び出しは個数を比べず、従来どおりラベルの
有無を報告する:

  $ cat > label.kel <<'KEL'
  > let f(x: Int32): Int32 = x
  > let b(): Int32 = f(x = 1)
  > KEL
  $ diktor --type-check label.kel
  f : (Int32) => Int32
  ! label.kel:2:18: 型エラー: ラベル x がありません(行は閉じています)
  [1]

newtype のコンストラクタの関数のフィールド、pub の値束縛の注釈、
インスタンスメソッドとクラス宣言の型でも、2 つの矢印と個数を述べる:

  $ cat > ctor.kel <<'KEL'
  > newtype Fn1 = Fn1((Int32) => Int32)
  > let v = Fn1(fn() => 1)
  > KEL
  $ diktor --type-check ctor.kel
  ! ctor.kel:2:9: 型エラー: 引数の個数が一致しません: () => _A と (Int32) => Int32 @ {}(引数は 0 個と 1 個です)
  [1]
  $ cat > pubv.kel <<'KEL'
  > pub let h: (Int32) => Int32 = fn() => 1
  > KEL
  $ diktor --type-check pubv.kel
  ! pubv.kel:1:9: 型エラー: 注釈された型を満たしません(引数の個数が一致しません: (Int32) => Int32 @ {} と () => _A(引数は 1 個と 0 個です))
  [1]
  $ cat > inst.kel <<'KEL'
  > type class Sh[A] {
  >   val sh: (A) => Int32
  > }
  > type instance Sh[Int32] {
  >   let sh() = 1
  > }
  > KEL
  $ diktor --type-check inst.kel
  ! inst.kel:5:7: 型エラー: インスタンスメソッド sh がクラス宣言の型を満たしません(引数の個数が一致しません: () => Int32 と (Int32) => Int32 @ {}(引数は 0 個と 1 個です))
  [1]

呼び出しの個数は実引数を調べる前に比べる。実引数の中に別の誤りが
あっても、個数の不一致を呼び出しの位置で先に報告する:

  $ cat > first.kel <<'KEL'
  > let f(x: Int32): Int32 = x
  > let b(): Int32 = f(nosuch, 2)
  > KEL
  $ diktor --type-check first.kel
  f : (Int32) => Int32
  ! first.kel:2:18: 型エラー: 引数の個数が一致しません: 呼び出す関数は 1 個の引数を取りますが、2 個を渡しています
  [1]

個数が合う呼び出しは通る:

  $ cat > ok.kel <<'KEL'
  > let zero[A, E](body: () => A @ E): A @ E = body()
  > let one[A, E](body: (Int32) => A @ E): A @ E = body(5)
  > let f(x: Int32, y: Int32): Int32 = x + y
  > let a(): Int32 = {
  >   with _ = zero()
  >   1
  > }
  > let b(): Int32 = {
  >   with x = one()
  >   x
  > }
  > echoln(show(a() + b() + f(1, 2)))
  > KEL
  $ diktor ok.kel
  9
