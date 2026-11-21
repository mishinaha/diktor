末尾カンマは、カンマで区切るリストのどの種類でも、最後の要素の後ろに書ける(sample.kel §0)。
型引数、型パラメータ、高カインドの型パラメータの穴のリスト:

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

  $ cat > tc.kel <<'KEL'
  > let a: List[Int32,] = Nil
  > let f[A,](x: A): A = x
  > let m[F[_,_,]](x: Int32): Int32 = x
  > KEL
  $ diktor --type-check tc.kel
  a : List[Int32]
  f : (A) => A
  m : (Int32) => Int32

インスタンスの型引数とエフェクトのラベルの引数も型引数のリストなので、同じ規則に従う:

  $ cat > tc2.kel <<'KEL'
  > type class Sizeof[A] {
  >   val sizeof: (A) => Int32
  > }
  > type instance Sizeof[Int32,] {
  >   let sizeof(x) = 4
  > }
  > let n = sizeof(1)
  > let g[h](r: Ref[h, Int32,]): Int32 @ {Heap[h,]} = Ref.get(r)
  > KEL
  $ diktor --type-check tc2.kel
  n : Int32
  g : (Ref[h, Int32]) => Int32 @ {Heap[h]}

末尾カンマを書けるのは最後の**要素**の後ろだけである。...rest と extends T は
要素ではなくリストを終える構文なので、その後ろには書けない:

  $ printf 'let f(t) = t match { case {x, ...r,} => x }\n' > term1.kel
  $ diktor --type-check term1.kel
  term1.kel:1:35: 構文エラー: 付近のトークンを確認してください
  [2]

残りの 8 種類のリスト(引数、パラメータ、レコード、タプル、パターン、エフェクト行、
effect の操作、コンストラクタのフィールド)にも末尾カンマを書ける:

  $ cat > tc3.kel <<'KEL'
  > effect Ev = {
  >   op1: (Int32,) => Int32,
  >   op2: (String) => {},
  > }
  > newtype C = C(Int32, b: String,)
  > let f(x: Int32, y: Int32,): Int32 = x
  > let g() = f(1, 2,)
  > let r = {a = 1, b = 2,}
  > let t = (1, 2,)
  > let pm(v: C): Int32 = v match { case C(a, b,) => a }
  > let pt(v: (Int32, Int32)): Int32 = v match { case (a, b,) => a }
  > let er(k: () => {} @ {Ev, Console,}): Int32 = 1
  > KEL
  $ diktor --type-check tc3.kel
  f : (Int32, Int32) => Int32
  g : () => Int32
  r : {a: Int32, b: Int32}
  t : (Int32, Int32)
  pm : (C) => Int32
  pt : ((Int32, Int32)) => Int32
  er : (() => {} @ {Ev, Console}) => Int32

リストを終える構文 extends の後ろにもカンマは書けない。型でも式でも、...rest と
同じである:

  $ printf 'let f[R](p: {x: Int32 extends R,}): Int32 = p.x\n' > term2.kel
  $ diktor --type-check term2.kel
  term2.kel:1:32: 構文エラー: 付近のトークンを確認してください
  [2]

  $ printf 'let r = {a = 1}\nlet s = {b = 2, extends r,}\n' > term3.kel
  $ diktor --type-check term3.kel
  term3.kel:2:26: 構文エラー: 付近のトークンを確認してください
  [2]

  $ printf 'let f(t) = t match { case (x, ...r,) => x }\n' > term4.kel
  $ diktor --type-check term4.kel
  term4.kel:1:35: 構文エラー: 付近のトークンを確認してください
  [2]

リストを終える構文の**前**のカンマは、最後の要素の末尾カンマなので書ける:

  $ printf 'let f[R](p: {x: Int32, extends R}): Int32 = p.x\n' > term5.kel
  $ diktor --type-check term5.kel
  f : ({x: Int32 extends R1}) => Int32

フィールドの省略記法(punning)で書いたフィールド 1 つのレコードは {x,} と書ける({x} はブロックになる):

  $ printf 'let x = 1\nlet a = {x,}\necholn(show(a.x))\n' > pan1.kel
  $ diktor pan1.kel
  1
