末尾カンマは例外なく全カンマ区切りリストで許す(M18 / F1 / D56。
計画 §6.1 の字義、260829-3 課題 15)。

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

ty_args は instance の型引数とエフェクト行のラベル引数でも同じ規則:

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
  g : (Ref[A, Int32]) => Int32 @ {Heap[A] extends R1}

末尾カンマが付くのは最後の**要素**の後だけ。...rest と extends T は
要素ではなく終端子なので、その後には付けられない(検証で確定した境界):

  $ printf 'let f(t) = t match { case {x, ...r,} => x }\n' > term1.kel
  $ diktor --type-check term1.kel
  term1.kel:1:35: パースエラー(付近のトークンを確認してください)
  [2]

残る 8 種のリスト(引数・パラメータ・レコード・タプル・パターン・エフェクト行・
effect の操作・コンストラクタのフィールド)。§0 の「どの種類でも」の残り半分:

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

終端子 extends の後にもカンマは置けない(型・式の両方。既存の ...rest と
同じ境界):

  $ printf 'let f[R](p: {x: Int32 extends R,}): Int32 = p.x\n' > term2.kel
  $ diktor --type-check term2.kel
  term2.kel:1:32: パースエラー(付近のトークンを確認してください)
  [2]

  $ printf 'let r = {a = 1}\nlet s = {b = 2, extends r,}\n' > term3.kel
  $ diktor --type-check term3.kel
  term3.kel:2:26: パースエラー(付近のトークンを確認してください)
  [2]

  $ printf 'let f(t) = t match { case (x, ...r,) => x }\n' > term4.kel
  $ diktor --type-check term4.kel
  term4.kel:1:35: パースエラー(付近のトークンを確認してください)
  [2]

終端子の**前**のカンマは要素の末尾カンマなので置ける:

  $ printf 'let f[R](p: {x: Int32, extends R}): Int32 = p.x\n' > term5.kel
  $ diktor --type-check term5.kel
  f : ({x: Int32 extends R1}) => Int32

D56 の帰結: 単一フィールドのパンニングが {x,} で書ける({x} はブロック):

  $ printf 'let x = 1\nlet a = {x,}\necholn(show(a.x))\n' > pan1.kel
  $ diktor pan1.kel
  1
