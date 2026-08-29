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

D56 の帰結: 単一フィールドのパンニングが {x,} で書ける({x} はブロック):

  $ printf 'let x = 1\nlet a = {x,}\necholn(show(a.x))\n' > pan1.kel
  $ diktor pan1.kel
  1
