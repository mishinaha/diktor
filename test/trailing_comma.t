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
