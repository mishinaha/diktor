par / par_map の組み込み登録(M16 / H2、D45)。逐次実装だが、
コールバックの行が @ {} に閉じているため並列実行と観測同値。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

  $ cat > par.kel <<'KEL'
  > let mk(): Array[Int32] = run h {
  >   let a = MutableArray.new(3, 0)
  >   MutableArray.set(a, 0, 1)
  >   MutableArray.set(a, 1, 2)
  >   MutableArray.set(a, 2, 3)
  >   MutableArray.freeze(a)
  > }
  > let total(a: Array[Int32]): Int32 = run h {
  >   let acc = Ref.new(0)
  >   Array.each(a, fn(x) => Ref.set(acc, Ref.get(acc) + x))
  >   Ref.get(acc)
  > }
  > let dbl(x: Int32): Int32 = x * 2
  > echoln(show(total(par_map(mk(), dbl))))
  > let p = par(fn() => 1 + 2, fn() => "ok")
  > echoln(show(p._0))
  > echoln(p._1)
  > KEL
  $ diktor par.kel
  12
  3
  ok

コールバックの純粋性は型で守られる(仕様 sample.kel §11 の決定性の根拠。
既知の破れは 260829-5 台帳 V14 / V15 — 高階位置の省略 @ とファイル prim):

  $ cat > parbad.kel <<'KEL'
  > let mk(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(1, 0)) }
  > let _ = par_map(mk(), fn(x) => { echo("no"); x })
  > KEL
  $ diktor --type-check parbad.kel
  mk : () => Array[Int32]
  ! parbad.kel:2:34: 型エラー: ラベル Console がありません(行は閉じています)
  [1]

sample.kel 自身の let par_map = ??? / let par = ??? は組み込みを覆うので
ゴールデン不変(typecheck_sample.t が回帰)。
