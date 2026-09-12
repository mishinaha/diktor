仕様待ちの穴の固定(M20 / I1 / I5 / I10 / D64〜D66)。**このファイルは
diktor の意図した挙動ではなく、仕様側の裁定待ちの現状を機械に見張らせる
ためにある。** 仕様が動いたらここが最初に鳴り、doc/log/260830-1-m20.md の
台帳が「触る場所」を教える。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

Array の穴(I1 / I12 / D64)は 2026-09-12 の仕様改訂(§10 の不変 Array[A] /
可変 MutableArray[h, A] の分離)で閉じた。ここにあった arrayhole / eachheap /
eachpure / eachclosed の 4 ブロックは test/region.t へ移し、「仕様の穴」では
なく「意図した挙動」のゴールデンになっている(M24。設計は
doc/log/260912-1-plan.md §3)。

暫定裁定の観測点(I5 / D65): タプルラベルは _item、整数リテラルは
Int32 に既定化:

  $ cat > tupledefault.kel <<'KEL'
  > let fst_[A, R](t: {_item: A extends R}): A = t._0
  > let n = 1 + 1
  > KEL
  $ diktor --type-check tupledefault.kel
  fst_ : ({_item: A extends R1}) => A
  n : Int32

cancel 節からの perform の再入(I10 / D66)は仕様 §9 が裁定した(D100。cancel 節は
自分のハンドラが外れた文脈で走り、perform は外側の同名ハンドラに届く)。
観測点 cancelre.kel は test/eval.t の cancelouter / cancelnores へ移した。
