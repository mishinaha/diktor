仕様待ちの穴の固定(M20 / I1 / I5 / I10 / D64〜D66)。**このファイルは
diktor の意図した挙動ではなく、仕様側の裁定待ちの現状を機械に見張らせる
ためにある。** 仕様が動いたらここが最初に鳴り、doc/log/260830-1-m20.md の
台帳が「触る場所」を教える。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

Array が h を持たないため、引数を破壊する関数が純粋として型付く
(I1 / D64。仕様への対案は Array / MutArray 分離 — sample.kel を
書き換えずに済む唯一の案):

  $ cat > arrayhole.kel <<'KEL'
  > let bump(a: Array[Int32]): Unit = run h { Array.set(a, 0, 42) }
  > let leak(): Array[Int32] = run h { Array.new(3, 0) }
  > let peek(a: Array[Int32]): Int32 = run h { Array.get(a, 0) }
  > KEL
  $ diktor --type-check arrayhole.kel
  bump : (Array[Int32]) => {}
  leak : () => Array[Int32]
  peek : (Array[Int32]) => Int32

Array.each は Heap を要求する(I12 — get / set と表を揃える一貫性の
修正。h は自由変数のままなので上の穴は塞がっていない):

  $ cat > eachheap.kel <<'KEL'
  > let total(xs: Array[Int32]): Int32 = run h {
  >   let acc = Ref.new(0)
  >   Array.each(xs, fn(x) => Ref.set(acc, Ref.get(acc) + x))
  >   Ref.get(acc)
  > }
  > KEL
  $ diktor --type-check eachheap.kel
  total : (Array[Int32]) => Int32
  $ printf 'let outside(xs: Array[Int32]): {} @ {} = Array.each(xs, fn(x) => ())\n' > eachout.kel
  $ diktor --type-check eachout.kel
  ! eachout.kel:1:42: 型エラー: ラベル Heap がありません(行は閉じています)
  [1]

暫定裁定の観測点(I5 / D65): タプルラベルは _item、整数リテラルは
Int32 に既定化:

  $ cat > tupledefault.kel <<'KEL'
  > let fst_[A, R](t: {_item: A extends R}): A = t._0
  > let n = 1 + 1
  > KEL
  $ diktor --type-check tupledefault.kel
  fst_ : ({_item: A extends R1}) => A
  n : Int32

cancel 節からの perform の再入(I10 / D66)。現状: 再入は再設置された
自分のハンドラに捕まり、cancel 内で生じる Unwind は抑制され、巻き戻しは
続行する(from-cancel の note は resume され、外側の 99 が返る)。
仕様が (b) 自ハンドラ無効化 か (c) 実行時エラー を選んだらここが変わる:

  $ cat > cancelre.kel <<'KEL'
  > effect Stop = { stop: () => {} }
  > effect Log = { note: (String) => {} }
  > let inner[E](): Int32 @ {Log, Stop extends E} =
  >   { perform stop(); 1 } handle {
  >     case note(s) => resume({})
  >     case cancel => { perform note("from-cancel"); () }
  >     case return(x) => x
  >   }
  > let mid[E](): Int32 @ {Stop extends E} = inner() handle {
  >   case note(s) => resume({})
  >   case return(x) => x
  > }
  > let go[E](): Int32 @ E = mid() handle {
  >   case stop() => 99
  >   case return(x) => x
  > }
  > echoln(show(go()))
  > KEL
  $ diktor cancelre.kel
  99
