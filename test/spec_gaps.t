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

Array.each は Heap を要求**しない**(I12 の一貫性修正は M20 検証で撤回 —
each はコールバックと行を共有するため、Heap を課すと @ {} の純粋
コールバックが渡せなくなる。読みの純粋性は Array / MutArray 分離
(D64)で一括裁定する):

  $ cat > eachheap.kel <<'KEL'
  > let total(xs: Array[Int32]): Int32 = run h {
  >   let acc = Ref.new(0)
  >   Array.each(xs, fn(x) => Ref.set(acc, Ref.get(acc) + x))
  >   Ref.get(acc)
  > }
  > KEL
  $ diktor --type-check eachheap.kel
  total : (Array[Int32]) => Int32
  $ printf 'let use(xs: Array[Int32]): {} = run h { Array.each(xs, fn(x) => ()) }\n' > eachpure.kel
  $ diktor --type-check eachpure.kel
  use : (Array[Int32]) => {}

なお注釈で @ {} と**閉じた**コールバックを run の中の each に渡す形は、
each とは無関係に落ちる(run が体の行に Heap[h] を要求し、閉じた行は
それを受けられない — 非サブエフェクティングの既存規則):

  $ cat > eachclosed.kel <<'KEL'
  > let g(x: Int32): {} @ {} = {}
  > let use(xs: Array[Int32]): {} = run h { Array.each(xs, g) }
  > KEL
  $ diktor --type-check eachclosed.kel
  g : (Int32) => {}
  ! eachclosed.kel:2:56: 型エラー: ラベル Heap がありません(行は閉じています)
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

cancel 節からの perform の再入(I10 / D66)。現状: 巻き戻し中の再入は
処理され(from-cancel の note は外側の note ハンドラに届いて resume)、
cancel 内で生じる Unwind は抑制され、巻き戻しは続行して外側の 99 が
返る。仕様が (b) 自ハンドラ無効化 か (c) 実行時エラー を選んだら
ここが変わる:

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
