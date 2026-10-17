型パラメータの行変数と空の行の衝突(LangSpec §13.2)。行変数は何が入るか決まって
いないので、@ {} や入れ子の矢印で省略した @(どちらも空の行)とは一致しない。
単一化の報告は原因だけを述べ、直し方を書かない。下のブロックは、落ちる形ごとに、
報告の文言と、通るように書き換えた形を並べる。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

関数束縛の返り値の注釈が空の行の矢印だと、原因だけを報告する。返り値の
矢印に @ E と書けば通る:

  $ cat > fnrigid.kel <<'KEL'
  > let h[E](g: () => Int32 @ E): () => Int32 @ {} = g
  > KEL
  $ diktor --type-check fnrigid.kel
  ! fnrigid.kel:1:5: 型エラー: 注釈された返り値型を満たしません(行 ς1 は注釈で固定された行変数なので、空の行と一致させられません)
  [1]
  $ cat > fnrigidok.kel <<'KEL'
  > let h[E](g: () => Int32 @ E): () => Int32 @ E = g
  > KEL
  $ diktor --type-check fnrigidok.kel
  h : (() => Int32) => () => Int32

valrigid は、局所の値束縛の注釈の空の行が、外側の型パラメータの行変数とぶつかる形で、
報告は原因だけを述べる。valrigidomit は同じ束縛の注釈を省いた形で、通る:

  $ cat > valrigid.kel <<'KEL'
  > let f[E](g: () => Int32 @ E): Int32 @ E = {
  >   let k: () => Int32 @ {} = g
  >   k()
  > }
  > KEL
  $ diktor --type-check valrigid.kel
  ! valrigid.kel:2:7: 型エラー: 注釈された型を満たしません(行 ς1 は注釈で固定された行変数なので、空の行と一致させられません)
  [1]
  $ cat > valrigidomit.kel <<'KEL'
  > let f[E](g: () => Int32 @ E): Int32 @ E = {
  >   let k = g
  >   k()
  > }
  > KEL
  $ diktor --type-check valrigidomit.kel
  f : (() => Int32) => Int32

valinitrigid は、空の行が初期化式の関数 ap の仮引数の側にある形で、valrigid と同じ文言に
なる。k の注釈には行変数 E が既に書かれている。valinitrigidok は ap に型パラメータ R を
取らせて仮引数の行を R にした形で、k の注釈を変えずに通る:

  $ cat > valinitrigid.kel <<'KEL'
  > let ap(h: () => Int32 @ {}): Int32 = h()
  > let f[E](g: () => Int32 @ E): Int32 @ E = {
  >   let k: (() => Int32 @ E) => Int32 = ap
  >   k(g)
  > }
  > KEL
  $ diktor --type-check valinitrigid.kel
  ap : (() => Int32 @ {}) => Int32
  ! valinitrigid.kel:3:7: 型エラー: 注釈された型を満たしません(行 ς1 は注釈で固定された行変数なので、空の行と一致させられません)
  [1]
  $ cat > valinitrigidok.kel <<'KEL'
  > let ap[R](h: () => Int32 @ R): Int32 = h()
  > let f[E](g: () => Int32 @ E): Int32 @ E = {
  >   let k: (() => Int32 @ E) => Int32 = ap
  >   k(g)
  > }
  > KEL
  $ diktor --type-check valinitrigidok.kel
  ap : (() => Int32) => Int32
  f : (() => Int32) => Int32

clsrigid、clsrecrigid、clsfnrigid は、宣言が行変数 E を取るメソッドの実装を、それぞれ
値束縛、let rec の値束縛、型パラメータを取らない関数束縛で書き、引数の関数の行を省いた
(空の行)形で、どれも報告は原因だけを述べる。clsfnrigidtp は関数束縛に型パラメータ E を
取らせて引数と返り値の行に書いた形で、clsvalomit は値束縛の注釈を省いた形で、clsrecomit は
let rec の値束縛の注釈を省いた形で、どれも通る:

  $ cat > clsrigid.kel <<'KEL'
  > type class Run[A] {
  >   val run1[E]: (A, () => Int32 @ E) => Int32 @ E
  > }
  > type instance Run[Int32] {
  >   let run1: (Int32, () => Int32) => Int32 = fn(a, g) => g()
  > }
  > KEL
  $ diktor --type-check clsrigid.kel
  ! clsrigid.kel:5:7: 型エラー: インスタンスメソッド run1 がクラス宣言の型を満たしません(行 ς1 は注釈で固定された行変数なので、空の行と一致させられません)
  [1]
  $ cat > clsrecrigid.kel <<'KEL'
  > type class Run[A] {
  >   val run1[E]: (A, () => Int32 @ E) => Int32 @ E
  > }
  > type instance Run[Int32] {
  >   let rec run1: (Int32, () => Int32) => Int32 = fn(a, g) => g()
  > }
  > KEL
  $ diktor --type-check clsrecrigid.kel
  ! clsrecrigid.kel:5:11: 型エラー: インスタンスメソッド run1 がクラス宣言の型を満たしません(行 ς1 は注釈で固定された行変数なので、空の行と一致させられません)
  [1]
  $ cat > clsfnrigid.kel <<'KEL'
  > type class Run[A] {
  >   val run1[E]: (A, () => Int32 @ E) => Int32 @ E
  > }
  > type instance Run[Int32] {
  >   let run1(a: Int32, g: () => Int32): Int32 = g()
  > }
  > KEL
  $ diktor --type-check clsfnrigid.kel
  ! clsfnrigid.kel:5:7: 型エラー: インスタンスメソッド run1 がクラス宣言の型を満たしません(行 ς1 は注釈で固定された行変数なので、空の行と一致させられません)
  [1]
  $ cat > clsfnrigidtp.kel <<'KEL'
  > type class Run[A] {
  >   val run1[E]: (A, () => Int32 @ E) => Int32 @ E
  > }
  > type instance Run[Int32] {
  >   let run1[E](a: Int32, g: () => Int32 @ E): Int32 @ E = g()
  > }
  > KEL
  $ diktor --type-check clsfnrigidtp.kel
  $ cat > clsvalomit.kel <<'KEL'
  > type class Run[A] {
  >   val run1[E]: (A, () => Int32 @ E) => Int32 @ E
  > }
  > type instance Run[Int32] {
  >   let run1 = fn(a, g) => g()
  > }
  > KEL
  $ diktor --type-check clsvalomit.kel
  $ cat > clsrecomit.kel <<'KEL'
  > type class Run[A] {
  >   val run1[E]: (A, () => Int32 @ E) => Int32 @ E
  > }
  > type instance Run[Int32] {
  >   let rec run1 = fn(a, g) => g()
  > }
  > KEL
  $ diktor --type-check clsrecomit.kel
