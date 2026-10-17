pub newtype のフィールド、effect の操作、type class のメソッドごとの検査の診断の位置。
下のブロックは、検査ごとに、その診断がどの位置を指すかを示す。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

ntpos は、pub newtype の 2 つ目のラベルつきのフィールド fail の矢印に @ が無い形で、
完全注釈の診断は宣言の先頭ではなく、ラベル fail の右の型(4:11)を指す:

  $ cat > ntpos.kel <<'KEL'
  > module P {
  >   pub newtype Parser[A] = Parser(
  >     go: (String) => Option[A] @ {},
  >     fail: (String) => Unit)
  > }
  > KEL
  $ diktor --type-check ntpos.kel
  ! ntpos.kel:4:11: 型エラー: pub な newtype のフィールドには完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]

ntpos2 は、2 つ目のコンストラクタ B の 2 つ目のフィールドの型引数の中の矢印に @ が無い形で、
診断はそのフィールドの型の先頭の List(2:14)を指す:

  $ cat > ntpos2.kel <<'KEL'
  > pub newtype T = A((Int32) => Int32 @ {})
  >   | B(Int32, List[(Int32) => Int32])
  > KEL
  $ diktor --type-check ntpos2.kel
  ! ntpos2.kel:2:14: 型エラー: pub な newtype のフィールドには完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]

effpos は、effect の操作 level の型が矢印でない形で、診断はその型(3:10)を指す:

  $ cat > effpos.kel <<'KEL'
  > effect Log = {
  >   log: (String) => Unit,
  >   level: Int32
  > }
  > KEL
  $ diktor --type-check effpos.kel
  ! effpos.kel:3:10: 型エラー: 操作 level の型は矢印型でなければなりません
  [1]

effpos2 は予約された操作名 cancel を宣言する形で、診断は名前の右にある型(3:11)を指す:

  $ cat > effpos2.kel <<'KEL'
  > effect Log = {
  >   log: (String) => Unit,
  >   cancel: () => Unit
  > }
  > KEL
  $ diktor --type-check effpos2.kel
  ! effpos2.kel:3:11: 型エラー: 操作名 cancel は予約されています(handle の cancel 節と衝突するため宣言できません)
  [1]

effpos3 は英小文字で始まらない操作名 _x を宣言する形で、診断は名前の右にある型(3:7)を指す:

  $ cat > effpos3.kel <<'KEL'
  > effect Log = {
  >   log: (String) => Unit,
  >   _x: () => Unit
  > }
  > KEL
  $ diktor --type-check effpos3.kel
  ! effpos3.kel:3:7: 型エラー: 操作名 _x は英小文字で始めてください(handle の節が操作名として読めません)
  [1]

effpos4 は同じ effect の中で操作名 log を 2 度宣言する形で、診断は 2 度目の宣言の型(4:8)を指す:

  $ cat > effpos4.kel <<'KEL'
  > effect Log = {
  >   log: (String) => Unit,
  >   flush: () => Unit,
  >   log: () => Unit
  > }
  > KEL
  $ diktor --type-check effpos4.kel
  ! effpos4.kel:4:8: 型エラー: 操作 log が二重に宣言されています
  [1]

effpos5 は effect に型パラメータを書いた形で、この診断は操作ではなく宣言全体の誤りなので、
宣言の先頭(1:1)を指す:

  $ cat > effpos5.kel <<'KEL'
  > effect Log[A] = {
  >   log: (A) => Unit
  > }
  > KEL
  $ diktor --type-check effpos5.kel
  ! effpos5.kel:1:1: 型エラー: effect 宣言に型パラメータは書けません(sample.kel §9)
  [1]

clspos は type class のメソッド h の型が矢印でない形で、診断はその型(3:10)を指す。
clspos2 はメソッド f を 2 度宣言する形で、診断は 2 度目の宣言の型(4:10)を指す:

  $ cat > clspos.kel <<'KEL'
  > type class C[A] {
  >   val g: (A) => Int32
  >   val h: A
  > }
  > KEL
  $ diktor --type-check --no-prelude clspos.kel
  ! clspos.kel:3:10: 型エラー: メソッド h の型は矢印型でなければなりません
  [1]
  $ cat > clspos2.kel <<'KEL'
  > type class C[A] {
  >   val g: (A) => Int32
  >   val f: (A) => Int32
  >   val f: (A) => String
  > }
  > KEL
  $ diktor --type-check --no-prelude clspos2.kel
  ! clspos2.kel:4:10: 型エラー: メソッド f が二重に宣言されています
  [1]
