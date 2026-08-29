extern C の既知名と型契約(計画 260829-4 H9 / H14)。

既知名(sin/cos/sqrt/exp/log)は引数型と返り値型を契約と照合する。
かつては嘘の型が通り、呼ぶと原因の見えない実行時エラーになった:

  $ printf 'extern "C" let sin(x: String): String\n' > cbad.kel
  $ diktor --type-check cbad.kel
  ! 型エラー: extern "C" の既知名 sin の型は (Float64) => Float64 でなければなりません
  [1]

契約どおりの宣言は通り、実装に届く:

  $ cat > cok.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > echoln(show(sqrt(9.0)))
  > KEL
  $ diktor cok.kel
  3.0

行は照合しない(@ Blocking を付けるかはバインディング作者の判断、
sample.kel:551):

  $ printf 'extern "C" let sin(x: Float64): Float64 @ Blocking\n' > cblk1.kel
  $ diktor --type-check cblk1.kel
  sin : (Float64) => Float64 @ {Blocking extends R1}

未知名は従来どおり受理(宣言は通り、呼ぶと落ちる。本物の C FFI は
検証不能な宣言なのでこの線引きは意図的):

  $ cat > cunk.kel <<'KEL'
  > extern "C" let nosuch(x: Float64): Float64
  > echoln(show(nosuch(1.0)))
  > KEL
  $ diktor cunk.kel
  実行時エラー: 未実装のプリミティブ: nosuch
  [3]

仕様の形(sample.kel:549 相当)が通り続けること:

  $ printf 'newtype Stmt = ???\nextern "C" let sqlite_step(s: Stmt): Int32 @ Blocking\n' > cblk2.kel
  $ diktor --type-check cblk2.kel
  sqlite_step : (Stmt) => Int32 @ {Blocking extends R1}
