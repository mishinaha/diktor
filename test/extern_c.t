extern C の既知名と型契約(計画 260829-4 H9 / H14)。

既知名(sin/cos/sqrt/exp/log)は引数型と返り値型を契約と照合する。
かつては嘘の型が通り、呼ぶと原因の見えない実行時エラーになった:

  $ printf 'extern "C" let sin(x: String): String\n' > cbad.kel
  $ diktor --type-check cbad.kel
  ! cbad.kel:1:1: 型エラー: extern "C" の既知名 sin の型は (Float64) => Float64 でなければなりません
  [1]

契約どおりの宣言は通り、実装に届く:

  $ cat > cok.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > echoln(show(sqrt(9.0)))
  > KEL
  $ diktor cok.kel
  3.0

行は照合しない(@ Blocking を付けるかはバインディング作者の判断、
sample.kel:794):

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

仕様の形(sample.kel:792 相当)が通り続けること:

  $ printf 'newtype Stmt = ???\nextern "C" let sqlite_step(s: Stmt): Int32 @ Blocking\n' > cblk2.kel
  $ diktor --type-check cblk2.kel
  sqlite_step : (Stmt) => Int32 @ {Blocking extends R1}

module 内の extern も、実装と登録簿の鍵は非修飾の実装名(H14。かつては
修飾名が鍵になり、プレリュード保護が module の中から迂回できた):

  $ printf 'module M { extern "prim" let __int32_add(x: String, y: String): String }\n' > mext.kel
  $ diktor --type-check mext.kel
  ! mext.kel:1:12: 型エラー: プレリュードの extern __int32_add は再宣言できません
  [1]

module に包んだ既知名 FFI は実装に届く(かつては Math.sqrt が実装表から
外れ、黙って未実装になった):

  $ cat > mffi.kel <<'KEL'
  > module Math { pub extern "C" let sqrt(x: Float64): Float64 }
  > echoln(show(Math.sqrt(9.0)))
  > KEL
  $ diktor mffi.kel
  3.0

型契約も module 越しに効く:

  $ printf 'module M2 { extern "C" let sin(x: String): String }\n' > mbad.kel
  $ diktor --type-check mbad.kel
  ! mbad.kel:1:13: 型エラー: extern "C" の既知名 sin の型は (Float64) => Float64 でなければなりません
  [1]

別々の module は同じ C シンボルをそれぞれの名前で束縛できる
(二重宣言の検査は Keleut 側の修飾名で行う。260829-5 検証修正):

  $ cat > mm2.kel <<'KEL'
  > module Fast { pub extern "C" let sqrt(x: Float64): Float64 }
  > module Precise { pub extern "C" let sqrt(x: Float64): Float64 }
  > echoln(show(Fast.sqrt(4.0)))
  > echoln(show(Precise.sqrt(9.0)))
  > KEL
  $ diktor mm2.kel
  2.0
  3.0

同じ修飾名の二重宣言は従来どおり拒否:

  $ printf 'extern "C" let sqrt(x: Float64): Float64\nextern "C" let sqrt(x: Float64): Float64\n' > dd.kel
  $ diktor --type-check dd.kel
  sqrt : (Float64) => Float64
  ! dd.kel:2:1: 型エラー: extern sqrt が二重に宣言されています
  [1]

未実装メッセージは、表を引いた実装名が修飾名と食い違うとき両方を見せる:

  $ cat > mun.kel <<'KEL'
  > module M { pub extern "prim" let __no_such(x: Int32): Int32 }
  > echoln(show(M.__no_such(1)))
  > KEL
  $ diktor mun.kel
  実行時エラー: 未実装のプリミティブ: M.__no_such(実装名 __no_such が見つかりません)
  [3]

pinned は Blocking を落とす(M16 / H11)。操作を持たないラベルを落とすのは
型の上の行為だけで、実行は恒等(v0 はタスク 1 つ・Async no-op なので、
仕様が Blocking に求める 2 契約を恒等が満たす)。落とさずにトップレベル
から呼ぶことも仕様 §12 の改訂(D88)で許された — 落とさずに閉じた行や
注釈で固定した行へ持ち込むと拒否される例は test/blocking_top.t の
bpure / bann にある:

  $ cat > pin.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > echoln(show(pinned(fn() => sqrt(16.0))))
  > KEL
  $ diktor pin.kel
  4.0
