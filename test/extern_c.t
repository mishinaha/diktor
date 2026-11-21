extern "C" の既知名と、そのシグネチャの照合(第6章 §6.2b)のテストである。

既知名(sin、cos、sqrt、exp、log)の宣言は、引数の型と返り値の型を決まったシグネチャと照合する。
照合しないと、偽った型の宣言が型検査に通り、呼び出したときに原因の分かりにくい実行時エラーになる:

  $ printf 'extern "C" let sin(x: String): String\n' > cbad.kel
  $ diktor --type-check cbad.kel
  ! cbad.kel:1:1: 型エラー: extern "C" の既知名 sin の型は (Float64) => Float64 でなければなりません
  [1]

シグネチャどおりの宣言は型検査に通り、実装を呼び出せる:

  $ cat > cok.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64
  > echoln(show(sqrt(9.0)))
  > KEL
  $ diktor cok.kel
  3.0

@ Blocking を明示した宣言も照合に通る。エフェクト行は照合しない。どの行を書くかは、
バインディングの作者が決めるからである(sample.kel:798-799):

  $ printf 'extern "C" let sin(x: Float64): Float64 @ Blocking\n' > cblk1.kel
  $ diktor --type-check cblk1.kel
  sin : (Float64) => Float64 @ {Blocking}
  $ printf 'extern "C" let sin(x: Float64): Float64 @ Console\n' > cblk3.kel
  $ diktor --type-check cblk3.kel
  sin : (Float64) => Float64 @ {Console}

既知名でない名前の宣言は受理し、呼び出すと実行時エラーになる(LangSpec §17)。
C の関数の宣言は一般には検証できないので、照合するのは既知名だけである:

  $ cat > cunk.kel <<'KEL'
  > extern "C" let nosuch(x: Float64): Float64
  > echoln(show(nosuch(1.0)))
  > KEL
  $ diktor cunk.kel
  実行時エラー: 未実装のプリミティブ: nosuch
  [3]

sample.kel:796 と同じ形の宣言は、型検査に通る:

  $ printf 'newtype Stmt\nextern "C" let sqlite_step(s: Stmt): Int32 @ Blocking\n' > cblk2.kel
  $ diktor --type-check cblk2.kel
  sqlite_step : (Stmt) => Int32 @ {Blocking}

module の中の extern でも、実装を探すキーと、プレリュードの保護を調べる登録表のキーは、修飾しない実装名である
(第6章 §6.2)。修飾名をキーにすると、module の中で宣言すればプレリュードの保護を回避できてしまう:

  $ printf 'module M { extern "prim" let __int32_add(x: String, y: String): String }\n' > mext.kel
  $ diktor --type-check mext.kel
  ! mext.kel:1:12: 型エラー: プレリュードの extern __int32_add は再宣言できません
  [1]

module の中で宣言した既知名の外部関数も、実装を呼び出せる。実装は修飾しない実装名で
探すので、Math.sqrt は sqrt の実装を呼び出す:

  $ cat > mffi.kel <<'KEL'
  > module Math { pub extern "C" let sqrt(x: Float64): Float64 }
  > echoln(show(Math.sqrt(9.0)))
  > KEL
  $ diktor mffi.kel
  3.0

シグネチャの照合は、module の中の宣言にも適用される:

  $ printf 'module M2 { extern "C" let sin(x: String): String }\n' > mbad.kel
  $ diktor --type-check mbad.kel
  ! mbad.kel:1:13: 型エラー: extern "C" の既知名 sin の型は (Float64) => Float64 でなければなりません
  [1]

別々の module は、同じ C のシンボルをそれぞれの名前で束縛できる。
二重宣言の検査は、Keleut 側の修飾名で行うからである:

  $ cat > mm2.kel <<'KEL'
  > module Fast { pub extern "C" let sqrt(x: Float64): Float64 }
  > module Precise { pub extern "C" let sqrt(x: Float64): Float64 }
  > echoln(show(Fast.sqrt(4.0)))
  > echoln(show(Precise.sqrt(9.0)))
  > KEL
  $ diktor mm2.kel
  2.0
  3.0

同じ修飾名の二重宣言は拒否する:

  $ printf 'extern "C" let sqrt(x: Float64): Float64\nextern "C" let sqrt(x: Float64): Float64\n' > dd.kel
  $ diktor --type-check dd.kel
  sqrt : (Float64) => Float64 @ {Blocking}
  ! dd.kel:2:1: 型エラー: extern sqrt が二重に宣言されています
  [1]

未実装のメッセージは、実装を探すのに使った実装名が修飾名と違うとき、両方の名前を示す:

  $ cat > mun.kel <<'KEL'
  > module M { pub extern "prim" let __no_such(x: Int32): Int32 }
  > echoln(show(M.__no_such(1)))
  > KEL
  $ diktor mun.kel
  実行時エラー: 未実装のプリミティブ: M.__no_such(実装名 __no_such が見つかりません)
  [3]

pinned は行から Blocking を取り除く(LangSpec §17)。Blocking は操作を持たないラベルなので、
取り除くのは型の上だけの操作で、実行時の pinned は本体を 1 回呼び出すだけである。Diktor はタスクを 1 つしか持たず、
キャンセルポイントも持たないので、Blocking について守る 2 つの規則(並列度を減らさないことと、
キャンセルポイントにならないこと)をこの実装が満たす。@ Blocking の関数は、Blocking を取り除かずにトップレベルから呼び出すこともできる。
取り除かないまま、閉じた行や注釈で固定した行に持ち込むと拒否される例は、test/blocking_top.t の
bpure と bann にある:

  $ cat > pin.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > echoln(show(pinned(fn() => sqrt(16.0))))
  > KEL
  $ diktor pin.kel
  4.0
