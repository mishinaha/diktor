標準環境の型、エフェクト、クラスの名前と、標準環境のインスタンスの組は、トップレベルの
同じ種別の宣言に使えない(LangSpec §16.1、§12.2)。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

型エイリアス、newtype、effect、type class、インスタンスの 5 種類がどれも落ちる:

  $ printf 'type Unit = {}\n' > s1.kel
  $ diktor --type-check s1.kel
  ! s1.kel:1:1: 型エラー: 標準環境の型エイリアス Unit は再宣言できません
  [1]
  $ printf 'newtype Option[A] = None | Some(A)\n' > s2.kel
  $ diktor --type-check s2.kel
  ! s2.kel:1:1: 型エラー: 標準環境の newtype Option は再宣言できません
  [1]
  $ printf 'effect Console = { write: (String) => Unit }\n' > s3.kel
  $ diktor --type-check s3.kel
  ! s3.kel:1:1: 型エラー: 標準環境の effect Console は再宣言できません
  [1]
  $ printf 'type class Add[A] { val add: (A, A) => A }\n' > s4.kel
  $ diktor --type-check s4.kel
  ! s4.kel:1:1: 型エラー: 標準環境の type class Add は再宣言できません
  [1]
  $ printf 'type instance Add[Int32] { let add(x, y) = __int32_sub(x, y) }\n' > s5.kel
  $ diktor --type-check s5.kel
  ! s5.kel:1:1: 型エラー: 標準環境のインスタンス Add[Int32] は再宣言できません
  [1]

組み込みのラベル(プレリュードでなく処理系が登録するもの)も同じ:

  $ printf 'effect Blocking = {}\n' > s6.kel
  $ diktor --type-check s6.kel
  ! s6.kel:1:1: 型エラー: 標準環境の effect Blocking は再宣言できません
  [1]

標準環境のクラスに、新しい型のインスタンスを足すことはできる:

  $ cat > s7.kel <<'KEL'
  > newtype Meters(Int32)
  > type instance Add[Meters] {
  >   let add(a, b) = (a, b) match { case (Meters(x), Meters(y)) => Meters(x + y) }
  > }
  > echoln((Meters(3) + Meters(4)) match { case Meters(v) => show(v) })
  > KEL
  $ diktor s7.kel
  7

モジュールの中の名前は修飾されるので、標準環境の名前と同じ綴りでも宣言できる:

  $ cat > s8.kel <<'KEL'
  > module M { pub newtype Option = Opt(Int32) }
  > let v: M.Option = Opt(1)
  > echoln("ok")
  > KEL
  $ diktor s8.kel
  ok

標準環境と同じ名前のクラスの宣言は、メソッドの型を照合せず、名前で拒否する。sc/lib/s.kel は
import されたファイル(起点でない単位)で、show の型が標準環境と違う Show を宣言する。
p10.kel は --prelude で差し替えたプレリュードで、標準環境と同じ型の Show を宣言する。
どちらも同じ文面で落ちる:

  $ mkdir -p sc/lib
  $ printf 'pub type class Show[A] { val show: (A) => Boolean }\n' > sc/lib/s.kel
  $ printf 'from "./lib/s" import Show\necholn("x")\n' > sc/s9.kel
  $ (cd sc && diktor --type-check s9.kel)
  ! lib/s.kel:1:1: 型エラー: 標準環境の type class Show は再宣言できません
  [1]
  $ printf 'type class Show[A] { val show: (A) => String }\n' > p10.kel
  $ printf 'echoln("x")\n' > s10.kel
  $ diktor --prelude p10.kel --type-check s10.kel
  ! p10.kel:1:1: 型エラー: 標準環境の type class Show は再宣言できません
  [1]
