標準環境の名前は、トップレベルの宣言に使えない(LangSpec §16.1、§12.2)。

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
