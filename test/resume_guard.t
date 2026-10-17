操作節の本体の中に書いた match の節のガードは本体の一部なので、再開する
操作の節では resume を書ける。再開した計算の値をガードで使える:

  $ cat > matchguard.kel <<'KEL'
  > effect Test = { test: () => Int32 }
  > let r = { let a = perform test(); a + 1 } handle {
  >   case test() => 0 match { case _ if resume(10) > 5 => 100 case _ => 0 }
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check matchguard.kel
  r : Int32
  _ : {}
  $ diktor matchguard.kel
  100

条件式の条件も本体の一部なので、resume を書ける:

  $ cat > ifcond.kel <<'KEL'
  > effect Test = { test: () => Boolean }
  > let r = perform test() handle { case test() => if resume(true) then true else false }
  > echoln(show(r))
  > KEL
  $ diktor ifcond.kel
  true

本体の中の 2 つのガードで resume を呼ぶ形は型検査を通り、2 回目の再開が
実行時エラーになる:

  $ cat > matchguard2.kel <<'KEL'
  > effect Test = { test: () => Boolean }
  > let r = perform test() handle {
  >   case test() => 1 match { case _ if resume(false) => true case _ if resume(true) => true case _ => false }
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check matchguard2.kel
  r : Boolean
  _ : {}
  $ diktor matchguard2.kel
  実行時エラー: resume は高々1回しか呼べません(アフィン)
  [3]

節の中に書いた入れ子の handle の操作節のガードには、外側の節の resume を
書けない:

  $ cat > innerguard.kel <<'KEL'
  > effect Test = { test: () => Boolean }
  > effect Ask = { ask: () => Int32 }
  > let r = perform test() handle {
  >   case test() => perform Ask.ask() handle {
  >     case ask() if resume(true) => false
  >     case ask() => true
  >   }
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check innerguard.kel
  ! innerguard.kel:5:19: 型エラー: 操作節のガードには resume を書けません(ガードは節が選ばれる前に評価されるので、継続を再開できません)
  [1]

操作節のガードの中に書いた別の handle の操作節の resume は、内側の節の
継続を再開するものなので、書ける:

  $ cat > guardhandle.kel <<'KEL'
  > effect Test = { test: () => Boolean }
  > effect Ask = { ask: () => Int32 }
  > let r = perform test() handle {
  >   case test() if (perform Ask.ask() handle { case ask() => resume(1) }) > 0 => resume(true)
  >   case test() => false
  > }
  > echoln(show(r))
  > KEL
  $ diktor guardhandle.kel
  true
