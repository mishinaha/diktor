resume を書けない位置(仕様 §13.5)。操作節のガード、return 節、cancel 節に書いた
resume は型検査で拒否し、診断は最も内側の位置を名指しする。
操作節の外に書いた resume は、操作節の中でだけ使えることを述べる。
再開しない操作の節の本体に書いた resume の診断は never_ops.t で見張る。

操作節のガード。再開する操作の節でも再開しない操作の節でも同じ診断になる:

  $ cat > guard.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = perform ask() handle { case ask() if resume(1) > 0 => resume(1)  case ask() => resume(2) }
  > KEL
  $ diktor --type-check guard.kel
  ! guard.kel:2:46: 型エラー: 操作節のガードには resume を書けません(ガードは節が選ばれる前に評価されるので、継続を再開できません)
  [1]
  $ cat > neverguard.kel <<'KEL'
  > effect Fail = { throw: (String) => Never }
  > let r = { perform throw("x"); 1 } handle { case throw(e) if resume(???) => 0  case throw(e) => 1 }
  > KEL
  $ diktor --type-check neverguard.kel
  ! neverguard.kel:2:61: 型エラー: 操作節のガードには resume を書けません(ガードは節が選ばれる前に評価されるので、継続を再開できません)
  [1]

自分のハンドラの return 節と cancel 節:

  $ cat > ownreturn.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = perform ask() handle { case ask() => resume(1)  case return(x) => resume(x) }
  > KEL
  $ diktor --type-check ownreturn.kel
  ! ownreturn.kel:2:75: 型エラー: return 節には resume を書けません(再開する継続がありません)
  [1]
  $ cat > owncancel.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = perform ask() handle { case ask() => resume(1)  case cancel => { resume(1); () } }
  > KEL
  $ diktor --type-check owncancel.kel
  ! owncancel.kel:2:74: 型エラー: cancel 節には resume を書けません(再開する継続がありません)
  [1]

操作節の中に書いた入れ子の handle の return 節と cancel 節では、外側の節が再開する
操作の節でも再開しない操作の節でも、内側の節の診断になる:

  $ cat > nestedreturn.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > effect Ask2 = { ask2: () => Int32 }
  > let r = perform ask() handle { case ask() => 2 handle { case ask2() => resume(1)  case return(x) => resume(x) } }
  > KEL
  $ diktor --type-check nestedreturn.kel
  ! nestedreturn.kel:3:101: 型エラー: return 節には resume を書けません(再開する継続がありません)
  [1]
  $ cat > nevernestedcancel.kel <<'KEL'
  > effect Fail = { throw: (String) => Never }
  > effect Ask = { ask: () => Int32 }
  > let r = { perform throw("x"); 1 } handle { case throw(e) => 2 handle { case ask() => resume(1)  case cancel => { resume(???); () } } }
  > KEL
  $ diktor --type-check nevernestedcancel.kel
  ! nevernestedcancel.kel:3:114: 型エラー: cancel 節には resume を書けません(再開する継続がありません)
  [1]

操作節の外:

  $ cat > outside.kel <<'KEL'
  > let bad = resume(1)
  > KEL
  $ diktor --type-check outside.kel
  ! outside.kel:1:11: 型エラー: resume は操作節の中でのみ使えます
  [1]
