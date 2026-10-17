handle の 1 つの節だけで決まる誤りは、その節の位置で報告する。
節の頭の誤り(引数の個数、ラベル、所属、形、修飾)は節のパターンを、
return 節と cancel 節のガードの誤りはガードの式を指す。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

操作節の引数が多すぎる形は、その節のパターン(4:8)を指す。
handle 式の先頭(3:9)ではない:

  $ cat > arity2.kel <<'KEL'
  > newtype Box = MkBox(Int32)
  > effect Ask = { ask: (Box) => Int32 }
  > let r = perform ask(MkBox(3)) handle {
  >   case ask(MkBox(n), m) => resume(n)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check arity2.kel
  ! arity2.kel:4:8: 型エラー: 操作 ask は 1 引数です(節には 2 個書かれています)
  [1]

引数が足りない形と、同じ操作の 2 つ目の節だけが誤っている形も、その節を指す:

  $ cat > arity0.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case return(x) => x
  >     case ask() => resume(0)
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check arity0.kel
  ! arity0.kel:5:10: 型エラー: 操作 ask は 1 引数です(節には 0 個書かれています)
  [1]

  $ cat > aritysecond.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case ask(1) => resume(0)
  >     case ask(n, m) => resume(n)
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check aritysecond.kel
  ! aritysecond.kel:5:10: 型エラー: 操作 ask は 1 引数です(節には 2 個書かれています)
  [1]

操作節の引数にラベルを書いた形も、その節のパターンを指す:

  $ cat > label.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case return(v) => v
  >     case ask(x = a) => resume(a)
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check label.kel
  ! label.kel:5:10: 型エラー: 操作節の引数にラベルは書けません
  [1]

節の本体の中の handle の誤りは、内側の節(6:14)を指す:

  $ cat > inner.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case ask(n) =>
  >       resume(perform ask(n) handle {
  >         case ask() => resume(0)
  >       })
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check inner.kel
  ! inner.kel:6:14: 型エラー: 操作 ask は 1 引数です(節には 0 個書かれています)
  [1]

節の頭の形の誤りと 2 つ目の return 節も、その節を指す:

  $ cat > retshape.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case ask(n) => resume(n)
  >     case return(a, b) => a
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check retshape.kel
  ! retshape.kel:5:10: 型エラー: return 節は case return(x) の形で書いてください
  [1]

  $ cat > badhead.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case ask(n) => resume(n)
  >     case 3 => 4
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check badhead.kel
  ! badhead.kel:5:10: 型エラー: handle の節は操作名 / return / cancel で始めてください
  [1]

  $ cat > tworet.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case ask(n) => resume(n)
  >     case return(v) => v
  >     case return(w) => w
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check tworet.kel
  ! tworet.kel:6:10: 型エラー: return 節は1つまでです
  [1]

2 つ目の cancel 節も、2 つ目の節(6:10)を指す:

  $ cat > twocancel.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case ask(n) => resume(n)
  >     case cancel => ()
  >     case cancel => ()
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check twocancel.kel
  ! twocancel.kel:6:10: 型エラー: cancel 節は1つまでです
  [1]

  $ cat > cancelarg.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case ask(n) => resume(n)
  >     case cancel(x) => ()
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check cancelarg.kel
  ! cancelarg.kel:5:10: 未実装: cancel(reason)(v0 は case cancel のみ)
  [4]

修飾した操作節が決めた対象に属さない操作の節は、その節を指す:

  $ cat > notbelong.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > effect Tell = { tell: (Int32) => Unit }
  > let r =
  >   perform Ask.ask(1) handle {
  >     case Ask.ask(n) => resume(n)
  >     case tell(x) => resume(())
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check notbelong.kel
  ! notbelong.kel:6:10: 型エラー: 操作 tell はエフェクト Ask に属しません
  [1]

return 節のガードは、ガードの式(5:23)を指す:

  $ cat > retguard.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case ask(n) => resume(n)
  >     case return(v) if true => v
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check retguard.kel
  ! retguard.kel:5:23: 型エラー: return 節にガードは書けません
  [1]

対象エフェクトの決定の誤りは、特定の 1 節に帰せないので、handle 式の位置(3:3)を指す:

  $ cat > missing.kel <<'KEL'
  > effect Two = { one: () => Int32, two: () => Int32 }
  > let r =
  >   perform one() handle {
  >     case return(v) => v
  >     case one() => resume(1)
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check missing.kel
  ! missing.kel:3:3: 型エラー: ハンドラが操作を網羅していません: Two の two が漏れています
  [1]

  $ cat > unknownqual.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r =
  >   perform ask(1) handle {
  >     case return(v) => v
  >     case Nope.ask(n) => resume(n)
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check unknownqual.kel
  ! unknownqual.kel:3:3: 型エラー: 未知のエフェクト: Nope
  [1]

操作節が 1 つも無い誤りも、節の不在から決まるので、handle 式の位置(2:3)を指す:

  $ cat > noop.kel <<'KEL'
  > let r =
  >   1 handle {
  >     case return(v) => v
  >   }
  > echoln(show(r))
  > KEL
  $ diktor --type-check noop.kel
  ! noop.kel:2:3: 型エラー: handle には少なくとも1つの操作節が必要です
  [1]
