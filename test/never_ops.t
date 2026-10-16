再開しない操作(仕様 §13.1)。返り値の型が Never の操作は再開できないので、
perform の式は穴と同じく周囲が要求する型になり(§13.3)、その操作の節には resume を
書けず(§13.5)、処理系は節の本体を評価する前に中断していた計算を破棄する(§13.6)。

perform の式が要求される型になる。match の腕にそのまま置ける:

  $ cat > nevertype.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let get(o: Option[Int32]): Int32 @ Fail = o match {
  >   case Some(v) => v
  >   case None => perform throw("none")
  > }
  > EOF
  $ diktor --type-check nevertype.kel
  get : (Option[Int32]) => Int32 @ {Fail}

型変数の返り値型を持つ関数にすると、呼ぶ側の型に合わせて使える(失敗の補助関数の形):

  $ cat > generic.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let abort[A](m: String): A @ Fail = perform throw(m)
  > let n: Int32 = abort("x") handle { case throw(e) => 42 }
  > echoln(show(n))
  > let s: String = abort("y") handle { case throw(e) => "s:" + e }
  > echoln(s)
  > EOF
  $ diktor --type-check generic.kel
  abort : (String) => A @ {Fail}
  n : Int32
  _ : {}
  s : String
  _ : {}
  $ diktor generic.kel
  42
  s:y

判定は型エイリアスを展開した後の型で行う:

  $ cat > alias.kel <<'EOF'
  > type Boom = Never
  > effect Fail = { throw: (String) => Boom }
  > let get(o: Option[Int32]): Int32 @ Fail = o match {
  >   case Some(v) => v
  >   case None => perform throw("none")
  > }
  > echoln(show(get(None) handle { case throw(e) => { echoln("caught " + e); 0 - 1 } }))
  > EOF
  $ diktor alias.kel
  caught none
  -1

従来の書き方 perform op(..) match {} は、照合対象の型が決まらないので網羅漏れの警告になる(動作は変わらない):

  $ cat > absurd.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let get(o: Option[Int32]): Int32 @ Fail = o match {
  >   case Some(v) => v
  >   case None => perform throw("none") match {}
  > }
  > let r = get(Some(3)) handle { case throw(e) => 0 - 1 }
  > echoln(show(r))
  > let r2 = get(None) handle { case throw(e) => 0 - 1 }
  > echoln(show(r2))
  > EOF
  $ diktor absurd.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  3
  -1

再開しない操作の節に resume は書けない。閉包の本体に書いても同じ診断になる:

  $ cat > resumedirect.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let r = { perform throw("x"); 1 } handle { case throw(e) => resume(???) }
  > EOF
  $ diktor resumedirect.kel
  ! resumedirect.kel:2:61: 型エラー: 再開しない操作 throw の節には resume を書けません(操作の返り値の型が Never です)
  [1]
  $ cat > resumelambda.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let r = { perform throw("x"); 1 } handle { case throw(e) => { let f = fn() => resume(???); f() } }
  > EOF
  $ diktor resumelambda.kel
  ! resumelambda.kel:2:79: 型エラー: 再開しない操作 throw の節には resume を書けません(操作の返り値の型が Never です)
  [1]

節の本体の中の別のハンドラの操作節では、その節の resume を書ける。外側の再開する
ハンドラの下で起きた再開しない操作も、外側へ届く:

  $ cat > nested.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Ask = { ask: () => Int32 }
  > let r = { perform throw("x"); 1 } handle {
  >   case throw(e) => {
  >     let a = (perform ask() + 1) handle { case ask() => resume(10) }
  >     echoln("nested " + show(a))
  >     a
  >   }
  > }
  > echoln(show(r))
  > let r2 = ({ let a = perform ask(); if a > 5 then perform throw("big") else a }) handle {
  >   case throw(e) => { echoln("outer catch " + e); 0 }
  > } handle {
  >   case ask() => resume(9)
  > }
  > echoln(show(r2))
  > EOF
  $ diktor nested.kel
  nested 11
  11
  outer catch big
  0

同じエフェクトに再開する操作と再開しない操作を混ぜられる。判定は操作ごとである:

  $ cat > mixed.kel <<'EOF'
  > effect Parser = { next: () => Int32, fail: (String) => Never }
  > let parse(): Int32 @ Parser = {
  >   let a = perform next()
  >   if a < 0 then perform fail("negative") else a * 2
  > }
  > let r1 = parse() handle {
  >   case next() => resume(21)
  >   case fail(m) => { echoln("fail " + m); 0 - 1 }
  >   case return(x) => x
  > }
  > echoln(show(r1))
  > let r2 = parse() handle {
  >   case next() => resume(0 - 1)
  >   case fail(m) => { echoln("fail " + m); 0 - 1 }
  >   case return(x) => x
  > }
  > echoln(show(r2))
  > EOF
  $ diktor mixed.kel
  42
  fail negative
  -1

節のガードと絞り込みは再開する操作と同じに働く:

  $ cat > guard.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let r = { perform throw("retry"); 1 } handle {
  >   case throw(e) if e == "retry" => { echoln("guarded"); 7 }
  >   case throw(e) => { echoln("other " + e); 0 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor guard.kel
  guarded
  7

トップレベルに残せない規則(§13.7)は再開しない操作にも同じに働く:

  $ cat > toplevel.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let x = perform throw("top")
  > EOF
  $ diktor toplevel.kel
  ! toplevel.kel:2:9: 型エラー: エフェクト Fail をここでは実行できません(ラベル Fail がありません(行は閉じています))
  [1]
