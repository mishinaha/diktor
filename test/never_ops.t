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

判定は型エイリアスを展開した後の型で行う。perform の側(式の型)も節の側(resume の拒否)も同じ:

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
  $ cat > aliasresume.kel <<'EOF'
  > type Boom = Never
  > effect Fail = { throw: (String) => Boom }
  > let r = { perform throw("x"); 1 } handle { case throw(e) => resume(???) }
  > EOF
  $ diktor aliasresume.kel
  ! aliasresume.kel:3:61: 型エラー: 再開しない操作 throw の節には resume を書けません(操作の返り値の型が Never です)
  [1]

従来の書き方 perform op(..) match {} は、照合対象の型が決まらないので網羅漏れの警告になる
(match {} を外した nevertype の形では警告は出ない。動作は変わらない):

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

節の本体の中の別のハンドラの操作節では、その節の resume を書ける。再開するハンドラの
下で起きた再開しない操作は、そのハンドラを越えて外側に届き、越えられたハンドラの
cancel 節が節の本体より先に走る:

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
  > let r2 = (({ let a = perform ask(); if a > 5 then perform throw("big") else a }) handle {
  >   case ask() => resume(9)
  >   case cancel => echoln("cancel ask")
  > }) handle {
  >   case throw(e) => { echoln("outer catch " + e); 0 }
  > }
  > echoln(show(r2))
  > EOF
  $ diktor nested.kel
  nested 11
  11
  cancel ask
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

節のガードと絞り込みは再開する操作と同じに働く。ガードは継続を捨てる前に評価する
(偽のガードの出力が、内側の cancel 節の出力より先に出る):

  $ cat > guard.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Res = { use: () => Unit }
  > let r = ({ perform use(); perform throw("other") }) handle {
  >   case use() => resume()
  >   case cancel => echoln("cancel res")
  > } handle {
  >   case throw(e) if { echoln("guard " + e); e == "retry" } => 7
  >   case throw("other") => { echoln("literal other"); 8 }
  >   case throw(e) => 0
  > }
  > echoln(show(r))
  > EOF
  $ diktor guard.kel
  guard other
  cancel res
  literal other
  8

巻き戻しの順序。処理系は節の本体を評価する前に中断していた計算を破棄するので、
内側のハンドラの cancel 節が節の本体より先に走る:

  $ cat > order.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Res = { use: (String) => Unit }
  > let with_res[A, E](name: String, body: () => A @ {Res, Console extends E}): A @ {Console extends E} = {
  >   echoln("open " + name)
  >   body() handle {
  >     case use(s)    => resume(echoln(name + " uses " + s))
  >     case return(x) => { echoln("close " + name); x }
  >     case cancel    => echoln("cancel " + name)
  >   }
  > }
  > let r = {
  >   with _ = with_res("outer")
  >   with _ = with_res("inner")
  >   perform throw("abort")
  >   0
  > } handle {
  >   case throw(e) => { echoln("catch " + e); 0 - 1 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor order.kel
  open outer
  open inner
  cancel inner
  cancel outer
  catch abort
  -1

節の本体はハンドラの外側で評価する。節の本体が実行時エラーで脱出しても、
そのハンドラ自身の cancel 節は走らない(外側のハンドラの cancel 節は走る):

  $ cat > clauseerror.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Res = { use: (String) => Unit }
  > let with_res[A, E](name: String, body: () => A @ {Res, Console extends E}): A @ {Console extends E} = {
  >   echoln("open " + name)
  >   body() handle {
  >     case use(s)    => resume(echoln(name + " uses " + s))
  >     case return(x) => { echoln("close " + name); x }
  >     case cancel    => echoln("cancel " + name)
  >   }
  > }
  > let r = {
  >   with _ = with_res("outer")
  >   let v = {
  >     with _ = with_res("inner")
  >     perform throw("boom")
  >     1
  >   } handle {
  >     case throw(e) => { echoln("catch " + e); __panic("in clause") }
  >     case cancel => echoln("cancel catcher")
  >   }
  >   v
  > }
  > echoln("unreachable")
  > EOF
  $ diktor clauseerror.kel
  open outer
  open inner
  cancel inner
  catch boom
  cancel outer
  実行時エラー: panic: in clause
  [3]

節の本体で同じ操作を起こすと外側のハンドラに届く(再送出)。再送出するハンドラ自身の
cancel 節は走らず、その外側で巻き戻されるハンドラ(oops)の cancel 節は走る:

  $ cat > rethrow.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Other = { oops: (Int32) => Never }
  > let inner(): Int32 @ {Fail, Other} = { perform throw("x"); 1 }
  > let mid(): Int32 @ {Fail, Other, Console} = inner() handle {
  >   case throw(e) => if e == "x" then perform throw("re:" + e) else 2
  >   case cancel => echoln("cancel mid")
  > }
  > let r = (mid() handle { case oops(n) => n case cancel => echoln("cancel oops") }) handle {
  >   case throw(e) => { echoln("outer got " + e); 0 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor rethrow.kel
  cancel oops
  outer got re:x
  0

再開する操作の節から再開しない操作を起こすこともできる。再開しない操作のハンドラが先に
継続を捨てるので、内側の資源の cancel 節と、再開する操作のハンドラ自身の cancel 節
(外側から巻き戻されるので走る)が、再開しない操作の節の本体より先に走る:

  $ cat > fromclause.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Ask = { ask: () => Int32 }
  > effect Res = { use: () => Unit }
  > let r = {
  >   let v = ({ perform use(); perform ask() + 1 }) handle {
  >     case use() => resume()
  >     case return(x) => { echoln("close res"); x }
  >     case cancel => echoln("cancel res")
  >   }
  >   v
  > } handle {
  >   case ask() => { echoln("ask clause throws"); perform throw("from clause") }
  >   case cancel => echoln("cancel ask")
  > } handle {
  >   case throw(e) => { echoln("caught " + e); 0 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor fromclause.kel
  ask clause throws
  cancel res
  cancel ask
  caught from clause
  0

cancel 節から再開しない操作を起こすと、その操作のハンドラが行う破棄は cancel 節の
打ち切りで止まる(§13.6)。ハンドラは節の本体を評価せず(caught の行が出ない)、
巻き戻しはそのまま続く。巻き戻しが実行時エラーによるものならプログラムはそれで終わり、
内側のハンドラの破棄によるものなら本体が続き、その値がハンドラ式の値になる:

  $ cat > cancelperform.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Res = { use: () => Unit }
  > let r = {
  >   let v = { perform use(); 1 / 0 } handle {
  >     case use() => resume()
  >     case cancel => { echoln("cancel res"); perform throw("from cancel") }
  >   }
  >   v
  > } handle {
  >   case throw(e) => { echoln("caught " + e); 0 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor cancelperform.kel
  cancel res
  cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました
  実行時エラー: ゼロ除算です
  [3]
  $ cat > cancelnormal.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Stop = { stop: () => Never }
  > effect Res = { use: () => Unit }
  > let r = {
  >   let v = ({ perform use(); perform stop(); 1 }) handle {
  >     case use() => resume()
  >     case cancel => { echoln("cancel res"); perform throw("from cancel") }
  >   } handle {
  >     case stop() => { echoln("stop clause"); 2 }
  >   }
  >   echoln("after inner " + show(v))
  >   v + 10
  > } handle {
  >   case throw(e) => { echoln("caught " + e); 0 }
  >   case return(x) => { echoln("return " + show(x)); x }
  > }
  > echoln(show(r))
  > EOF
  $ diktor cancelnormal.kel
  cancel res
  cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました
  stop clause
  after inner 2
  return 12
  12

トップレベルに残せない規則(§13.7)は再開しない操作にも同じに働く:

  $ cat > toplevel.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let x = perform throw("top")
  > EOF
  $ diktor toplevel.kel
  ! toplevel.kel:2:9: 型エラー: エフェクト Fail をここでは実行できません(ラベル Fail がありません(行は閉じています))
  [1]
