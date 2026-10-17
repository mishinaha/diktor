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

判定は型エイリアスを展開した後の型で行う。perform の側(式の型)も節の側(resume の拒否と、
先に継続を捨てる順序)も同じ:

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
  $ cat > aliasorder.kel <<'EOF'
  > type Boom = Never
  > effect Fail = { throw: (String) => Boom }
  > effect Res = { use: () => Unit }
  > let r = ({ perform use(); perform throw("x") }) handle {
  >   case use() => resume()
  >   case cancel => echoln("cancel res")
  > } handle {
  >   case throw(e) => { echoln("caught " + e); 0 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor aliasorder.kel
  cancel res
  caught x
  0

absurd の get は、let で束縛した関数の本体で、再開しない操作の perform の結果を直接
match {} で照合する。この get の照合対象の型変数は Never に決まり(§11.2)、網羅漏れの警告は
出ない。absurdplain は get から match {} を外したもので、出力は absurd と同じである。
absurdann は照合対象を Never と注釈した局所の値束縛 z で受けてから照合し、get(None) は
absurd と同じく -1 を返す:

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
  3
  -1
  $ cat > absurdplain.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let get(o: Option[Int32]): Int32 @ Fail = o match {
  >   case Some(v) => v
  >   case None => perform throw("none")
  > }
  > let r = get(Some(3)) handle { case throw(e) => 0 - 1 }
  > echoln(show(r))
  > let r2 = get(None) handle { case throw(e) => 0 - 1 }
  > echoln(show(r2))
  > EOF
  $ diktor absurdplain.kel
  3
  -1
  $ cat > absurdann.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let get(o: Option[Int32]): Int32 @ Fail = o match {
  >   case Some(v) => v
  >   case None => { let z: Never = perform throw("none"); z match {} }
  > }
  > let r2 = get(None) handle { case throw(e) => 0 - 1 }
  > echoln(show(r2))
  > EOF
  $ diktor absurdann.kel
  -1

照合対象の型が網羅性を調べた時点で数値の述語を持たない未定の型変数のとき、節のない
match {} の警告は、その型がコンストラクタを持たない型と分かっていないことを言う文面になる。
absurdshow の h と k は、注釈のない引数を show に渡してから照合する。引数の型変数は Show の
制約が付き、束縛の型にも現れるので Never に決まらず、2 つとも新しい文面の警告になる。
--strict-exhaustive では終了コード 1 になる:

  $ cat > absurdshow.kel <<'EOF'
  > let h = fn(y) => { echoln(show(y)); y match {} }
  > let k(x) = { echoln(show(x)); x match {} }
  > echoln("ok")
  > EOF
  $ diktor absurdshow.kel
  ⚠ match が非網羅的です。照合対象の型は、網羅性を調べた時点で Never のようなコンストラクタを持たない型と分かっていません(節のない match {} が網羅的なのは、照合対象がそのような型のときだけです)
  ⚠ match が非網羅的です。照合対象の型は、網羅性を調べた時点で Never のようなコンストラクタを持たない型と分かっていません(節のない match {} が網羅的なのは、照合対象がそのような型のときだけです)
  ok
  $ diktor --strict-exhaustive absurdshow.kel
  ⚠ match が非網羅的です。照合対象の型は、網羅性を調べた時点で Never のようなコンストラクタを持たない型と分かっていません(節のない match {} が網羅的なのは、照合対象がそのような型のときだけです)
  ⚠ match が非網羅的です。照合対象の型は、網羅性を調べた時点で Never のようなコンストラクタを持たない型と分かっていません(節のない match {} が網羅的なのは、照合対象がそのような型のときだけです)
  [1]

absurdother の 3 つの match は従来の文面のままである。f は型パラメータ A の値を照合し、
照合対象の型は未定の型変数でない。g は数値のリテラルを照合し、照合対象の型変数は数値の
述語を持つ。k の match はガード付きの節を 1 つ持つので、節のない match でない:

  $ cat > absurdother.kel <<'EOF'
  > let f[A](x: A): Int32 = x match {}
  > let g(): Int32 = 1 match {}
  > let k(x, b: Boolean): Int32 = x match { case y if b => 1 }
  > echoln("ok")
  > EOF
  $ diktor absurdother.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  ⚠ match が非網羅的です。例えば _ が漏れています
  ⚠ match が非網羅的です。例えば _ が漏れています
  ok

neverclass は、Never にインスタンスを持つクラス Describe のメソッドの引数に、perform の式を
直接置く。perform の式の型は新しい型変数で、Describe の制約だけを持ち、f の型に現れないので、
曖昧な制約の型エラーになる。neverclasshelper は、返り値を注釈しない補助関数 fail を経由する。
fail の返り値の型は一般化された型変数なので、呼び出しの型も同じく曖昧な制約になる:

  $ cat > neverclass.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[Never] { let describe(n: Never) = n match {} }
  > let f(): String @ Fail = describe(perform throw("x"))
  > EOF
  $ diktor neverclass.kel
  ! neverclass.kel:4:5: 型エラー: 曖昧な制約: Describe を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]
  $ cat > neverclasshelper.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[Never] { let describe(n: Never) = n match {} }
  > let fail(m: String) = perform throw(m)
  > let f(): String @ Fail = describe(fail("x"))
  > EOF
  $ diktor neverclasshelper.kel
  ! neverclasshelper.kel:5:5: 型エラー: 曖昧な制約: Describe を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

neverclassann の f は返り値を Never と注釈した補助関数 fail を経由し、g は perform の結果を
Never と注釈した値束縛 v で受ける。どちらも describe の引数の型が Never に決まり、
Describe[Never] のインスタンスを選んで型検査を通る。実行すると perform がハンドラに捕まる:

  $ cat > neverclassann.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[Never] { let describe(n: Never) = n match {} }
  > let fail(m: String): Never @ Fail = perform throw(m)
  > let f(): String @ Fail = describe(fail("x"))
  > let g(): String @ Fail = { let v: Never = perform throw("y"); describe(v) }
  > echoln(f() handle { case throw(m) => "caught " + m })
  > echoln(g() handle { case throw(m) => "caught " + m })
  > EOF
  $ diktor neverclassann.kel
  caught x
  caught y

再開しない操作の節に resume は書けない。閉包の本体に書いても、節の中の入れ子の
handle の本体に書いても(外側の節の継続を指す)、同じ診断になる:

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
  $ cat > resumenested.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Ask = { ask: () => Int32 }
  > let r = { perform throw("x"); 1 } handle { case throw(e) => (resume(???)) handle { case ask() => resume(1) } }
  > EOF
  $ diktor resumenested.kel
  ! resumenested.kel:3:62: 型エラー: 再開しない操作 throw の節には resume を書けません(操作の返り値の型が Never です)
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

同じハンドラの操作節が末尾位置にない resume で再開した計算の中で再開しない操作が
起きると、節の値はその resume の返り値になり(§13.5、§13.6)、保留していた節の評価が
続く:

  $ cat > nontailresume.kel <<'EOF'
  > effect Parser = { next: () => Int32, fail: (String) => Never }
  > let r = ({ let a = perform next(); if a > 5 then perform fail("big") else a }) handle {
  >   case next() => { let v = resume(7); echoln("next clause got " + show(v)); v + 1000 }
  >   case fail(m) => { echoln("fail clause " + m); 5 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor nontailresume.kel
  fail clause big
  next clause got 5
  1005

同じエフェクトに再開する操作と再開しない操作を混ぜられる。判定は操作ごとで、
再開しない操作の節だけが resume を拒まれる:

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
  $ cat > mixedresume.kel <<'EOF'
  > effect Parser = { next: () => Int32, fail: (String) => Never }
  > let r = ({ perform next() }) handle {
  >   case next() => resume(1)
  >   case fail(m) => resume(???)
  > }
  > EOF
  $ diktor mixedresume.kel
  ! mixedresume.kel:4:19: 型エラー: 再開しない操作 fail の節には resume を書けません(操作の返り値の型が Never です)
  [1]

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

ガードから操作を起こして外側のハンドラが継続を捨てるときと、ガードで実行時エラーが
起きたときは、継続がまだ生きているので、ハンドラは外側から巻き戻され、自分の cancel 節が
走る(§13.6):

  $ cat > guardescape.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Res = { use: () => Unit }
  > let r = (({ perform use(); perform throw("g") }) handle {
  >   case use() => resume()
  >   case cancel => echoln("cancel res")
  > } handle {
  >   case throw(e) if { echoln("guard " + e); perform throw("from guard") } => 1
  >   case throw(e) => 2
  >   case cancel => echoln("cancel h")
  > }) handle {
  >   case throw(e) => { echoln("outer " + e); 3 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor guardescape.kel
  guard g
  cancel res
  cancel h
  outer from guard
  3
  $ cat > guarderror.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Res = { use: () => Unit }
  > let r = ({ perform use(); perform throw("g") }) handle {
  >   case use() => resume()
  >   case cancel => echoln("cancel res")
  > } handle {
  >   case throw(e) if 1 / 0 == 1 => 1
  >   case throw(e) => 2
  >   case cancel => echoln("cancel h")
  > }
  > echoln(show(r))
  > EOF
  $ diktor guarderror.kel
  cancel res
  cancel h
  実行時エラー: ゼロ除算です
  [3]

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

別のエフェクトの再開しない操作で抜けるときも、再開する操作を起こして外側の節が resume
しないときも同じで、抜けるハンドラ自身の cancel 節は走らない(§13.6):

  $ cat > otherescape.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Other = { oops: (Int32) => Never }
  > let mid(): Int32 @ {Other, Console} = ({ perform throw("x"); 1 }) handle {
  >   case throw(e) => perform oops(9)
  >   case cancel => echoln("cancel mid")
  > }
  > let r = mid() handle { case oops(n) => { echoln("oops " + show(n)); n } }
  > echoln(show(r))
  > EOF
  $ diktor otherescape.kel
  oops 9
  9
  $ cat > askescape.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Ask = { ask: () => Int32 }
  > let mid(): Int32 @ {Ask, Console} = ({ perform throw("x"); 1 }) handle {
  >   case throw(e) => perform ask() + 1
  >   case cancel => echoln("cancel mid")
  > }
  > let r = mid() handle { case ask() => { echoln("ask: no resume"); 5 } }
  > echoln(show(r))
  > EOF
  $ diktor askescape.kel
  ask: no resume
  5

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
内側のハンドラ(stop)の破棄によるものならその節の本体が走ってハンドラの本体が続き、
その値がハンドラ式の値になる:

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

破棄を進めている当のハンドラがその操作を受け取っても同じで、打ち切られた操作の節の
本体は走らず、巻き戻しは外側(mid の cancel 節)へ続き、先の操作の節の本体が走る:

  $ cat > cancelsame.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > effect Res = { use: () => Unit }
  > effect Mid = { tick: () => Unit }
  > let r = (({ perform use(); perform throw("first") }) handle {
  >   case use() => resume()
  >   case cancel => { echoln("cancel res"); perform throw("from cancel") }
  > }) handle {
  >   case tick() => resume()
  >   case cancel => echoln("cancel mid")
  > } handle {
  >   case throw(e) => { echoln("H clause " + e); 1 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor cancelsame.kel
  cancel res
  cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました
  cancel mid
  H clause first
  1

当のハンドラが再開する操作も持ち、cancel 節がその操作を起こし、その節が末尾でない
resume で再開したときは、先の破棄で終わった計算の値、つまり再開しない操作の節の値が、
その resume の返り値になる(§13.6):

  $ cat > cancelresume.kel <<'EOF'
  > effect Mixed = { ask: () => Int32, throw: (String) => Never }
  > effect Res = { use: () => Unit }
  > let r = ({ perform use(); perform throw("first") }) handle {
  >   case use() => resume()
  >   case cancel => { echoln("cancel res"); let a = perform ask(); echoln("cancel got " + show(a)) }
  > } handle {
  >   case ask() => { let x = resume(5); echoln("ask clause got " + show(x)); x + 1000 }
  >   case throw(e) => { echoln("H clause " + e); 7 }
  > }
  > echoln(show(r))
  > EOF
  $ diktor cancelresume.kel
  cancel res
  cancel got 5
  H clause first
  ask clause got 7
  1007

節の値が、同じハンドラの別の再開しない操作の打ち切りを経て、末尾でない resume に届く形と、
2 つのハンドラの節の値がそれぞれの resume に届く形。打ち切られた操作の節の本体は走らず、
各ハンドラの節の本体は 1 回だけ走る:

  $ cat > cancelresumevia.kel <<'EOF'
  > effect E = { throw: (String) => Never, abort2: (Int32) => Never, ask: () => Int32 }
  > effect Res = { use: () => Unit }
  > let r = ({ perform use(); perform throw("first") }) handle {
  >   case use() => resume()
  >   case cancel => { echoln("cancel res"); let a = perform ask(); echoln("cancel got " + show(a)); perform abort2(a); echoln("not reached") }
  > } handle {
  >   case throw(e) => { echoln("H throw " + e); 100 }
  >   case abort2(n) => { echoln("H abort2 " + show(n)); 200 }
  >   case ask() => { let x = resume(5); echoln("ask got " + show(x)); x + 1000 }
  > }
  > echoln("r=" + show(r))
  > EOF
  $ diktor cancelresumevia.kel
  cancel res
  cancel got 5
  cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました
  H throw first
  ask got 100
  r=1100
  $ cat > cancelresumetwo.kel <<'EOF'
  > effect E0 = { ask0: () => Int32, abort0: (String) => Never }
  > effect E1 = { ask1: () => Int32, abort1: (String) => Never }
  > effect Res = { use: () => Unit }
  > let r = {
  >   let w = {
  >     let z = ({ perform use(); perform abort1("one"); 1 }) handle {
  >       case use() => resume()
  >       case cancel => { echoln("cancel res"); let a = perform ask0(); echoln("cancel got a=" + show(a)); let b = perform ask1(); echoln("cancel got b=" + show(b)); perform abort0("from cancel"); echoln("not reached") }
  >     }
  >     z
  >   } handle {
  >     case ask1() => { let y = resume(7); echoln("ask1 got " + show(y)); y + 50000 }
  >     case abort1(e) => { echoln("H1 clause " + e); 10 }
  >     case cancel => echoln("H1 cancel")
  >   }
  >   echoln("H1 value " + show(w))
  >   w
  > } handle {
  >   case ask0() => { let x = resume(5); echoln("ask0 got " + show(x)); x + 1000 }
  >   case abort0(e) => { echoln("H0 abort0 " + e); 20 }
  >   case return(v) => { echoln("H0 return " + show(v)); v + 300 }
  >   case cancel => echoln("H0 cancel")
  > }
  > echoln("r=" + show(r))
  > EOF
  $ diktor cancelresumetwo.kel
  cancel res
  cancel got a=5
  cancel got b=7
  cancel 節で例外が抑制されました: cancel 節から操作の巻き戻しで脱出しようとしました
  H1 clause one
  ask1 got 10
  H1 value 50010
  H0 return 50010
  ask0 got 50310
  r=51310

トップレベルに残せない規則(§13.7)は再開しない操作にも同じに働く:

  $ cat > toplevel.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let x = perform throw("top")
  > EOF
  $ diktor toplevel.kel
  ! toplevel.kel:2:9: 型エラー: エフェクト Fail をここでは実行できません(ラベル Fail がありません(行は閉じています))
  [1]
