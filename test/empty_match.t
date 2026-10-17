節のない match {} の照合対象の型が網羅性を調べる時点で未定の型変数のとき、処理系はその型を
Never に決めることがある(§11.2)。変数に制約が付かないことと、match を含む束縛の外から観測
できないことが、決める条件に含まれる。決めると match {} は網羅的になる。

direct は、再開しない操作の perform の結果を関数の中で直接照合する。警告は出ず、
--strict-exhaustive でも終了コードは 0 である:

  $ cat > direct.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let get(o: Option[Int32]): Int32 @ Fail = o match {
  >   case Some(v) => v
  >   case None => perform throw("none") match {}
  > }
  > echoln(show(get(None) handle { case throw(e) => 0 - 1 }))
  > EOF
  $ diktor direct.kel
  -1
  $ diktor --strict-exhaustive direct.kel
  -1

次の 4 本は、照合対象が perform の式そのものではない。helper は返り値を注釈しない
補助関数 fail の結果を照合し、--strict-exhaustive でも終了コードは 0 である。
valbind は perform の結果を局所の値束縛 z で受けてから照合する。abort は返り値を型パラメータに
した補助関数の結果を照合する。mutual は let rec の群の中で perform の結果を照合する。
どれも警告は出ない:

  $ cat > helper.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let fail(m: String) = perform throw(m)
  > let get(o: Option[Int32]): Int32 @ Fail = o match {
  >   case Some(v) => v
  >   case None => fail("none") match {}
  > }
  > echoln(show(get(None) handle { case throw(e) => 0 - 1 }))
  > EOF
  $ diktor helper.kel
  -1
  $ diktor --strict-exhaustive helper.kel
  -1
  $ cat > valbind.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let get(o: Option[Int32]): Int32 @ Fail = o match {
  >   case Some(v) => v
  >   case None => { let z = perform throw("none"); z match {} }
  > }
  > echoln(show(get(None) handle { case throw(e) => 0 - 1 }))
  > EOF
  $ diktor valbind.kel
  -1
  $ cat > abort.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let abort[A](m: String): A @ Fail = perform throw(m)
  > let get(o: Option[Int32]): Int32 @ Fail = o match {
  >   case Some(v) => v
  >   case None => abort("none") match {}
  > }
  > echoln(show(get(None) handle { case throw(e) => 0 - 1 }))
  > EOF
  $ diktor abort.kel
  -1
  $ cat > mutual.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let rec f(n: Int32): Int32 @ Fail = if n == 0 then { perform throw("z") match {} } else g(n - 1)
  > and g(n: Int32): Int32 @ Fail = f(n)
  > echoln(show({ f(2) } handle { case throw(e) => -1 }))
  > EOF
  $ diktor mutual.kel
  -1

laterlet2 は、match の後に無関係な局所の let m を置く。m の束縛の網羅性の検査は get の
束縛より先に走るが、照合対象の型変数は get の本体のレベルにあるので、そこでは決めずに
get の束縛の検査に送る。そこで Never に決まり、--strict-exhaustive でも警告は出ない:

  $ cat > laterlet2.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let get(o: Option[Int32]): Int32 @ Fail = {
  >   if o == None then perform throw("none") match {} else ()
  >   let m = 1
  >   m
  > }
  > echoln(show(get(None) handle { case throw(e) => 0 - 1 }))
  > EOF
  $ diktor laterlet2.kel
  -1
  $ diktor --strict-exhaustive laterlet2.kel
  -1

okarm の mk の型では、#Ok の積載値の型は型変数である。go の v match {} の照合対象は、
その型変数を具体化した変数で、go の型に現れないので、go の束縛の検査で Never に決まる。
#Ok(v) の v は値の無い型になるので、第 1 節は到達不能と報告される。go(true) は mk の中で
perform を起こすので、ハンドラが -1 を返す:

  $ cat > okarm.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let mk(b: Boolean) = if b then #Ok(perform throw("x")) else #Err(3)
  > let go(b: Boolean): Int32 @ Fail = mk(b) match {
  >   case #Ok(v) => v match {}
  >   case #Err(n) => n
  > }
  > echoln(show(go(false) handle { case throw(e) => 0 - 1 }))
  > echoln(show(go(true) handle { case throw(e) => 0 - 1 }))
  > EOF
  $ diktor okarm.kel
  ⚠ 第 1 節は到達不能です(冗長)
  3
  -1

unannparam は、型注釈のない引数 x を照合する。x の型変数は f の型に現れるので決めず、
網羅漏れの警告になる。--type-check の出力のとおり、f の型は (A) => B のままである:

  $ cat > unannparam.kel <<'EOF'
  > let f(x) = x match {}
  > echoln("ok")
  > EOF
  $ diktor unannparam.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  ok
  $ diktor --type-check unannparam.kel
  f : (A) => B
  ⚠ match が非網羅的です。例えば _ が漏れています
  _ : {}

r11_void_helper は、unannparam と同じ形の elim を、右辺のない newtype Void の値に使う。
elim の引数の型変数を決めないので、use の elim(v) は型が合い、警告の後で実行される:

  $ cat > r11_void_helper.kel <<'EOF'
  > newtype Void
  > let elim(x) = x match {}
  > let use(v: Void): Int32 = elim(v)
  > echoln("ok")
  > EOF
  $ diktor r11_void_helper.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  ok

r1_nongen_top の h は、値制限で一般化しない最上位の束縛である。照合対象 y の型変数は h の
型に現れるので決めず、警告になる。決めないので、後の h(3) は型が合い、k(false) は 0 を
返す。w1 の局所の g は、前の最上位の束縛 p の弱い型変数を照合する。その変数は最上位の
レベルにあるので決めず、警告になる。決めないので、後の p(3) は型が合い、3 を出力する:

  $ cat > r1_nongen_top.kel <<'EOF'
  > let id(x) = x
  > let h = id(fn(y) => y match {})
  > let k(b: Boolean): Int32 = if b then h(3) else 0
  > echoln(show(k(false)))
  > EOF
  $ diktor r1_nongen_top.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  0
  $ cat > w1.kel <<'EOF'
  > let id(x) = x
  > let p = id(fn(y) => y)
  > fn(u: Int32) => { let g = fn(v) => p(v) match {}; u }
  > echoln(show(p(3)))
  > EOF
  $ diktor w1.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  3

rigid は、利用者が明示した型パラメータ A の値 x を、局所の束縛 q の中で照合する。A は
未定の型変数でないので決めず、警告になる。numvar は、perform の結果を局所の値束縛 r で
受け、let a の中で照合し、後で r == 0 と比べる。比べると r の型変数に数値の制約が付くので
決めず、警告になる:

  $ cat > rigid.kel <<'EOF'
  > let f[A](x: A): Int32 = { let q = x match {}; 0 }
  > echoln("ok")
  > EOF
  $ diktor rigid.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  ok
  $ cat > numvar.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > let f(): Int32 @ Fail = { let r = perform throw("x"); let a = r match {}; if r == 0 then 1 else 2 }
  > echoln("ok")
  > EOF
  $ diktor numvar.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  ok

toplevelstmt は、最上位の値でない式文に、局所の束縛で包まずに match {} を直接書く。
照合対象の型変数は最上位のレベルにあるので決めず、警告になり、--strict-exhaustive では
終了コード 1 になる:

  $ cat > toplevelstmt.kel <<'EOF'
  > effect Fail = { throw: (String) => Never }
  > { perform throw("x") match {} } handle { case throw(e) => echoln(e) }
  > EOF
  $ diktor toplevelstmt.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  x
  $ diktor --strict-exhaustive toplevelstmt.kel
  ⚠ match が非網羅的です。例えば _ が漏れています
  [1]
