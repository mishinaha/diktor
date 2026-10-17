再帰群の中で前にある束縛から後ろにある束縛への参照は単相である(LangSpec §6.3)。
前にある束縛の本体が後ろの束縛の型パラメータを何かの型に決めると、2 つの剛定数か、
剛定数と具体的な型が一致せずに型エラーになる。下の twotp、twotprev、concrete は、
その報告に原因に近い事実を括弧で添える形で、recfield と rechkt も添える形である。
selfrec、selfret、recfieldself、notp、region は添えない形である。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

[A: Eq] と [B: Eq] を注釈した 2 つの関数が互いを呼ぶ形。f の本体が g を呼ぶ時点で、
g の引数の型が f の A に決まる。g の本体が f を呼ぶ位置(引数 x)で、A と g の B が
一致しない:

  $ cat > twotp.kel <<'KEL'
  > let rec f[A: Eq](x: A, y: A): Boolean = x == y && g(x, y)
  > and g[B: Eq](x: B, y: B): Boolean = x == y || f(x, y)
  > echoln(show(f(1, 2)))
  > KEL
  $ diktor twotp.kel
  ! twotp.kel:2:49: 型エラー: スコープ付きの型が一致しません: ς1 と ς2(再帰群の中で、前にある束縛から後ろにある束縛への参照は単相です。f の型パラメータ A が g の型に入り込んでいます。前にある束縛の本体が後ろの束縛の型パラメータを何かの型に決める形は、型検査に通りません。§6.3)
  [1]

2 つの束縛を逆の順に書いても、互いを呼ぶので同じ形で落ちる。報告は入れ替わった
名前を挙げる:

  $ cat > twotprev.kel <<'KEL'
  > let rec g[B: Eq](x: B, y: B): Boolean = x == y || f(x, y)
  > and f[A: Eq](x: A, y: A): Boolean = x == y && g(x, y)
  > echoln(show(f(1, 2)))
  > KEL
  $ diktor twotprev.kel
  ! twotprev.kel:2:49: 型エラー: スコープ付きの型が一致しません: ς1 と ς2(再帰群の中で、前にある束縛から後ろにある束縛への参照は単相です。g の型パラメータ B が f の型に入り込んでいます。前にある束縛の本体が後ろの束縛の型パラメータを何かの型に決める形は、型検査に通りません。§6.3)
  [1]

後ろの g の型パラメータの注釈を外すと、g の型は f の A から決まり、群の終わりに
一般化されるので通る:

  $ cat > twotpinfer.kel <<'KEL'
  > let rec f[A: Eq](x: A, y: A): Boolean = x == y && g(x, y)
  > and g(x, y) = x == y || f(x, y)
  > echoln(show(f(1, 2)))
  > KEL
  $ diktor twotpinfer.kel
  false

前にある束縛が後ろの束縛の型パラメータの位置に具体的な型の値を渡す形。衝突は g の
本体の型を g の名前の型と一致させるところで起きる:

  $ cat > concrete.kel <<'KEL'
  > let rec f[A](x: A): Int32 = g(1i32)
  > and g[B](y: B): Int32 = 0
  > echoln(show(f(1)))
  > KEL
  $ diktor concrete.kel
  ! concrete.kel:2:5: 型エラー: スコープ付きの型が一致しません: Int32 と ς1(再帰群の中で、前にある束縛から後ろにある束縛への参照は単相です。f の本体が、型パラメータを持つ g を参照しています。前にある束縛の本体が後ろの束縛の型パラメータを何かの型に決める形は、型検査に通りません。§6.3、§18.2)
  [1]

selfrec は、前にある f が後ろの g を参照するが、g の型パラメータ B を Int32 に決めるのは
g 自身の本体の g(1i32)(多相再帰)である形で、前の束縛を挙げない。selfrecone は g だけの群、
selfrecrev は 2 つを逆の順に書いた形で、どちらも selfrec と同じ文言で落ちる:

  $ cat > selfrec.kel <<'KEL'
  > let rec f(n: Int32): Int32 = { let k = g; n }
  > and g[B](y: B): Int32 = g(1i32)
  > echoln(show(f(1i32)))
  > KEL
  $ diktor selfrec.kel
  ! selfrec.kel:2:5: 型エラー: スコープ付きの型が一致しません: Int32 と ς1
  [1]
  $ cat > selfrecone.kel <<'KEL'
  > let rec g[B](y: B): Int32 = g(1i32)
  > echoln(show(g(1i32)))
  > KEL
  $ diktor selfrecone.kel
  ! selfrecone.kel:1:9: 型エラー: スコープ付きの型が一致しません: Int32 と ς1
  [1]
  $ cat > selfrecrev.kel <<'KEL'
  > let rec g[B](y: B): Int32 = g(1i32)
  > and f(n: Int32): Int32 = { let k = g; n }
  > echoln(show(f(1i32)))
  > KEL
  $ diktor selfrecrev.kel
  ! selfrecrev.kel:1:9: 型エラー: スコープ付きの型が一致しません: Int32 と ς1
  [1]

selfret は、前にある f が useret(g) で g の返り値の位置を Int32 に決めるが、g の型パラメータ B
を Int32 に決めるのは g 自身の本体の g(1i32) である形で、前の束縛を挙げない:

  $ cat > selfret.kel <<'KEL'
  > let useret[X](h: (X) => Int32): Int32 = 0
  > let rec f(n: Int32): Int32 = useret(g)
  > and g[B](y: B) = g(1i32)
  > KEL
  $ diktor --type-check selfret.kel
  useret : ((A) => Int32 @ {}) => Int32
  ! selfret.kel:3:5: 型エラー: スコープ付きの型が一致しません: Int32 と ς1
  [1]

recfield は、前にある f が g の注釈 {a: Int32, b: B} と違うラベルの順のレコード式
{b = 1i32, a = ???} を渡し、g の型パラメータ B の欄 b を Int32 に決める形で、f を挙げる:

  $ cat > recfield.kel <<'KEL'
  > let rec f(n: Int32): Int32 = g({b = 1i32, a = ???})
  > and g[B](r: {a: Int32, b: B}): Int32 = 0
  > KEL
  $ diktor --type-check recfield.kel
  ! recfield.kel:2:5: 型エラー: スコープ付きの型が一致しません: Int32 と ς1(再帰群の中で、前にある束縛から後ろにある束縛への参照は単相です。f の本体が、型パラメータを持つ g を参照しています。前にある束縛の本体が後ろの束縛の型パラメータを何かの型に決める形は、型検査に通りません。§6.3、§18.2)
  [1]

recfieldself は、前にある f が g に渡すレコード式で、B の欄 a を ??? のまま未定に残す形で、
f を挙げない。B の欄を Int32 に決めるのは g 自身の本体の呼び出しである。g だけの群の
recfieldselfone も、同じ文言で落ちる:

  $ cat > recfieldself.kel <<'KEL'
  > let rec f(n: Int32): Int32 = g({b = 1i32, a = ???})
  > and g[B](r: {a: B, b: Int32}): Int32 = g({a = 1i32, b = 2i32})
  > KEL
  $ diktor --type-check recfieldself.kel
  ! recfieldself.kel:2:5: 型エラー: スコープ付きの型が一致しません: Int32 と ς1
  [1]
  $ cat > recfieldselfone.kel <<'KEL'
  > let rec g[B](r: {a: B, b: Int32}): Int32 = g({a = 1i32, b = 2i32})
  > KEL
  $ diktor --type-check recfieldselfone.kel
  ! recfieldselfone.kel:1:9: 型エラー: スコープ付きの型が一致しません: Int32 と ς1
  [1]

rechkt は、前にある f が、高カインドの型パラメータ F を持つ g の引数 F[Int32] の位置に
Option[Int32] の値を渡し、F を Option に決める形で、f を挙げる:

  $ cat > rechkt.kel <<'KEL'
  > let rec f(n: Option[Int32]): Int32 = g(n)
  > and g[F[_]](y: F[Int32]): Int32 = 0
  > KEL
  $ diktor --type-check rechkt.kel
  ! rechkt.kel:2:5: 型エラー: スコープ付きの型が一致しません: Option と ς1(再帰群の中で、前にある束縛から後ろにある束縛への参照は単相です。f の本体が、型パラメータを持つ g を参照しています。前にある束縛の本体が後ろの束縛の型パラメータを何かの型に決める形は、型検査に通りません。§6.3、§18.2)
  [1]

notp は、型パラメータを持たない g の Int32 の位置に、f が自分の型パラメータ A の値を渡す
形で、何も添えない。notprev は 2 つを逆の順に書いた形で、これも落ち、何も添えない:

  $ cat > notp.kel <<'KEL'
  > let rec f[A](x: A): Int32 = g(x)
  > and g(y: Int32): Int32 = 0
  > echoln(show(f(1)))
  > KEL
  $ diktor notp.kel
  ! notp.kel:2:5: 型エラー: スコープ付きの型が一致しません: ς1 と Int32
  [1]
  $ cat > notprev.kel <<'KEL'
  > let rec g(y: Int32): Int32 = 0
  > and f[A](x: A): Int32 = g(x)
  > echoln(show(f(1)))
  > KEL
  $ diktor notprev.kel
  ! notprev.kel:2:27: 型エラー: スコープ付きの型が一致しません: ς1 と Int32
  [1]

region は、bump の本体の run の中で、bump の引数の配列を使う形で、リージョンの取り違えの
報告に何も添えない。regionone は bump だけの群で、同じ文言で落ちる:

  $ cat > region.kel <<'KEL'
  > let rec f[h](a: MutableArray[h, Int32]): Unit = bump(a)
  > and bump[k](a: MutableArray[k, Int32]): Unit = run h2 { MutableArray.set(a, 0, 42) }
  > KEL
  $ diktor --type-check region.kel
  ! region.kel:2:74: 型エラー: ほかのリージョンの MutableArray を使おうとしています(スコープ付きの型が一致しません: ς1 と ς2)
  [1]
  $ cat > regionone.kel <<'KEL'
  > let rec bump[k](a: MutableArray[k, Int32]): Unit = run h2 { MutableArray.set(a, 0, 42) }
  > KEL
  $ diktor --type-check regionone.kel
  ! regionone.kel:1:78: 型エラー: ほかのリージョンの MutableArray を使おうとしています(スコープ付きの型が一致しません: ς1 と ς2)
  [1]
