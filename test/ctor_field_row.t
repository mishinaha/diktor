コンストラクタの実引数とフィールドの型の単一化が行の不一致で失敗したとき、newtype の
フィールドの矢印の読み方(LangSpec §13.2)を診断に添えることがある。宣言したフィールドの
型のどこかに、閉じた行を持つ矢印か、型引数に書いた閉じた行があることが、添える条件の 1 つである。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

次の 4 つは読み方を添える。閉じた行を書いた位置は、ctorbox ではフィールドに書いた矢印、ctoralias ではエイリアス F を
展開して現れる矢印、ctornested では型引数 List[...] の中の矢印、ctorrowarg では行パラメータを
取る型 Cb の型引数に書いた {} である:

  $ cat > ctorbox.kel <<'KEL'
  > newtype Box = Box(() => Int32)
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let x = Box(b)
  > KEL
  $ diktor --type-check ctorbox.kel
  b : () => Int32 @ {Console}
  ! ctorbox.kel:3:9: 型エラー: ラベル Console がありません(行は閉じています)(コンストラクタ Box のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > ctoralias.kel <<'KEL'
  > type F = () => Int32
  > newtype Box = Box(F)
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let x = Box(b)
  > KEL
  $ diktor --type-check ctoralias.kel
  b : () => Int32 @ {Console}
  ! ctoralias.kel:4:9: 型エラー: ラベル Console がありません(行は閉じています)(コンストラクタ Box のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > ctornested.kel <<'KEL'
  > newtype L = L(List[() => Int32])
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let x = L(Cons(b, Nil))
  > KEL
  $ diktor --type-check ctornested.kel
  b : () => Int32 @ {Console}
  ! ctornested.kel:3:9: 型エラー: ラベル Console がありません(行は閉じています)(コンストラクタ L のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > ctorrowarg.kel <<'KEL'
  > newtype Cb[R] = Cb(() => Int32 @ R)
  > newtype W = W(Cb[{}])
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let w = W(Cb(b))
  > KEL
  $ diktor --type-check ctorrowarg.kel
  b : () => Int32 @ {Console}
  ! ctorrowarg.kel:4:9: 型エラー: ラベル Console がありません(行は閉じています)(コンストラクタ W のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

フィールドの型が型パラメータそのもの(Pair の A、Cons の A)なら、閉じた行を書いた位置が
フィールドにないので、読み方を添えず、単一化の報告だけを出す。ctortp は、mkp() の型と b の型が、
どちらも A に決まろうとして一致しない形である(mkp() は名前の参照でない式なので、行が閉じたままである)。
ctortpname は、b の型と、名前 ys の要素の型が、どちらも A に決まろうとして一致しない形である
(ys の型注釈の内側の矢印は、行が閉じている):

  $ cat > ctortp.kel <<'KEL'
  > newtype Pair[A] = Pair(A, A)
  > let mkp(): () => Int32 = fn() => 1
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let p = Pair(mkp(), b)
  > KEL
  $ diktor --type-check ctortp.kel
  mkp : () => () => Int32 @ {}
  b : () => Int32 @ {Console}
  ! ctortp.kel:4:9: 型エラー: ラベル Console がありません(行は閉じています)
  [1]
  $ cat > ctortpname.kel <<'KEL'
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let ys: List[() => Int32] = Nil
  > let xs = Cons(b, ys)
  > KEL
  $ diktor --type-check ctortpname.kel
  b : () => Int32 @ {Console}
  ys : List[() => Int32 @ {}]
  ! ctortpname.kel:3:10: 型エラー: ラベル Console がありません(行は閉じています)
  [1]

ctorrowvar の Two の 2 つのフィールドは、どちらも行が行変数 R である矢印で、閉じた行を
書いた位置がない。2 つのフィールドに mkp() と b を置くと、どちらの行も R に決まろうとして一致しないが、読み方は添えない:

  $ cat > ctorrowvar.kel <<'KEL'
  > newtype Two[R] = Two(() => Int32 @ R, () => Int32 @ R)
  > let mkp(): () => Int32 = fn() => 1
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let t = Two(mkp(), b)
  > KEL
  $ diktor --type-check ctorrowvar.kel
  mkp : () => () => Int32 @ {}
  b : () => Int32 @ {Console}
  ! ctorrowvar.kel:4:9: 型エラー: ラベル Console がありません(行は閉じています)
  [1]

ctorrecnoarrow は、フィールドの型が、閉じた行を持つ矢印も型引数に書いた閉じた行も含まないレコードである
(レコード自身の行は閉じている)。レコードのフィールド g が欠けた形で、読み方を添えない:

  $ cat > ctorrecnoarrow.kel <<'KEL'
  > newtype R = R({f: Int32, g: Int32})
  > let x = R({f = 1})
  > KEL
  $ diktor --type-check ctorrecnoarrow.kel
  ! ctorrecnoarrow.kel:2:9: 型エラー: ラベル g がありません(行は閉じています)
  [1]

添えるかどうかの判定は、単一化がフィールドの型のどこで失敗したかも、欠けたラベルがエフェクトかどうかも
調べない。ctormixed は、フィールドが閉じた行を持つ矢印 (A) => Int32 を含み、k の引数の型と
k2 の引数の型が、どちらも型パラメータ A に決まろうとして一致しない形で、読み方を添える。
ctorrecmiss は、閉じた行を持つ矢印を含むレコードのフィールドで、エフェクトでないフィールド g が
欠けた形で、これも読み方を添える。ctorarity は、閉じた行を持つ矢印のフィールドに、引数の個数が
違う関数を渡す形である。単一化が、行の不一致より前に個数の不一致として報告するので、読み方は
添えない:

  $ cat > ctormixed.kel <<'KEL'
  > newtype Q[A] = Q(List[(A) => Int32], List[(A) => Int32])
  > let k(g: () => Int32): Int32 = 0
  > let k2(g: () => Int32 @ Console): Int32 = 0
  > let q = Q(Cons(k, Nil), Cons(k2, Nil))
  > KEL
  $ diktor --type-check ctormixed.kel
  k : (() => Int32 @ {}) => Int32
  k2 : (() => Int32 @ {Console}) => Int32
  ! ctormixed.kel:4:9: 型エラー: ラベル Console がありません(行は閉じています)(コンストラクタ Q のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > ctorarity.kel <<'KEL'
  > newtype Box = Box((Int32) => Int32)
  > let k(): Int32 = 1
  > let x = Box(k)
  > KEL
  $ diktor --type-check ctorarity.kel
  k : () => Int32
  ! ctorarity.kel:3:9: 型エラー: 引数の個数が一致しません: () => Int32 と (Int32) => Int32 @ {}(引数は 0 個と 1 個です)
  [1]
  $ cat > ctorrecmiss.kel <<'KEL'
  > newtype R = R({f: () => Int32, g: Int32})
  > let x = R({f = fn() => 1})
  > KEL
  $ diktor --type-check ctorrecmiss.kel
  ! ctorrecmiss.kel:2:9: 型エラー: ラベル g がありません(行は閉じています)(コンストラクタ R のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
