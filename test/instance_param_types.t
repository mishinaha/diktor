インスタンスのメソッドの仮引数のうち、型注釈のない変数と _ の型は、クラス宣言のシグネチャで対応する位置にある引数の型に決まる(LangSpec §12.2)。
let の値束縛に書いた無名関数の仮引数も、すべての仮引数が型注釈のない変数か _ であれば、同じように決まる。
処理系は本体を推論する前にその型を仮引数に与えるので、本体の数値リテラルの型と網羅性の検査の結果は、その型によって決まる。
let rec の値束縛(let rec x = fn(...) => ...)の仮引数には、シグネチャの型を与えない。
返り値の型と最も外側の行も与えず、推論の後の包摂の検査でシグネチャと比べる。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

シグネチャの引数の型が Never なので、仮引数 n の型は Never に決まり、n match {} は網羅的である。
関数束縛(D1)、let の値束縛の無名関数(D2)、let rec の関数束縛(D3)の 3 つの形で書く。
どれも、--strict-exhaustive を付けても警告が出ない:

  $ cat > insnever.kel <<'KEL'
  > type class D1[A] { val d1: (A) => String }
  > type class D2[A] { val d2: (A) => String }
  > type class D3[A] { val d3: (A) => String }
  > type instance D1[Never] { let d1(n) = n match {} }
  > type instance D2[Never] { let d2 = fn(n) => n match {} }
  > type instance D3[Never] { let rec d3(n) = n match {} }
  > KEL
  $ diktor --strict-exhaustive --type-check insnever.kel

let rec の値束縛で書いた d3 の仮引数 n にはシグネチャの型を与えないので、n match {} は網羅漏れの警告になる。
--strict-exhaustive を付けると終了コード 1 で終了する:

  $ cat > insrecval.kel <<'KEL'
  > type class D3[A] { val d3: (A) => String }
  > type instance D3[Never] { let rec d3 = fn(n) => n match {} }
  > KEL
  $ diktor --strict-exhaustive --type-check insrecval.kel
  ⚠ match が非網羅的です。照合対象の型は、網羅性を調べた時点で Never のようなコンストラクタを持たない型と分かっていません(節のない match {} が網羅的なのは、照合対象がそのような型のときだけです)
  [1]

insnever と同じく、Describe[Never] の describe の仮引数 n の型は Never に決まる。
これを確かめるために、case _ を 2 つ並べた match を Describe[Never] と Describe[String] に書いて、結果を比較する。
inswild2never では n の型が Never なので、第 1 節と第 2 節の両方を到達不能と報告する。
inswild2str では第 1 節が String の値に一致するので、第 2 節だけを報告する:

  $ cat > inswild2never.kel <<'KEL'
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[Never] { let describe(n) = n match { case _ => "never" case _ => "never2" } }
  > type instance Describe[Int32] { let describe(n) = show(n) }
  > echo(describe(3i32))
  > KEL
  $ diktor --strict-exhaustive --type-check inswild2never.kel
  ⚠ 第 1 節は到達不能です(冗長)
  ⚠ 第 2 節は到達不能です(冗長)
  _ : {}
  [1]
  $ cat > inswild2str.kel <<'KEL'
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[String] { let describe(n) = n match { case _ => "s" case _ => "s2" } }
  > type instance Describe[Int32] { let describe(n) = show(n) }
  > echo(describe(3i32))
  > KEL
  $ diktor --strict-exhaustive --type-check inswild2str.kel
  ⚠ 第 2 節は到達不能です(冗長)
  _ : {}
  [1]

inswildnever は、同じ Describe[Never] で節を 1 つにした形である。
値を持たない型を 1 つのパターンで受ける場合の規則(uninhabited_pattern.t)に該当するので、警告が出ない。
--strict-exhaustive を付けても終了コードは 0 である:

  $ cat > inswildnever.kel <<'KEL'
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[Never] { let describe(n) = n match { case _ => "never" } }
  > type instance Describe[Int32] { let describe(n) = show(n) }
  > echo(describe(3i32))
  > KEL
  $ diktor inswildnever.kel
  3
  $ diktor --strict-exhaustive --type-check inswildnever.kel
  _ : {}

クラス Lv のメソッド lv では、仮引数 l の型がシグネチャの #Lo | #Hi に決まるので、第 3 節の case _ に到達不能(冗長な節)の警告が出る。
--strict-exhaustive を付けると終了コード 1 で終了する:

  $ cat > inswildlv.kel <<'KEL'
  > type class Lv[A] { val lv: (A, #Lo | #Hi) => String }
  > type instance Lv[Int32] { let lv(n, l) = l match { case #Lo => "lo" case #Hi => "hi" case _ => "other" } }
  > echo(lv(1, #Hi))
  > KEL
  $ diktor inswildlv.kel
  ⚠ 第 3 節は到達不能です(冗長)
  hi
  $ diktor --strict-exhaustive --type-check inswildlv.kel
  ⚠ 第 3 節は到達不能です(冗長)
  _ : {}
  [1]

a と b の型がシグネチャの Int64 に決まるので、a > 10 の 10 も Int64 になり、受理する:

  $ cat > inslit.kel <<'KEL'
  > type class Pick[A] { val pick: (A, A) => A }
  > type instance Pick[Int64] { let pick(a, b) = if a > 10 then a else b }
  > echo(show(pick(3i64, 20i64)))
  > KEL
  $ diktor inslit.kel
  20

l の型がシグネチャの #Lo | #Hi に決まるので、case #Lo だけの match は、型エラーではなく網羅漏れの警告になる。
--strict-exhaustive を付けると終了コード 1 で終了する:

  $ cat > insvariant.kel <<'KEL'
  > type class Lv[A] { val lv: (A, #Lo | #Hi) => String }
  > type instance Lv[Int32] { let lv(n, l) = l match { case #Lo => "lo" } }
  > echo(lv(1, #Lo))
  > KEL
  $ diktor insvariant.kel
  ⚠ match が非網羅的です。たとえば #Hi(_) が漏れています
  lo
  $ diktor --strict-exhaustive insvariant.kel
  ⚠ match が非網羅的です。たとえば #Hi(_) が漏れています
  [1]

n の型がシグネチャの Int32 に決まるので、__string_concat(n, "x") の型の不一致は、本体の n の位置(2:67)で報告する。
メッセージは、包摂の検査の `クラス宣言の型を満たしません` ではなく、`型が一致しません` だけである:

  $ cat > insbody.kel <<'KEL'
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[Int32] { let describe(n) = __string_concat(n, "x") }
  > KEL
  $ diktor --type-check insbody.kel
  ! insbody.kel:2:67: 型エラー: 型が一致しません: Int32 と String
  [1]

返り値の型はシグネチャから決めないので、リテラル 0 の型は既定の Int32 になる。
そのため、包摂の検査でシグネチャの Int64 と比べた時点で型エラーになる:

  $ cat > insret.kel <<'KEL'
  > type class Sz[A] { val size: (A) => Int64 }
  > type instance Sz[String] { let size(s) = 0 }
  > echo(show(size("a")))
  > KEL
  $ diktor insret.kel
  ! insret.kel:2:32: 型エラー: インスタンスメソッド size がクラス宣言の型を満たしません(型が一致しません: Int32 と Int64)
  [1]

型注釈を書いた仮引数 n: Int32 にはシグネチャの型 String を与えないので、型の不一致は包摂の検査で報告する:

  $ cat > insannot.kel <<'KEL'
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[String] { let describe(n: Int32) = "x" }
  > KEL
  $ diktor --type-check insannot.kel
  ! insannot.kel:2:38: 型エラー: インスタンスメソッド describe がクラス宣言の型を満たしません(型が一致しません: Int32 と String)
  [1]

前提付きインスタンス Show[Box[_]] と Eq[Box[_]] では、インスタンスの型パラメータ A を固定したスコーレム定数を含む Box[A] を仮引数に与える。
本体で前提のクラスのメソッド show と == を使う形を受理する。
--strict-exhaustive を付けても警告は出ない:

  $ cat > inspremise.kel <<'KEL'
  > newtype Box[A] = Box(A)
  > type instance[A: Show] Show[Box[_]] { let show(b) = b match { case Box(x) => "Box(" + show(x) + ")" } }
  > type instance[A: Eq] Eq[Box[_]] { let eq(a, b) = (a, b) match { case (Box(x), Box(y)) => x == y } }
  > echo(show(Box(3i32)))
  > echo(show(Box(1i32) == Box(1i32)))
  > echo(show(Box("a") == Box("b")))
  > KEL
  $ diktor inspremise.kel
  Box(3)truefalse
  $ diktor --strict-exhaustive --type-check inspremise.kel
  _ : {}
  _ : {}
  _ : {}
