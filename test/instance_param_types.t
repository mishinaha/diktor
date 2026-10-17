インスタンスのメソッドの仮引数のうち、型注釈のない変数と _ の型は、クラス宣言の署名の
対応する引数の型に決まる(LangSpec §12.2)。let の値束縛で書いた無名関数の仮引数も同じで
ある。処理系は本体を推論する前にその型を仮引数に渡すので、本体の数値リテラルの型と
網羅性の検査はその型を見る。let rec の値束縛の形(let rec x = fn(...) => ...)の仮引数には
渡さない。返り値の型と最外の行は渡さず、推論の後の包摂で署名と照らす。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

署名の引数が Never なので、仮引数 n の型は Never に決まり、n match {} は網羅的である。
関数束縛(D1)、let の値束縛の無名関数(D2)、let rec の関数束縛(D3)の 3 つの形で書き、
--strict-exhaustive でも警告を出さない:

  $ cat > insnever.kel <<'KEL'
  > type class D1[A] { val d1: (A) => String }
  > type class D2[A] { val d2: (A) => String }
  > type class D3[A] { val d3: (A) => String }
  > type instance D1[Never] { let d1(n) = n match {} }
  > type instance D2[Never] { let d2 = fn(n) => n match {} }
  > type instance D3[Never] { let rec d3(n) = n match {} }
  > KEL
  $ diktor --strict-exhaustive --type-check insnever.kel

let rec の値束縛の形で書いた d3 の仮引数 n には署名の型を渡さないので、n match {} は
網羅漏れの警告になり、--strict-exhaustive では終了状態 1 になる:

  $ cat > insrecval.kel <<'KEL'
  > type class D3[A] { val d3: (A) => String }
  > type instance D3[Never] { let rec d3 = fn(n) => n match {} }
  > KEL
  $ diktor --strict-exhaustive --type-check insrecval.kel
  ⚠ match が非網羅的です。照合対象の型は、網羅性を調べた時点で Never のようなコンストラクタを持たない型と分かっていません(節のない match {} が網羅的なのは、照合対象がそのような型のときだけです)
  [1]

insnever と同じく、Describe[Never] の describe の case _ には一致する値が無いという警告が出る。
Lv の lv の l の型は署名の #Lo | #Hi に決まるので、第 3 節の case _ には冗長の警告が
出る。--strict-exhaustive では終了状態 1 になる:

  $ cat > inswild.kel <<'KEL'
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[Never] { let describe(n) = n match { case _ => "never" } }
  > type instance Describe[Int32] { let describe(n) = show(n) }
  > type class Lv[A] { val lv: (A, #Lo | #Hi) => String }
  > type instance Lv[Int32] { let lv(n, l) = l match { case #Lo => "lo" case #Hi => "hi" case _ => "other" } }
  > echo(describe(3i32))
  > echo(lv(1, #Hi))
  > KEL
  $ diktor inswild.kel
  ⚠ このパターンには一致する値がありません
  ⚠ 第 3 節は到達不能です(冗長)
  3hi
  $ diktor --strict-exhaustive --type-check inswild.kel
  ⚠ このパターンには一致する値がありません
  ⚠ 第 3 節は到達不能です(冗長)
  _ : {}
  _ : {}
  [1]

a と b の型が署名の Int64 に決まるので、a > 10 の 10 も Int64 になり、受理する:

  $ cat > inslit.kel <<'KEL'
  > type class Pick[A] { val pick: (A, A) => A }
  > type instance Pick[Int64] { let pick(a, b) = if a > 10 then a else b }
  > echo(show(pick(3i64, 20i64)))
  > KEL
  $ diktor inslit.kel
  20

l の型が署名の #Lo | #Hi に決まるので、case #Lo だけの match は型エラーではなく網羅漏れの
警告になる。--strict-exhaustive では終了状態 1 になる:

  $ cat > insvariant.kel <<'KEL'
  > type class Lv[A] { val lv: (A, #Lo | #Hi) => String }
  > type instance Lv[Int32] { let lv(n, l) = l match { case #Lo => "lo" } }
  > echo(lv(1, #Lo))
  > KEL
  $ diktor insvariant.kel
  ⚠ match が非網羅的です。例えば #Hi(_) が漏れています
  lo
  $ diktor --strict-exhaustive insvariant.kel
  ⚠ match が非網羅的です。例えば #Hi(_) が漏れています
  [1]

n の型が署名の Int32 に決まるので、__string_concat(n, "x") の食い違いは、包摂の言い換え
ではなく、本体の n の位置(2:67)の素の文面で出る:

  $ cat > insbody.kel <<'KEL'
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[Int32] { let describe(n) = __string_concat(n, "x") }
  > KEL
  $ diktor --type-check insbody.kel
  ! insbody.kel:2:67: 型エラー: 型が一致しません: Int32 と String
  [1]

返り値の型は署名から決めないので、リテラル 0 は既定の Int32 になり、包摂で署名の Int64
と照らした時点で落ちる:

  $ cat > insret.kel <<'KEL'
  > type class Sz[A] { val size: (A) => Int64 }
  > type instance Sz[String] { let size(s) = 0 }
  > echo(show(size("a")))
  > KEL
  $ diktor insret.kel
  ! insret.kel:2:32: 型エラー: インスタンスメソッド size がクラス宣言の型を満たしません(型が一致しません: Int32 と Int64)
  [1]

注釈を書いた仮引数 n: Int32 には署名の型 String を渡さないので、食い違いは包摂で報告する:

  $ cat > insannot.kel <<'KEL'
  > type class Describe[A] { val describe: (A) => String }
  > type instance Describe[String] { let describe(n: Int32) = "x" }
  > KEL
  $ diktor --type-check insannot.kel
  ! insannot.kel:2:38: 型エラー: インスタンスメソッド describe がクラス宣言の型を満たしません(型が一致しません: Int32 と String)
  [1]

前提を持つインスタンス Show[Box[_]] と Eq[Box[_]] では、頭の剛定数 A を含む Box[A] を
仮引数に渡す。本体で前提のクラスのメソッド show と == を使う形を受理し、
--strict-exhaustive でも警告は出ない:

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
