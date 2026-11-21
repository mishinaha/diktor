値を持たない型を受けるパターン(LangSpec §11.2)。関数の引数、無名関数の引数、let のパターン
束縛、return 節、節が 1 つの match のように、パターンが 1 つだけの位置では、受ける型が
値を持たなければ、網羅漏れも、一致する値がないことも報告しない。その位置には値が来ないので、
照合が失敗することもない。値を持つかどうかは型だけで決め、パターンの形は調べない。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

関数と無名関数の引数。pv は右辺を省いた newtype の Empt を変数で、pr は {x: Empt} を
レコードで、pt は (Int32, Never) をタプルで、pc は Absurd をコンストラクタで、pnest は
{x: Absurd} を入れ子のパターンで、pvar は #V(Never) をヴァリアントで受ける。lc は無名関数の
引数で Absurd をコンストラクタで受ける。--strict-exhaustive でも、どれにも警告は出ない:

  $ cat > params.kel <<'KEL'
  > newtype Empt
  > newtype Absurd = MkA(Empt)
  > let pv(n: Empt) = 1
  > let pr({x}: {x: Empt}) = 2
  > let pt((a, b): (Int32, Never)) = 3
  > let pc(MkA(n)) = 4
  > let pnest({x = MkA(n)}: {x: Absurd}) = 5
  > let pvar(#V(n): #V(Never)) = 6
  > let lc = fn(MkA(n)) => 7
  > KEL
  $ diktor --strict-exhaustive --type-check --no-prelude params.kel
  pv : (Empt) => Int32
  pr : ({x: Empt}) => Int32
  pt : ((Int32, Never)) => Int32
  pc : (Absurd) => Int32
  pnest : ({x: Absurd}) => Int32
  pvar : (#V(Never)) => Int32
  lc : (Absurd) => Int32

let のパターン束縛(bt はタプル、bc はコンストラクタ)、節が 1 つの match(mv は Never を
変数で、mc は Absurd をコンストラクタで受ける)、return 節(rc は Absurd をコンストラクタで
受ける)にも、警告は出ない:

  $ cat > single.kel <<'KEL'
  > newtype Empt
  > newtype Absurd = MkA(Empt)
  > effect Fail = { throw: (String) => Never }
  > effect Nop = { nop: () => Int32 }
  > let bt(): Int32 @ Fail = { let (a, b): (Int32, Never) = (1, perform throw("y")); a }
  > let bc(): Int32 @ Fail = { let MkA(n) = perform throw("z"); 2 }
  > let mv(n: Never): Int32 = n match { case m => 1 }
  > let mc(a: Absurd): Int32 = a match { case MkA(_) => 2 }
  > let rc(t: () => Absurd @ Nop): Int32 = t() handle { case nop() => resume(1)  case return(MkA(n)) => 3 }
  > KEL
  $ diktor --strict-exhaustive --type-check --no-prelude single.kel
  bt : () => Int32 @ {Fail}
  bc : () => Int32 @ {Fail}
  mv : (Never) => Int32
  mc : (Absurd) => Int32
  rc : (() => Absurd @ {Nop}) => Int32

値を持たないデータ型 Absurd の引数を、引数のコンストラクタパターン(elimA)と、節が 1 つの match
(elimB)で分解し、中の Empt を節のない match で受ける。警告が出ないので、--strict-exhaustive でも実行して 42 を出力する:

  $ cat > elim.kel <<'KEL'
  > newtype Empt
  > newtype Absurd = MkA(Empt)
  > let elimA[A](MkA(n)): A = n match {}
  > let elimB[A](a: Absurd): A = a match { case MkA(n) => n match {} }
  > let pick(r: #Ok(Int32) | #Err(Absurd)): Int32 = r match {
  >   case #Ok(n) => n
  >   case #Err(a) => elimA(a)
  > }
  > echo(show(pick(#Ok(41)) + 1))
  > KEL
  $ diktor --strict-exhaustive elim.kel
  42

警告が残る形。k1 の Opt2[Empt] には Nn の値があるので、Sm(x) には Nn の漏れと、一致する
値がないことを警告する。k2 は Never に節を 2 つ書いた match で、どちらの節も到達不能と
報告する。k3 はペイロードが Never の #Err(e) の節で、到達不能と報告する。k4 は
コンストラクタを持つが値を持たない型 Absurd への節のない match {} で、網羅漏れを警告する:

  $ cat > keep.kel <<'KEL'
  > newtype Empt
  > newtype Absurd = MkA(Empt)
  > newtype Opt2[A] = Sm(A) | Nn
  > let k1(Sm(x): Opt2[Empt]) = 1
  > let k2(n: Never): Int32 = n match { case a => 1  case b => 2 }
  > let k3(o: #Ok(Int32) | #Err(Never)): Int32 = o match { case #Ok(n) => n  case #Err(e) => 0 }
  > let k4[A](a: Absurd): A = a match {}
  > KEL
  $ diktor --type-check --no-prelude keep.kel
  k1 : (Opt2[Empt]) => Int32
  ⚠ match が非網羅的です。例えば Nn が漏れています
  ⚠ このパターンには一致する値がありません
  k2 : (Never) => Int32
  ⚠ 第 1 節は到達不能です(冗長)
  ⚠ 第 2 節は到達不能です(冗長)
  k3 : (#Ok(Int32) | #Err(Never)) => Int32
  ⚠ 第 2 節は到達不能です(冗長)
  k4 : (Absurd) => A
  ⚠ match が非網羅的です。例えば MkA(_) が漏れています

再帰するデータ型。処理系は、型をたどる途中で同じデータ型の名前に戻ると、型引数が
違っていても値を持つとみなし、そこから先をたどらない。r1 の M[Never] は、S の引数 M[Int32] で M に戻るので
値を持つとみなされ、Z(x) には S(_) の漏れと、一致する値がないことを警告する。r2 の
L = C(L) | D(L) は値を作れない型だが、L をたどって L に戻ったところで値を持つとみなすので、
C(x) に D(_) の漏れを警告する。r3 は M の S の引数 M[Int32] を値を持たない M2[Empt] に替えた
M2 で、M2[Never] は値を作れないが、S2 の引数で M2 に戻るので、Z2(x) には r1 と同じ
2 つの警告が出る:

  $ cat > rec.kel <<'KEL'
  > newtype M[A] = Z(A) | S(M[Int32])
  > newtype L = C(L) | D(L)
  > let r1(Z(x): M[Never]) = 1
  > let r2(C(x)) = 2
  > newtype Empt
  > newtype M2[A] = Z2(A) | S2(M2[Empt])
  > let r3(Z2(x): M2[Never]) = 3
  > KEL
  $ diktor --type-check --no-prelude rec.kel
  r1 : (M[Never]) => Int32
  ⚠ match が非網羅的です。例えば S(_) が漏れています
  ⚠ このパターンには一致する値がありません
  r2 : (L) => Int32
  ⚠ match が非網羅的です。例えば D(_) が漏れています
  r3 : (M2[Never]) => Int32
  ⚠ match が非網羅的です。例えば S2(_) が漏れています
  ⚠ このパターンには一致する値がありません

W[A] = Wr(A, Boolean) の A に置く型によって、値を持つとみなすかどうかが分かれる。a1 の関数型、
a2 の組み込みの不透明な型 Array[Never]、a3 の型パラメータ、a4 の String、a6 の開いた行の
ヴァリアントは値を持つとみなすので、W も値を持ち、Wr(x, true) に Wr(_, false) の漏れを
警告する。a5 の Never と a7 の閉じた行の #A(Never) は値を持たないので、W も値を持たず、
警告しない:

  $ cat > valued.kel <<'KEL'
  > newtype W[A] = Wr(A, Boolean)
  > let a1(Wr(x, true): W[(Int32) => Never]) = 1
  > let a2(Wr(x, true): W[Array[Never]]) = 2
  > let a3[B](Wr(x, true): W[B]) = 3
  > let a4(Wr(x, true): W[String]) = 4
  > let a5(Wr(x, true): W[Never]) = 5
  > let a6[R](Wr(x, true): W[#A(Never) | R]) = 6
  > let a7(Wr(x, true): W[#A(Never)]) = 7
  > KEL
  $ diktor --type-check valued.kel
  a1 : (W[(Int32) => Never @ {}]) => Int32
  ⚠ match が非網羅的です。例えば Wr(_, false) が漏れています
  a2 : (W[Array[Never]]) => Int32
  ⚠ match が非網羅的です。例えば Wr(_, false) が漏れています
  a3 : (W[A]) => Int32
  ⚠ match が非網羅的です。例えば Wr(_, false) が漏れています
  a4 : (W[String]) => Int32
  ⚠ match が非網羅的です。例えば Wr(_, false) が漏れています
  a5 : (W[Never]) => Int32
  a6 : (W[#A(Never) | R1]) => Int32
  ⚠ match が非網羅的です。例えば Wr(_, false) が漏れています
  a7 : (W[#A(Never)]) => Int32

値を持つかどうかを調べ終えたデータ型は、1 回の判定の中で結果を記録し、たどり直さない。deep.kel の
T0 から T31 は、2 つのコンストラクタがどちらも次の番号の型を引数に持ち、T32 は値を持たない型
だけを引数に持つ。たどり直すと 2 の 32 乗に比例する時間がかかる形だが、型検査は終了し、警告は出ない:

  $ { echo 'newtype Empt'
  >   for i in $(seq 0 31); do echo "newtype T$i = A$i(T$((i+1))) | B$i(T$((i+1)))"; done
  >   echo 'newtype T32 = A32(Empt) | B32(Empt)'
  >   echo 'let f(A0(x)) = 1'; } > deep.kel
  $ diktor --type-check --no-prelude deep.kel
  f : (T0) => Int32
