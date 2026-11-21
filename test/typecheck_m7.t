型クラスのユーザ宣言の型検査のゴールデンテストである。
期待出力を変えるときは、差分を目で確かめてから dune promote で更新する。

sample.kel §8 の例(クラス宣言、インスタンス、fma、メソッドが固有の型パラメータを持つ
高カインド型のクラスの宣言と、let rec で書いたインスタンス)。
Add、Mul、Eq とそのインスタンスは、宣言せずに組み込みのものを使う:

  $ cat > cls.kel <<'EOF'
  > type Unit = {}
  > type Point = {x: Float64, y: Float64}
  > newtype List[A] = Nil | Cons(A, tail: List[A])
  > extern "prim" let __int32_add(x: Int32, y: Int32): Int32
  > extern "prim" let __int32_mul(x: Int32, y: Int32): Int32
  > extern "prim" let __string_concat(x: String, y: String): String
  > let fma[A: Add + Mul](x: A, y: A, z: A): A = x * y + z
  > let same_point(p: Point, q: Point): Boolean = p == q
  > type class MyShow[A] { val myshow: (A) => String }
  > type instance MyShow[Boolean] {
  >   let myshow(b) = b match { case true => "true" case false => "false" }
  > }
  > let use_myshow = myshow(true)
  > let generic_show = fn(x) => myshow(x)
  > type class Functor[F[_]] {
  >   val map[A, B, E]: (F[A], (A) => B @ E) => F[B] @ E
  > }
  > type instance Functor[List[_]] {
  >   let rec map[A, B, E](xs: List[A], f: (A) => B @ E): List[B] @ E =
  >     xs match {
  >       case Nil              => Nil
  >       case Cons(head, tail) => Cons(f(head), map(tail, f))
  >     }
  > }
  > EOF
  $ diktor --type-check --no-prelude cls.kel
  __int32_add : (Int32, Int32) => Int32
  __int32_mul : (Int32, Int32) => Int32
  __string_concat : (String, String) => String
  fma : [A: Add + Mul] (A, A, A) => A
  same_point : ({x: Float64, y: Float64}, {x: Float64, y: Float64}) => Boolean
  use_myshow : String
  generic_show : [A: MyShow] (A) => String

注釈のない束縛でのクラス制約の推論。関数型は Show のインスタンスではないのでエラーになる:

  $ cat > ml9.kel <<'EOF'
  > let s = show(42)
  > let f = fn(x) => show(x)
  > let cmp = fn(x) => lt(x, x)
  > let bad = show(fn(x) => x)
  > EOF
  $ diktor --type-check --no-prelude ml9.kel
  s : String
  f : [A: Show] (A) => String
  cmp : [A: Ord] (A) => Boolean
  ! ml9.kel:4:16: 型エラー: (_A) => _A は Show のインスタンスではありません
  [1]

返り値にだけクラスパラメータが現れるメソッドを宣言できる。どのインスタンスのメソッドかは
型検査が型から決めるので、注釈か結果を使う位置が F を決めればよい(使用例は
test/dictionary_passing.t の pure と pureamb にある):

  $ cat > c2.kel <<'EOF'
  > newtype Box[A] = Box(A)
  > type class Pure[F[_]] { val pure[A]: (A) => F[A] }
  > EOF
  $ diktor --type-check --no-prelude c2.kel

エラーになる宣言(インスタンスの二重宣言、メソッドの型の不一致、メソッドの漏れ、複数のパラメータ、予約述語):

  $ cat > c1.kel <<'EOF'
  > type class C[A] { val f: (A) => A }
  > type instance C[Int32] { let f(x) = x }
  > type instance C[Int32] { let f(x) = x }
  > EOF
  $ diktor --type-check --no-prelude c1.kel
  ! c1.kel:3:1: 型エラー: インスタンス C[Int32] が二重に宣言されています(コヒーレンス違反)
  [1]

  $ cat > c3.kel <<'EOF'
  > type class C[A] { val f: (A) => A }
  > type instance C[Int32] { let f(x) = x == x }
  > EOF
  $ diktor --type-check --no-prelude c3.kel
  ! c3.kel:2:30: 型エラー: インスタンスメソッド f がクラス宣言の型を満たしません(型が一致しません: Boolean と Int32)
  [1]

  $ cat > c4.kel <<'EOF'
  > type class C[A] {
  >   val f: (A) => A
  >   val g: (A) => A
  > }
  > type instance C[Int32] { let f(x) = x }
  > EOF
  $ diktor --type-check --no-prelude c4.kel
  ! c4.kel:5:1: 型エラー: インスタンスがメソッドを網羅していません: g が漏れています
  [1]

  $ cat > c5.kel <<'EOF'
  > type class C[A, B] { val f: (A) => B }
  > EOF
  $ diktor --type-check --no-prelude c5.kel
  ! c5.kel:1:1: 型エラー: type class のパラメータは1個です(多パラメータ型クラスは意図的に排除、sample.kel:356)
  [1]

  $ cat > c6.kel <<'EOF'
  > type class Integral[A] { val toi: (A) => Int32 }
  > EOF
  $ diktor --type-check --no-prelude c6.kel
  ! c6.kel:1:1: 型エラー: Integral は予約されたリテラル述語です(ユーザ宣言不可、D8)
  [1]

予約述語は、インスタンス宣言でも拒否する。受理すると、ユーザのインスタンスが
数値リテラルの制約の解決に使われる:

  $ printf 'type instance Integral[String] { }\n' > c7.kel
  $ diktor --type-check --no-prelude c7.kel
  ! c7.kel:1:1: 型エラー: Integral は予約されたリテラル述語です(インスタンスは宣言できません、D8)
  [1]

  $ printf 'type instance Fractional[String] { }\n' > c8.kel
  $ diktor --type-check --no-prelude c8.kel
  ! c8.kel:1:1: 型エラー: Fractional は予約されたリテラル述語です(インスタンスは宣言できません、D8)
  [1]

型パラメータの制約に書いた未知のクラスは、宣言の時点でエラーにする。
関数の型パラメータでも、クラスのメソッドの型パラメータでも同じである:

  $ printf 'let f[A: Bogus](x: A): A = x\n' > c9.kel
  $ diktor --type-check --no-prelude c9.kel
  ! c9.kel:1:5: 型エラー: 未知のクラス: Bogus
  [1]

  $ printf 'type class C3[A] { val m[B: Bogus]: (A, B) => A }\n' > c10.kel
  $ diktor --type-check --no-prelude c10.kel
  ! c10.kel:1:1: 型エラー: 未知のクラス: Bogus
  [1]

制約のクラスは後ろで宣言していてもよい。制約の検査は、すべてのクラスを登録した後に行う:

  $ cat > c11.kel <<'KEL'
  > let uses2[A: Later2](x: A): A = lm2(x)
  > type class Later2[A] { val lm2: (A) => A }
  > KEL
  $ diktor --type-check --no-prelude c11.kel
  uses2 : [A: Later2] (A) => A

予約述語は、--prelude で渡したプレリュードのインスタンス宣言、型パラメータの制約、
クラスのメソッドの制約でも拒否する:

  $ printf 'type instance Integral[String] { }\n' > pre_evil.kel
  $ printf 'let s: String = 1\n' > main1.kel
  $ diktor --prelude pre_evil.kel --type-check main1.kel
  ! pre_evil.kel:1:1: 型エラー: Integral は予約されたリテラル述語です(インスタンスは宣言できません、D8)
  [1]

  $ printf 'let f[A: Integral](): A = 1\n' > c12.kel
  $ diktor --type-check c12.kel
  ! c12.kel:1:5: 型エラー: Integral は予約されたリテラル述語です(制約には書けません、D8)
  [1]

  $ printf 'type class C4[A] { val m[B: Fractional]: (A, B) => A }\n' > c13.kel
  $ diktor --type-check c13.kel
  ! c13.kel:1:1: 型エラー: Fractional は予約されたリテラル述語です(制約には書けません、D8)
  [1]

インスタンスの対象の型が未知の型でも、予約述語であることを先に報告する:

  $ printf 'type instance Integral[Nope] { }\n' > c14.kel
  $ diktor --type-check --no-prelude c14.kel
  ! c14.kel:1:1: 型エラー: Integral は予約されたリテラル述語です(インスタンスは宣言できません、D8)
  [1]

同じクラスの中でメソッドを二重に宣言するとエラーになる。受理すると、型検査は最後の宣言の
型を使い、インスタンスとの照合は最初の宣言を使うので、型と実行時の動作が食い違う:

  $ cat > c15.kel <<'KEL'
  > type class C5[A] { val f: (A) => Int32
  >  val f: (A) => String }
  > KEL
  $ diktor --type-check --no-prelude c15.kel
  ! c15.kel:2:9: 型エラー: メソッド f が二重に宣言されています
  [1]

module の中の let は、同じ module の let と自分自身を、修飾せずに参照できる
(module の中では、修飾しない名前が値の別名として登録されている):

  $ cat > modref.kel <<'KEL'
  > module M {
  >   let helper(x: Int32): Int32 = x + 1
  >   pub let use(x: Int32): Int32 = helper(x) + 1
  >   pub let rec down(n: Int32): Int32 = n match { case 0 => 0 case _ => down(n - 1) }
  > }
  > echoln(show(M.use(1)))
  > echoln(show(M.down(3)))
  > KEL
  $ diktor modref.kel
  3
  0

module の中の名前がトップレベルの名前と同じなら、宣言の時点で拒否する。
受理してどちらかを優先すると、型検査は宣言の時点の環境を、評価器は
呼び出しの時点の環境を参照するので、宣言の順序と呼び出しの時点によっては、
両者が別の宣言を選ぶことになる:

  $ cat > modshadow.kel <<'KEL'
  > let helper(x: Int32): Int32 = 100
  > module M {
  >   let helper(x: Int32): Int32 = x + 1
  >   let use(x: Int32): Int32 = helper(x)
  > }
  > echoln(show(M.use(1)))
  > KEL
  $ diktor modshadow.kel
  ! modshadow.kel:3:3: 型エラー: module M の helper はトップレベルの helper と同名です(module 内の名前とトップレベル名は同名にできません)
  [1]

2 つの module が同じ名前を公開すると、修飾しない名前は曖昧なのでエラーになる。修飾すれば使える:

  $ cat > modclash.kel <<'KEL'
  > module A { pub newtype T = TA(Int32) }
  > module B { pub newtype T = TB(Int32) }
  > let x: T = TA(1)
  > KEL
  $ diktor --type-check modclash.kel
  ! modclash.kel:3:8: 型エラー: 未知の型: T(A.T か B.T と修飾してください)
  [1]

  $ cat > modclash2.kel <<'KEL'
  > module A { pub newtype T = TA(Int32) }
  > module B { pub newtype T = TB(Int32) }
  > let x: A.T = TA(1)
  > let y: B.T = TB(2)
  > echoln(show(x match { case TA(n) => n }) + show(y match { case TB(n) => n }))
  > KEL
  $ diktor modclash2.kel
  12

  $ cat > modclash3.kel <<'KEL'
  > module A { pub let f(x: Int32): Int32 = x + 1 }
  > module B { pub let f(x: Int32): Int32 = x + 2 }
  > echoln(show(A.f(1)) + show(B.f(1)))
  > KEL
  $ diktor modclash3.kel
  23

組み込みのスカラー型の名前は、型エイリアスでも再宣言できない(newtype と同じ検査):

  $ printf 'type Float64 = String\n' > v2alias.kel
  $ diktor --type-check v2alias.kel
  ! v2alias.kel:1:1: 型エラー: 組み込み型 Float64 は型エイリアスで再宣言できません
  [1]

module の値の修飾しない名前が曖昧なときは、修飾名を示す。
型の診断「A.T か B.T と修飾してください」と同じ形式である:

  $ cat > vamb.kel <<'EOF2'
  > module A { pub let down(n: Int32): Int32 = n + 1 }
  > module B { pub let down(n: Int32): Int32 = n }
  > echoln(show(down(3)))
  > EOF2
  $ diktor --type-check vamb.kel
  A.down : (Int32) => Int32 @ {}
  B.down : (Int32) => Int32 @ {}
  ! vamb.kel:3:13: 型エラー: 未束縛の変数: down(A.down か B.down と修飾してください)
  [1]

コンストラクタのシグネチャが完全かどうかの判定(第10章 §10.10 の sig_complete)。コンストラクタが 0 個の Never は、
節のない match で網羅される。照合対象の型のコンストラクタを 1 つも書いていない match は、ワイルドカードの節で判定する:

  $ cat > sigc.kel <<'KEL'
  > let absurd[A](n: Never): A = n match {}
  > let allwild = fn(b: Boolean) => b match { case _ => 0 }
  > KEL
  $ diktor --type-check --no-prelude sigc.kel
  absurd : (Never) => A
  allwild : (Boolean) => Int32

網羅性の警告は、宣言をまたいでソースの順に並ぶ(第10章 §10.13 の検査キュー)。
1 つの宣言の中では、引数のパターンの警告が本体の警告の後に出る:

  $ cat > warnorder.kel <<'KEL'
  > let a = fn(x: Boolean) => x match { case true => 1 }
  > let b = fn(p: (Boolean, Boolean)) => p match { case (true, true) => 1  case (false, false) => 2 }
  > let c = fn(x: Int32) => x match { case 0 => 1  case 1 => 2 }
  > let d = fn(x: Boolean) => x match { case true => 1  case false => 2  case _ => 3 }
  > KEL
  $ diktor --type-check --no-prelude warnorder.kel
  a : (Boolean) => Int32
  ⚠ match が非網羅的です。例えば false が漏れています
  b : ((Boolean, Boolean)) => Int32
  ⚠ match が非網羅的です。例えば (true, false) が漏れています
  c : (Int32) => Int32
  ⚠ match が非網羅的です。例えば 2 が漏れています
  d : (Boolean) => Int32
  ⚠ 第 3 節は到達不能です(冗長)

反例の組み立て。漏れている値を、コンストラクタの引数をそろえた形に組み立て直して示す(第10章 §10.8 の rebuild)。
位置で書いたフィールドと名前付きのフィールドのコンストラクタを並べ、最初に見つかる Seg(false, true) を示す:

  $ cat > rebuild.kel <<'KEL'
  > newtype Shape = Dot | Seg(Boolean, Boolean) | Box(w: Boolean, h: Boolean)
  > let f = fn(s: Shape) => s match {
  >   case Dot => 0
  >   case Seg(true, true) => 1
  >   case Box(w = true, h = true) => 2
  > }
  > KEL
  $ diktor --type-check --no-prelude rebuild.kel
  f : (Shape) => Int32
  ⚠ match が非網羅的です。例えば Seg(false, true) が漏れています

関数の引数と return 節に書いた、一致しない値のあるパターンも網羅性検査に掛ける。
検査しないと、型検査に通ったプログラムが実行時に
「パターンに値が一致しません」で終了する:

  $ cat > v10.kel <<'KEL'
  > let g(true: Boolean): Int32 = 1
  > let h = fn(0) => 1
  > KEL
  $ diktor --type-check --no-prelude v10.kel
  g : (Boolean) => Int32
  ⚠ match が非網羅的です。例えば false が漏れています
  h : (Int32) => Int32
  ⚠ match が非網羅的です。例えば 1 が漏れています

  $ cat > v10b.kel <<'KEL'
  > newtype Pair = P(Boolean, Boolean)
  > let f(P(true, b): Pair): Boolean = b
  > KEL
  $ diktor --type-check --no-prelude v10b.kel
  f : (Pair) => Boolean
  ⚠ match が非網羅的です。例えば P(false, true) が漏れています

  $ cat > v10c.kel <<'KEL'
  > effect E1 = { op1: () => Boolean }
  > let f(): Int32 @ {} = (perform op1()) handle {
  >   case op1() => resume(true)
  >   case return(true) => 1
  > }
  > KEL
  $ diktor --type-check v10c.kel
  f : () => Int32 @ {}
  ⚠ match が非網羅的です。例えば false が漏れています

検査モードで検査する無名関数(注釈のある高階関数の引数の位置に書いたもの)の
引数のパターンも、推論モードのときと同じく
網羅性検査に掛ける:

  $ cat > v10d.kel <<'KEL'
  > let apply2(f: (Boolean) => Int32, b: Boolean): Int32 = f(b)
  > let r = apply2(fn(true) => 1, false)
  > KEL
  $ diktor --type-check v10d.kel
  apply2 : ((Boolean) => Int32 @ {}, Boolean) => Int32
  r : Int32
  ⚠ match が非網羅的です。例えば false が漏れています

引数と return 節のパターンの検査は、本体の推論より後に検査キューに入れる。
先に入れると、本体の中の let がキューを処理するときにこの検査も実行されて、行が早く閉じ、
受理するべきプログラムが型エラーになる:

  $ cat > v10e.kel <<'KEL'
  > let g(t: #A | #B | #C): Int32 = t match { case #A => 1  case #B => 2  case #C => 3 }
  > let rec f(#A) = 1
  > and h(v) = { let z = f(v); g(v) }
  > KEL
  $ diktor --type-check --no-prelude v10e.kel
  g : (#A | #B | #C) => Int32
  f : (#A | #B | #C) => Int32
  h : (#A | #B | #C) => Int32
  ⚠ match が非網羅的です。例えば #B(_) が漏れています

  $ cat > v10f.kel <<'KEL'
  > effect Nop = { nop: () => Int32 }
  > let g(t: #A | #B | #C): Int32 = t match { case #A => 1  case #B => 2  case #C => 3 }
  > let f(v) = v handle {
  >   case nop() => resume(1)
  >   case return(#A) => { let z = 1; g(v) }
  > }
  > KEL
  $ diktor --type-check --no-prelude v10f.kel
  g : (#A | #B | #C) => Int32
  f : (#A | #B | #C) => Int32
  ⚠ match が非網羅的です。例えば #B(_) が漏れています

パターンが 1 つだけの位置には節がないので、警告に節の番号を出さない:

  $ cat > v10g.kel <<'KEL'
  > newtype Empt
  > newtype Opt2[A] = Sm(A) | Nn
  > let f(Sm(x): Opt2[Empt]) = 1
  > KEL
  $ diktor --type-check --no-prelude v10g.kel
  f : (Opt2[Empt]) => Int32
  ⚠ match が非網羅的です。例えば Nn が漏れています
  ⚠ このパターンには一致する値がありません

関数の引数と無名関数の引数に書いたコンストラクタパターンは、
コンストラクタが 1 つしかない型のものでも網羅性検査に掛ける。
v10h の Absurd は、フィールドの型 Empt が値を持たないので値を持たず、引数に値が来ないので、
f と g に警告は出ない(値を持たない型を受けるパターンの扱いは uninhabited_pattern.t)。
v10hp の P = MkP(Opt2[Int32]) には値があり、MkP(Sm(n)) で受ける f と g のそれぞれに
MkP(Nn) の漏れを警告する。この警告から、検査に掛けていることが分かる:

  $ cat > v10h.kel <<'KEL'
  > newtype Empt
  > newtype Absurd = MkA(Empt)
  > let f(MkA(n)) = 1
  > let g = fn(MkA(n)) => 2
  > KEL
  $ diktor --type-check --no-prelude v10h.kel
  f : (Absurd) => Int32
  g : (Absurd) => Int32
  $ cat > v10hp.kel <<'KEL'
  > newtype Opt2[A] = Sm(A) | Nn
  > newtype P = MkP(Opt2[Int32])
  > let f(MkP(Sm(n))) = 1
  > let g = fn(MkP(Sm(n))) => 2
  > KEL
  $ diktor --type-check --no-prelude v10hp.kel
  f : (P) => Int32
  ⚠ match が非網羅的です。例えば MkP(Nn) が漏れています
  g : (P) => Int32
  ⚠ match が非網羅的です。例えば MkP(Nn) が漏れています
