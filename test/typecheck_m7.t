M7(型クラスのユーザ宣言)のゴールデン。
変更時は dune promote で更新し、必ず目視レビューすること。

sample.kel §8 の一式(クラス宣言・インスタンス・fma・derive structural・
メソッド固有型パラメータ付き HKT クラスの宣言と let rec インスタンス)。
Add / Eq は組み込みと同名なので「照合の上で受理」される(実体は組み込み):

  $ cat > cls.kel <<'EOF'
  > type Unit = {}
  > type Point = {x: Float64, y: Float64}
  > newtype List[A] = Nil | Cons(A, tail: List[A])
  > extern "prim" let __int32_add(x: Int32, y: Int32): Int32
  > extern "prim" let __int32_mul(x: Int32, y: Int32): Int32
  > extern "prim" let __string_concat(x: String, y: String): String
  > type class Add[A] { val add: (A, A) => A }
  > type class Mul[A] { val mul: (A, A) => A }
  > type instance Add[Int32]  { let add(x, y) = __int32_add(x, y) }
  > type instance Mul[Int32]  { let mul(x, y) = __int32_mul(x, y) }
  > type instance Add[String] { let add(x, y) = __string_concat(x, y) }
  > let fma[A: Add + Mul](x: A, y: A, z: A): A = x * y + z
  > type class Eq[A] {
  >   val eq: (A, A) => Boolean
  >   derive structural
  > }
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

MiniLang §16-9(クラス制約、注釈なし。read 系は v1 の曖昧性検査待ちで除外):

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
  ! 型エラー: (_A) => _A は Show のインスタンスではありません
  [1]

エラー経路(コヒーレンス / v0 出現位置制約 / 型不一致 / 網羅 / 多パラメータ / 予約述語):

  $ cat > c1.kel <<'EOF'
  > type class C[A] { val f: (A) => A }
  > type instance C[Int32] { let f(x) = x }
  > type instance C[Int32] { let f(x) = x }
  > EOF
  $ diktor --type-check --no-prelude c1.kel
  ! 型エラー: インスタンス C[Int32] が二重に宣言されています(コヒーレンス違反)
  [1]

  $ cat > c2.kel <<'EOF'
  > newtype Box[A] = Box(A)
  > type class Pure[F[_]] { val pure[A]: (A) => F[A] }
  > EOF
  $ diktor --type-check --no-prelude c2.kel
  ! 型エラー: メソッド pure はクラスパラメータが引数位置に現れないため v0 では宣言できません(実行時ディスパッチの前提、§7.4)
  [1]

  $ cat > c3.kel <<'EOF'
  > type class C[A] { val f: (A) => A }
  > type instance C[Int32] { let f(x) = x == x }
  > EOF
  $ diktor --type-check --no-prelude c3.kel
  ! 型エラー: インスタンスメソッド f がクラス宣言の型を満たしません(型が一致しません: Boolean と Int32)
  [1]

  $ cat > c4.kel <<'EOF'
  > type class C[A] {
  >   val f: (A) => A
  >   val g: (A) => A
  > }
  > type instance C[Int32] { let f(x) = x }
  > EOF
  $ diktor --type-check --no-prelude c4.kel
  ! 型エラー: インスタンスがメソッドを網羅していません: g が漏れています
  [1]

  $ cat > c5.kel <<'EOF'
  > type class C[A, B] { val f: (A) => B }
  > EOF
  $ diktor --type-check --no-prelude c5.kel
  ! 型エラー: type class のパラメータは1個です(多パラメータ型クラスは意図的に排除、sample.kel:275)
  [1]

  $ cat > c6.kel <<'EOF'
  > type class Integral[A] { val toi: (A) => Int32 }
  > EOF
  $ diktor --type-check --no-prelude c6.kel
  ! 型エラー: Integral は予約されたリテラル述語です(ユーザ宣言不可、D8)
  [1]
