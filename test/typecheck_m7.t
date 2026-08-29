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
  ! ml9.kel:4:16: 型エラー: (_A) => _A は Show のインスタンスではありません
  [1]

エラー経路(コヒーレンス / v0 出現位置制約 / 型不一致 / 網羅 / 多パラメータ / 予約述語):

  $ cat > c1.kel <<'EOF'
  > type class C[A] { val f: (A) => A }
  > type instance C[Int32] { let f(x) = x }
  > type instance C[Int32] { let f(x) = x }
  > EOF
  $ diktor --type-check --no-prelude c1.kel
  ! c1.kel:3:1: 型エラー: インスタンス C[Int32] が二重に宣言されています(コヒーレンス違反)
  [1]

  $ cat > c2.kel <<'EOF'
  > newtype Box[A] = Box(A)
  > type class Pure[F[_]] { val pure[A]: (A) => F[A] }
  > EOF
  $ diktor --type-check --no-prelude c2.kel
  ! c2.kel:2:1: 型エラー: メソッド pure はクラスパラメータが引数の頭に現れないため v0 では宣言できません(実行時タグディスパッチの前提、§7.4)
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
  ! c5.kel:1:1: 型エラー: type class のパラメータは1個です(多パラメータ型クラスは意図的に排除、sample.kel:275)
  [1]

  $ cat > c6.kel <<'EOF'
  > type class Integral[A] { val toi: (A) => Int32 }
  > EOF
  $ diktor --type-check --no-prelude c6.kel
  ! c6.kel:1:1: 型エラー: Integral は予約されたリテラル述語です(ユーザ宣言不可、D8)
  [1]

予約述語はインスタンス宣言側の入口でも拒否される(D8。かつては素通りして
制約解決に使われた):

  $ printf 'type instance Integral[String] { }\n' > c7.kel
  $ diktor --type-check --no-prelude c7.kel
  ! c7.kel:1:1: 型エラー: Integral は予約されたリテラル述語です(インスタンスは宣言できません、D8)
  [1]

  $ printf 'type instance Fractional[String] { }\n' > c8.kel
  $ diktor --type-check --no-prelude c8.kel
  ! c8.kel:1:1: 型エラー: Fractional は予約されたリテラル述語です(インスタンスは宣言できません、D8)
  [1]

型パラメータ制約の未知クラスは宣言時に落ちる(かつては宣言の印字が出てから
使用点で落ち、クラスメソッド側は一切落ちなかった):

  $ printf 'let f[A: Bogus](x: A): A = x\n' > c9.kel
  $ diktor --type-check --no-prelude c9.kel
  ! c9.kel:1:5: 型エラー: 未知のクラス: Bogus
  [1]

  $ printf 'type class C3[A] { val m[B: Bogus]: (A, B) => A }\n' > c10.kel
  $ diktor --type-check --no-prelude c10.kel
  ! c10.kel:1:1: 型エラー: 未知のクラス: Bogus
  [1]

制約のクラスは後方で宣言されていてもよい(検査はクラス表が出揃ってから):

  $ cat > c11.kel <<'KEL'
  > let uses2[A: Later2](x: A): A = lm2(x)
  > type class Later2[A] { val lm2: (A) => A }
  > KEL
  $ diktor --type-check --no-prelude c11.kel
  uses2 : [A: Later2] (A) => A

予約述語は残りの入口でも拒否される(260829-5 検証修正。--prelude の
ユーザ製プレリュード・型パラメータ制約・クラスメソッドの制約):

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

インスタンス頭の書き方に関わらず、予約述語の拒否理由が最初に出る:

  $ printf 'type instance Integral[Nope] { }\n' > c14.kel
  $ diktor --type-check --no-prelude c14.kel
  ! c14.kel:1:1: 型エラー: Integral は予約されたリテラル述語です(インスタンスは宣言できません、D8)
  [1]

同一クラス内の重複メソッドを拒否(素通りすると elab は最後の宣言で
型付け、インスタンス照合は最初を見るので実行時に崩壊した):

  $ cat > c15.kel <<'KEL'
  > type class C5[A] { val f: (A) => Int32
  >  val f: (A) => String }
  > KEL
  $ diktor --type-check --no-prelude c15.kel
  ! c15.kel:1:1: 型エラー: メソッド f が二重に宣言されています
  [1]

newtype の型パラメータ制約も検証される(D6 の残り):

  $ printf 'newtype Box[A: Bogus] = Box(A)\n' > c16.kel
  $ diktor --type-check --no-prelude c16.kel
  ! c16.kel:1:1: 型エラー: 未知のクラス: Bogus
  [1]

プレリュード所有のエイリアス名の再宣言は黙って捨てられない(C1 の構造
照合が先に落ちる。かつては宣言ごと消えて exit 0 だった):

  $ printf 'type Unit[A: Bogus] = A\n' > c17.kel
  $ diktor --type-check c17.kel
  ! c17.kel:1:1: 型エラー: 型エイリアス Unit の宣言がプレリュードの宣言と一致しません(型パラメータの個数が違います: プレリュードは 0、宣言は 1)
  [1]

module 内 let の相互参照と自己再帰(C5a / D39。値の同義語のフォール
バック。かつては自己再帰すら「未束縛の変数」で落ちた):

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

module 内の名前とトップレベル名の衝突は宣言時に拒否する(M16 / D43。
かつては「外側が勝つ」フォールバックだったが、elab は宣言時点・評価器は
呼び出し時点の環境を見るため、宣言順と呼び出し時刻の組で解決が食い違い、
黙って別の実体を選んだ — M15 検証 V12):

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

同義語の衝突は曖昧(C5d / D39。かつては黙って後勝ち):

  $ cat > modclash.kel <<'KEL'
  > module A { newtype T = TA(Int32) }
  > module B { newtype T = TB(Int32) }
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

組み込みスカラー名はエイリアスでも奪えない(V2。newtype 側と同じ検査):

  $ printf 'type Float64 = String\n' > v2alias.kel
  $ diktor --type-check v2alias.kel
  ! v2alias.kel:1:1: 型エラー: 組み込み型 Float64 は型エイリアスで再宣言できません
  [1]

module の値の非修飾名が曖昧なとき、修飾名を案内する(D39 の値側。
型側の「A.T か B.T と修飾してください」と同じ形):

  $ cat > vamb.kel <<'EOF2'
  > module A { pub let down(n: Int32): Int32 = n + 1 }
  > module B { pub let down(n: Int32): Int32 = n }
  > echoln(show(down(3)))
  > EOF2
  $ diktor --type-check vamb.kel
  A.down : (Int32) => Int32
  B.down : (Int32) => Int32
  ! vamb.kel:3:13: 型エラー: 未束縛の変数: down(A.down か B.down と修飾してください)
  [1]
