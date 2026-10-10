型クラスの辞書渡し(LangSpec §6.2、§12.1。M60)。制約付きの束縛は辞書を
引数に取る関数になり、辞書は呼ぶ側の型から型検査が決める。高階カインドのクラス、
返り値型にだけクラスパラメータが現れるメソッド、構造的な等価、再帰群、前方参照と、
辞書が決まらない場合の曖昧性エラーを確かめる。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

高階カインドのクラス Applicative。pure の型 (A) => F[A] は引数に F が現れないので、
F は注釈が要求する型から決まる。o と l は同じ pure から別のインスタンスを選ぶ:

  $ cat > pure.kel <<'KEL'
  > type class Applicative[F[_]] {
  >   val pure[A]: (A) => F[A]
  >   val ap[A, B, E]: (F[(A) => B @ E], F[A]) => F[B] @ E
  > }
  > type instance Applicative[Option[_]] {
  >   let pure(x) = Some(x)
  >   let ap(f, x) = (f, x) match {
  >     case (Some(g), Some(v)) => Some(g(v))
  >     case _ => None
  >   }
  > }
  > type instance Applicative[List[_]] {
  >   let pure(x) = Cons(x, Nil)
  >   let ap(fs, xs) = fs match {
  >     case Nil => Nil
  >     case Cons(g, _) => xs match { case Nil => Nil case Cons(v, _) => Cons(g(v), Nil) }
  >   }
  > }
  > let o: Option[Int32] = pure(1)
  > let l: List[String] = pure("a")
  > echoln(show(o))
  > echoln(show(l))
  > echoln(show(ap(pure(fn(x: Int32) => x + 1), o)))
  > KEL
  $ diktor pure.kel
  Some(1)
  [a]
  Some(2)

[F[_]: Applicative] の制約を持つ関数は、高階カインドの辞書を引数に受け取り、
中で呼ぶ pure と ap にそのまま渡す:

  $ cat > lift2.kel <<'KEL'
  > type class Applicative[F[_]] {
  >   val pure[A]: (A) => F[A]
  >   val ap[A, B, E]: (F[(A) => B @ E], F[A]) => F[B] @ E
  > }
  > type instance Applicative[Option[_]] {
  >   let pure(x) = Some(x)
  >   let ap(f, x) = (f, x) match {
  >     case (Some(g), Some(v)) => Some(g(v))
  >     case _ => None
  >   }
  > }
  > let lift2[F[_]: Applicative, A, B, C](f: (A, B) => C, x: F[A], y: F[B]): F[C] =
  >   ap(ap(pure(fn(a: A) => fn(b: B) => f(a, b)), x), y)
  > echoln(show(lift2(fn(a: Int32, b: Int32) => a * b, Some(6), Some(7))))
  > echoln(show(lift2(fn(a: Int32, b: Int32) => a * b, Some(6), None)))
  > KEL
  $ diktor lift2.kel
  Some(42)
  None

注釈の無い let a = pure(1) は一般化しない束縛で、ファイルの終わりまでに F が
決まらないので曖昧性エラーになる:

  $ cat > pureamb.kel <<'KEL'
  > type class Applicative[F[_]] {
  >   val pure[A]: (A) => F[A]
  > }
  > type instance Applicative[Option[_]] { let pure(x) = Some(x) }
  > let a = pure(1)
  > KEL
  $ diktor pureamb.kel
  ! pureamb.kel:5:9: 型エラー: 曖昧な制約: Applicative を満たす型が決まりません(一般化しない束縛か式文の型変数です。注釈で型を決めてください)
  [1]

同じ束縛でも、後ろの束縛が型を決めれば曖昧ではない。a は弱い型変数を持つ型として
表示され、b の注釈で Option に決まる:

  $ cat > purelater.kel <<'KEL'
  > type class Applicative[F[_]] {
  >   val pure[A]: (A) => F[A]
  > }
  > type instance Applicative[Option[_]] { let pure(x) = Some(x) }
  > let a = pure(1)
  > let b: Option[Int32] = a
  > KEL
  $ diktor --type-check purelater.kel
  a : [_F: Applicative] _F[Int32]
  b : Option[Int32]

クラスパラメータが返り値型にだけ現れるメソッド read。注釈、+ の相手、&& の
オペランドが型を決める。制約 Read + Add を持つ関数の中でも辞書が決まる:

  $ cat > read.kel <<'KEL'
  > type class Read[A] { val read: (String) => A }
  > type instance Read[Int32] { let read(s) = 42 }
  > type instance Read[Boolean] { let read(s) = true }
  > let n: Int32 = read("1")
  > let b = read("t") && false
  > echoln(show(n + read("2")))
  > echoln(show(b))
  > let twice[A: Read + Add](s: String): A = read(s) + read(s)
  > let t: Int32 = twice("x")
  > echoln(show(t))
  > KEL
  $ diktor read.kel
  84
  false
  84

メソッドが自分の制約 [B: Show] を持つ。B の辞書は呼ぶ位置ごとに渡され、
前提付きのインスタンス Pp[Option[_]] の中から再帰的に pp を呼んでも届く:

  $ cat > ownconstraint.kel <<'KEL'
  > type class Pp[A] { val pp[B: Show]: (A, B) => String }
  > newtype Foo = Foo
  > type instance Pp[Foo] { let pp(a, b) = "Foo:" + show(b) }
  > type instance[A: Pp] Pp[Option[_]] { let pp(o, b) = o match { case Some(x) => "S(" + pp(x, b) + ")" case None => "N" } }
  > echoln(pp(Foo, 3))
  > echoln(Pp.pp(Foo, "x"))
  > echoln(pp(Some(Some(Foo)), 3))
  > let g[A: Pp](a: A): String = pp(a, true)
  > echoln(g(Foo))
  > KEL
  $ diktor ownconstraint.kel
  Foo:3
  Foo:x
  S(S(Foo:3))
  Foo:true

構造的な等価(==)。ラベルの順の違うレコードは等しく、タプルの要素とヴァリアントの
ペイロードは要素の型の Eq を使う(Box の eq は常に true)。[A: Eq] の関数の中で
{v = x} を比べると、A の辞書がレコードの等価に渡る:

  $ cat > structeq.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type instance Eq[Box] { let eq(a, b) = true }
  > echoln(show({p = 1, q = "a"} == {q = "a", p = 1}))
  > echoln(show((1, Box(1)) == (1, Box(2))))
  > let va: #A(Int32) | #B(String) = #A(1)
  > echoln(show(va == #A(1)))
  > echoln(show(va == #B("x")))
  > let f[A: Eq](x: A, y: A): Boolean = {v = x} == {v = y}
  > echoln(show(f(Box(1), Box(3))))
  > echoln(show(f(Cons(1, Nil), Cons(2, Nil))))
  > KEL
  $ diktor structeq.kel
  true
  true
  true
  false
  true
  false

局所の多相関数 both は外側の辞書(A の Show)を捕まえたまま、自分の型変数は呼ぶ位置で
決める。再帰群 sa と sr では、sr が sa の辞書を受け渡す:

  $ cat > localpoly.kel <<'KEL'
  > let outer[A: Show](x: A): String = {
  >   let both(y) = show(y) + "/" + show(x)
  >   both(1) + " " + both(true)
  > }
  > echoln(outer("s"))
  > let rec sa[A: Show](xs: List[A]): String = xs match { case Nil => "." case Cons(h, t) => show(h) + sr(t) }
  > and sr(t) = sa(t)
  > echoln(sa(Cons(1, Cons(2, Nil))))
  > KEL
  $ diktor localpoly.kel
  1/s true/s
  12.

制約付きの型パラメータを注釈で明示した再帰群。g の中で f を Int32 と Boolean の
2 つの型で使えるのは、f の型パラメータ A がほかの束縛の型に流れ込まず、f の本体の
検査の後に解放されるからである(LangSpec §6.3)。h と i では h の型パラメータが i の
引数の型に流れ込んで群の終わりまで残り、i を通して同じ辞書が回る:

  $ cat > recpub.kel <<'KEL'
  > let rec f[A: Show](x: A): String @ {} = show(x)
  > and g(n: Int32): String = f(n) + f(true)
  > echoln(g(3))
  > let rec h[A: Show](x: A, k: Int32): String @ {} = (k == 0) match { case true => show(x) case false => i(x, k - 1) }
  > and i(y, k: Int32): String = h(y, k)
  > echoln(h("z", 3))
  > KEL
  $ diktor recpub.kel
  3true
  z

再帰群の中の参照が要る辞書を、呼ぶ側の束縛の型から決められなければ曖昧性エラー。
f の中の g(???) と g(Nil) は、g の引数の型が f の型に現れない:

  $ cat > recamb.kel <<'KEL'
  > let rec f(): Int32 = { let _ = g(???); 0 }
  > and g(y) = show(y)
  > KEL
  $ diktor recamb.kel
  ! recamb.kel:1:32: 型エラー: 曖昧な制約: 再帰群の中のこの参照が要る辞書を、呼ぶ側の束縛の型から決められません(注釈で型を決めてください)
  [1]
  $ cat > recamb2.kel <<'KEL'
  > let rec f(): String = g(Nil)
  > and g(ys) = show(ys)
  > echoln(f())
  > KEL
  $ diktor recamb2.kel
  ! recamb2.kel:1:23: 型エラー: 曖昧な制約: 再帰群の中のこの参照が要る辞書を、呼ぶ側の束縛の型から決められません(注釈で型を決めてください)
  [1]

制約付きの型パラメータが束縛の型に現れなければ、呼ぶ側はその辞書を決められない。
本体での使い方によらず、宣言の時点で曖昧性エラーになる。extern の宣言も同じ:

  $ cat > tpabsent.kel <<'KEL'
  > let f[A: Show](): String = { let y: A = ???; show(y) }
  > KEL
  $ diktor tpabsent.kel
  ! tpabsent.kel:1:5: 型エラー: 曖昧な制約: 型パラメータ A の制約 Show を束縛の型から決められません(束縛の型に現れない型パラメータに制約が付いています)
  [1]
  $ cat > tpabsent2.kel <<'KEL'
  > let f[A: Show](): String = { let y: List[A] = Nil; show(y) }
  > echoln(f())
  > KEL
  $ diktor tpabsent2.kel
  ! tpabsent2.kel:1:5: 型エラー: 曖昧な制約: 型パラメータ A の制約 Show を束縛の型から決められません(束縛の型に現れない型パラメータに制約が付いています)
  [1]
  $ cat > tpabsent3.kel <<'KEL'
  > let f[A: Show](): Int32 = 0
  > echoln(show(f()))
  > KEL
  $ diktor tpabsent3.kel
  ! tpabsent3.kel:1:5: 型エラー: 曖昧な制約: 型パラメータ A の制約 Show を束縛の型から決められません(束縛の型に現れない型パラメータに制約が付いています)
  [1]
  $ cat > tpabsent4.kel <<'KEL'
  > extern "prim" let f[A: Show](x: Int32): Int32
  > KEL
  $ diktor tpabsent4.kel
  ! tpabsent4.kel:1:1: 型エラー: 曖昧な制約: 型パラメータ A の制約 Show を束縛の型から決められません(束縛の型に現れない型パラメータに制約が付いています)
  [1]

型にクラスパラメータが現れないメソッドは、どのインスタンスのものかを型から決められない
ので、クラスの宣言で型エラーになる:

  $ cat > nooccur.kel <<'KEL'
  > type class C[A] { val f: (Int32) => Int32 }
  > KEL
  $ diktor nooccur.kel
  ! nooccur.kel:1:1: 型エラー: メソッド f の型にクラスパラメータが現れません(どのインスタンスのメソッドかを型から決められません)
  [1]

弱い型変数を持つ s の Show の辞書は、後ろの g で Foo に決まる。Foo のインスタンスが
s より後ろで宣言されていても、辞書はファイル全体を見て決まる:

  $ cat > weaklater.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let s = idf(show)
  > let g() = s(Foo)
  > newtype Foo = Foo
  > type instance Show[Foo] { let show(x) = "foo" }
  > echoln(g())
  > KEL
  $ diktor weaklater.kel
  foo

制約付きの extern を、制約付きの関数から呼ぶ。辞書の受け渡しは通り、実装の無い
プリミティブを呼んだ時点で実行時エラーになる:

  $ cat > externc.kel <<'KEL'
  > extern "prim" let foo[A: Show](x: A): String
  > let g[B: Show](y: B): String = foo(y)
  > echoln(g(1))
  > KEL
  $ diktor externc.kel
  実行時エラー: 未実装のプリミティブ: foo
  [3]

インスタンスのメソッドから、後ろで宣言する制約付きの関数を呼ぶ。helper2 は型パラメータの
順(B, A)と引数の型の中の出現順(A, B)が違うが、Eq と Show の辞書を取り違えない:

  $ cat > fwd.kel <<'KEL'
  > newtype Foo = Foo
  > type instance Show[Foo] { let show(x) = helper(1, "a") }
  > let user(): String = helper2(Foo, 2)
  > let helper[A: Show, B: Show](x: A, y: B): String @ {} = show(y) + show(x) + "!"
  > let helper2[B: Eq, A: Show](x: A, y: B): String @ {} = show(x) + show(y == y)
  > echoln(show(Foo))
  > echoln(user())
  > KEL
  $ diktor fwd.kel
  a1!
  a1!true

一般化する束縛(値)が制約を持つと、辞書を受け取る関数になり、本体は使うときに
評価される。p は使われないので ??? に到達しない。r は r.f(1) で辞書が決まり、その時点で
レコードを作るので ??? に到達する:

  $ cat > valhole.kel <<'KEL'
  > let p = (show, ???)
  > echoln("after")
  > KEL
  $ diktor valhole.kel
  after
  $ cat > valhole2.kel <<'KEL'
  > let r = {f = show, g = ???}
  > echoln("after")
  > echoln(r.f(1))
  > KEL
  $ diktor valhole2.kel
  after
  実行時エラー: ??? に到達しました
  [3]

インスタンスの本体の評価。前提付きのインスタンスは辞書を受け取る関数になるので、
使わなければ ??? に到達しない。前提の無いインスタンスは宣言の実行で本体を評価する:

  $ cat > insthole.kel <<'KEL'
  > newtype Box[A] = Box(A)
  > type instance[A: Show] Show[Box[_]] { let show = ??? }
  > echoln("after")
  > KEL
  $ diktor insthole.kel
  after
  $ cat > insthole2.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type instance Show[Box] { let show = ??? }
  > echoln("after")
  > KEL
  $ diktor insthole2.kel
  実行時エラー: ??? に到達しました
  [3]

式文の show は一般化して辞書を受け取る関数になり、評価しても何も起きない:

  $ cat > dexp.kel <<'KEL'
  > show
  > echoln("x")
  > KEL
  $ diktor dexp.kel
  x

前置の - と % は演算子クラス Neg と Rem のメソッドなので、[A: Neg] と [A: Rem] の
制約を持つ関数から呼べる。Neg は Int32、Int64、Float64、Rem は Int32 と Int64 で使う
(Float64 は Rem のインスタンスではない):

  $ cat > negrem.kel <<'KEL'
  > let negate[A: Neg](x: A): A = -x
  > let modulo[A: Rem](x: A, y: A): A = x % y
  > echoln(show(negate(7)))
  > echoln(show(negate(5i64)))
  > echoln(show(negate(1.5)))
  > echoln(show(modulo(7, 3)))
  > echoln(show(modulo(-7, 3)))
  > echoln(show(modulo(17i64, 5i64)))
  > KEL
  $ diktor negrem.kel
  -7
  -5
  -1.5
  1
  -1
  2
