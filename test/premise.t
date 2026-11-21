前提付きインスタンスのテストである(sample.kel の §8)。規則は sample.kel:411-421 に
書いてある。sample.kel:422-429 が示す形の Eq[List[_]] を、
--no-prelude で自前の List に対して書くと、型検査に通る:

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

  $ cat > pr.kel <<'EOF'
  > newtype List[A] = Cons(head: A, tail: List[A]) | Nil
  > type instance[A: Eq] Eq[List[_]] {
  >   let rec eq(xs, ys) = (xs, ys) match {
  >     case (Nil, Nil)                 => true
  >     case (Cons(x, xt), Cons(y, yt)) => x == y && eq(xt, yt)
  >     case _                          => false
  >   }
  > }
  > let same[A: Eq](xs: List[A], ys: List[A]): Boolean = xs == ys
  > let b = Cons(1i32, Cons(2i32, Nil)) == Cons(1i32, Nil)
  > EOF
  $ diktor --type-check --no-prelude pr.kel
  same : [A: Eq] (List[A], List[A]) => Boolean
  b : Boolean

前提は型引数に伝播する(unify.ml §8.4 の TCon の分岐の処理である):

  $ cat > pr2.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > newtype Opaque = MkOpaque(Int32)
  > type instance[A: Eq] Eq[List[_]] {
  >   let rec eq(xs, ys) = (xs, ys) match {
  >     case (Nil, Nil)                 => true
  >     case (Cons(x, xt), Cons(y, yt)) => x == y && eq(xt, yt)
  >     case _                          => false
  >   }
  > }
  > let ng = Cons(MkOpaque(1i32), Nil) == Cons(MkOpaque(1i32), Nil)
  > EOF
  $ diktor --type-check --no-prelude pr2.kel
  ! pr2.kel:10:10: 型エラー: Opaque は Eq のインスタンスではありません。List[Opaque] が Eq であるための前提として要求されました
  [1]

前提は、構造的な等値比較がたどるフィールドの型にも伝播する(レコードのフィールドが List[Opaque] である):

  $ cat > pr3.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > newtype Opaque = MkOpaque(Int32)
  > type instance[A: Eq] Eq[List[_]] {
  >   let rec eq(xs, ys) = (xs, ys) match {
  >     case (Nil, Nil)                 => true
  >     case (Cons(x, xt), Cons(y, yt)) => x == y && eq(xt, yt)
  >     case _                          => false
  >   }
  > }
  > let ok(p: {xs: List[Int32]}, q: {xs: List[Int32]}): Boolean = p == q
  > let ng(p: {xs: List[Opaque]}, q: {xs: List[Opaque]}): Boolean = p == q
  > EOF
  $ diktor --type-check --no-prelude pr3.kel
  ok : ({xs: List[Int32]}, {xs: List[Int32]}) => Boolean
  ! pr3.kel:11:65: 型エラー: Opaque は Eq のインスタンスではありません。List[Opaque] が Eq であるための前提として要求されました
  [1]

束縛子(インスタンスの型パラメータ)を書かないと、インスタンスの対象の型のカインドが、クラス Eq のパラメータのカインド Type と一致しない:

  $ cat > pr4.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance Eq[List[_]] { let rec eq(xs, ys) = true }
  > EOF
  $ diktor --type-check --no-prelude pr4.kel
  ! pr4.kel:2:1: 型エラー: インスタンスの対象の型 List のカインドがクラス Eq のパラメータと一致しません
  [1]

対象の型に書く `_` の個数は、型構成子が取る型引数の個数と一致しなければならない:

  $ cat > pr5a.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type class Functor[F[_]] { val map[A, B, E]: (F[A], (A) => B @ E) => F[B] @ E }
  > type instance Functor[List[_, _, _]] {
  >   let rec map[A, B, E](xs: List[A], f: (A) => B @ E): List[B] @ E = Nil
  > }
  > EOF
  $ diktor --type-check --no-prelude pr5a.kel
  ! pr5a.kel:3:1: 型エラー: インスタンスの対象の型 List は型引数を 1 個取りますが、_ が 3 個書かれています
  [1]

`_` が型構成子の取る型引数より少ない場合も、同じ形の診断でエラーになる(上の pr5a は
多い場合である):

  $ cat > pr5b.kel <<'EOF'
  > newtype Pair[A, B] = MkPair(fst: A, snd: B)
  > type instance[A: Eq] Eq[Pair[_]] { let eq(p, q) = true }
  > EOF
  $ diktor --type-check --no-prelude pr5b.kel
  ! pr5b.kel:2:1: 型エラー: インスタンスの対象の型 Pair は型引数を 2 個取りますが、_ が 1 個書かれています
  [1]

束縛子は `_` より多く書けない。束縛子のカインドは、対応する `_` の位置の型引数のカインドと一致しなければならない:

  $ cat > pr5.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance[A: Eq, B: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }
  > EOF
  $ diktor --type-check --no-prelude pr5.kel
  ! pr5.kel:2:1: 型エラー: インスタンスの型パラメータが 2 個ありますが、対象の型 List の _ は 1 個です
  [1]
  $ cat > pr6.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance[F[_]: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }
  > EOF
  $ diktor --type-check --no-prelude pr6.kel
  ! pr6.kel:2:1: 型エラー: インスタンスの型パラメータ F のカインドが対象の型 List の引数と一致しません
  [1]

`_` が 0 個の対象の型には、束縛子を付けられない(「束縛子は `_` より多く書けない」規則の、`_` が
ない場合である):

  $ cat > pr20.kel <<'EOF'
  > newtype Opaque = MkOpaque(Int32)
  > type instance[A: Eq] Eq[Opaque] { let eq(a, b) = true }
  > EOF
  $ diktor --type-check --no-prelude pr20.kel
  ! pr20.kel:2:1: 型エラー: インスタンスの型パラメータが 1 個ありますが、対象の型 Opaque の _ は 0 個です
  [1]

制約を書かない束縛子では、本体の `==` が型検査に通らない。本体が要求する制約の辞書は
束縛子に書いた前提から受け取るので、制約は束縛子に書いてある必要がある:

  $ cat > pr7.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance[A] Eq[List[_]] {
  >   let rec eq(xs, ys) = (xs, ys) match {
  >     case (Nil, Nil)                 => true
  >     case (Cons(x, xt), Cons(y, yt)) => x == y && eq(xt, yt)
  >     case _                          => false
  >   }
  > }
  > EOF
  $ diktor --type-check --no-prelude pr7.kel
  ! pr7.kel:5:40: 型エラー: 型パラメータ ς1 は Eq のインスタンスではありません。[A: Eq] のように制約を書いてください
  [1]

未知のクラスと予約述語は、束縛子の位置でも拒否する:

  $ cat > pr8.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance[A: Bogus] Eq[List[_]] { let rec eq(xs, ys) = true }
  > EOF
  $ diktor --type-check --no-prelude pr8.kel
  ! pr8.kel:2:1: 型エラー: 未知のクラス: Bogus
  [1]
  $ cat > pr9.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance[A: Integral] Eq[List[_]] { let rec eq(xs, ys) = true }
  > EOF
  $ diktor --type-check --no-prelude pr9.kel
  ! pr9.kel:2:1: 型エラー: Integral は予約されたリテラル述語です(制約には書けません、D8)
  [1]

前提付きインスタンスのメソッドは、前提の辞書を受け取って要素の比較に渡す。入れ子のリストでも動く。
標準環境の List に対する Eq のインスタンスは標準環境が持つ(孤児規則)ので、自前のリスト型で示す:

  $ cat > pr10.kel <<'EOF'
  > newtype Lst[A] = LNil | LCons(A, Lst[A])
  > type instance[A: Eq] Eq[Lst[_]] {
  >   let rec eq(xs, ys) = (xs, ys) match {
  >     case (LNil, LNil)                 => true
  >     case (LCons(x, xt), LCons(y, yt)) => x == y && eq(xt, yt)
  >     case _                            => false
  >   }
  > }
  > echoln(show(LCons(1i32, LCons(2i32, LNil)) == LCons(1i32, LCons(2i32, LNil))))
  > echoln(show(LCons(1i32, LNil) == LCons(2i32, LNil)))
  > echoln(show(LCons(LCons("a", LNil), LNil) == LCons(LCons("a", LNil), LNil)))
  > echoln(show(LCons(LCons("a", LNil), LNil) == LCons(LCons("b", LNil), LNil)))
  > echoln(show(LNil == LCons(1i32, LNil)))
  > EOF
  $ diktor pr10.kel
  true
  false
  true
  false
  false

AST のダンプでは、束縛子があるときだけ tparams が出る:

  $ cat > pr11.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > newtype Opaque = MkOpaque(Int32)
  > type instance[A: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }
  > type instance Eq[Opaque] { let eq(a, b) = true }
  > EOF
  $ diktor --dump-ast pr11.kel
  (newtype List (A) (Cons A (tail: (tapp List A))) (Nil))
  (newtype Opaque (MkOpaque Int32))
  (instance (tparams (: A Eq)) Eq ((tapp List _))
   (dletrec (binding eq (params xs ys) = true)))
  (instance Eq (Opaque) (dlet (binding eq (params a b) = true)))

束縛子の名前は本体の型スコープに入るので、メソッドの型注釈に書ける:

  $ cat > pr12.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance[A: Eq] Eq[List[_]] { let rec eq(xs: List[A], ys: List[A]): Boolean = true }
  > EOF
  $ diktor --type-check --no-prelude pr12.kel

同名の newtype があっても、本体の型注釈は型検査に通る。インスタンスの外の A は newtype A
のままで、z の型に出る:

  $ cat > pr21.kel <<'EOF'
  > newtype A = MkA(Int32)
  > newtype List[X] = Cons(X, tail: List[X]) | Nil
  > type instance[A: Eq] Eq[List[_]] { let rec eq(xs: List[A], ys: List[A]): Boolean = true }
  > let z(p: A): A = p
  > EOF
  $ diktor --type-check --no-prelude pr21.kel
  z : (A) => A

束縛子は対象の型の `_` を束縛する。`_` に対応する位置の片方だけを具体的な型で注釈すると、
クラス宣言の側のスコーレム定数(診断では「スコープ付きの型」)と一致せず、型エラーになる:

  $ cat > pr22.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > newtype Opaque = MkOpaque(Int32)
  > type instance[A: Eq] Eq[List[_]] { let rec eq(xs: List[Opaque], ys: List[A]): Boolean = true }
  > EOF
  $ diktor --type-check --no-prelude pr22.kel
  ! pr22.kel:3:44: 型エラー: インスタンスメソッド eq がクラス宣言の型を満たしません(スコープ付きの型が一致しません: Opaque と ς1)
  [1]

メソッド自身の型パラメータが同名なら、内側を優先する。束縛子に書いた Eq の制約は
本体に適用されず、本体の == が型エラーになる:

  $ cat > pr23.kel <<'EOF'
  > newtype List[X] = Cons(X, tail: List[X]) | Nil
  > type instance[A: Eq] Eq[List[_]] {
  >   let rec eq[A](xs: List[A], ys: List[A]): Boolean = (xs, ys) match {
  >     case (Nil, Nil) => true
  >     case (Cons(x, xt), Cons(y, yt)) => x == y && eq(xt, yt)
  >     case _ => false
  >   }
  > }
  > EOF
  $ diktor --type-check --no-prelude pr23.kel
  ! pr23.kel:5:40: 型エラー: 型パラメータ ς1 は Eq のインスタンスではありません。[A: Eq] のように制約を書いてください
  [1]

束縛子のリストには末尾カンマを置ける。空の束縛子リストは構文エラーである。type instance に pub は
付けられない(コヒーレンスのために、インスタンスはどこからでも見える必要があり、pub に意味がない):

  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\ntype instance[A: Eq,] Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr13.kel
  $ diktor --type-check --no-prelude pr13.kel
  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\ntype instance[] Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr14.kel
  $ diktor --type-check --no-prelude pr14.kel
  pr14.kel:2:15: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\npub type instance[A: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr15.kel
  $ diktor --type-check --no-prelude pr15.kel
  pr15.kel:2:1: 構文エラー: type instance に pub は付けられません
  [2]

instance と [ の間には空白、改行、ブロックコメントのどれを挟んでもよく、束縛子
リストと対象の型の間の空白も省ける(4 つとも終了コード 0 で、出力はない):

  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\ntype instance [A: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr24.kel
  $ diktor --type-check --no-prelude pr24.kel
  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\ntype instance\n  [A: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr25.kel
  $ diktor --type-check --no-prelude pr25.kel
  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\ntype instance /* c */ [A: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr26.kel
  $ diktor --type-check --no-prelude pr26.kel
  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\ntype instance[A: Eq]Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr27.kel
  $ diktor --type-check --no-prelude pr27.kel

module の中の型に対しても、前提付きインスタンスを書ける(対象の型は修飾名 M.L[_] で書く):

  $ cat > pr16.kel <<'EOF'
  > module M {
  >   pub newtype L[A] = C(A, tail: L[A]) | N
  > }
  > type instance[A: Eq] Eq[M.L[_]] {
  >   let rec eq(xs, ys) = (xs, ys) match {
  >     case (M.N, M.N)                 => true
  >     case (M.C(x, xt), M.C(y, yt)) => x == y && eq(xt, yt)
  >     case _                          => false
  >   }
  > }
  > let b = M.C(1i32, M.N) == M.C(1i32, M.N)
  > EOF
  $ diktor --type-check --no-prelude pr16.kel
  b : Boolean

i 番目の束縛子は、対象の型の i 番目の `_` に対応する(`_` が 2 個、束縛子が 2 個のとき、
位置 0 の前提と位置 1 の前提が別々に適用される):

  $ cat > pr17.kel <<'EOF'
  > newtype Pair[A, B] = MkPair(fst: A, snd: B)
  > newtype Opaque = MkOpaque(Int32)
  > type class Sh[A] { val sh: (A) => String }
  > type instance Sh[Int32] { let sh(x) = "i" }
  > type instance[A: Eq, B: Sh] Eq[Pair[_, _]] {
  >   let eq(p, q) = (p, q) match { case (MkPair(a, b), MkPair(c, d)) => a == c && sh(b) == sh(d) }
  > }
  > let ok(p: Pair[Int32, Int32], q: Pair[Int32, Int32]): Boolean = p == q
  > let ng1(p: Pair[Int32, Opaque], q: Pair[Int32, Opaque]): Boolean = p == q
  > EOF
  $ diktor --type-check --no-prelude pr17.kel
  ok : (Pair[Int32, Int32], Pair[Int32, Int32]) => Boolean
  ! pr17.kel:9:68: 型エラー: Opaque は Sh のインスタンスではありません。Pair[Int32, Opaque] が Eq であるための前提として要求されました
  [1]
  $ sed 's/Pair\[Int32, Opaque\]/Pair[Opaque, Int32]/g; s/ng1/ng2/' pr17.kel > pr18.kel
  $ diktor --type-check --no-prelude pr18.kel
  ok : (Pair[Int32, Int32], Pair[Int32, Int32]) => Boolean
  ! pr18.kel:9:68: 型エラー: Opaque は Eq のインスタンスではありません。Pair[Opaque, Int32] が Eq であるための前提として要求されました
  [1]

束縛子が `_` より少ない形である。部分適用の対象の型に前提が付くのは、この組み合わせだけである。
対象の型 P2[_, _] は型引数を 1 個取るカインドのままで、位置 0 に前提が付く:

  $ cat > pr19.kel <<'EOF'
  > newtype P2[A, B] = MkP2(fst: A, snd: B)
  > newtype Opaque = MkOpaque(Int32)
  > type class Functor[F[_]] { val map[A, B, E]: (F[A], (A) => B @ E) => F[B] @ E }
  > type instance[A: Eq] Functor[P2[_, _]] {
  >   let map(p, f) = p match { case MkP2(a, b) => MkP2(a, f(b)) }
  > }
  > let use1(p: P2[Int32, Int32]): P2[Int32, Int32] = map(p, fn(x) => x)
  > let use2(p: P2[Opaque, Int32]): P2[Opaque, Int32] = map(p, fn(x) => x)
  > EOF
  $ diktor --type-check --no-prelude pr19.kel
  use1 : (P2[Int32, Int32]) => P2[Int32, Int32]
  ! pr19.kel:8:57: 型エラー: Opaque は Eq のインスタンスではありません。P2[Opaque] が Functor であるための前提として要求されました
  [1]

前提をたどって生じた要求が満たされないとき、診断に、たどり始めた型とクラス(要求の発生元)を添える
ことがある。pr21 は List[List[Opaque]] の比較で、添えるのは外側の 1 組だけであり、途中の
List[Opaque] は書かない:

  $ cat > pr21.kel <<'KEL'
  > newtype Opaque = MkOpaque(Int32)
  > let ng(xs: List[List[Opaque]]): Boolean = xs == xs
  > KEL
  $ diktor --type-check pr21.kel
  ! pr21.kel:2:43: 型エラー: Opaque は Eq のインスタンスではありません。List[List[Opaque]] が Eq であるための前提として要求されました
  [1]

pr22 は、前提が先に単一化変数に伝播し、その変数が後で具体的な型に決まる形で、これにも
発生元を添える。左の Nil が List[α] に Eq を要求し、α が List[Opaque] に決まる
のは右辺を読んだ後である:

  $ cat > pr22.kel <<'KEL'
  > newtype Opaque = MkOpaque(Int32)
  > let ng = Nil == Cons(Cons(MkOpaque(1i32), Nil), Nil)
  > KEL
  $ diktor --type-check pr22.kel
  ! pr22.kel:2:10: 型エラー: Opaque は Eq のインスタンスではありません。List[List[Opaque]] が Eq であるための前提として要求されました
  [1]

pr23 は前提が型パラメータに伝播した形で、発生元を、制約の書き方の案内より前に置く。
pr24 は前提をたどらない要求(Opaque そのものの比較)で、何も添えない:

  $ cat > pr23.kel <<'KEL'
  > let f[A](xs: List[A], ys: List[A]): Boolean = xs == ys
  > KEL
  $ diktor --type-check pr23.kel
  ! pr23.kel:1:47: 型エラー: 型パラメータ ς1 は Eq のインスタンスではありません。List[ς1] が Eq であるための前提として要求されました。[A: Eq] のように制約を書いてください
  [1]
  $ cat > pr24.kel <<'KEL'
  > newtype Opaque = MkOpaque(Int32)
  > let ng = MkOpaque(1i32) == MkOpaque(1i32)
  > KEL
  $ diktor --type-check pr24.kel
  ! pr24.kel:2:10: 型エラー: Opaque は Eq のインスタンスではありません
  [1]

pr25 の f は A に Eq を付け、B には付けていないので、満たされないのは B である。
診断の型と発生元の型は、型変数の名前を割り当てる表を共有して表示するので、前半の ς1 と、発生元
P2[ς2, ς1] の 2 つ目の位置(B の位置)の ς1 は同じ名前になる:

  $ cat > pr25.kel <<'KEL'
  > newtype P2[A, B] = MkP2(A, B)
  > type instance[A: Eq, B: Eq] Eq[P2[_, _]] {
  >   let eq(p, q) = (p, q) match { case (MkP2(a, b), MkP2(c, d)) => a == c && b == d }
  > }
  > let f[A: Eq, B](x: P2[A, B], y: P2[A, B]): Boolean = x == y
  > KEL
  $ diktor --type-check pr25.kel
  ! pr25.kel:5:54: 型エラー: 型パラメータ ς1 は Eq のインスタンスではありません。P2[ς2, ς1] が Eq であるための前提として要求されました。[A: Eq] のように制約を書いてください
  [1]

発生元は、前提が単一化変数に制約を付けた時点の要求である。pr26 では、診断の位置は
x が Opaque に決まった 5 行目の x == o(前提をたどらない比較)を指し、発生元は
4 行目の比較の List[Opaque] である。pr27 は、同じ比較を let で一般化される k の本体に
置いた形で、k(o) で具体化した変数には発生元が引き継がれず、元のメッセージだけが出る:

  $ cat > pr26.kel <<'KEL'
  > newtype Opaque = MkOpaque(Int32)
  > let ng(o: Opaque): Boolean = {
  >   let k = fn(x) => {
  >     let a = Cons(x, Nil) == Nil
  >     x == o
  >   }
  >   k(o)
  > }
  > KEL
  $ diktor --type-check pr26.kel
  ! pr26.kel:5:5: 型エラー: Opaque は Eq のインスタンスではありません。List[Opaque] が Eq であるための前提として要求されました
  [1]
  $ cat > pr27.kel <<'KEL'
  > newtype Opaque = MkOpaque(Int32)
  > let ng(o: Opaque): Boolean = {
  >   let k = fn(x) => Cons(x, Nil) == Nil
  >   k(o)
  > }
  > KEL
  $ diktor --type-check pr27.kel
  ! pr27.kel:4:5: 型エラー: Opaque は Eq のインスタンスではありません
  [1]
