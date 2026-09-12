前提つきインスタンス(仕様 §8、M22 / D93〜D97)。sample.kel §8 の Eq[List[_]] が
そのまま通ること:

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

前提が引数へ伝播する(unify.ml §8.4 の TCon 枝がここで初めて実際に走る):

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
  ! pr2.kel:10:10: 型エラー: Opaque は Eq のインスタンスではありません
  [1]

前提が構造的導出の先へも届く(レコードのフィールドが List[Opaque]):

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
  ! pr3.kel:11:65: 型エラー: Opaque は Eq のインスタンスではありません
  [1]

束縛子を書かないと頭のカインドが合わない(Eq は Type のクラス):

  $ cat > pr4.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance Eq[List[_]] { let rec eq(xs, ys) = true }
  > EOF
  $ diktor --type-check --no-prelude pr4.kel
  ! pr4.kel:2:1: 型エラー: インスタンス頭 List のカインドがクラス Eq のパラメータと一致しません
  [1]

頭の `_` の個数は構成子のアリティと一致すること(D96。改訂前は未検査だった):

  $ cat > pr5a.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type class Functor[F[_]] { val map[A, B, E]: (F[A], (A) => B @ E) => F[B] @ E }
  > type instance Functor[List[_, _, _]] {
  >   let rec map[A, B, E](xs: List[A], f: (A) => B @ E): List[B] @ E = Nil
  > }
  > EOF
  $ diktor --type-check --no-prelude pr5a.kel
  ! pr5a.kel:3:1: 型エラー: インスタンス頭 List は型引数を 1 個取りますが、_ が 3 個書かれています
  [1]

束縛子は穴より多くできない。束縛子のカインドは頭の引数と一致すること(D97):

  $ cat > pr5.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance[A: Eq, B: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }
  > EOF
  $ diktor --type-check --no-prelude pr5.kel
  ! pr5.kel:2:1: 型エラー: インスタンスの型パラメータが 2 個ありますが、頭 List の _ は 1 個です
  [1]
  $ cat > pr6.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance[F[_]: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }
  > EOF
  $ diktor --type-check --no-prelude pr6.kel
  ! pr6.kel:2:1: 型エラー: インスタンスの型パラメータ F のカインドが頭 List の引数と一致しません
  [1]

制約を書かない束縛子では本体の `==` が通らない(前提は選択にだけ使うので、
本体が要求する制約は束縛子に書いてある必要がある):

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
  ! pr7.kel:3:11: 型エラー: インスタンスメソッド eq がクラス宣言の型を満たしません(型パラメータ ς1 は Eq のインスタンスではありません。[A: Eq] のように制約を書いてください)
  [1]

未知のクラス・予約述語は束縛子の位置でも拒む:

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

実行時のディスパッチは値の頭だけを見る(前提は運ばない — D95)。入れ子も通る:

  $ cat > pr10.kel <<'EOF'
  > newtype List[A] = Cons(head: A, tail: List[A]) | Nil
  > type instance[A: Eq] Eq[List[_]] {
  >   let rec eq(xs, ys) = (xs, ys) match {
  >     case (Nil, Nil)                 => true
  >     case (Cons(x, xt), Cons(y, yt)) => x == y && eq(xt, yt)
  >     case _                          => false
  >   }
  > }
  > echoln(show(Cons(1i32, Cons(2i32, Nil)) == Cons(1i32, Cons(2i32, Nil))))
  > echoln(show(Cons(1i32, Nil) == Cons(2i32, Nil)))
  > echoln(show(Cons(Cons("a", Nil), Nil) == Cons(Cons("a", Nil), Nil)))
  > echoln(show(Cons(Cons("a", Nil), Nil) == Cons(Cons("b", Nil), Nil)))
  > echoln(show(Nil == Cons(1i32, Nil)))
  > EOF
  $ diktor pr10.kel
  true
  false
  true
  false
  false

AST ダンプ(束縛子があるときだけ tparams が出る):

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

束縛子の名前は本体の型スコープに入る(D94。メソッドに注釈が書ける):

  $ cat > pr12.kel <<'EOF'
  > newtype List[A] = Cons(A, tail: List[A]) | Nil
  > type instance[A: Eq] Eq[List[_]] { let rec eq(xs: List[A], ys: List[A]): Boolean = true }
  > EOF
  $ diktor --type-check --no-prelude pr12.kel

束縛子の末尾カンマは置ける(D56)。空の束縛子リストは構文エラー。pub は
従来どおり付けられない(コヒーレンスが大域可視を要求するので意味が無い):

  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\ntype instance[A: Eq,] Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr13.kel
  $ diktor --type-check --no-prelude pr13.kel
  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\ntype instance[] Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr14.kel
  $ diktor --type-check --no-prelude pr14.kel
  pr14.kel:2:15: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'newtype List[A] = Cons(A, tail: List[A]) | Nil\npub type instance[A: Eq] Eq[List[_]] { let rec eq(xs, ys) = true }\n' > pr15.kel
  $ diktor --type-check --no-prelude pr15.kel
  pr15.kel:3:1: 構文エラー: type instance に pub は付けられません
  [2]

module 越しの前提つきインスタンス(頭は修飾名 M.L[_]):

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
