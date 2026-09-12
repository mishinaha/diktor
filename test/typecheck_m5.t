M5(newtype / パターン / Maranget 網羅性)のゴールデン。
変更時は dune promote で更新し、必ず目視レビューすること。

newtype 一式(sample.kel §6)と MiniLang §16-2(let rec とデータ宣言):

  $ cat > data.kel <<'EOF'
  > newtype Option[A] = None | Some(A)
  > newtype List[A] = Nil | Cons(A, tail: List[A])
  > newtype UserId(Int32)
  > newtype Opaque = ???
  > let rec length[A](xs: List[A]): Int32 = xs match {
  >   case Nil => 0
  >   case Cons(_, tail) => 1 + length(tail)
  > }
  > let rec map2 = fn(f, xs) => xs match {
  >   case Nil => Nil
  >   case Cons(head, tail) => Cons(f(head), map2(f, tail))
  > }
  > let lst = Cons(1, Cons(2, Nil))
  > let opt = Some(42)
  > let uid = UserId(7)
  > let labeled = Cons(1, tail = Nil)
  > EOF
  $ diktor --type-check --no-prelude data.kel
  length : (List[A]) => Int32
  map2 : ((A) => B, List[A]) => List[B]
  lst : List[Int32]
  opt : Option[Int32]
  uid : UserId
  labeled : List[Int32]

MiniLang §16-3(網羅性検査 — 宣言された型は注釈が要らない):

  $ cat > exh.kel <<'EOF'
  > newtype Option[A] = None | Some(A)
  > let partial = fn(o) => o match { case Some(x) => x }
  > let deep = fn(o) => o match {
  >   case Some(Some(x)) => x
  >   case None => 0
  > }
  > let bools = fn(a, b) => (a, b) match {
  >   case (true, _) => 1
  >   case (false, true) => 2
  > }
  > let redundant = fn(a, b) => (a, b) match {
  >   case (true, _) => 1
  >   case (_, true) => 2
  >   case (false, false) => 3
  >   case (true, true) => 4
  > }
  > EOF
  $ diktor --type-check --no-prelude exh.kel
  partial : (Option[A]) => A
  ⚠ match が非網羅的です。例えば None が漏れています
  deep : (Option[Option[Int32]]) => Int32
  ⚠ match が非網羅的です。例えば Some(None) が漏れています
  bools : (Boolean, Boolean) => Int32
  ⚠ match が非網羅的です。例えば (false, false) が漏れています
  redundant : (Boolean, Boolean) => Int32
  ⚠ 第 4 節は到達不能です(冗長)

--strict-exhaustive で警告がエラー化(exit 1):

  $ diktor --type-check --no-prelude --strict-exhaustive exh.kel > /dev/null; echo "exit: $?"
  exit: 1

構造的ヴァリアント(sample.kel §5)と行を閉じる規則:

  $ cat > variant.kel <<'EOF'
  > type Parity = #Even | #Odd
  > let flip(p: Parity): Parity = p match {
  >   case #Even => #Odd
  >   case #Odd => #Even
  > }
  > let closed = fn(t) => t match {
  >   case #Lft(n) => n + 0
  >   case #Rgt(_) => 0
  > }
  > let open_default = fn(t) => t match {
  >   case #Lft(n) => n
  >   case _ => 0
  > }
  > let payload = #Point(1, 2)
  > let guard = fn(t) => t match {
  >   case #Val(x) if x == 0 => 0
  >   case #Val(x) => x
  > }
  > EOF
  $ diktor --type-check --no-prelude variant.kel
  flip : (#Even | #Odd) => #Even | #Odd
  closed : (#Lft(Int32) | #Rgt(A)) => Int32
  open_default : (#Lft(Int32) | R1) => Int32
  payload : #Point((Int32, Int32)) | R1
  guard : (#Val(Int32)) => Int32

ヴァリアント和のエイリアスと網羅性(case _ 不要。sample.kel §5):

  $ cat > union.kel <<'EOF'
  > type IoError = #NotFound | #Denied
  > type ParseError = #Unexpected
  > type AnyError = IoError | ParseError
  > let report(e: AnyError): Int32 = e match {
  >   case #NotFound => 1
  >   case #Denied => 2
  >   case #Unexpected => 3
  > }
  > EOF
  $ diktor --type-check --no-prelude union.kel
  report : (#NotFound | #Denied | #Unexpected) => Int32

Never は節ゼロの match で網羅(§7.5):

  $ cat > never.kel <<'EOF'
  > let absurd[A](n: Never): A = n match {}
  > EOF
  $ diktor --type-check --no-prelude never.kel
  absurd : (Never) => A

パターン束縛の網羅性警告(§6.4)とラベル指定パターンの _ 補完:

  $ cat > patlet.kel <<'EOF'
  > newtype List[A] = Nil | Cons(A, tail: List[A])
  > let f = fn(xs) => {
  >   let Cons(head, tail) = xs
  >   head
  > }
  > let g = fn(xs) => xs match { case Cons(tail = t) => t case Nil => Nil }
  > EOF
  $ diktor --type-check --no-prelude patlet.kel
  f : (List[A]) => A
  ⚠ match が非網羅的です。例えば Nil が漏れています
  g : (List[A]) => List[A]

コンストラクタのエラー経路:

  $ cat > ctorbad.kel <<'EOF'
  > newtype Option[A] = None | Some(A)
  > let bad = Some(1, 2)
  > EOF
  $ diktor --type-check --no-prelude ctorbad.kel
  ! ctorbad.kel:2:11: 型エラー: コンストラクタ Some の引数が多すぎます
  [1]

  $ cat > ctorbad2.kel <<'EOF'
  > newtype List[A] = Nil | Cons(A, tail: List[A])
  > let bad = Cons(1)
  > EOF
  $ diktor --type-check --no-prelude ctorbad2.kel
  ! ctorbad2.kel:2:11: 型エラー: コンストラクタ Cons の引数が不足しています(式では全フィールド必須)
  [1]

  $ cat > ctorbad3.kel <<'EOF'
  > newtype Opaque = ???
  > let bad = fn(o) => o match { case Opaque(x) => x }
  > EOF
  $ diktor --type-check --no-prelude ctorbad3.kel
  ! ctorbad3.kel:2:35: 型エラー: 未知のコンストラクタ: Opaque
  [1]

1 要素タプルは反例でも実行時値でも (x,) と出る(§4 の再糖衣化は型だけでなく
エラーメッセージにも及ぶ。(x) はグループ化なので貼り戻せない。M21 / D101):

  $ cat > tup1.kel <<'KEL'
  > let f(t: (Boolean,)): Int32 = t match { case (true,) => 1 }
  > echoln(show(f((false,))))
  > KEL
  $ diktor tup1.kel
  ⚠ match が非網羅的です。例えば (false,) が漏れています
  実行時エラー: match のどの節にも一致しません: (false,)
  [3]
