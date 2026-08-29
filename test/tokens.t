--dump-tokens のゴールデン(計画 §9.2: ASI とブレース再分類を固定する唯一の手段)。
変更時は dune promote で更新し、必ず目視レビューすること。

ASI の基本(既存バグ 0.2-12 の回帰: let 2連続の間に区切りが入ること):

  $ cat > asi.kel <<'EOF'
  > let x = 1
  > let y = 2
  > EOF
  $ diktor --dump-tokens asi.kel
     1  let
     1  x
     1  =
     1  1
     1  <NL>
     2  let
     2  y
     2  =
     2  2
     3  <EOF>

行継続(演算子・AND・ドットチェーンの前では NL が落ちる):

  $ cat > cont.kel <<'EOF'
  > let a = 1 +
  >   2
  > let rec f(x) = g(x)
  > and g(x) = f(x)
  > let b = r
  >   .field
  > EOF
  $ diktor --dump-tokens cont.kel
     1  let
     1  a
     1  =
     1  1
     1  +
     2  2
     2  <NL>
     3  let
     3  rec
     3  f
     3  (
     3  x
     3  )
     3  =
     3  g
     3  (
     3  x
     3  )
     4  and
     4  g
     4  (
     4  x
     4  )
     4  =
     4  f
     4  (
     4  x
     4  )
     4  <NL>
     5  let
     5  b
     5  =
     5  r
     6  .
     6  field
     7  <EOF>

括弧・角括弧・レコード内では NL が抑止される:

  $ cat > suppress.kel <<'EOF'
  > let s = f(a,
  >           b)
  > let r = {x = 1,
  >          y = 2}
  > let l = xs[
  >   0]
  > EOF
  $ diktor --dump-tokens suppress.kel
     1  let
     1  s
     1  =
     1  f
     1  (
     1  a
     1  ,
     2  b
     2  )
     2  <NL>
     3  let
     3  r
     3  =
     3  {rec
     3  x
     3  =
     3  1
     3  ,
     4  y
     4  =
     4  2
     4  }
     4  <NL>
     5  let
     5  l
     5  =
     5  xs
     5  [
     6  0
     6  ]
     7  <EOF>

`{` の 3-way 再分類(§5.3 の表のとおり):

  $ cat > brace.kel <<'EOF'
  > let empty = {}
  > let ext = {extends r}
  > let rcd = {x = 1}
  > let pan = {a, b}
  > let upd = {p with x = 1}
  > let blk1 = {x}
  > let blk2 = { f(); g() }
  > type P = {x: Float64}
  > EOF
  $ diktor --dump-tokens brace.kel
     1  let
     1  empty
     1  =
     1  {rec
     1  }
     1  <NL>
     2  let
     2  ext
     2  =
     2  {rec
     2  extends
     2  r
     2  }
     2  <NL>
     3  let
     3  rcd
     3  =
     3  {rec
     3  x
     3  =
     3  1
     3  }
     3  <NL>
     4  let
     4  pan
     4  =
     4  {rec
     4  a
     4  ,
     4  b
     4  }
     4  <NL>
     5  let
     5  upd
     5  =
     5  {rec
     5  p
     5  with
     5  x
     5  =
     5  1
     5  }
     5  <NL>
     6  let
     6  blk1
     6  =
     6  {blk
     6  x
     6  }
     6  <NL>
     7  let
     7  blk2
     7  =
     7  {blk
     7  f
     7  (
     7  )
     7  ;
     7  g
     7  (
     7  )
     7  }
     7  <NL>
     8  type
     8  P
     8  =
     8  {ty
     8  x
     8  :
     8  Float64
     8  }
     9  <EOF>

ブロック内の文区切りと match/handle の節(case 後の NL は => まで抑止):

  $ cat > block.kel <<'EOF'
  > let g = fn(v) => {
  >   let w = v \ tag
  >   w match {
  >     case Some(x)
  >       if x == 1 => x
  >     case _ => 0
  >   }
  > }
  > EOF
  $ diktor --dump-tokens block.kel
     1  let
     1  g
     1  =
     1  fn
     1  (
     1  v
     1  )
     1  =>
     1  {blk
     2  let
     2  w
     2  =
     2  v
     2  \
     2  tag
     2  <NL>
     3  w
     3  match
     3  {blk
     4  case
     4  Some
     4  (
     4  x
     4  )
     5  if
     5  x
     5  ==
     5  1
     5  =>
     5  x
     6  case
     6  _
     6  =>
     6  0
     7  }
     8  }
     9  <EOF>

クラス本体(val / derive が行頭に来られること。spike の FIX-11):

  $ cat > cls.kel <<'EOF'
  > type class Eq[A] {
  >   val eq: (A, A) => Boolean
  >   derive structural
  > }
  > EOF
  $ diktor --dump-tokens cls.kel
     1  type
     1  class
     1  Eq
     1  [
     1  A
     1  ]
     1  {blk
     2  val
     2  eq
     2  :
     2  (
     2  A
     2  ,
     2  A
     2  )
     2  =>
     2  Boolean
     2  <NL>
     3  derive
     3  structural
     4  }
     5  <EOF>

コメント・shebang(// は NL を残す。改行入り /* */ は NL 1個として振る舞う):

  $ cat > comment.kel <<'EOF'
  > #!/usr/bin/env diktor
  > let a = 1 // 行コメント
  > let b = /* 入れ子 /* の */ コメント */ 2
  > let c = 3 /* 改行入り
  >   コメント */ let d = 4
  > EOF
  $ diktor --dump-tokens comment.kel
     2  let
     2  a
     2  =
     2  1
     2  <NL>
     3  let
     3  b
     3  =
     3  2
     3  <NL>
     4  let
     4  c
     4  =
     4  3
     5  <NL>
     5  let
     5  d
     5  =
     5  4
     6  <EOF>

数値リテラル(D13: 接尾辞・基数・桁区切り・指数):

  $ cat > num.kel <<'EOF'
  > let a = 42
  > let b = 1_000_000i64
  > let c = 0xff_ffu32
  > let d = 0o777
  > let e = 0b1010i8
  > let f = 1.5
  > let g = 2e10
  > let h = 1.5e-3f32
  > let i = 3f64
  > let j = -7
  > EOF
  $ diktor --dump-tokens num.kel
     1  let
     1  a
     1  =
     1  42
     1  <NL>
     2  let
     2  b
     2  =
     2  1_000_000i64
     2  <NL>
     3  let
     3  c
     3  =
     3  0xff_ffu32
     3  <NL>
     4  let
     4  d
     4  =
     4  0o777
     4  <NL>
     5  let
     5  e
     5  =
     5  0b1010i8
     5  <NL>
     6  let
     6  f
     6  =
     6  1.5
     6  <NL>
     7  let
     7  g
     7  =
     7  2e10
     7  <NL>
     8  let
     8  h
     8  =
     8  1.5e-3f32
     8  <NL>
     9  let
     9  i
     9  =
     9  3f64
     9  <NL>
    10  let
    10  j
    10  =
    10  -
    10  7
    11  <EOF>

文字列・#Foo・???・...rest・その他の新トークン:

  $ cat > misc.kel <<'EOF'
  > let s = "a\n\tあ"
  > let v = #Even
  > let h = ???
  > let f = fn(x, ...rest) => x
  > let cmp = a <= b >= c
  > EOF
  $ diktor --dump-tokens misc.kel
     1  let
     1  s
     1  =
     1  "a\n\t\227\129\130"
     1  <NL>
     2  let
     2  v
     2  =
     2  #Even
     2  <NL>
     3  let
     3  h
     3  =
     3  ???
     3  <NL>
     4  let
     4  f
     4  =
     4  fn
     4  (
     4  x
     4  ,
     4  ...
     4  rest
     4  )
     4  =>
     4  x
     4  <NL>
     5  let
     5  cmp
     5  =
     5  a
     5  <=
     5  b
     5  >=
     5  c
     6  <EOF>

字句エラー(exit 2):

  $ printf 'let a = "unterminated' > err.kel
  $ diktor --dump-tokens err.kel
  err.kel:1:22: 字句エラー: unterminated string literal
  [2]

sample.kel 全文のトークン化(spike と同じ 2526 トークンであること):

  $ diktor --dump-tokens sample/sample.kel | wc -l
  2526
  $ diktor --dump-tokens sample/sample.kel | tail -6
   582  .
   582  parse
   582  (
   582  "456"
   582  )
   608  <EOF>

小数部の省略(1. / 2.e3)と、その後の ASI(D25。行末の 1. は NUMBER で
文を終えられる — 以前は DOT で継続していた):

  $ cat > dotasi.kel <<'EOF2'
  > let x = 1.
  > let y = 2.e3
  > EOF2
  $ diktor --dump-tokens dotasi.kel
     1  let
     1  x
     1  =
     1  1.
     1  <NL>
     2  let
     2  y
     2  =
     2  2.e3
     3  <EOF>
