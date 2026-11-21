--dump-tokens の出力を固定するゴールデンテスト。ASI と `{` の分類を固定する手段は、このテストだけである。
出力が変わったときは dune promote で更新し、差分を目で確認する。

ASI の基本。2 つ続く let の間に区切りが入る:

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

行の継続。行末の演算子の後ろと、行頭の and と . の前では、NL を捨てる:

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

丸括弧、角括弧、レコードの中では NL を捨てる:

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

`{` を 3 通りに分類する(第2章 §2.9。判別の表は sample.kel:20-25):

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

ブロックの中の文の区切りと、match と handle の節。case の後ろの NL は => まで捨てる:

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

クラスの本体。2 つ目の val を行頭に書ける:

  $ cat > cls.kel <<'EOF'
  > type class Eq[A] {
  >   val eq: (A, A) => Boolean
  >   val ne: (A, A) => Boolean
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
     3  val
     3  ne
     3  :
     3  (
     3  A
     3  ,
     3  A
     3  )
     3  =>
     3  Boolean
     4  }
     5  <EOF>

コメントと shebang。// は NL を残し、改行を含む /* */ は NL 1 個として扱う:

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

数値リテラル。接尾辞、基数、桁区切り、指数:

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

文字列、#Foo、???、...rest と、そのほかのトークン:

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

字句エラーは終了コード 2 で終了する:

  $ printf 'let a = "unterminated' > err.kel
  $ diktor --dump-tokens err.kel
  err.kel:1:22: 字句エラー: 文字列リテラルが閉じていません
  [2]

先頭の BOM は字句エラーになる(sample.kel §0)。診断は、BOM、C0 制御文字、DEL と C1 制御文字、
NBSP、ソフトハイフン、U+200B〜U+200F、U+2028〜U+202E、U+2060〜U+2064 を
文字そのものではなく U+XXXX の形で表示し、それ以外は文字のまま表示する。見えない文字を
そのまま出すと、期待出力として固定できないからである。文字の集合は第2章 §2.7 と同じ:

  $ printf '\xef\xbb\xbflet x = 1\n' > bom.kel
  $ diktor --dump-tokens bom.kel
  bom.kel:1:1: 字句エラー: 予期しない文字です: U+FEFF
  [2]

文字列とコメントの外では、BOM は先頭以外にあっても字句エラーになる。sample.kel の §0 が、BOM を「ソースの
どこにあっても字句エラーにする」と定め、例外を文字列リテラルの中とコメントの中の 2 つに
限っている(sample.kel:40-42)。文字列の中の BOM は値の一部になり、
コメントの中の BOM は読み飛ばされる:

  $ printf 'let x = 1\n\xef\xbb\xbflet y = 2\n' > bom2.kel
  $ diktor --dump-tokens bom2.kel
  bom2.kel:2:1: 字句エラー: 予期しない文字です: U+FEFF
  [2]

  $ printf 'let x = "a\xef\xbb\xbfb"\n' > bomstr.kel
  $ diktor --dump-tokens bomstr.kel
     1  let
     1  x
     1  =
     1  "a\239\187\191b"
     2  <EOF>

  $ printf 'let x = 1 // a\xef\xbb\xbfb\n' > bomcom.kel
  $ diktor --dump-tokens bomcom.kel
     1  let
     1  x
     1  =
     1  1
     2  <EOF>

U+XXXX の形で表示する各区間の代表(C0 の垂直タブ、DEL、C1 の NEL、NBSP、
ソフトハイフン、ゼロ幅スペース、右から左への上書き、ワードジョイナ)。
文字のまま表示する側の代表は test/errloc.t の ¤(U+00A4):

  $ printf 'let x = 1 \x0b 2\n' > c0.kel
  $ diktor --dump-tokens c0.kel
  c0.kel:1:11: 字句エラー: 予期しない文字です: U+000B
  [2]
  $ printf 'let x = 1 \x7f 2\n' > del.kel
  $ diktor --dump-tokens del.kel
  del.kel:1:11: 字句エラー: 予期しない文字です: U+007F
  [2]
  $ printf 'let x = 1 \xc2\x85 2\n' > nel.kel
  $ diktor --dump-tokens nel.kel
  nel.kel:1:11: 字句エラー: 予期しない文字です: U+0085
  [2]
  $ printf 'let x = 1 \xc2\xa0 2\n' > nbsp.kel
  $ diktor --dump-tokens nbsp.kel
  nbsp.kel:1:11: 字句エラー: 予期しない文字です: U+00A0
  [2]
  $ printf 'let x = 1 \xc2\xad 2\n' > shy.kel
  $ diktor --dump-tokens shy.kel
  shy.kel:1:11: 字句エラー: 予期しない文字です: U+00AD
  [2]
  $ printf 'let x = 1 \xe2\x80\x8b 2\n' > zwsp.kel
  $ diktor --dump-tokens zwsp.kel
  zwsp.kel:1:11: 字句エラー: 予期しない文字です: U+200B
  [2]
  $ printf 'let x = 1 \xe2\x80\xae 2\n' > rlo.kel
  $ diktor --dump-tokens rlo.kel
  rlo.kel:1:11: 字句エラー: 予期しない文字です: U+202E
  [2]
  $ printf 'let x = 1 \xe2\x81\xa0 2\n' > wj.kel
  $ diktor --dump-tokens wj.kel
  wj.kel:1:11: 字句エラー: 予期しない文字です: U+2060
  [2]

CR(sample.kel §0)。文字列の外の CR は空白として扱うので、CRLF は改行として働き、単独の CR は
改行にならない。文字列の中の CR はそのまま値に入る:

  $ printf 'let x = 1\r\nlet y = 2\r\n' > crlf.kel
  $ diktor --dump-tokens crlf.kel
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

  $ printf 'let x = 1\rlet y = 2\n' > cronly.kel
  $ diktor --type-check cronly.kel
  cronly.kel:1:11: 構文エラー: 付近のトークンを確認してください
  [2]

  $ printf 'echoln("a\rb")\n' > crstr.kel
  $ diktor crstr.kel | od -c | head -1
  0000000   a  \r   b  \n

エスケープの集合(sample.kel §2)。\n \t \r \a \b \f \v \\ \" \' と \uXXXX、\UXXXXXXXX である。
文字列には、改行をそのまま含めてもよい:

  $ cat > esc.kel <<'KEL'
  > let s = "\a\b\f\v\r\t\n\'\"\\あ\U0001F600"
  > KEL
  $ diktor --dump-tokens esc.kel
     1  let
     1  s
     1  =
     1  "\007\b\012\011\r\t\n'\"\\\227\129\130\240\159\152\128"
     2  <EOF>

  $ printf 'let s = "a\nb"\necholn(s)\n' > rawnl.kel
  $ diktor rawnl.kel
  a
  b

サロゲート、範囲外のコードポイント、未知のエスケープは字句エラーになる(sample.kel §2)。
Uchar.of_int 0xD800 は Invalid_argument を投げるので、先に Uchar.is_valid で調べて字句エラーにする:

  $ cat > surr.kel <<'KEL'
  > let s = "\uD800"
  > KEL
  $ diktor --dump-tokens surr.kel
  surr.kel:1:15: 字句エラー: Unicode エスケープの値がサロゲートか、U+10FFFF を超えています
  [2]

  $ cat > oor.kel <<'KEL'
  > let s = "\U00110000"
  > KEL
  $ diktor --dump-tokens oor.kel
  oor.kel:1:19: 字句エラー: Unicode エスケープの値がサロゲートか、U+10FFFF を超えています
  [2]

  $ cat > badesc.kel <<'KEL'
  > let s = "\q"
  > KEL
  $ diktor --dump-tokens badesc.kel
  badesc.kel:1:11: 字句エラー: 不正なエスケープです
  [2]

小数点で始まる数値は書けない。1._0 と 1.foo は、最長一致で、数値の後ろに識別子が続く形になる
(sample.kel §2。t._0 のようなフィールドの選択と区別するためである):

  $ printf 'let x = .5\n' > dot5.kel
  $ diktor --type-check dot5.kel
  dot5.kel:1:9: 構文エラー: 付近のトークンを確認してください
  [2]

  $ cat > projnum.kel <<'KEL'
  > let x = 1._0
  > let y = 1.foo
  > KEL
  $ diktor --dump-tokens projnum.kel
     1  let
     1  x
     1  =
     1  1.
     1  _0
     1  <NL>
     2  let
     2  y
     2  =
     2  1.
     2  foo
     3  <EOF>

数値の書き間違いも最長一致で複数のトークンに分かれ、字句エラーにはならない(LangSpec 付録 A.2)。
分かれた後ろのトークンで構文解析が進めなくなったとき、診断は数値の先頭を指し、
数値とその直後のトークンを示す。終了コードは構文エラーの 2 のままである:

  $ printf 'let a = 0b102\n' > glued1.kel
  $ diktor --type-check glued1.kel
  glued1.kel:1:9: 構文エラー: 数値リテラル 0b10 の直後に 2 が続いています(数値リテラルの表記を確認してください)
  [2]
  $ printf 'let a = 0x\n' > glued2.kel
  $ diktor --type-check glued2.kel
  glued2.kel:1:9: 構文エラー: 数値リテラル 0 の直後に x が続いています(数値リテラルの表記を確認してください)
  [2]
  $ printf 'let a = 1u\n' > glued3.kel
  $ diktor --type-check glued3.kel
  glued3.kel:1:9: 構文エラー: 数値リテラル 1 の直後に u が続いています(数値リテラルの表記を確認してください)
  [2]
  $ printf 'let a = 1.2.3\n' > glued4.kel
  $ diktor --type-check glued4.kel
  glued4.kel:1:9: 構文エラー: 数値リテラル 1.2 の直後に .3 が続いています(数値リテラルの表記を確認してください)
  [2]
  $ diktor --type-check projnum.kel
  projnum.kel:1:9: 構文エラー: 数値リテラル 1. の直後に _0 が続いています(数値リテラルの表記を確認してください)
  [2]

進めなくなる位置が式の途中でもパターンでも、負の数値リテラルでも同じである。REPL は同じメッセージを出して、セッションを続ける:

  $ cat > gluedpos.kel <<'KEL'
  > let g(x: Int32, y: Int32): Int32 = x
  > let a = g(1, 2x)
  > KEL
  $ diktor --type-check gluedpos.kel
  gluedpos.kel:2:14: 構文エラー: 数値リテラル 2 の直後に x が続いています(数値リテラルの表記を確認してください)
  [2]
  $ cat > gluedpat.kel <<'KEL'
  > let f(x: Int32): Int32 = x match {
  >   case 0b102 => 1
  >   case _ => 0
  > }
  > KEL
  $ diktor --type-check gluedpat.kel
  gluedpat.kel:2:8: 構文エラー: 数値リテラル 0b10 の直後に 2 が続いています(数値リテラルの表記を確認してください)
  [2]
  $ printf 'let a = -0b102\n' > gluedneg.kel
  $ diktor --type-check gluedneg.kel
  gluedneg.kel:1:10: 構文エラー: 数値リテラル 0b10 の直後に 2 が続いています(数値リテラルの表記を確認してください)
  [2]
  $ printf 'let a = 0b102\n1 + 1\n' | diktor --repl
  <stdin>:1:9: 構文エラー: 数値リテラル 0b10 の直後に 2 が続いています(数値リテラルの表記を確認してください)
  _ : Int32 = 2

数値と後ろのトークンの間に空白がある形と、後ろのトークンが英数字でも _ でも . でも始まらない形は、
数値を示さない汎用のメッセージになる。浮動小数の後ろの . はフィールドの選択として
文法に合うので、その後ろの予約語で進めなくなる形は数値の書き間違いとはみなさず、
予約語の誤用の判定(test/reserved_word.t)に任せる。gluedkw は match を識別子に
置き換えると次の { まで読み進められるので、予約語の誤用のメッセージになる。
gluedkw2 は match の後ろの改行が捨てられて次のトークンが 2 行目の let になり、
置き換えても読み進められないので、汎用のメッセージになる。
数値に予約語が隙間なく続いても、文法に合えば受理する:

  $ printf 'let a = 1 x\n' > gluedsp.kel
  $ diktor --type-check gluedsp.kel
  gluedsp.kel:1:11: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let a = 1"s"\n' > gluedtext.kel
  $ diktor --type-check gluedtext.kel
  gluedtext.kel:1:10: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let a = 1.2.match { case _ => 1 }\n' > gluedkw.kel
  $ diktor --type-check gluedkw.kel
  gluedkw.kel:1:13: 構文エラー: 予約語 match はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let a = 1.2.match\nlet b = 2\n' > gluedkw2.kel
  $ diktor --type-check gluedkw2.kel
  gluedkw2.kel:1:13: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let c = true\nlet a = if c then 1else 2\n' > gluedelse.kel
  $ diktor --type-check gluedelse.kel
  c : Boolean
  a : Int32

`{` の判別に例外のある 3 つの位置(sample.kel §0、sample.kel:26-28)。実装は、この位置で先読みを
やめるのではなく、3 種の `{` を 1 つにまとめた %inline lbrace で受理する。
したがって、分類の結果は位置ではなく先読みで決まるが、どの分類でも同じ木になる:

  $ cat > effbrace.kel <<'KEL'
  > effect Print = { print: (String) => {} }
  > effect Fs2 = {}
  > type R1: EffectRow = {Print}
  > type R2: EffectRow = {Print, Fs2}
  > let p(m: String): {} @ {Print} = perform print(m)
  > let z(): {} @ {} = ()
  > KEL
  $ diktor --dump-tokens effbrace.kel | grep '{'
     1  {ty
     1  {rec
     2  {rec
     3  {blk
     4  {rec
     5  {rec
     5  {blk
     6  {rec
     6  {rec
  $ diktor --type-check --no-prelude effbrace.kel
  p : (String) => {} @ {Print}
  z : () => {} @ {}

この 3 つの位置では、分類がどれになっても、行の途中の改行が文の区切りにならない。下の
effect 宣言の本体(1 行目)、EffectRow のエイリアスの右辺(4 行目)、@ の直後
(7 行目)は、どれも内容と } の間に改行を挟んである。分類は {ty と {blk に分かれるが、
{blk の 2 つでも改行は文の区切りにならず、f と g は同じエフェクト行の型になる(ASI の層は第2章 §2.10):

  $ cat > effnl.kel <<'KEL'
  > effect Print = {
  >   print: (String) => {}
  > }
  > type R: EffectRow = {
  >   Print
  > }
  > let f(): {} @ {Print
  > } = perform print("x")
  > let g(): {} @ R = perform print("x")
  > KEL
  $ diktor --dump-tokens effnl.kel | grep '{'
     1  {ty
     2  {rec
     4  {blk
     7  {rec
     7  {blk
     9  {rec
  $ diktor --type-check --no-prelude effnl.kel
  f : () => {} @ {Print}
  g : () => {} @ {Print}

エフェクト行にレコード型のフィールドを書くと、分類は {ty になる。構文解析はこの形を拒否せず、
意味解析の段階が型エラーにする(第3章 §3.23):

  $ printf 'let f(): {} @ {x: Int32} = ()\n' > effield.kel
  $ diktor --type-check effield.kel
  ! effield.kel:1:15: 型エラー: エフェクト行にフィールド x は書けません
  [1]

sample.kel の全文をトークンに分ける(コピー元のリビジョンは test/sample/README.md にある):

  $ diktor --dump-tokens sample/sample.kel | wc -l
  2526
  $ diktor --dump-tokens sample/sample.kel | tail -6
   850  .
   850  parse
   850  (
   850  "456"
   850  )
   882  <EOF>

小数部の省略(1. と 2.e3)と、その後ろの ASI。行末の 1. は NUMBER なので、
文を終えられる:

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

連続するコメント行は NL 1 個になる。生トークンの列では NL が連続しない、という
不変条件(第2章 §2.5)を、このブロックで確かめる:

  $ cat > manycomments.kel <<'KEL'
  > let a = 1
  > // one
  > // two
  > // three
  > let b = 2
  > KEL
  $ diktor --dump-tokens manycomments.kel
     1  let
     1  a
     1  =
     1  1
     1  <NL>
     5  let
     5  b
     5  =
     5  2
     6  <EOF>

先読みキューの長さは定数である。NL が連続しないという不変条件によって、コメントが 64000 行
続いても、処理時間は行数に比例する:

  $ awk 'BEGIN{print "let a = 1"; for(i=0;i<64000;i++) print "// filler"; print "let b = 2"}' > big.kel
  $ timeout 10 diktor --dump-tokens big.kel | tail -3
  64002  =
  64002  2
  64003  <EOF>

節の最上位の => は、節の矢印である。ガードの最上位にある fn の
矢印は、RClause が fn の個数を数えて見送る。fn の矢印で RClause を pop すると、
後ろの改行が文の区切りになってしまう:

  $ cat > guardfn.kel <<'KEL'
  > let g(v) = v match {
  >   case x if fn(y) => y
  >     (1) => x
  >   case _ => 0
  > }
  > KEL
  $ diktor --dump-tokens guardfn.kel
     1  let
     1  g
     1  (
     1  v
     1  )
     1  =
     1  v
     1  match
     1  {blk
     2  case
     2  x
     2  if
     2  fn
     2  (
     2  y
     2  )
     2  =>
     2  y
     3  (
     3  1
     3  )
     3  =>
     3  x
     4  case
     4  _
     4  =>
     4  0
     5  }
     6  <EOF>
  $ diktor --type-check guardfn.kel
  ! guardfn.kel:1:12: 型エラー: 型が一致しません: ((_A) => _B) => _B と Boolean
  [1]

fn の矢印が来ないまま節が終わる壊れた入力でも、閉じ括弧が RClause を
強制的に取り除くので、対応のずれはそこで止まる。取り除かないと、region スタックが
1 段深いまま、ファイルの末尾まで NL が捨てられる:

  $ cat > brokenfn.kel <<'KEL'
  > let z = (v match {
  >   case a if fn => 1
  >   case _ => 0
  > })
  > let p = 1
  > KEL
  $ diktor --dump-tokens brokenfn.kel | tail -7
     4  )
     4  <NL>
     5  let
     5  p
     5  =
     5  1
     6  <EOF>
