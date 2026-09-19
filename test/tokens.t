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

先頭の BOM は字句エラー(仕様 §0)。BOM・C0 制御文字・DEL と C1 制御文字・
NBSP・ソフトハイフン・U+200B〜U+200F・U+2028〜U+202E・U+2060〜U+2064 は
字面ではなく U+XXXX で出し、それ以外は字面のまま(M21 / F-C6。生のまま
出すとゴールデンに焼けない。集合は第2章 §2.7 と同じ):

  $ printf '\xef\xbb\xbflet x = 1\n' > bom.kel
  $ diktor --dump-tokens bom.kel
  bom.kel:1:1: 字句エラー: unexpected character: U+FEFF
  [2]

文字列とコメントの外なら、BOM は先頭以外でも読めない(仕様が定めているのは
先頭だけだが、読めないことに変わりはない — D102 / D111。文字列の中の BOM は
値の一部になり、コメントの中の BOM は読み飛ばされる):

  $ printf 'let x = 1\n\xef\xbb\xbflet y = 2\n' > bom2.kel
  $ diktor --dump-tokens bom2.kel
  bom2.kel:2:1: 字句エラー: unexpected character: U+FEFF
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

U+XXXX に落とす各区間の代表(C0 の垂直タブ・DEL・C1 の NEL・NBSP・
ソフトハイフン・ゼロ幅スペース・右から左への上書き・ワードジョイナ)。
落とさない側の代表は test/errloc.t の ¤(U+00A4):

  $ printf 'let x = 1 \x0b 2\n' > c0.kel
  $ diktor --dump-tokens c0.kel
  c0.kel:1:11: 字句エラー: unexpected character: U+000B
  [2]
  $ printf 'let x = 1 \x7f 2\n' > del.kel
  $ diktor --dump-tokens del.kel
  del.kel:1:11: 字句エラー: unexpected character: U+007F
  [2]
  $ printf 'let x = 1 \xc2\x85 2\n' > nel.kel
  $ diktor --dump-tokens nel.kel
  nel.kel:1:11: 字句エラー: unexpected character: U+0085
  [2]
  $ printf 'let x = 1 \xc2\xa0 2\n' > nbsp.kel
  $ diktor --dump-tokens nbsp.kel
  nbsp.kel:1:11: 字句エラー: unexpected character: U+00A0
  [2]
  $ printf 'let x = 1 \xc2\xad 2\n' > shy.kel
  $ diktor --dump-tokens shy.kel
  shy.kel:1:11: 字句エラー: unexpected character: U+00AD
  [2]
  $ printf 'let x = 1 \xe2\x80\x8b 2\n' > zwsp.kel
  $ diktor --dump-tokens zwsp.kel
  zwsp.kel:1:11: 字句エラー: unexpected character: U+200B
  [2]
  $ printf 'let x = 1 \xe2\x80\xae 2\n' > rlo.kel
  $ diktor --dump-tokens rlo.kel
  rlo.kel:1:11: 字句エラー: unexpected character: U+202E
  [2]
  $ printf 'let x = 1 \xe2\x81\xa0 2\n' > wj.kel
  $ diktor --dump-tokens wj.kel
  wj.kel:1:11: 字句エラー: unexpected character: U+2060
  [2]

CR(仕様 §0。文字列の外の CR は空白、CRLF が改行として働き、単独の CR は
改行にならない。文字列の中の CR はそのまま値に入る):

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
  cronly.kel:1:11: パースエラー(付近のトークンを確認してください)
  [2]

  $ printf 'echoln("a\rb")\n' > crstr.kel
  $ diktor crstr.kel | od -c | head -1
  0000000   a  \r   b  \n

エスケープの集合(仕様 §2。\n \t \r \a \b \f \v \\ \" \' と \uXXXX / \UXXXXXXXX。
生の改行も含めてよい):

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

サロゲート・範囲外のコードポイントと未知のエスケープは字句エラー(仕様 §2。
Uchar.of_int 0xD800 は Invalid_argument を投げるので、is_valid で先に落とす):

  $ cat > surr.kel <<'KEL'
  > let s = "\uD800"
  > KEL
  $ diktor --dump-tokens surr.kel
  surr.kel:1:15: 字句エラー: invalid unicode escape (out of range or surrogate)
  [2]

  $ cat > oor.kel <<'KEL'
  > let s = "\U00110000"
  > KEL
  $ diktor --dump-tokens oor.kel
  oor.kel:1:19: 字句エラー: invalid unicode escape (out of range or surrogate)
  [2]

  $ cat > badesc.kel <<'KEL'
  > let s = "\q"
  > KEL
  $ diktor --dump-tokens badesc.kel
  badesc.kel:1:11: 字句エラー: invalid escape sequence
  [2]

先頭小数点は許さず、最長一致で 1._0 / 1.foo は「数値 + 識別子」に読む
(仕様 §2。t._0 の射影と読み分けるため):

  $ printf 'let x = .5\n' > dot5.kel
  $ diktor --type-check dot5.kel
  dot5.kel:1:9: パースエラー(付近のトークンを確認してください)
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

`{` の読み分けの 3 文脈(仕様 §0 の追加行)。実装は文脈で先読みを止めるのでは
なく、3 種を束ねた %inline lbrace で受ける(D12 / FIX-2b)。したがって分類の
結果は文脈ではなく先読みで決まるが、どの分類でも同じ木になる:

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
  p : (String) => {} @ {Print extends R1}
  z : () => {}

エフェクト行にレコード型のフィールドを書くと、分類は {ty になるが拒否は
意味の層が行う(「決めずに運んで、意味の層で決める」— §3.23):

  $ printf 'let f(): {} @ {x: Int32} = ()\n' > effield.kel
  $ diktor --type-check effield.kel
  ! effield.kel:1:15: 型エラー: エフェクト行にフィールド x は書けません
  [1]

sample.kel 全文のトークン化(2741 トークン。スパイク 260829-1 が数えた 2526 は
改訂前 — 親 2fd2d2e — の写しに対するもので、2026-09-12 の改訂で 776 行になった):

  $ diktor --dump-tokens sample/sample.kel | wc -l
  2741
  $ diktor --dump-tokens sample/sample.kel | tail -6
   748  .
   748  parse
   748  (
   748  "456"
   748  )
   777  <EOF>

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

連続するコメント行は NL 1 個に潰れる(M18 / F3 / D58 の不変条件
「生トークン列に NL は連続しない」の明示):

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

先読みキューは定数長(かつてはコメント 64000 行で二次の 34 秒。
不変条件 D58 でキュー長が高々 3 に落ち、線形になった):

  $ awk 'BEGIN{print "let a = 1"; for(i=0;i<64000;i++) print "// filler"; print "let b = 2"}' > big.kel
  $ timeout 10 diktor --dump-tokens big.kel | tail -3
  64002  =
  64002  2
  64003  <EOF>

節の最上位の => は必ず節の矢印(M18 / F2 / D57。ガード最上位の fn の
矢印は RClause が本数を数えて見送る。かつては fn の矢印で region が
早期 pop し、続きの改行に区切りが入った):

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

壊れた入力(fn の矢印が来ないまま節が終わる)でも、閉じ括弧が RClause を
強制解消するので、ずれはそこで止まる(M18 検証。かつては region が
1 枚深いままファイル末尾まで NL が落ちた):

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
