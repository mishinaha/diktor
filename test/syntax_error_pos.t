構文エラーの位置。
文法には合うが形を拒否する構文エラーは、拒否した構文の始まりを指す。
文法に合わない入力の汎用の文面(付近のトークンを確認してください、と、この位置の後ろ、…)
では、前のトークンが続きを求めていて(行末の演算子やカンマ、括弧の中)、
文法に合わないトークンがそれより後ろの行にあるときは、前のトークンの終わりを主な位置にし、
合わなかったトークンの位置を本文に添える。
予約語の誤用(test/reserved_word.t)と数値の綴り間違い(test/tokens.t)の文面は、
この規則によらず、予約語と数値の位置を指す。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

## 形を拒否する構文エラー

ブロックの中の宣言は、ブロックの終わりではなく宣言の始まりを指す:

  $ cat > blkdecl.kel <<'KEL'
  > let f() = {
  >   newtype U = U(Int32)
  >   let a = 1
  >   a
  > }
  > let z = 2
  > KEL
  $ diktor blkdecl.kel
  blkdecl.kel:2:3: 構文エラー: この宣言はブロック内では使えません(let / let rec / 式のみ)
  [2]

  $ printf 'let f() = {\n  pub let x = 1\n  x\n}\n' > blkpub.kel
  $ diktor blkpub.kel
  blkpub.kel:2:3: 構文エラー: ブロックの中の let には pub を付けられません(with より後ろの宣言は公開できません)
  [2]

  $ printf 'let f() = {\n  pub let rec g(x) = x\n  g(1)\n}\n' > blkpubrec.kel
  $ diktor blkpubrec.kel
  blkpubrec.kel:2:3: 構文エラー: ブロックの中の let rec には pub を付けられません(with より後ろの宣言は公開できません)
  [2]

with の右辺は、右辺の式の始まりを指す:

  $ printf 'let f() = {\n  with x = 1\n  x\n}\n' > withnc.kel
  $ diktor withnc.kel
  withnc.kel:2:12: 構文エラー: with の右辺は関数呼び出しでなければなりません
  [2]

resume の引数は、次の節が後ろの行にあっても resume の行を指す:

  $ cat > reslabel.kel <<'KEL'
  > effect Ask = {
  >   ask: () => Int32
  > }
  > let f(): Int32 @ {Ask} = perform ask()
  > let g(): Int32 = f() handle {
  >   case ask() => resume(x = 1)
  > 
  >   case return(v) => v
  > }
  > KEL
  $ diktor reslabel.kel
  reslabel.kel:6:17: 構文エラー: resume の引数にラベルは付けられません
  [2]
  $ sed 's/resume(x = 1)/resume(1, 2)/' reslabel.kel > res2.kel
  $ diktor res2.kel
  res2.kel:6:17: 構文エラー: resume の引数は高々1個です
  [2]

pub を付けた type instance、ラベルの大文字、ヴァリアントのラベル付き引数、レコード更新の基底:

  $ printf 'newtype N = N(Int32)\npub type instance Show[N] {\n  let show(x) = "n"\n}\n\nlet b = 2\n' > pubinst.kel
  $ diktor pubinst.kel
  pubinst.kel:2:1: 構文エラー: type instance に pub は付けられません
  [2]
  $ printf 'let r = {a = 1}\nlet x = r.Foo\n\nlet b = 2\n' > upper.kel
  $ diktor upper.kel
  upper.kel:2:11: 構文エラー: レコードのラベルに大文字識別子は使えません: Foo
  [2]
  $ printf 'let x = #Foo(a = 1, b = 2)\n\nlet b = 2\n' > varlbl.kel
  $ diktor varlbl.kel
  varlbl.kel:1:9: 構文エラー: #Foo(...) にラベル付き引数は使えません
  [2]
  $ printf 'let f(v) = v match {\n  case #Foo(a = x) => x\n}\n' > varpat.kel
  $ diktor varpat.kel
  varpat.kel:2:8: 構文エラー: #Foo(...) パターンにラベル付き引数は使えません
  [2]
  $ printf 'let r = {a = 1}\nlet s = {Foo with a = 2}\n\nlet b = 2\n' > upd.kel
  $ diktor upd.kel
  upd.kel:2:10: 構文エラー: レコード更新の基底は小文字始まりの識別子 1 個です
  [2]

## 文法に合わないトークン

続きの無い二項演算子、閉じていない括弧、括弧の中のカンマの抜けは、前のトークンの終わりを指す:

  $ printf 'let x = 1 +\n\n\nlet b = 2\n' > opend.kel
  $ diktor opend.kel
  opend.kel:1:12: 構文エラー: この位置の後ろ、4:1 のトークンが文法に合いません
  [2]
  $ printf 'let x = (1, 2\n\nlet b = 2\n' > paren.kel
  $ diktor paren.kel
  paren.kel:1:14: 構文エラー: この位置の後ろ、3:1 のトークンが文法に合いません
  [2]
  $ printf 'let f(a, b) = a\nlet y = f(\n  1\n  2\n)\n' > comma.kel
  $ diktor comma.kel
  comma.kel:3:4: 構文エラー: この位置の後ろ、4:3 のトークンが文法に合いません
  [2]

前のトークンが文を終えられ、括弧の外にあるときは、行頭の余った閉じ括弧そのものを指す:

  $ printf 'let x = 1\n)\n' > stray.kel
  $ diktor stray.kel
  stray.kel:2:1: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let f() = {\n  let x = 1\n  x\n}\n}\n' > strayb.kel
  $ diktor strayb.kel
  strayb.kel:5:1: 構文エラー: 付近のトークンを確認してください
  [2]

同じ行にあるときと、区切りになった改行の後ろにあるときは、合わないトークンを指す:

  $ printf 'let x = 1 + * 2\n' > sameline.kel
  $ diktor sameline.kel
  sameline.kel:1:13: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let x = 1\n\n\nval y: Int32\n' > afternl.kel
  $ diktor afternl.kel
  afternl.kel:4:1: 構文エラー: 付近のトークンを確認してください
  [2]

## 対話的な実行

対話的な実行でも、次の入力の先頭ではなく、誤りのある宣言を指す:

  $ printf 'let a = 1\nlet z = { newtype M = M(Int32); 1 }\nlet b = 2\n' | diktor --repl
  a : Int32 = 1
  <stdin>:2:11: 構文エラー: この宣言はブロック内では使えません(let / let rec / 式のみ)
  b : Int32 = 2

括弧の中で続きを待った入力が次の行で合わなくなったときも、前のトークンの終わりを指す:

  $ printf 'let x = (1 +\n)\nlet y = 2\n' | diktor --repl
  <stdin>:1:13: 構文エラー: この位置の後ろ、2:1 のトークンが文法に合いません
  y : Int32 = 2
