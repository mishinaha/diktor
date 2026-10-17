予約語(LangSpec §2.2)を識別子の位置に書くと、構文エラーになる。
予約語を識別子に置き換えると次のトークンまで読み進められるときは、
予約語の綴りと位置を示し、その位置には書けないと言う文面になる。ファイルを読むときの終了コードは 2 で、
対話的な実行ではセッションが続く。

束縛の名前、引数、型パラメータ:

  $ printf 'let then = 1\n' > bind.kel
  $ diktor bind.kel
  bind.kel:1:5: 構文エラー: 予約語 then はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let rec val(x: Int32): Int32 = x\n' > recname.kel
  $ diktor recname.kel
  recname.kel:1:9: 構文エラー: 予約語 val はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let f(else: Int32): Int32 = 1\n' > param.kel
  $ diktor param.kel
  param.kel:1:7: 構文エラー: 予約語 else はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let f[with](x: Int32): Int32 = x\n' > typaram.kel
  $ diktor typaram.kel
  typaram.kel:1:7: 構文エラー: 予約語 with はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let x = true\nlet true = 1\n' > bool.kel
  $ diktor bool.kel
  bool.kel:2:5: 構文エラー: 予約語 true はここには書けません(予約語は識別子に使えません)
  [2]

レコードのラベル。レコード式、更新、レコード型、レコードパターン、フィールドの選択、
名前付き引数に書いた形である。
ただし、その位置で式や宣言を始められる予約語は、後ろのブロックのとおり汎用の文面のままになる:

  $ printf 'let r = {then = 1}\n' > reclabel.kel
  $ diktor reclabel.kel
  reclabel.kel:1:10: 構文エラー: 予約語 then はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let r = {a = 1}\nlet s = {r with match = 2}\n' > update.kel
  $ diktor update.kel
  update.kel:2:17: 構文エラー: 予約語 match はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let f(x: {if: Int32}): Int32 = 1\n' > tylabel.kel
  $ diktor tylabel.kel
  tylabel.kel:1:11: 構文エラー: 予約語 if はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let p = {a = 1, b = 2}\nlet {a, then} = p\n' > patlabel.kel
  $ diktor patlabel.kel
  patlabel.kel:2:9: 構文エラー: 予約語 then はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let r = {a = 1}\nlet z = r.module\n' > select.kel
  $ diktor select.kel
  select.kel:2:11: 構文エラー: 予約語 module はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let f(x: Int32): Int32 = x\nlet y = f(import = 1)\n' > namedarg.kel
  $ diktor namedarg.kel
  namedarg.kel:2:11: 構文エラー: 予約語 import はここには書けません(予約語は識別子に使えません)
  [2]

式の中の変数、case のパターン、エフェクトの操作名、extern の名前:

  $ printf 'let g(x: Int32): Int32 = x\nlet y = g(handle)\n' > arg.kel
  $ diktor arg.kel
  arg.kel:2:11: 構文エラー: 予約語 handle はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let x = 1 match { case rec => 1 }\n' > casepat.kel
  $ diktor casepat.kel
  casepat.kel:1:24: 構文エラー: 予約語 rec はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'effect E = { run: () => Int32 }\n' > effop.kel
  $ diktor effop.kel
  effop.kel:1:14: 構文エラー: 予約語 run はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'extern "c" let pub(x: Int32): Int32\n' > extern.kel
  $ diktor extern.kel
  extern.kel:1:16: 構文エラー: 予約語 pub はここには書けません(予約語は識別子に使えません)
  [2]

予約語を識別子に置き換えても次のトークンで詰まる入力は、汎用の文面のままである。
括弧で囲まない if のオペランド、宣言の後ろの import、右辺の書き忘れ、
予約語で終わる入力がそれにあたる。右辺の書き忘れは、= が続きを求めたまま
行をまたいで詰まるので、= の終わりを指し、詰まったトークンの位置を添える:

  $ printf 'let g = 1 + if true then 1 else 2\n' > operand.kel
  $ diktor operand.kel
  operand.kel:1:13: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let x = 1\nfrom "./a" import b\n' > late.kel
  $ diktor late.kel
  late.kel:2:1: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let x =\nlet y = 2\n' > norhs.kel
  $ diktor norhs.kel
  norhs.kel:1:8: 構文エラー: この位置の後ろ、2:1 のトークンが文法に合いません
  [2]
  $ printf 'let then\n' > eof.kel
  $ diktor eof.kel
  eof.kel:1:5: 構文エラー: 付近のトークンを確認してください
  [2]

予約語がその位置で式か宣言を始められるときは、予約語ではなく次のトークンで詰まり、汎用の文面になる。
レコード式のラベルの type と if、呼び出しの引数の if がそれにあたる:

  $ printf 'let r = {type = 1}\n' > decllabel.kel
  $ diktor decllabel.kel
  decllabel.kel:1:15: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let r = {if = 1}\n' > exprlabel.kel
  $ diktor exprlabel.kel
  exprlabel.kel:1:13: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let g(x: Int32): Int32 = x\nlet y = g(if)\n' > exprarg.kel
  $ diktor exprarg.kel
  exprarg.kel:2:13: 構文エラー: 付近のトークンを確認してください
  [2]

対話的な実行でも、予約語の次のトークンが同じ行にあれば同じ文面を出し、
セッションは続く。行が式を始める予約語(ここでは if)で終わるときは、
続きの行を待つ:

  $ printf 'let then = 1\nlet x = 2\nlet y = if\ntrue then 1 else 0\n' | diktor --repl
  <stdin>:1:5: 構文エラー: 予約語 then はここには書けません(予約語は識別子に使えません)
  x : Int32 = 2
  y : Int32 = 1

予約語の誤用の判定は、予約語を識別子に置き換えて次のトークンまで読み進められることを
求める。対話的な実行は入力ごとに別にパースするので、行末の予約語では次のトークンが EOF に
なり、置き換えた入力がそこで終われることが判定の条件の 1 つになる。

nlword.kel の 1 行目の let then は、let x に置き換えても EOF では終われないので、
対話的な実行は汎用の文面を出し、2 行目の = 1 を別の入力として報告する。
ファイルでは次の行の = まで読むので、予約語の文面になる:

  $ printf 'let then\n= 1\nlet y = 2\n' > nlword.kel
  $ diktor nlword.kel
  nlword.kel:1:5: 構文エラー: 予約語 then はここには書けません(予約語は識別子に使えません)
  [2]
  $ diktor --repl < nlword.kel
  <stdin>:1:5: 構文エラー: 付近のトークンを確認してください
  <stdin>:2:1: 構文エラー: 付近のトークンを確認してください
  y : Int32 = 2

eolword.kel の 1 行目の let x = then は、let x = y に置き換えると EOF で終われるので、
対話的な実行は予約語の文面を出し、2 行目を処理する。ファイルでは then の後ろの改行が
捨てられて次のトークンが 2 行目の let になり、置き換えた入力はそこで読み進められないので、
汎用の文面になる:

  $ printf 'let x = then\nlet y = 2\n' > eolword.kel
  $ diktor eolword.kel
  eolword.kel:1:9: 構文エラー: 付近のトークンを確認してください
  [2]
  $ diktor --repl < eolword.kel
  <stdin>:1:9: 構文エラー: 予約語 then はここには書けません(予約語は識別子に使えません)
  y : Int32 = 2

式を始める予約語を、括弧で囲まずに演算子のオペランドに書いた形は、汎用の文面のままである。
識別子に置き換えると次の ( まで進めるが、括弧を置けば同じ予約語を書ける位置だからである:

  $ printf 'let g = 1 + if (true) then 1 else 2\n' > operand2.kel
  $ diktor operand2.kel
  operand2.kel:1:13: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let g = 1 + fn(x: Int32) => x\n' > operandfn.kel
  $ diktor operandfn.kel
  operandfn.kel:1:13: 構文エラー: 付近のトークンを確認してください
  [2]

予約語を識別子として書いたのではなく、位置を誤って書いた形でも、
識別子に置き換えると呼び出しや末尾ブロックとして読み進められるときは、同じ文面になる。
前置の handle と match(LangSpec では後置)、import と from の順序の誤りがそれにあたる。
文面はその位置に書けないことを先に言うので、これらでも誤りにならない:

  $ printf 'let f(): Int32 = 1\nlet r = handle { f() } with { x => x }\n' > prehandle.kel
  $ diktor prehandle.kel
  prehandle.kel:2:9: 構文エラー: 予約語 handle はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'let x = 1\nlet y = match(x) { case 1 => 2, case _ => 3 }\n' > prematch.kel
  $ diktor prematch.kel
  prematch.kel:2:9: 構文エラー: 予約語 match はここには書けません(予約語は識別子に使えません)
  [2]
  $ printf 'import { b } from "./a"\nlet x = 1\n' > jsimport.kel
  $ diktor jsimport.kel
  jsimport.kel:1:1: 構文エラー: 予約語 import はここには書けません(予約語は識別子に使えません)
  [2]
