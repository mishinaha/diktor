import 文と、ファイルの名前空間。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

## 字句と構文

import の直後の { は改行を区切りにしない括弧で、--dump-tokens では {rec と出る。
波括弧の中の改行は区切り(<NL>)にならない:

  $ cat > nl2.kel <<'KEL'
  > from "./a" import {
  >   A,
  >   b,
  > }
  > KEL
  $ diktor --dump-tokens nl2.kel
     1  from
     1  "./a"
     1  import
     1  {rec
     2  A
     2  ,
     3  b
     3  ,
     4  }
     5  <EOF>

--dump-ast は import 文を宣言の前に出す。import の後の ;; と、from と import の間の改行は通る:

  $ printf 'from "./a" import base;; from "./b" import { C, d }\nlet y = 1\n' > semi.kel
  $ diktor --dump-ast semi.kel
  (import "./a" (base))
  (import "./b" (C) (d))
  (dlet (binding y = 1))
  $ printf 'from "p"\nimport M.f\n' > split.kel
  $ diktor --dump-ast split.kel
  (import "p" (M f))
  $ diktor --dump-ast nl2.kel
  (import "./a" (A) (b))

名前は 2 段まで。ファイルの途中、トップレベルの with の後ろの import、空の {}、波括弧の中の
カンマの無い並びは、パースエラーになる:

  $ printf 'from "./lib/leaf" import D.E.f\n' > deep.kel
  $ diktor deep.kel
  deep.kel:1:29: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'let x = 1\nfrom "./a" import b\n' > late.kel
  $ diktor late.kel
  late.kel:2:1: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'with x = f()\nfrom "./a" import b\n' > wth.kel
  $ diktor wth.kel
  wth.kel:2:1: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'from "./a" import {}\n' > empty.kel
  $ diktor empty.kel
  empty.kel:1:20: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'from "./a" import {\n  A\n  b\n}\n' > nl.kel
  $ diktor nl.kel
  nl.kel:3:3: パースエラー(付近のトークンを確認してください)
  [2]

from と import は予約語である:

  $ printf 'let from = 1\n' > letfrom.kel
  $ diktor letfrom.kel
  letfrom.kel:1:5: パースエラー(付近のトークンを確認してください)
  [2]

差し替えたプレリュードと対話的な実行には import を書けない:

  $ printf 'from "./a" import b\n' > pre.kel
  $ printf 'let y = 1\n' > use.kel
  $ diktor --prelude pre.kel use.kel
  pre.kel:1:1: 構文エラー: import はコマンド行で渡したファイルにだけ書けます
  [2]
  $ printf 'from "./a" import b\n' | diktor --repl
  <stdin>:1:1: 構文エラー: import は対話的な実行では書けません

## ブロックの中の pub

ブロックの中の let と let rec に pub を付けると構文エラーになる。トップレベルの with より後ろの
文もブロックなので、同じく拒否する。位置はパーサが最後に読んだトークンである:

  $ printf 'let z = { pub let x: Int32 = 1; x }\n' > pb1.kel
  $ diktor pb1.kel
  pb1.kel:2:1: 構文エラー: ブロックの中の let には pub を付けられません(with より後ろの宣言は公開できません)
  [2]
  $ printf 'with x = 1\npub let rec f(n: Int32): Int32 = n\n' > pb2.kel
  $ diktor pb2.kel
  pb2.kel:3:1: 構文エラー: ブロックの中の let rec には pub を付けられません(with より後ろの宣言は公開できません)
  [2]
