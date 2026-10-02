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

## 読み込み

import の循環は、循環を閉じた import 文の位置で報告し、循環に入っているファイルだけを並べる。
自分自身の import も循環である:

  $ cat > cyc_a.kel <<'KEL'
  > from "./cyc_b" import b
  > pub let a: Int32 = 1
  > KEL
  $ cat > cyc_b.kel <<'KEL'
  > from "./cyc_c" import c
  > pub let b: Int32 = 1
  > KEL
  $ cat > cyc_c.kel <<'KEL'
  > from "./cyc_a" import a
  > pub let c: Int32 = 1
  > KEL
  $ diktor cyc_a.kel
  ! cyc_c.kel:1:1: import エラー: import が循環しています: cyc_a.kel → cyc_b.kel → cyc_c.kel → cyc_a.kel
  [1]
  $ printf 'from "./cyc_b" import b\n' > outer.kel
  $ diktor outer.kel
  ! cyc_a.kel:1:1: import エラー: import が循環しています: cyc_b.kel → cyc_c.kel → cyc_a.kel → cyc_b.kel
  [1]
  $ printf 'from "./self" import x\npub let x: Int32 = 1\n' > self.kel
  $ diktor self.kel
  ! self.kel:1:1: import エラー: import が循環しています: self.kel → self.kel
  [1]

パスの形の誤りと、見つからない import 先。見つからないときは、探したファイルを括弧の中に出す。
表示するパスは、import を書いたファイルの位置から . と .. を相殺した綴りである:

  $ printf 'from "./nothere" import x\n' > nf.kel
  $ diktor nf.kel
  ! nf.kel:1:1: import エラー: import 先が見つかりません: ./nothere(nothere.kel)
  [1]
  $ mkdir -p up/lib
  $ printf 'from "../none" import x\n' > up/lib/m.kel
  $ printf 'from "./lib/m" import x\n' > up/main.kel
  $ diktor up/main.kel
  ! up/lib/m.kel:1:1: import エラー: import 先が見つかりません: ../none(up/none.kel)
  [1]
  $ printf 'from "C:/x" import x\n' > col.kel
  $ diktor col.kel
  ! col.kel:1:1: import エラー: import のパスにコロンは書けません("kel:" などの前置は予約されています): C:/x
  [1]
  $ printf 'from "/etc/x" import x\n' > abs.kel
  $ diktor abs.kel
  ! abs.kel:1:1: import エラー: import のパスに絶対パスは書けません: /etc/x
  [1]
  $ printf 'from "./lib/leaf.kel" import base\n' > ext.kel
  $ diktor ext.kel
  ! ext.kel:1:1: import エラー: import のパスに拡張子 .kel は書きません: ./lib/leaf.kel
  [1]
  $ cat > bs.kel <<'KEL'
  > from "lib\\a" import x
  > KEL
  $ diktor bs.kel
  ! bs.kel:1:1: import エラー: import のパスの区切りは / です: lib\a
  [1]
  $ printf 'from "./a/../b" import x\n' > comp.kel
  $ diktor comp.kel
  ! comp.kel:1:1: import エラー: import のパスの成分が不正です: ./a/../b
  [1]
  $ printf 'from "./../b" import x\n' > mix.kel
  $ diktor mix.kel
  ! mix.kel:1:1: import エラー: import のパスの ./ と ../ は混ぜられません: ./../b
  [1]

./ と ../ で始まらないパスは検索パス(--import-path)の中を探す。検索パスの既定は空で、
複数のディレクトリで見つかれば誤りにする。候補は --import-path を書いた順に並べる。
同じファイルを別の綴りの検索パスで見つけたものは 1 つと数える:

  $ mkdir -p sp/std alt/std
  $ printf 'pub let x: Int32 = 1\n' > sp/std/list.kel
  $ cp sp/std/list.kel alt/std/list.kel
  $ printf 'from "std/list" import x\nlet y: Int32 = x\n' > usesp.kel
  $ diktor usesp.kel
  ! usesp.kel:1:1: import エラー: import 先が検索パスに見つかりません: std/list
  [1]
  $ diktor --import-path sp --import-path alt usesp.kel
  ! usesp.kel:1:1: import エラー: import 先が検索パスに複数あります: std/list(sp/std/list.kel、alt/std/list.kel)
  [1]
  $ diktor --import-path alt --import-path sp usesp.kel
  ! usesp.kel:1:1: import エラー: import 先が検索パスに複数あります: std/list(alt/std/list.kel、sp/std/list.kel)
  [1]

コマンド行で連結したファイルは import できない。import 先が開けないときは終了コード 64 にする:

  $ printf 'pub let x: Int32 = 1\n' > ca.kel
  $ printf 'from "./ca" import x\n' > cb.kel
  $ diktor ca.kel cb.kel
  ! cb.kel:1:1: import エラー: コマンド行で連結したファイルは import できません: ./ca
  [1]
  $ mkdir -p dir.kel
  $ printf 'from "./dir" import x\n' > dd.kel
  $ diktor dd.kel
  diktor: ファイルを開けません: dir.kel: Is a directory
  [64]
