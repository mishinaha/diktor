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

## ファイルの名前空間

型を import するとコンストラクタも入る。import 先の非公開の補助関数は、import した側の同名の
関数と衝突せず、それぞれ自分のファイルの helper を使う(4.0 と ok!)。非公開の補助関数は、
import した側からは見えない:

  $ mkdir -p ok/lib
  $ cat > ok/lib/shape.kel <<'KEL'
  > pub newtype Shape = Circle(Float64) | Square(Float64)
  > let helper(x: Float64): Float64 = x * x
  > pub let area(s: Shape): Float64 = s match {
  >   case Circle(r) => 3.0 * helper(r)
  >   case Square(a) => helper(a)
  > }
  > KEL
  $ cat > ok/main.kel <<'KEL'
  > from "./lib/shape" import { Shape, area, }
  > let helper(x: String): String = x + "!"
  > echoln(show(area(Square(2.0))))
  > echoln(helper("ok"))
  > KEL
  $ (cd ok && diktor main.kel)
  4.0
  ok!
  $ printf 'from "./lib/shape" import area\nlet h: Float64 = helper(2.0)\n' > ok/priv.kel
  $ (cd ok && diktor priv.kel)
  ! priv.kel:2:18: 型エラー: 未束縛の変数: helper
  [1]

ダイヤモンドの import では、共有のファイルを 1 回だけ初期化し、依存される側から順に初期化する。
from と import の間で改行してもよい:

  $ mkdir -p dia/lib
  $ cat > dia/lib/leaf.kel <<'KEL'
  > echoln("init leaf")
  > pub let base: Int32 = 10
  > KEL
  $ cat > dia/lib/left.kel <<'KEL'
  > from "./leaf" import base
  > echoln("init left")
  > pub let l: Int32 = base + 1
  > KEL
  $ cat > dia/lib/right.kel <<'KEL'
  > from "./leaf" import base
  > echoln("init right")
  > pub let r: Int32 = base + 2
  > KEL
  $ cat > dia/main.kel <<'KEL'
  > from "./lib/left" import l
  > from "./lib/right"
  >   import { r, }
  > echoln("init main")
  > echoln(show(l + r))
  > KEL
  $ (cd dia && diktor main.kel)
  init leaf
  init left
  init right
  init main
  23

import を書いた順が初期化の順を決める:

  $ cat > dia/main2.kel <<'KEL'
  > from "./lib/right" import r
  > from "./lib/left" import l
  > echoln("init main")
  > echoln(show(l + r))
  > KEL
  $ (cd dia && diktor main2.kel)
  init leaf
  init right
  init left
  init main
  23

公開されていない名前と存在しない名前。pub の無い module は import できない:

  $ mkdir -p pv/lib
  $ cat > pv/lib/a.kel <<'KEL'
  > let hidden: Int32 = 1
  > pub let shown: Int32 = 2
  > module Inner { pub let f(x: Int32): Int32 = x }
  > KEL
  $ printf 'from "./lib/a" import hidden\n' > pv/m1.kel
  $ (cd pv && diktor m1.kel)
  ! m1.kel:1:23: import エラー: ./lib/a の hidden は公開されていません
  [1]
  $ printf 'from "./lib/a" import Nope\n' > pv/m2.kel
  $ (cd pv && diktor m2.kel)
  ! m2.kel:1:23: import エラー: ./lib/a に Nope という公開の宣言はありません
  [1]
  $ printf 'from "./lib/a" import Inner.f\n' > pv/m3.kel
  $ (cd pv && diktor m3.kel)
  ! m3.kel:1:23: import エラー: ./lib/a の Inner は公開されていません
  [1]

名前の衝突。2 つの import が別々の宣言を同じ名前で束縛すると誤りになる。シンボリックリンクを
通した別の綴りで同じ宣言を重ねて束縛するのは構わない。import した名前と同じ名前をトップレベルで
宣言することと、import した型のコンストラクタと同じ名前のコンストラクタを宣言することも誤りになる:

  $ mkdir -p cl/lib
  $ printf 'pub let f(x: Int32): Int32 = x\npub newtype T = Leaf\n' > cl/lib/a.kel
  $ printf 'pub let f(x: Int32): Int32 = x + 1\nnewtype V = Leaf\n' > cl/lib/b.kel
  $ printf 'from "./lib/a" import f\nfrom "./lib/b" import f\n' > cl/m1.kel
  $ (cd cl && diktor m1.kel)
  ! m1.kel:2:23: import エラー: f は ./lib/a からも import しています(別の宣言です)
  [1]
  $ ln -s lib cl/lib2
  $ printf 'from "./lib/a" import f\nfrom "./lib2/a" import f\nlet y: Int32 = f(1)\n' > cl/m2.kel
  $ (cd cl && diktor --type-check m2.kel)
  y : Int32
  $ printf 'from "./lib/a" import f\nlet f(x: Int32): Int32 = x\n' > cl/m3.kel
  $ (cd cl && diktor m3.kel)
  ! m3.kel:2:1: 型エラー: f は import した名前と同じです
  [1]
  $ printf 'from "./lib/a" import T\nnewtype W = Leaf\n' > cl/m5.kel
  $ (cd cl && diktor m5.kel)
  ! m5.kel:2:1: 型エラー: コンストラクタ Leaf は import した型 T のコンストラクタと同じ名前です
  [1]

コンストラクタの一意性はファイルの中で決まる。lib/a.kel と lib/b.kel はどちらも Leaf を持つが、
b の型を import しなければ衝突しない。2 つのファイルを連結すると 1 個のファイルなので衝突する:

  $ printf 'from "./lib/a" import T\nfrom "./lib/b" import f\nlet t: T = Leaf\n' > cl/m4.kel
  $ (cd cl && diktor --type-check m4.kel)
  t : T
  $ (cd cl && diktor --type-check lib/a.kel lib/b.kel)
  ! lib/b.kel:2:1: 型エラー: コンストラクタ Leaf が二重に宣言されています(コンストラクタ名はファイルの中で一意)
  [1]

別々のファイルの同じ名前の型は別の型である。1 つの診断に並ぶときは、ファイルを添えて区別する:

  $ printf 'pub newtype T = T1\npub let v: T = T1\n' > cl/lib/t.kel
  $ printf 'from "./lib/t" import v\nnewtype T = T2\nlet w: T = v\n' > cl/m6.kel
  $ (cd cl && diktor m6.kel)
  ! m6.kel:3:5: 型エラー: 注釈された型を満たしません(型が一致しません: T(m6.kel) と T(lib/t.kel))
  [1]

## インスタンスと孤児規則

インスタンスは import で指定しなくても見える。インスタンスはクラスか型を宣言したファイルにだけ
書け、標準環境のクラスと標準環境の型の組は標準環境だけが持つ。標準環境は Eq[List[_]] と
Eq[Option[_]] を持つ:

  $ mkdir -p or/lib
  $ cat > or/lib/p.kel <<'KEL'
  > pub newtype P = P(Int32)
  > type instance Show[P] { let show(p) = p match { case P(n) => "P" + show(n) } }
  > KEL
  $ printf 'pub newtype Q = Q(Int32)\n' > or/lib/q.kel
  $ printf 'from "./lib/p" import P\necholn(show(P(1)))\n' > or/m1.kel
  $ (cd or && diktor m1.kel)
  P1
  $ printf 'from "./lib/q" import Q\ntype instance Show[Q] { let show(q) = "Q" }\n' > or/m2.kel
  $ (cd or && diktor m2.kel)
  ! m2.kel:2:1: 型エラー: Show[Q] のインスタンスは、Show か Q を宣言したファイルにだけ書けます
  [1]
  $ printf 'type instance[A: Ord] Ord[List[_]] { let lt(a, b) = true\nlet le(a, b) = true\nlet gt(a, b) = true\nlet ge(a, b) = true }\n' > or/m3.kel
  $ (cd or && diktor m3.kel)
  ! m3.kel:1:1: 型エラー: Ord[List] のインスタンスは、Ord か List を宣言したファイルにだけ書けます
  [1]
  $ printf 'echoln(show(Cons(1, Nil) == Cons(1, Nil)))\necholn(show(Some(1) == None))\n' > or/m4.kel
  $ (cd or && diktor m4.kel)
  true
  false

## ロード時のエフェクト

import したファイルのトップレベルも、起点と同じ閉じた行で検査する。診断の位置は import した
ファイルを指す:

  $ mkdir -p fx/lib
  $ printf 'perform print("x")\npub let v: Int32 = 1\n' > fx/lib/bad.kel
  $ printf 'from "./lib/bad" import v\n' > fx/m1.kel
  $ (cd fx && diktor m1.kel)
  ! lib/bad.kel:1:1: 型エラー: エフェクト Print をここでは実行できません(ラベル Print がありません(行は閉じています))
  [1]

## 宣言の種類

型エイリアス、エフェクト、クラス、pub module を import できる。クラスのメソッドは修飾名でも
非修飾名でも呼べ、import した側の型にインスタンスを書ける。module の値と型は修飾名で引き、
module と同名の型(コンパニオン)は module 名で引ける。module の中の非公開の値は見えない。
import した側の --type-check は起点の束縛だけを出し、import したファイルの警告には
ファイル名を前置する:

  $ mkdir -p kind/lib
  $ cat > kind/lib/k.kel <<'KEL'
  > pub newtype Box[A] = Box(A)
  > pub type Pair[A] = (A, A)
  > pub effect Log = { log: (String) => {} }
  > pub type class Named[A] { val name: (A) => String }
  > type instance[A] Named[Box[_]] { let name(b) = "box" }
  > pub module M {
  >   pub newtype M = Mk(Int32)
  >   pub let get(m: M): Int32 = m match { case Mk(n) => n }
  >   let secret: Int32 = 7
  > }
  > pub let swap(p: Pair[Int32]): Pair[Int32] = p match { case (a, b) => (b, a) }
  > pub let run_log[A](f: () => A @ {Log, Print}): A @ Print = f() handle { case log(s) => { println(s); resume() } }
  > let first(x: Option[Int32]): Int32 = x match { case Some(n) => n }
  > KEL
  $ cat > kind/main.kel <<'KEL'
  > from "./lib/k" import { Box, Pair, Log, Named, M, swap, run_log }
  > newtype Mine = Mine(Int32)
  > type instance Named[Mine] { let name(m) = "mine" }
  > let p: Pair[Int32] = swap((1, 2))
  > echoln(p match { case (a, b) => show(a) + show(b) })
  > echoln(name(Box(1)) + " " + Named.name(Mine(3)))
  > let mm: M = M.Mk(4)
  > echoln(show(M.get(mm)))
  > with_stdout { run_log { perform log("logged"); 0 } }
  > KEL
  $ (cd kind && diktor main.kel)
  ⚠ lib/k.kel: match が非網羅的です。例えば None が漏れています
  21
  box mine
  4
  logged
  $ (cd kind && diktor --type-check main.kel)
  ⚠ lib/k.kel: match が非網羅的です。例えば None が漏れています
  p : (Int32, Int32)
  _ : {}
  _ : {}
  mm : M.M
  _ : {}
  _ : Int32
  $ printf 'from "./lib/k" import M\nlet s: Int32 = M.secret\n' > kind/sec.kel
  $ (cd kind && diktor sec.kel 2>&1 | tail -1)
  ! sec.kel:2:16: 型エラー: 未束縛の変数: M.secret

import M.n は module M の公開の宣言 n だけを束縛し、M 自身は束縛しない:

  $ printf 'from "./lib/k" import M.get\nlet g = get\nlet h = M.get\n' > kind/mem.kel
  $ (cd kind && diktor mem.kel 2>&1 | tail -1)
  ! mem.kel:3:9: 型エラー: 未束縛の変数: M.get
  $ printf 'from "./lib/k" import { M, M.get }\nlet g: Int32 = get(M.Mk(1))\n' > kind/mem2.kel
  $ (cd kind && diktor --type-check mem2.kel 2>&1 | tail -1)
  g : Int32

連結したファイル群は 1 個の起点で、どのファイルの先頭の import も全体から見える:

  $ printf 'pub let y: Int32 = 2\n' > cy.kel
  $ printf 'pub let w: Int32 = 3\n' > cw.kel
  $ printf 'from "./cw" import w\nlet x0: Int32 = w\n' > c1.kel
  $ printf 'from "./cy" import y\nlet z: Int32 = y + x0 + w\n' > c2.kel
  $ diktor --type-check c1.kel c2.kel
  x0 : Int32
  z : Int32

module と同じ名前の型(コンパニオン)は、import した型と同じ名前にできない。別々のファイルは、
同じ名前の extern を宣言できる:

  $ mkdir -p co/lib
  $ printf 'pub newtype C = C1\n' > co/lib/c.kel
  $ printf 'from "./lib/c" import C\nmodule C { pub newtype C = C2 }\n' > co/m1.kel
  $ (cd co && diktor m1.kel)
  ! m1.kel:2:12: 型エラー: module C のコンパニオン型 C は既存の型 C と同名です(module 内の型とトップレベルの型は同名にできません)
  [1]
  $ printf 'pub extern "C" let sqrt(x: Float64): Float64 @ Blocking\npub let one: Int32 = 1\n' > co/lib/e.kel
  $ printf 'from "./lib/e" import one\nextern "C" let sqrt(x: Float64): Float64 @ Blocking\nlet r: Int32 = one\n' > co/m2.kel
  $ (cd co && diktor --type-check m2.kel)
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  r : Int32
  $ printf 'from "./lib/e" import sqrt\nmodule N { pub extern "C" let sqrt(x: Float64): Float64 @ Blocking }\n' > co/m3.kel
  $ (cd co && diktor m3.kel)
  ! m3.kel:2:12: 型エラー: module N の sqrt はトップレベルの sqrt と同名です(module 内の名前とトップレベル名は同名にできません)
  [1]

公開されるのは pub の宣言だけである。pub の束縛の後ろに同名の非公開の束縛を置いても、
import されるのは pub の束縛である:

  $ mkdir -p pubv/lib
  $ printf 'pub let x: Int32 = 1\nlet x: String = "private"\n' > pubv/lib/a.kel
  $ printf 'from "./lib/a" import x\nlet y = x\n' > pubv/m1.kel
  $ (cd pubv && diktor --type-check m1.kel)
  y : Int32

module を import すると、コンパニオン型の名前も型として束縛する。同じ名前の型は宣言できない:

  $ mkdir -p cmp/lib
  $ printf 'pub module M { pub newtype M = Ma(Int32) }\n' > cmp/lib/a.kel
  $ printf 'from "./lib/a" import M\nnewtype M = Mine(String)\n' > cmp/m1.kel
  $ (cd cmp && diktor m1.kel)
  ! m1.kel:2:1: 型エラー: M は import した名前と同じです
  [1]

import したクラスのメソッドの非修飾名は、値の名前として数える。同名のメソッドを持つ 2 つの
クラスは、同じファイルで宣言できないのと同じく、両方を import できない:

  $ mkdir -p mth/lib
  $ printf 'pub type class P[A] { val pp: (A) => String }\n' > mth/lib/a.kel
  $ printf 'pub type class Q[A] { val pp: (A) => Int32 }\n' > mth/lib/b.kel
  $ printf 'from "./lib/a" import P\nfrom "./lib/b" import Q\n' > mth/m1.kel
  $ (cd mth && diktor m1.kel)
  ! m1.kel:2:23: import エラー: pp は ./lib/a からも import しています(別の宣言です)
  [1]

シンボリックリンクの下の .. は、綴りの上で相殺すると別のファイルを指すことがある。そのときは
相殺しない綴りで報告する:

  $ mkdir -p sym/real/deep/lib
  $ printf 'pub let v: Int32 = "s"\n' > sym/real/deep/b.kel
  $ printf 'from "../b" import v\npub let w: Int32 = v\n' > sym/real/deep/lib/a.kel
  $ printf 'pub let v: Int32 = 1\n' > sym/b.kel
  $ ln -s real/deep/lib sym/lib
  $ printf 'from "./lib/a" import w\n' > sym/main.kel
  $ (cd sym && diktor main.kel)
  ! lib/../b.kel:1:9: 型エラー: 注釈された型を満たしません(型が一致しません: Int32 と String)
  [1]

同じファイルに同じ名前の pub の値が 2 つあるときは、後の宣言が前を覆うので、後の宣言を import する:

  $ mkdir -p twice/lib
  $ printf 'pub let x: Int32 = 1\npub let x: String = "second"\n' > twice/lib/a.kel
  $ printf 'from "./lib/a" import x\nlet y = x\n' > twice/m1.kel
  $ (cd twice && diktor --type-check m1.kel)
  y : String
