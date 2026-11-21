過去に見つかった欠陥の回帰テストである。
欠陥はどれも、型検査の健全性か処理系の頑健性に関わる。

行変数 [R] を行の位置に書ける(sample.kel:201-203 / :209-215):

  $ cat > rowvar.kel <<'EOF'
  > let fst2[A, R](t: {_item: A extends R}): A = t._item
  > echoln(fst2({_item = "hi", x = 1}))
  > echoln(fst2({x = 1, _item = "hi"}))
  > let describe[R](v: #Even | #Odd | R): String = v match {
  >   case #Even => "even"
  >   case #Odd  => "odd"
  >   case _     => "unknown"
  > }
  > echoln(describe(#Even))
  > echoln(describe(#Other))
  > EOF
  $ diktor rowvar.kel
  hi
  hi
  even
  unknown

run の本体が返すクロージャの型の行に Heap[h] が残ると、h がスコープの外に漏れるので
型エラーになる(LangSpec §14.1、sample.kel:668-669)。vr は、行に Heap[h] を持つ
クロージャを Ref に入れてから取り出し、run の本体から返す:

  $ cat > vr.kel <<'EOF'
  > let escaped[E](): (Int32) => Int32 @ {Console extends E} = run h {
  >   let slot: Ref[h, (Int32) => Int32 @ {Heap[h]}] = Ref.new(fn(x) => x)
  >   let cell = Ref.new(41)
  >   let _ = Ref.set(slot, fn(x) => Ref.get(cell) + x)
  >   Ref.get(slot)
  > }
  > EOF
  $ diktor --type-check vr.kel
  ! vr.kel:1:60: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

注釈の最も外側の矢印で @ を省略した値束縛 g は、本体が関数呼び出しなので一般化されず
(値制限、LangSpec §6.2)、行は最初の呼び出しで閉じた行に決まる。2 つ目の呼び出し
g(2) は、閉じた行の関数を呼ぶときに行の末尾を開くので、型検査に通る。呼ぶ順序を逆にすると
エラーになるプログラムは、spec_gaps.t の ordervr で確かめる:

  $ cat > vrgen.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let idf[A](x: A): A = x
  > let main(): Unit @ {Console} = {
  >   let g: (Int32) => Int32 = idf(fn(x) => x)
  >   let a = g(1)
  >   let b = (g(2) + perform ask()) handle {
  >     case ask() => resume(10)
  >     case return(x) => x
  >   }
  >   echoln(show(a + b))
  > }
  > main()
  > EOF
  $ diktor vrgen.kel
  13

g の本体を無名関数(値)に替えると、g は一般化され、同じように 2 つの文脈から呼べる:

  $ cat > vrgenv.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let idf[A](x: A): A = x
  > let main(): Unit @ {Console} = {
  >   let g: (Int32) => Int32 = fn(x) => x + 1
  >   let a = g(1)
  >   let b = (g(2) + perform ask()) handle {
  >     case ask() => resume(10)
  >     case return(x) => x
  >   }
  >   echoln(show(a + b))
  > }
  > main()
  > EOF
  $ diktor vrgenv.kel
  15

注釈の最も外側の矢印に閉じた空でない行を書いた g は、本体が関数呼び出しのままでも、行の異なる
2 つの文脈から呼べる。書いた行の末尾は、使うたびに開く(LangSpec §13.2、sample.kel:478-480)。
vrgen の g の注釈に @ {Console} を追加しても型検査に通る:

  $ cat > vrgen2.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let idf[A](x: A): A = x
  > let main(): Unit @ {Console} = {
  >   let g: (Int32) => Int32 @ {Console} = idf(fn(x) => x + 1)
  >   let a = g(1)
  >   let b = (g(2) + perform ask()) handle {
  >     case ask() => resume(10)
  >     case return(x) => x
  >   }
  >   echoln(show(a + b))
  > }
  > main()
  > EOF
  $ diktor vrgen2.kel
  15

本体が値でない値束縛の注釈の最も外側の矢印に閉じた行を書いても、その注釈を経由して外側の
Ref の内容の行を開くことはできない。Ref の内容の行は g の注釈の閉じた行 {Console} に
決まり、Heap[h] を読むクロージャを Ref に入れる位置で型エラーになる。クロージャを run の外へ
返すことはできない(LangSpec §14.1):

  $ cat > vrleak.kel <<'EOF'
  > let escaped[E](): (Int32) => Int32 @ {Console extends E} = run h {
  >   let slot = Ref.new(fn(x) => x)
  >   let g: (Int32) => Int32 @ {Console} = Ref.get(slot)
  >   let cell = Ref.new(41)
  >   let _ = Ref.set(slot, fn(x) => Ref.get(cell) + x)
  >   Ref.get(slot)
  > }
  > echoln(show(escaped()(1)))
  > EOF
  $ diktor vrleak.kel
  ! vrleak.kel:5:34: 型エラー: ラベル Heap がありません(行は閉じています)
  [1]

同じ形で Ask を起こすクロージャを Ref に入れ、行に Ask のない関数 bad から呼ぶプログラムも、
クロージャを Ref に入れる位置で型エラーになる:

  $ cat > vrleak2.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let bad(): Int32 @ {Console} = run h {
  >   let slot = Ref.new(fn(x) => x)
  >   let g: (Int32) => Int32 @ {Console} = Ref.get(slot)
  >   let _ = Ref.set(slot, fn(x) => perform ask() + x)
  >   Ref.get(slot)(1)
  > }
  > echoln(show(bad()))
  > EOF
  $ diktor vrleak2.kel
  ! vrleak2.kel:5:34: 型エラー: エフェクト Ask をここでは実行できません(ラベル Ask がありません(行は閉じています))
  [1]

Ref を使わない形でも、型エラーになる。f の注釈のない引数 z を idf に渡し、その結果を本体が値でない
束縛 _ の注釈 @ {Console} で受けると、z の行は {Console} に決まり、Ask を起こす関数を
f に渡す 7 行目でエラーになる:

  $ cat > vrleak3.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let idf[A](x: A): A = x
  > let f(z) = {
  >   let _: (Int32) => Int32 @ {Console} = idf(z)
  >   z(1)
  > }
  > let main(): Unit @ {Console} = echoln(show(f(fn(x) => perform ask() + x)))
  > main()
  > EOF
  $ diktor vrleak3.kel
  ! vrleak3.kel:7:55: 型エラー: エフェクト Ask をここでは実行できません(ラベル Ask がありません(行は閉じています))
  [1]

先に f の本体で呼んだ単相の束縛 h を idf に渡し、その結果を本体が値でない束縛 g の注釈 @ {Console} で受ける形は、
h の行が {Console} に決まるだけで、型検査に通る。g と h は同じ関数で、実行すると x を 2 回出力する:

  $ cat > vrleak4.kel <<'EOF'
  > let idf[A](x: A): A = x
  > let f() = {
  >   let h = idf(fn() => echoln("x"))
  >   h()
  >   let g: () => Unit @ {Console} = idf(h)
  >   g()
  > }
  > f()
  > EOF
  $ diktor vrleak4.kel
  x
  x

本体が値でない値束縛の注釈の最も外側の矢印に閉じた行を書いた g は、同じ行の文脈から 2 回呼べる:

  $ cat > vrok.kel <<'EOF'
  > let idf[A](x: A): A = x
  > let f(): Int32 @ {Console} = {
  >   let g: (Int32) => Int32 @ {Console} = idf(fn(x) => { echoln("g"); x })
  >   g(1) + g(2)
  > }
  > echoln(show(f()))
  > EOF
  $ diktor vrok.kel
  g
  g
  3

パターン束縛 let (5) の注釈の最も外側の矢印に閉じた行を書いても、pub を付けて最も外側の @ を
省略しても、内部エラーではなく型エラーになる:

  $ printf 'let (5): (Int32) => Int32 @ {Console} = fn(x) => x\necholn("ok")\n' > patrigid.kel
  $ diktor patrigid.kel
  ! patrigid.kel:1:6: 型エラー: (Int32) => Int32 @ {Console} は Integral のインスタンスではありません
  [1]
  $ printf 'pub let (5): (Int32) => Int32 = fn(x) => x\necholn("ok")\n' > patrigid2.kel
  $ diktor patrigid2.kel
  ! patrigid2.kel:1:10: 型エラー: (Int32) => Int32 @ {} は Integral のインスタンスではありません
  [1]

前提付きインスタンスの、本体が値でないメソッドも、注釈にインスタンス宣言の型パラメータ
A を使える:

  $ cat > instnv.kel <<'EOF'
  > let idf[A](x: A): A = x
  > type class Sz[T] { val sz: (T) => Int32 }
  > newtype Box[A] = Box(A)
  > type instance[A] Sz[Box[_]] {
  >   let sz: (Box[A]) => Int32 @ {} = idf(fn(b) => 1)
  > }
  > echoln(show(sz(Box("x"))))
  > EOF
  $ diktor instnv.kel
  1

メソッドはクラスパラメータの型で選ぶ(第 1 引数が別の型でも、その型では選ばない):

  $ cat > pick.kel <<'EOF'
  > type class Pick[A] { val pick: (Int32, A) => Int32 }
  > type instance Pick[Int32]  { let pick(n, a) = a }
  > type instance Pick[String] { let pick(n, a) = n }
  > echoln(show(pick(0, "boom")))
  > EOF
  $ diktor pick.kel
  0

組み込みインスタンスは差し替えられない(コヒーレンス)。標準環境のインスタンスと
同じクラスと型の組に対するインスタンスは、宣言の時点で拒否する:

  $ cat > coh.kel <<'EOF'
  > type instance Add[Int32] { let add(x, y) = __int32_sub(x, y) }
  > echoln(show(2 + 3))
  > EOF
  $ diktor coh.kel
  ! coh.kel:1:1: 型エラー: 標準環境のインスタンス Add[Int32] は再宣言できません
  [1]

module の中の type instance が実行時に見つかる(sample.kel §13 の形):

  $ cat > modinst.kel <<'EOF'
  > module BigInt {
  >   pub newtype BigInt = Small(Int32)
  >   type instance Add[BigInt] { let add(x, y) = x }
  > }
  > let a = Small(1)
  > echoln(show((a + a) match { case Small(n) => n }))
  > EOF
  $ diktor modinst.kel
  1

newtype による組み込みの型名の再宣言を拒否する:

  $ printf 'newtype Boolean = Yes\n' > redef.kel
  $ diktor --type-check redef.kel
  ! redef.kel:1:1: 型エラー: 組み込み型 Boolean は newtype で再宣言できません
  [1]

extern の再宣言を拒否する:

  $ printf 'extern "prim" let __int32_add(x: String, y: String): String\n' > exr.kel
  $ diktor --type-check exr.kel
  ! exr.kel:1:1: 型エラー: プレリュードの extern __int32_add は再宣言できません
  [1]

プレリュードはプリミティブの実装表のすべての名前を extern で宣言しているので、実装表のどの名前も
再宣言できない。宣言のない名前があると、ユーザが偽の型を付けて実装を呼び出せる:

  $ printf 'extern "prim" let __string_le(x: Int32, y: Int32): Int32\n' > exr2.kel
  $ diktor --type-check exr2.kel
  ! exr2.kel:1:1: 型エラー: プレリュードの extern __string_le は再宣言できません
  [1]

  $ printf 'extern "prim" let __int64_ge(x: Int64, y: Int64): Int32\n' > exr3.kel
  $ diktor --type-check exr3.kel
  ! exr3.kel:1:1: 型エラー: プレリュードの extern __int64_ge は再宣言できません
  [1]

どの表にもない名前は、C リンケージで宣言しても、呼ぶと未実装のプリミティブになる。
cos は、prim リンケージで宣言して呼ぶと未実装のプリミティブになり、
C リンケージで宣言すれば C の実装を呼べる:

  $ cat > abi.kel <<'KEL'
  > extern "C" let __nosuch_prim_name(x: Int32): Int32
  > echoln(show(__nosuch_prim_name(1)))
  > KEL
  $ diktor abi.kel
  実行時エラー: 未実装のプリミティブ: __nosuch_prim_name
  [3]

  $ cat > abi2.kel <<'KEL'
  > extern "prim" let cos(x: Float64): Float64
  > echoln(show(cos(0.0)))
  > KEL
  $ diktor abi2.kel
  実行時エラー: 未実装のプリミティブ: cos
  [3]

  $ cat > abic.kel <<'KEL'
  > extern "C" let cos(x: Float64): Float64
  > echoln(show(cos(0.0)))
  > KEL
  $ diktor abic.kel
  1.0

ABI の文字列そのものも検査する:

  $ printf 'extern "wat" let foo(x: Int32): Int32\n' > abi3.kel
  $ diktor --type-check abi3.kel
  ! abi3.kel:1:1: 型エラー: 未知の extern リンケージ: wat(prim か C を指定してください)
  [1]

次の 10 個のプリミティブを正しい型で呼べる(プレリュードの extern の宣言に漏れがないことを確かめる):

  $ cat > prims.kel <<'KEL'
  > echoln(show(__string_le("a","b")) + show(__string_gt("a","b")) + show(__string_ge("a","a")))
  > echoln(show(__int64_le(1i64,2i64)) + show(__int64_gt(1i64,2i64)) + show(__int64_ge(2i64,2i64)))
  > echoln(show(__float64_le(1.0,2.0)) + show(__float64_gt(1.0,2.0)) + show(__float64_ge(2.0,2.0)))
  > echoln(__show_int32(42))
  > KEL
  $ diktor prims.kel
  truefalsetrue
  truefalsetrue
  truefalsetrue
  42

let rec の右辺が関数でなければ、型検査で拒否する:

  $ cat > lrn.kel <<'EOF'
  > let f(): Int32 = run h {
  >   let rec r = Ref.new(0)
  >   Ref.get(r)
  > }
  > EOF
  $ diktor --type-check lrn.kel
  ! lrn.kel:2:3: 型エラー: let rec の右辺は関数でなければなりません
  [1]

頑健性のテストである。OCaml の例外をそのまま外へ出さず、終了コード規約に従う診断と終了コードにする:

  $ diktor /no/such/file.kel
  diktor: ファイルを開けません: /no/such/file.kel: No such file or directory
  [64]

  $ printf 'let x = 1\n// \xff\xfe\n' > badutf8.kel
  $ diktor badutf8.kel
  badutf8.kel:2:4: 字句エラー: 不正な UTF-8 バイト列です
  [2]

  $ printf 'echoln(show(1i999999999999999999999))\n' > hugesuf.kel
  $ diktor hugesuf.kel
  ! hugesuf.kel:1:13: 型エラー: 数値リテラル 1i999999999999999999999 の接尾辞 i999999999999999999999 はありません(接尾辞は i32、i64、f64 だけです)
  [1]

  $ printf 'module A { module B { let x = 1 } }\n' > nestmod.kel
  $ diktor nestmod.kel
  ! nestmod.kel:1:12: 未実装: module の入れ子(M10)
  [4]

  $ cat > unkeff.kel <<'EOF'
  > effect A = { op1: () => Int32 }
  > let r = (fn() => perform op1())() handle {
  >   case Nope.op1() => resume(1)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF
  $ diktor unkeff.kel
  ! unkeff.kel:2:9: 型エラー: 未知のエフェクト: Nope
  [1]

Float64 は、読み直すと元の値に戻る最短の 10 進表記で表示する:

  $ cat > fl.kel <<'EOF'
  > echoln(show(0.1 + 0.2))
  > echoln(show(123456789012345.0))
  > echoln(show(1.0))
  > EOF
  $ diktor fl.kel
  0.30000000000000004
  123456789012345.0
  1.0

入れ子の run の中からは、外側のリージョンの Ref を読めない(リージョンの安全性):

  $ cat > nestrun.kel <<'EOF'
  > let f(): Int32 = run h1 {
  >   let r = Ref.new(1)
  >   let x = run h2 { let s = Ref.new(2); Ref.get(r) + Ref.get(s) }
  >   x
  > }
  > EOF
  $ diktor --type-check nestrun.kel
  ! nestrun.kel:3:48: 型エラー: ほかのリージョンの Ref を使おうとしています(スコープ付きの型が一致しません: ς1 と ς2)
  [1]

ブロックの Seq は、文のノードとは別のノードを使う。同じノードを使うと、
末尾から 2 番目の文の型が Seq の型で上書きされ、数値リテラルを値にする処理
(第14章 number_value)が誤った型を読んで実行時エラーになる:

  $ cat > seq1.kel <<'KEL'
  > let f() = { 1; "x" }
  > echoln(f())
  > KEL
  $ diktor seq1.kel
  x

  $ cat > seq2.kel <<'KEL'
  > let g() = { "a"; 1; "b" }
  > echoln(g())
  > KEL
  $ diktor seq2.kel
  b

  $ cat > seq3.kel <<'KEL'
  > let h() = { 1; () }
  > let _ = h()
  > KEL
  $ diktor seq3.kel; echo "exit: $?"
  exit: 0

return 節と cancel 節にガードは書けない。型検査で受理すると、ガードが実行時に
評価されないまま無視される:

  $ cat > retguard.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() => resume(1)
  >   case return(x) if x > 100 => 999
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check retguard.kel
  ! retguard.kel:4:21: 型エラー: return 節にガードは書けません
  [1]

  $ cat > cancelguard.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() => resume(1)
  >   case return(x) => x
  >   case cancel if false => ()
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check cancelguard.kel
  ! cancelguard.kel:5:18: 型エラー: cancel 節にガードは書けません
  [1]

同名のメソッドを持つ型クラスを 2 つ宣言すると拒否する。修飾しないメソッド名が指すクラスが
elab(宣言の順)と interp(ハッシュの順)で食い違い、別のクラスのメソッドを呼んだり、
誤って「見つかりません」と報告したりするからである:

  $ cat > mclash.kel <<'KEL'
  > type class Alpha[A] { val sz: (A) => Int32 }
  > type class Beta[A]  { val sz: (A) => Int32 }
  > KEL
  $ diktor --type-check mclash.kel
  ! mclash.kel:2:1: 型エラー: メソッド名 sz は型クラス Alpha が既に宣言しています(非修飾名が衝突するため、v0 では同名メソッドを複数のクラスに宣言できません)
  [1]

組み込みクラスのメソッド名も同じように扱う:

  $ printf 'type class MyShow[A] { val show: (A) => String }\n' > mclash2.kel
  $ diktor --type-check mclash2.kel
  ! mclash2.kel:1:1: 型エラー: メソッド名 show は型クラス Show が既に宣言しています(非修飾名が衝突するため、v0 では同名メソッドを複数のクラスに宣言できません)
  [1]

操作節のガードには resume を書けない。interp はガードを、resume を使えない状態で
評価するので、型検査で拒否する:

  $ cat > gresume.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() if resume(7) > 0 => resume(1)
  >   case ask() => resume(2)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check gresume.kel
  ! gresume.kel:3:17: 型エラー: 操作節のガードには resume を書けません(ガードは節が選ばれる前に評価されるので、継続を再開できません)
  [1]

ガードの resume をクロージャで囲んでも同じである(§11.21 の検査を回避できない):

  $ cat > gresume2.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() if (fn(u: Unit) => resume(7))(()) > 0 => resume(1)
  >   case ask() => resume(2)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check gresume2.kel
  ! gresume2.kel:3:33: 型エラー: 操作節のガードには resume を書けません(ガードは節が選ばれる前に評価されるので、継続を再開できません)
  [1]

操作節の中の関数束縛の本体に書いた resume は、その関数を節の中で呼ぶだけでも
型検査で拒否する。fn() => resume(41) を束縛する形と同じメッセージのエラーになる:

  $ cat > lfresume.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() => {
  >     let f() = resume(41)
  >     f()
  >   }
  >   case return(x) => x
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check lfresume.kel
  ! lfresume.kel:4:15: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]
  $ sed 's/let f() = resume(41)/let f = fn() => resume(41)/' lfresume.kel > lflam.kel
  $ diktor --type-check lflam.kel
  ! lflam.kel:4:21: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]

let rec の関数束縛(and でつないだ 2 つ目の束縛を含む)と、型パラメータ付きの
関数束縛も同じメッセージで拒否する。右辺に resume(41) だけを書いた let rec の値束縛は、
let rec の右辺の検査でエラーになる:

  $ sed 's/let f() = /let rec f() = /' lfresume.kel > lfrec.kel
  $ diktor --type-check lfrec.kel
  ! lfrec.kel:4:19: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]
  $ sed 's/let f() = resume(41)/let rec f(): Int32 = g() and g(): Int32 = resume(41)/' lfresume.kel > lfand.kel
  $ diktor --type-check lfand.kel
  ! lfand.kel:4:47: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]
  $ sed -e 's/let f() = /let f[A](a: A): Int32 = /' -e 's/    f()/    f(0)/' lfresume.kel > lftp.kel
  $ diktor --type-check lftp.kel
  ! lftp.kel:4:29: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]
  $ sed -e 's/let f() = resume(41)/let rec x = resume(41)/' -e 's/    f()/    x/' lfresume.kel > lfrecval.kel
  $ diktor --type-check lfrecval.kel
  ! lfrecval.kel:4:5: 型エラー: let rec の右辺は関数でなければなりません
  [1]

関数束縛を Ref に入れて節の外で呼ぶプログラムは、型検査でエラーになり、実行を始めない
(1 行目の echoln の start を出力しない):

  $ cat > lfleak.kel <<'KEL'
  > echoln("start")
  > effect Ask = { ask: () => Int32 }
  > let main(): Int32 = run h {
  >   let cell = Ref.new(fn() => 0)
  >   let r = (perform ask() + 1) handle {
  >     case ask() => {
  >       let f() = resume(41)
  >       Ref.set(cell, f)
  >       0
  >     }
  >     case return(x) => x
  >   }
  >   r + Ref.get(cell)()
  > }
  > echoln(show(main()))
  > KEL
  $ diktor lfleak.kel
  ! lfleak.kel:7:17: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]

resume を含まない関数束縛、値束縛の右辺の resume、関数束縛の本体にある内側の
handle の操作節の resume は、型検査に通る:

  $ cat > lfok.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > effect Ask2 = { ask2: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() => {
  >     let one() = 1
  >     let g() = (perform ask2() + 1) handle {
  >       case ask2() => resume(38)
  >       case return(y) => y
  >     }
  >     let v = resume(g() + one() + 1)
  >     v
  >   }
  >   case return(x) => x
  > }
  > echoln(show(r))
  > KEL
  $ diktor lfok.kel
  42

内側の handle の操作節の中の関数束縛に書いた resume と、関数束縛の本体にある
内側の handle の本体に書いた外側の節の resume も拒否する:

  $ sed 's/case ask2() => resume(38)/case ask2() => { let k() = resume(38); k() }/' lfok.kel > lfinner.kel
  $ diktor --type-check lfinner.kel
  ! lfinner.kel:7:34: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]
  $ sed 's/(perform ask2() + 1) handle/(resume(perform ask2())) handle/' lfok.kel > lfinbody.kel
  $ diktor --type-check lfinbody.kel
  ! lfinbody.kel:6:16: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]

標準環境のインスタンスと同じクラスと型の組に対するユーザのインスタンスは、1 つ目の宣言で
拒否する(2 つ書いても、診断は 1 つ目の位置を指す):

  $ cat > dupinst.kel <<'KEL'
  > type instance Add[Int32] { let add(x, y) = x }
  > type instance Add[Int32] { let add(x, y) = y }
  > KEL
  $ diktor --type-check dupinst.kel
  ! dupinst.kel:1:1: 型エラー: 標準環境のインスタンス Add[Int32] は再宣言できません
  [1]

ガードがなく、かつどんな引数にも一致する節が 1 つもない操作は、型検査で拒否する。仕様には、
どの節にも一致しなかった操作を外側のハンドラへ回す規則がないので(sample.kel:515)、
すべての節が一致しないことがあるハンドラは受理しない:

  $ cat > guardonly.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1) + perform ask(2)) handle {
  >   case ask(n) if n == 1 => resume(100)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check guardonly.kel
  ! guardonly.kel:2:9: 型エラー: 操作 ask には、ガードがなく、どんな引数にも一致する節がありません(どの節にも一致しなかった操作を外側のハンドラへ回す規則はありません)。ガードのない case ask(_) を最後に置いてください
  [1]

標準出力に書き出せないときも、終了コード規約に従って 74 で終了する。OCaml の既定の
flush は Format の at_exit で、最上位の例外ハンドラの外で実行されるので、それに任せると
Fatal error と終了コード 2 になる:

  $ printf 'echoln("hello")\n' > outerr.kel
  $ diktor outerr.kel > /dev/full
  diktor: 標準出力に書き出せません: No space left on device
  [74]

  $ diktor --type-check outerr.kel > /dev/full
  diktor: 標準出力に書き出せません: No space left on device
  [74]

return と cancel は操作名として予約している。handle は節を名前で分類し、これらの名前の節を
return 節と cancel 節として扱うので、操作名に使えると、宣言できてもハンドルできない effect ができるからである:

  $ printf 'effect E = { cancel: () => Int32 }\n' > opres.kel
  $ diktor --type-check opres.kel
  ! opres.kel:1:22: 型エラー: 操作名 cancel は予約されています(handle の cancel 節と衝突するため宣言できません)
  [1]

  $ printf 'effect E2 = { return: () => Int32 }\n' > opres2.kel
  $ diktor --type-check opres2.kel
  ! opres2.kel:1:23: 型エラー: 操作名 return は予約されています(handle の return 節と衝突するため宣言できません)
  [1]

終了は必ず safe_exit を通す。exit をそのまま呼ぶと、at_exit の flush が書き出せない出力で
失敗し、どの終了コードも Fatal error と終了コード 2 に変わる:

  $ printf 'echoln("hello")\necholn(show(1 / 0))\n' > m74.kel
  $ diktor m74.kel > /dev/full
  実行時エラー: ゼロ除算です
  [3]

  $ diktor m74.kel >/dev/null 2>/dev/full
  [3]

入力の読み取りエラーでも終了コード 64 で終了する。with_input は、open だけでなく読み取りまでを
try で囲む。ディレクトリを渡すと、EISDIR のエラーは読み取りのときに起きる:

  $ mkdir -p adir
  $ diktor adir
  diktor: ファイルを開けません: adir: Is a directory
  [64]

SIGPIPE は無視し、出力エラーとして終了コード 74 で終了する。既定の動作のままだと、シグナルで
終了して終了コードが 141 になり、終了コード規約から外れる:

  $ cat > big74.kel <<'KEL'
  > let rec loop(n: Int32): Unit =
  >   (n == 0) match {
  >     case true => ()
  >     case false => { echoln("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"); loop(n - 1) }
  >   }
  > loop(100000)
  > KEL
  $ bash -c 'diktor big74.kel | head -c 100 >/dev/null; echo "code: ${PIPESTATUS[0]}"' 2>&1 | tail -1
  code: 74

操作名は英小文字で始まる名前に限る。handle が節を分類するときに操作名として読めない名前の操作を持つ effect は、
ハンドルできないからである:

  $ printf 'effect E3 = { _foo: (Int32) => Int32 }\n' > opus.kel
  $ diktor --type-check opus.kel
  ! opus.kel:1:21: 型エラー: 操作名 _foo は英小文字で始めてください(handle の節が操作名として読めません)
  [1]

プログラムを実行するときの診断は標準エラーに出力する(標準出力はプログラムの出力だけに使う):

  $ printf 'let bad = 1 + true\n' > terr.kel
  $ diktor terr.kel 2>/dev/null; echo "exit: $?"
  exit: 1

--strict-exhaustive が数えるのは、表示した警告だけである。プレリュードの
表示しない警告まで数えると、何も表示せずに終了コード 1 で終了してしまう:

  $ cat > wpre.kel <<'KEL'
  > newtype Opt3[A] = None3 | Some3(A)
  > let pf = fn(o) => o match { case Some3(x) => x }
  > KEL
  $ printf 'let x = 1\n' > wu.kel
  $ diktor --type-check --strict-exhaustive --prelude wpre.kel wu.kel; echo "exit: $?"
  x : Int32
  exit: 0

resume の引数にはラベルを付けられない。引数は操作の返り値そのものだからである。
ラベルを付けた 1 個の引数には、個数の診断ではなくラベルの診断を出す:

  $ cat > reslabel.kel <<'KEL'
  > effect Ask = {
  >   ask: () => Int32
  > }
  > let f(): Int32 @ {Ask} = perform ask()
  > let g(): Int32 = f() handle {
  >   case ask() => resume(x = 1)
  >   case return(v) => v
  > }
  > KEL
  $ diktor --type-check reslabel.kel
  reslabel.kel:6:17: 構文エラー: resume の引数にラベルは付けられません
  [2]

  $ sed 's/resume(x = 1)/resume(1, 2)/' reslabel.kel > res2.kel
  $ diktor --type-check res2.kel
  res2.kel:6:17: 構文エラー: resume の引数は高々1個です
  [2]

組み込みメソッド表の 39 組のすべてが、実際に選ばれることを確かめる:

  $ cat > ordall.kel <<'KEL'
  > echoln(show(1 < 2) + show(1 <= 2) + show(1 > 2) + show(1 >= 2))
  > echoln(show(1i64 < 2i64) + show(1i64 <= 2i64) + show(1i64 > 2i64) + show(1i64 >= 2i64))
  > echoln(show(1.0 < 2.0) + show(1.0 <= 2.0) + show(1.0 > 2.0) + show(1.0 >= 2.0))
  > echoln(show("a" < "b") + show("a" <= "b") + show("a" > "b") + show("a" >= "b"))
  > echoln(show(1 + 2) + show(1i64 + 2i64) + show(1.0 + 2.0) + ("a" + "b"))
  > echoln(show(3 - 1) + show(3i64 - 1i64) + show(3.0 - 1.0))
  > echoln(show(3 * 2) + show(3i64 * 2i64) + show(3.0 * 2.0))
  > echoln(show(6 / 2) + show(6i64 / 2i64) + show(6.0 / 2.0))
  > echoln(show(1 == 1) + show(1i64 == 1i64) + show(1.0 == 1.0) + show("a" == "a") + show(true == true))
  > KEL
  $ diktor ordall.kel
  truetruefalsefalse
  truetruefalsefalse
  truetruefalsefalse
  truetruefalsefalse
  333.0ab
  222.0
  666.0
  333.0
  truetruetruetruetrue

インスタンス宣言より前の位置でインスタンスを使うと、実行時エラーになる。型検査はパス 1c で
表をそろえるので宣言の順序を問わないが、実行時には宣言を評価するまでインスタンスの実装がない:

  $ cat > instorder.kel <<'KEL'
  > newtype Box = Box(Int32)
  > let b1 = Box(1) == Box(1)
  > type instance Eq[Box] { let eq(a, b) = false }
  > echoln(show(b1))
  > KEL
  $ diktor --type-check instorder.kel
  b1 : Boolean
  _ : {}
  $ diktor instorder.kel
  実行時エラー: Eq[Box] のインスタンスは宣言より前の位置では使えません(実行はまだ実体を持ちません。インスタンス宣言を使用より前に置いてください)
  [3]

後から宣言したインスタンスも見つかる。それより前の呼び出しが記録した「見つからない」という
結果を残したままにすると、後の宣言が見つからなくなる:

  $ cat > cacheinv.kel <<'KEL'
  > type class Pick2[A] { val pick2: (Int32, A) => Int32 }
  > type instance Pick2[Int32] { let pick2(n, a) = a }
  > echoln(show(pick2(0, 7)))
  > type instance Pick2[String] { let pick2(n, a) = n }
  > echoln(show(pick2(5, "x")))
  > KEL
  $ diktor cacheinv.kel
  7
  5
