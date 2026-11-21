標準環境のシグネチャのエフェクト行をテストする(LangSpec §16 の冒頭)。最も外側の @ を省略したシグネチャは、
プリミティブを除いて @ {} と読む。組み込みのクラスのメソッドや、Array.length、Ref.get のように、
シグネチャの最も外側の行が閉じている関数を、処理系は閉じた行のまま持つ。名前の参照、呼び出し、演算子の使用の
ときに、使用時に行を開く規則(LangSpec §13.2)で行の末尾を開く。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

一般化しない値束縛 f に組み込みのメソッド show を入れると、f の行は、名前の参照で開いた
行の末尾のまま残り、束縛の終わりに閉じた {} に戻る(LangSpec §13.2)。--type-check が表示する f の型に
@ {} が付き、f を Console の文脈と Print の文脈の両方から呼び出せる:

  $ cat > bshowweak.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let f = idf(show)
  > let p(): Unit @ Console = echoln(f(1i32))
  > let q(): Unit @ Print = println(f(2i32))
  > p()
  > with_stdout(q)
  > KEL
  $ diktor bshowweak.kel
  1
  2
  $ diktor --type-check bshowweak.kel
  idf : (A) => A
  f : [_A: Show] (_A) => String @ {}
  p : () => {} @ {Console}
  q : () => {} @ {Print}
  _ : {}
  _ : {}

型注釈で型を決めた f の行も閉じた {} に戻り、--type-check の表示に @ {} が付く:

  $ cat > bshowann.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let f: (Int32) => String = idf(show)
  > let p(): Unit @ Console = echoln(f(1i32))
  > let q(): Unit @ Print = println(f(2i32))
  > p()
  > with_stdout(q)
  > KEL
  $ diktor --type-check bshowann.kel
  idf : (A) => A
  f : (Int32) => String @ {}
  p : () => {} @ {Console}
  q : () => {} @ {Print}
  _ : {}
  _ : {}

Array.length は @ を省略したシグネチャなので、行は閉じた {} と読む(LangSpec §14.3)。idf に渡して得た len を
Console の文脈と Print の文脈から呼び出せる:

  $ cat > barrlen.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let arr: Array[Int32] = run h { MutableArray.freeze(MutableArray.new(3, 7)) }
  > let len = idf(Array.length)
  > let p(): Unit @ Console = echoln(show(len(arr)))
  > let q(): Unit @ Print = println(show(len(arr)))
  > p()
  > with_stdout(q)
  > KEL
  $ diktor barrlen.kel
  3
  3

Ref.get の行は閉じた {Heap[h]} で、run の本体の中にある、行の違う 2 つの関数から呼び出せる:

  $ cat > brefget.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let main(): Unit @ Console = {
  >   let n = run h {
  >     let r = Ref.new(1i32)
  >     let g = idf(Ref.get)
  >     let k(): Int32 @ {Heap[h], Console} = { echoln("k"); g(r) }
  >     let m(): Int32 @ {Heap[h], Print} = { println("m"); g(r) }
  >     k() + with_stdout(m)
  >   }
  >   echoln(show(n))
  > }
  > main()
  > KEL
  $ diktor brefget.kel
  k
  m
  2

演算子 + と前置の - は、メソッドの呼び出しと同じく、閉じた型スキームの行の末尾を開く。
本体が x + 1 である g と、-x である h の行は、その開いた行の末尾なので、束縛の終わりに閉じた {} に
戻る。そのため g と h は、Ask を起こす文脈から先に呼び出しても、後で Console の文脈から呼び出せる。
行が決まっていない fn(x) => x の形は、spec_gaps.t の ordervr が検査する:

  $ cat > bopweak.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let idf[A](x: A): A = x
  > let main(): Unit @ {Console} = {
  >   let g: (Int32) => Int32 = idf(fn(x) => x + 1)
  >   let h: (Int32) => Int32 = idf(fn(x) => -x)
  >   let b = (g(2) + h(3) + perform ask()) handle {
  >     case ask() => resume(10)
  >     case return(x) => x
  >   }
  >   let a = g(1) + h(1)
  >   echoln(show(a + b))
  > }
  > main()
  > KEL
  $ diktor bopweak.kel
  11

演算子を本体に持つ 2 つの無名関数を if で選ぶ束縛 g の行も、閉じた {} と表示される:

  $ cat > bopdisp.kel <<'KEL'
  > let g = if true then fn(x: Int32) => x + 1 else fn(x: Int32) => x - 1
  > KEL
  $ diktor --type-check bopdisp.kel
  g : (Int32) => Int32 @ {}

プリミティブ(extern "prim")で省略した @ は、使うたびに新しい行変数になる。
__string_length を id に渡して得た、一般化しない束縛 g の行は、最初の使用 p で Print に決まるので、
Console の文脈の c で型エラーになる:

  $ cat > stdprim.kel <<'KEL'
  > let id[T](x: T): T = x
  > let g = id(__string_length)
  > let p(): Unit @ Print = println(show(g("ab")))
  > let c(): Unit @ Console = echoln(show(g("abc")))
  > KEL
  $ diktor --type-check stdprim.kel
  id : (A) => A
  g : (String) => Int32
  p : () => {} @ {Print}
  ! stdprim.kel:4:39: 型エラー: ラベル Print がありません(行は閉じています)
  [1]

演算子は、メソッドの型スキームの閉じた行の末尾を開いてから、その位置で有効なエフェクト行と一致させる。
そのため、@ Console の f の本体でも、@ Print の s の本体でも使える:

  $ cat > stdop.kel <<'KEL'
  > let f(): Int32 @ Console = { echoln("a"); 1 + 2 * 3 - -4 }
  > let s(): String @ Print = { println("b"); show(1 < 2) + show(3 % 2) }
  > echoln(with_stdout(fn() => s()))
  > echoln(show(f()))
  > KEL
  $ diktor stdop.kel
  b
  true1
  a
  11

組み込みの Show のインスタンスの実装が Print を起こすと、純粋性の規則を明記した
メッセージで拒否する。「元の報告」の部分は、閉じた空の行に Print がないことを示す:

  $ cat > stdinst.kel <<'KEL'
  > newtype N(Int32)
  > type instance Show[N] {
  >   let show(n) = { println("side"); "n" }
  > }
  > echoln(show(N(1)))
  > KEL
  $ diktor stdinst.kel
  ! stdinst.kel:3:7: 型エラー: 型クラスのメソッドの実装は純粋でなければなりません(宣言の最外の行にラベルがありません — 仕様 §9)。インスタンスメソッド show の本体がエフェクトを起こしています。元の報告: ラベル Print がありません(行は閉じています)
  [1]
