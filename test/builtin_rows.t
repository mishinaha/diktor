標準環境の署名の行(LangSpec §16 の冒頭)。最外の @ を省略した署名は、プリミティブを
除き @ {} と読む。処理系は組み込みのクラスのメソッドと Ref、Array の操作の最外の行を
閉じた行で持ち、名前の参照、呼び出し、演算子の使用のときに、使用時の開き(LangSpec
§13.2)が尾部を開く。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

一般化しない値束縛 f に組み込みのメソッド show を入れると、f の行は名前の参照で開いた
尾部のまま残り、束縛の終わりに閉じた {} に戻る(LangSpec §13.2)。そのため f を Console
の文脈と Print の文脈の両方から呼べる:

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

注釈で型を決めた f も閉じた {} に戻り、--type-check の表示に @ {} が付く:

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

Array.length は @ を省いた署名で、閉じた {} と読む(LangSpec §14.3)。idf で包んだ len を
Console と Print の文脈から呼べる:

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

Ref.get の行は閉じた {Heap[h]} で、run の本体の中の行の違う 2 つの関数から呼べる:

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

演算子 + と前置の - は、メソッドの呼び出しと同じく閉じたスキーマの尾部を開く。
本体が x + 1 の g と -x の h の行はその開いた尾部なので、束縛の終わりに閉じた {} に
戻る。g と h は Ask を起こす文脈から先に呼んでも、後で Console の文脈から呼べる
(行が決まっていない fn(x) => x の形は spec_gaps.t の ordervr が見張る):

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

演算子を本体に持つ 2 つの無名関数を if で選ぶ束縛 g も、閉じた {} の行と表示する:

  $ cat > bopdisp.kel <<'KEL'
  > let g = if true then fn(x: Int32) => x + 1 else fn(x: Int32) => x - 1
  > KEL
  $ diktor --type-check bopdisp.kel
  g : (Int32) => Int32 @ {}

プリミティブ(extern "prim")で省略した @ は、使うたびに新しい行変数になる。
__string_length を包んだ一般化しない束縛 g の行は、最初の使用 p で Print に決まり、
Console の文脈の c で落ちる:

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

演算子は、メソッドのスキーマの閉じた行を開いてから位置の行と一致させるので、
@ Console の f の本体でも @ Print の s の本体でも使える:

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

組み込みの Show のインスタンスの実装が Print を起こすと、純粋性の規則を名指しする
文面で拒否する。元の報告は、閉じた空の行に Print が無いことを言う:

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
