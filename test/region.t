リージョンと配列(sample.kel の §10、LangSpec §14)。配列を不変の Array[A] と可変の MutableArray[h, A] に分けたことで、
脱出検査、並列処理の決定性、pub の純粋性が守られることを確かめるゴールデンテストである。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

不変配列の読み取りは純粋である。run も Heap も必要ない:

  $ cat > read.kel <<'KEL'
  > let peek(a: Array[Int32]): Int32 = Array.get(a, 0)
  > let len(a: Array[Int32]): Int32 = Array.length(a)
  > let g(x: Int32): {} @ {} = {}
  > let walk(a: Array[Int32]): {} @ {} = Array.each(a, g)
  > KEL
  $ diktor --type-check read.kel
  peek : (Array[Int32]) => Int32
  len : (Array[Int32]) => Int32
  g : (Int32) => {} @ {}
  walk : (Array[Int32]) => {} @ {}

可変配列は h を型に持つので、引数を破壊的に更新する関数は、純粋な関数としては型検査に通らない
(sample.kel:677):

  $ cat > bump.kel <<'KEL'
  > let bump[h](a: MutableArray[h, Int32]): Unit = run h2 { MutableArray.set(a, 0, 42) }
  > KEL
  $ diktor --type-check bump.kel
  ! bump.kel:1:74: 型エラー: ほかのリージョンの MutableArray を使おうとしています(スコープ付きの型が一致しません: ς1 と ς2)
  [1]

書き込むと宣言すれば通る。エフェクト行に Heap[h] が現れる:

  $ cat > honest.kel <<'KEL'
  > let bump[h, E](a: MutableArray[h, Int32]): Unit @ {Heap[h] extends E} =
  >   MutableArray.set(a, 0, 42)
  > KEL
  $ diktor --type-check honest.kel
  bump : (MutableArray[h, Int32]) => {} @ {Heap[h] extends R1}

MutableArray.length も Heap[h] を要求する。長さを変える操作はないが、可変配列に
触れること自体をエフェクト行に記録するためである(sample.kel の §10 のシグネチャの一覧と、
その理由を書いた sample.kel:696 のとおり):

  $ cat > mlen.kel <<'KEL'
  > let demo(): Int32 = run h {
  >   let a = MutableArray.new(4, 0)
  >   MutableArray.length(a)
  > }
  > echoln(show(demo()))
  > KEL
  $ diktor mlen.kel
  4

読むだけの操作(length と get)にも Heap[h] が付いていることは、pub の純粋性と、
@ {} のコールバックを受け取る関数(入力の中で宣言した pmap)で確かめる。シグネチャから Heap を外しても上の mlen は
通るので、シグネチャの回帰はこの 3 ブロックで検出する:

  $ printf 'pub let mlen[h](a: MutableArray[h, Int32]): Int32 = MutableArray.length(a)\n' > publen.kel
  $ diktor --type-check publen.kel
  ! publen.kel:1:53: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Heap がありません(行は閉じています))
  [1]
  $ printf 'pub let mget[h](a: MutableArray[h, Int32]): Int32 = MutableArray.get(a, 0)\n' > pubget.kel
  $ diktor --type-check pubget.kel
  ! pubget.kel:1:53: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Heap がありません(行は閉じています))
  [1]
  $ cat > parget.kel <<'KEL'
  > let pmap[A, B](xs: Array[A], f: (A) => B @ {}): Array[B] = ???
  > let bad[h](a: MutableArray[h, Int32], xs: Array[Int32]): Array[Int32] =
  >   pmap(xs, fn(x) => MutableArray.get(a, 0) + x)
  > KEL
  $ diktor --type-check parget.kel
  pmap : (Array[A], (A) => B @ {}) => Array[B]
  ! parget.kel:3:21: 型エラー: ラベル Heap がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

可変配列は run の外に持ち出せない:

  $ cat > leak.kel <<'KEL'
  > let leak(): Array[Int32] = run h { MutableArray.new(3, 0) }
  > KEL
  $ diktor --type-check leak.kel
  ! leak.kel:1:28: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

freeze で不変配列にすれば持ち出せる(sample.kel の §10 の doubled):

  $ cat > doubled.kel <<'KEL'
  > let doubled(xs: Array[Int32]): Array[Int32] = run h {
  >   let out = MutableArray.new(Array.length(xs), 0)
  >   let i = Ref.new(0)
  >   Array.each(xs, fn(x) => {
  >     MutableArray.set(out, Ref.get(i), x * 2)
  >     Ref.set(i, Ref.get(i) + 1)
  >   })
  >   MutableArray.freeze(out)
  > }
  > let sum(xs: Array[Int32]): Int32 = run h {
  >   let acc = Ref.new(0)
  >   Array.each(xs, fn(x) => Ref.set(acc, Ref.get(acc) + x))
  >   Ref.get(acc)
  > }
  > let mk(): Array[Int32] = run h {
  >   let a = MutableArray.new(3, 0)
  >   MutableArray.set(a, 0, 1)
  >   MutableArray.set(a, 1, 2)
  >   MutableArray.set(a, 2, 3)
  >   MutableArray.freeze(a)
  > }
  > echoln(show(sum(doubled(mk()))))
  > KEL
  $ diktor --type-check doubled.kel
  doubled : (Array[Int32]) => Array[Int32]
  sum : (Array[Int32]) => Int32
  mk : () => Array[Int32]
  _ : {}
  $ diktor doubled.kel
  12

freeze の観測できる契約。freeze の後に元の可変配列へ書き込んでも、取り出した
配列は変わらない(実装は内容をコピーする):

  $ cat > freeze.kel <<'KEL'
  > let demo(): Int32 = run h {
  >   let a = MutableArray.new(2, 1)
  >   let frozen = MutableArray.freeze(a)
  >   MutableArray.set(a, 0, 99)
  >   Array.get(frozen, 0) + MutableArray.get(a, 0)
  > }
  > echoln(show(demo()))
  > KEL
  $ diktor freeze.kel
  100

この契約は 1 段だけに適用される。要素そのものが可変配列なら、取り出した配列の
要素は、元の可変配列の要素と同じものを指す(sample.kel:694)。freeze の後に
inner へ書き込んだ 99 を、frozen を通して読める:

  $ cat > nested.kel <<'KEL'
  > let probe(): Int32 = run h {
  >   let inner = MutableArray.new(2, 0)
  >   let outer = MutableArray.new(1, inner)
  >   let frozen = MutableArray.freeze(outer)
  >   MutableArray.set(inner, 0, 99)
  >   MutableArray.get(Array.get(frozen, 0), 0)
  > }
  > echoln(show(probe()))
  > KEL
  $ diktor nested.kel
  99

値は共有されるが、型の安全性は保たれる。要素が可変配列だと、その h が結果の型に
残るので、脱出検査が run の外への持ち出しを拒否する(sample.kel:695)。要素が
可変配列でなければ、同じ形のプログラムが通る:

  $ printf 'let leak(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(1, MutableArray.new(1, 0))) }\n' > nested2.kel
  $ diktor --type-check nested2.kel
  ! nested2.kel:1:28: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]
  $ printf 'let flat(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(1, 0)) }\n' > flat.kel
  $ diktor --type-check flat.kel
  flat : () => Array[Int32]

MutableArray[h, A] は型注釈として書ける。sample.kel の §10 のシグネチャの一覧にある「ここだけの
表記」(sample.kel:679)は型パラメータの並び [h, A] を指していて、MutableArray[h, A] を型の式として書くことは禁じていない
(sample.kel:697)。型の表示では h になる(名前の付け方は次の regionshow で確かめる):

  $ printf 'let use[h, A](a: MutableArray[h, A], i: Int32): A @ Heap[h] = MutableArray.get(a, i)\n' > maannot.kel
  $ diktor --type-check maannot.kel
  use : (MutableArray[h, A], Int32) => A @ {Heap[h]}

型の表示では、型パラメータの名前を付け直す。Ref と MutableArray の第 1 引数か、エフェクトの
Heap の引数に現れる変数は h、h1 の順に名前を付け、それ以外の型変数とは別に数える(two)。束縛子に
書いた名前 r、s は表示に残らない。同じ変数が値の型の位置にも現れるときも h と表示する
(both)。一般化されない変数には下線が付く(w)。ユーザの newtype の型引数は
リージョンの位置として数えないので、Box[k] の k は、同じ表示の中に Ref[k, Int32] が
現れる unbox では h になり、現れない size では A になる。regionshow2 は、run の本体で、Int32 と注釈した変数に
Ref の値を束縛する。Ref の第 1 引数の位置にあるスコーレム定数(run のリージョン変数を固定した定数)は、h
ではなく ς1 と表示される:

  $ cat > regionshow.kel <<'KEL'
  > let two[r, s, A](x: Ref[r, A], y: MutableArray[s, Int32]): A @ {Heap[r], Heap[s]} = Ref.get(x)
  > let both[A](x: A, r: Ref[A, Int32]): Int32 = 0
  > let id[A](x: A): A = x
  > let w = id(Ref.new)
  > newtype Box[k] = Box(Ref[k, Int32])
  > let unbox[k](b: Box[k]): Ref[k, Int32] = b match { case Box(r) => r }
  > let size[k](b: Box[k]): Int32 = 0
  > KEL
  $ diktor --type-check regionshow.kel
  two : (Ref[h, A], MutableArray[h1, Int32]) => A @ {Heap[h], Heap[h1]}
  both : (h, Ref[h, Int32]) => Int32
  id : (A) => A
  w : (_A) => Ref[_h, _A] @ {Heap[_h]}
  unbox : (Box[h]) => Ref[h, Int32]
  size : (Box[A]) => Int32
  $ printf 'let g(): Int32 = run h { let r = Ref.new(0); let x: Int32 = r; 0 }\n' > regionshow2.kel
  $ diktor --type-check regionshow2.kel
  ! regionshow2.kel:1:50: 型エラー: 注釈された型を満たしません(型が一致しません: Int32 と Ref[ς1, _A])
  [1]

構造的ヴァリアントのコンストラクタ #Heap のラベルは、エフェクトの Heap と同じ
名前になる。型の表示では、ヴァリアントの行に現れる Heap の引数をリージョンの位置として
数えない。vheap の v と u の型変数は A と表示される:

  $ cat > vheap.kel <<'KEL'
  > let v[A](x: A) = #Heap(x)
  > let u[A](t: #Heap(A) | #Other(A)): Int32 = 0
  > KEL
  $ diktor --type-check vheap.kel
  v : (A) => #Heap(A) | R1
  u : (#Heap(A) | #Other(A)) => Int32

単一化も、ヴァリアントの行とエフェクト行を同じように区別する。vheapmis は #Heap の引数で String と Int32 が一致しない
プログラムで、ラベルだけを #Other に替えた votheremis と同じメッセージで報告する:

  $ cat > vheapmis.kel <<'KEL'
  > let f(x: #Heap(Int32)): Int32 = 0
  > let g: Int32 = f(#Heap("s"))
  > KEL
  $ diktor --type-check vheapmis.kel
  f : (#Heap(Int32)) => Int32
  ! vheapmis.kel:2:18: 型エラー: 型が一致しません: String と Int32
  [1]
  $ cat > votheremis.kel <<'KEL'
  > let f(x: #Other(Int32)): Int32 = 0
  > let g: Int32 = f(#Other("s"))
  > KEL
  $ diktor --type-check votheremis.kel
  f : (#Other(Int32)) => Int32
  ! votheremis.kel:2:18: 型エラー: 型が一致しません: String と Int32
  [1]

添字が範囲外なら、不変配列でも可変配列でも実行時エラーになる。負の長さも実行時エラーになる:

  $ printf 'let mk(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(2, 1)) }\necholn(show(Array.get(mk(), 5)))\n' > oob1.kel
  $ diktor oob1.kel
  実行時エラー: 配列の範囲外です
  [3]
  $ printf 'let f(): Int32 = run h { MutableArray.get(MutableArray.new(2, 1), 5) }\necholn(show(f()))\n' > oob2.kel
  $ diktor oob2.kel
  実行時エラー: 配列の範囲外です
  [3]
  $ printf 'let mk(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(-1, 1)) }\necholn(show(Array.length(mk())))\n' > negl.kel
  $ diktor negl.kel
  実行時エラー: MutableArray.new: 長さが負です
  [3]

@ {} のコールバックは可変配列を操作できない(sample.kel の §11 の決定性)。
run で囲んでも、外側のリージョンの可変配列には書き込めない:

  $ cat > pardet.kel <<'KEL'
  > let pmap[A, B](xs: Array[A], f: (A) => B @ {}): Array[B] = ???
  > let bad[h](a: MutableArray[h, Int32], xs: Array[Int32]): Array[Int32] =
  >   pmap(xs, fn(x) => run h2 { MutableArray.set(a, 0, x); x })
  > KEL
  $ diktor --type-check pardet.kel
  pmap : (Array[A], (A) => B @ {}) => Array[B]
  ! pardet.kel:3:47: 型エラー: ほかのリージョンの MutableArray を使おうとしています(スコープ付きの型が一致しません: ς1 と ς2)
  [1]

不変配列は @ {} のコールバックから読める:

  $ cat > parread.kel <<'KEL'
  > let pmap[A, B](xs: Array[A], f: (A) => B @ {}): Array[B] = ???
  > let mk(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(2, 5)) }
  > let f(xs: Array[Int32]): Array[Int32] = pmap(xs, fn(x) => x + Array.get(xs, 0))
  > echoln(show(Array.get(f(mk()), 1)))
  > KEL
  $ diktor --type-check parread.kel
  pmap : (Array[A], (A) => B @ {}) => Array[B]
  mk : () => Array[Int32]
  f : (Array[Int32]) => Array[Int32]
  _ : {}

pub の「@ を省略した宣言は純粋」という規則も、同じ検査で守られる:

  $ cat > pubpure.kel <<'KEL'
  > pub let wipe[h](a: MutableArray[h, Int32]): Unit = run h2 { MutableArray.set(a, 0, 7) }
  > KEL
  $ diktor --type-check pubpure.kel
  ! pubpure.kel:1:78: 型エラー: ほかのリージョンの MutableArray を使おうとしています(スコープ付きの型が一致しません: ς1 と ς2)
  [1]

最も外側の矢印に @ {} と書いた関数 g には、名前で参照するときに行を開く規則が適用されるので、run の
中の each に渡せる(LangSpec §13.2):

  $ cat > eachclosed.kel <<'KEL'
  > let g(x: Int32): {} @ {} = {}
  > let use(xs: Array[Int32]): {} = run h { Array.each(xs, g) }
  > KEL
  $ diktor --type-check eachclosed.kel
  g : (Int32) => {} @ {}
  use : (Array[Int32]) => {}

newtype のフィールドを通して、終了したリージョンの可変配列に書き込むプログラムも拒否する。
入れ子の矢印で @ を省略すると @ {} になるので、Box のフィールドの関数は Heap を起こせない。
配列を不変と可変に分けるだけでは、この形を拒否できない:

  $ cat > adv5.kel <<'KEL'
  > newtype Box = Box(() => Int32)
  > let escape(): Box = run h {
  >   let a = MutableArray.new(1, 41)
  >   Box(fn() => { MutableArray.set(a, 0, 42); MutableArray.get(a, 0) })
  > }
  > let call(b: Box): Int32 = b match { case Box(f) => f() }
  > echoln(show(call(escape())))
  > KEL
  $ diktor --type-check adv5.kel
  ! adv5.kel:4:3: 型エラー: ラベル Heap がありません(行は閉じています)(コンストラクタ Box のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

不変配列に書き込む手段はない:

  $ printf 'let bump(a: Array[Int32]): Unit = run h { Array.set(a, 0, 42) }\n' > noset.kel
  $ diktor --type-check noset.kel
  ! noset.kel:1:43: 型エラー: 未束縛の変数: Array.set
  [1]
  $ printf 'let mk(): Array[Int32] = run h { Array.new(3, 0) }\n' > nonew.kel
  $ diktor --type-check nonew.kel
  ! nonew.kel:1:34: 型エラー: 未束縛の変数: Array.new
  [1]

Ref の第 1 引数で 2 つのスコーレム定数のリージョンが一致しないときは、ほかのリージョンの
Ref を使おうとしたものとして報告する。regswap は run を含まず、エフェクト行が Heap[h] の関数の中で、
型パラメータ k のリージョンの参照を読む:

  $ cat > regswap.kel <<'KEL'
  > let swap[h, k](a: Ref[h, Int32], b: Ref[k, Int32]): Unit @ Heap[h] = Ref.set(a, Ref.get(b))
  > KEL
  $ diktor --type-check regswap.kel
  ! regswap.kel:1:89: 型エラー: ほかのリージョンの Ref を使おうとしています(スコープ付きの型が一致しません: ς1 と ς2)
  [1]

regannot は、内側の run の本体で、内側の参照に外側のリージョンの Ref という注釈を付ける。
注釈を検査したときのメッセージにも、括弧の中に同じ言い換えが入る:

  $ cat > regannot.kel <<'KEL'
  > let g(): Int32 = run h {
  >   let r = Ref.new(0)
  >   run k {
  >     let s = Ref.new(1)
  >     let t: Ref[h, Int32] = s
  >     0
  >   }
  > }
  > KEL
  $ diktor --type-check regannot.kel
  ! regannot.kel:5:9: 型エラー: 注釈された型を満たしません(ほかのリージョンの Ref を使おうとしています(スコープ付きの型が一致しません: ς1 と ς2))
  [1]

片方のリージョンがまだ決まっていない型変数のときは、言い換えずに元のメッセージで
報告する。次の 2 つでは、その型変数に run のリージョン変数を束縛すると
スコープの外へ漏れる。regesc は Ref の第 1 引数で、regheapesc は Heap の引数で、
脱出のメッセージになる:

  $ cat > regesc.kel <<'KEL'
  > let mk[B](x: B): Ref[B, Int32] = ???
  > let f(): Unit = {
  >   let k = fn(z) => { let s = mk(z); run h { Ref.get(s); () } }
  >   ()
  > }
  > KEL
  $ diktor --type-check regesc.kel
  mk : (h) => Ref[h, Int32]
  ! regesc.kel:3:53: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]
  $ cat > regheapesc.kel <<'KEL'
  > let mk[B](x: B): () => Int32 @ Heap[B] = ???
  > let f(): Unit = {
  >   let k = fn(z) => { let s = mk(z); run h { s(); () } }
  >   ()
  > }
  > KEL
  $ diktor --type-check regheapesc.kel
  mk : (h) => () => Int32 @ {Heap[h]}
  ! regheapesc.kel:3:45: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

片方のリージョンがまだ決まっていない型変数で、もう片方が型変数でない型のときも、
束縛の検査が失敗すればそのメッセージで報告し、リージョンではないとは報告しない。
regoccurs は、g の h を具体化した型変数に、その変数を含む Ref の型を束縛しようとして
occurs check に失敗する。regescref は、Ref の第 1 引数の型変数に、run のスコーレム定数を含む
Ref の型を束縛しようとして、脱出のエラーになる:

  $ cat > regoccurs.kel <<'KEL'
  > let g[h](r: Ref[h, Int32], s: Ref[Ref[h, Int32], Int32]): Unit = ()
  > let t(x) = g(x, x)
  > KEL
  $ diktor --type-check regoccurs.kel
  g : (Ref[h, Int32], Ref[Ref[h, Int32], Int32]) => {}
  ! regoccurs.kel:2:17: 型エラー: occurs check に失敗しました(無限型が発生します)
  [1]
  $ cat > regescref.kel <<'KEL'
  > let mk[B](x: B): Ref[B, Int32] = ???
  > let eq[A](x: A, y: A): Unit = ()
  > let f(): Unit = {
  >   let k = fn(z) => { let s = mk(z); run h { let t = Ref.new(0); eq(s, mk(t)); () } }
  >   ()
  > }
  > KEL
  $ diktor --type-check regescref.kel
  mk : (h) => Ref[h, Int32]
  eq : (A, A) => {}
  ! regescref.kel:4:71: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]
