リージョンと配列(仕様 §10)。不変 Array[A] と可変 MutableArray[h, A]
の分離が、脱出検査・par の決定性・pub の純粋性をどう守るかのゴールデン。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

不変配列の読みは純粋 — run も Heap も要らない:

  $ cat > read.kel <<'KEL'
  > let peek(a: Array[Int32]): Int32 = Array.get(a, 0)
  > let len(a: Array[Int32]): Int32 = Array.length(a)
  > let g(x: Int32): {} @ {} = {}
  > let walk(a: Array[Int32]): {} @ {} = Array.each(a, g)
  > KEL
  $ diktor --type-check read.kel
  peek : (Array[Int32]) => Int32
  len : (Array[Int32]) => Int32
  g : (Int32) => {}
  walk : (Array[Int32]) => {}

可変配列は h を型に持つので、引数を破壊する関数は純粋として型付かない
(仕様 §10「bump が書けない」):

  $ cat > bump.kel <<'KEL'
  > let bump[h](a: MutableArray[h, Int32]): Unit = run h2 { MutableArray.set(a, 0, 42) }
  > KEL
  $ diktor --type-check bump.kel
  ! bump.kel:1:74: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
  [1]

書くと宣言したなら通る。行に Heap[h] が出る:

  $ cat > honest.kel <<'KEL'
  > let bump[h, E](a: MutableArray[h, Int32]): Unit @ {Heap[h] extends E} =
  >   MutableArray.set(a, 0, 42)
  > KEL
  $ diktor --type-check honest.kel
  bump : (MutableArray[A, Int32]) => {} @ {Heap[A] extends R1}

MutableArray.length も Heap[h] を要求する(長さは変わらないが、可変配列に
触れること自体が行に載る — 仕様 §10 の署名一覧のとおり):

  $ cat > mlen.kel <<'KEL'
  > let demo(): Int32 = run h {
  >   let a = MutableArray.new(4, 0)
  >   MutableArray.length(a)
  > }
  > echoln(show(demo()))
  > KEL
  $ diktor mlen.kel
  4

読むだけの操作(length / get)にも Heap[h] が載っていることは、pub の純粋性と
par_map の @ {} コールバックで観測する(署名から Heap を外しても上の mlen は
通ってしまうので、この 3 ブロックが署名の回帰):

  $ printf 'pub let mlen[h](a: MutableArray[h, Int32]): Int32 = MutableArray.length(a)\n' > publen.kel
  $ diktor --type-check publen.kel
  ! publen.kel:1:53: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: 行 ς1 は注釈で固定された行変数なので、ラベル Heap を足せません(注釈側に Heap を(必要なら引数つきで)書き足してください))
  [1]
  $ printf 'pub let mget[h](a: MutableArray[h, Int32]): Int32 = MutableArray.get(a, 0)\n' > pubget.kel
  $ diktor --type-check pubget.kel
  ! pubget.kel:1:53: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: 行 ς1 は注釈で固定された行変数なので、ラベル Heap を足せません(注釈側に Heap を(必要なら引数つきで)書き足してください))
  [1]
  $ cat > parget.kel <<'KEL'
  > let bad[h](a: MutableArray[h, Int32], xs: Array[Int32]): Array[Int32] =
  >   par_map(xs, fn(x) => MutableArray.get(a, 0) + x)
  > KEL
  $ diktor --type-check parget.kel
  ! parget.kel:2:24: 型エラー: ラベル Heap がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

可変配列は run の外に出せない:

  $ cat > leak.kel <<'KEL'
  > let leak(): Array[Int32] = run h { MutableArray.new(3, 0) }
  > KEL
  $ diktor --type-check leak.kel
  ! leak.kel:1:28: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

freeze で不変配列にすれば出せる(仕様 §10 の doubled):

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

freeze の観測可能な契約: freeze 後に元の可変配列へ書いても、取り出した
配列は変わらない(実装はコピー — D69):

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

この契約は 1 段だけ成り立つ。要素そのものが可変配列なら、取り出した配列の
要素は元と同じものを指す(D137)。freeze の後に inner へ書いた 99 が、
frozen 越しに読める:

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

値は共有されるが、型の側は破れない。要素が可変配列だと、その h が結果の型に
残るので脱出検査が run の外への持ち出しを拒む(D137)。要素が可変配列でなければ
同じ形が通る:

  $ printf 'let leak(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(1, MutableArray.new(1, 0))) }\n' > nested2.kel
  $ diktor --type-check nested2.kel
  ! nested2.kel:1:28: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]
  $ printf 'let flat(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(1, 0)) }\n' > flat.kel
  $ diktor --type-check flat.kel
  flat : () => Array[Int32]

MutableArray[h, A] は型注釈として書ける。仕様 §10 の署名一覧が断る「ここだけの
表記」はパラメータの並びの話であって、型式を禁じてはいない(D137)。印字は
型パラメータを付け直すので、h は A として出る:

  $ printf 'let use[h, A](a: MutableArray[h, A], i: Int32): A @ Heap[h] = MutableArray.get(a, i)\n' > maannot.kel
  $ diktor --type-check maannot.kel
  use : (MutableArray[A, B], Int32) => B @ {Heap[A] extends R1}

添字が範囲外なら実行時エラー(不変・可変とも)。負の長さも実行時に弾く:

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

par_map の @ {} コールバックは可変配列に触れない(§11 の決定性。分離前は
run で包めば書けた — M20 の動機 (a)):

  $ cat > pardet.kel <<'KEL'
  > let bad[h](a: MutableArray[h, Int32], xs: Array[Int32]): Array[Int32] =
  >   par_map(xs, fn(x) => run h2 { MutableArray.set(a, 0, x); x })
  > KEL
  $ diktor --type-check pardet.kel
  ! pardet.kel:2:50: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
  [1]

不変配列は par_map のコールバックから読める:

  $ cat > parread.kel <<'KEL'
  > let mk(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(2, 5)) }
  > let f(xs: Array[Int32]): Array[Int32] = par_map(xs, fn(x) => x + Array.get(xs, 0))
  > echoln(show(Array.get(f(mk()), 1)))
  > KEL
  $ diktor parread.kel
  10

pub の「@ を省略した宣言は純粋」も同じ経路で守られる(M20 の動機 (b)):

  $ cat > pubpure.kel <<'KEL'
  > pub let wipe[h](a: MutableArray[h, Int32]): Unit = run h2 { MutableArray.set(a, 0, 7) }
  > KEL
  $ diktor --type-check pubpure.kel
  ! pubpure.kel:1:78: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
  [1]

閉じた行 @ {} のコールバックを run の中の each に渡す形は、each とは無関係に
落ちる(run が体の行に Heap[h] を要求し、閉じた行はそれを受けられない —
非サブエフェクティングの既存規則。旧 spec_gaps.t の eachclosed):

  $ cat > eachclosed.kel <<'KEL'
  > let g(x: Int32): {} @ {} = {}
  > let use(xs: Array[Int32]): {} = run h { Array.each(xs, g) }
  > KEL
  $ diktor --type-check eachclosed.kel
  g : (Int32) => {}
  ! eachclosed.kel:2:56: 型エラー: ラベル Heap がありません(行は閉じています)
  [1]

newtype のフィールドを経由して死んだリージョンの可変配列を書く形も、入れ子の
矢印の省略 @ が @ {} になった(M26 / D75)ので閉じた — 分離(M24)だけでは
残っていた V14 の形(M24 の時点では 42 を出して通った):

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

不変配列に書く手段は無い:

  $ printf 'let bump(a: Array[Int32]): Unit = run h { Array.set(a, 0, 42) }\n' > noset.kel
  $ diktor --type-check noset.kel
  ! noset.kel:1:43: 型エラー: 未束縛の変数: Array.set
  [1]
  $ printf 'let mk(): Array[Int32] = run h { Array.new(3, 0) }\n' > nonew.kel
  $ diktor --type-check nonew.kel
  ! nonew.kel:1:34: 型エラー: 未束縛の変数: Array.new
  [1]
