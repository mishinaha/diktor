newtype と型エイリアスの型パラメータについて、カインド推論の結果を期待出力と比較するゴールデンテストである。
行の中に書く EffectRow エイリアス、高カインドの型変数の定義域、値の型の位置とエフェクト位置でのカインドの照合も扱う。
期待出力を変えるときは dune promote で更新し、差分を目で確認する。

sample.kel §6 は、型パラメータのカインドを、同じ型宣言のグループにある型の本体での使われ方から推論すると定める。
使われ方がなければ、カインドは Type になる(sample.kel:246-247)。
型引数の読み方は、対応するパラメータのカインドによって変わる(sample.kel:252)。
例には、sample.kel §9 の `newtype Callback[E] = Callback(() => Unit @ E)`(sample.kel:509)を使う。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

行カインドのパラメータを持つ newtype を宣言できる。
その型引数には、行変数も具体的な行も書ける:

  $ cat > cb.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Callback[E] = Callback(() => Unit @ E)
  > let mk[E](f: () => Unit @ E): Callback[E] = Callback(f)
  > let run_cb[E](c: Callback[E]): Unit @ E = c match { case Callback(f) => f() }
  > let println(message: String): Unit @ Print = perform print(message)
  > let pure_cb(): Callback[{}] = Callback(fn() => {})
  > let print_cb(): Callback[{Print}] = Callback(fn() => println("x"))
  > EOF
  $ diktor --type-check --no-prelude cb.kel
  mk : (() => {}) => Callback[R1]
  run_cb : (Callback[R1]) => {}
  println : (String) => {} @ {Print}
  pure_cb : () => Callback[{}]
  print_cb : () => Callback[{Print}]

行変数を含む行も書け、pub の宣言に必要な完全な型注釈(sample.kel §13)にも使える:

  $ cat > cbext.kel <<'EOF'
  > pub newtype Callback[E] = Callback(() => Unit @ E)
  > pub let mk[E](f: () => Unit @ E): Callback[E] = Callback(f)
  > pub let open_[E](c: Callback[E]): () => Unit @ E = c match { case Callback(f) => f }
  > let with_ext[E](c: Callback[{Print extends E}]): Callback[{Print extends E}] = c
  > EOF
  $ diktor --type-check cbext.kel
  mk : (() => {}) => Callback[R1] @ {}
  open_ : (Callback[R1]) => (() => {}) @ {}
  with_ext : (Callback[{Print extends R1}]) => Callback[{Print extends R1}]

実行もできる(値の構築、分解、handle を挟んだ呼び出し):

  $ cat > cbrun.kel <<'EOF'
  > newtype Callback[E] = Callback(() => Unit @ E)
  > let run_cb[E](c: Callback[E]): Unit @ E = c match { case Callback(f) => f() }
  > let println(message: String): Unit @ Print = perform print(message)
  > let main(): Unit @ Console = {
  >   let c = Callback(fn() => println("hello"))
  >   run_cb(c) handle {
  >     case print(m) => resume(perform write(m))
  >   }
  > }
  > main()
  > EOF
  $ diktor cbrun.kel
  hello

使われ方のないパラメータのカインドは Type に決まる(既定化):

  $ cat > phantom.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Phantom[E] = Phantom(Int32)
  > let ok(): Phantom[Int32] = Phantom(0)
  > EOF
  $ diktor --type-check --no-prelude phantom.kel
  ok : () => Phantom[Int32]

カインドを決める「使われ方」は、そのパラメータを宣言した型の本体に限らない。
同じ型宣言のグループにある、すべての型の本体が推論に使われる。
自分の本体では使っていないパラメータでも、ほかの宣言の本体が行カインドの位置に渡せば、行カインドになる。
ここでは、N の本体が同じ X を Ph[X] と Callback[X] に渡すので、Ph の E は行カインドになる:

  $ cat > phantomrow.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Callback[E] = Callback(() => Unit @ E)
  > newtype Ph[E] = MkPh(Int32)
  > newtype N[X] = MkN(Ph[X], Callback[X])
  > let f(x: Ph[{Print}]): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude phantomrow.kel
  f : (Ph[{Print}]) => Int32

同じ宣言から、行として使う側(上の N と Callback)を取り除くと、パラメータのカインドは Type に決まる。
そのため、型引数の {Print} は型として読まれ、エラーになる:

  $ cat > phantomtype.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Ph2[E] = MkPh2(Int32)
  > let f(x: Ph2[{Print}]): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude phantomtype.kel
  ! phantomtype.kel:4:14: 型エラー: エフェクトラベルはこの位置(レコード型)では使えません
  [1]

Type カインドのパラメータに行を渡すと、その型を書いた宣言の時点でエラーになる。
値を作る箇所まで待たずに、`カインドが一致しません` を報告する:

  $ cat > kinderr.kel <<'EOF'
  > type Unit = {}
  > newtype Box[A] = Box(A)
  > let f[E](g: () => Unit @ E): Box[E] = ???
  > EOF
  $ diktor --type-check --no-prelude kinderr.kel
  ! kinderr.kel:3:30: 型エラー: 型構成子 Box の第1引数のカインドが一致しません: Type を期待しましたが ς1 は Row です
  [1]

入れ子の型引数で取り違えた場合(Row の位置に Type の型を書く):

  $ printf 'newtype Callback[E] = Callback(() => Unit @ E)\nlet f[E](c: Callback[Callback[E]]): Int32 = 0\n' > nest.kel
  $ diktor --type-check nest.kel
  ! nest.kel:2:13: 型エラー: 型構成子 Callback の第1引数のカインドが一致しません: Row を期待しましたが Callback[ς1] は Type です
  [1]

コンストラクタのフィールドの型のカインドは、Type でなければならない。
同じパラメータを行と型の両方に使う宣言は、この検査でエラーになる:

  $ cat > fieldkind.kel <<'EOF'
  > type Unit = {}
  > newtype Bad[E] = Bad(() => Unit @ E, E)
  > EOF
  $ diktor --type-check --no-prelude fieldkind.kel
  ! fieldkind.kel:2:38: 型エラー: コンストラクタ Bad のフィールドの型のカインドが Type ではありません: R1 :: Row
  [1]

EffectRow エイリアスをフィールドの型に書いた宣言も、宣言の時点でエラーになる。
値を作る箇所(3 行目の X(???))ではなく、2 行目の宣言の位置を報告する:

  $ printf 'type P: EffectRow = {Print}\nnewtype X = X(P)\nlet f(): X = X(???)\n' > fieldalias.kel
  $ diktor --type-check fieldalias.kel
  ! fieldalias.kel:2:15: 型エラー: コンストラクタ X のフィールドの型のカインドが Type ではありません: {Print} :: Row
  [1]

相互再帰する newtype では、どちらを先に宣言してもカインドが伝わる。
宣言ごとに既定化すると、先に処理した宣言が、もう一方のパラメータのカインドまで Type に決めてしまうので、既定化はグループ全体を読んだ後に行う。
ここでは行変数を渡し、具体的な行を渡す場合は下の fwdrow で確かめる:

  $ cat > mutual.kel <<'EOF'
  > type Unit = {}
  > newtype A2[E] = MkA(B2[E])
  > newtype B2[E] = MkB(() => Unit @ E)
  > let f[E](x: A2[E]): A2[E] = x
  > EOF
  $ diktor --type-check --no-prelude mutual.kel
  f : (A2[R1]) => A2[R1]
  $ cat > mutual2.kel <<'EOF'
  > type Unit = {}
  > newtype B3[E] = MkB3(() => Unit @ E)
  > newtype A3[E] = MkA3(B3[E])
  > let f[E](x: A3[E]): A3[E] = x
  > EOF
  $ diktor --type-check --no-prelude mutual2.kel
  f : (A3[R1]) => A3[R1]

後ろで宣言する newtype の行カインドのパラメータに具体的な行を渡す宣言も、宣言順によらず型検査に通る。
パス 1b(コンストラクタを登録するパス)の前に、newtype の本体を試しに精緻化(elaboration)して、カインドだけを決めて結果を捨てるからである(以下、この処理を試行と呼ぶ)。
渡す先の本体の試行がパラメータのカインドを決めれば、パス 1b は型引数の {…} を行として判別できる。
fwdrow は渡す先の B4 を後ろで宣言し、fwdrow2 は B5 を前で宣言する:

  $ cat > fwdrow.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype A4[X] = MkA4(B4[{Print extends X}])
  > newtype B4[E] = MkB4(() => Unit @ E)
  > let f[E](x: A4[E]): A4[E] = x
  > EOF
  $ diktor --type-check --no-prelude fwdrow.kel
  f : (A4[R1]) => A4[R1]
  $ cat > fwdrow2.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype B5[E] = MkB5(() => Unit @ E)
  > newtype A5[X] = MkA5(B5[{Print extends X}])
  > let f[E](x: A5[E]): A5[E] = x
  > EOF
  $ diktor --type-check --no-prelude fwdrow2.kel
  f : (A5[R1]) => A5[R1]

連鎖が 1 段深い場合(fwdrow3)と、module の中に置いた場合(fwdrowmod)でも同じである:

  $ cat > fwdrow3.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype A7[X] = MkA7(B7[{Print extends X}])
  > newtype B7[Y] = MkB7(C7[Y])
  > newtype C7[E] = MkC7(() => Unit @ E)
  > let f[E](x: A7[E]): A7[E] = x
  > EOF
  $ diktor --type-check --no-prelude fwdrow3.kel
  f : (A7[R1]) => A7[R1]
  $ cat > fwdrowmod.kel <<'EOF'
  > module M {
  >   pub newtype A6[X] = MkA6(B6[{Print extends X}])
  >   pub newtype B6[E] = MkB6(() => Unit @ E)
  > }
  > let f[E](x: M.A6[E]): M.A6[E] = x
  > EOF
  $ diktor --type-check fwdrowmod.kel
  f : (M.A6[R1]) => M.A6[R1]

module の中にある深さ 2 の連鎖も型検査に通ることから、試行のループが module のスコープの中(with_decl_module)で実行されることを確かめる。
fwdrowmod2 では、B9 の本体の C9[Y] が module の内部の型を修飾なしで参照するので、スコープの外で試行すると C9 を解決できない。
上の fwdrowmod は、module の内部の型を参照しない B6 の本体の試行だけでカインドが決まるので、この確認にならない:

  $ cat > fwdrowmod2.kel <<'EOF'
  > module M {
  >   pub newtype A9[X] = MkA9(B9[{Print extends X}])
  >   pub newtype B9[Y] = MkB9(C9[Y])
  >   pub newtype C9[E] = MkC9(() => Unit @ E)
  > }
  > let f[E](x: M.A9[E]): M.A9[E] = x
  > EOF
  $ diktor --type-check fwdrowmod2.kel
  f : (M.A9[R1]) => M.A9[R1]

effect の名前は、試行より前のパス 1a で宣言表に登録する。
そのため、() => Unit @ {Log} のようなフィールドも試行の中で読め、その後ろのフィールドがパラメータのカインドを決める。
2 つのフィールドが別々のコンストラクタにあっても同じである:

  $ cat > specfield.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype B10[E] = MkB10(() => Unit @ {Log}, () => Unit @ E)
  > newtype A10 = MkA10(B10[{}])
  > let f(x: A10): A10 = x
  > EOF
  $ diktor --type-check --no-prelude specfield.kel
  f : (A10) => A10
  $ cat > specfield2.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype B11[E] = MkB11a(() => Unit @ {Log}) | MkB11b(() => Unit @ E)
  > newtype A11 = MkA11(B11[{}])
  > let f(x: A11): A11 = x
  > EOF
  $ diktor --type-check --no-prelude specfield2.kel
  f : (A11) => A11

1 つのフィールドの中に行変数とラベルが並ぶ場合も、試行はフィールド全体を読む。
タプルやレコードの要素は右から読むが、右端の {Log} でエラーになって止まることはない:

  $ cat > specinner.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype B12[E] = MkB12((() => Unit @ E, () => Unit @ {Log}))
  > newtype A12 = MkA12(B12[{}])
  > let f(x: A12): A12 = x
  > EOF
  $ diktor --type-check --no-prelude specinner.kel
  f : (A12) => A12
  $ cat > specinner2.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype B13[E] = MkB13((() => Unit @ E, () => Unit @ {Log}))
  > newtype A13[X] = MkA13(B13[{extends X}])
  > let f[E](x: A13[E]): A13[E] = x
  > EOF
  $ diktor --type-check --no-prelude specinner2.kel
  f : (A13[R1]) => A13[R1]

前方参照でも同じで、後ろのフィールドから連鎖してカインドが決まれば型検査に通る。
B14 の第 2 フィールドの C14[Y] が、Y のカインドを C14 のパラメータのカインドと同じカインド変数にする。
その後、C14 の本体の試行が、そのカインドを行に決める:

  $ cat > specfwd.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype A14[X] = MkA14(B14[{Log extends X}])
  > newtype B14[Y] = MkB14(() => Unit @ {Log}, C14[Y])
  > newtype C14[E] = MkC14(() => Unit @ E)
  > let f[E](x: A14[E]): A14[E] = x
  > EOF
  $ diktor --type-check --no-prelude specfwd.kel
  f : (A14[R1]) => A14[R1]

後ろで宣言する型に渡す型引数が {}(空の波括弧)でも、型検査に通る。
試行の間は、カインドが決まっていないパラメータに渡した要素のない波括弧({} と {extends X})を、読まずに飛ばす。
飛ばした波括弧は、渡す先のカインドが決まった後に、パス 1b がもう一度読む。
渡す先の本体が、ラベルを含むフィールドの中でパラメータを使う場合(specunit2)も、その本体の試行がカインドを決めるので通る:

  $ cat > specunit.kel <<'EOF'
  > type Unit = {}
  > newtype A15[X] = MkA15(B15[{}], () => Unit @ X)
  > newtype B15[E] = MkB15(() => Unit @ E)
  > let f[E](x: A15[E]): A15[E] = x
  > EOF
  $ diktor --type-check --no-prelude specunit.kel
  f : (A15[R1]) => A15[R1]
  $ cat > specunit2.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype A16 = MkA16(B16[{}])
  > newtype B16[E] = MkB16((() => Unit @ E, () => Unit @ {Log}))
  > let f(x: A16): A16 = x
  > EOF
  $ diktor --type-check --no-prelude specunit2.kel
  f : (A16) => A16

型引数にラベルを書いた場合も、宣言順によらず型検査に通る(speclab と speclab2):

  $ cat > speclab.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype A17[X] = MkA17(B17[{Log extends X}])
  > newtype B17[E] = MkB17((() => Unit @ E, () => Unit @ {Log}))
  > let f[E](x: A17[E]): A17[E] = x
  > EOF
  $ diktor --type-check --no-prelude speclab.kel
  f : (A17[R1]) => A17[R1]
  $ cat > speclab2.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype B18[E] = MkB18((() => Unit @ E, () => Unit @ {Log}))
  > newtype A18[X] = MkA18(B18[{Log extends X}])
  > let f[E](x: A18[E]): A18[E] = x
  > EOF
  $ diktor --type-check --no-prelude speclab2.kel
  f : (A18[R1]) => A18[R1]

ラベルを略記(@ Log)で書いても、module の中に置いても同じである:

  $ cat > specbare.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype A = MkA(B[{}])
  > newtype B[E] = MkB((() => Unit @ E, () => Unit @ Log))
  > let f(x: A): A = x
  > EOF
  $ diktor --type-check --no-prelude specbare.kel
  f : (A) => A
  $ cat > specmod.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > module M {
  >   pub newtype A = MkA(B[{}])
  >   pub newtype B[E] = MkB((() => Unit @ E, () => Unit @ {Log}))
  > }
  > let f(x: M.A): M.A = x
  > EOF
  $ diktor --type-check --no-prelude specmod.kel
  f : (M.A) => M.A

渡す先の本体が、さらに後ろの newtype にラベル付きの行を渡す場合である。
1 回目の試行は、C[{Log}] を読む時点で C のパラメータのカインドが決まっていないので失敗する。
試行は、決まったカインドが増えなくなるまで繰り返すので、2 回目には読める:

  $ cat > specfix.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype A = MkA(B[{}])
  > newtype B[E] = MkB((() => Unit @ E, C[{Log}]))
  > newtype C[F] = MkC(() => Unit @ F)
  > let f(x: A): A = x
  > EOF
  $ diktor --type-check --no-prelude specfix.kel
  f : (A) => A

この繰り返しは、型エイリアスのパラメータのカインドが決まったことも、進展として数える。
ここでは、Al2 から Al1 のカインドが決まった後の回で、B の E のカインドが決まる:

  $ cat > specalias.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype A = MkA(B[{}])
  > newtype B[E] = MkB((() => Unit @ E, Al1[{Log}]))
  > type Al1[F] = Al2[F]
  > type Al2[G] = () => Unit @ G
  > let f(x: A): A = x
  > EOF
  $ diktor --type-check --no-prelude specalias.kel
  f : (A) => A

宣言のないラベル(名前の書き間違い)は、試行の中でも読めない。
これは、パス 1b が未知のエフェクトとして報告する:

  $ cat > spectypo.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype A = MkA(B[{}])
  > newtype B[E] = MkB((() => Unit @ E, () => Unit @ {Lgo}))
  > EOF
  $ diktor --type-check --no-prelude spectypo.kel
  ! spectypo.kel:4:50: 型エラー: 未知のエフェクト: Lgo
  [1]

後ろで宣言する型に {} を渡した型の値を作り、実行できる:

  $ cat > specrun.kel <<'EOF'
  > effect Log = { log: (String) => Unit }
  > newtype A = MkA(B[{}])
  > newtype B[E] = MkB((() => Unit @ E, () => Unit @ {Log}))
  > let main() = {
  >   let a = MkA(MkB((fn() => {}, fn() => perform log("x"))))
  >   a match { case MkA(MkB((g, _))) => g() }
  >   echoln("ok")
  > }
  > main()
  > EOF
  $ diktor specrun.kel
  ok

型エイリアスの型引数にも、パラメータのカインドが決まる前に読む位置がある。
後ろで宣言するエイリアスに {} を渡す宣言も、型検査に通る。
{} は、エイリアスの本体が E を使う位置(ここでは @ の右)に合わせて、空のエフェクト行として読む:

  $ cat > aliasunit.kel <<'EOF'
  > type Unit = {}
  > type C19 = A19[{}]
  > type A19[E] = (Int32) => Unit @ E
  > let f(g: C19): Unit = g(1)
  > EOF
  $ diktor --type-check --no-prelude aliasunit.kel
  f : ((Int32) => {} @ {}) => {}

本体が E を値の型の位置で使うエイリアスでは、同じ {} を空のレコード型として読む:

  $ cat > aliasunit2.kel <<'EOF'
  > type Unit = {}
  > type C20 = A20[{}]
  > type A20[E] = (E, Int32)
  > let v: C20 = ({}, 2)
  > EOF
  $ diktor --type-check --no-prelude aliasunit2.kel
  v : ({}, Int32)

エイリアスの連鎖に {extends R} を渡す場合である。
中継するエイリアス B21 のパラメータも、末端の A21 が決めるカインドになり、{extends R} の R は行カインドになる:

  $ cat > aliasunit3.kel <<'EOF'
  > type Unit = {}
  > type C21[R] = B21[{extends R}]
  > type D21 = B21[{}]
  > type B21[E] = A21[E]
  > type A21[E] = (Int32) => Unit @ E
  > let f[R](g: C21[R]): Unit @ R = g(1)
  > let h(g: D21): Unit = g(2)
  > EOF
  $ diktor --type-check --no-prelude aliasunit3.kel
  f : ((Int32) => {}) => {}
  h : ((Int32) => {} @ {}) => {}

A26 は本体でパラメータを使わず、C26 はその型引数に {extends R} を渡す。
aliasunit4 の C26[{}] は型検査に通り、aliasunit4b の C26[Int32] は、R には行が必要なので拒否する:

  $ cat > aliasunit4.kel <<'EOF'
  > type C26[R] = A26[{extends R}]
  > type A26[E] = Int32
  > let v: C26[{}] = 1
  > EOF
  $ diktor --type-check --no-prelude aliasunit4.kel
  v : Int32
  $ printf 'type C26[R] = A26[{extends R}]\ntype A26[E] = Int32\nlet w: C26[Int32] = 1\n' > aliasunit4b.kel
  $ diktor --type-check --no-prelude aliasunit4b.kel
  ! aliasunit4b.kel:3:12: 型エラー: 型 Int32 はエフェクトではありません(ここにはエフェクト行が要ります)
  [1]

newtype のフィールドから、前で宣言したエイリアスに具体的な行({Print})を渡す場合(N22)である。
後ろで宣言するエイリアスに {} を渡す場合も、同じファイルで確かめる。
{Print} を渡す場合は、パス 1b が型引数を判別する時点で、エイリアスのパラメータのカインドが決まっている必要がある。
そのため、エイリアスの本体もパス 1b の前に試行する:

  $ cat > ntalias.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Callback22[E] = MkCb22(() => Unit @ E)
  > type Cb22[E] = Callback22[E]
  > newtype N22 = MkN22(Cb22[{Print}])
  > newtype M22 = MkM22(A22[{}])
  > type A22[E] = (Int32) => Unit @ E
  > let f(n: N22, m: M22): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude ntalias.kel
  f : (N22, M22) => Int32

エイリアスの本体の中で、行のパラメータより右に、同じ型宣言のグループのエフェクトラベルがある場合である。
effect の名前はパス 1a で宣言表に登録するので、試行の中でもラベルを読める。
そのため、パラメータのカインドが決まる:

  $ cat > aliaslab.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > type Cb23[E] = (() => Unit @ E, () => Unit @ {Log})
  > newtype N23 = MkN23(Cb23[{}])
  > newtype M23 = MkM23(Cb23[{Log}])
  > let f(n: N23, m: M23): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude aliaslab.kel
  f : (N23, M23) => Int32

試行の中でも、ラベルとして読むのは、effect の宣言表に名前がある場合だけである。
effect でない型の名前(aliaslab2 の Q24)は、エイリアスの本体の位置で `エフェクトではありません` のエラーになる。
宣言のない名前(aliaslab3 の Nope)は、同じ位置で `未知のエフェクト` のエラーになる:

  $ cat > aliaslab2.kel <<'EOF'
  > type Unit = {}
  > newtype Q24 = MkQ24(Int32)
  > type C24 = A24[{}]
  > type A24[E] = (Int32) => Unit @ {Q24 extends E}
  > EOF
  $ diktor --type-check --no-prelude aliaslab2.kel
  ! aliaslab2.kel:4:33: 型エラー: 型 Q24 はエフェクトではありません(ここにはエフェクト行が要ります)
  [1]
  $ cat > aliaslab3.kel <<'EOF'
  > type Unit = {}
  > type C25 = A25[{}]
  > type A25[E] = (Int32) => Unit @ {Nope extends E}
  > EOF
  $ diktor --type-check --no-prelude aliaslab3.kel
  ! aliaslab3.kel:3:33: 型エラー: 未知のエフェクト: Nope
  [1]

module の中の newtype も同じように扱う(パス 1b の後の処理は、module を平坦化した後の修飾名で宣言を参照する):

  $ cat > modcb.kel <<'EOF'
  > module Cb {
  >   pub newtype Callback[E] = Callback(() => Unit @ E)
  >   pub let mk[E](f: () => Unit @ E): Callback[E] = Callback(f)
  > }
  > let g(c: Cb.Callback[{Print}]): Int32 = 0
  > EOF
  $ diktor --type-check modcb.kel
  Cb.mk : (() => {}) => Cb.Callback[R1] @ {}
  g : (Cb.Callback[{Print}]) => Int32

行カインドのパラメータを持つ型は、Functor のインスタンスにできない。
インスタンスの対象の型(診断では `インスタンス頭`)のカインドが EffectRow -> Type になり、クラスが要求する Type -> Type と合わないからである。
sample.kel §8 は、構造的導出を持つ Eq のカインドの規則を述べている(sample.kel:398-400)。
それに続けて、同じ規則の帰結として、このことを書いている(sample.kel:401-403):

  $ cat > nofunctor.kel <<'EOF'
  > type Unit = {}
  > newtype Callback[E] = Callback(() => Unit @ E)
  > type class Functor[F[_]] {
  >   val map[A, B, E]: (F[A], (A) => B @ E) => F[B] @ E
  > }
  > type instance Functor[Callback[_]] {
  >   let rec map(c, f) = c
  > }
  > EOF
  $ diktor --type-check --no-prelude nofunctor.kel
  ! nofunctor.kel:6:1: 型エラー: インスタンス頭 Callback のカインドがクラス Functor のパラメータと一致しません
  [1]

型クラスのパラメータは、EffectRow のカインドにできない(sample.kel §8、sample.kel:359-361)。
クラスパラメータのカインドは、宣言の束縛子の形で決まる。
[A] なら Type で、[F[_]] なら Type を取って Type を返すカインドである(穴は F[_, _] のように複数でもよい)。
パラメータを行として使うと、宣言の時点でエラーになる。
メソッドのシグネチャに直接書いた場合(classrow)も、行カインドのパラメータを持つ newtype に渡した場合(classrow2)も同じである:

  $ cat > classrow.kel <<'EOF'
  > type Unit = {}
  > type class C[E] {
  >   val m: (Int32) => Unit @ E
  > }
  > EOF
  $ diktor --type-check --no-prelude classrow.kel
  ! classrow.kel:3:28: 型エラー: 行カインドではない型パラメータです: E
  [1]
  $ cat > classrow2.kel <<'EOF'
  > type Unit = {}
  > newtype Callback[E] = Callback(() => Unit @ E)
  > type class C[E] {
  >   val m: (Callback[E]) => Unit
  > }
  > EOF
  $ diktor --type-check --no-prelude classrow2.kel
  ! classrow2.kel:4:20: 型エラー: 行カインドではない型パラメータです: E
  [1]

メソッドの型パラメータは、行カインドにできる。
エフェクトについて量化したいときは、クラスのパラメータではなく、メソッドの型パラメータとして行変数を取る(sample.kel:362-363)。
sample.kel §8 の Functor の map がその例である:

  $ cat > classrowok.kel <<'EOF'
  > type Unit = {}
  > type class Runner[A] {
  >   val run_[E]: (A, () => Unit @ E) => Unit @ E
  > }
  > type instance Runner[Int32] {
  >   let run_(x, f) = f()
  > }
  > EOF
  $ diktor --type-check --no-prelude classrowok.kel

型エイリアスのパラメータのカインドも、本体から推論してエイリアスの表に記録する。
そのため、newtype の別名にすぎないエイリアスにも、行変数と具体的な行のどちらも渡せる。
引数をすべて型として読むと、具体的な行は `エフェクトラベルはこの位置(レコード型)では使えません` のエラーになる。
パラメータのカインドが行なら、引数を行として読むので、このエラーにならない:

  $ cat > alias.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Callback[E] = Callback(() => Unit @ E)
  > type Cb[E] = Callback[E]
  > let f[E](c: Cb[E]): Cb[E] = c
  > let g(c: Cb[{Print}]): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude alias.kel
  f : (Callback[R1]) => Callback[R1]
  g : (Callback[{Print}]) => Int32

型引数の読み方は、宣言されたパラメータのカインドによって変わる(sample.kel §6、sample.kel:252-255)。
Row カインドのパラメータの位置ではエフェクト行として読むので、{} は空の行になる。
同じ位置では、波括弧のない Print は {Print} の略記になる。
Type カインドのパラメータの位置では、型として読む:

  $ cat > rowarg.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Callback[E] = Callback(() => Unit @ E)
  > newtype Box[A] = Box(A)
  > let a(): Callback[{}] = Callback(fn() => {})
  > let b(c: Callback[Print]): Callback[Print] = c
  > let d(x: Box[{}]): Box[{}] = x
  > let e(): Box[{}] = Box({})
  > EOF
  $ diktor --type-check --no-prelude rowarg.kel
  a : () => Callback[{}]
  b : (Callback[{Print}]) => Callback[{Print}]
  d : (Box[{}]) => Box[{}]
  e : () => Box[{}]

同じ {} が位置によって別の意味になるが、どちらも {} と表示されるので、表示からは区別できない。
Type の位置の {} が空のレコード型(= Unit)であることは、値を入れると確かめられる:

  $ printf 'type Unit = {}\nnewtype Box[A] = Box(A)\nlet bad(): Box[{}] = Box(1)\n' > rowarg2.kel
  $ diktor --type-check --no-prelude rowarg2.kel
  ! rowarg2.kel:3:5: 型エラー: 注釈された返り値型を満たしません({} は Integral のインスタンスではありません)
  [1]

エイリアスのパラメータのカインドの推論は、宣言順に依存しない。
パス 1b の後の処理が本体を試しに精緻化して推論し、エイリアスを使う箇所の検査より前に終えるからである。
エイリアスを使う宣言がエイリアスより前にあっても、エイリアスが newtype より前にあっても同じである:

  $ cat > aliasorder.kel <<'EOF'
  > let g(c: Cb[{Print}]): Int32 = 0
  > type Cb[E] = Callback[E]
  > newtype Callback[E] = Callback(() => Unit @ E)
  > EOF
  $ diktor --type-check aliasorder.kel
  g : (Callback[{Print}]) => Int32

エイリアスを通して newtype のパラメータのカインドが決まる場合である。
既定化は試行の後に行うので、X のカインドが先に Type に決まることはない:

  $ cat > aliasfwd.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype A6[X] = MkA6(Cb2[X])
  > type Cb2[E] = Callback2[E]
  > newtype Callback2[E] = Callback2(() => Unit @ E)
  > let f[E](x: A6[E]): A6[E] = x
  > let g(x: A6[{Print}]): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude aliasfwd.kel
  f : (A6[R1]) => A6[R1]
  g : (A6[{Print}]) => Int32

newtype のフィールドから、後ろで宣言するエイリアスを通して具体的な行を渡す場合である。
エイリアスの本体もパス 1b より前に試行するので、パス 1b が型引数を判別する時点で、エイリアスのパラメータのカインドは決まっている。
そのため、ラベルを書いた行(fwdalias)を行として読む。
要素のない波括弧(fwdalias2)も行として読む:

  $ cat > fwdalias.kel <<'EOF'
  > newtype H = MkH(Cb[{Print}])
  > type Cb[E] = Callback[E]
  > newtype Callback[E] = Callback(() => Unit @ E)
  > let fire(h: H): Unit @ Print = h match { case MkH(Callback(f)) => f() }
  > let h = MkH(Callback(fn() => println("hello")))
  > with_stdout(fn() => fire(h))
  > EOF
  $ diktor fwdalias.kel
  hello
  $ cat > fwdalias2.kel <<'EOF'
  > newtype J = MkJ(() => Unit @ Wr[{}])
  > type Wr[E]: EffectRow = {Print extends E}
  > let j = MkJ(fn() => println("wr"))
  > with_stdout(fn() => j match { case MkJ(f) => f() })
  > EOF
  $ diktor fwdalias2.kel
  wr

newtype の本体の試行がエイリアスを読んで、パラメータのカインドが決まる場合(fwdalias3)である。
エイリアスの本体が、後ろで宣言する newtype に具体的な行を渡す場合(fwdalias4)も確かめる。
どちらも、決まったカインドが増えなくなるまで試行を繰り返すので、型検査に通る:

  $ cat > fwdalias3.kel <<'EOF'
  > newtype A = MkA(B[{}])
  > newtype B[E] = MkB((() => Unit @ E, Th[{Print}]))
  > type Th[E] = () => Unit @ E
  > EOF
  $ diktor --type-check fwdalias3.kel
  $ cat > fwdalias4.kel <<'EOF'
  > newtype H = MkH(K[{}])
  > type K[E] = (() => Unit @ E, Callback[{Print}])
  > newtype Callback[E] = Callback(() => Unit @ E)
  > EOF
  $ diktor --type-check fwdalias4.kel

エイリアスが指す newtype の本体で、行のパラメータより右に、同じ型宣言のグループのエフェクトラベルがある場合である。
この場合も、エイリアスを間に挟んで型検査に通る:

  $ cat > fwdalias5.kel <<'EOF'
  > effect Log = { log: (String) => Unit }
  > newtype H = MkH(Cb[{}])
  > type Cb[E] = B[E]
  > newtype B[E] = MkB((() => Unit @ E, () => Unit @ {Log}))
  > EOF
  $ diktor --type-check fwdalias5.kel

行カインドのパラメータに型を渡すと、エイリアスの型引数として読んだ時点でエラーになる:

  $ printf 'type Unit = {}\nnewtype Callback[E] = Callback(() => Unit @ E)\ntype Cb[E] = Callback[E]\nlet f(c: Cb[Int32]): Int32 = 0\n' > aliaskind.kel
  $ diktor --type-check --no-prelude aliaskind.kel
  ! aliaskind.kel:4:13: 型エラー: 型 Int32 はエフェクトではありません(ここにはエフェクト行が要ります)
  [1]

パラメータを持つ EffectRow エイリアスは、行の要素の位置にも書ける。
引数の付いた要素は、エフェクトの表だけでなく、エイリアスの表からも探す。
エフェクトの表だけを調べる実装では、`未知のエフェクト: WithPrint` のエラーになる:

  $ cat > splice.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > effect Fs = {}
  > type WithPrint[E]: EffectRow = {Print extends E}
  > let f[E](x: Int32): Int32 @ {Fs, WithPrint[E]} = x
  > EOF
  $ diktor --type-check --no-prelude splice.kel
  f : (Int32) => Int32 @ {Fs, Print extends R1}

開いた行に展開されるエイリアスは、行の末尾以外にも書ける。
splice_row が、展開結果の行変数の手前に、残りの要素を挿入する。
展開の結果、行変数が 2 つになる行は型エラーである:

  $ cat > splice2.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > effect Fs = {}
  > type W[E]: EffectRow = {Print extends E}
  > type Both[E]: EffectRow = {W[E], Fs}
  > let f[E](x: Int32): Int32 @ {W[E], Fs} = x
  > let g[E](x: Int32): Int32 @ Both[E] = x
  > EOF
  $ diktor --type-check --no-prelude splice2.kel
  f : (Int32) => Int32 @ {Print, Fs extends R1}
  g : (Int32) => Int32 @ {Print, Fs extends R1}
  $ printf 'type Unit = {}\neffect Print = { print: (String) => Unit }\ntype W[E]: EffectRow = {Print extends E}\nlet f[E, E2](x: Int32): Int32 @ {W[E] extends E2} = x\n' > splice3.kel
  $ diktor --type-check --no-prelude splice3.kel
  ! splice3.kel:4:33: 型エラー: エイリアス W は開いた行に展開されるので、extends や別の開いた行と同じ行には置けません(行変数は 1 つまで)
  [1]
  $ printf 'type Unit = {}\neffect Print = { print: (String) => Unit }\ntype W[E]: EffectRow = {Print extends E}\nlet f[E](x: Int32): Int32 @ {W[E], W[E]} = x\n' > splice4.kel
  $ diktor --type-check --no-prelude splice4.kel
  ! splice4.kel:4:29: 型エラー: エイリアス W は開いた行に展開されるので、extends や別の開いた行と同じ行には置けません(行変数は 1 つまで)
  [1]

エフェクト行の位置に型の名前を書いたときは、`未知のエフェクト` ではなく `エフェクトではありません` と報告する。
Int32 は宣言されている名前で、未知ではないからである:

  $ cat > kinderr2.kel <<'EOF'
  > type Unit = {}
  > newtype Callback[E] = Callback(() => Unit @ E)
  > let f(c: Callback[Int32]): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude kinderr2.kel
  ! kinderr2.kel:3:19: 型エラー: 型 Int32 はエフェクトではありません(ここにはエフェクト行が要ります)
  [1]

宣言のない名前は `未知のエフェクト` と報告する:

  $ printf 'newtype Callback[E] = Callback(() => Unit @ E)\nlet f(c: Callback[{Nope}]): Int32 = 0\n' > nope.kel
  $ diktor --type-check nope.kel
  ! nope.kel:2:19: 型エラー: 未知のエフェクト: Nope
  [1]

高カインドの型変数への適用でも、定義域のカインドを照合する。
F[_] の定義域は Type なので、F[E] が E のカインドを Type に決め、次の @ E でエラーになる。
診断の位置が 2 番目に E を使う箇所になるのは、F[E] を読む時点では E のカインドが決まっておらず、照合に通るからである。
この照合によって、E を型と行の両方に使う f を拒否する:

  $ cat > hkt.kel <<'EOF'
  > type Unit = {}
  > let f[F[_], E](x: F[E], g: () => Unit @ E): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude hkt.kel
  ! hkt.kel:2:41: 型エラー: 行カインドではない型パラメータです: E
  [1]

行としての使用を先に書くと、E のカインドが先に Row に決まり、F[E] の位置でエラーになる:

  $ cat > hkt2.kel <<'EOF'
  > type Unit = {}
  > let f[F[_], E](g: () => Unit @ E, x: F[E]): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude hkt2.kel
  ! hkt2.kel:2:38: 型エラー: 型引数のカインドが一致しません: Type を期待しましたが ς1 は Row です
  [1]

高カインドのパラメータに Type カインドの引数を渡す通常の使い方は、型検査に通る:

  $ cat > hktok.kel <<'EOF'
  > let f[F[_], A](x: F[A]): F[A] = x
  > let g(xs: List[Int32]): List[Int32] = f(xs)
  > EOF
  $ diktor --type-check hktok.kel
  f : (F[A]) => F[A]
  g : (List[Int32]) => List[Int32]

値の型の位置では、読んだ型のカインドが Type でなければならない。
値の型の位置とは、矢印の引数と返り値、レコードのフィールド、タプルの要素、ヴァリアントのペイロード(診断では `積載`)である。
EffectRow エイリアスを書くと、その位置でエラーになる:

  $ cat > valkind.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let f(x: (P, Int32)): Int32 = 0
  > EOF
  $ diktor --type-check valkind.kel
  ! valkind.kel:2:11: 型エラー: タプルの要素の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind2.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let f(x: {a: P}): Int32 = 0
  > EOF
  $ diktor --type-check valkind2.kel
  ! valkind2.kel:2:14: 型エラー: レコードのフィールド a の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind3.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let f(g: (P) => Int32): Int32 = 0
  > EOF
  $ diktor --type-check valkind3.kel
  ! valkind3.kel:2:11: 型エラー: 矢印の引数の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind4.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let f(g: () => P @ {}): Int32 = 0
  > EOF
  $ diktor --type-check valkind4.kel
  ! valkind4.kel:2:16: 型エラー: 矢印の返り値の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind5.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let f(x: #T(P)): Int32 = 0
  > EOF
  $ diktor --type-check valkind5.kel
  ! valkind5.kel:2:13: 型エラー: ヴァリアント #T の積載の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind6.kel <<'EOF'
  > type P: EffectRow = {Print}
  > type class C2[A] { val m: (A) => P }
  > EOF
  $ diktor --type-check valkind6.kel
  ! valkind6.kel:2:34: 型エラー: 矢印の返り値の型のカインドが Type ではありません: {Print} :: Row
  [1]

ペイロードは、ヴァリアント型の中でも検査する。
上の valkind5 は #T(P) だけの型だが、値の型として読めるケース(#U)と並べても、行を書いたケースの位置でエラーになる:

  $ cat > sumkind.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let f(x: #U(Int32) | #T(P)): Int32 = 0
  > EOF
  $ diktor --type-check sumkind.kel
  ! sumkind.kel:2:25: 型エラー: ヴァリアント #T の積載の型のカインドが Type ではありません: {Print} :: Row
  [1]

型注釈の位置も、値の型の位置である。
診断は、内部名ではなく、注釈に書いた行とそのカインド({Print} :: Row)を示す:

  $ cat > annotkind.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let f(x: P): Int32 = 0
  > EOF
  $ diktor --type-check annotkind.kel
  ! annotkind.kel:2:10: 型エラー: 型注釈のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > annotkind2.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let f(): P = ???
  > EOF
  $ diktor --type-check annotkind2.kel
  ! annotkind2.kel:2:10: 型エラー: 返り値の型注釈のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > annotkind3.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let m: P = ???
  > EOF
  $ diktor --type-check annotkind3.kel
  ! annotkind3.kel:2:8: 型エラー: 型注釈のカインドが Type ではありません: {Print} :: Row
  [1]

上の annotkind2 は rec のない let だが、返り値の型注釈は、ほかの形の宣言でも同じように照合する。
次の 3 つは、extern、let rec、型クラスのインスタンスのメソッドの場合である。
どれも annotkind2 と同じメッセージのエラーになる:

  $ cat > extkind.kel <<'EOF'
  > type P: EffectRow = {Print}
  > extern "C" let nosuch(x: Float64): P
  > EOF
  $ diktor --type-check extkind.kel
  ! extkind.kel:2:36: 型エラー: 返り値の型注釈のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > reckind.kel <<'EOF'
  > type P: EffectRow = {Print}
  > let rec f(x: Int32): P = f(x)
  > EOF
  $ diktor --type-check reckind.kel
  ! reckind.kel:2:22: 型エラー: 返り値の型注釈のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > instkind.kel <<'EOF'
  > type P: EffectRow = {Print}
  > newtype Box = Box(Int32)
  > type class C[A] { val m: (A) => Int32 }
  > type instance C[Box] { let m(b): P = ??? }
  > EOF
  $ diktor --type-check instkind.kel
  ! instkind.kel:4:34: 型エラー: 返り値の型注釈のカインドが Type ではありません: {Print} :: Row
  [1]

同じパラメータを行と値の両方に使う宣言は、タプルやレコードで囲んであっても、宣言の時点でエラーになる。
エラーの位置は、そのパラメータを 2 番目に読む箇所である。
先に読んだ箇所がカインドを決め、後に読んだ箇所がそのカインドと合わないからである:

  $ cat > rowval.kel <<'EOF'
  > type Unit = {}
  > newtype Bad2[E] = Bad2((E, Int32), () => Unit @ E)
  > EOF
  $ diktor --type-check --no-prelude rowval.kel
  ! rowval.kel:2:49: 型エラー: 行カインドではない型パラメータです: E
  [1]
  $ cat > rowval2.kel <<'EOF'
  > type Unit = {}
  > newtype Bad3[E] = Bad3(() => Unit @ E, {a: E})
  > EOF
  $ diktor --type-check --no-prelude rowval2.kel
  ! rowval2.kel:2:44: 型エラー: レコードのフィールド a の型のカインドが Type ではありません: R1 :: Row
  [1]
  $ cat > rowval3.kel <<'EOF'
  > type Unit = {}
  > let f[E](x: (() => Unit @ E, E)): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude rowval3.kel
  ! rowval3.kel:2:27: 型エラー: 行カインドではない型パラメータです: E
  [1]

高カインドのパラメータを、引数を付けずに値の型の位置に書いた場合も、同じ照合でエラーになる。
タプルの要素として書いた場合も検査する:

  $ cat > hktval.kel <<'EOF'
  > type Unit = {}
  > newtype W[F[_]] = MkW((F, Int32))
  > EOF
  $ diktor --type-check --no-prelude hktval.kel
  ! hktval.kel:2:24: 型エラー: タプルの要素の型のカインドが Type ではありません: F :: [_] Type
  [1]

エフェクト位置に書けるのは、カインドが Row の型だけである。
エフェクト位置とは、@ の右と EffectRow エイリアスの本体である(sample.kel §9、sample.kel:469)。
この照合がないと、Type カインドの型の適用が行の末尾に入ったまま型検査に通る。
そのような型を持つ関数は、どこからも呼び出せない:

  $ printf 'let f(x: Int32): Int32 @ MutableArray[Int32, Int32] = x\n' > effkind.kel
  $ diktor --type-check effkind.kel
  ! effkind.kel:1:26: 型エラー: エフェクト位置の型のカインドが Row ではありません: MutableArray[Int32, Int32] :: Type
  [1]
  $ printf 'type Unit = {}\ntype Pair2[A] = (A, A)\nlet f(x: Int32): Int32 @ Pair2[Int32] = x\n' > effkind2.kel
  $ diktor --type-check --no-prelude effkind2.kel
  ! effkind2.kel:3:26: 型エラー: エフェクト位置の型のカインドが Row ではありません: (Int32, Int32) :: Type
  [1]

module で修飾した型名を @ の右に書いた場合(effkind3)も、同じ照合でエラーになる。
EffectRow エイリアスの本体に Type カインドの型を書いた場合(effkind4)も同じである:

  $ printf 'module M { pub type T = Int32 }\nlet f(x: Int32): Int32 @ M.T = x\n' > effkind3.kel
  $ diktor --type-check effkind3.kel
  ! effkind3.kel:2:26: 型エラー: エフェクト位置の型のカインドが Row ではありません: Int32 :: Type
  [1]
  $ printf 'type W: EffectRow = MutableArray[Int32, Int32]\nlet f(x: Int32): Int32 @ W = x\n' > effkind4.kel
  $ diktor --type-check effkind4.kel
  ! effkind4.kel:1:21: 型エラー: エフェクト位置の型のカインドが Row ではありません: MutableArray[Int32, Int32] :: Type
  [1]

結果のカインドが決まっていない型の適用も、エラーにする。
arity 0 の束縛子に引数を付けると、drop_arrows がその束縛子に矢印のカインドを割り当てる。
これを same_kind で照合すると、「Type を取って Row を返す」という言語にない型構成子を受理してしまうので、カインドの構造の一致で判定する。
カインドが決まっていないときだけ、診断から :: とカインドの表示を省く。
カインド変数の内部の連番が表示され、その番号がプレリュードの行数によって変わるからである:

  $ printf 'let f[F, E](x: Int32): Int32 @ F[E] = x\n' > effkind5.kel
  $ diktor --type-check effkind5.kel
  ! effkind5.kel:1:32: 型エラー: エフェクト位置の型のカインドが Row ではありません: ς1[ς2]
  [1]

行カインドのパラメータに渡す型引数も、同じ規則で照合する。
arity 0 の束縛子への適用 F[E] を Callback に渡すと、その宣言の位置でエラーになる。
この宣言を受理すると、f に閉じた行の Callback を渡した箇所で、内部名を含む単一化のエラーになるからである:

  $ cat > hktrow.kel <<'EOF'
  > newtype Callback[E] = Callback(() => Unit @ E)
  > let f[F, E](c: Callback[F[E]]): Int32 = 0
  > let g(c: Callback[{}]): Int32 = f(c)
  > EOF
  $ diktor --type-check hktrow.kel
  ! hktrow.kel:2:16: 型エラー: 型構成子 Callback の第1引数のカインドが一致しません: Row を期待しましたが ς1[ς2] は行になりません
  [1]

newtype の本体に書いた場合と、EffectRow エイリアスの型引数に書いた場合も同じである:

  $ cat > hktrow2.kel <<'EOF'
  > newtype Callback[E] = Callback(() => Unit @ E)
  > newtype Holder[F, E] = Holder(Callback[F[E]])
  > EOF
  $ diktor --type-check hktrow2.kel
  ! hktrow2.kel:2:31: 型エラー: 型構成子 Callback の第1引数のカインドが一致しません: Row を期待しましたが F[A] は行になりません
  [1]
  $ cat > hktrow3.kel <<'EOF'
  > type W[E]: EffectRow = {Print extends E}
  > let f[F, E](x: Int32): Int32 @ W[F[E]] = x
  > EOF
  $ diktor --type-check hktrow3.kel
  ! hktrow3.kel:2:32: 型エラー: 型エイリアス W の型引数のカインドが一致しません: Row を期待しましたが ς1[ς2] は行になりません
  [1]

レコードの行の extends の右と、ヴァリアント型の末尾(診断では `ヴァリアント和の末尾`)も、同じ規則で照合する。
ここで G のカインドが先に決まると、後ろの Callback[G[Int32]] の照合にも通ってしまう。
そのため、この 2 か所でも、宣言の位置でエラーにする:

  $ cat > hktrow6.kel <<'EOF'
  > newtype Callback[E] = Callback(() => Unit @ E)
  > let f[G](r: {x: Int32 extends G[Int32]}, c: Callback[G[Int32]]): Int32 = r.x
  > EOF
  $ diktor --type-check hktrow6.kel
  ! hktrow6.kel:2:13: 型エラー: extends の右の型のカインドが Row ではありません: ς1[Int32]
  [1]
  $ cat > hktrow7.kel <<'EOF'
  > let f[G](v: #A(Int32) | G[Int32]): Int32 = 0
  > EOF
  $ diktor --type-check hktrow7.kel
  ! hktrow7.kel:1:13: 型エラー: ヴァリアント和の末尾の型のカインドが Row ではありません: ς1[Int32]
  [1]

Type エイリアスの本体に書いた場合は、エイリアスの宣言でエラーになる。
パラメータのカインドの推論は、本体を読めないので、F のカインドを「Type を取って Type を返す」に決める。
そのため、メッセージは Type との不一致を報告する:

  $ cat > hktrow5.kel <<'EOF'
  > newtype Callback[E] = Callback(() => Unit @ E)
  > type Cb[F, E] = Callback[F[E]]
  > EOF
  $ diktor --type-check hktrow5.kel
  ! hktrow5.kel:2:17: 型エラー: 型構成子 Callback の第1引数のカインドが一致しません: Row を期待しましたが ς1[ς2] は Type です
  [1]

Callback を後ろで宣言すると、Holder の本体を読む時点では、Callback のパラメータのカインドが決まっていない。
そのため、F[E] を書いた位置ではエラーにできない。
この場合は、すべてのカインドが決まった後で検査する。
F を適用した結果のカインドが Row になっていれば、newtype の先頭の位置で報告する:

  $ cat > hktrow4.kel <<'EOF'
  > newtype Holder[F, E] = Holder(Callback[F[E]])
  > newtype Callback[E] = Callback(() => Unit @ E)
  > EOF
  $ diktor --type-check hktrow4.kel
  ! hktrow4.kel:1:1: 型エラー: newtype Holder の型パラメータ F への適用が行として使われています(行を返す型構成子はありません)
  [1]

渡す先のパラメータが、本体でレコードの行の extends の右に使われている場合である。
この場合も、newtype の先頭の位置で報告する:

  $ cat > hktrow8.kel <<'EOF'
  > newtype H[G] = MkH(Box[G[Int32]])
  > newtype Box[R] = MkBox({x: Int32 extends R})
  > EOF
  $ diktor --type-check hktrow8.kel
  ! hktrow8.kel:1:1: 型エラー: newtype H の型パラメータ G への適用が行として使われています(行を返す型構成子はありません)
  [1]

型エイリアスの本体から、後ろで宣言する newtype に渡す場合も、エイリアスの先頭の位置で報告する。
エイリアスの本体もパス 1b より前に試行するからである。
newtype の場合と同じく、渡す先のパラメータが、F を適用した結果のカインドを Row に決める:

  $ cat > hktrow9.kel <<'EOF'
  > type Cb[F, E] = Callback[F[E]]
  > newtype Callback[E] = Callback(() => Unit @ E)
  > EOF
  $ diktor --type-check hktrow9.kel
  ! hktrow9.kel:1:1: 型エラー: 型エイリアス Cb の型パラメータ F への適用が行として使われています(行を返す型構成子はありません)
  [1]

次の宣言はエラーにしない。
展開結果が型パラメータそのものになるエイリアス(Id と、恒等のエイリアスを重ねた Id2)は、行変数のカインドの推論によって Row に決まり、型検査に通る。
型変数の部分適用を Type -> Type のパラメータに渡す宣言(T[F[String]])も、型検査に通る:

  $ cat > hktrowok.kel <<'EOF'
  > type Id[A] = A
  > type Id2[A] = Id[A]
  > newtype Callback[E] = Callback(() => Unit @ E)
  > newtype N[X] = MkN(Callback[Id[X]])
  > let f(n: N[{Print}]): Int32 = 0
  > newtype N2[X] = MkN2(Callback[Id2[X]])
  > let f2(n: N2[{Print}]): Int32 = 0
  > newtype T[G] = MkT(G[Int32])
  > let g[F](x: T[F[String]], y: F[String, Int32]): Int32 = 0
  > EOF
  $ diktor --type-check hktrowok.kel
  f : (N[{Print}]) => Int32
  f2 : (N2[{Print}]) => Int32
  g : (T[F[String]], F[String, Int32]) => Int32

EffectRow エイリアスの適用は、エフェクト位置を読む関数 elab_eff の最後の分岐を通って行になるので、この分岐ではカインドの照合だけを行い、すべてをエラーにはしない。
module で修飾したエイリアスも、パラメータを持つエイリアスも同じである:

  $ cat > effok.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > module M { pub type W[E]: EffectRow = {Print extends E} }
  > let f[E](x: Int32): Int32 @ M.W[E] = x
  > EOF
  $ diktor --type-check --no-prelude effok.kel
  f : (Int32) => Int32 @ {Print extends R1}

型引数のカインドを判別する処理から呼ぶときだけ、この照合を行わない(~check_row:false)。
呼び出し元は型構成子の名前と引数の位置を示せるので、呼び出し元の診断を使う:

  $ printf 'newtype Callback[E] = Callback(() => Unit @ E)\nlet f(c: Callback[MutableArray[Int32, Int32]]): Int32 = 0\n' > nest2.kel
  $ diktor --type-check nest2.kel
  ! nest2.kel:2:10: 型エラー: 型構成子 Callback の第1引数のカインドが一致しません: Row を期待しましたが MutableArray[Int32, Int32] は Type です
  [1]

エフェクト位置に名前や型の適用を書いて、読んだ結果が行にならなかったときの診断は 3 通りあり、それぞれ別の事実を報告する。
修飾も型引数もない名前が型として登録されていなければ、`未知のエフェクト: Nope` と報告する(名前の書き間違い。上の nope)。
登録されていれば、`型 Int32 はエフェクトではありません` と報告する(書く位置の間違い。上の kinderr2)。
module で修飾した名前と型の適用は、読んだ結果のカインドを調べる。
行でなければ、`エフェクト位置の型のカインドが Row ではありません` と報告する。
3 つを 1 つのメッセージにまとめると、どれかの場合に事実と合わなくなる。
エフェクト位置でエラーになる診断は、この 3 つだけではない。
行カインドでない型パラメータと Type エイリアスは、名前を参照した時点で、手前の分岐が別のメッセージで先にエラーにする。
その例は、下の regionkind、上の classrow と classrow2、次の effkind6 である:

  $ printf 'type P = Int32\nlet f(x: Int32): Int32 @ P = x\n' > effkind6.kel
  $ diktor --type-check effkind6.kel
  ! effkind6.kel:2:26: 型エラー: エフェクト位置に Type エイリアス P は使えません(: EffectRow を付けてください)
  [1]

逆に、カインドの注釈のないエイリアス(と : Type を付けたエイリアス)の本体が行になる場合は、宣言の位置でエラーにする。
このエイリアスは、値の型の位置ではカインドの不一致でエラーになる。
エフェクト位置でも Type エイリアスとしてエラーになるので、どこにも書けない。
診断は、: EffectRow の注釈を付けるように案内する:

  $ cat > aliasrow.kel <<'EOF'
  > effect Log = { log: (String) => Unit }
  > type P: EffectRow = {Log}
  > type Q = P
  > EOF
  $ diktor --type-check aliasrow.kel
  ! aliasrow.kel:3:10: 型エラー: Type エイリアス Q の本体のカインドが Type ではありません: {Log} :: Row(行に名前を付けるには : EffectRow を付けてください)
  [1]
  $ printf 'effect Log = { log: (String) => Unit }\ntype P: EffectRow = {Log}\ntype Q: Type = P\n' > aliasrow2.kel
  $ diktor --type-check aliasrow2.kel
  ! aliasrow2.kel:3:16: 型エラー: Type エイリアス Q の本体のカインドが Type ではありません: {Log} :: Row(行に名前を付けるには : EffectRow を付けてください)
  [1]

パラメータを持つエイリアスも同じである。
この宣言を受理すると、@ Q[E] と、行を受け取る型引数の位置(Callback[Q[E]])では、展開後のカインドで照合するので使えてしまう。
しかし、Type エイリアスを行の位置に書いていることに変わりはないので、宣言の位置でエラーにする:

  $ cat > aliasrow3.kel <<'EOF'
  > effect Log = { log: (String) => Unit }
  > type P[E]: EffectRow = {Log extends E}
  > type Q[E] = P[E]
  > let f[E](x: Int32): Int32 @ Q[E] = x
  > EOF
  $ diktor --type-check aliasrow3.kel
  ! aliasrow3.kel:3:13: 型エラー: Type エイリアス Q の本体のカインドが Type ではありません: {Log extends ς1} :: Row(行に名前を付けるには : EffectRow を付けてください)
  [1]

import したファイルのエイリアスでも、診断はそのファイルの中での名前を示す:

  $ printf 'effect Log = { log: (String) => Unit }\npub type P[E]: EffectRow = {Log extends E}\npub type Q[E] = P[E]\npub type Id[A] = A\n' > aliasrowlib.kel
  $ printf 'from "./aliasrowlib" import { Id }\nlet x: Id[Int32] = 4\n' > aliasrowmain.kel
  $ diktor --type-check aliasrowmain.kel
  ! aliasrowlib.kel:3:17: 型エラー: Type エイリアス Q の本体のカインドが Type ではありません: {Log extends ς1} :: Row(行に名前を付けるには : EffectRow を付けてください)
  [1]

エラーにするのは、本体が行のときだけである。
高カインドのパラメータを引数なしで書いた本体は Type ではないが、別のエイリアスの引数(App[Q[F]])として使えるので、宣言を受理する:

  $ cat > aliasrow4.kel <<'EOF'
  > type Q[F[_]] = F
  > type App[G[_]] = G[Int32]
  > let get[F[_]](x: App[Q[F]], f: (F[Int32]) => Int32): Int32 = f(x)
  > echoln(show(get(Some(5), fn(o) => o match { case Some(n) => n case None => 0 })))
  > EOF
  $ diktor aliasrow4.kel
  5

この照合は、パス 2 で宣言順に行う。
aliasrow5 では、エイリアスより前の宣言が、パラメータのない Q を @ Q と書いている。
この使用は、それだけで Type エイリアスの誤用としてエラーになるので、使用箇所の診断が宣言の位置の診断より先に出る:

  $ cat > aliasrow5.kel <<'EOF'
  > effect Log = { log: (String) => Unit }
  > let f(x: Int32): Int32 @ Q = x
  > type P: EffectRow = {Log}
  > type Q = P
  > EOF
  $ diktor --type-check aliasrow5.kel
  ! aliasrow5.kel:2:26: 型エラー: エフェクト位置に Type エイリアス Q は使えません(: EffectRow を付けてください)
  [1]

elab_eff の最後の分岐に入る 3 つ目の経路は、{… extends <ty>} の右である(文法上、extends の右は eff ではなく ty である)。
この経路でカインドを照合するので、EBraceRow の分岐にある `extends の右は行でなければなりません` の検査には到達しない。
到達しない検査は、安全網として残してある:

  $ printf 'let f(x: Int32): Int32 @ {extends #Tag} = x\n' > effkind7.kel
  $ diktor --type-check effkind7.kel
  ! effkind7.kel:1:35: 型エラー: エフェクト位置の型のカインドが Row ではありません: #Tag :: Type
  [1]

run が導入するリージョン変数 h のカインドは Type である(sample.kel §10、sample.kel:670)。
そのため、行の位置(@ h)には書けない:

  $ cat > regionkind.kel <<'EOF'
  > let f(): Int32 = run h {
  >   let g: () => Int32 @ h = fn() => 1
  >   g()
  > }
  > EOF
  $ diktor --type-check regionkind.kel
  ! regionkind.kel:2:24: 型エラー: 行カインドではない型パラメータです: h
  [1]

h は、値の型の位置には書ける。
値の型の位置はカインド Type を要求するので、この宣言が型検査に通ることから、h のカインドが Type だと確かめられる。
h を型とする値を作る方法はないので、関数 g が呼ばれることはない:

  $ cat > regionkind2.kel <<'EOF'
  > let f(): Int32 = run h {
  >   let g: (h) => Int32 = fn(x) => 1
  >   0
  > }
  > EOF
  $ diktor --type-check regionkind2.kel
  f : () => Int32

h のカインドが Type なので、リージョンの位置にリージョンでない型を書いた型も拒否しない(LangSpec §14.1)。
Ref[Int32, Int32] と MutableArray[String, Int32] がその例である。
そのような型の値は作れない:

  $ cat > refkind.kel <<'KEL'
  > let f(r: Ref[Int32, Int32]): Int32 = 0
  > let g[A](r: Ref[A, Int32]): Int32 = 0
  > let h(r: MutableArray[String, Int32]): Int32 = 0
  > KEL
  $ diktor --type-check refkind.kel
  f : (Ref[Int32, Int32]) => Int32
  g : (Ref[h, Int32]) => Int32
  h : (MutableArray[String, Int32]) => Int32

@ Heap[Int32] と注釈した関数も型検査に通るが、どこからも呼び出せない。
run の本体から呼ぶと Heap の引数がリージョンでないというエラーになり、トップレベルから呼ぶと Heap のラベルがないというエラーになる:

  $ cat > refkind3.kel <<'KEL'
  > let f(): Int32 @ Heap[Int32] = 0
  > let g(): Int32 = run h { f() }
  > KEL
  $ diktor --type-check refkind3.kel
  f : () => Int32 @ {Heap[Int32]}
  ! refkind3.kel:2:26: 型エラー: Heap の引数 Int32 はリージョンではありません。Heap の引数には run のリージョン変数か型パラメータを書きます
  [1]
  $ cat > refkind4.kel <<'KEL'
  > let f(): Int32 @ Heap[Int32] = 0
  > let v = f()
  > KEL
  $ diktor --type-check refkind4.kel
  f : () => Int32 @ {Heap[Int32]}
  ! refkind4.kel:2:9: 型エラー: ラベル Heap がありません(行は閉じています)
  [1]

そのような型の値は作れない。
Ref.new が返す参照のリージョンは run の変数 h なので、Ref[Int32, Int32] という注釈とは一致しない:

  $ cat > refkind5.kel <<'KEL'
  > let v: Int32 = run h { let r: Ref[Int32, Int32] = Ref.new(0); 0 }
  > KEL
  $ diktor --type-check refkind5.kel
  ! refkind5.kel:1:28: 型エラー: 注釈された型を満たしません(Ref の第 1 引数 Int32 はリージョンではありません。Ref の第 1 引数には run のリージョン変数か型パラメータを書きます)
  [1]

MutableArray の第 1 引数も、同じメッセージで報告する:

  $ cat > refkind6.kel <<'KEL'
  > let v: Int32 = run h { let a: MutableArray[String, Int32] = MutableArray.new(3, 0); 0 }
  > KEL
  $ diktor --type-check refkind6.kel
  ! refkind6.kel:1:28: 型エラー: 注釈された型を満たしません(MutableArray の第 1 引数 String はリージョンではありません。MutableArray の第 1 引数には run のリージョン変数か型パラメータを書きます)
  [1]

run を通さずに Heap どうしが一致しない場合も、リージョンでない型を示して報告する。
次の例は、@ Heap[String] の関数から @ Heap[Int32] の関数を呼ぶ。
診断は、2 つの型のうち Int32 を示す:

  $ cat > refkind7.kel <<'KEL'
  > let f(): Int32 @ Heap[Int32] = 0
  > let g(): Int32 @ Heap[String] = f()
  > KEL
  $ diktor --type-check refkind7.kel
  f : () => Int32 @ {Heap[Int32]}
  ! refkind7.kel:2:33: 型エラー: Heap の引数 Int32 はリージョンではありません。Heap の引数には run のリージョン変数か型パラメータを書きます
  [1]

関数の型の注釈の中の Heap[h] と一致させる場合も同じである:

  $ cat > refkind8.kel <<'KEL'
  > let f(): Int32 @ Heap[Int32] = 0
  > let g(): Int32 = run h { let k: () => Int32 @ Heap[h] = f; k() }
  > KEL
  $ diktor --type-check refkind8.kel
  f : () => Int32 @ {Heap[Int32]}
  ! refkind8.kel:2:30: 型エラー: 注釈された型を満たしません(Heap の引数 Int32 はリージョンではありません。Heap の引数には run のリージョン変数か型パラメータを書きます)
  [1]

Heap の引数がどちらもスコーレム定数(型パラメータを固定した定数)のときは、ほかのリージョンのヒープを使おうとしたものとして報告する。
次の例は、型パラメータ A のヒープを使う関数を、run h の本体で呼ぶ。
A と h は別のスコーレム定数なので、一致しない:

  $ cat > refkind9.kel <<'KEL'
  > let f[A](g: () => Int32 @ Heap[A]): Int32 = run h { g() }
  > KEL
  $ diktor --type-check refkind9.kel
  ! refkind9.kel:1:53: 型エラー: ほかのリージョンのヒープを使おうとしています(スコープ付きの型が一致しません: ς1 と ς2)
  [1]
