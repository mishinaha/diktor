M23 / ワークストリーム C(newtype の型パラメータのカインド推論)と M28(C5〜C7:
型エイリアスのカインド、行 splice、HKT の定義域)のゴールデン。
変更時は dune promote で更新し、必ず目視レビューすること。

仕様 §6「型パラメータのカインドは宣言群の中の型の本体での使われ方から推論し、
使われ方が無ければ Type」(sample.kel:235)「型引数の位置は、そのパラメータの
カインドで読み方が変わる」(sample.kel:238)と、§9 の
`newtype Callback[E] = Callback(() => Unit @ E)`(sample.kel:486)。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

行カインドのパラメータを持つ newtype が宣言でき、行変数でも具体的な行でも
型引数に書ける(D80 / D82):

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
  println : (String) => {} @ {Print extends R1}
  pure_cb : () => Callback[{}]
  print_cb : () => Callback[{Print}]

行変数を含む行も書ける。pub でも完全注釈になる(仕様 §13):

  $ cat > cbext.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > pub newtype Callback[E] = Callback(() => Unit @ E)
  > pub let mk[E](f: () => Unit @ E): Callback[E] = Callback(f)
  > pub let open_[E](c: Callback[E]): () => Unit @ E = c match { case Callback(f) => f }
  > let with_ext[E](c: Callback[{Print extends E}]): Callback[{Print extends E}] = c
  > EOF
  $ diktor --type-check cbext.kel
  mk : (() => {}) => Callback[R1]
  open_ : (Callback[R1]) => () => {}
  with_ext : (Callback[{Print extends R1}]) => Callback[{Print extends R1}]

実行も通る(構築・分解・handle 越しの呼び出し):

  $ cat > cbrun.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
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

使われ方の無いパラメータは Type に既定化される(D7 の一般化。D81):

  $ cat > phantom.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Phantom[E] = Phantom(Int32)
  > let ok(): Phantom[Int32] = Phantom(0)
  > EOF
  $ diktor --type-check --no-prelude phantom.kel
  ok : () => Phantom[Int32]

カインドを決める「使われ方」は自分の宣言の本体に限らない(D129)。宣言群の中の
型の本体が材料になるので、自分の本体では Int32 しか使っていないパラメータでも、
他の宣言の本体が同じパラメータを行カインドの位置へ流し込めば行カインドになる
(ここでは N の本体が Ph[X] と Callback[X] を並べる):

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

同じ形から、行として使う側(上の N と Callback)を消すと Type に既定化され、
型引数の {Print} は型として読まれる:

  $ cat > phantomtype.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype Ph2[E] = MkPh2(Int32)
  > let f(x: Ph2[{Print}]): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude phantomtype.kel
  ! phantomtype.kel:4:14: 型エラー: エフェクトラベルはこの位置(レコード型)では使えません
  [1]

表現を隠した newtype(= ???)でもパラメータは登録され既定化される:

  $ printf 'newtype X[A] = ???\nlet f[A](x: X[A]): X[A] = x\n' > hole.kel
  $ diktor --type-check --no-prelude hole.kel
  f : (X[A]) => X[A]

Type のパラメータに行を渡すと宣言の時点で落ちる(かつては構築点まで
「カインドが一致しません」が出なかった。D82):

  $ cat > kinderr.kel <<'EOF'
  > type Unit = {}
  > newtype Box[A] = Box(A)
  > let f[E](g: () => Unit @ E): Box[E] = ???
  > EOF
  $ diktor --type-check --no-prelude kinderr.kel
  ! kinderr.kel:3:30: 型エラー: 型構成子 Box の第1引数のカインドが一致しません: Type を期待しましたが ς1 は Row です
  [1]

入れ子の取り違え(Row の位置に Type):

  $ printf 'newtype Callback[E] = Callback(() => Unit @ E)\nlet f[E](c: Callback[Callback[E]]): Int32 = 0\n' > nest.kel
  $ diktor --type-check nest.kel
  ! nest.kel:2:13: 型エラー: 型構成子 Callback の第1引数のカインドが一致しません: Row を期待しましたが Callback[ς1] は Type です
  [1]

コンストラクタのフィールドの型は必ずカインド Type(D83)。
同じパラメータを行と型の両方で使う宣言はここで落ちる:

  $ cat > fieldkind.kel <<'EOF'
  > type Unit = {}
  > newtype Bad[E] = Bad(() => Unit @ E, E)
  > EOF
  $ diktor --type-check --no-prelude fieldkind.kel
  ! fieldkind.kel:2:38: 型エラー: コンストラクタ Bad のフィールドの型のカインドが Type ではありません: R1 :: Row
  [1]

EffectRow エイリアスをフィールドに書いた形も宣言の時点で落ちる(かつては
構築点で内部名の診断だった):

  $ printf 'effect Print = { print: (String) => Unit }\ntype P: EffectRow = {Print}\nnewtype X = X(P)\nlet f(): X = X(???)\n' > fieldalias.kel
  $ diktor --type-check fieldalias.kel
  ! fieldalias.kel:3:15: 型エラー: コンストラクタ X のフィールドの型のカインドが Type ではありません: {Print} :: Row
  [1]

相互再帰する newtype でも、宣言順のどちらでもカインドが伝わる(D81。
宣言ごとに既定化すると先に処理した側が相手のカインドまで固定する。
これは行変数を渡す形。具体的な行を渡す形は下の fwdrow):

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

行カインドのパラメータへ具体的な行を前方参照つきで渡す形も、相手の本体の投機が
そのパラメータのカインドに届く限り宣言順に依存しない(D132。1b の前に newtype の
本体を投機的に読んでカインドだけ決めるので、読み分けが {…} を行として読める。
かつては B4 を先に置かないと落ちた。届かない形は下の speclab):

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

連鎖と module の中でも同じ(投機は宣言順に 1 周するだけだが、深さ 2 は届く):

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
  > effect Print = { print: (String) => Unit }
  > module M {
  >   pub newtype A6[X] = MkA6(B6[{Print extends X}])
  >   pub newtype B6[E] = MkB6(() => Unit @ E)
  > }
  > let f[E](x: M.A6[E]): M.A6[E] = x
  > EOF
  $ diktor --type-check fwdrowmod.kel
  f : (M.A6[R1]) => M.A6[R1]

module の中の深さ 2 の連鎖も通る。投機のループを with_decl_module で包んでいるか
を見張るのはこの形で、上の fwdrowmod は B6 の投機だけで通るため包みを外しても
緑のまま(M29 の検証で実測。C9[Y] が module の内部型を非修飾で参照する):

  $ cat > fwdrowmod2.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > module M {
  >   pub newtype A9[X] = MkA9(B9[{Print extends X}])
  >   pub newtype B9[Y] = MkB9(C9[Y])
  >   pub newtype C9[E] = MkC9(() => Unit @ E)
  > }
  > let f[E](x: M.A9[E]): M.A9[E] = x
  > EOF
  $ diktor --type-check fwdrowmod2.kel
  f : (M.A9[R1]) => M.A9[R1]

投機は effect の操作の登録(1b)より前に走るので、同じ宣言群のエフェクトラベルは
投機の時点ではすべて未知で、() => Unit @ {Log} のようなフィールドは投機の中で
落ちる。例外をフィールドごとに握り潰すので、手前のフィールドが落ちても後続の
フィールドがパラメータのカインドを決める(M29 の検証。コンストラクタが 2 つに
分かれていても同じ):

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

1 つのフィールドの中で投機が先にラベルへ当たる形では、そのフィールドは丸ごと
落ちる(タプルやレコードの要素は右から読むので、右端の {Log} で落ちて左の E に
届かない)。それでも通るのは、投機の間だけ、カインドが未確定のパラメータへ渡した
要素なしの波括弧 — {} と {extends X} — を読まずに飛ばすからで、1b が相手の
カインドの決まった状態でもう一度読む:

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

前方参照でも同じで、相手の手前のフィールドが投機で落ちても、後続のフィールドから
連鎖でカインドが決まれば通る(B14 の第 1 フィールドは投機で落ちるが、第 2 の
C14[Y] が Y を C14 のパラメータのセルに張り、C14 の投機がそれを行にする):

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

前方参照の型引数が {}(空の波括弧)の形も、飛ばす読みで通る(台帳 V22 の主たる
形)。残るのは、相手の投機がそのパラメータのカインドを決められず、かつ型引数が
要素なしの波括弧のときだけ — このとき {} は空レコードとして読めてしまい、
照合が相手のパラメータを Type に張る(台帳 V22 の残り):

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
  > EOF
  $ diktor --type-check --no-prelude specunit2.kel
  ! specunit2.kel:4:38: 型エラー: 行カインドではない型パラメータです: E
  [1]

投機がパラメータに届かない形では、型引数にラベルを書いても宣言順に依存する。
同じ 2 つの宣言を入れ替えれば通るので、効いているのは型引数の字面ではなく、
投機が相手のパラメータのカインドを決められたかどうかである:

  $ cat > speclab.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype A17[X] = MkA17(B17[{Log extends X}])
  > newtype B17[E] = MkB17((() => Unit @ E, () => Unit @ {Log}))
  > let f[E](x: A17[E]): A17[E] = x
  > EOF
  $ diktor --type-check --no-prelude speclab.kel
  ! speclab.kel:3:28: 型エラー: エフェクトラベルはこの位置(レコード型)では使えません
  [1]
  $ cat > speclab2.kel <<'EOF'
  > type Unit = {}
  > effect Log = { log: (String) => Unit }
  > newtype B18[E] = MkB18((() => Unit @ E, () => Unit @ {Log}))
  > newtype A18[X] = MkA18(B18[{Log extends X}])
  > let f[E](x: A18[E]): A18[E] = x
  > EOF
  $ diktor --type-check --no-prelude speclab2.kel
  f : (A18[R1]) => A18[R1]

module の中の newtype も同じ経路(1b の後始末は平坦化後の修飾名で引く):

  $ cat > modcb.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > module Cb {
  >   pub newtype Callback[E] = Callback(() => Unit @ E)
  >   pub let mk[E](f: () => Unit @ E): Callback[E] = Callback(f)
  > }
  > let g(c: Cb.Callback[{Print}]): Int32 = 0
  > EOF
  $ diktor --type-check modcb.kel
  Cb.mk : (() => {}) => Cb.Callback[R1]
  g : (Cb.Callback[{Print}]) => Int32

プレリュード所有名の再宣言はプレリュードが決めたカインドを引き継ぐ(D80。
別のセルを作ると構造照合で KVar と KStar が食い違う):

  $ printf 'type Unit = {}\nnewtype Callback[E] = Callback(() => Unit @ E)\n' > tinypre.kel
  $ printf 'newtype Callback[E] = Callback(() => Unit @ E)\nlet f[E](c: Callback[E]): Callback[E] = c\n' > redecl.kel
  $ diktor --prelude tinypre.kel --type-check redecl.kel
  f : (Callback[R1]) => Callback[R1]
  $ printf 'newtype Callback[E] = Callback(E)\n' > redecl2.kel
  $ diktor --prelude tinypre.kel --type-check redecl2.kel
  ! redecl2.kel:1:32: 型エラー: コンストラクタ Callback のフィールドの型のカインドが Type ではありません: R1 :: Row
  [1]

行カインドのパラメータを持つ型は Functor のインスタンスにできない(D126)。
頭のカインドが EffectRow -> Type になり、クラスが要求する Type -> Type と
合わないためで、仕様 §8 が derive structural の制限(sample.kel:381-383)と
並べて帰結として書いている(sample.kel:384-386):

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

型クラスのパラメータに EffectRow のカインドは取れない(D125。仕様 §8、
sample.kel:344-345。カインドは束縛子の形で宣言時に決まり、[A] なら Type、
[F[_]] なら Type を取って Type を返す形になる — 穴は F[_, _] と複数でもよい)。
行として使うと、メソッドの署名に直接書いても、行カインドのパラメータを
持つ newtype に渡しても、宣言の時点で落ちる:

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

メソッドの型パラメータのほうは行カインドになれる。エフェクトで量化したいときは、
クラスのパラメータではなくこちらに行変数を取る(sample.kel:346。仕様 §8 の
Functor の map が見本):

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

型エイリアスのパラメータのカインドも本体から推論して表に残す(D84)。
newtype を透過に包むエイリアスに、行変数でも具体的な行でも渡せる(かつては
引数を全部型として読んだので、具体的な行は「エフェクトラベルはこの位置
(レコード型)では使えません」で落ちた):

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

型引数の位置は、宣言されたパラメータのカインドで読み方が変わる(D82。仕様 §6、
sample.kel:238-241)。Row のパラメータの位置ではエフェクト行として読むので、{} は
空行に、裸の Print は {Print} の略記になる。Type のパラメータの位置では型として
読む:

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

同じ {} が位置で別の意味になるが、印字はどちらも {} で見分けが付かない。Type の
位置の {} が空レコード(= Unit)であることは、値を入れると見える:

  $ printf 'type Unit = {}\nnewtype Box[A] = Box(A)\nlet bad(): Box[{}] = Box(1)\n' > rowarg2.kel
  $ diktor --type-check --no-prelude rowarg2.kel
  ! rowarg2.kel:3:5: 型エラー: 注釈された返り値型を満たしません({} は Integral のインスタンスではありません)
  [1]

エイリアスのパラメータのカインドの推論は宣言順に依存しない(1b の後始末の
投機的な精緻化で、使用点より前に済む。使用がエイリアスより前でも、
エイリアスが newtype より前でも同じ):

  $ cat > aliasorder.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > let g(c: Cb[{Print}]): Int32 = 0
  > type Cb[E] = Callback[E]
  > newtype Callback[E] = Callback(() => Unit @ E)
  > EOF
  $ diktor --type-check aliasorder.kel
  g : (Callback[{Print}]) => Int32

エイリアス経由で newtype のパラメータのカインドが決まる形。既定化を投機より
後に置いたので、X が先に Type に固定されない(D81 / D84):

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

行カインドのパラメータに型を渡すと、エイリアスの側の診断で落ちる:

  $ printf 'type Unit = {}\nnewtype Callback[E] = Callback(() => Unit @ E)\ntype Cb[E] = Callback[E]\nlet f(c: Cb[Int32]): Int32 = 0\n' > aliaskind.kel
  $ diktor --type-check --no-prelude aliaskind.kel
  ! aliaskind.kel:4:13: 型エラー: 型 Int32 はエフェクトではありません(ここにはエフェクト行が要ります)
  [1]

パラメータつき EffectRow エイリアスは行 splice の位置にも置ける(D85。M17 の
「記録のみ」の 1 件。かつては引数つきの要素がエフェクト表しか見ず「未知の
エフェクト: WithPrint」で落ちた):

  $ cat > splice.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > effect Fs = {}
  > type WithPrint[E]: EffectRow = {Print extends E}
  > let f[E](x: Int32): Int32 @ {Fs, WithPrint[E]} = x
  > EOF
  $ diktor --type-check --no-prelude splice.kel
  f : (Int32) => Int32 @ {Fs, Print extends R1}

開いた行に展開されるエイリアスは末尾以外にも置ける。splice_row が展開結果の
行変数の手前に残りの要素を差し込む(かつては row_append の左が開いた行になり
[BUG] で落ちた — M28 の検証)。行変数が 2 つになる形は型エラー:

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

エフェクト行の位置に型の名前を書いたときは「未知」ではなく「エフェクトでは
ない」と言う(D85。Int32 は未知ではない):

  $ cat > kinderr2.kel <<'EOF'
  > type Unit = {}
  > newtype Callback[E] = Callback(() => Unit @ E)
  > let f(c: Callback[Int32]): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude kinderr2.kel
  ! kinderr2.kel:3:19: 型エラー: 型 Int32 はエフェクトではありません(ここにはエフェクト行が要ります)
  [1]

本当に未知の名前は従来どおり:

  $ printf 'newtype Callback[E] = Callback(() => Unit @ E)\nlet f(c: Callback[{Nope}]): Int32 = 0\n' > nope.kel
  $ diktor --type-check nope.kel
  ! nope.kel:2:19: 型エラー: 未知のエフェクト: Nope
  [1]

行カインドになったパラメータに型クラスの制約は書けない(M28。260829-5 の M17
「記録のみ」の 2 件目。かつてエイリアスでは全使用点で落ち、newtype では構築点が
行を見ないので黙って素通りした):

  $ printf 'type R[E: Show]: EffectRow = {Console extends E}\n' > rowconstr.kel
  $ diktor --type-check rowconstr.kel
  ! rowconstr.kel:1:1: 型エラー: 型パラメータ E は行カインドなので、型クラス Show の制約は書けません(型クラスは Type のクラス)
  [1]
  $ printf 'newtype N[E: Show] = N(() => Unit @ E)\n' > rowconstr2.kel
  $ diktor --type-check rowconstr2.kel
  ! rowconstr2.kel:1:1: 型エラー: 型パラメータ E は行カインドなので、型クラス Show の制約は書けません(型クラスは Type のクラス)
  [1]

Type のパラメータの制約は従来どおり言及時に効く(規則 3):

  $ printf 'type P[A: Show] = (A, A)\nlet f(x: P[Int32]): Int32 = 0\n' > tyconstr.kel
  $ diktor --type-check tyconstr.kel
  f : ((Int32, Int32)) => Int32

高階カインドの型変数への適用も定義域を照合する(D86)。F[_] の定義域は Type
なので F[E] が E を Type に確定させ、次の @ E で落ちる。診断の位置が 2 番目の
使用点になるのは、F[E] の時点では E のカインドが未定で照合が通るため(かつては
何も起きず (F[R1], () => {}) => Int32 と型付いた):

  $ cat > hkt.kel <<'EOF'
  > type Unit = {}
  > let f[F[_], E](x: F[E], g: () => Unit @ E): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude hkt.kel
  ! hkt.kel:2:41: 型エラー: 行カインドではない型パラメータです: E
  [1]

行を先に確定させた形は F[E] の側で落ちる:

  $ cat > hkt2.kel <<'EOF'
  > type Unit = {}
  > let f[F[_], E](g: () => Unit @ E, x: F[E]): Int32 = 0
  > EOF
  $ diktor --type-check --no-prelude hkt2.kel
  ! hkt2.kel:2:38: 型エラー: 型引数のカインドが一致しません: Type を期待しましたが ς1 は Row です
  [1]

Functor の正常系は変わらない:

  $ cat > hktok.kel <<'EOF'
  > let f[F[_], A](x: F[A]): F[A] = x
  > let g(xs: List[Int32]): List[Int32] = f(xs)
  > EOF
  $ diktor --type-check hktok.kel
  f : (F[A]) => F[A]
  g : (List[Int32]) => List[Int32]

値の型の位置(矢印の引数と返り値、レコードのフィールド、タプルの要素、
ヴァリアントの積載)は、読んだ型のカインドが Type でなければならない
(D131。台帳 V20)。EffectRow エイリアスを書くとその位置で落ちる:

  $ cat > valkind.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let f(x: (P, Int32)): Int32 = 0
  > EOF
  $ diktor --type-check valkind.kel
  ! valkind.kel:3:11: 型エラー: タプルの要素の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind2.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let f(x: {a: P}): Int32 = 0
  > EOF
  $ diktor --type-check valkind2.kel
  ! valkind2.kel:3:14: 型エラー: レコードのフィールド a の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind3.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let f(g: (P) => Int32): Int32 = 0
  > EOF
  $ diktor --type-check valkind3.kel
  ! valkind3.kel:3:11: 型エラー: 矢印の引数の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind4.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let f(g: () => P @ {}): Int32 = 0
  > EOF
  $ diktor --type-check valkind4.kel
  ! valkind4.kel:3:16: 型エラー: 矢印の返り値の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind5.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let f(x: #T(P)): Int32 = 0
  > EOF
  $ diktor --type-check valkind5.kel
  ! valkind5.kel:3:13: 型エラー: ヴァリアント #T の積載の型のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > valkind6.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > type class C2[A] { val m: (A) => P }
  > EOF
  $ diktor --type-check valkind6.kel
  ! valkind6.kel:3:34: 型エラー: 矢印の返り値の型のカインドが Type ではありません: {Print} :: Row
  [1]

積載は和の中でも読む。上の valkind5 は単独の #T(P) だが、値の型として
読める枝(#U)と並べても、行を書いた枝の位置で落ちる:

  $ cat > sumkind.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let f(x: #U(Int32) | #T(P)): Int32 = 0
  > EOF
  $ diktor --type-check sumkind.kel
  ! sumkind.kel:3:25: 型エラー: ヴァリアント #T の積載の型のカインドが Type ではありません: {Print} :: Row
  [1]

注釈の位置も値の型の位置(D131)。かつては束縛の単一化まで生き延びて
内部名の「カインドが一致しません: _A :: Type と {Print}」だった:

  $ cat > annotkind.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let f(x: P): Int32 = 0
  > EOF
  $ diktor --type-check annotkind.kel
  ! annotkind.kel:3:10: 型エラー: 型注釈のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > annotkind2.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let f(): P = ???
  > EOF
  $ diktor --type-check annotkind2.kel
  ! annotkind2.kel:3:10: 型エラー: 返り値の型注釈のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > annotkind3.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let m: P = ???
  > EOF
  $ diktor --type-check annotkind3.kel
  ! annotkind3.kel:3:8: 型エラー: 型注釈のカインドが Type ではありません: {Print} :: Row
  [1]

上の annotkind2 は素の let だが、返り値の注釈は他の宣言の形でも同じ照合を
受ける。extern・let rec・型クラスのインスタンスのメソッドの 3 つとも、
annotkind2 と同じ文言で落ちる(D131):

  $ cat > extkind.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > extern "C" let nosuch(x: Float64): P
  > EOF
  $ diktor --type-check extkind.kel
  ! extkind.kel:3:36: 型エラー: 返り値の型注釈のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > reckind.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > let rec f(x: Int32): P = f(x)
  > EOF
  $ diktor --type-check reckind.kel
  ! reckind.kel:3:22: 型エラー: 返り値の型注釈のカインドが Type ではありません: {Print} :: Row
  [1]
  $ cat > instkind.kel <<'EOF'
  > effect Print = { print: (String) => Unit }
  > type P: EffectRow = {Print}
  > newtype Box = Box(Int32)
  > type class C[A] { val m: (A) => Int32 }
  > type instance C[Box] { let m(b): P = ??? }
  > EOF
  $ diktor --type-check instkind.kel
  ! instkind.kel:5:34: 型エラー: 返り値の型注釈のカインドが Type ではありません: {Print} :: Row
  [1]

同じパラメータを行と値の両方で使う宣言は、包んであっても宣言の時点で
落ちる(台帳 V17)。落ちる位置は先に読んだ側がカインドを決めたあとの
二番目の使用点になる:

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

高階カインドのパラメータを裸で値の型の位置に書いた形も同じ照合が落とす
(D131。かつてはタプルに包むと素通りしていた):

  $ cat > hktval.kel <<'EOF'
  > type Unit = {}
  > newtype W[F[_]] = MkW((F, Int32))
  > EOF
  $ diktor --type-check --no-prelude hktval.kel
  ! hktval.kel:2:24: 型エラー: タプルの要素の型のカインドが Type ではありません: F :: [_] Type
  [1]

エフェクト位置(@ の右と EffectRow エイリアスの本体)に書けるのは、カインドが
Row の型だけ(D127。台帳 V19。仕様 §9「@ の右はエフェクト行」— sample.kel:447)。
かつては elab_eff の最後の枝が elab_type に落ちるだけで、Type カインドの適用型が
行の尾部に入った — 型検査は通り、その関数は誰からも呼べなくなっていた:

  $ printf 'let f(x: Int32): Int32 @ MutableArray[Int32, Int32] = x\n' > effkind.kel
  $ diktor --type-check effkind.kel
  ! effkind.kel:1:26: 型エラー: エフェクト位置の型のカインドが Row ではありません: MutableArray[Int32, Int32] :: Type
  [1]
  $ printf 'type Unit = {}\ntype Pair2[A] = (A, A)\nlet f(x: Int32): Int32 @ Pair2[Int32] = x\n' > effkind2.kel
  $ diktor --type-check --no-prelude effkind2.kel
  ! effkind2.kel:3:26: 型エラー: エフェクト位置の型のカインドが Row ではありません: (Int32, Int32) :: Type
  [1]

module 修飾の型名と EffectRow エイリアスの本体も同じ枝を通る(台帳 V19 が
書いていなかった 2 つ目と 3 つ目の穴):

  $ printf 'module M { pub type T = Int32 }\nlet f(x: Int32): Int32 @ M.T = x\n' > effkind3.kel
  $ diktor --type-check effkind3.kel
  ! effkind3.kel:2:26: 型エラー: エフェクト位置の型のカインドが Row ではありません: Int32 :: Type
  [1]
  $ printf 'type W: EffectRow = MutableArray[Int32, Int32]\nlet f(x: Int32): Int32 @ W = x\n' > effkind4.kel
  $ diktor --type-check effkind4.kel
  ! effkind4.kel:1:21: 型エラー: エフェクト位置の型のカインドが Row ではありません: MutableArray[Int32, Int32] :: Type
  [1]

結果のカインドが未確定な適用も落とす。arity 0 の束縛子に引数を付けると
drop_arrows がカインドを張るので、same_kind で照合すると「Type を取って Row を
返す」という言語に無い構成子を受理してしまう。判定は構造マッチで、カインドが
未確定のときだけ :: の併記を落とす(内部の連番が漏れ、プレリュードの行数で
番号が動くため):

  $ printf 'let f[F, E](x: Int32): Int32 @ F[E] = x\n' > effkind5.kel
  $ diktor --type-check effkind5.kel
  ! effkind5.kel:1:32: 型エラー: エフェクト位置の型のカインドが Row ではありません: ς1[ς2]
  [1]

EffectRow エイリアスの適用はこの枝を通って正しく行になる(枝ごと落とさずに
照合だけを足した理由。module 修飾でもパラメータつきでも同じ):

  $ cat > effok.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > module M { pub type W[E]: EffectRow = {Print extends E} }
  > let f[E](x: Int32): Int32 @ M.W[E] = x
  > EOF
  $ diktor --type-check --no-prelude effok.kel
  f : (Int32) => Int32 @ {Print extends R1}

D82 の型引数の読み分けから呼ぶときだけ照合を抑制する(~check_row:false)。
呼び出し側は構成子名と引数の位置を添えられるので、そちらの診断を残す:

  $ printf 'newtype Callback[E] = Callback(() => Unit @ E)\nlet f(c: Callback[MutableArray[Int32, Int32]]): Int32 = 0\n' > nest2.kel
  $ diktor --type-check nest2.kel
  ! nest2.kel:2:10: 型エラー: 型構成子 Callback の第1引数のカインドが一致しません: Row を期待しましたが MutableArray[Int32, Int32] は Type です
  [1]

エフェクト位置に名前や適用形を書いて、読んだ結果が行にならなかったときの言い分けは
3 つあり、言っている事実が違う。裸の名前が型として登録されていなければ「未知の
エフェクト: Nope」(綴りの誤り。上の nope)、登録されていれば「型 Int32 はエフェクト
ではありません」(位置の誤り。上の kinderr2)、module 修飾の名前と適用形は読んだ
結果のカインドを見て「エフェクト位置の型のカインドが Row ではありません」(読んだ
結果が行にならない)。3 つを 1 つの文言に揃えると、どれかが嘘になる。エフェクト位置
で落ちる診断がこの 3 つで尽きるわけではない。行カインドでない型パラメータと Type
エイリアスは、名前を引いた時点で手前の枝が別の文言で先に落とす(下の regionkind と
上の classrow / classrow2、および effkind6):

  $ printf 'type P = Int32\nlet f(x: Int32): Int32 @ P = x\n' > effkind6.kel
  $ diktor --type-check effkind6.kel
  ! effkind6.kel:2:26: 型エラー: エフェクト位置に Type エイリアス P は使えません(: EffectRow を付けてください)
  [1]

最後の枝へ通る 3 つ目の道は {… extends <ty>} の右(文法の extends は eff ではなく
ty を取る)。この経路ができたぶん、EBraceRow の枝の「extends の右は行でなければ
なりません」は到達不能になった(枝は安全網として残してある):

  $ printf 'let f(x: Int32): Int32 @ {extends #Tag} = x\n' > effkind7.kel
  $ diktor --type-check effkind7.kel
  ! effkind7.kel:1:35: 型エラー: エフェクト位置の型のカインドが Row ではありません: #Tag :: Type
  [1]

run が導入するリージョン変数 h のカインドは Type(D130。仕様 §10、
sample.kel:641)。行の位置(@ h)には書けない:

  $ cat > regionkind.kel <<'EOF'
  > let f(): Int32 = run h {
  >   let g: () => Int32 @ h = fn() => 1
  >   g()
  > }
  > EOF
  $ diktor --type-check regionkind.kel
  ! regionkind.kel:2:24: 型エラー: 行カインドではない型パラメータです: h
  [1]

値の型の位置には書けてしまう。値の型の位置はカインド Type を要求する(D131)
ので、これが通ること自体が h のカインドが Type だという観測になる。h の値を
作る手段は無いので実行には届かない(台帳 V21):

  $ cat > regionkind2.kel <<'EOF'
  > let f(): Int32 = run h {
  >   let g: (h) => Int32 = fn(x) => 1
  >   0
  > }
  > EOF
  $ diktor --type-check regionkind2.kel
  f : () => Int32
