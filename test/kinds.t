M23 / ワークストリーム C(newtype の型パラメータのカインド推論)のゴールデン。
変更時は dune promote で更新し、必ず目視レビューすること。

仕様 §6「型パラメータのカインドは本体での使われ方から推論し、使われ方が
無ければ Type」と §9 の `newtype Callback[E] = Callback(() => Unit @ E)`。

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

行カインドのパラメータへ具体的な行を前方参照つきで渡す形だけは宣言順に
依存する(§11.31 の末尾。相手がまだ 1b を通っていないとカインドが KVar の
ままなので、読み分けが {…} を型として読む。行変数を渡す形は依存しない):

  $ cat > fwdrow.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype A4[X] = MkA4(B4[{Print extends X}])
  > newtype B4[E] = MkB4(() => Unit @ E)
  > let f[E](x: A4[E]): A4[E] = x
  > EOF
  $ diktor --type-check --no-prelude fwdrow.kel
  ! fwdrow.kel:3:25: 型エラー: エフェクトラベルはこの位置(レコード型)では使えません
  [1]
  $ cat > fwdrow2.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > newtype B5[E] = MkB5(() => Unit @ E)
  > newtype A5[X] = MkA5(B5[{Print extends X}])
  > let f[E](x: A5[E]): A5[E] = x
  > EOF
  $ diktor --type-check --no-prelude fwdrow2.kel
  f : (A5[R1]) => A5[R1]

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

行カインドのパラメータを持つ型は Functor のインスタンスにできない
(頭のカインドが [_] Type ではなくなるため。D80 の副産物):

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

型エイリアスのパラメータのカインドも本体から推論して表に残す(D84)。
newtype を透過に包むエイリアスに、行変数でも具体的な行でも渡せる(かつては
引数を全部型として読んだので、具体的な行は「エフェクトラベルはこの位置では
使えません」で落ちた):

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

宣言順に依存しない(推論は 1b の後始末の投機的な精緻化で、使用点より前に済む。
使用がエイリアスより前でも、エイリアスが newtype より前でも同じ):

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
