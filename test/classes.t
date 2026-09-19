型クラスの検査(M17)。曖昧性検査(D2 / D48)、エイリアスの
パラメータ制約(D5 / D51)、derive structural のカインド(D9)。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

MiniLang §16-9(曖昧性検査)。read : Str -> a は v0 ではクラスとしては
宣言できない(クラスパラメータは引数の頭に現れよ、§11.33)ので、同じ
型を持つ普通の多相 let で代用する:

  $ cat > ml9b.kel <<'KEL'
  > let read_[A: Show](s: String): A = ???
  > let s = show(read_("1"))
  > KEL
  $ diktor --type-check --no-prelude ml9b.kel
  read_ : [A: Show] (String) => A
  ! ml9b.kel:2:1: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

文脈が型を決めていれば曖昧ではない:

  $ cat > ml9c.kel <<'KEL'
  > let read_[A: Show](s: String): A = ???
  > let n = read_("1") + 1i32
  > let wrapper2() = { let m = read_("2"); m + 1i32 }
  > KEL
  $ diktor --type-check --no-prelude ml9c.kel
  read_ : [A: Show] (String) => A
  n : Int32
  wrapper2 : () => Int32

入れ子の let も一般化点の直前で見る(all=false 経路):

  $ cat > ml9d.kel <<'KEL'
  > let read_[A: Show](s: String): A = ???
  > let wrapper() = { let v = show(read_("2")); v }
  > KEL
  $ diktor --type-check --no-prelude ml9d.kel
  read_ : [A: Show] (String) => A
  ! ml9d.kel:2:5: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

公開型から到達できる制約は、弱い変数でも曖昧ではない(値制限で
一般化されないだけ):

  $ cat > ml9e.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let weak = idf(show)
  > KEL
  $ diktor --type-check --no-prelude ml9e.kel
  idf : (A) => A
  weak : [_A: Show] (_A) => String

予約述語が乗った変数は既定化で決まるので曖昧にしない(D8 / D48):

  $ cat > ml9f.kel <<'KEL'
  > let ne = 1 != 2
  > let z = show(1 + 1)
  > KEL
  $ diktor --type-check --no-prelude ml9f.kel
  ne : Boolean
  z : String

文の位置の式も検査対象(捨てられる値の制約は誰にも決まらない。
MiniLang より厳しくなる点):

  $ printf 'let read_[A: Show](s: String): A = ???\nlet f() = { show; "x" }\n' > ml9g.kel
  $ diktor --type-check --no-prelude ml9g.kel
  read_ : [A: Show] (String) => A
  ! ml9g.kel:2:5: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

曖昧な制約は評価に到達しない:

  $ printf 'let read_[A: Show](s: String): A = ???\necholn(show(read_("1")))\n' > amb.kel
  $ diktor amb.kel
  ! amb.kel:2:1: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

エイリアスのパラメータ制約は言及時に課される(D51。エイリアスは透過で
構築点が無いので、newtype の「構築時」より早い時点になる。かつては
黙って無視された):

  $ printf 'type P[A: Show] = (A, A)\nlet ok: P[Int32] = (1i32, 2i32)\n' > alc.kel
  $ diktor --type-check --no-prelude alc.kel
  ok : (Int32, Int32)
  $ cat > alc2.kel <<'KEL'
  > newtype NoShow = MkNoShow
  > type P[A: Show] = (A, A)
  > let bad: P[NoShow] = (MkNoShow, MkNoShow)
  > KEL
  $ diktor --type-check --no-prelude alc2.kel
  ! alc2.kel:3:10: 型エラー: NoShow は Show のインスタンスではありません
  [1]

derive structural はユーザの新クラスでは全面拒否(M15)。カインド検査
(D9 — sample.kel §14 の TODO への回答: 弾ける)が単独で効くのは
組み込みと同名のクラスの再宣言だけ。案内が行動可能なほう(全面拒否)を
先に出す:

  $ cat > c14.kel <<'KEL'
  > type class MyF[F[_]] {
  >   val mymap[A, B, E]: (F[A], (A) => B @ E) => F[B] @ E
  >   derive structural
  > }
  > KEL
  $ diktor --type-check --no-prelude c14.kel
  ! c14.kel:1:1: 型エラー: derive structural はユーザ宣言のクラスには書けません(構造的な型へのインスタンスは組み込みの自動導出のみが与えます)
  [1]
  $ cat > c14b.kel <<'KEL'
  > type class Eq[F[_]] {
  >   val eq[A]: (F[A], F[A]) => Boolean
  >   derive structural
  > }
  > KEL
  $ diktor --type-check c14b.kel
  ! c14b.kel:1:1: 型エラー: derive structural は Type のクラスにしか付けられません(Eq のパラメータは [_] Type です)
  [1]

コンストラクタ由来の制約つき変数も台帳に載る(M17 検証。かつて
subst_params 経路が台帳をすり抜け、Empty 由来の Show だけ素通りした):

  $ cat > fn1.kel <<'KEL'
  > newtype Box[A: Show] = Empty | Box(A)
  > let idf[A](x: A): A = x
  > let g(): String = { let e = idf(Empty); "x" }
  > KEL
  $ diktor --type-check --no-prelude fn1.kel
  idf : (A) => A
  ! fn1.kel:3:5: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

instance 本体にも宣言終端の掃き出しが掛かる(M17 検証。値制限で
一般化されない本体 let は all=false 検査を通らない):

  $ cat > inam.kel <<'KEL'
  > type class C[A] { val cm: (A) => A @ {} }
  > let read_[A: Show](s: String): A = ???
  > let idf[A](x: A): A = x
  > type instance C[Int32] { let cm = { show(read_("z")); idf(fn(x: Int32) => x) } }
  > KEL
  $ diktor --type-check --no-prelude inam.kel
  read_ : [A: Show] (String) => A
  idf : (A) => A
  ! inam.kel:4:1: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

制約つきエイリアスは宣言スキーマの位置(newtype フィールド・クラス
メソッド型)でも使える — Generic のパラメータが制約を持っていれば
満たされ、無ければ制約を書けと案内される(M17 検証。かつて add_class が
Generic を扱えず、満たしていても落ちた):

  $ cat > alg.kel <<'KEL'
  > type P[A: Show] = (A, A)
  > newtype Wrap[B: Show] = Wrap(P[B])
  > let w = Wrap((1i32, 2i32))
  > KEL
  $ diktor --type-check --no-prelude alg.kel
  w : Wrap[Int32]
  $ printf 'type P[A: Show] = (A, A)\nnewtype Wrap[B] = Wrap(P[B])\n' > alg2.kel
  $ diktor --type-check --no-prelude alg2.kel
  ! alg2.kel:2:24: 型エラー: 型パラメータ A は Show のインスタンスではありません。[A: Show] のように制約を書いてください
  [1]

スーパークラスは入れない裁定(§8 / D98)。クラスパラメータの制約は宣言時に
拒否し、Ord は Eq を含意しないので両方要るときは [A: Eq + Ord] と並べて書く:

  $ cat > super.kel <<'KEL'
  > type class MyEq[A] { val myeq: (A, A) => Boolean }
  > type class MyOrd[A: MyEq] { val mylt: (A, A) => Boolean }
  > KEL
  $ diktor --type-check --no-prelude super.kel
  ! super.kel:2:1: 型エラー: クラスパラメータに制約は書けません(スーパークラスは入れない裁定です。両方が要るときは [A: Eq + Ord] のように並べて書いてください)
  [1]

  $ printf 'let f[A: Ord](x: A, y: A): Boolean = x == y\n' > ordeq.kel
  $ diktor --type-check ordeq.kel
  ! ordeq.kel:1:38: 型エラー: 型パラメータ ς1 は Eq のインスタンスではありません。[A: Eq] のように制約を書いてください
  [1]

  $ printf 'let f[A: Eq + Ord](x: A, y: A): Boolean = x == y && x < y\n' > ordeq2.kel
  $ diktor --type-check ordeq2.kel
  f : [A: Eq + Ord] (A, A) => Boolean

型クラスのメソッドの最外の @ 省略は「実装は純粋・公開は行多相」(§9 / D77)。
引数の矢印の @ を省略したメソッドも、純粋な実装なら書ける(入れ子の省略 @ は
@ {} なので実装の行は {} に固まる — 包摂が最外の行を最後に見て受理する):

  $ cat > clsrow.kel <<'KEL'
  > type Unit = {}
  > newtype Box[A] = Box(A)
  > type class Mapper2[F[_]] {
  >   val fmap2[X, Y]: (F[X], (X) => Y) => F[Y]
  > }
  > type instance Mapper2[Box[_]] {
  >   let fmap2(b, f) = b match { case Box(x) => Box(f(x)) }
  > }
  > KEL
  $ diktor --type-check --no-prelude clsrow.kel

エフェクト多相にしたいメソッドは行変数を明示する(§8 の Functor):

  $ cat > clsrow2.kel <<'KEL'
  > type Unit = {}
  > newtype Box[A] = Box(A)
  > type class Mapper[F[_]] {
  >   val fmap[X, Y, E]: (F[X], (X) => Y @ E) => F[Y] @ E
  > }
  > type instance Mapper[Box[_]] {
  >   let fmap(b, f) = b match { case Box(x) => Box(f(x)) }
  > }
  > KEL
  $ diktor --type-check --no-prelude clsrow2.kel

実装が純粋でなければ落ちる(§9 の「実装が純粋でなければならず」):

  $ cat > clsimpure.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Sizer[T] { val size: (T) => Int32 }
  > type instance Sizer[Box] { let size(b) = b match { case Box(x) => { echo("eff!"); x } } }
  > KEL
  $ diktor --type-check clsimpure.kel
  ! clsimpure.kel:3:32: 型エラー: 型クラスのメソッドの実装は純粋でなければなりません(公開される型は行多相 — 仕様 §9)。インスタンスメソッド size の本体がエフェクトを起こしています。元の報告: 行 ς1 は注釈で固定された行変数なので、ラベル Console を足せません(注釈側に Console を(必要なら引数つきで)書き足してください)
  [1]

型クラスのメソッドの最外のラベル付き行も、let / extern と同じく公開では行変数で
開かれる(仕様 §9 の表は束縛の最外にメソッドを含める。M26 の検証まで開いておらず、
@ Console と書いたメソッドは注釈つきの文脈からもトップレベルからも呼べなかった):

  $ cat > clsrow3.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Pr[T] { val pr: (T) => Unit @ Console }
  > type instance Pr[Box] { let pr(b) = b match { case Box(x) => echo("n") } }
  > let use(b: Box): Unit @ {Console, Print} = pr(b)
  > let use2(b: Box): Unit @ Console = pr(b)
  > use2(Box(1))
  > KEL
  $ diktor --type-check clsrow3.kel
  use : (Box) => {} @ {Console, Print extends R1}
  use2 : (Box) => {} @ {Console extends R1}
  _ : {}
  $ diktor clsrow3.kel
  n

本体が上限で、純粋な文脈からは呼べない(D44 と同じ非対称):

  $ cat > clsrow4.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Pr[T] { val pr: (T) => Unit @ Console }
  > type instance Pr[Box] { let pr(b) = b match { case Box(x) => () } }
  > let use3(b: Box): Unit @ {} = pr(b)
  > KEL
  $ diktor --type-check clsrow4.kel
  ! clsrow4.kel:4:31: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
