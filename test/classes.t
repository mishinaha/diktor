型クラスの検査をテストする。曖昧性の検査、インスタンスの実装の純粋性、標準環境の Show のインスタンスと、
型エイリアスのパラメータやクラスパラメータに制約を書けないことを扱う。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

曖昧性の検査をテストする。型クラスのメソッドではない多相関数 read_(型は [A: Show] (String) => A)でも、
結果の型が決まらない使い方は曖昧性エラーになる(クラスのメソッドで書く形は
test/dictionary_passing.t の read と pureamb が扱う):

  $ cat > ml9b.kel <<'KEL'
  > let read_[A: Show](s: String): A = ???
  > let s = show(read_("1"))
  > KEL
  $ diktor --type-check --no-prelude ml9b.kel
  read_ : [A: Show] (String) => A
  ! ml9b.kel:2:1: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

文脈から型が決まれば曖昧ではない:

  $ cat > ml9c.kel <<'KEL'
  > let read_[A: Show](s: String): A = ???
  > let n = read_("1") + 1i32
  > let wrapper2() = { let m = read_("2"); m + 1i32 }
  > KEL
  $ diktor --type-check --no-prelude ml9c.kel
  read_ : [A: Show] (String) => A
  n : Int32
  wrapper2 : () => Int32

内側の let に残った制約も、それを囲む束縛 wrapper を一般化する直前に検査する(check_ambiguity の all=false の経路で、診断は wrapper を指す):

  $ cat > ml9d.kel <<'KEL'
  > let read_[A: Show](s: String): A = ???
  > let wrapper() = { let v = show(read_("2")); v }
  > KEL
  $ diktor --type-check --no-prelude ml9d.kel
  read_ : [A: Show] (String) => A
  ! ml9d.kel:2:5: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

一般化しない束縛(値制限)の型変数に付いた制約は、ファイルの終わりまでに型が
決まれば曖昧ではない。同じファイルの中で weak を Int32 に適用すれば型検査に通る:

  $ cat > ml9e.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let weak = idf(show)
  > weak(1i32)
  > KEL
  $ diktor --type-check --no-prelude ml9e.kel
  idf : (A) => A
  weak : [_A: Show] (_A) => String @ {}
  _ : String

ファイルの終わりまでに型が決まらなければ、曖昧性エラーになる。辞書はファイルごとに
静的に決まり、未解決の辞書を実行時まで残さない(LangSpec §6.2):

  $ cat > ml9e2.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let weak = idf(show)
  > KEL
  $ diktor --type-check --no-prelude ml9e2.kel
  idf : (A) => A
  weak : [_A: Show] (_A) => String @ {}
  ! ml9e2.kel:2:16: 型エラー: 曖昧な制約: Show を満たす型が決まりません(一般化しない束縛か式文の型変数です。注釈で型を決めてください)
  [1]

予約述語の付いた型変数は既定化で型が決まるので、曖昧性エラーにしない:

  $ cat > ml9f.kel <<'KEL'
  > let ne = 1 != 2
  > let z = show(1 + 1)
  > KEL
  $ diktor --type-check --no-prelude ml9f.kel
  ne : Boolean
  z : String

式文も検査の対象である。値を捨てる式の型変数に付いた制約は、
どこからも型が決まらないので、曖昧性エラーになる:

  $ printf 'let read_[A: Show](s: String): A = ???\nlet f() = { show; "x" }\n' > ml9g.kel
  $ diktor --type-check --no-prelude ml9g.kel
  read_ : [A: Show] (String) => A
  ! ml9g.kel:2:5: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

曖昧な制約のあるプログラムは、型検査で拒否されて評価されない:

  $ printf 'let read_[A: Show](s: String): A = ???\necholn(show(read_("1")))\n' > amb.kel
  $ diktor amb.kel
  ! amb.kel:2:1: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

型エイリアスのパラメータには制約を書けない(LangSpec §12.1)。宣言の時点で拒否する:

  $ printf 'type P[A: Show] = (A, A)\nlet ok: P[Int32] = (1i32, 2i32)\n' > alc.kel
  $ diktor --type-check --no-prelude alc.kel
  ! alc.kel:1:1: 型エラー: 型エイリアス P の型パラメータ A には型クラスの制約を書けません
  [1]

インスタンスの本体にも、宣言の終わりの曖昧性の検査を行う。inam のように、値でない式で書いた実装は一般化されず、
結果の型に現れない Show の制約が残るので、宣言の終わりの検査で曖昧性エラーになる(診断は宣言の先頭を指す)。
inam2 のように関数として書いた実装は、束縛を一般化する直前の検査で曖昧性エラーになる(診断は束縛の名前を指す):

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
  $ cat > inam2.kel <<'KEL'
  > type class C[A] { val cm: (A) => A @ {} }
  > let read_[A: Show](s: String): A = ???
  > let idf[A](x: A): A = x
  > type instance C[Int32] { let cm(x) = { show(read_("z")); idf(x) } }
  > KEL
  $ diktor --type-check --no-prelude inam2.kel
  read_ : [A: Show] (String) => A
  idf : (A) => A
  ! inam2.kel:4:30: 型エラー: 曖昧な制約: Show を満たす型が決まりません(結果の型に現れない型変数です。注釈で型を決めてください)
  [1]

スーパークラスは設けない(sample.kel §8)。クラスパラメータに書いた制約は宣言の時点で
拒否する。Ord は Eq を含まないので、両方が必要なときは [A: Eq + Ord] と並べて書く:

  $ cat > super.kel <<'KEL'
  > type class MyEq[A] { val myeq: (A, A) => Boolean }
  > type class MyOrd[A: MyEq] { val mylt: (A, A) => Boolean }
  > KEL
  $ diktor --type-check --no-prelude super.kel
  ! super.kel:2:1: 型エラー: クラスパラメータに制約は書けません(スーパークラスは入れないという設計上の決定です。両方が必要なときは [A: Eq + Ord] のように並べて書いてください)
  [1]

  $ printf 'let f[A: Ord](x: A, y: A): Boolean = x == y\n' > ordeq.kel
  $ diktor --type-check ordeq.kel
  ! ordeq.kel:1:38: 型エラー: 型パラメータ ς1 は Eq のインスタンスではありません。[A: Eq] のように制約を書いてください
  [1]

  $ printf 'let f[A: Eq + Ord](x: A, y: A): Boolean = x == y && x < y\n' > ordeq2.kel
  $ diktor --type-check ordeq2.kel
  f : [A: Eq + Ord] (A, A) => Boolean

型クラスのメソッドの最も外側で省略した @ は @ {} と読み、実装は純粋でなければならない(sample.kel §9)。
引数の矢印の @ を省略したメソッドも、純粋な実装なら書ける。入れ子の矢印で省略した @ は @ {} なので、実装の行は
{} に決まり、インスタンスの本体の包摂検査(第11章 §11.38)が最も外側の行を最後に比較して受理する:

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

メソッドをエフェクト多相にするには、行変数を明示する(sample.kel §8 の Functor):

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

実装が純粋でなければ型エラーになる(sample.kel §9):

  $ cat > clsimpure.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Sizer[T] { val size: (T) => Int32 }
  > type instance Sizer[Box] { let size(b) = b match { case Box(x) => { echo("eff!"); x } } }
  > KEL
  $ diktor --type-check clsimpure.kel
  ! clsimpure.kel:3:32: 型エラー: 型クラスのメソッドの実装は純粋でなければなりません(宣言の最も外側の行にラベルがありません — 仕様 §9)。インスタンスメソッド size の本体がエフェクトを起こしています。元の報告: ラベル Console がありません(行は閉じています)
  [1]

型クラスのメソッドの最も外側の矢印に書いたラベル付きの行も、let や extern と同じく、閉じたまま束縛の型になり、
呼び出すときに行の末尾を開く(LangSpec §13.2 は、型クラスのメソッドの宣言で型の先頭に書いた矢印も、最も外側の矢印に含める)。
そのため、@ Console と書いたメソッドを、Console を含む行を注釈した関数(use と use2)から呼び出せ、use2 はトップレベルからも呼び出せる:

  $ cat > clsrow3.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Pr[T] { val pr: (T) => Unit @ Console }
  > type instance Pr[Box] { let pr(b) = b match { case Box(x) => echo("n") } }
  > let use(b: Box): Unit @ {Console, Print} = pr(b)
  > let use2(b: Box): Unit @ Console = pr(b)
  > use2(Box(1))
  > KEL
  $ diktor --type-check clsrow3.kel
  use : (Box) => {} @ {Console, Print}
  use2 : (Box) => {} @ {Console}
  _ : {}
  $ diktor clsrow3.kel
  n

メソッドに書いた行は、実装の本体が起こせるエフェクトの上限である。実装が何も起こさなくても、純粋な文脈からは呼び出せない:

  $ cat > clsrow4.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Pr[T] { val pr: (T) => Unit @ Console }
  > type instance Pr[Box] { let pr(b) = b match { case Box(x) => () } }
  > let use3(b: Box): Unit @ {} = pr(b)
  > KEL
  $ diktor --type-check clsrow4.kel
  ! clsrow4.kel:4:31: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を伝えるなら行変数を型パラメータに取ってください。§9)
  [1]

純粋性の規則を明記したメッセージにするかどうかは、宣言の形で決まる。宣言が @ Print のようにラベルを書いた形では、
実装が起こした Console との不一致であって純粋性の問題ではないので、通常のメッセージで報告する:

  $ cat > clsmismatch.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Pr[T] { val pr: (T) => Unit @ Print }
  > type instance Pr[Box] { let pr(b) = b match { case Box(x) => echo("n") } }
  > KEL
  $ diktor --type-check clsmismatch.kel
  ! clsmismatch.kel:3:29: 型エラー: インスタンスメソッド pr がクラス宣言の型を満たしません(ラベル Console がありません(行は閉じています))
  [1]

宣言がラベルを 1 つも書いていなければ、@ を省略していなくても、規則を明記したメッセージになる。
メソッドの型パラメータに行変数を取って @ E と書いた形は、上の clsimpure と同じ規則を明記した
メッセージになる(「元の報告」の部分は、宣言の行が注釈で固定された行変数であることを示す):

  $ cat > clsbarerow.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Pr2[T] { val pr2[E]: (T) => Unit @ E }
  > type instance Pr2[Box] { let pr2(b) = b match { case Box(x) => echo("n") } }
  > KEL
  $ diktor --type-check clsbarerow.kel
  ! clsbarerow.kel:3:30: 型エラー: 型クラスのメソッドの実装は純粋でなければなりません(宣言の最も外側の行にラベルがありません — 仕様 §9)。インスタンスメソッド pr2 の本体がエフェクトを起こしています。元の報告: 行 ς1 は注釈で固定された行変数なので、ラベル Console を追加できません(注釈側に Console を(必要なら引数つきで)書き足してください)
  [1]

メッセージの後半は、実装の束縛の形に応じて変わる。clsannotrow は、実装の関数束縛が最も外側に
@ Print を書き、本体は何もエフェクトを起こさない形で、後半は本体ではなく型注釈を指す(本体が
echo を呼び出し、型注釈を書かない形は上の clsimpure である):

  $ cat > clsannotrow.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class Sizer[T] { val size: (T) => Int32 }
  > type instance Sizer[Box] { let size(b: Box): Int32 @ Print = b match { case Box(x) => x } }
  > KEL
  $ diktor --type-check clsannotrow.kel
  ! clsannotrow.kel:3:32: 型エラー: 型クラスのメソッドの実装は純粋でなければなりません(宣言の最も外側の行にラベルがありません — 仕様 §9)。インスタンスメソッド size の注釈に @ {} 以外の行を書いています。元の報告: ラベル Print がありません(行は閉じています)
  [1]

clsannotalias は、実装の値束縛の型注釈の先頭に、行が Print である矢印のエイリアス Fn を書いた形で、
これも後半は型注釈を指す:

  $ cat > clsannotalias.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type Fn = (Box) => Int32 @ Print
  > type class Sizer[T] { val size: (T) => Int32 }
  > type instance Sizer[Box] { let size: Fn = fn(b) => 1 }
  > KEL
  $ diktor --type-check clsannotalias.kel
  ! clsannotalias.kel:4:32: 型エラー: 型クラスのメソッドの実装は純粋でなければなりません(宣言の最も外側の行にラベルがありません — 仕様 §9)。インスタンスメソッド size の注釈に @ {} 以外の行を書いています。元の報告: ラベル Print がありません(行は閉じています)
  [1]

clsvalrow は、型注釈を書かない値束縛の初期化式に、@ Print と注釈した関数 sizeP の名前だけを
書いた形である。最も外側の @ を書かない値束縛なので、行は初期化式の値の型で決まる。後半は、
本体にも型注釈にも触れず、初期化式の値の型について述べる:

  $ cat > clsvalrow.kel <<'KEL'
  > newtype Box = Box(Int32)
  > let sizeP(b: Box): Int32 @ Print = 1
  > type class Sizer[T] { val size: (T) => Int32 }
  > type instance Sizer[Box] { let size = sizeP }
  > KEL
  $ diktor --type-check clsvalrow.kel
  sizeP : (Box) => Int32 @ {Print}
  ! clsvalrow.kel:4:32: 型エラー: 型クラスのメソッドの実装は純粋でなければなりません(宣言の最も外側の行にラベルがありません — 仕様 §9)。インスタンスメソッド size の初期化式の値の型の最も外側の行が空ではありません。元の報告: ラベル Print がありません(行は閉じています)
  [1]

規則を明記したメッセージは、最も外側の行の単一化が失敗したときに出すので、同じ宣言でも実装によって
メッセージが変わる。高階の引数を呼び出さない実装は最も外側の行の単一化で失敗し、呼び出す実装は引数の
単一化のほうが先に失敗する。どちらも型エラーになることは変わらない:

  $ cat > clsargpure.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class R3[T] { val r3[E]: (T, () => Unit @ E) => Unit @ E }
  > type instance R3[Box] { let r3(b, f) = { echo("x"); () } }
  > KEL
  $ diktor --type-check clsargpure.kel
  ! clsargpure.kel:3:29: 型エラー: 型クラスのメソッドの実装は純粋でなければなりません(宣言の最も外側の行にラベルがありません — 仕様 §9)。インスタンスメソッド r3 の本体がエフェクトを起こしています。元の報告: 行 ς1 は注釈で固定された行変数なので、ラベル Console を追加できません(注釈側に Console を(必要なら引数つきで)書き足してください)
  [1]
  $ cat > clsargcall.kel <<'KEL'
  > newtype Box = Box(Int32)
  > type class R3[T] { val r3[E]: (T, () => Unit @ E) => Unit @ E }
  > type instance R3[Box] { let r3(b, f) = { echo("x"); f() } }
  > KEL
  $ diktor --type-check clsargcall.kel
  ! clsargcall.kel:3:29: 型エラー: インスタンスメソッド r3 がクラス宣言の型を満たしません(行 ς1 は注釈で固定された行変数なので、ラベル Console を追加できません(注釈側に Console を(必要なら引数つきで)書き足してください))
  [1]

プレリュードは、List と Option に前提付きの Show のインスタンスを持つ。出力の形式を
ここで固定する。要素の区切りは `, `、空リストは `[]` で、Option はコンストラクタの
名前のまま表示する。文字列の要素に引用符が付かないのは、Show[String] が文字列をそのまま返すからである:

  $ cat > pshow.kel <<'KEL'
  > let empty(): List[Int32] = Nil
  > let none(): Option[Int32] = None
  > echoln(show(Cons(1, Cons(2, Cons(3, Nil)))))
  > echoln(show(Cons(1, Nil)))
  > echoln(show(empty()))
  > echoln(show(Some(1)))
  > echoln(show(none()))
  > echoln(show(Cons(Some(1), Cons(None, Nil))))
  > echoln(show(Cons("a", Cons("b", Nil))))
  > KEL
  $ diktor pshow.kel
  [1, 2, 3]
  [1]
  []
  Some(1)
  None
  [Some(1), None]
  [a, b]

長さ 0 から 20 のリストと入れ子のリストで、要素の順序と区切りが、先頭から順につないだ結果と
同じになることを確かめる。Show[List] は要素を 4 つずつのまとまりにし、隣り合う 2 つをつなぐ処理を、
向きを交互に変えて繰り返す。長さ 20 までで、まとまりの数とつなぐ回数の境界の場合がひととおり現れる:

  $ cat > pshowsplit.kel <<'KEL'
  > let rec upto(i: Int32, acc: List[Int32]): List[Int32] = if i == 0 then acc else upto(i - 1, Cons(i, acc))
  > let rec each(n: Int32): Unit @ Console = if n == 21 then () else {
  >   echoln(show(upto(n, Nil)))
  >   each(n + 1)
  > }
  > each(0)
  > echoln(show(Cons(upto(3, Nil), Cons(upto(0, Nil), Cons(upto(5, Nil), Nil)))))
  > KEL
  $ diktor pshowsplit.kel
  []
  [1]
  [1, 2]
  [1, 2, 3]
  [1, 2, 3, 4]
  [1, 2, 3, 4, 5]
  [1, 2, 3, 4, 5, 6]
  [1, 2, 3, 4, 5, 6, 7]
  [1, 2, 3, 4, 5, 6, 7, 8]
  [1, 2, 3, 4, 5, 6, 7, 8, 9]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
  [[1, 2, 3], [], [1, 2, 3, 4, 5]]

インスタンスに書いた前提 [A: Show] は有効である。要素の型が Show のインスタンスでなければ型エラーになる:

  $ cat > pshowop.kel <<'KEL'
  > newtype Opaque = Op(Int32)
  > echoln(show(Cons(Op(1), Nil)))
  > KEL
  $ diktor --type-check pshowop.kel
  ! pshowop.kel:2:13: 型エラー: Opaque は Show のインスタンスではありません。List[Opaque] が Show であるための前提として要求されました
  [1]

同梱のプレリュードを使っているときに、ユーザが同じ対象の型のインスタンスをもう一度宣言すると、コヒーレンス違反に
なる(標準環境が持つインスタンスと同じクラスと型の組は宣言できない。LangSpec §12.2):

  $ cat > pshowdup.kel <<'KEL'
  > type instance[A: Show] Show[List[_]] {
  >   let show(xs) = "USER"
  > }
  > KEL
  $ diktor --type-check pshowdup.kel
  ! pshowdup.kel:1:1: 型エラー: インスタンス Show[List] が二重に宣言されています(コヒーレンス違反)
  [1]

残りの 2 つの場合を確かめる。--no-prelude では List もインスタンスもなくなるので、上で拒否されたのと
同じ対象の型のインスタンスを、ユーザが自分で宣言できる。2 度書けば、ユーザの宣言どうしの重複として型エラーになる:

  $ cat > pshow2.kel <<'KEL'
  > newtype List[A] = Nil | Cons(head: A, tail: List[A])
  > type instance[A: Show] Show[List[_]] {
  >   let show(xs) = xs match {
  >     case Nil => "<>"
  >     case Cons(head = h, tail = t) => Show.show(h)
  >   }
  > }
  > let s = show(Cons(1, Nil))
  > KEL
  $ diktor --type-check --no-prelude pshow2.kel
  s : String
  $ cat > pshow2b.kel <<'KEL'
  > newtype List[A] = Nil | Cons(head: A, tail: List[A])
  > type instance[A: Show] Show[List[_]] { let show(xs) = "1" }
  > type instance[A: Show] Show[List[_]] { let show(xs) = "2" }
  > KEL
  $ diktor --type-check --no-prelude pshow2b.kel
  ! pshow2b.kel:3:1: 型エラー: インスタンス Show[List] が二重に宣言されています(コヒーレンス違反)
  [1]

--prelude でプレリュードを差し替えたときは、差し替えたプレリュードのインスタンスが使われる。同梱の
Show[Option] はほかの宣言とともになくなる。ユーザの再宣言は、同梱のプレリュードのときと同じく型エラーになる:

  $ cat > pshowpre.kel <<'KEL'
  > type Unit = {}
  > effect Console = { write: (String) => Unit }
  > newtype List[A] = Nil | Cons(head: A, tail: List[A])
  > type instance[A: Show] Show[List[_]] {
  >   let show(xs) = xs match {
  >     case Nil => "<>"
  >     case Cons(head = h, tail = t) => "<" + Show.show(h) + ">"
  >   }
  > }
  > let echoln(message: String): Unit @ Console = perform write(message + "\n")
  > KEL
  $ printf 'echoln(show(Cons(7, Nil)))\n' > pshowuse.kel
  $ diktor --prelude pshowpre.kel pshowuse.kel
  <7>
  $ printf 'echoln(show(Some(1)))\n' > pshowuse2.kel
  $ diktor --prelude pshowpre.kel --type-check pshowuse2.kel
  ! pshowuse2.kel:1:13: 型エラー: 未知のコンストラクタ: Some
  [1]
  $ diktor --prelude pshowpre.kel --type-check pshowdup.kel
  ! pshowdup.kel:1:1: 型エラー: インスタンス Show[List] が二重に宣言されています(コヒーレンス違反)
  [1]
