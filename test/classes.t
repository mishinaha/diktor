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

予約述語が乗った変数は既定化で決まるので曖昧にしない(D8 / D49):

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

エイリアスのパラメータ制約は展開時に課される(D51。newtype と同じ扱い。
かつては黙って無視され、同じ構文の意味が宣言種別で違った):

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

derive structural はカインドでも弾く(D9 — sample.kel §14 の TODO への
回答: 弾ける。構造的導出はレコード・ヴァリアントに配る規則なので
Type のクラスにしか意味が無い):

  $ cat > c14.kel <<'KEL'
  > type class MyF[F[_]] {
  >   val mymap[A, B, E]: (F[A], (A) => B @ E) => F[B] @ E
  >   derive structural
  > }
  > KEL
  $ diktor --type-check --no-prelude c14.kel
  ! c14.kel:1:1: 型エラー: derive structural は Type のクラスにしか付けられません(MyF のパラメータは [_] Type です)
  [1]
