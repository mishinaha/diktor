可視性検査(M16 / H1、D41〜D43)。検査は module 境界だけ(D41 —
複数ファイルは 1 プログラムに連結されるので、ファイル境界は見ない)。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

非 pub の let を外から修飾参照すると拒否。型行は宣言順に出てから止まる:

  $ cat > vis1.kel <<'KEL'
  > module M {
  >   pub let f(x: Int32): Int32 = x
  >   let g(x: Int32): Int32 = x
  > }
  > echoln(show(M.g(1)))
  > KEL
  $ diktor --type-check vis1.kel
  M.f : (Int32) => Int32
  M.g : (Int32) => Int32
  ! vis1.kel:5:13: 型エラー: M.g は module M の外からは参照できません(pub を付けてください)
  [1]

pub の let は外から呼べる:

  $ cat > vis2.kel <<'KEL'
  > module M { pub let f(x: Int32): Int32 = x }
  > echoln(show(M.f(41) + 1))
  > KEL
  $ diktor vis2.kel
  42

非 pub の型を外から修飾参照:

  $ cat > vis3.kel <<'KEL'
  > module M { newtype Priv = P(Int32) }
  > let u(x: M.Priv): Int32 = 0
  > KEL
  $ diktor --type-check vis3.kel
  ! vis3.kel:2:10: 型エラー: 型 M.Priv は module M の外からは参照できません(pub を付けてください)
  [1]

非修飾の内部型は外から見えない。非 pub の名前は候補にも挙げない
(案内に従っても可視性エラーになるだけ — M16 検証):

  $ cat > vis4.kel <<'KEL'
  > module M { newtype Priv = P(Int32) }
  > let u(x: Priv): Int32 = 0
  > KEL
  $ diktor --type-check vis4.kel
  ! vis4.kel:2:10: 型エラー: 未知の型: Priv
  [1]

pub なら候補として案内される:

  $ cat > vis4b.kel <<'KEL'
  > module M { pub newtype Pub = P(Int32) }
  > let u(x: Pub): Int32 = 0
  > KEL
  $ diktor --type-check vis4b.kel
  ! vis4b.kel:2:10: 型エラー: 未知の型: Pub(M.Pub と修飾してください)
  [1]

非 pub newtype のコンストラクタは外から使えない(D42 — コンストラクタの
可視性は所属 newtype の pub に従う):

  $ cat > vis5.kel <<'KEL'
  > module M {
  >   newtype Priv = P(Int32)
  >   pub let mk(n: Int32): Priv = P(n)
  > }
  > let x = P(1)
  > KEL
  $ diktor --type-check vis5.kel
  M.mk : (Int32) => M.Priv
  ! vis5.kel:5:9: 型エラー: コンストラクタ P は module M の外からは参照できません(newtype M.Priv に pub を付けてください)
  [1]

コンパニオン型(module 名と同名の pub 型)は module 名で参照できる
(sample.kel §13。大域に残る唯一の同義語):

  $ cat > vis6.kel <<'KEL'
  > module Big {
  >   pub newtype Big = Small(Int32)
  >   pub let mk(n: Int32): Big = Small(n)
  > }
  > type MyBig = Big
  > let v(): MyBig = Big.mk(1)
  > KEL
  $ diktor --type-check vis6.kel
  Big.mk : (Int32) => Big.Big
  v : () => Big.Big

module の中では非 pub の名前が修飾でも非修飾でも見える(実行も一致):

  $ cat > vis7.kel <<'KEL'
  > module M {
  >   newtype Priv = P(Int32)
  >   let helper(x: Priv): Int32 = x match { case P(n) => n }
  >   pub let go(n: Int32): Int32 = M.helper(P(n)) + 1
  > }
  > echoln(show(M.go(1)))
  > KEL
  $ diktor vis7.kel
  2

  $ cat > vis8.kel <<'KEL'
  > module M {
  >   newtype Priv = P(Int32)
  >   let helper(x: Priv): Int32 = x match { case P(n) => n }
  >   pub let go(n: Int32): Int32 = helper(P(n)) + 1
  > }
  > echoln(show(M.go(1)))
  > KEL
  $ diktor vis8.kel
  2

module 内の型エイリアスにも可視性が乗り、修飾名で参照できる(M.A の
修飾エイリアス参照は M16 で発見した抜けの修正):

  $ cat > vis9.kel <<'KEL'
  > module M { type A = Int32 }
  > let f(x: M.A): Int32 = x
  > KEL
  $ diktor --type-check vis9.kel
  ! vis9.kel:2:10: 型エラー: 型 M.A は module M の外からは参照できません(pub を付けてください)
  [1]

  $ cat > vis11.kel <<'KEL'
  > module M { pub type Pair[A] = (A, A) }
  > let f(x: M.Pair[Int32]): Int32 = x._0 + x._1
  > echoln(show(f((20, 22))))
  > KEL
  $ diktor vis11.kel
  42

pub エイリアスの本体は宣言スコープで展開される(D43)。非 pub 型を指す
pub エイリアスは、その型の素性を作者の選択として外へ見せる:

  $ cat > vis10.kel <<'KEL'
  > module M {
  >   newtype Priv = P(Int32)
  >   pub type Pub = Priv
  > }
  > let f(x: M.Pub): Int32 = 1
  > KEL
  $ diktor --type-check vis10.kel
  f : (M.Priv) => Int32

module の中で宣言した EffectRow エイリアスは、同じ module の中から修飾せずに、
@ の後ろ、行の要素、extends の右、行を取る型引数、EffectRow エイリアスの右辺に
書ける。どの位置でも W は Print を含む行として読まれ、@ の後ろに W を書いた関数は
実行もできる:

  $ cat > visrow1.kel <<'KEL'
  > newtype Cb[E] = Cb(() => Unit @ E)
  > module M {
  >   pub type W: EffectRow = {Print}
  >   type V: EffectRow = W
  >   let at(x: Int32): Int32 @ W = x
  >   let elem(x: Int32): Int32 @ {W, Console} = x
  >   let tail(x: Int32): Int32 @ {Console extends W} = x
  >   let arg(c: Cb[W]): Int32 = 0
  >   let rhs(x: Int32): Int32 @ V = x
  >   pub let say(s: String): Unit @ W = perform print(s + "\n")
  > }
  > with_stdout(fn() => M.say("hi"))
  > KEL
  $ diktor --type-check visrow1.kel
  M.at : (Int32) => Int32 @ {Print extends R1}
  M.elem : (Int32) => Int32 @ {Print, Console extends R1}
  M.tail : (Int32) => Int32 @ {Console, Print extends R1}
  M.arg : (Cb[{Print}]) => Int32
  M.rhs : (Int32) => Int32 @ {Print extends R1}
  M.say : (String) => {} @ {Print extends R1}
  _ : {}
  $ diktor visrow1.kel
  hi

行の要素の位置にも、修飾名 M.W を書ける。module の外からは pub のエイリアスだけが
書け、pub でなければ可視性の検査で落ちる:

  $ cat > visrow2.kel <<'KEL'
  > module M {
  >   pub type W: EffectRow = {Print}
  >   let f(x: Int32): Int32 @ {M.W, Console} = x
  > }
  > let g(x: Int32): Int32 @ {M.W, Console} = x
  > KEL
  $ diktor --type-check visrow2.kel
  M.f : (Int32) => Int32 @ {Print, Console extends R1}
  g : (Int32) => Int32 @ {Print, Console extends R1}
  $ printf 'module M { type W: EffectRow = {Print} }\nlet g(x: Int32): Int32 @ {M.W, Console} = x\n' > visrow3.kel
  $ diktor --type-check visrow3.kel
  ! visrow3.kel:2:26: 型エラー: 型 M.W は module M の外からは参照できません(pub を付けてください)
  [1]

module の外から、引数の無い W を修飾せずに @ の後ろに書くと、未知のエフェクトとして
拒否する。pub の EffectRow エイリアスなら修飾を案内し、pub でなければ案内しない:

  $ printf 'module M { pub type W: EffectRow = {Print} }\nlet g(x: Int32): Int32 @ W = x\n' > visrow4.kel
  $ diktor --type-check visrow4.kel
  ! visrow4.kel:2:26: 型エラー: 未知のエフェクト: W(M.W と修飾してください)
  [1]
  $ printf 'module M { type W: EffectRow = {Print} }\nlet g(x: Int32): Int32 @ W = x\n' > visrow5.kel
  $ diktor --type-check visrow5.kel
  ! visrow5.kel:2:26: 型エラー: 未知のエフェクト: W
  [1]

型の位置では、module の中の非修飾名は、同名のトップレベルの宣言より module の宣言を指す。
エフェクト位置の EffectRow エイリアスも、型の位置の T と同じく module の W を指し、
module の外では、トップレベルの W と T を指す:

  $ cat > visrow6.kel <<'KEL'
  > type W: EffectRow = {Console}
  > type T = String
  > module M {
  >   pub type W: EffectRow = {Print}
  >   pub type T = Int32
  >   let f(x: T): T @ W = x
  > }
  > let g(x: T): T @ W = x
  > KEL
  $ diktor --type-check visrow6.kel
  M.f : (Int32) => Int32 @ {Print extends R1}
  g : (String) => String @ {Console extends R1}

プレリュードや組み込みのエフェクト(Console、Heap)と同名の EffectRow エイリアスを
module に宣言すると、module の中では、引数の無い形も引数つきの形も、@ の後ろでも
行の要素でも、そのエイリアスを指す。module の外では、Console も Heap[E] も
元のエフェクトのままである。module の中からも、トップレベルのエイリアス Out を
経由すれば、元の Console を書ける(Out の本体はトップレベルのスコープで読む):

  $ cat > visrow7.kel <<'KEL'
  > type Out: EffectRow = {Console}
  > module M {
  >   pub type Console: EffectRow = {Print}
  >   pub type Heap[E]: EffectRow = {Print extends E}
  >   let f(x: Int32): Int32 @ Console = x
  >   let g(x: Int32): Int32 @ {Console} = x
  >   let h[E](x: Int32): Int32 @ Heap[E] = x
  >   let k[E](x: Int32): Int32 @ {Heap[E]} = x
  >   let o(x: Int32): Int32 @ Out = x
  > }
  > let m(x: Int32): Int32 @ Console = x
  > let n[E](x: Int32): Int32 @ Heap[E] = x
  > KEL
  $ diktor --type-check visrow7.kel
  M.f : (Int32) => Int32 @ {Print extends R1}
  M.g : (Int32) => Int32 @ {Print extends R1}
  M.h : (Int32) => Int32 @ {Print extends R1}
  M.k : (Int32) => Int32 @ {Print extends R1}
  M.o : (Int32) => Int32 @ {Console extends R1}
  m : (Int32) => Int32 @ {Console extends R1}
  n : (Int32) => Int32 @ {Heap[A] extends R1}

module の中でエフェクト名を EffectRow エイリアスで覆うと、エイリアスの本体に書いた
同じ名前もエイリアス自身を指すので、使う箇所が無くても、宣言を再帰として拒否する。
型の位置で、module の中に type T = (T, Int32) と書いたときと同じである:

  $ printf 'module M { pub type Console: EffectRow = {Console, Print} }\n' > visrow8.kel
  $ diktor --type-check visrow8.kel
  ! visrow8.kel:1:42: 型エラー: 型エイリアス M.Console が再帰しています(エイリアスは非再帰)
  [1]
  $ printf 'type T = String\nmodule N { pub type T = (T, Int32) }\n' > visrow9.kel
  $ diktor --type-check visrow9.kel
  ! visrow9.kel:2:26: 型エラー: 型エイリアス N.T が再帰しています(エイリアスは非再帰)
  [1]

エフェクト位置で、module の宣言が同名の名前を覆うのは、EffectRow エイリアスのときだけ
である。module の newtype や Type エイリアスがエフェクトと同名でも、module の中の
@ の後ろや行の要素のその名前は、引数の有無によらず、エフェクトを指す:

  $ cat > visrow10.kel <<'KEL'
  > module M {
  >   pub newtype Console = MkC(Int32)
  >   type Print = Int32
  >   type Heap[A] = A
  >   let f(x: Int32): Int32 @ Console = x
  >   let g(x: Int32): Int32 @ {Print, Console} = x
  >   let h[H](x: Int32): Int32 @ Heap[H] = x
  >   let k[H](x: Int32): Int32 @ {Heap[H]} = x
  > }
  > KEL
  $ diktor --type-check visrow10.kel
  M.f : (Int32) => Int32 @ {Console extends R1}
  M.g : (Int32) => Int32 @ {Print, Console extends R1}
  M.h : (Int32) => Int32 @ {Heap[A] extends R1}
  M.k : (Int32) => Int32 @ {Heap[A] extends R1}
  $ cat > visrow10b.kel <<'KEL'
  > module N {
  >   pub newtype Heap[A] = MkH(A)
  >   type Console = Int32
  >   let f(x: Int32): Int32 @ Console = x
  >   let g(x: Int32): Int32 @ {Console, Print} = x
  >   let h[H](x: Int32): Int32 @ Heap[H] = x
  >   let k[H](x: Int32): Int32 @ {Heap[H]} = x
  > }
  > KEL
  $ diktor --type-check visrow10b.kel
  N.f : (Int32) => Int32 @ {Console extends R1}
  N.g : (Int32) => Int32 @ {Console, Print extends R1}
  N.h : (Int32) => Int32 @ {Heap[A] extends R1}
  N.k : (Int32) => Int32 @ {Heap[A] extends R1}

同じく、module の newtype や Type エイリアスは、同名のトップレベルの EffectRow
エイリアスも覆わない。module の中のエフェクト位置のその名前は、引数の有無に
よらず、トップレベルのエイリアスを指す:

  $ cat > visrow11.kel <<'KEL'
  > type W: EffectRow = {Console}
  > type V[E]: EffectRow = {Print extends E}
  > module M {
  >   pub newtype W = MkW(Int32)
  >   type V[A] = A
  >   let f(x: Int32): Int32 @ W = x
  >   let g(x: Int32): Int32 @ {W, Print} = x
  >   let h[E](x: Int32): Int32 @ V[E] = x
  >   let k[E](x: Int32): Int32 @ {V[E], Console} = x
  > }
  > KEL
  $ diktor --type-check visrow11.kel
  M.f : (Int32) => Int32 @ {Console extends R1}
  M.g : (Int32) => Int32 @ {Console, Print extends R1}
  M.h : (Int32) => Int32 @ {Print extends R1}
  M.k : (Int32) => Int32 @ {Print, Console extends R1}
  $ cat > visrow11b.kel <<'KEL'
  > type W: EffectRow = {Console}
  > type V[E]: EffectRow = {Print extends E}
  > module N {
  >   pub newtype V[A] = MkV(A)
  >   type W = Int32
  >   let f(x: Int32): Int32 @ W = x
  >   let g(x: Int32): Int32 @ {W, Print} = x
  >   let h[E](x: Int32): Int32 @ V[E] = x
  >   let k[E](x: Int32): Int32 @ {V[E], Console} = x
  > }
  > KEL
  $ diktor --type-check visrow11b.kel
  N.f : (Int32) => Int32 @ {Console extends R1}
  N.g : (Int32) => Int32 @ {Console, Print extends R1}
  N.h : (Int32) => Int32 @ {Print extends R1}
  N.k : (Int32) => Int32 @ {Print, Console extends R1}

module の Type エイリアスと同名のエフェクトもトップレベルのエイリアスも無ければ、
module の中で @ の後ろや行の要素に書いたその名前は、未知のエフェクトではなく、
Type エイリアスとして引いたうえで拒否する:

  $ printf 'module M {\n  type T = Int32\n  let f(x: Int32): Int32 @ T = x\n}\n' > visrow12.kel
  $ diktor --type-check visrow12.kel
  ! visrow12.kel:3:28: 型エラー: エフェクト位置に Type エイリアス T は使えません(: EffectRow を付けてください)
  [1]
  $ printf 'module M {\n  type T = Int32\n  let f(x: Int32): Int32 @ {T} = x\n}\n' > visrow13.kel
  $ diktor --type-check visrow13.kel
  ! visrow13.kel:3:28: 型エラー: エフェクト行に Type エイリアス T は置けません(: EffectRow を付けてください)
  [1]

EffectRow エイリアスのコンパニオンは、module の外から module 名だけで書ける。
pub でなければ可視性の検査で落ちる:

  $ printf 'module W { pub type W: EffectRow = {Print} }\nlet f(x: Int32): Int32 @ {W, Console} = x\n' > visrow14.kel
  $ diktor --type-check visrow14.kel
  f : (Int32) => Int32 @ {Print, Console extends R1}
  $ printf 'module W { type W: EffectRow = {Print} }\nlet f(x: Int32): Int32 @ W = x\n' > visrow15.kel
  $ diktor --type-check visrow15.kel
  ! visrow15.kel:2:26: 型エラー: 型 W.W は module W の外からは参照できません(pub を付けてください)
  [1]

同名クラスによる可視性の迂回は宣言時に拒否(M16 検証。修飾名 M.f が
クラス M のメソッド f と値環境で区別できないため):

  $ cat > visc.kel <<'KEL'
  > module Vault {
  >   newtype Priv = P(Int32)
  >   pub let mk(n: Int32): Priv = P(n)
  >   let peek(p: Priv): Int32 = p match { case P(v) => v }
  > }
  > type class Vault[A] { val peek: (A) => A }
  > echoln(show(Vault.peek(Vault.mk(9))))
  > KEL
  $ diktor visc.kel
  ! visc.kel:4:3: 型エラー: module Vault の peek は型クラス Vault のメソッド peek と修飾名が衝突します(module か メソッドを改名してください)
  [1]

instance 頭も可視性検査を通り、修飾名 M.T を受ける(M16 検証。かつては
非 pub 型に外からインスタンスが付けられ、module 自身のコヒーレンス枠を
横取りできた):

  $ cat > visi.kel <<'KEL'
  > type class C[A] { val m: (A) => Int32 }
  > module M { newtype M = Mk(Int32) }
  > type instance C[M] { let m(x) = 777 }
  > KEL
  $ diktor --type-check visi.kel
  ! visi.kel:3:1: 型エラー: 型 M.M は module M の外からは参照できません(pub を付けてください)
  [1]

  $ cat > visq.kel <<'KEL'
  > type class C[A] { val m: (A) => Int32 }
  > module M {
  >   pub newtype T = Mk(Int32)
  >   pub let mk(n: Int32): T = Mk(n)
  > }
  > type instance C[M.T] { let m(x) = 42 }
  > echoln(show(C.m(M.mk(1))))
  > KEL
  $ diktor visq.kel
  42

コンパニオン型は既存の型名を奪えない(M16 検証。module Foo を 1 行
足すだけで newtype Foo の名目型が破れた):

  $ cat > visk.kel <<'KEL'
  > newtype Foo = Wrap(Int32)
  > module Foo { pub type Foo = Int32 }
  > let use(x: Foo): Foo = x
  > KEL
  $ diktor --type-check visk.kel
  ! visk.kel:2:14: 型エラー: module Foo のコンパニオン型 Foo は既存の型 Foo と同名です(module 内の型とトップレベルの型は同名にできません)
  [1]
  $ printf 'module List { pub newtype List = L(Int32) }\necholn("x")\n' > visl.kel
  $ diktor --type-check visl.kel
  ! visl.kel:1:15: 型エラー: module List のコンパニオン型 List は既存の型 List と同名です(module 内の型とトップレベルの型は同名にできません)
  [1]

コンパニオン型は、プレリュードのエフェクト名(Console、Print)も組み込みの
エフェクト名(Heap)も奪えない。型エイリアスでも newtype でも拒否する:

  $ printf 'module Console { pub type Console: EffectRow = {Print} }\n' > viske1.kel
  $ diktor --type-check viske1.kel
  ! viske1.kel:1:18: 型エラー: module Console のコンパニオン型 Console は既存のエフェクト Console と同名です(型とエフェクトは同名にできません)
  [1]
  $ printf 'module Print { pub newtype Print = P(Int32) }\n' > viske2.kel
  $ diktor --type-check viske2.kel
  ! viske2.kel:1:16: 型エラー: module Print のコンパニオン型 Print は既存のエフェクト Print と同名です(型とエフェクトは同名にできません)
  [1]
  $ printf 'module Heap { pub type Heap: EffectRow = {Print} }\n' > viske3.kel
  $ diktor --type-check viske3.kel
  ! viske3.kel:1:15: 型エラー: module Heap のコンパニオン型 Heap は既存のエフェクト Heap と同名です(型とエフェクトは同名にできません)
  [1]

トップレベルのパターン束縛の束縛子も同名禁止の対象(M16 検証。
binding_name は PVar しか見ないので、let (a, b) = … の a がすり抜けて
型検査と実行が別の実体を選んだ):

  $ cat > visp.kel <<'KEL'
  > module M {
  >   let a(): Int32 = 1
  >   pub let go(): Int32 = a()
  > }
  > let (a, b) = (fn() => 99, "x")
  > echoln(show(M.go()))
  > KEL
  $ diktor --type-check visp.kel
  ! visp.kel:2:3: 型エラー: module M の a はトップレベルの a と同名です(module 内の名前とトップレベル名は同名にできません)
  [1]

newtype の型名とコンストラクタは可視性を共有する(§13。pub なら両方公開。
型名だけ公開して表現を隠す手段はまだ無い):

  $ cat > vispub.kel <<'KEL'
  > module M {
  >   pub newtype Pub = Q(Int32)
  > }
  > let x = M.Q(1)
  > let y(v: M.Pub): Int32 = v match { case M.Q(n) => n }
  > KEL
  $ diktor --type-check vispub.kel
  x : M.Pub
  y : (M.Pub) => Int32

  $ printf 'module M { newtype Priv = P(Int32) }\nlet f(v: M.Priv): Int32 = 1\n' > vispriv.kel
  $ diktor --type-check vispriv.kel
  ! vispriv.kel:2:10: 型エラー: 型 M.Priv は module M の外からは参照できません(pub を付けてください)
  [1]

組み込みの修飾名は module 宣言で奪えない(D141 / P18)。診断は宣言の位置を
指す:

  $ cat > visbi.kel <<'KEL'
  > module MutableArray {
  >   pub let set[A](a: A, i: Int32, x: A): Unit = {}
  > }
  > KEL
  $ diktor --type-check visbi.kel
  ! visbi.kel:2:3: 型エラー: module MutableArray の set は組み込みの MutableArray.set と同名です(組み込みの名前は宣言できません)
  [1]
  $ printf 'module Ref { pub let new[A](x: A): Int32 = 0 }\n' > visbi2.kel
  $ diktor --type-check visbi2.kel
  ! visbi2.kel:1:14: 型エラー: module Ref の new は組み込みの Ref.new と同名です(組み込みの名前は宣言できません)
  [1]

module 名そのものは予約しない。組み込みに無い綴りを同じ module 名の下に
足すのは通る:

  $ printf 'module Array { pub let sum(a: Array[Int32]): Int32 = 0 }\n' > visbi3.kel
  $ diktor --type-check visbi3.kel
  Array.sum : (Array[Int32]) => Int32
  $ printf 'module Ref { pub let swap[A](a: Ref[A, Int32]): Int32 = 0 }\n' > visbi4.kel
  $ diktor --type-check visbi4.kel
  Ref.swap : (Ref[A, Int32]) => Int32

--prelude で差し替えたプレリュードも、ユーザのプログラムと同じに拒否される。
平坦化は in_prelude のフラグが立つ前に走るので、プレリュードだからという免除が
効かないためである(§11.42)。診断はプレリュード側のファイルと位置を指す:

  $ printf 'module Ref { pub let new[A](x: A): Int32 = 0 }\n' > visbipre.kel
  $ printf 'let f(): Int32 = 0\n' > visbiuse.kel
  $ diktor --prelude visbipre.kel --type-check visbiuse.kel
  ! visbipre.kel:1:14: 型エラー: module Ref の new は組み込みの Ref.new と同名です(組み込みの名前は宣言できません)
  [1]
