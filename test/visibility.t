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
