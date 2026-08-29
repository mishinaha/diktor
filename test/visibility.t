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

非修飾の内部型は外から見えない(同義語が module スコープになった。
候補の案内つき):

  $ cat > vis4.kel <<'KEL'
  > module M { newtype Priv = P(Int32) }
  > let u(x: Priv): Int32 = 0
  > KEL
  $ diktor --type-check vis4.kel
  ! vis4.kel:2:10: 型エラー: 未知の型: Priv(M.Priv と修飾してください)
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
