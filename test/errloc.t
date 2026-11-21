型エラーの位置のテストである。診断は「! ファイル:行:桁: 型エラー: 本文」の形式で出る。
桁は、行頭からのコードポイント数に 1 を足したもので、バイト数から求めたものではない(第16章 §16.3)。

代表的な 3 つの場合として、演算子の式、未束縛の変数、宣言の先頭の位置を確かめる。期待出力の位置は、
同じ位置に ¤ を置いたときの字句エラーの位置と一致することを確かめてある:

  $ cat > op.kel <<'KEL'
  > let a = 1
  > let bad =
  >   1 + true
  > let c = 2
  > KEL
  $ diktor --type-check op.kel
  a : Int32
  ! op.kel:3:3: 型エラー: Boolean は Add のインスタンスではありません
  [1]

  $ printf 'let f(x: Int32): Int32 = helper(x)\n' > unbound.kel
  $ diktor --type-check unbound.kel
  ! unbound.kel:1:26: 型エラー: 未束縛の変数: helper
  [1]

  $ printf 'type class C5[A, B] { val f: (A) => B }\n' > c5.kel
  $ diktor --type-check --no-prelude c5.kel
  ! c5.kel:1:1: 型エラー: type class のパラメータは1個です(多パラメータ型クラスは意図的に排除、sample.kel:356)
  [1]

前方参照のシグネチャを登録するパス 1c は、位置付きの型エラーも報告せずに捨てる(第11章 §11.37)。
捨てなければ、1c が g の注釈のエラーを先に報告し、a : Int32 の行が出力されなくなる:

  $ cat > sig.kel <<'KEL'
  > let a = 1
  > let g(x: Int32): Nope @ {} = x
  > KEL
  $ diktor --type-check sig.kel
  a : Int32
  ! sig.kel:2:18: 型エラー: 未知の型: Nope
  [1]

桁はコードポイント数で数える。マルチバイト文字を含む行と ASCII だけの行で、
同じ位置のエラーが同じ桁になる:

  $ printf 'let bad = { "\xe3\x81\x82\xe3\x81\x84\xe3\x81\x86"; nosuch }\n' > mb1.kel
  $ diktor --type-check mb1.kel
  ! mb1.kel:1:20: 型エラー: 未束縛の変数: nosuch
  [1]

  $ printf 'let bad = { "abc"; nosuch }\n' > mb2.kel
  $ diktor --type-check mb2.kel
  ! mb2.kel:1:20: 型エラー: 未束縛の変数: nosuch
  [1]

字句エラーの桁も同じ定義である。UTF-8 のデコーダを替えると、この性質は気付かないうちに
崩れることがあるので、型エラーと字句エラーの両方をここで固定する:

  $ printf 'let bad = { "\xe3\x81\x82\xe3\x81\x84\xe3\x81\x86"; \xc2\xa4 }\n' > mb3.kel
  $ diktor --type-check mb3.kel
  mb3.kel:1:20: 字句エラー: 予期しない文字です: ¤
  [2]

  $ printf 'let bad = { "abc"; \xc2\xa4 }\n' > mb4.kel
  $ diktor --type-check mb4.kel
  mb4.kel:1:20: 字句エラー: 予期しない文字です: ¤
  [2]
