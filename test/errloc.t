型エラーの位置(E1 / D53)。形は ! ファイル:行:桁: 型エラー: 本文。
桁は行頭からのコードポイント差 + 1(E3。バイト差ではない)。

代表 3 ケース(位置は計画 260829-4 §7 で ¤ 置換の字句エラーと突き合わせて
実測検証済み):

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
  ! c5.kel:1:1: 型エラー: type class のパラメータは1個です(多パラメータ型クラスは意図的に排除、sample.kel:275)
  [1]

前方参照シグネチャ(パス 1c)は位置つきエラーも握り潰す(§11.37 の回帰。
節を足し忘れると 1c が先に報告して a : Int32 の行が消える):

  $ cat > sig.kel <<'KEL'
  > let a = 1
  > let g(x: Int32): Nope @ {} = x
  > KEL
  $ diktor --type-check sig.kel
  a : Int32
  ! sig.kel:2:18: 型エラー: 未知の型: Nope
  [1]

桁はコードポイント差(E3)。多バイト文字を含む行と ASCII だけの行で、
同じ位置の誤りが同じ桁に出る:

  $ printf 'let bad = { "\xe3\x81\x82\xe3\x81\x84\xe3\x81\x86"; nosuch }\n' > mb1.kel
  $ diktor --type-check mb1.kel
  ! mb1.kel:1:20: 型エラー: 未束縛の変数: nosuch
  [1]

  $ printf 'let bad = { "abc"; nosuch }\n' > mb2.kel
  $ diktor --type-check mb2.kel
  ! mb2.kel:1:20: 型エラー: 未束縛の変数: nosuch
  [1]

字句エラーの桁も同じ定義(この性質は Utf8 デコーダの差し替えで静かに
壊れうるので、両系統をここに固定する):

  $ printf 'let bad = { "\xe3\x81\x82\xe3\x81\x84\xe3\x81\x86"; \xc2\xa4 }\n' > mb3.kel
  $ diktor --type-check mb3.kel
  mb3.kel:1:20: 字句エラー: unexpected character: ¤
  [2]

  $ printf 'let bad = { "abc"; \xc2\xa4 }\n' > mb4.kel
  $ diktor --type-check mb4.kel
  mb4.kel:1:20: 字句エラー: unexpected character: ¤
  [2]
