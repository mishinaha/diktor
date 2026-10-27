対話的な実行で、トップレベルの値と同名の値を持つ前の入力の module が複数あるときの診断(LangSpec §6.6)。
診断は、宣言の順や表をたどる順に依らず、名前の最も小さい module を挙げる。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

module B、A、C の順に宣言しても、診断は module A を挙げる:

  $ diktor --repl <<'EOF2'
  > module B { pub let v: Int32 = 1 }
  > module A { pub let v: Int32 = 2 }
  > module C { pub let v: Int32 = 3 }
  > let v = 4
  > EOF2
  B.v : Int32 = 1
  A.v : Int32 = 2
  C.v : Int32 = 3
  ! <stdin>:4:1: 型エラー: トップレベルの v は、前の入力の module A の v と同名です(module 内の名前とトップレベル名は同名にできません)

module M0、M2 の順でも、診断は module M0 を挙げる:

  $ diktor --repl <<'EOF2'
  > module M0 { pub let v: Int32 = 1 }
  > module M2 { pub let v: Int32 = 2 }
  > let v = 3
  > EOF2
  M0.v : Int32 = 1
  M2.v : Int32 = 2
  ! <stdin>:3:1: 型エラー: トップレベルの v は、前の入力の module M0 の v と同名です(module 内の名前とトップレベル名は同名にできません)
