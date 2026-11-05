対話的な実行(--repl)で標準入力を読めないときは、
diktor: 標準入力を読めません: 理由 を stderr に出し、終了コード 74 で終わる。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

閉じた標準入力:

  $ diktor --repl <&-
  diktor: 標準入力を読めません: Bad file descriptor
  [74]

ディレクトリの標準入力(cram の作業ディレクトリ):

  $ diktor --repl < .
  diktor: 標準入力を読めません: Is a directory
  [74]
