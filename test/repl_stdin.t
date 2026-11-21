対話的な実行(--repl)で標準入力を読めないときは、
`diktor: 標準入力を読めません: ` に理由(OS のエラーメッセージ)を続けた行を標準エラーに出し、終了コード 74 で終了する。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

標準入力を閉じたとき:

  $ diktor --repl <&-
  diktor: 標準入力を読めません: Bad file descriptor
  [74]

標準入力がディレクトリのとき(cram の作業ディレクトリを渡す):

  $ diktor --repl < .
  diktor: 標準入力を読めません: Is a directory
  [74]
