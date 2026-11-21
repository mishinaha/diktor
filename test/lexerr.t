字句エラーのメッセージは日本語で、エラーの位置を伴う。
ファイルを読み込むときは終了コード 2 で終了し、対話的な実行(REPL)ではセッションが続く。
このファイルは、tokens.t、run_exit.t、errloc.t が固定していない字句エラーを固定する。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

\u と \U の後の 16 進数の桁が足りない場合:

  $ printf 'let s = "\\u12"\n' > short.kel
  $ diktor short.kel
  short.kel:1:14: 字句エラー: Unicode エスケープの 16 進の桁が足りません
  [2]
  $ printf 'let s = "\\U0011"\n' > shortU.kel
  $ diktor shortU.kel
  shortU.kel:1:16: 字句エラー: Unicode エスケープの 16 進の桁が足りません
  [2]

バックスラッシュの直後でファイルが終わる場合は、閉じていない文字列ではなく、不正なエスケープのエラーになる:

  $ printf 'let s = "\\' > esceof.kel
  $ diktor esceof.kel
  esceof.kel:1:11: 字句エラー: 不正なエスケープです
  [2]

ブロックコメントが閉じていない場合:

  $ printf 'let a = 1 /* abc' > untermc.kel
  $ diktor untermc.kel
  untermc.kel:1:17: 字句エラー: ブロックコメントが閉じていません
  [2]

#! がファイルの先頭以外にある場合:

  $ printf 'let a = 1\n#!x\n' > stray.kel
  $ diktor stray.kel
  stray.kel:2:1: 字句エラー: #! はファイルの先頭にだけ書けます
  [2]

対話的な実行では、閉じていないブロックコメントと文字列リテラルは、次の行に続くものとして読む。
不正なエスケープはエラーとして報告し、次の入力に進む:

  $ printf '/* a\nb */ echoln("ok")\nlet s = "x\ny"\necholn(s)\nlet a = "\\q"\necholn("next")\n' | diktor --repl
  ok
  s : String = "x\ny"
  x
  y
  <stdin>:6:11: 字句エラー: 不正なエスケープです
  next
