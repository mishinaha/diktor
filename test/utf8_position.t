不正な UTF-8 のバイト列の字句エラーは、不正なバイトの位置を ファイル:行:桁 で示す。
桁は行頭からのコードポイントの数に 1 を足したもので、終了状態は 2 である。

文字列の中、識別子の途中、行コメントの中のどこでも、不正なバイトそのものを指す:

  $ printf 'echoln("before")\nlet x = "\377"\n' > instr.kel
  $ diktor instr.kel; echo "exit: $?"
  instr.kel:2:10: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2
  $ printf 'let ab\377c = 1\n' > inident.kel
  $ diktor inident.kel; echo "exit: $?"
  inident.kel:1:7: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2
  $ printf 'let x = 1 // \377\n' > incomment.kel
  $ diktor incomment.kel; echo "exit: $?"
  incomment.kel:1:14: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2

最初のトークンを読み終える前に不正なバイトに当たっても、ファイル名を示す:

  $ printf '/* \377 */\nlet x = 1\n' > firstblock.kel
  $ diktor firstblock.kel; echo "exit: $?"
  firstblock.kel:1:4: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2
  $ printf '\377\n' > firstbyte.kel
  $ printf 'let x = 1\n' > fine.kel
  $ diktor fine.kel firstbyte.kel; echo "exit: $?"
  firstbyte.kel:1:1: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2

途中で切れた多バイト列と、サロゲートを符号化した 3 バイトは、その先頭のバイトを指す:

  $ printf 'let x = 1\n\343\201' > trunc.kel
  $ diktor trunc.kel; echo "exit: $?"
  trunc.kel:2:1: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2
  $ printf 'let s = "\355\240\200"\n' > surrogate.kel
  $ diktor surrogate.kel; echo "exit: $?"
  surrogate.kel:1:10: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2

前に多バイト文字があっても、桁はコードポイントで数える。
3 バイトの文字 2 つの後ろの不正なバイトは 12 桁目である:

  $ printf 'let s = "\343\201\202\343\201\204\377"\n' > aftermb.kel
  $ diktor aftermb.kel; echo "exit: $?"
  aftermb.kel:1:12: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2

字句解析器は入力を 512 コードポイントずつ読み進める。
その境界をまたいだ先の不正なバイトも、正しい桁を指す:

  $ printf '//%0510d\377\n' 0 > chunk.kel
  $ diktor chunk.kel; echo "exit: $?"
  chunk.kel:1:513: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2

import 先のファイルの誤りは、そのファイルの名前と位置で示す:

  $ printf 'let y = "\377"\n' > badlib.kel
  $ printf 'from "./badlib" import y\necholn("a")\n' > useslib.kel
  $ diktor useslib.kel; echo "exit: $?"
  badlib.kel:1:10: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2

--type-check と --dump-tokens も同じ診断を出す:

  $ diktor --type-check instr.kel; echo "exit: $?"
  instr.kel:2:10: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2
  $ diktor --dump-tokens instr.kel; echo "exit: $?"
  instr.kel:2:10: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2

対話的な実行では、入力の行と桁で示し、セッションは続く。
:type の後ろの式でも、行の中の桁で示す:

  $ printf 'let a = 1\nlet x = "\377"\nlet b = 2\n:type "\377"\n' | diktor --repl
  a : Int32 = 1
  <stdin>:2:10: 字句エラー: 不正な UTF-8 バイト列です
  b : Int32 = 2
  <stdin>:4:8: 字句エラー: 不正な UTF-8 バイト列です
