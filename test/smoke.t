入力ファイルなしは使用法エラー(exit 64):

  $ diktor 2>&1 | head -1
  diktor: no input files
  $ diktor; echo "exit: $?"
  diktor: no input files
  usage: diktor [OPTIONS] FILE.kel...
    --type-check         型検査のみ。トップレベル束縛の型を "name : type" で出力
    --dump-tokens        ASI 適用後のトークン列を出力
    --dump-ast           脱糖後の AST を S 式で出力
    --no-prelude / --prelude PATH
    --strict-exhaustive  網羅性・到達不能警告をエラー化
  exit: 64

未実装モードは exit 4:

  $ echo 'let x = 1' > t.kel
  $ diktor t.kel; echo "exit: $?"
  未実装: プレリュード(M8 で実装。--no-prelude を使ってください)
  exit: 4
