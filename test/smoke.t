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

最小の正常終了:

  $ echo 'let x = 1' > t.kel
  $ diktor t.kel; echo "exit: $?"
  exit: 0

未実装は exit 4(仕様にあって v0 が実装していないもの。§16.8):

  $ echo 'let x = 1u8' > u8.kel
  $ diktor u8.kel; echo "exit: $?"
  ! 未実装: 数値接尾辞 1u8(v0 は i32/i64/f64 のみ)
  exit: 4
