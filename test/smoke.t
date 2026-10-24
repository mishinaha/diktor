入力ファイルなしは使用法エラー(exit 64):

  $ diktor 2>&1 | head -1
  diktor: no input files
  $ diktor; echo "exit: $?"
  diktor: no input files
  usage: diktor [OPTIONS] FILE.kel...
    --type-check         型検査のみ。トップレベル束縛の型を "name : type" で出力
    --dump-tokens        ASI 適用後のトークン列を出力
    --dump-ast           脱糖後の AST を S 式で出力
    --repl               対話的に実行する(FILE は不要)
    --no-prelude / --prelude PATH
    --strict-exhaustive  網羅性・到達不能警告をエラー化
    --import-path DIR    import の検索パスに DIR を足す(繰り返せる)
    --emit-ir-text FILE  型検査の後、実行せずに KIR の正準のテキストを FILE に書く
  exit: 64

最小の正常終了:

  $ echo 'let x = 1' > t.kel
  $ diktor t.kel; echo "exit: $?"
  exit: 0

未実装は exit 4(§16.8)。
cr.kel の case cancel(e) は、付録 A.5 の clause ::= "case" pat の形として構文の上では読める。
LangSpec の cancel 節は case cancel の形だけで、Diktor は case cancel(e) の形を未実装として報告する:

  $ printf 'effect E = { op: () => Int32 }\nlet r = (1) handle { case op() => resume(1) case cancel(e) => () }\n' > cr.kel
  $ diktor cr.kel; echo "exit: $?"
  ! cr.kel:2:50: 未実装: cancel(reason)(v0 は case cancel のみ)
  exit: 4

言語に無い数値の接尾辞は型エラーで exit 1(LangSpec §4.2、§15.5):

  $ echo 'let x = 1u8' > u8.kel
  $ diktor u8.kel; echo "exit: $?"
  ! u8.kel:1:9: 型エラー: 数値リテラル 1u8 の接尾辞 u8 はありません(接尾辞は i32、i64、f64 だけです)
  exit: 1
