実行の開始と終了(LangSpec §15.5)。終了状態は、正常終了 0、型検査での拒否と import の
誤り 1、字句と構文の誤り 2、実行時エラー 3 である。プログラムを実行するとき、診断と
警告は標準エラーに出し、実行時エラーの前に標準出力へ書いた内容は残す。診断の文面
そのものは各機能のテストが持つ。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

正常終了は 0。起点の初期化(§15.4)を終えたら終わる:

  $ cat > exitok.kel <<'KEL'
  > echoln("hello")
  > let x = 1 + 2
  > echoln(show(x))
  > KEL
  $ diktor exitok.kel; echo "exit: $?"
  hello
  3
  exit: 0

型検査で拒否したプログラムは 1。初期化を始めないので、型エラーより前の式文も
評価せず、標準出力は空である。診断は標準エラーに出る:

  $ cat > exittype.kel <<'KEL'
  > echoln("before")
  > let x: Int32 = "s"
  > KEL
  $ diktor exittype.kel 2> /dev/null; echo "exit: $?"
  exit: 1
  $ diktor exittype.kel > /dev/null; echo "exit: $?"
  ! exittype.kel:2:5: 型エラー: 注釈された型を満たしません(型が一致しません: Int32 と String)
  exit: 1

import の誤りも 1:

  $ printf 'from "./nosuch" import x\necholn("a")\n' > exitimport.kel
  $ diktor exitimport.kel 2> /dev/null; echo "exit: $?"
  exit: 1
  $ diktor exitimport.kel > /dev/null; echo "exit: $?"
  ! exitimport.kel:1:1: import エラー: import 先が見つかりません: ./nosuch(nosuch.kel)
  exit: 1

構文エラー、字句エラー、不正な UTF-8 のバイト列は 2。どれも初期化を始めない:

  $ printf 'echoln("before")\nlet x = (1 +\n' > exitparse.kel
  $ diktor exitparse.kel 2> /dev/null; echo "exit: $?"
  exit: 2
  $ diktor exitparse.kel > /dev/null; echo "exit: $?"
  exitparse.kel:3:1: パースエラー(付近のトークンを確認してください)
  exit: 2
  $ printf 'echoln("before")\nlet x = "\\q"\n' > exitlex.kel
  $ diktor exitlex.kel 2> /dev/null; echo "exit: $?"
  exit: 2
  $ diktor exitlex.kel > /dev/null; echo "exit: $?"
  exitlex.kel:2:11: 字句エラー: invalid escape sequence
  exit: 2
  $ printf 'echoln("before")\nlet x = "\377"\n' > exitutf8.kel
  $ od -An -tx1 exitutf8.kel
   65 63 68 6f 6c 6e 28 22 62 65 66 6f 72 65 22 29
   0a 6c 65 74 20 78 20 3d 20 22 ff 22 0a
  $ diktor exitutf8.kel 2> /dev/null; echo "exit: $?"
  exit: 2
  $ diktor exitutf8.kel > /dev/null; echo "exit: $?"
  exitutf8.kel: 字句エラー: 不正な UTF-8 バイト列です
  exit: 2

実行時エラーは 3。止まるまでに標準出力へ書いた内容は残り、診断は標準エラーに出る:

  $ cat > exitrt.kel <<'KEL'
  > echo("before ")
  > echoln("line")
  > let z = 0
  > echoln(show(1 / z))
  > echoln("after")
  > KEL
  $ diktor exitrt.kel 2> /dev/null; echo "exit: $?"
  before line
  exit: 3
  $ diktor exitrt.kel > /dev/null; echo "exit: $?"
  実行時エラー: ゼロ除算です
  exit: 3

標準出力と標準エラーを 1 本にまとめると、診断はそれまでの出力の後ろに出る。
実行時エラーの巻き戻しでも cancel 節は走る(§13.6):

  $ cat > exitcancel.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let z = 0
  > echoln("start")
  > let r = (perform ask() / z) handle {
  >   case ask() => resume(1)
  >   case cancel => echoln("cancel ran")
  > }
  > echoln("after")
  > KEL
  $ diktor exitcancel.kel 2>&1; echo "exit: $?"
  start
  cancel ran
  実行時エラー: ゼロ除算です
  exit: 3

警告は型検査の段階で標準エラーに出すので、1 本にまとめるとプログラムの出力より
前に出る。警告があっても実行する(§11.2):

  $ cat > warnrun.kel <<'KEL'
  > echoln("before")
  > let f(n: Int32): String = n match { case 0 => "zero" }
  > echoln(f(0))
  > KEL
  $ diktor warnrun.kel 2> /dev/null; echo "exit: $?"
  before
  zero
  exit: 0
  $ diktor warnrun.kel > /dev/null; echo "exit: $?"
  ⚠ match が非網羅的です。例えば 1 が漏れています
  exit: 0
  $ diktor warnrun.kel 2>&1; echo "exit: $?"
  ⚠ match が非網羅的です。例えば 1 が漏れています
  before
  zero
  exit: 0

--strict-exhaustive は、警告があれば実行せずに型検査での拒否と同じ 1 で終わる:

  $ diktor --strict-exhaustive warnrun.kel 2> /dev/null; echo "exit: $?"
  exit: 1
  $ diktor --strict-exhaustive warnrun.kel 2>&1; echo "exit: $?"
  ⚠ match が非網羅的です。例えば 1 が漏れています
  exit: 1

初期化前の呼び出し(§6.4)。完全な署名を持つ後ろの関数は型検査に通るが、
初期化の前に呼ぶと実行時エラーで 3 になる:

  $ cat > initcall.kel <<'KEL'
  > let f(): Int32 = g()
  > echoln("before")
  > echoln(show(f()))
  > let g(): Int32 @ {} = 42
  > KEL
  $ diktor initcall.kel 2> /dev/null; echo "exit: $?"
  before
  exit: 3
  $ diktor initcall.kel > /dev/null; echo "exit: $?"
  実行時エラー: 未束縛の変数: g
  exit: 3

インスタンスのメソッドも、インスタンス宣言を実行する前に使うと実行時エラーで 3:

  $ cat > initinst.kel <<'KEL'
  > newtype L(String)
  > type class R[A] { val r: (A) => String }
  > let use(x: L): String = r(x)
  > echoln("before")
  > echoln(use(L("a")))
  > type instance R[L] { let r(x) = x match { case L(s) => s } }
  > KEL
  $ diktor initinst.kel 2> /dev/null; echo "exit: $?"
  before
  exit: 3
  $ diktor initinst.kel > /dev/null; echo "exit: $?"
  実行時エラー: R[L] のインスタンスは宣言より前の位置では使えません(実行はまだ実体を持ちません。インスタンス宣言を使用より前に置いてください)
  exit: 3
