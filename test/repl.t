対話的な実行(--repl。LangSpec §6.6)。入力は標準入力から読み、標準入力が端末でないので
プロンプトは出ない。結果、診断、プログラムの出力は、すべて標準出力に出る。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

前の入力の束縛を次の入力で使え、同じ名前の再束縛は、前の束縛を捕捉した関数に影響しない:

  $ diktor --repl <<'EOF2'
  > let a = 1
  > let geta(): Int32 = a
  > let a = "s"
  > a
  > geta()
  > EOF2
  a : Int32 = 1
  geta : () => Int32 = <fn>
  a : String = "s"
  _ : String = "s"
  _ : Int32 = 1

型エラーの入力は、単一化の結果も含めて全部戻る。
f の弱い型変数 _A は、失敗した入力の中で Int32 に決まったが、次の入力では String に決められる:

  $ diktor --repl <<'EOF2'
  > let id[A](x: A): A = x
  > let f = id(fn(y) => y)
  > let g = f(1); let bad = 1 + "a"
  > f("a")
  > g
  > EOF2
  id : (A) => A = <fn>
  f : (_A) => _A = <fn>
  ! <stdin>:3:25: 型エラー: String は Integral のインスタンスではありません
  _ : String = "a"
  ! <stdin>:5:1: 型エラー: 未束縛の変数: g

型エラーの入力の宣言は表に残らない。打ち直した newtype が通る:

  $ diktor --repl <<'EOF2'
  > newtype T = A | Nil
  > newtype T = A | B
  > B
  > newtype T = C
  > EOF2
  ! <stdin>:1:1: 型エラー: コンストラクタ Nil が二重に宣言されています(コンストラクタ名はファイルの中で一意)
  _ : T = B
  ! <stdin>:4:1: 型エラー: newtype T が二重に宣言されています

実行時エラーの入力は、入力の単位で戻る。同じ入力の中で先に済んだ束縛も残らない:

  $ diktor --repl <<'EOF2'
  > let a = 2
  > let a = 3; let z = 5; echoln("before"); 1 / 0
  > a
  > z
  > EOF2
  a : Int32 = 2
  before
  実行時エラー: ゼロ除算です
  _ : Int32 = 2
  ! <stdin>:4:1: 型エラー: 未束縛の変数: z

括弧や文字列の途中なら続きの行を待つ。パースが通った時点で入力が終わるので、
次の行の and は続きにならない:

  $ diktor --repl <<'EOF2'
  > let h(n: Int32): Int32 = {
  >   n * 2
  > }
  > h(21)
  > "a
  > b"
  > let rec ev(n: Int32): Boolean = n == 0 || od(n - 1)
  > and od(n: Int32): Boolean = n != 0 && ev(n - 1)
  > EOF2
  h : (Int32) => Int32 = <fn>
  _ : Int32 = 42
  _ : String = "a\nb"
  ! <stdin>:7:43: 型エラー: 未束縛の変数: od
  <stdin>:8:1: パースエラー(付近のトークンを確認してください)

println はトップレベルで使える。Print はランタイムのハンドラが標準出力へつなぐ:

  $ diktor --repl <<'EOF2'
  > println("hello")
  > with_stdout(fn() => println("inner"))
  > EOF2
  hello
  inner

Ref は入力をまたいで持てない(§13.7):

  $ diktor --repl <<'EOF2'
  > let r = run h { Ref.new(0) }
  > EOF2
  ! <stdin>:1:9: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています

:type は、式を let の右辺と同じ規則で一般化した型を表示する。値でない式の型変数は弱い型変数のまま
表示する。:reset の後は、前の束縛が残らない:

  $ diktor --repl <<'EOF2'
  > :type fn(a) => a
  > let id[A](x: A): A = x
  > :type id
  > :type id(None)
  > :type       zzz
  > let x = 1
  > :reset
  > x
  > EOF2
  (A) => A
  id : (A) => A = <fn>
  (A) => A
  Option[_A]
  ! <stdin>:5:13: 型エラー: 未束縛の変数: zzz
  x : Int32 = 1
  ! <stdin>:8:1: 型エラー: 未束縛の変数: x

前の入力の module の中の値と同じ名前のトップレベルの値は、入力の順によらず拒否する。
ファイルでは同じ組み合わせを平坦化が拒否する:

  $ diktor --repl <<'EOF2'
  > module M { let foo: Int32 = 2; pub let g(): Int32 = foo }
  > let foo = "s"
  > M.g()
  > let bar = 1
  > module N { let bar: Int32 = 2 }
  > EOF2
  M.foo : Int32 = 2
  M.g : () => Int32 = <fn>
  ! <stdin>:2:1: 型エラー: トップレベルの foo は、前の入力の module M の foo と同名です(module 内の名前とトップレベル名は同名にできません)
  _ : Int32 = 2
  bar : Int32 = 1
  ! <stdin>:5:12: 型エラー: module N の bar はトップレベルの bar と同名です(module 内の名前とトップレベル名は同名にできません)

後の入力で宣言したクラスのメソッドは、同じ名前の既存の束縛を覆わない(型検査の先勝ちと一致させる):

  $ diktor --repl <<'EOF2'
  > let sh2 = 1
  > type class S2[X] { val sh2: (X) => Int32 }
  > sh2
  > type instance S2[String] { let sh2(s: String): Int32 = 7 }
  > S2.sh2("a")
  > EOF2
  sh2 : Int32 = 1
  _ : Int32 = 1
  _ : Int32 = 7

後の入力で宣言したクラスのメソッドを、非修飾名で呼べる。型検査と評価が同じ実体を選ぶ:

  $ diktor --repl <<'EOF2'
  > type class Sz[X] { val sz: (X) => Int32 }
  > type instance Sz[String] { let sz(s: String): Int32 = 3 }
  > sz("abc")
  > Sz.sz("abc")
  > EOF2
  _ : Int32 = 3
  _ : Int32 = 3

インスタンスを宣言した入力が実行時エラーで落ちると、そのインスタンスも残らない(クラスは前の入力の宣言なので残る):

  $ diktor --repl <<'EOF2'
  > type class Tg[X] { val tg: (X) => Int32 }
  > type instance Tg[Int32] { let tg(x: Int32): Int32 = 1 }; 1 / 0
  > tg(5)
  > EOF2
  実行時エラー: ゼロ除算です
  ! <stdin>:3:1: 型エラー: Int32 は Tg のインスタンスではありません

Show のインスタンスを持つ newtype の値は Show.show で表示し、持たない値は構造に沿って表示する:

  $ diktor --repl <<'EOF2'
  > newtype Pt = Pt(Int32, Int32)
  > type instance Show[Pt] { let show(p) = p match { case Pt(x, y) => "<" + show(x) + "," + show(y) + ">" } }
  > Pt(1, 2)
  > newtype Q = Q(Int32)
  > Q(3)
  > EOF2
  _ : Pt = <1,2>
  _ : Q = Q(3)

--no-prelude では、利用者が宣言した Print はトップレベルの行に載らない:

  $ diktor --no-prelude --repl <<'EOF2'
  > effect Print = { print: (Int32) => Int32 }
  > perform print(1)
  > EOF2
  ! <stdin>:2:1: 型エラー: エフェクト Print をここでは実行できません(ラベル Print がありません(行は閉じています))

入力の途中で標準入力が終わると、そう報告して終わる:

  $ printf 'let x = (1 +\n' | diktor --repl
  <stdin>: 入力が途中で終わっています


1 入力の中で同じ名前を束縛し直しても、それぞれの束縛を自分の型で表示する:

  $ diktor --repl <<'EOF2'
  > let a = 1; let a = "s"
  > let r = {x = 1}; let r = Some(2)
  > EOF2
  a : Int32 = 1
  a : String = "s"
  r : {x: Int32} = {x = 1}
  r : Option[Int32] = Some(2)

結果の表示で Show のインスタンスが実行時エラーを出すと、その入力を取り消し、セッションは続く:

  $ diktor --repl <<'EOF2'
  > newtype Bad = Bad(Int32)
  > type instance Show[Bad] { let show(b) = b match { case Bad(x) => show(x / 0) } }
  > let bb = Bad(1)
  > bb
  > let ok = 3
  > EOF2
  実行時エラー: ゼロ除算です
  ! <stdin>:4:1: 型エラー: 未束縛の変数: bb
  ok : Int32 = 3

コマンドの行末の空白と CR は読み飛ばす。--repl にはファイルを渡せない:

  $ printf 'let x = 1\n:reset  \nx\n:q\r\nlet y = 2\n' | diktor --repl
  x : Int32 = 1
  ! <stdin>:3:1: 型エラー: 未束縛の変数: x
  $ diktor --repl x.kel 2>&1 | head -1
  diktor: --repl takes no input files
  $ diktor --repl x.kel > /dev/null 2>&1
  [64]
