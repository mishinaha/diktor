仕様が明示的に保留した項目の現状を見張る(D109)。**このファイルは diktor の
意図した挙動ではなく、仕様 §14 が TODO として保留した項目の「現状」を機械に
見張らせるためにある。** 仕様が裁定を下したらここが最初に鳴り、鳴った
ブロックの見出しが仕様の行と関係する章を教える。裁定が下りた項目の観測点は
削らず、意図した挙動のゴールデンとして通常の回帰テストへ移す。
仕様が TODO ではなく制限として書いた項目(LangSpec §13.2 の使用時の開きの
順序依存、付録 A.8 の操作とエフェクトの型パラメータ)の現状も、同じ扱いで末尾の節に
置いて見張る。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

来歴: 2026-09-12 の仕様改訂で doc/log/260830-1-m20.md §1 の台帳 10 項目のうち
8 項目が確定した(行き先の一覧は doc/log/260912-3-sync.md §3)。ここにあった
Array 系 4 ブロック(arrayhole / eachheap / eachpure / eachclosed)は
test/region.t へ(M24)、cancelre は test/eval.t の cancelouter / cancelnores へ
(M21)、tupledefault は削除(観測点は test/typecheck.t の resugar と
test/typecheck_sample.t が持つ。M25)。2026-09-19 の改訂で §14 の TODO は
12 件から 14 件になった。増えた 2 件は、リージョンの専用カインド(§14:877-878。
現状は台帳 V21 として test/kinds.t の regionkind2 が見張る)と、型パラメータの
カインド注記(§14:879-881。注記構文は入れないと決めたので観測点は無い — D124)。
§13.2 の単純化で「非 pub の let で、本体は純粋、呼び出しはどの行からでも可、を注釈で
書く手段」の TODO が決着し、13 件になった(観測点は test/annot_rows.t の sumgen と
sumclosed へ移した)。以下は 13 件のうち、このファイルが観測点を置く 3 件。Chan の署名(§14:866)、
module の入れ子(:867)、Ord[Float64] / Eq[Float64] と NaN(:868-873)は cram では
観測できないので記録のみ。

非有限値(NaN、無限大)のリテラル(§14:874、§2)。現状は無く、文字列化の字面
nan / inf は読み戻せない(表示側は test/numeric.t の infnan):

  $ printf 'let x: Float64 = nan\n' > nanlit.kel
  $ diktor --type-check nanlit.kel
  ! nanlit.kel:1:18: 型エラー: 未束縛の変数: nan
  [1]

整数算術の桁あふれ(§14:875、§2)。現状は wrap-around で、実行時エラーにする
案が仕様に残っている(変換の実行時エラーとの対比は test/numeric.t の cvbig):

  $ cat > wrap.kel <<'KEL'
  > let maxi = 2147483647
  > let mini = 0 - maxi - 1
  > echoln(show(maxi + 1))
  > echoln(show(mini - 1))
  > echoln(show(maxi * 2))
  > echoln(show(9223372036854775807i64 + 1i64))
  > KEL
  $ diktor wrap.kel
  -2147483648
  2147483647
  -2
  -9223372036854775808

不変配列の生成手段(§14:876、§10)。現状は MutableArray.freeze だけで、リテラルも
Array.new も無い(freeze の側は test/region.t の freeze / nonew):

  $ printf 'let mk(): Array[Int32] = run h { Array.new(3, 0) }\n' > nonew.kel
  $ diktor --type-check nonew.kel
  ! nonew.kel:1:34: 型エラー: 未束縛の変数: Array.new
  [1]
  $ printf 'let xs: Array[Int32] = [1, 2, 3]\n' > arrlit.kel
  $ diktor --type-check arrlit.kel
  arrlit.kel:1:24: パースエラー(付近のトークンを確認してください)
  [2]

使用時の開きの順序依存(LangSpec §13.2 の制限の 2 つ目)。使用の時点で関数の行や
要求する側の型がまだ決まっていないときは開かずに一致させ、その使用で決まった行が
その後の使用に効く。そのため、文や実引数の順序によって受理されるかどうかが変わる。

注釈のない引数 f を先に呼ぶと、f の行は本体の行と同じ変数になり、その後でリストに
r.k(閉じた @ {})と並べたときにその変数が {} に決まるので、本体の echoln が落ちる。
リストに入れてから呼べば、f の行は先に {} に決まり、呼ぶときに開くので通る:

  $ cat > orderfirst.kel <<'KEL'
  > let h = fn(f, r: {k: () => Unit}) => {
  >   f()
  >   let xs = Cons(f, Cons(r.k, Nil))
  >   echoln("x")
  > }
  > KEL
  $ diktor --type-check orderfirst.kel
  ! orderfirst.kel:4:3: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ cat > orderlist.kel <<'KEL'
  > let h = fn(f, r: {k: () => Unit}) => {
  >   let xs = Cons(f, Cons(r.k, Nil))
  >   f()
  >   echoln("x")
  > }
  > KEL
  $ diktor --type-check orderlist.kel
  h : (() => {} @ {}, {k: () => {} @ {}}) => {} @ {Console extends R1}

構文上の値でない初期化式を持ち、注釈の最外の @ を省略した値束縛 g は一般化しない
ので、行は最初の呼び出しで決まる。perform ask() と同じ式の中で先に呼ぶと g の行に
Ask が入り、後の Console の文脈からの呼び出しが落ちる(逆の順序は
test/verify_fixes.t の vrgen が通す):

  $ cat > ordervr.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let idf[A](x: A): A = x
  > let main(): Unit @ {Console} = {
  >   let g: (Int32) => Int32 = idf(fn(x) => x + 1)
  >   let b = (g(2) + perform ask()) handle {
  >     case ask() => resume(10)
  >     case return(x) => x
  >   }
  >   let a = g(1)
  >   echoln(show(a + b))
  > }
  > main()
  > KEL
  $ diktor --type-check ordervr.kel
  idf : (A) => A
  ! ordervr.kel:9:11: 型エラー: ラベル Ask がありません(行は閉じています)
  [1]

型変数の仮引数に名前の参照 b と名前の参照でない式 mkp() を並べて渡すとき、先の b で
型変数が矢印に決まれば、mkp() の位置は関数型を要求する位置になって開く。mkp() を
先に置くと型変数が閉じた {} の矢印に決まり、後の b と一致しない:

  $ cat > orderargs1.kel <<'KEL'
  > let mkp(): () => Int32 = fn() => 1
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let pick[A](c: Boolean, x: A, y: A): A = c match { case true => x case false => y }
  > let use(): Int32 @ Console = pick(true, b, mkp())()
  > KEL
  $ diktor --type-check orderargs1.kel
  mkp : () => () => Int32 @ {}
  b : () => Int32 @ {Console}
  pick : (Boolean, A, A) => A
  use : () => Int32 @ {Console}
  $ cat > orderargs2.kel <<'KEL'
  > let mkp(): () => Int32 = fn() => 1
  > let b(): Int32 @ Console = { echo("b"); 2 }
  > let pick[A](c: Boolean, x: A, y: A): A = c match { case true => x case false => y }
  > let use(): Int32 @ Console = pick(true, mkp(), b)()
  > KEL
  $ diktor --type-check orderargs2.kel
  mkp : () => () => Int32 @ {}
  b : () => Int32 @ {Console}
  pick : (Boolean, A, A) => A
  ! orderargs2.kel:4:48: 型エラー: ラベル Console がありません(行は閉じています)
  [1]

操作とエフェクトの型パラメータ(LangSpec 付録 A.8)。所有者が後で許すかどうかを
決める形として見張る(doc/log/261009-3-proposal.md の判断 9-9)。eff_op は typarams を
持たないので、操作の型パラメータはパースエラーになる:

  $ cat > effopparam.kel <<'KEL'
  > effect E = { op[A]: (A) => A }
  > KEL
  $ diktor --type-check effopparam.kel
  effopparam.kel:1:16: パースエラー(付近のトークンを確認してください)
  [2]

エフェクトの宣言の typarams は文法が受け、型検査が拒む(§13.1):

  $ cat > effparam.kel <<'KEL'
  > effect E[A] = { op: (A) => A }
  > KEL
  $ diktor --type-check effparam.kel
  ! effparam.kel:1:1: 型エラー: effect 宣言に型パラメータは書けません(sample.kel §9)
  [1]
