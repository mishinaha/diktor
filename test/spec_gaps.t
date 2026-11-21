仕様が明示的に保留した項目について、現在の動作を固定する。**このファイルが固定するのは、Diktor の
意図した動作ではない。sample.kel の §14 が TODO として保留した項目の、現在の動作である。**
仕様が項目を決めて実装が変わると、このファイルのブロックが最初に失敗し、失敗した
ブロックの説明の行が、仕様の行と関係する節を示す。仕様が決まった項目のブロックは
削除せず、意図した動作のゴールデンテストとして通常の回帰テストに移す。
仕様が TODO ではなく制限として書いた項目(LangSpec §13.2 の使用時に行を開く規則の
順序依存と、付録 A.8 の操作とエフェクトの型パラメータ)の現在の動作も、同じ扱いで末尾の
ブロックに置いて固定する。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

sample.kel の §14 には TODO が 12 件ある。このファイルは、そのうち次の 3 件のブロックを持つ。
非有限値のリテラル(sample.kel:874)、整数算術のオーバーフロー(:875)、不変配列を作る手段(:876)である。
リージョンに専用のカインドを導入するかどうか(:877-878)は、test/kinds.t の regionkind2 が
現在の動作を固定する。型パラメータのカインドを注釈する構文(:879-881)は、構文を追加して
いないので、ブロックを置かない。Chan のシグネチャ(:866)、module の入れ子(:867)、
Ord[Float64] / Eq[Float64] と NaN(:868-873)は、cram のテストでは観測できないので、ブロックを
置かない。spawn に渡すタスクの行(:856)、Nursery の入れ子(:862)、導出規則のマクロ(:864)、
newtype の表現を隠す手段(:865)にも、ブロックはない。
仕様がすでに決めた項目の動作は、次のテストが固定する。
配列についての項目は、test/region.t の bump や eachclosed などが固定する。cancel 節の中の perform が
外側のハンドラに届くことは test/eval.t の cancelouter が、受け取ったハンドラが resume せずに節を抜けたときの
巻き戻しを抑制することは同じファイルの cancelnores が固定する。タプルのラベルが _item であることと、整数リテラルを
Int32 に決めることは、test/typecheck.t の resugar と test/typecheck_sample.t が固定する。@ を省略した値束縛の行と
@ {} と書いた行の違い(LangSpec §13.2)は、test/annot_rows.t の sumgen と sumclosed が固定する。

非有限値(NaN、無限大)のリテラル(sample.kel:874、§2)。現在はリテラルがなく、文字列化した表記
nan と inf は読み戻せない(表示の側は test/numeric.t の infnan):

  $ printf 'let x: Float64 = nan\n' > nanlit.kel
  $ diktor --type-check nanlit.kel
  ! nanlit.kel:1:18: 型エラー: 未束縛の変数: nan
  [1]

整数算術のオーバーフロー(sample.kel:875、§2)。現在は折り返す(2 の補数で下位のビットだけが残る)。実行時エラーにする
案が仕様に残っている(数値変換が実行時エラーになる例は test/numeric.t の cvbig):

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

不変配列を作る手段(sample.kel:876、§10)。現在は MutableArray.freeze だけで、リテラルも
Array.new もない(freeze の側は test/region.t の freeze と nonew):

  $ printf 'let mk(): Array[Int32] = run h { Array.new(3, 0) }\n' > nonew.kel
  $ diktor --type-check nonew.kel
  ! nonew.kel:1:34: 型エラー: 未束縛の変数: Array.new
  [1]
  $ printf 'let xs: Array[Int32] = [1, 2, 3]\n' > arrlit.kel
  $ diktor --type-check arrlit.kel
  arrlit.kel:1:24: 構文エラー: 付近のトークンを確認してください
  [2]

使用時に行を開く規則の順序依存(LangSpec §13.2 の 2 つ目の制限)。使用の時点で関数の行や
要求する側の型がまだ決まっていないときは、行を開かずに一致させ、その使用で決まった行が
その後の使用に影響する。そのため、文や実引数の順序によって、受理されるかどうかが変わる。

注釈のない引数 f を先に呼ぶと、f の行は本体の行と同じ変数になる。その後でリストに
r.k(閉じた @ {})と並べたときにその変数が {} に決まるので、本体の echoln が型エラーになる。
リストに入れてから呼べば、f の行は先に {} に決まり、呼ぶときに行を開くので型検査に通る:

  $ cat > orderfirst.kel <<'KEL'
  > let h = fn(f, r: {k: () => Unit}) => {
  >   f()
  >   let xs = Cons(f, Cons(r.k, Nil))
  >   echoln("x")
  > }
  > KEL
  $ diktor --type-check orderfirst.kel
  ! orderfirst.kel:4:3: 型エラー: ラベル Console がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を伝えるなら行変数を型パラメータに取ってください。§9)
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

初期化式が構文上の値でなく、注釈の最も外側の @ を省略した値束縛 g は一般化しない
ので、行は最初の呼び出しで決まる。perform ask() と同じ式の中で先に呼ぶと g の行に
Ask が入り、その後で、有効なエフェクト行が Console である位置から呼ぶと型エラーになる(逆の順序は
test/verify_fixes.t の vrgen で型検査に通る)。本体が x + 1 のように演算子を使う形では、演算子が
開いた行の末尾の行変数が無名関数の行になり、束縛の終わりに閉じた行に戻るので、同じ順序で呼んでも
型検査に通る(test/builtin_rows.t の bopweak):

  $ cat > ordervr.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let idf[A](x: A): A = x
  > let main(): Unit @ {Console} = {
  >   let g: (Int32) => Int32 = idf(fn(x) => x)
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

型が型変数である仮引数に、名前の参照 b と名前の参照でない式 mkp() を並べて渡す。先の b で
型変数が矢印に決まれば、mkp() の位置は関数型を要求する位置になり、行を開く。mkp() を
先に置くと、型変数が閉じた {} の矢印に決まり、後の b と一致しない:

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

操作とエフェクトの型パラメータ(LangSpec 付録 A.8)。将来許すかどうかは決まっていないので、
現在の動作を固定する。文法の eff_op は typarams を
持たないので、操作の型パラメータは構文エラーになる:

  $ cat > effopparam.kel <<'KEL'
  > effect E = { op[A]: (A) => A }
  > KEL
  $ diktor --type-check effopparam.kel
  effopparam.kel:1:16: 構文エラー: 付近のトークンを確認してください
  [2]

エフェクトの宣言の typarams は、文法上は書けるが、型検査がエラーにする(LangSpec §13.1):

  $ cat > effparam.kel <<'KEL'
  > effect E[A] = { op: (A) => A }
  > KEL
  $ diktor --type-check effparam.kel
  ! effparam.kel:1:1: 型エラー: effect 宣言に型パラメータは書けません(sample.kel §9)
  [1]
