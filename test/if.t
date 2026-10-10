条件式 if e1 then e2 else e3(仕様 §5.8)。Boolean の値に対する 2 節の match の略記で、
構文木のノードを持たない。パーサが case true と case false の 2 節を持つ match に
脱糖するので、型、評価順序、網羅性、末尾位置はすべて match の規則で決まる。

脱糖：if と、同じ 2 節を書いた match は、同じ構文木になる:

  $ cat > desugar.kel <<'KEL'
  > let f(b: Boolean): Int32 = if b then 1 else 2
  > let g(b: Boolean): Int32 = b match { case true => 1 case false => 2 }
  > KEL
  $ diktor --dump-ast desugar.kel
  (dlet
   (binding f (params (pannot b Boolean)) : Int32 =
    (match b (case true => 1) (case false => 2))))
  (dlet
   (binding g (params (pannot b Boolean)) : Int32 =
    (match b (case true => 1) (case false => 2))))

評価。else の枝にも if を書ける:

  $ cat > basic.kel <<'KEL'
  > let sign(n: Int32): Int32 = if n < 0 then 0 - 1 else if n == 0 then 0 else 1
  > echoln(show(sign(0 - 5)))
  > echoln(show(sign(0)))
  > echoln(show(sign(7)))
  > echoln(if true then "yes" else "no")
  > let r = if true then { let y = 2; y * 3 } else { 0 }
  > echoln(show(r))
  > KEL
  $ diktor basic.kel
  -1
  0
  1
  yes
  6

評価順序：条件を 1 回だけ評価し、選んだ枝だけを評価する:

  $ cat > order.kel <<'KEL'
  > let t(s: String, b: Boolean): Boolean = { echoln(s); b }
  > echoln(show(if t("cond", true) then t("then", true) else t("else", false)))
  > echoln(show(if t("cond", false) then t("then", true) else t("else", false)))
  > KEL
  $ diktor order.kel
  cond
  then
  true
  cond
  else
  false

else の枝は右へできるだけ長く取る(仕様 §5.2 の表では fn と同じ段)。
2 + 10 も後置の match も else の枝に入る。if の結果を演算に使うときは括弧で囲む:

  $ cat > prec.kel <<'KEL'
  > echoln(show(if true then 1 else 2 + 10))
  > echoln(show((if true then 1 else 2) + 10))
  > echoln(show(if true then Some(1) else None match { case Some(x) => Some(x + 1) case None => None }))
  > echoln(if 1 < 2 && 2 < 3 then "both" else "not")
  > KEL
  $ diktor prec.kel
  1
  11
  Some(1)
  both

括弧で囲まない if は、演算子のオペランドに書けない:

  $ printf 'let g = 1 + if true then 1 else 2\n' > operand.kel
  $ diktor operand.kel
  operand.kel:1:13: パースエラー(付近のトークンを確認してください)
  [2]

else は省略できない。改行が文を区切った位置で else を待っていたことが、
パースエラーの位置で分かる:

  $ cat > noelse.kel <<'KEL'
  > let f(b: Boolean): Unit = {
  >   if b then echoln("x")
  >   echoln("y")
  > }
  > KEL
  $ diktor noelse.kel
  noelse.kel:2:24: パースエラー(付近のトークンを確認してください)
  [2]

改行：then と else で始まる行と、then と else で終わる行は、前後の行に続く。
if で始まる行は新しい文を始める:

  $ cat > newline.kel <<'KEL'
  > let pick(n: Int32): String =
  >   if n > 0
  >   then "pos"
  >   else "nonpos"
  > let pick2(n: Int32): String = {
  >   let k = n * 2
  >   if k > 10 then
  >     "big"
  >   else if k > 0 then
  >     "small"
  >   else
  >     "none"
  > }
  > echoln(pick(1))
  > echoln(pick(0))
  > echoln(pick2(6))
  > echoln(pick2(1))
  > echoln(pick2(0))
  > let x = 1
  > if x == 1 then echoln("one") else echoln("other")
  > echoln("after")
  > KEL
  $ diktor newline.kel
  pos
  nonpos
  big
  small
  none
  one
  after
  $ printf 'let x = 1\nif x == 1\nthen 2\nelse 3\n' > tok.kel
  $ diktor --dump-tokens tok.kel
     1  let
     1  x
     1  =
     1  1
     1  <NL>
     2  if
     2  x
     2  ==
     2  1
     3  then
     3  2
     4  else
     4  3
     5  <EOF>

対話的な実行でも、then や else で行が終わるか、次の行が then や else で始まれば、
入力を読み続ける:

  $ printf 'let y = if false then\n0\nelse 5\n' | diktor --repl
  y : Int32 = 5

型：条件は Boolean でなければならない。誤りは条件の位置に報告する:

  $ cat > condty.kel <<'KEL'
  > let f(s: String): Int32 =
  >   if s
  >   then 1
  >   else 2
  > KEL
  $ diktor --type-check condty.kel
  ! condty.kel:2:6: 型エラー: 型が一致しません: String と Boolean
  [1]

2 つの枝は同じ型でなければならない。診断は同じ 2 節の match と同じになる:

  $ printf 'let f(b: Boolean) = if b then "one" else b\n' > armty.kel
  $ diktor --type-check armty.kel
  ! armty.kel:1:21: 型エラー: 型が一致しません: Boolean と String
  [1]
  $ printf 'let f(b: Boolean) = b match { case true => "one" case false => b }\n' > armty2.kel
  $ diktor --type-check armty2.kel
  ! armty2.kel:1:21: 型エラー: 型が一致しません: Boolean と String
  [1]

型注釈が無くても、条件は Boolean に、枝は共通の型に推論する:

  $ cat > infer.kel <<'KEL'
  > let choose(b, x, y) = if b then x else y
  > echoln(show(choose(true, 1, 2)))
  > echoln(choose(false, "a", "b"))
  > KEL
  $ diktor infer.kel
  1
  b

網羅性：脱糖した 2 節は網羅的なので、警告を出さない。
対照の 1 節の match には警告が出る:

  $ cat > exhaust.kel <<'KEL'
  > let f(b: Boolean): Int32 = if b then 1 else 2
  > let g(b: Boolean): Int32 = b match { case true => 1 }
  > echoln(show(f(false)))
  > KEL
  $ diktor exhaust.kel
  ⚠ match が非網羅的です。例えば false が漏れています
  2

then と else は予約語で、変数、引数、レコードのラベルに使えない:

  $ printf 'let then = 1\n' > kwthen.kel
  $ diktor kwthen.kel
  kwthen.kel:1:5: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'let f(else: Int32): Int32 = else\n' > kwelse.kel
  $ diktor kwelse.kel
  kwelse.kel:1:7: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'let r = {then = 1}\n' > kwlabel.kel
  $ diktor kwlabel.kel
  kwlabel.kel:1:10: パースエラー(付近のトークンを確認してください)
  [2]

ガードの if と共存する。ガードの中の条件式は、括弧が無くても読める。
ガードの前の改行は、今までどおり節を区切らない:

  $ cat > guard.kel <<'KEL'
  > let classify(n: Int32): String = n match {
  >   case 0 => "zero"
  >   case x if if x < 0 then true else false => "negative"
  >   case x
  >     if x > 100 => if x > 1000 then "huge" else "big"
  >   case _ => "positive"
  > }
  > echoln(classify(0))
  > echoln(classify(0 - 3))
  > echoln(classify(500))
  > echoln(classify(5000))
  > echoln(classify(5))
  > KEL
  $ diktor guard.kel
  zero
  negative
  big
  huge
  positive

2 つの枝に、閉じた行の違う名前付き関数を置ける。
束縛、引数、呼び出し先のどの位置でも、枝の型は合流する:

  $ cat > join.kel <<'KEL'
  > let pure_f(): Unit @ {} = ()
  > let print_f(): Unit @ Console = echoln("p")
  > let call[E](f: () => Unit @ E): Unit @ E = f()
  > let run_it(b: Boolean): Unit @ Console = {
  >   let g = if b then pure_f else print_f
  >   g()
  >   call(if b then pure_f else print_f)
  >   (if b then pure_f else print_f)()
  > }
  > run_it(false)
  > run_it(true)
  > echoln("end")
  > KEL
  $ diktor join.kel
  p
  p
  p
  end

末尾位置：then と else の枝は、match の節の本体として末尾位置にある(仕様 §5.7)。
test/tail_calls.t と同じく、OCAMLRUNPARAM=l=100k で上限を絞って 10 万回続ける。
対照の末尾でない再帰は落ちる:

  $ cat > nontail.kel <<'KEL'
  > let rec sum(n: Int32): Int32 = if n == 0 then 0 else n + sum(n - 1)
  > echoln(show(sum(100000)))
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor nontail.kel
  実行時エラー: スタックオーバーフロー(再帰が深すぎます)
  [3]

else の枝と then の枝からの自己再帰、else if を通る相互再帰、else の枝のブロック:

  $ cat > tail.kel <<'KEL'
  > let rec loop(n: Int32, acc: Int32): Int32 = if n == 0 then acc else loop(n - 1, acc + 1)
  > let rec down(n: Int32): Int32 = if n != 0 then down(n - 1) else 0
  > let rec even(n: Int32): Boolean = if n == 0 then true else if n == 1 then false else odd(n - 1)
  > and odd(n: Int32): Boolean = if n == 0 then false else even(n - 1)
  > let rec blk(n: Int32): Unit = {
  >   let m = n - 1
  >   if n == 0 then () else { let k = m; blk(k) }
  > }
  > echoln(show(loop(100000, 0)))
  > echoln(show(down(100000)))
  > echoln(show(even(100000)))
  > blk(100000)
  > echoln("ok")
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor tail.kel
  100000
  0
  true
  ok

操作節の本体の if の枝にある resume は、末尾 resume である:

  $ cat > resume.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > effect Tick = { tick: () => Unit }
  > let rec asks(n: Int32, acc: Int32): Int32 @ Ask =
  >   if n == 0 then acc else asks(n - 1, acc + perform ask(n))
  > let rec ticks(n: Int32): Unit @ Tick = if n == 0 then () else { perform tick(); ticks(n - 1) }
  > echoln(show(asks(100000, 0) handle { case ask(x) => if x > 0 then resume(1) else resume(0) }))
  > ticks(100000) handle { case tick() => { let c = 1; if c == 1 then resume() else resume() } }
  > echoln("ticks")
  > KEL
  $ OCAMLRUNPARAM=l=100k diktor resume.kel
  100000
  ticks
