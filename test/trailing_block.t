末尾ブロック(LangSpec §5.5)。呼び出しの最後の引数として、括弧の外に無名関数を書く。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

3 つの位置(呼び出しの直後、M.f の直後、識別子の直後)と、3 つの中身
({ 文の列 }、{ x => 文の列 }、{ case ... })の組み合わせ。複数行の中身と、
入れ子の末尾ブロックも通る:

  $ cat > ok.kel <<'EOF'
  > let call_with[A, B, E](x: A, f: (A) => B @ E): B @ E = f(x)
  > let after[R, E](msg: String, f: () => R @ {Console extends E}): R @ {Console extends E} = {
  >   echoln(msg)
  >   f()
  > }
  > let twice[E](f: () => Unit @ E): Unit @ E = {
  >   f()
  >   f()
  > }
  > let apply3[R, E](f: (Int32) => R @ E): R @ E = f(3)
  > module M {
  >   pub let call0[R, E](f: () => R @ E): R @ E = f()
  >   pub let apply7[R, E](f: (Int32) => R @ E): R @ E = f(7)
  > }
  > echoln(show(after("call") { 5 }))
  > echoln(show(call_with(20) { x => x + 1 }))
  > echoln(call_with(Some(3)) {
  >   case Some(n) => show(n)
  >   case None => "none"
  > })
  > echoln(show(M.call0 { 1 + 2 }))
  > echoln(show(M.apply7 { x => x * 2 }))
  > echoln(M.apply7 { case 7 => "seven"
  >   case _ => "other" })
  > twice { echoln("twice") }
  > echoln(show(apply3 { x => x * 100 }))
  > echoln(apply3 { case 0 => "zero"
  >   case _ => "nonzero" })
  > echoln(show(call_with(1) { x =>
  >   let y = x + 1
  >   call_with(y) { z => z * 10 }
  > }))
  > EOF
  $ diktor ok.kel
  call
  5
  21
  3
  3
  14
  seven
  twice
  twice
  300
  nonzero
  20

g(1) { k } は 1 個の呼び出しで、引数の行の末尾に関数が加わる。
g(1, fn() => k) と同じ構文木になる。{ x => e } は fn(x) => e になり、
{ case ... } は、利用者が書けない名前 %arg を引数に取る照合関数になる。
g(1)(2) { k } では、末尾ブロックは 2 つ目の呼び出しに加わる:

  $ cat > ast.kel <<'EOF'
  > let a = g(1) { k }
  > let b = g(1, fn() => k)
  > let c = M.f { x => x }
  > let d = M.f(fn(x) => x)
  > let e = f { case Some(y) => y }
  > let h = g(1)(2) { k }
  > EOF
  $ diktor --dump-ast ast.kel
  (dlet (binding a = (apply g (extend _item 1 (extend _item (fn () k) {})))))
  (dlet (binding b = (apply g (extend _item 1 (extend _item (fn () k) {})))))
  (dlet (binding c = (apply M.f (extend _item (fn (x) x) {}))))
  (dlet (binding d = (apply M.f (extend _item (fn (x) x) {}))))
  (dlet
   (binding e =
    (apply f
     (extend _item (fn (%arg) (match %arg (case (pctor Some y) => y))) {}))))
  (dlet
   (binding h =
    (apply (apply g (extend _item 1 {}))
     (extend _item 2 (extend _item (fn () k) {})))))
  $ echo 'let a = %arg' > pct.kel
  $ diktor --type-check pct.kel
  pct.kel:1:9: 字句エラー: unexpected character: %
  [2]

{ case (a, b) => e } はタプル 1 個を受け取る関数で、2 引数の関数ではない
(LangSpec §3.1)。最後の引数が ((A, B)) => R なら通り、(A, B) => R なら
型エラーになる:

  $ cat > tuple1.kel <<'EOF'
  > let apply_pair[A, B, R](p: (A, B), f: ((A, B)) => R): R = f(p)
  > echoln(show(apply_pair((1, 2)) { case (a, b) => a * 10 + b }))
  > EOF
  $ diktor tuple1.kel
  12
  $ cat > tuple2.kel <<'EOF'
  > let apply2(a: Int32, b: Int32, f: (Int32, Int32) => Int32): Int32 = f(a, b)
  > let r = apply2(1, 2) { case (a, b) => a + b }
  > EOF
  $ diktor --type-check tuple2.kel
  apply2 : (Int32, Int32, (Int32, Int32) => Int32) => Int32
  ! tuple2.kel:2:22: 型エラー: 型が一致しません: (_A, _A) と Int32
  [1]

{ case ... } の照合は match と同じ規則で、残りを受ける節が無ければ照合対象の
行を閉じる(LangSpec §11.2)。注釈の無い g の引数は #A | #B に閉じるので、
g(#C) は型エラーになる:

  $ cat > close.kel <<'EOF'
  > let call_with[A, B, E](x: A, f: (A) => B @ E): B @ E = f(x)
  > let g = fn(v) => call_with(v) { case #A => 1
  >   case #B => 2 }
  > echoln(show(g(#A)))
  > echoln(show(g(#C)))
  > EOF
  $ diktor close.kel
  ! close.kel:5:15: 型エラー: ラベル C がありません(行は閉じています)
  [1]

{ _ => e } は書けない。引数のない関数は { e }、引数を捨てる 1 引数の関数は
{ case _ => e } と書く:

  $ echo 'let a = f { _ => 1 }' > wild.kel
  $ diktor --type-check wild.kel
  wild.kel:1:13: 構文エラー: 末尾ブロックの引数に _ は書けません(引数なしは { 式 }、引数を捨てる 1 引数は { case _ => 式 })
  [2]

中身がレコードの形(空の {} を含む)の末尾ブロックはエラーにする。
末尾ブロックは常に関数を渡す:

  $ echo 'let a = f {}' > empty.kel
  $ diktor --type-check empty.kel
  empty.kel:1:11: 構文エラー: 末尾ブロックの中身にレコードの形は書けません(空の {} もレコードです。何もしない関数は { () } と書きます)
  [2]
  $ echo 'let a = g(1) {x = 1}' > rec.kel
  $ diktor --type-check rec.kel
  rec.kel:1:14: 構文エラー: 末尾ブロックの中身にレコードの形は書けません(空の {} もレコードです。何もしない関数は { () } と書きます)
  [2]
  $ echo 'let a = M.f {x,}' > pun.kel
  $ diktor --type-check pun.kel
  pun.kel:1:13: 構文エラー: 末尾ブロックの中身にレコードの形は書けません(空の {} もレコードです。何もしない関数は { () } と書きます)
  [2]

コンストラクタ、構造的ヴァリアント、perform、resume には付けられない。
引数リストのある形は専用の診断になり、引数リストの無い Foo { k } と
#Tag { k } は一般のパースエラーになる:

  $ echo 'let a = Some(1) { k }' > ctor.kel
  $ diktor --type-check ctor.kel
  ctor.kel:1:17: 構文エラー: コンストラクタと構造的ヴァリアントには末尾ブロックを付けられません
  [2]
  $ echo 'let a = #Tag(1) { k }' > tag.kel
  $ diktor --type-check tag.kel
  tag.kel:1:17: 構文エラー: コンストラクタと構造的ヴァリアントには末尾ブロックを付けられません
  [2]
  $ echo 'let a = perform op(1) { k }' > perf.kel
  $ diktor --type-check perf.kel
  perf.kel:1:23: 構文エラー: perform には末尾ブロックを付けられません
  [2]
  $ echo 'let a = resume(1) { k }' > res.kel
  $ diktor --type-check res.kel
  res.kel:1:19: 構文エラー: resume には末尾ブロックを付けられません
  [2]
  $ echo 'let a = Foo { k }' > ctor0.kel
  $ diktor --type-check ctor0.kel
  ctor0.kel:1:13: パースエラー(付近のトークンを確認してください)
  [2]
  $ echo 'let a = #Tag { k }' > tag0.kel
  $ diktor --type-check tag0.kel
  tag0.kel:1:14: パースエラー(付近のトークンを確認してください)
  [2]

末尾ブロックは 1 つの呼び出しに 1 個まで:

  $ echo 'let a = f { 1 } { 2 }' > two.kel
  $ diktor --type-check two.kel
  two.kel:1:17: 構文エラー: 末尾ブロックは 1 つの呼び出しに 1 個までです
  [2]
  $ echo 'let a = g(1) { x => x } { 2 }' > two2.kel
  $ diktor --type-check two2.kel
  two2.kel:1:25: 構文エラー: 末尾ブロックは 1 つの呼び出しに 1 個までです
  [2]

括弧で囲んだ式の後ろには書けない。(g(1)) { k } は g(1) の結果への適用にも、
g(1, fn() => k) にもならず、パースエラーになる:

  $ echo 'let a = (g(1)) { k }' > paren.kel
  $ diktor --type-check paren.kel
  paren.kel:1:16: パースエラー(付近のトークンを確認してください)
  [2]

{ x => ... } と { case ... } は、末尾ブロックの位置の外ではエラーになる。
トップレベルとブロックの中で { を次の行に書くと、改行が文を区切るので、
ここに当たる:

  $ cat > nl1.kel <<'EOF'
  > let a = {
  >   let r = f
  >   { x => x }
  > }
  > EOF
  $ diktor --type-check nl1.kel
  nl1.kel:3:3: 構文エラー: { x => ... } と { case ... } は末尾ブロックとしてだけ書けます(呼び出しの直後の同じ行に置くか、fn(x) => ... と書きます)
  [2]
  $ cat > nl2.kel <<'EOF'
  > let a = {
  >   g(1)
  >   { case _ => 1 }
  > }
  > EOF
  $ diktor --type-check nl2.kel
  nl2.kel:3:3: 構文エラー: { x => ... } と { case ... } は末尾ブロックとしてだけ書けます(呼び出しの直後の同じ行に置くか、fn(x) => ... と書きます)
  [2]
  $ echo 'let a = g(1, { x => x })' > argpos.kel
  $ diktor --type-check argpos.kel
  argpos.kel:1:14: 構文エラー: { x => ... } と { case ... } は末尾ブロックとしてだけ書けます(呼び出しの直後の同じ行に置くか、fn(x) => ... と書きます)
  [2]

丸括弧の中では改行が文を区切らないので、{ を次の行に書いた末尾ブロックは、
同じ行の規則の違反として報告する:

  $ printf 'let a = (f\n{ 1 })\n' > nl3.kel
  $ diktor --type-check nl3.kel
  nl3.kel:2:1: 構文エラー: 末尾ブロックの { は、呼び出しと同じ行に書きます
  [2]
  $ printf 'let a = (g(1)\n{ x => x })\n' > nl4.kel
  $ diktor --type-check nl4.kel
  nl4.kel:2:1: 構文エラー: 末尾ブロックの { は、呼び出しと同じ行に書きます
  [2]

{ 文の列 } を次の行に書くと、ブロックの式文になり、エラーにならない。
次の 2 行は let r = f と式文 { 1 } の 2 つの文である:

  $ printf 'let f = 1\nlet r = f\n{ 1 }\n' > nl5.kel
  $ diktor --dump-ast nl5.kel
  (dlet (binding f = 1))
  (dlet (binding r = f))
  (exp 1)

末尾ブロックの本体は無名関数の本体なので、操作節の中の末尾ブロックには
その節の resume を書けない(LangSpec §13.5)。末尾ブロックの中の別の handle
の resume は書ける:

  $ cat > resume.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let call0[R, E](f: () => R @ E): R @ E = f()
  > let r = (perform ask() + 1) handle {
  >   case ask() => call0 { resume(41) }
  > }
  > EOF
  $ diktor --type-check resume.kel
  call0 : (() => A) => A
  ! resume.kel:4:25: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]
  $ cat > resume2.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let call0[R, E](f: () => R @ E): R @ E = f()
  > echoln(show(call0 { perform ask() + 1 } handle { case ask() => resume(41) }))
  > EOF
  $ diktor resume2.kel
  42

末尾ブロックの本体は run の本体に含めない(LangSpec §14.1)。run の本体の
末尾ブロックで、そのリージョンの参照を読み書きできる。入れ子の run の
本体に書いた末尾ブロックから外側の run の参照を読むと、fn で書いた場合と
同じく型エラーになる:

  $ cat > run1.kel <<'EOF'
  > let each[A, E](xs: Array[A], f: (A) => Unit @ E): Unit @ E = Array.each(xs, f)
  > let sum(xs: Array[Int32]): Int32 = run h {
  >   let acc = Ref.new(0)
  >   each(xs) { x => Ref.set(acc, Ref.get(acc) + x) }
  >   Ref.get(acc)
  > }
  > echoln(show(sum(run h { MutableArray.freeze(MutableArray.new(4, 5)) })))
  > EOF
  $ diktor run1.kel
  20
  $ cat > run2.kel <<'EOF'
  > let call0[R, E](f: () => R @ E): R @ E = f()
  > let leak(): Int32 = run h {
  >   let r = Ref.new(1)
  >   run k { call0 { Ref.get(r) } }
  > }
  > EOF
  $ diktor --type-check run2.kel
  call0 : (() => A) => A
  ! run2.kel:4:27: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
  [1]

with の右辺に末尾ブロック付きの呼び出しを書くと、継続は末尾ブロックの
後ろに加わる:

  $ printf 'with x = f(a) { k }\nx\n' > with.kel
  $ diktor --dump-ast with.kel
  (exp
   (apply f
    (extend _item a (extend _item (fn () k) (extend _item (fn (x) x) {})))))
