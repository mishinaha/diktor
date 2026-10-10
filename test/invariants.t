保存する性質(LangSpec §18)。各ブロックは、変換の前と後の 2 つのファイルを実行し、
標準出力のバイト列と終了状態を比べる。inv は、両方が一致すれば same: exit N を、
どちらかが違えば differ: exit N / M を出す。診断と警告の文面は名前と位置を含むので
比べない(§18 の「評価の結果」の定義)。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"
  $ inv() { diktor "$1" > "$1.out" 2> /dev/null; a=$?; diktor "$2" > "$2.out" 2> /dev/null; b=$?; if [ $a = $b ] && cmp -s "$1.out" "$2.out"; then echo "same: exit $a"; else echo "differ: exit $a / $b"; fi; }

§18.1 束縛名の付け替え。関数、値、引数、パターンの変数、型パラメータ、行変数を
一斉に付け替える(inv は実行の標準出力と終了状態だけを比べる):

  $ cat > alpha_a.kel <<'KEL'
  > let apply[A, B, E](f: (A) => B @ E, x: A): B @ E = f(x)
  > let twice[E](f: () => Unit @ E): Unit @ E = { f(); f() }
  > let rec len[A](xs: List[A]): Int32 = xs match { case Nil => 0 case Cons(_, t) => 1 + len(t) }
  > let total = {
  >   let n = apply(fn(v) => v + 1, 41)
  >   let m = len(Cons(n, Cons(n, Nil)))
  >   n + m
  > }
  > twice { echoln(show(total)) }
  > KEL
  $ cat > alpha_b.kel <<'KEL'
  > let call[X, Y, Q](g: (X) => Y @ Q, y: X): Y @ Q = g(y)
  > let double[Rw](h: () => Unit @ Rw): Unit @ Rw = { h(); h() }
  > let rec count[T](ys: List[T]): Int32 = ys match { case Nil => 0 case Cons(_, rest) => 1 + count(rest) }
  > let sum_ = {
  >   let a = call(fn(w) => w + 1, 41)
  >   let b = count(Cons(a, Cons(a, Nil)))
  >   a + b
  > }
  > double { echoln(show(sum_)) }
  > KEL
  $ inv alpha_a.kel alpha_b.kel
  same: exit 0
  $ cat alpha_a.kel.out
  44
  44

§18.1 のパンニング。{a,} の a はラベルと変数を兼ねるので、{a = a,} の形に展開してから
変数の側だけを b に付け替える:

  $ cat > alphapun_a.kel <<'KEL'
  > let a = 1
  > let r = {a,}
  > echoln(show(r.a))
  > KEL
  $ cat > alphapun_b.kel <<'KEL'
  > let b = 1
  > let r = {a = b}
  > echoln(show(r.a))
  > KEL
  $ inv alphapun_a.kel alphapun_b.kel
  same: exit 0

§18.2 依存のない宣言の並べ替え。型、関数、値の宣言を、参照の向きを保たずに入れ替える
(式文は動かさない):

  $ cat > reorder_a.kel <<'KEL'
  > newtype Shape = Circle(Float64) | Square(Float64)
  > let area(s: Shape): Float64 = s match { case Circle(r) => r * r * 3.0 case Square(a) => a * a }
  > let unit_sq = Square(1.0)
  > let label = "area"
  > echoln(label + " " + show(area(unit_sq)))
  > KEL
  $ cat > reorder_b.kel <<'KEL'
  > let label = "area"
  > newtype Shape = Circle(Float64) | Square(Float64)
  > let unit_sq = Square(1.0)
  > let area(s: Shape): Float64 = s match { case Circle(r) => r * r * 3.0 case Square(a) => a * a }
  > echoln(label + " " + show(area(unit_sq)))
  > KEL
  $ inv reorder_a.kel reorder_b.kel
  same: exit 0

§18.2。型の宣言は、間に値の宣言を挟んでも後ろの型を参照できる(§6.4):

  $ cat > reordertype_a.kel <<'KEL'
  > type A = B
  > newtype B = B(Int32)
  > let x = 1
  > let y: A = B(x)
  > echoln("ok")
  > KEL
  $ cat > reordertype_b.kel <<'KEL'
  > type A = B
  > let x = 1
  > newtype B = B(Int32)
  > let y: A = B(x)
  > echoln("ok")
  > KEL
  $ inv reordertype_a.kel reordertype_b.kel
  same: exit 0

§18.2 の再帰群の中の順序。注釈のない f が、後ろの閉じた行の g を呼ぶ。
群の署名を先に置くので、どちらの順序でも受理する:

  $ cat > reorderrec_a.kel <<'KEL'
  > let rec f() = { println("a"); g() }
  > and g(): Unit @ {} = ()
  > with_stdout(f)
  > KEL
  $ cat > reorderrec_b.kel <<'KEL'
  > let rec g(): Unit @ {} = ()
  > and f() = { println("a"); g() }
  > with_stdout(f)
  > KEL
  $ inv reorderrec_a.kel reorderrec_b.kel
  same: exit 0

§18.2 の再帰群の除外。f[A] の本体が g[A] の型パラメータを A に決める。群の中の
まだ検査していない g への参照は単相なので、f を先に書くと 2 つの剛定数 A を単一化して落ちる:

  $ cat > reorderrectp_a.kel <<'KEL'
  > let rec f[A](x: A): Unit @ Print = { println("f"); g(x) }
  > and g[A](x: A): Unit @ {} = ()
  > with_stdout(fn() => f(1))
  > KEL
  $ cat > reorderrectp_b.kel <<'KEL'
  > let rec g[A](x: A): Unit @ {} = ()
  > and f[A](x: A): Unit @ Print = { println("f"); g(x) }
  > with_stdout(fn() => f(1))
  > KEL
  $ inv reorderrectp_a.kel reorderrectp_b.kel
  differ: exit 1 / 0

§18.2 の条件 4 の除外。2 つの宣言は互いを参照しないが、一般化しない束縛 r を共有する。
r(1) を先に書くと、宣言の終わりの既定化で r が (Int32) => Int32 に決まる(§4.2):

  $ cat > weakorder_a.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let r = idf(fn(y) => y)
  > let a = r(1)
  > let b: Int64 = r(2)
  > echoln(show(a) + show(b))
  > KEL
  $ cat > weakorder_b.kel <<'KEL'
  > let idf[A](x: A): A = x
  > let r = idf(fn(y) => y)
  > let b: Int64 = r(2)
  > let a = r(1)
  > echoln(show(a) + show(b))
  > KEL
  $ inv weakorder_a.kel weakorder_b.kel
  differ: exit 1 / 0

§18.2 の条件 1 の除外。v の初期化式は g を直接書かないが、f の本体をたどると g を参照する。
2 つ目の組は、値束縛 k の初期化式を通して f に届く:

  $ cat > reorderindirect_a.kel <<'KEL'
  > let f(): Int32 = g()
  > let v: Int32 = f()
  > let g(): Int32 @ {} = 42
  > echoln(show(v))
  > KEL
  $ cat > reorderindirect_b.kel <<'KEL'
  > let f(): Int32 = g()
  > let g(): Int32 @ {} = 42
  > let v: Int32 = f()
  > echoln(show(v))
  > KEL
  $ inv reorderindirect_a.kel reorderindirect_b.kel
  differ: exit 3 / 0
  $ cat > reorderindirect_c.kel <<'KEL'
  > let f(): Int32 = g()
  > let k = f
  > let v: Int32 = k()
  > let g(): Int32 @ {} = 42
  > echoln(show(v))
  > KEL
  $ cat > reorderindirect_d.kel <<'KEL'
  > let f(): Int32 = g()
  > let k = f
  > let g(): Int32 @ {} = 42
  > let v: Int32 = k()
  > echoln(show(v))
  > KEL
  $ inv reorderindirect_c.kel reorderindirect_d.kel
  differ: exit 3 / 0

§18.2 の条件 1 のインスタンスの除外。v の初期化式は、use の本体のメソッドの呼び出しを
通してインスタンスを使うので、インスタンス宣言と入れ替えられない:

  $ cat > reorderinst_a.kel <<'KEL'
  > newtype L(String)
  > type class R[A] { val r: (A) => String }
  > let use(x: L): String = r(x)
  > let v: String = use(L("a"))
  > type instance R[L] { let r(x) = x match { case L(s) => s } }
  > echoln(v)
  > KEL
  $ cat > reorderinst_b.kel <<'KEL'
  > newtype L(String)
  > type class R[A] { val r: (A) => String }
  > let use(x: L): String = r(x)
  > type instance R[L] { let r(x) = x match { case L(s) => s } }
  > let v: String = use(L("a"))
  > echoln(v)
  > KEL
  $ inv reorderinst_a.kel reorderinst_b.kel
  differ: exit 3 / 0

§18.2 の条件 3 の除外。値束縛で書いたメソッドを持つインスタンスは、初期化で式を評価する。
??? の評価が実行時エラーになるので、echoln との順序で標準出力が変わる:

  $ cat > reorderinsthole_a.kel <<'KEL'
  > newtype N = N(Int32)
  > echoln("a")
  > type instance Show[N] { let show: (N) => String = ??? }
  > KEL
  $ cat > reorderinsthole_b.kel <<'KEL'
  > newtype N = N(Int32)
  > type instance Show[N] { let show: (N) => String = ??? }
  > echoln("a")
  > KEL
  $ inv reorderinsthole_a.kel reorderinsthole_b.kel
  differ: exit 3 / 3

§18.2 のブロックの最後の文の除外。最後の文の値がブロックの値になる(§5.4):

  $ cat > reorderlast_a.kel <<'KEL'
  > let v: Int32 = { let g(n: Int32): Int32 = n; 5 }
  > echoln(show(v))
  > KEL
  $ cat > reorderlast_b.kel <<'KEL'
  > let v: Int32 = { 5; let g(n: Int32): Int32 = n }
  > echoln(show(v))
  > KEL
  $ inv reorderlast_a.kel reorderlast_b.kel
  differ: exit 0 / 1

§18.3 ラベルの順序。レコード型、レコード式、レコードのパターン、構造的ヴァリアント型:

  $ cat > label_a.kel <<'KEL'
  > let p: {x: Int32, y: String} = {x = 1, y = "s"}
  > let f[R](r: {x: Int32, y: String extends R}): String = r.y + show(r.x)
  > let v: #A(Int32) | #B = #A(1)
  > let {x, y} = {x = 1, y = 2}
  > echoln(f(p) + show(x + y) + (v match { case #A(n) => show(n) case #B => "b" }))
  > KEL
  $ cat > label_b.kel <<'KEL'
  > let p: {y: String, x: Int32} = {y = "s", x = 1}
  > let f[R](r: {y: String, x: Int32 extends R}): String = r.y + show(r.x)
  > let v: #B | #A(Int32) = #A(1)
  > let {y, x} = {x = 1, y = 2}
  > echoln(f(p) + show(x + y) + (v match { case #A(n) => show(n) case #B => "b" }))
  > KEL
  $ inv label_a.kel label_b.kel
  same: exit 0
  $ cat label_a.kel.out
  s131

§18.3。コンストラクタの名前付き引数の順序(引数の式がエフェクトを起こさない場合):

  $ cat > labelnamed_a.kel <<'KEL'
  > newtype P = P(a: Int32, b: String)
  > let p = P(a = 1, b = "x")
  > echoln(p match { case P(a, b) => b + show(a) })
  > KEL
  $ cat > labelnamed_b.kel <<'KEL'
  > newtype P = P(a: Int32, b: String)
  > let p = P(b = "x", a = 1)
  > echoln(p match { case P(a, b) => b + show(a) })
  > KEL
  $ inv labelnamed_a.kel labelnamed_b.kel
  same: exit 0

§18.3 のエフェクト行のラベルの順序。同じ操作名を持つ 2 つのエフェクトは、行の順序では
選ばず、修飾を求める。どちらの順序でも型検査に通らない:

  $ cat > labelrow_a.kel <<'KEL'
  > effect A = { ask: () => Int32 }
  > effect B = { ask: () => Int32 }
  > let q(): Int32 @ {A, B} = perform ask()
  > let r = ((q() handle { case A.ask() => resume(1) }) handle { case B.ask() => resume(2) })
  > echoln(show(r))
  > KEL
  $ cat > labelrow_b.kel <<'KEL'
  > effect A = { ask: () => Int32 }
  > effect B = { ask: () => Int32 }
  > let q(): Int32 @ {B, A} = perform ask()
  > let r = ((q() handle { case A.ask() => resume(1) }) handle { case B.ask() => resume(2) })
  > echoln(show(r))
  > KEL
  $ inv labelrow_a.kel labelrow_b.kel
  same: exit 1

§18.3 の除外。レコード式に書いたフィールドの順序は評価の順序を決める(§7.2)。
フィールドの式がエフェクトを起こすと、出力が変わる:

  $ cat > evalorder_a.kel <<'KEL'
  > let n(s: String): Int32 @ Console = { echo(s); 1 }
  > let p = {x = n("x"), y = n("y")}
  > echoln("")
  > KEL
  $ cat > evalorder_b.kel <<'KEL'
  > let n(s: String): Int32 @ Console = { echo(s); 1 }
  > let p = {y = n("y"), x = n("x")}
  > echoln("")
  > KEL
  $ inv evalorder_a.kel evalorder_b.kel
  differ: exit 0 / 0
  $ cat evalorder_a.kel.out evalorder_b.kel.out
  xy
  yx

§18.4 型エイリアスへの置換。値束縛の注釈の矢印をエイリアスにしても、@ Console の
文脈から呼べる:

  $ cat > alias_a.kel <<'KEL'
  > let k: (Int32) => Int32 = fn(x) => x
  > let use(): Int32 @ Console = k(1)
  > echoln(show(use()))
  > KEL
  $ cat > alias_b.kel <<'KEL'
  > type F = (Int32) => Int32
  > let k: F = fn(x) => x
  > let use(): Int32 @ Console = k(1)
  > echoln(show(use()))
  > KEL
  $ inv alias_a.kel alias_b.kel
  same: exit 0

§18.4。エフェクト行の別名と、行を取る型パラメータを持つエイリアス:

  $ cat > aliasrow_a.kel <<'KEL'
  > let f(): Unit @ {Print, Console} = { println("p"); echoln("c") }
  > newtype Cb[E] = Cb(() => Unit @ E)
  > let run_cb[E](c: Cb[E]): Unit @ E = c match { case Cb(g) => g() }
  > with_stdout(f)
  > run_cb(Cb(fn() => echoln("cb")))
  > KEL
  $ cat > aliasrow_b.kel <<'KEL'
  > type Out: EffectRow = {Print, Console}
  > type Fn[E] = () => Unit @ E
  > let f(): Unit @ Out = { println("p"); echoln("c") }
  > newtype Cb[E] = Cb(Fn[E])
  > let run_cb[E](c: Cb[E]): Unit @ E = c match { case Cb(g) => g() }
  > with_stdout(f)
  > run_cb(Cb(fn() => echoln("cb")))
  > KEL
  $ inv aliasrow_a.kel aliasrow_b.kel
  same: exit 0

§18.4 の 3 つ目の除外。pub のない値束縛の注釈の先頭の矢印で省略した @ は本体からの
推論を表し、エイリアスの本体の矢印で省略した @ は @ {} を表すので、置き換えると型が変わる:

  $ cat > aliasouter_a.kel <<'KEL'
  > let k: (Int32) => Int32 = fn(x) => { echoln("k"); x }
  > echoln(show(k(1)))
  > KEL
  $ cat > aliasouter_b.kel <<'KEL'
  > type F = (Int32) => Int32
  > let k: F = fn(x) => { echoln("k"); x }
  > echoln(show(k(1)))
  > KEL
  $ inv aliasouter_a.kel aliasouter_b.kel
  differ: exit 0 / 1

§18.4 の pub の宣言の注釈の除外。注釈に直接書いた入れ子の矢印には @ が要る(§15.2)が、
エイリアスの本体はこの要求を受けない:

  $ cat > aliaspub_a.kel <<'KEL'
  > pub let h(f: (Int32) => Int32): Int32 = f(1)
  > KEL
  $ cat > aliaspub_b.kel <<'KEL'
  > pub type F = (Int32) => Int32
  > pub let h(f: F): Int32 = f(1)
  > KEL
  $ inv aliaspub_a.kel aliaspub_b.kel
  differ: exit 1 / 0

§18.4 のインスタンスの対象の除外。対象は型構成子に限る(§12.2)ので、エイリアスに
置き換えられない:

  $ cat > aliasinst.kel <<'KEL'
  > newtype Seq[A] = Empty | More(A, Seq[A])
  > type S = Seq[Int32]
  > type class Size[A] { val size: (A) => Int32 }
  > type instance Size[S] { let size(x) = 0 }
  > KEL
  $ diktor --type-check aliasinst.kel
  ! aliasinst.kel:4:1: 型エラー: 未知の型構成子: S
  [1]

§18.5 対話的な実行で受理しなかった入力。型エラー、実行時エラー、構文エラーの入力を挟んでも、
受理した入力の表示は変わらない。差分は失敗した入力の診断と、実行時エラーまでに書いた
出力 half の追加(+)だけである:

  $ cat > repl_a.txt <<'KEL'
  > let idf[A](x: A): A = x
  > let g = idf(fn(y) => y)
  > newtype N = N(Int32)
  > g(N(1))
  > N(2)
  > let h = g
  > KEL
  $ cat > repl_b.txt <<'KEL'
  > let idf[A](x: A): A = x
  > let bad1: Int32 = "s"
  > let g = idf(fn(y) => y)
  > let bad2 = { let w = g(true); 1 / 0 }
  > newtype N = N(Int32)
  > let bad3 = { newtype M = M(Int32); 1 }
  > type instance Show[N] { let show(x) = "n" }; let bad4 = 1 / 0
  > g(N(1))
  > echoln("half"); let bad5 = 1 / 0
  > N(2)
  > let h = g
  > KEL
  $ diktor --repl < repl_a.txt > repl_a.out
  $ diktor --repl < repl_b.txt > repl_b.out
  $ diff repl_a.out repl_b.out | grep '^[<>]' | sed 's/^>/+/; s/^</-/'
  + ! <stdin>:2:5: 型エラー: 注釈された型を満たしません(型が一致しません: Int32 と String)
  + 実行時エラー: ゼロ除算です
  + <stdin>:7:1: 構文エラー: この宣言はブロック内では使えません(let / let rec / 式のみ)
  + 実行時エラー: ゼロ除算です
  + half
  + 実行時エラー: ゼロ除算です
