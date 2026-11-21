--type-check --no-prelude で確かめる、型推論の中核のゴールデンテストである。
期待出力を変えるときは、差分を目で確かめてから dune promote で更新する。

sample.kel §1(型エイリアス)、§2(組み込みの制約を持つ数値リテラル)、§3(レコード)、§4(タプル):

  $ cat > basics.kel <<'EOF'
  > type MyInt = Int32
  > type Point = {x: Float64, y: Float64}
  > type Pair = (Int32, String)
  > let n: MyInt = 42
  > let d = 1 + 2
  > let f = 1.5
  > let s = "a" + "b"
  > let big = 1_000_000i64
  > let point(x: Float64, y: Float64): Point = {x = x, y = y}
  > let dist2(p: Point): Float64 = p.x * p.x + p.y * p.y
  > let pair: Pair = (1, "one")
  > let first = pair._0
  > let second = pair._1
  > EOF
  $ diktor --type-check --no-prelude basics.kel
  n : Int32
  d : Int32
  f : Float64
  s : String
  big : Int64
  point : (Float64, Float64) => {x: Float64, y: Float64}
  dist2 : ({x: Float64, y: Float64}) => Float64
  pair : (Int32, String)
  first : Int32
  second : String

行多相、Scoped Labels、先頭の要素だけを指定したタプルの多相(sample.kel §3、§4):

  $ cat > rows.kel <<'EOF'
  > let getx = fn(r) => r.x + 1
  > let shadow = {
  >   let r = {x = 1, y = true}
  >   let r2 = {x = "hello" extends r}
  >   {outer = r2.x, inner = (r2 \ x).x}
  > }
  > let fst2[A, R](t: {_item: A extends R}): A = t._0
  > let swap[A, B](p: (A, B)): (B, A) = (p._1, p._0)
  > let update = fn(p) => {p with x = 1.5}
  > EOF
  $ diktor --type-check --no-prelude rows.kel
  getx : ({x: Int32 extends R1}) => Int32
  shadow : {outer: String, inner: Int32}
  fst2 : ({_item: A extends R1}) => A
  swap : ((A, B)) => (B, A)
  update : ({x: A extends R1}) => {x: Float64 extends R1}

演算子とクラス制約(sample.kel §8)。演算子のクラスは Decls が組み込みとして登録している:

  $ cat > ops.kel <<'EOF'
  > let fma[A: Add + Mul](x: A, y: A, z: A): A = x * y + z
  > let lt3 = fn(x) => x < x
  > let ne = 1 != 2
  > let logic = true && !false || 1 == 1
  > EOF
  $ diktor --type-check --no-prelude ops.kel
  fma : [A: Add + Mul] (A, A, A) => A
  lt3 : [A: Ord] (A) => Boolean
  ne : Boolean
  logic : Boolean

let 多相と一般化。let で束縛した id は多相に使えるが、無名関数の引数 f は単相である:

  $ cat > ml1.kel <<'EOF'
  > let r = {
  >   let id = fn(x) => x
  >   {a = id(1), b = id(true)}
  > }
  > EOF
  $ diktor --type-check --no-prelude ml1.kel
  r : {a: Int32, b: Boolean}

  $ cat > ml1b.kel <<'EOF'
  > let bad = fn(f) => {a = f(1), b = f(true)}
  > EOF
  $ diktor --type-check --no-prelude ml1b.kel
  ! ml1b.kel:1:37: 型エラー: Boolean は Integral のインスタンスではありません
  [1]

行多相のレコードと Scoped Labels は、上の rows.kel で確かめている。

値制限。構文上の値でない初期化式の型は一般化しない(run を使う例は typecheck_m6.t の stvr.kel):

  $ cat > ml8.kel <<'EOF'
  > let idf = fn(x) => x
  > let weak = (fn(x) => x)(fn(y) => y)
  > EOF
  $ diktor --type-check --no-prelude ml8.kel
  idf : (A) => A
  weak : (_A) => _A

型注釈とスコーレム化。注釈の型パラメータは、本体の検査の間は固定した型として扱う:

  $ cat > ml5.kel <<'EOF'
  > let polyid[A](x: A): A = x
  > EOF
  $ diktor --type-check --no-prelude ml5.kel
  polyid : (A) => A

  $ cat > ml5b.kel <<'EOF'
  > let bad[A](x: A): A = x + 1
  > EOF
  $ diktor --type-check --no-prelude ml5b.kel
  ! ml5b.kel:1:23: 型エラー: 型パラメータ ς1 は Add のインスタンスではありません。[A: Add] のように制約を書いてください
  [1]

  $ cat > ml5c.kel <<'EOF'
  > let bad = fn(y) => {
  >   let f[A](x: A): A = y
  >   f
  > }
  > EOF
  $ diktor --type-check --no-prelude ml5c.kel
  ! ml5c.kel:2:7: 型エラー: 注釈された返り値型を満たしません(スコープ付きの型 ς1 がスコープの外に漏れています(ς1 は型パラメータ A です。A のスコープの外の型と共有された、型の決まっていない変数(注釈の無い引数の型や、一般化されない束縛の型など)に A を入れようとしています))
  [1]

let rec と前方参照。引数と返り値の型を注釈し、最も外側の矢印の @ も書いた関数は、
宣言より前から参照できる(LangSpec §6.4)。最も外側の @ を省略した関数は、
前方参照できない:

  $ cat > rec.kel <<'EOF'
  > let rec even(n) = n == 0 || odd(n - 1)
  > and odd(n) = !(n == 0) && even(n - 1)
  > let forward(x: Int32): Int32 @ {} = helper(x)
  > let helper(y: Int32): Int32 @ {} = y + 1
  > EOF
  $ diktor --type-check --no-prelude rec.kel
  even : (Int32) => Boolean
  odd : (Int32) => Boolean
  forward : (Int32) => Int32 @ {}
  helper : (Int32) => Int32 @ {}

  $ cat > fwdbad.kel <<'EOF'
  > let forward(x: Int32): Int32 = helper(x)
  > let helper(y: Int32): Int32 = y + 1
  > EOF
  $ diktor --type-check --no-prelude fwdbad.kel
  ! fwdbad.kel:1:32: 型エラー: 未束縛の変数: helper
  [1]

エフェクト行の付いた矢印型の注釈と、@ {} の注釈:

  $ cat > eff.kel <<'EOF'
  > let compose[A, B, C, E](f: (A) => B @ E, g: (B) => C @ E): (A) => C @ E =
  >   fn(x) => g(f(x))
  > let pure_fn(x: Int32): Int32 @ {} = x + 1
  > EOF
  $ diktor --type-check --no-prelude eff.kel
  compose : ((A) => B, (B) => C) => (A) => C
  pure_fn : (Int32) => Int32 @ {}

構造的な Eq の導出(sample.kel:392-396)。閉じた行の型にだけ適用できる:

  $ cat > eq.kel <<'EOF'
  > type Point = {x: Float64, y: Float64}
  > let same_point(p: Point, q: Point): Boolean = p == q
  > let same_pair(p: (Int32, String), q: (Int32, String)): Boolean = p == q
  > EOF
  $ diktor --type-check --no-prelude eq.kel
  same_point : ({x: Float64, y: Float64}, {x: Float64, y: Float64}) => Boolean
  same_pair : ((Int32, String), (Int32, String)) => Boolean

  $ cat > eqbad.kel <<'EOF'
  > let same[R](p: {x: Int32 extends R}, q: {x: Int32 extends R}): Boolean = p == q
  > EOF
  $ diktor --type-check --no-prelude eqbad.kel
  ! eqbad.kel:1:74: 型エラー: 行変数を含む型 {x: Int32 extends ς1} に Eq の構造的導出は適用できません(行が閉じていません)
  [1]

数値リテラルのエラー:

  $ cat > numbad.kel <<'EOF'
  > let bad = 0 + "x"
  > EOF
  $ diktor --type-check --no-prelude numbad.kel
  ! numbad.kel:1:11: 型エラー: String は Integral のインスタンスではありません
  [1]

  $ cat > numbad2.kel <<'EOF'
  > let bad = 1u8
  > EOF
  $ diktor --type-check --no-prelude numbad2.kel
  ! numbad2.kel:1:11: 型エラー: 数値リテラル 1u8 の接尾辞 u8 はありません(接尾辞は i32、i64、f64 だけです)
  [1]

型エイリアスの検査。再帰と部分適用はエラーになる:

  $ cat > aliasbad.kel <<'EOF'
  > type X = X
  > EOF
  $ diktor --type-check --no-prelude aliasbad.kel
  ! aliasbad.kel:1:10: 型エラー: 型エイリアス X が再帰しています(エイリアスは非再帰)
  [1]

  $ cat > aliasbad2.kel <<'EOF'
  > type Pair2[A, B] = (A, B)
  > let q: Pair2[Int32] = (1, "a")
  > EOF
  $ diktor --type-check --no-prelude aliasbad2.kel
  ! aliasbad2.kel:2:8: 型エラー: 型エイリアス Pair2 の引数は 2 個必要です(1 個与えられました。部分適用は禁止)
  [1]

未実装の構文も診断として報告し、それより前の宣言の型は表示する:

  $ cat > mix.kel <<'EOF2'
  > effect E = { op: () => Int32 }
  > let ok = 1 + 2
  > let bad = (1) handle { case op() => resume(1) case cancel(e) => () }
  > EOF2
  $ diktor --type-check --no-prelude mix.kel
  ok : Int32
  ! mix.kel:3:52: 未実装: cancel(reason)(v0 は case cancel のみ)
  [4]

標準環境の名前は再宣言できない(LangSpec §16.1)。newtype、型エイリアス、effect、
type class の 4 種別を 1 つずつ確かめる(インスタンスは test/verify_fixes.t の coh):

  $ printf 'newtype Option[A] = None(Int32) | Some\n' > d1.kel
  $ diktor --type-check d1.kel
  ! d1.kel:1:1: 型エラー: 標準環境の newtype Option は再宣言できません
  [1]

  $ printf 'type Unit = Int32\n' > d5.kel
  $ diktor --type-check d5.kel
  ! d5.kel:1:1: 型エラー: 標準環境の型エイリアス Unit は再宣言できません
  [1]

  $ printf 'effect Console = { write: (Int32) => Unit }\n' > d7.kel
  $ diktor --type-check d7.kel
  ! d7.kel:1:1: 型エラー: 標準環境の effect Console は再宣言できません
  [1]

  $ printf 'type class Add[A] { val add: (A, A) => Boolean }\n' > d8.kel
  $ diktor --type-check d8.kel
  ! d8.kel:1:1: 型エラー: 標準環境の type class Add は再宣言できません
  [1]

同じファイルを 2 回渡すと、二重宣言のエラーになる:

  $ printf 'newtype Foo = Bar\n' > dup1.kel
  $ diktor --type-check dup1.kel dup1.kel
  ! dup1.kel:1:1: 型エラー: newtype Foo が二重に宣言されています
  [1]

型名の名前空間は newtype、型エイリアス、effect で共通である。
種別を変えた再宣言もエラーになるので、type List[A] = Int32 で
プレリュードの List を置き換えることはできない:

  $ printf 'type List[A] = Int32\nlet main(): Int32 = 1\n' > ns1.kel
  $ diktor --type-check ns1.kel
  ! ns1.kel:1:1: 型エラー: List は既に newtype として宣言されています(型エイリアス では再宣言できません)
  [1]
  $ printf 'newtype Unit = Nope\nlet main(): Int32 = 1\n' > ns2.kel
  $ diktor --type-check ns2.kel
  ! ns2.kel:1:1: 型エラー: Unit は既に 型エイリアス として宣言されています(newtype では再宣言できません)
  [1]
  $ printf 'newtype Foo = A\ntype Foo = Int32\nlet main(): Int32 = 1\n' > ns3.kel
  $ diktor --type-check ns3.kel
  ! ns3.kel:2:1: 型エラー: Foo は既に newtype として宣言されています(型エイリアス では再宣言できません)
  [1]
  $ printf 'effect Int32 = { w: () => Unit }\nlet main(): Int32 = 1\n' > ns4.kel
  $ diktor --type-check ns4.kel
  ! ns4.kel:1:1: 型エラー: 組み込み型 Int32 は effect で再宣言できません
  [1]

標準環境の名前を 2 回宣言しても、1 つ目の宣言でエラーになる:

  $ printf 'newtype List[A] = Nil | Cons(head: A, tail: List[A])\nnewtype List[A] = Nil | Cons(head: A, tail: List[A])\necholn("x")\n' > rd1.kel
  $ diktor --type-check rd1.kel
  ! rd1.kel:1:1: 型エラー: 標準環境の newtype List は再宣言できません
  [1]
  $ printf 'type class Add[A] { val add: (A, A) => A }\ntype class Add[A] { val add: (A, A) => A }\nlet main(): Int32 = 1\n' > rd2.kel
  $ diktor --type-check rd2.kel
  ! rd2.kel:1:1: 型エラー: 標準環境の type class Add は再宣言できません
  [1]

波括弧のない引数付きのエフェクトラベル @ Heap[h] は、@ {Heap[h]} の略記
である:

  $ printf 'let g[h](r: Ref[h, Int32]): Int32 @ Heap[h] = Ref.get(r)\n' > effshort.kel
  $ diktor --type-check effshort.kel
  g : (Ref[h, Int32]) => Int32 @ {Heap[h]}

組み込みクラスのメソッドの型スキーム(Decls の arrow1 と arrow2 が組み立てる):

  $ cat > methods.kel <<'KEL'
  > let a = add(1, 2)
  > let b = lt(1, 2)
  > let c = show(1)
  > KEL
  $ diktor --type-check --no-prelude methods.kel
  a : Int32
  b : Boolean
  c : String

スコーレム定数を作る箇所のうち、注釈の型パラメータと run のリージョン変数を確かめる:

  $ cat > rigids.kel <<'KEL'
  > let ann[A: Add](x: A): A @ {} = x + x
  > let esc = run h { Ref.new(0) }
  > KEL
  $ diktor --type-check rigids.kel
  ann : [A: Add] (A) => A @ {}
  ! rigids.kel:2:11: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

入れ子のレコードの型変数は、読む順に採番する(第9章 §9.4)。
行の末尾の行変数を先に採番しないので、内側の行が R1、外側の行が R2 になる:

  $ cat > rowname.kel <<'KEL'
  > let g = fn(r) => r.x.y
  > let h = fn(r) => (r.x.y, r.p.q)
  > KEL
  $ diktor --type-check --no-prelude rowname.kel
  g : ({x: {y: A extends R1} extends R2}) => A
  h : ({x: {y: A extends R1}, p: {q: B extends R2} extends R3}) => (A, B)

スコーレム定数の制約は、型の前の角括弧には表示しない(第9章 §9.2)。
ς はユーザが書ける名前ではないので、[ς1: Add] ς1 のような表示にしない:

  $ cat > rigidcls.kel <<'KEL'
  > let cmp2[A: Add](x: A, y: A): Boolean = x < y
  > KEL
  $ diktor --type-check --no-prelude rigidcls.kel
  ! rigidcls.kel:1:41: 型エラー: 型パラメータ ς1 は Ord のインスタンスではありません。[A: Ord] のように制約を書いてください
  [1]

高カインドの型変数の適用 F[A] の型変数も、読む順に採番する。
先頭の型構成子 F を、引数 A より先に採番する:

  $ printf 'let idf2[F[_], A](x: F[A]): F[A] = x\nlet use3 = fn(w) => idf2(w)\n' > tapp.kel
  $ diktor --type-check --no-prelude tapp.kel
  idf2 : (F[A]) => F[A]
  use3 : (F[A]) => F[A]

タプルの表記に戻す形は 3 つある(第9章 §9.3)。2 要素以上は (A, B)、1 要素は (A,)、
空の行は {} と表示する。開いた行はタプルの形に戻さない:

  $ cat > resugar.kel <<'EOF'
  > let one = (1,)
  > let two = (1, "a")
  > let empty = ()
  > let opened[A, R](t: {_item: A extends R}): A = t._0
  > EOF
  $ diktor --type-check --no-prelude resugar.kel
  one : (Int32,)
  two : (Int32, String)
  empty : {}
  opened : ({_item: A extends R1}) => A

エラーメッセージの表示にも同じ規則を適用する:

  $ printf 'let bad: (Int32,) = "x"\n' > resugar2.kel
  $ diktor --type-check --no-prelude resugar2.kel
  ! resugar2.kel:1:5: 型エラー: 注釈された型を満たしません(型が一致しません: (Int32,) と String)
  [1]
