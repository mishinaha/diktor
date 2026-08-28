--type-check --no-prelude のゴールデン(M4: 推論コア)。
変更時は dune promote で更新し、必ず目視レビューすること。

sample.kel §1(型エイリアス)・§2(述語つきリテラル)・§3(レコード)・§4(タプル):

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

行多相・Scoped Labels・タプルの前置多相(sample.kel §3-§4):

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

演算子とクラス制約(sample.kel §8 の組み込み表。M4 は decls 直登録):

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

MiniLang §16-1(HM 多相と let 一般化):

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
  ! 型エラー: Boolean は Integral のインスタンスではありません
  [1]

MiniLang §16-4(行多相レコードと Scoped Labels は rows.kel で対応済み)。

MiniLang §16-8(値制限。runST の2例は M6 で追加):

  $ cat > ml8.kel <<'EOF'
  > let idf = fn(x) => x
  > let weak = (fn(x) => x)(fn(y) => y)
  > EOF
  $ diktor --type-check --no-prelude ml8.kel
  idf : (A) => A
  weak : (_A) => _A

MiniLang §16-5(型注釈と skolem 化):

  $ cat > ml5.kel <<'EOF'
  > let polyid[A](x: A): A = x
  > EOF
  $ diktor --type-check --no-prelude ml5.kel
  polyid : (A) => A

  $ cat > ml5b.kel <<'EOF'
  > let bad[A](x: A): A = x + 1
  > EOF
  $ diktor --type-check --no-prelude ml5b.kel
  ! 型エラー: 型パラメータ ς1 は Add のインスタンスではありません。[A: Add] のように制約を書いてください
  [1]

  $ cat > ml5c.kel <<'EOF'
  > let bad = fn(y) => {
  >   let f[A](x: A): A = y
  >   f
  > }
  > EOF
  $ diktor --type-check --no-prelude ml5c.kel
  ! 型エラー: 注釈された返り値型を満たしません(スコープ付きの型 ς1 がスコープの外に漏れています)
  [1]

let rec と前方参照(注釈が完全な let は宣言順に依存しない。§7.2 の2パス):

  $ cat > rec.kel <<'EOF'
  > let rec even(n) = n == 0 || odd(n - 1)
  > and odd(n) = !(n == 0) && even(n - 1)
  > let forward(x: Int32): Int32 = helper(x)
  > let helper(y: Int32): Int32 = y + 1
  > EOF
  $ diktor --type-check --no-prelude rec.kel
  even : (Int32) => Boolean
  odd : (Int32) => Boolean
  forward : (Int32) => Int32
  helper : (Int32) => Int32

エフェクト行つき矢印型の注釈と純粋注釈:

  $ cat > eff.kel <<'EOF'
  > let compose[A, B, C, E](f: (A) => B @ E, g: (B) => C @ E): (A) => C @ E =
  >   fn(x) => g(f(x))
  > let pure_fn(x: Int32): Int32 @ {} = x + 1
  > EOF
  $ diktor --type-check --no-prelude eff.kel
  compose : ((A) => B, (B) => C) => (A) => C
  pure_fn : (Int32) => Int32

構造的 Eq の導出(閉じた行のみ。sample.kel:305-309):

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
  ! 型エラー: 行変数を含む型 {x: Int32 extends ς1} に Eq の構造的導出は適用できません(行が閉じていません)
  [1]

数値まわりのエラー(D8, D13):

  $ cat > numbad.kel <<'EOF'
  > let bad = 0 + "x"
  > EOF
  $ diktor --type-check --no-prelude numbad.kel
  ! 型エラー: String は Integral のインスタンスではありません
  [1]

  $ cat > numbad2.kel <<'EOF'
  > let bad = 1u8
  > EOF
  $ diktor --type-check --no-prelude numbad2.kel
  ! 型エラー: 数値接尾辞 1u8 は v0 では未対応です(i32/i64/f64 を使ってください)
  [1]

型エイリアスの検査(非再帰・部分適用禁止):

  $ cat > aliasbad.kel <<'EOF'
  > type X = X
  > EOF
  $ diktor --type-check --no-prelude aliasbad.kel
  ! 型エラー: 型エイリアス X が再帰しています(エイリアスは非再帰)
  [1]

  $ cat > aliasbad2.kel <<'EOF'
  > type Pair2[A, B] = (A, B)
  > let q: Pair2[Int32] = (1, "a")
  > EOF
  $ diktor --type-check --no-prelude aliasbad2.kel
  ! 型エラー: 型エイリアス Pair2 の引数は 2 個必要です(1 個与えられました。部分適用は禁止)
  [1]
