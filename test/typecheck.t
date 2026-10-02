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
  ! ml1b.kel:1:37: 型エラー: Boolean は Integral のインスタンスではありません
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
  ! ml5b.kel:1:23: 型エラー: 型パラメータ ς1 は Add のインスタンスではありません。[A: Add] のように制約を書いてください
  [1]

  $ cat > ml5c.kel <<'EOF'
  > let bad = fn(y) => {
  >   let f[A](x: A): A = y
  >   f
  > }
  > EOF
  $ diktor --type-check --no-prelude ml5c.kel
  ! ml5c.kel:2:7: 型エラー: 注釈された返り値型を満たしません(スコープ付きの型 ς1 がスコープの外に漏れています)
  [1]

let rec と前方参照(注釈が完全 — @ も明示 — な let は宣言順に依存しない。§7.2 の2パス。
@ を省略した関数は前方参照できない: 省略 @ の過剰一般化を避けるため注釈内の全ての
矢印に @ が要る):

  $ cat > rec.kel <<'EOF'
  > let rec even(n) = n == 0 || odd(n - 1)
  > and odd(n) = !(n == 0) && even(n - 1)
  > let forward(x: Int32): Int32 @ {} = helper(x)
  > let helper(y: Int32): Int32 @ {} = y + 1
  > EOF
  $ diktor --type-check --no-prelude rec.kel
  even : (Int32) => Boolean
  odd : (Int32) => Boolean
  forward : (Int32) => Int32
  helper : (Int32) => Int32

  $ cat > fwdbad.kel <<'EOF'
  > let forward(x: Int32): Int32 = helper(x)
  > let helper(y: Int32): Int32 = y + 1
  > EOF
  $ diktor --type-check --no-prelude fwdbad.kel
  ! fwdbad.kel:1:32: 型エラー: 未束縛の変数: helper
  [1]

エフェクト行つき矢印型の注釈と純粋注釈:

  $ cat > eff.kel <<'EOF'
  > let compose[A, B, C, E](f: (A) => B @ E, g: (B) => C @ E): (A) => C @ E =
  >   fn(x) => g(f(x))
  > let pure_fn(x: Int32): Int32 @ {} = x + 1
  > EOF
  $ diktor --type-check --no-prelude eff.kel
  compose : ((A) => B, (B) => C) => (A) => C
  pure_fn : (Int32) => Int32

構造的 Eq の導出(閉じた行のみ。sample.kel:391-395):

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

数値まわりのエラー(D8, D13):

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
  ! numbad2.kel:1:11: 未実装: 数値接尾辞 1u8(v0 は i32/i64/f64 のみ)
  [4]

型エイリアスの検査(非再帰・部分適用禁止):

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

未実装は診断の流れに乗る(G6。それまでの型の行が消えない):

  $ cat > mix.kel <<'EOF2'
  > let ok = 1 + 2
  > let bad = 1u8
  > EOF2
  $ diktor --type-check --no-prelude mix.kel
  ok : Int32
  ! mix.kel:2:11: 未実装: 数値接尾辞 1u8(v0 は i32/i64/f64 のみ)
  [4]

標準環境の名前は再宣言できない(LangSpec §16.1。newtype、型エイリアス、effect、
type class の 4 種別で 1 つずつ。インスタンスは test/verify_fixes.t の coh):

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

同じファイルを 2 回渡すと二重宣言(CLI 経路の連結処理の回帰。C11):

  $ printf 'newtype Foo = Bar\n' > dup1.kel
  $ diktor --type-check dup1.kel dup1.kel
  ! dup1.kel:1:1: 型エラー: newtype Foo が二重に宣言されています
  [1]

型名の名前空間は newtype / 型エイリアス / effect で 1 つ(M15 検証。
かつて種別を替えた再宣言が種別ごとの検査をすり抜け、type List[A] =
Int32 がプレリュードの List を黙って奪った):

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

標準環境の名前を 2 回宣言しても、1 本目で落ちる:

  $ printf 'newtype List[A] = Nil | Cons(head: A, tail: List[A])\nnewtype List[A] = Nil | Cons(head: A, tail: List[A])\necholn("x")\n' > rd1.kel
  $ diktor --type-check rd1.kel
  ! rd1.kel:1:1: 型エラー: 標準環境の newtype List は再宣言できません
  [1]
  $ printf 'type class Add[A] { val add: (A, A) => A }\ntype class Add[A] { val add: (A, A) => A }\nlet main(): Int32 = 1\n' > rd2.kel
  $ diktor --type-check rd2.kel
  ! rd2.kel:1:1: 型エラー: 標準環境の type class Add は再宣言できません
  [1]

ブレース無しの引数付きエフェクトラベル @ Heap[h] は @ {Heap[h]} の略記
(M18 検証。文法は受けるのに elab に枝が無く「未知の型: Heap」だった):

  $ printf 'let g[h](r: Ref[h, Int32]): Int32 @ Heap[h] = Ref.get(r)\n' > effshort.kel
  $ diktor --type-check effshort.kel
  g : (Ref[A, Int32]) => Int32 @ {Heap[A] extends R1}

組み込みクラスのメソッドスキーマ(arrow1 / arrow2 の 1 枚から出る):

  $ cat > methods.kel <<'KEL'
  > let a = add(1, 2)
  > let b = lt(1, 2)
  > let c = show(1)
  > KEL
  $ diktor --type-check --no-prelude methods.kel
  a : Int32
  b : Boolean
  c : String

剛定数の 3 つの生成点を 1 ファイルで(M19 / G5 の new_rigid_ref 集約):

  $ cat > rigids.kel <<'KEL'
  > let ann[A: Add](x: A): A @ {} = x + x
  > let esc = run h { Ref.new(0) }
  > KEL
  $ diktor --type-check rigids.kel
  ann : [A: Add] (A) => A
  ! rigids.kel:2:11: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

入れ子レコードの採番は読み順(§9.4 の評価順。行尾を先に採番しない。
M19 / G4b — かつては ^ の右辺が先に評価され R2 → R1 の逆順が出た):

  $ cat > rowname.kel <<'KEL'
  > let g = fn(r) => r.x.y
  > let h = fn(r) => (r.x.y, r.p.q)
  > KEL
  $ diktor --type-check --no-prelude rowname.kel
  g : ({x: {y: A extends R1} extends R2}) => A
  h : ({x: {y: A extends R1}, p: {q: B extends R2} extends R3}) => (A, B)

剛定数の制約は角括弧の前置に出さない(§9.2: ς はユーザが書ける名前では
ない。M19 / G4c — かつては [ς1: Add] ς1 と出た):

  $ cat > rigidcls.kel <<'KEL'
  > let cmp2[A: Add](x: A, y: A): Boolean = x < y
  > KEL
  $ diktor --type-check --no-prelude rigidcls.kel
  ! rigidcls.kel:1:41: 型エラー: 型パラメータ ς1 は Ord のインスタンスではありません。[A: Ord] のように制約を書いてください
  [1]

高階型変数の適用(TApp)の採番も読み順(M19 検証。頭が引数より後に
採番されて F より A が若くなる逆順が出ていた…はずが、頭が先):

  $ printf 'let idf2[F[_], A](x: F[A]): F[A] = x\nlet use3 = fn(w) => idf2(w)\n' > tapp.kel
  $ diktor --type-check --no-prelude tapp.kel
  idf2 : (F[A]) => F[A]
  use3 : (F[A]) => F[A]

タプルの再糖衣化は 3 形(§4。2 要素以上は (A, B)、1 要素は (A,)、空行は {}。
開いた行は戻さない):

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

エラーメッセージの表示にも同じ規則が及ぶ:

  $ printf 'let bad: (Int32,) = "x"\n' > resugar2.kel
  $ diktor --type-check --no-prelude resugar2.kel
  ! resugar2.kel:1:5: 型エラー: 注釈された型を満たしません(型が一致しません: (Int32,) と String)
  [1]
