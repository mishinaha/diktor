M6(エフェクト行 / perform / handle / run / Rigid)のゴールデン。
変更時は dune promote で更新し、必ず目視レビューすること。

sample.kel §9 の核心(println / capture / try_ / with_file / copy)。
with_file の handle は write が Console と File の両方に宣言されていても
「全節が属し全操作が網羅される」File に解決される(D22)。
copy の perform write は行の最左(最内ハンドラ)の File に解決される:

  $ cat > eff9.kel <<'EOF'
  > type Unit = {}
  > effect Print   = { print: (String) => Unit }
  > effect Console = { write: (String) => Unit }
  > let println(message: String): Unit @ Print = perform print(message + "\n")
  > let capture[A, E](body: () => A @ {Print extends E}): {value: A, output: String} @ E =
  >   body() handle {
  >     case print(message) => {
  >       let {value, output} = resume()
  >       {value, output = message + output}
  >     }
  >     case return(x) => {value = x, output = ""}
  >   }
  > effect Fail = { throw: (String) => Never }
  > let try_[A, E](body: () => A @ {Fail extends E}): #Ok(A) | #Err(String) @ E =
  >   body() handle {
  >     case throw(e)  => #Err(e)
  >     case return(x) => #Ok(x)
  >   }
  > effect File = {
  >   read:  () => String,
  >   write: (String) => Unit,
  > }
  > extern "prim" let __open(path: String): Int32
  > extern "prim" let __read(h: Int32): String
  > extern "prim" let __write(h: Int32, s: String): Unit
  > extern "prim" let __close(h: Int32): Unit
  > let with_file[A, E](path: String, body: () => A @ {File extends E}): A @ E = {
  >   let h = __open(path)
  >   body() handle {
  >     case read()    => resume(__read(h))
  >     case write(s)  => resume(__write(h, s))
  >     case return(x) => { __close(h); x }
  >     case cancel    => __close(h)
  >   }
  > }
  > let copy(src: String, dst: String): Unit @ Console = {
  >   with _ = with_file(src)
  >   with _ = with_file(dst)
  >   perform write(perform read())
  > }
  > println("test") handle {
  >   case print(message) => resume(perform write(message))
  >   case return(x) => x
  > }
  > let captured = capture(fn() => println("test"))
  > EOF
  $ diktor --type-check --no-prelude eff9.kel
  println : (String) => {} @ {Print extends R1}
  capture : (() => A @ {Print extends R1}) => {value: A, output: String}
  try_ : (() => A @ {Fail extends R1}) => #Ok(A) | #Err(String)
  __open : (String) => Int32
  __read : (Int32) => String
  __write : (Int32, String) => {}
  __close : (Int32) => {}
  with_file : (String, () => A @ {File extends R1}) => A
  copy : (String, String) => {} @ {Console extends R1}
  _ : {}
  captured : {value: {}, output: String}

EffectRow エイリアスの splice(sample.kel:446):

  $ cat > effrow.kel <<'EOF'
  > type Unit = {}
  > effect ReqId  = { req_id: () => String }
  > effect Logger = { log: (String) => Unit }
  > type Request: EffectRow = {ReqId, Logger}
  > let logged(): Unit @ Request = perform log(perform req_id())
  > EOF
  $ diktor --type-check --no-prelude effrow.kel
  logged : () => {} @ {ReqId, Logger extends R1}

D22 のエラー経路(修飾要求)と修飾解決:

  $ cat > ambig.kel <<'EOF'
  > type Unit = {}
  > effect A1 = { op1: (String) => Unit }
  > effect A2 = { op1: (String) => Unit }
  > let bad(): Unit = perform op1("x")
  > EOF
  $ diktor --type-check --no-prelude ambig.kel
  ! ambig.kel:4:19: 型エラー: 操作 op1 は複数のエフェクト(A1, A2)に属します。A1.op1 のように修飾してください
  [1]

  $ cat > qual.kel <<'EOF'
  > type Unit = {}
  > effect A1 = { op1: (String) => Unit }
  > effect A2 = { op1: (String) => Unit }
  > let ok(): Unit @ A2 = perform A2.op1("x")
  > EOF
  $ diktor --type-check --no-prelude qual.kel
  ok : () => {} @ {A2 extends R1}

未処理エフェクト・網羅性・resume の誤用のエラー:

  $ cat > efferr.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > let bad(): Unit @ {} = perform print("x")
  > EOF
  $ diktor --type-check --no-prelude efferr.kel
  ! efferr.kel:3:24: 型エラー: エフェクト Print をここでは実行できません(ラベル Print がありません(行は閉じています))
  [1]

  $ cat > efferr2.kel <<'EOF'
  > type Unit = {}
  > effect File2 = { read2: () => String, write2: (String) => Unit }
  > let bad = fn(body) => body() handle {
  >   case read2() => resume("")
  >   case return(x) => x
  > }
  > EOF
  $ diktor --type-check --no-prelude efferr2.kel
  ! efferr2.kel:3:23: 型エラー: ハンドラが操作を網羅していません: File2 の write2 が漏れています
  [1]

  $ cat > efferr3.kel <<'EOF'
  > let bad = resume(1)
  > EOF
  $ diktor --type-check --no-prelude efferr3.kel
  ! efferr3.kel:1:11: 型エラー: resume は操作節の中でのみ使えます
  [1]

  $ cat > efferr4.kel <<'EOF'
  > type Unit = {}
  > effect Print = { print: (String) => Unit }
  > let bad = fn(body) => body() handle {
  >   case print(m) => fn() => resume(())
  >   case return(x) => x
  > }
  > EOF
  $ diktor --type-check --no-prelude efferr4.kel
  ! efferr4.kel:4:28: 型エラー: resume は second-class です(クロージャに閉じ込める・節の外へ持ち出すことはできません)
  [1]

MiniLang §16-7(run と脱出検査、全6例。§9.3 の期待どおり):

  $ cat > st.kel <<'EOF'
  > let ok1 = run h { let r = Ref.new(0); Ref.set(r, 42); Ref.get(r) }
  > let ok2 = run h { let x = run h2 { Ref.get(Ref.new(1)) }; x + 1 }
  > let poly = fn(u) => Ref.new(0)
  > EOF
  $ diktor --type-check --no-prelude st.kel
  ok1 : Int32
  ok2 : Int32
  poly : (A) => Ref[B, Int32] @ {Heap[B] extends R1}

  $ cat > stbad1.kel <<'EOF'
  > let bad = run h { Ref.new(0) }
  > EOF
  $ diktor --type-check --no-prelude stbad1.kel
  ! stbad1.kel:1:11: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

  $ cat > stbad2.kel <<'EOF'
  > let bad = run h { let r = Ref.new(0); fn(u) => Ref.get(r) }
  > EOF
  $ diktor --type-check --no-prelude stbad2.kel
  ! stbad2.kel:1:11: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

  $ cat > stbad3.kel <<'EOF'
  > let bad = run h { let r = Ref.new(0); run h2 { Ref.get(r) } }
  > EOF
  $ diktor --type-check --no-prelude stbad3.kel
  ! stbad3.kel:1:56: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
  [1]

MiniLang §16-8 の runST 2例(値制限):

  $ cat > stvr.kel <<'EOF'
  > type Unit = {}
  > let bad = run h {
  >   let r = Ref.new(fn(x) => x)
  >   Ref.set(r, fn(n) => n + 1)
  >   Ref.get(r)(true)
  > }
  > EOF
  $ diktor --type-check --no-prelude stvr.kel
  ! stvr.kel:5:14: 型エラー: Boolean は Add のインスタンスではありません
  [1]

剛な行変数へのラベル追加は原因を語る(M20 / I9。かつては
「行型ではありません: ς1」で、高階のエフェクト注釈の書き間違いに
最初に出る診断が原因に辿れなかった):

  $ cat > rigidrow.kel <<'KEL'
  > type Unit = {}
  > effect E1 = { op: (String) => Unit }
  > effect C = { wr: (String) => Unit }
  > let h1[A, E](b: () => A @ {E1 extends E}): A @ {C extends E} =
  >   b() handle {
  >     case op(s) => resume(perform wr(s))
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check --no-prelude rigidrow.kel
  ! rigidrow.kel:5:3: 型エラー: 行 ς1 は注釈で固定された行変数なので、ラベル C を足せません(注釈側に C を書き足してください)
  [1]
