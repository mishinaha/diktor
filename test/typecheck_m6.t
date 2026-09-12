M6(エフェクト行 / perform / handle / run / Rigid)のゴールデン。
変更時は dune promote で更新し、必ず目視レビューすること。

sample.kel §9 の核心(println / capture / try_ / with_file / copy)。
with_file の handle は write が Console と File の両方に宣言されていても
「全節が属し全操作が網羅される」File に解決される(D22)。
copy の perform write は行の最左の File に解決される(この例では最内
ハンドラと一致する。注釈した行では書かれた順 — 下の leftmost.kel):

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
  > let echo_test[E](): Unit @ {Console extends E} =
  >   println("test") handle {
  >     case print(message) => resume(perform Console.write(message))
  >     case return(x) => x
  >   }
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
  echo_test : () => {} @ {Console extends R1}
  captured : {value: {}, output: String}

EffectRow エイリアスの splice(sample.kel:572):

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

候補が 1 個なら行を見ずに解決する(§9 の規則は 2 段 — 曖昧なときだけ行の
最左を見る。ここで行を要求すると、注釈の無い let の perform が全部
修飾を要求されることになる。D99):

  $ cat > onecand.kel <<'EOF'
  > type Unit = {}
  > effect A1 = { op1: (String) => Unit }
  > let f() = perform op1("x")
  > EOF
  $ diktor --type-check --no-prelude onecand.kel
  f : () => {} @ {A1 extends R1}

候補が 2 個以上で、行にその候補が 1 つも現れないときだけ修飾を要求する:

  $ cat > twocand.kel <<'EOF'
  > type Unit = {}
  > effect A1 = { op1: (String) => Unit }
  > effect A2 = { op1: (String) => Unit }
  > let f() = perform op1("x")
  > EOF
  $ diktor --type-check --no-prelude twocand.kel
  ! twocand.kel:4:11: 型エラー: 操作 op1 は複数のエフェクト(A1, A2)に属します。A1.op1 のように修飾してください
  [1]

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
  ! rigidrow.kel:5:3: 型エラー: 行 ς1 は注釈で固定された行変数なので、ラベル C を足せません(注釈側に C を(必要なら引数つきで)書き足してください)
  [1]

非修飾操作名の解決は「行の最左」— 注釈された行では書かれた順であって
入れ子順ではない(M20 / I3。かつて本文が「最左 = 最内ハンドラ」と
一般化して書いていた誤りの反例。挙動は健全 — perform は解決済みの
完全名を運ぶので、実行時の捕捉と食い違わない):

  $ cat > leftmost.kel <<'KEL'
  > type Unit = {}
  > effect E1 = { op: (String) => Unit }
  > effect E2 = { op: (String) => Unit }
  > let f(): Unit @ {E1, E2} = perform op("f")
  > let g(): Unit @ {E2, E1} = perform op("g")
  > KEL
  $ diktor --type-check --no-prelude leftmost.kel
  f : () => {} @ {E1, E2 extends R1}
  g : () => {} @ {E2, E1 extends R1}

サブエフェクティングは無い(計画 §12 の意図した挙動の明示的な固定。
H4 / D23-a — @ {} は正確に空で、エフェクトのある文脈から呼べない。
公開 API の道は pub の @ 省略か行変数の明示。仕様への裁定要求は
260830-1 §3-2 / §3-6):

  $ cat > noSub.kel <<'KEL'
  > effect Logger = { log: (String) => Unit }
  > let pure_f(x: Int32): Int32 @ {} = x + 1
  > let impure(x: Int32): Int32 @ {Logger} = { perform log("hi"); pure_f(x) }
  > KEL
  $ diktor --type-check noSub.kel
  pure_f : (Int32) => Int32
  ! noSub.kel:3:63: 型エラー: ラベル Logger がありません(行は閉じています)(呼び出し先の行は空 = 純粋です。行の部分型付けが無いので、空でない行の下からは呼べません。入れ子の矢印の @ 省略は @ {} と読みます — 行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

行の並びは操作名の解決にだけ使い、型の等価性では順序を問わない(§9 / §3 の
Scoped Labels と同じ)。開いた行でも閉じた行でも順序違いは単一化する:

  $ cat > roworder.kel <<'EOF'
  > type Unit = {}
  > effect E1 = { op1: () => Unit }
  > effect E2 = { op2: () => Unit }
  > let a[E](k: () => Unit @ {E1, E2 extends E}): Unit @ {E1, E2 extends E} = k()
  > let b[E](k: () => Unit @ {E2, E1 extends E}): Unit @ {E1, E2 extends E} = a(k)
  > newtype Cb = Cb(() => Unit @ {E1, E2})
  > let mk(k: () => Unit @ {E2, E1}): Cb = Cb(k)
  > EOF
  $ diktor --type-check --no-prelude roworder.kel
  a : (() => {} @ {E1, E2 extends R1}) => {} @ {E1, E2 extends R1}
  b : (() => {} @ {E2, E1 extends R1}) => {} @ {E1, E2 extends R1}
  mk : (() => {} @ {E2, E1}) => Cb

同じエフェクトを二重に積むと、非修飾でも修飾でも内側にしか届かない(§9。
仕様の copy が src を読んでから dst を開くのはこのため):

  $ cat > doublestack.kel <<'KEL'
  > effect Tag = { tag: (String) => {} }
  > let with_tag[A, E](name: String, body: () => A @ {Tag, Console extends E}): A @ {Console extends E} =
  >   body() handle {
  >     case tag(s) => resume(echo(name + ":" + s + "\n"))
  >     case return(x) => x
  >   }
  > let go(): {} @ {Console} = {
  >   with _ = with_tag("outer")
  >   with _ = with_tag("inner")
  >   perform tag("hi")
  > }
  > go()
  > KEL
  $ diktor doublestack.kel
  inner:hi

修飾しても同じ(仕様 §9):

  $ sed 's/perform tag/perform Tag.tag/' doublestack.kel > doublestack2.kel
  $ diktor doublestack2.kel
  inner:hi

前方参照シグネチャは「注釈の頭の矢印に @ があること」で足りる(§9 改訂 / D79。
入れ子の省略 @ は @ {} に確定したので、宣言順に依存させる理由が消えた。
M26 より前は g の @ 省略だけで「未束縛の変数: helper」だった):

  $ cat > fwdsig.kel <<'KEL'
  > let user(): Int32 @ Console = helper(fn() => (), fn(n) => n)
  > let helper[E](f: () => Unit @ E, g: (Int32) => Int32): Int32 @ {Console extends E} = ???
  > KEL
  $ diktor --type-check fwdsig.kel
  user : () => Int32 @ {Console extends R1}
  helper : (() => {}, (Int32) => Int32) => Int32 @ {Console extends R1}
