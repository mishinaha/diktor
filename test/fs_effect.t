ファイル I/O の行 Fs(仕様 §9、sample.kel:465, :594-600。M27 / D87)。__open /
__read / __write / __close は @ Fs を載せるので、純粋な文脈からは呼べない。
かつては行なしで型付き、@ {} のコールバックからファイルを触れた(260829-5 台帳 V15)。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

プリミティブの型に Fs が載る。注釈した包み(o / r / w / c)は行が許容的なので
証拠にならない — 注釈なしの別名(p_*)が prim 自身の型を見せる(検証の指摘):

  $ cat > sig.kel <<'KEL'
  > let o(p: String): Int32 @ Fs = __open(p)
  > let r(h: Int32): String @ Fs = __read(h)
  > let w(h: Int32, s: String): Unit @ Fs = __write(h, s)
  > let c(h: Int32): Unit @ Fs = __close(h)
  > let p_open = __open
  > let p_read = __read
  > let p_write = __write
  > let p_close = __close
  > KEL
  $ diktor --type-check sig.kel
  o : (String) => Int32 @ {Fs extends R1}
  r : (Int32) => String @ {Fs extends R1}
  w : (Int32, String) => {} @ {Fs extends R1}
  c : (Int32) => {} @ {Fs extends R1}
  p_open : (String) => Int32 @ {Fs extends R1}
  p_read : (Int32) => String @ {Fs extends R1}
  p_write : (Int32, String) => {} @ {Fs extends R1}
  p_close : (Int32) => {} @ {Fs extends R1}

純粋な文脈からは呼べない:

  $ printf 'let pure_open(p: String): Int32 @ {} = __open(p)\n' > pure.kel
  $ diktor --type-check pure.kel
  ! pure.kel:1:40: 型エラー: ラベル Fs がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

pub の省略 @(純粋)も同じ:

  $ printf 'pub let f(): Int32 = __open("x")\n' > pub.kel
  $ diktor --type-check pub.kel
  ! pub.kel:1:22: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: 行 ς1 は注釈で固定された行変数なので、ラベル Fs を足せません(注釈側に Fs を(必要なら引数つきで)書き足してください))
  [1]

V15 の穴が閉じた — par / par_map の @ {} コールバックから触れない:

  $ cat > par_fs.kel <<'KEL'
  > let arr(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(1, 0)) }
  > let _ = par_map(arr(), fn(x) => __open("secret"))
  > KEL
  $ diktor --type-check par_fs.kel
  arr : () => Array[Int32]
  ! par_fs.kel:2:33: 型エラー: ラベル Fs がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]
  $ printf 'let p = par(fn() => __open("a"), fn() => 1)\n' > par2.kel
  $ diktor --type-check par2.kel
  ! par2.kel:1:21: 型エラー: ラベル Fs がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

トップレベルには Fs が載っているので、そこからは呼べる(仕様 sample.kel:655):

  $ cat > top.kel <<'KEL'
  > let h = __open("a.txt")
  > let _ = __write(h, "hello")
  > let _ = __close(h)
  > let g = __open("a.txt")
  > echoln(__read(g))
  > KEL
  $ diktor top.kel
  hello

Fs はランタイムが提供するのでユーザはハンドルできない(D90。操作を持たないので
非修飾では候補にも挙がらない。修飾で名指ししたときだけこの診断に届く):

  $ cat > fsh.kel <<'KEL'
  > let f[A, E](b: () => A @ {Fs extends E}): A @ E =
  >   b() handle {
  >     case Fs.nope() => resume({})
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check fsh.kel
  ! fsh.kel:2:3: 型エラー: エフェクト Fs はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:445, :511)。ファイル操作を差し替えたいときは File のような自前のエフェクトをハンドルしてください(仕様 sample.kel:575 の with_file が見本)
  [1]

仕様 sample.kel が自分で effect Fs = {} を宣言する形は、D35 の構造照合で
受理される(操作なしどうしで一致)。with_file を二重に積んで read が src 側、
write が dst 側に解決することも実行で示す:

  $ cat > fsdecl.kel <<'KEL'
  > effect Fs = {}
  > effect File = {
  >   read:  () => String,
  >   write: (String) => Unit,
  > }
  > let with_file[A, E](path: String, body: () => A @ {File, Fs extends E}): A @ {Fs extends E} = {
  >   let h = __open(path)
  >   body() handle {
  >     case read()    => resume(__read(h))
  >     case write(s)  => resume(__write(h, s))
  >     case return(x) => { __close(h); x }
  >     case cancel    => __close(h)
  >   }
  > }
  > let copy(src: String, dst: String): Unit @ {Console, Fs} = {
  >   with _ = with_file(src)
  >   let text = perform read()
  >   with _ = with_file(dst)
  >   perform write(text)
  > }
  > let seed(): Unit @ Fs = {
  >   let h = __open("src.txt")
  >   __write(h, "hello")
  >   __close(h)
  > }
  > seed()
  > copy("src.txt", "dst.txt")
  > let back = { let h = __open("dst.txt"); let s = __read(h); __close(h); s }
  > echoln("dst=[" + back + "]")
  > KEL
  $ diktor fsdecl.kel
  dst=[hello]

操作を足した再宣言は照合で落ちる:

  $ printf 'effect Fs = { op1: () => Int32 }\n' > fsbad.kel
  $ diktor --type-check fsbad.kel
  ! fsbad.kel:1:1: 型エラー: effect Fs の宣言がプレリュードの宣言と一致しません(操作が違います: プレリュードは操作を持ちません)
  [1]

プレリュードの extern は再宣言できない(@ Fs を剥がす経路を塞ぐ):

  $ printf 'extern "prim" let __open(p: String): Int32\n' > reo.kel
  $ diktor --type-check reo.kel
  ! reo.kel:1:1: 型エラー: プレリュードの extern __open は再宣言できません
  [1]
  $ printf 'module M { extern "prim" let __open(p: String): Int32 }\n' > reo2.kel
  $ diktor --type-check reo2.kel
  ! reo2.kel:1:12: 型エラー: プレリュードの extern __open は再宣言できません
  [1]

newtype のフィールドを経由して Fs を洗う形(V14)も、M26 で入れ子の省略 @ が
@ {} になったので閉じている — Fs と V14 の両方が揃って初めて決定性が守れる:

  $ cat > v14.kel <<'KEL'
  > newtype Cb = Cb(() => Int32)
  > let run_cb(c: Cb): Int32 = c match { case Cb(f) => f() }
  > let arr(): Array[Int32] = run h { MutableArray.freeze(MutableArray.new(1, 0)) }
  > let touched = par_map(arr(), fn(x) => run_cb(Cb(fn() => { let h = __open("secret"); __write(h, "leaked"); __close(h); 1 })))
  > let back = { let h = __open("secret"); let s = __read(h); __close(h); s }
  > echoln("read back: [" + back + "]")
  > KEL
  $ diktor --type-check v14.kel
  run_cb : (Cb) => Int32
  arr : () => Array[Int32]
  ! v14.kel:4:46: 型エラー: ラベル Fs がありません(行は閉じています)(コンストラクタ Cb のフィールドの行です。newtype のフィールドの矢印は書いたとおりに読み、@ の省略は @ {} — 純粋 — です。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

--no-prelude では Fs はトップレベル行に載らない(Console / Async と同じく
プレリュード所有ではないため。Blocking だけは組み込み登録なので載る —
test/blocking_top.t の bnp)。自前の effect Fs = {} と自前の prim は宣言できるが、
トップレベルから呼ぶ手段は無い(検証の指摘。§11.30)。--prelude で Fs を宣言する
差し替えなら所有になり、載る:

  $ cat > npfs.kel <<'KEL'
  > type Unit = {}
  > effect Fs = {}
  > extern "prim" let __open(path: String): Int32 @ Fs
  > extern "prim" let __close(h: Int32): Unit @ Fs
  > let main(): Unit @ Fs = { let h = __open("a"); __close(h) }
  > main()
  > KEL
  $ diktor --type-check --no-prelude npfs.kel
  __open : (String) => Int32 @ {Fs extends R1}
  __close : (Int32) => {} @ {Fs extends R1}
  main : () => {} @ {Fs extends R1}
  ! npfs.kel:6:1: 型エラー: ラベル Fs がありません(行は閉じています)
  [1]
  $ printf 'type Unit = {}\neffect Fs = {}\nextern "prim" let __open(path: String): Int32 @ Fs\nextern "prim" let __close(h: Int32): Unit @ Fs\n' > fspre.kel
  $ printf 'let main(): Unit @ Fs = { let h = __open("a"); __close(h) }\nmain()\n' > withpre.kel
  $ diktor --prelude fspre.kel --type-check withpre.kel
  main : () => {} @ {Fs extends R1}
  _ : {}
