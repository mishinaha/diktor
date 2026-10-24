KIR の評価器(--run-ir と --via-ir)は、論理的な深さ(IRSpec 11 節)で再帰の限度を数える。
限度は --max-depth N で変えられる。
最上位の初期化は深さ 0 で、末尾でない呼び出しは呼ばれた側を 1 つ深くし、末尾呼び出しは深さを変えない。
新しい深さが限度を超えると、その境目に入る前に実行時エラーにして 3 で終わる。
前半は handle を含まないプログラムを扱い、後半はハンドラ式の深さの規則を扱う。

末尾でない再帰は、限度 100 の下で f(98) まで通り、f(99) で限度を超える。
echoln を末尾でなく呼ぶ位置からの f(n) は深さ 1 で始まり、f(0) の深さは n + 1 になる。
f(0) から呼ぶ組み込みの Eq を合わせて n + 2 段で、f(99) は 101 段目に入ろうとして止まる。
止まった後の出力は書かない。
末尾呼び出しの 10 万回のループは、同じ限度の下で深さを増やさずに完走する。

  $ cat > nontail.kel <<'EOF'
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let rec loop(n: Int32): Int32 = if n == 0 then 0 else loop(n - 1)
  > echoln(show(loop(100000)))
  > echoln(show(f(98)))
  > echoln(show(f(99)))
  > echoln("not reached")
  > EOF
  $ diktor --via-ir --max-depth 100 nontail.kel; echo "exit: $?"
  0
  98
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3
  $ diktor --emit-ir nontail.kir nontail.kel && diktor --run-ir nontail.kir --max-depth 100; echo "exit: $?"
  0
  98
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

環境変数 DIKTOR_VIA_IR=1 は --via-ir と同じである。
木の評価器は論理的な深さを数えず、--max-depth は効かない。

  $ DIKTOR_VIA_IR=1 diktor --max-depth 100 nontail.kel; echo "exit: $?"
  0
  98
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3
  $ DIKTOR_VIA_IR=0 diktor --max-depth 100 nontail.kel; echo "exit: $?"
  0
  98
  99
  not reached
  exit: 0

組み込みの Array.each と pinned は、末尾でない位置から呼ぶと呼び出し元より 1 つ深く、利用者の関数をさらに 1 つ深く呼ぶ。
Array.each に渡した関数の中の f(x) は末尾でない呼び出しなので、f は深さ 3 で始まり、直接の呼び出しより 2 段早く止まる。
pinned に渡した関数は f を末尾で呼ぶので、f は深さ 2 で始まり、1 段早く止まる。

  $ cat > each.kel <<'EOF'
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let arr = run h { let a = MutableArray.new(1, 96); MutableArray.freeze(a) }
  > Array.each(arr, fn(x) => echoln(show(f(x))))
  > Array.each(arr, fn(x) => echoln(show(f(x + 1))))
  > EOF
  $ diktor --via-ir --max-depth 100 each.kel; echo "exit: $?"
  96
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3
  $ cat > pinned.kel <<'EOF'
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > echoln(show(pinned(fn() => f(97))))
  > echoln(show(pinned(fn() => f(98))))
  > EOF
  $ diktor --via-ir --max-depth 100 pinned.kel; echo "exit: $?"
  97
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

相互の末尾呼び出し、メソッドを通した末尾呼び出し、辞書を渡す末尾呼び出しも、深さを増やさない。
限度 10 の下で 10 万回続く。

  $ cat > tails.kel <<'EOF'
  > let rec even(n: Int32): Boolean = if n == 0 then true else odd(n - 1)
  > and odd(n: Int32): Boolean = if n == 0 then false else even(n - 1)
  > type class Step[A] { val step: (A, Int32) => Int32 }
  > type instance Step[Int32] { let rec step(x, n) = if n == 0 then x else step(x, n - 1) }
  > let rec count[A: Eq](x: A, n: Int32): Int32 = if n == 0 then 0 else if x == x then count(x, n - 1) else 1
  > echoln(show(even(100000)))
  > echoln(show(step(7, 100000)))
  > echoln(show(count("a", 100000)))
  > EOF
  $ diktor --via-ir --max-depth 10 tails.kel; echo "exit: $?"
  true
  7
  0
  exit: 0

演算子の呼び出し(`opcall`)は末尾位置にあっても末尾の呼び出しにならず(IRSpec 5.3 節)、1 段と数える。
f(0) は深さ n + 1 で add を末尾で呼び、add の本体の `a + b` が n + 2 段目に入る。

  $ cat > opcall.kel <<'EOF'
  > let add(a: Int32, b: Int32): Int32 = a + b
  > let rec f(n: Int32): Int32 = n match { case 0 => add(1, 2) case _ => 1 + f(n - 1) }
  > echoln(show(f(98)))
  > echoln(show(f(99)))
  > EOF
  $ diktor --via-ir --max-depth 100 opcall.kel; echo "exit: $?"
  101
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

辞書を渡す末尾でない再帰も、深さを 1 段ずつ数える。

  $ cat > dict.kel <<'EOF'
  > let rec g[A: Eq](x: A, n: Int32): Int32 = if n == 0 then 0 else { let r = g(x, n - 1); if x == x then r + 1 else r }
  > echoln(show(g(1, 50)))
  > echoln(show(g(1, 1000)))
  > EOF
  $ diktor --via-ir --max-depth 100 dict.kel; echo "exit: $?"
  50
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

--max-depth の値は 1 以上の 10 進の整数で、それ以外は使い方の誤り(64)である。

  $ diktor --via-ir --max-depth 0 nontail.kel 2>&1 | head -1
  diktor: --max-depth requires a positive integer: 0
  $ diktor --via-ir --max-depth 0 nontail.kel > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --via-ir --max-depth -5 nontail.kel > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --via-ir --max-depth 0x10 nontail.kel > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --via-ir --max-depth abc nontail.kel > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --via-ir --max-depth 99999999999999999999 nontail.kel > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --via-ir nontail.kel --max-depth > /dev/null 2>&1; echo "exit: $?"
  exit: 64

式の入れ子は深さに数えない。
呼び出しを 8 重のブロックで囲んでも、限度 100 の下で止まる位置は nontail.kel と同じである。

  $ cat > nest.kel <<'EOF'
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + { let a = { let b = { let c = { let d = { let e = { let g = { let h = { let i = f(n - 1); i }; h }; g }; e }; d }; c }; b }; a }
  > echoln(show(f(98)))
  > echoln(show(f(99)))
  > EOF
  $ diktor --via-ir --max-depth 100 nest.kel; echo "exit: $?"
  98
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

KIR の評価器は、末尾でない呼び出しのたびに OCaml のスタックも使い、1 段あたりの量は呼び出しを囲む式の入れ子が深いほど増える。
評価器は、末尾でない呼び出しの深さが 4096 の倍数になるたびに、その呼び出しを新しいファイバーで走らせる。
OCaml のスタックの上限はファイバーごとに掛かるので、上限は 4096 段の分のスタックにだけ掛かる。
そのため、OCAMLRUNPARAM で上限を 1M 語に絞っても、8 重のブロックで囲んだ 10 万段の再帰は最後まで走る。
上限を与えなくても同じである。

  $ printf 'let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + { let a = { let b = { let c = { let d = { let e = { let g = { let h = { let i = f(n - 1); i }; h }; g }; e }; d }; c }; b }; a }\necholn(show(f(100000)))\n' > nest2.kel
  $ OCAMLRUNPARAM=l=1M diktor --via-ir nest2.kel; echo "exit: $?"
  100000
  exit: 0
  $ diktor --via-ir nest2.kel; echo "exit: $?"
  100000
  exit: 0

ハンドラ式の本体は、ハンドラ式を評価した深さ h より 1 つ深い。
深さ p で perform を起こすと、節の選択と T の節の本体は p + 1 で走り、G の節の本体は h + 1 で走る。
t と g は、どちらも深さ 1 でハンドラ式を評価し、本体は深さ 2 で走る。
本体の dive(50) は深さ 3 で始まり、dive(0) が深さ 53 で ask を起こす。
T の節の本体は深さ 54 で走り、resume の引数の f(n) の中の f(0) の比較は n + 56 段目になる。
そのため t(50, 44) まで通り、t(50, 45) で止まる。
G の節の本体は深さ 2 で走り、f(n) の中の f(0) の比較は n + 4 段目になる。
そのため g(50, 96) は通り、g(50, 97) で止まる。
木の評価器では、どれも最後まで走る。

  $ cat > tg.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let rec dive(k: Int32): Int32 @ {Ask} = if k == 0 then perform ask() else 1 + dive(k - 1)
  > let t(k: Int32, n: Int32): Int32 = dive(k) handle { case ask() => resume(f(n)) }
  > let g(k: Int32, n: Int32): Int32 = dive(k) handle { case ask() => { let v = f(n); let r = resume(v); r } }
  > echoln(show(g(50, 96)))
  > echoln(show(t(50, 44)))
  > echoln(show(t(50, 45)))
  > EOF
  $ diktor --via-ir --max-depth 100 tg.kel; echo "exit: $?"
  146
  94
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3
  $ DIKTOR_VIA_IR=0 diktor tg.kel; echo "exit: $?"
  146
  94
  95
  exit: 0
  $ cat > tg2.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let rec dive(k: Int32): Int32 @ {Ask} = if k == 0 then perform ask() else 1 + dive(k - 1)
  > let g(k: Int32, n: Int32): Int32 = dive(k) handle { case ask() => { let v = f(n); let r = resume(v); r } }
  > echoln(show(g(50, 96)))
  > echoln(show(g(50, 97)))
  > EOF
  $ diktor --via-ir --max-depth 100 tg2.kel; echo "exit: $?"
  146
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

末尾でない resume で継続を深さ c で再開すると、継続の中の文脈の深さと、継続の中で始まったハンドラの深さが、c − h だけずれる(IRSpec 11.4 節)。
h は、継続を取り出したハンドラの深さである。
outer は深さ 1 でハンドラ式を評価し(h = 1)、本体の inner(n) は深さ 3 で内側のハンドラ式を評価する。
内側のハンドラ式の本体は深さ 4 で tick を起こし、外側の G の節の本体は深さ 2 で resume する。
c − h = 1 なので、内側のハンドラの深さは 3 から 4 にずれ、その return 節は深さ 4 で走る。
return 節は f(n) を末尾で呼ぶので、f(0) の比較は n + 5 段目になる。
そのため outer(95) まで通り、outer(96) で止まる。
深さをずらさなければ、outer(96) も通る。

  $ cat > shift.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > effect Tick = { tick: () => Unit }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let inner(n: Int32): Int32 @ {Tick} = { perform tick(); 0 } handle { case ask() => resume(0) case return(v) => f(n) }
  > let outer(n: Int32): Int32 = inner(n) handle { case tick() => { let r = resume(()); r } }
  > echoln(show(outer(95)))
  > echoln(show(outer(96)))
  > EOF
  $ diktor --via-ir --max-depth 100 shift.kel; echo "exit: $?"
  95
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

T の節の本体を評価している間は、そのハンドラが連鎖から外れている。
そこから外側のハンドラの G の操作を起こすと、外れていたハンドラは、外側の継続の中の文脈からだけ届く。
外側が c ≠ h で再開すると、このハンドラの深さもずれる。
inner は深さ 3 でハンドラ式を評価し、その本体は深さ 4 で ask を起こす。
T の節の本体は深さ 5 で tick を起こし、外側の G の節の本体は深さ 2 で resume するので、ずれは 1 である。
T の節の本体は末尾の resume で ask の継続を再開し、内側の本体は 1 を返す。
内側の return 節はずれた深さ 4 で走り、f(n) を末尾でなく呼ぶので、f(0) の比較は n + 6 段目になる。
outer(94) は 1 + 94 を印字し、outer(95) で止まる。

  $ cat > shiftt.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > effect Tick = { tick: () => Unit }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let inner(n: Int32): Int32 @ {Tick} = perform ask() handle { case ask() => { perform tick(); resume(1) } case return(v) => v + f(n) }
  > let outer(n: Int32): Int32 = inner(n) handle { case tick() => { let r = resume(()); r } }
  > echoln(show(outer(94)))
  > echoln(show(outer(95)))
  > EOF
  $ diktor --via-ir --max-depth 100 shiftt.kel; echo "exit: $?"
  95
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

継続の中の節が取り出して、まだ再開していない継続も、外側の継続を c ≠ h で再開するとずれる。
継続の中のフレームと Δ = p − h は、それを取り出した起動の h からの差として決まるからである。
outer は深さ 1 でハンドラ式を評価し(h = 1)、inner は深さ 3 で内側のハンドラ式を評価する(h = 3)。
内側の本体は深さ 4 で ask を起こし、内側の G の節の本体は深さ 4 で走って tick を起こす。
外側の G の節は深さ 2 で resume するので、ずれは 1 で、内側の h は 4 になり、内側の節の続きは深さ 5 で走る。
内側の節は、まだ再開していない ask の継続を深さ 5 で resume する。
その Δ は 1 なので、ask の perform は深さ 6 に戻り、f(n) の中の f(0) の比較は n + 8 段目になる。
そのため outer(92) まで通り、outer(93) で止まる。
ask の継続のフレームをずらさなければ、outer(93) も通る。

  $ cat > k2.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > effect Tick = { tick: () => Unit }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let inner(n: Int32): Int32 @ {Tick} = { let a = perform ask(); a + f(n) } handle { case ask() => { perform tick(); let r = resume(1); r } }
  > let outer(n: Int32): Int32 = inner(n) handle { case tick() => { let r = resume(()); r } }
  > echoln(show(outer(91)))
  > echoln(show(outer(92)))
  > echoln(show(outer(93)))
  > EOF
  $ diktor --via-ir --max-depth 100 k2.kel; echo "exit: $?"
  92
  93
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3
  $ DIKTOR_VIA_IR=0 diktor k2.kel; echo "exit: $?"
  92
  93
  94
  exit: 0

まだ再開していない継続の中で始まったハンドラの起動の h も、外側の継続を c ≠ h で再開するとずれる。
その継続を再開せずに捨てると、その中の起動の cancel 節は、ずれた後の h で走る。
outerG は深さ 1 でハンドラ式を評価し(h = 1)、inner は深さ 3 で ask のハンドラ式を評価する(h = 3)。
zz のハンドラ式は深さ 4 にあり(h = 4)、その本体は深さ 5 で ask を起こす。
ask の節は G の節で、その本体は深さ 4 で走って tick を起こす。
outerG の節は深さ 2 で resume するので、ずれは 1 で、ask の起動の h は 4、zz の起動の h は 5 になる。
ask の節は resume せずに 5 を返すので、zz の起動を含む ask の継続を捨て、zz の cancel 節が深さ 5 で走る。
f(m) の中の f(0) の比較は m + 7 段目になるので、outerG(93) は 93 を印字し、outerG(94) では cancel 節の中で限度を超える。
outerT の節は末尾の resume なのでずれず、zz の cancel 節は深さ 4 で走り、境目は 1 つ深い。

  $ cat > k2drop.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > effect Tick = { tick: () => Unit }
  > effect Zz = { zz: () => Unit }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let inner(m: Int32): Int32 @ {Tick, Console} = ({ let a = perform ask(); a } handle { case zz() => resume(()) case cancel => echoln(show(f(m))) }) handle { case ask() => { perform tick(); if 1 == 2 then { let r = resume(1); r } else 5 } }
  > let outerG(m: Int32): Int32 = inner(m) handle { case tick() => { let r = resume(()); r } }
  > let outerT(m: Int32): Int32 = inner(m) handle { case tick() => resume(()) }
  > echoln(show(outerG(93)))
  > echoln(show(outerG(94)))
  > echoln(show(outerT(94)))
  > echoln(show(outerT(95)))
  > EOF
  $ diktor --via-ir --max-depth 100 k2drop.kel; echo "exit: $?"
  93
  5
  cancel 節で例外が抑制されました: 論理的な深さが限度 100 を超えました
  5
  94
  5
  cancel 節で例外が抑制されました: 論理的な深さが限度 100 を超えました
  5
  exit: 0
  $ DIKTOR_VIA_IR=0 diktor k2drop.kel; echo "exit: $?"
  93
  5
  94
  5
  94
  5
  95
  5
  exit: 0

末尾でない resume は、再開した perform の深さ c + Δ(Δ = p − h)を、継続を再開する前に限度と比べる。
d(k) は深さ 1 でハンドラ式を評価し、dive(k) は深さ k + 3 で ask を起こすので、Δ = k + 2 である。
G の節の本体は深さ 2 で走り、resume は節の中のハンドラ式の本体(深さ 3)にあるので、c + Δ = k + 5 になる。
d(95) では c + Δ = 100 で、再開した計算は 2 だけずれた深さで最後まで走り、after と 96 を印字する。
d(96) では、節の選択の深さ k + 4 = 100 は限度の内にあり、resume の c + Δ = 101 が限度を超える。
継続はまだ使っていないので、節が resume の前に脱出したときと同じく継続を捨てて巻き戻し、ハンドラの cancel 節が走る。
resume の後の after は印字しない。

  $ cat > over.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > effect Tick = { tick: () => Unit }
  > let rec dive(k: Int32): Int32 @ {Ask} = if k == 0 then perform ask() else 1 + dive(k - 1)
  > let d(k: Int32): Int32 = dive(k) handle {
  >   case ask() => { let r = resume(1) handle { case tick() => resume(()) }; echoln("after"); r }
  >   case cancel => echoln("cancel")
  > }
  > echoln(show(d(95)))
  > echoln(show(d(96)))
  > EOF
  $ diktor --via-ir --max-depth 100 over.kel; echo "exit: $?"
  after
  96
  cancel
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

深さの限度を超えると、ほかの実行時エラーと同じく、有効なハンドラを内側から巻き戻して cancel 節を走らせる。

  $ cat > cancel.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let c2(): Int32 = (f(1000) handle { case ask() => resume(0) case cancel => echoln("cancel inner") }) handle { case ask() => resume(0) case cancel => echoln("cancel outer") }
  > echoln(show(c2()))
  > EOF
  $ diktor --via-ir --max-depth 100 cancel.kel; echo "exit: $?"
  cancel inner
  cancel outer
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

限度を超えた誤りが伝播している間は、限度を予備 R = max(1024, L / 64) だけ広げる(IRSpec 11.5 節)。
限度 100 では R = 1024 で、cancel 節は深さ 1124 まで使える。
c1 は深さ 1 でハンドラ式を評価し、cancel 節も深さ 1 で走る。
cancel 節の f(m) の中の f(0) の比較は m + 3 段目なので、c1(1121) の cancel 節は最後まで走って 1121 を印字する。
c1(1122) の cancel 節は予備の中でも限度を超え、その脱出は cancel 節の打ち切りとして記録される。
どちらも、その後で元の誤りが最上位に届いて 3 で終わる。

  $ cat > reserve.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let c1(m: Int32): Int32 = f(1000) handle { case ask() => resume(0) case cancel => echoln(show(f(m))) }
  > echoln(show(c1(1121)))
  > EOF
  $ diktor --via-ir --max-depth 100 reserve.kel; echo "exit: $?"
  1121
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3
  $ cat > reserve2.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let c1(m: Int32): Int32 = f(1000) handle { case ask() => resume(0) case cancel => echoln(show(f(m))) }
  > echoln(show(c1(1122)))
  > EOF
  $ diktor --via-ir --max-depth 100 reserve2.kel; echo "exit: $?"
  cancel 節で例外が抑制されました: 論理的な深さが限度 100 を超えました
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

cancel 節は、走る前の限度を覚えておき、節を出るときにその値へ戻す(IRSpec 11.5 節)。
そのため、cancel 節の中で限度を超え、その脱出が打ち切られて記録されると、限度は L に戻る。
rs.kel では、外側の N の節が内側の継続を捨て、内側の cancel 節の f(200) が限度 100 を超える。
その脱出は打ち切られて記録され、外側の N の節の値 7 が r になる。
その後の f(500) は、予備でなく限度 100 の下で走るので止まる。
限度を戻さなければ、f(500) は予備 R = 1024 の中で最後まで走る。

  $ cat > rs.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > effect Fail = { fail: () => Never }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let inner() = { perform fail(); 0 } handle { case ask() => resume(0) case cancel => echoln(show(f(200))) }
  > let r = inner() handle { case fail() => 7 }
  > echoln(show(r))
  > echoln(show(f(500)))
  > EOF
  $ diktor --via-ir --max-depth 100 rs.kel; echo "exit: $?"
  cancel 節で例外が抑制されました: 論理的な深さが限度 100 を超えました
  7
  実行時エラー: 論理的な深さが限度 100 を超えました
  exit: 3

伝播している誤りが深さの限度の誤りでなければ、cancel 節は予備を使えない。
rs2.kel では、ゼロ除算の誤りが伝播し、内側の cancel 節の f(200) が限度 100 を超えて打ち切られる。
限度は 100 に戻るので、外側の cancel 節の f(500) も打ち切られる。
その後で、元のゼロ除算の誤りが最上位に届いて 3 で終わる。
木の評価器では、どちらの cancel 節も最後まで走る。

  $ cat > rs2.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + f(n - 1)
  > let z(d: Int32): Int32 = 1 / d
  > let c(): Int32 = (z(0) handle { case ask() => resume(0) case cancel => echoln(show(f(200))) }) handle { case ask() => resume(0) case cancel => echoln(show(f(500))) }
  > echoln(show(c()))
  > EOF
  $ diktor --via-ir --max-depth 100 rs2.kel; echo "exit: $?"
  cancel 節で例外が抑制されました: 論理的な深さが限度 100 を超えました
  cancel 節で例外が抑制されました: 論理的な深さが限度 100 を超えました
  実行時エラー: ゼロ除算です
  exit: 3
  $ DIKTOR_VIA_IR=0 diktor rs2.kel; echo "exit: $?"
  200
  500
  実行時エラー: ゼロ除算です
  exit: 3

末尾の resume は深さを変えず、N の節の本体は深さ h で走る。
限度 10 の下で、T の節の末尾の resume、G の節の末尾の resume、N の節の本体から同じハンドラ式を評価し直す再試行が、どれも 10 万回続く。

  $ cat > loops.kel <<'EOF'
  > effect Tick = { tick: () => Unit }
  > effect Fail = { fail: () => Never }
  > let rec ticks(n: Int32): Unit @ {Tick} = if n == 0 then () else { perform tick(); ticks(n - 1) }
  > let rec retry(n: Int32): Int32 = (if n == 0 then 0 else { perform fail(); 1 }) handle { case fail() => retry(n - 1) }
  > ticks(100000) handle { case tick() => resume(()) }
  > echoln("T")
  > ticks(100000) handle { case tick() => if false then { let r = resume(()); r } else resume(()) }
  > echoln("G")
  > echoln(show(retry(100000)))
  > EOF
  $ diktor --via-ir --max-depth 10 loops.kel; echo "exit: $?"
  T
  G
  0
  exit: 0
