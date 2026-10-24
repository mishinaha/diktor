KIR の評価器(--run-ir と --via-ir)は、論理的な深さ(IRSpec 11 節)で再帰の限度を数える。
限度は --max-depth N で変えられる。
最上位の初期化は深さ 0 で、末尾でない呼び出しは呼ばれた側を 1 つ深くし、末尾呼び出しは深さを変えない。
新しい深さが限度を超えると、その境目に入る前に実行時エラーにして 3 で終わる。
ここでは handle を含まないプログラムだけを扱う。

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
そのため、OCaml のスタックが尽きると、論理的な深さが限度に届く前でもスタックオーバーフローの実行時エラーで 3 で終わる(IRSpec 11.5 節)。
評価器は評価の前に OCaml のスタックの上限を上げるが、OCAMLRUNPARAM が l を与えたときはその値に従う。
上限を 1M 語にすると、8 重のブロックで囲んだ 10 万段の再帰は、限度 2^20 に届く前にスタックが尽きる。
上限を与えなければ、同じ再帰は最後まで走る。

  $ printf 'let rec f(n: Int32): Int32 = if n == 0 then 0 else 1 + { let a = { let b = { let c = { let d = { let e = { let g = { let h = { let i = f(n - 1); i }; h }; g }; e }; d }; c }; b }; a }\necholn(show(f(100000)))\n' > nest2.kel
  $ OCAMLRUNPARAM=l=1M diktor --via-ir nest2.kel; echo "exit: $?"
  実行時エラー: スタックオーバーフロー(再帰が深すぎます)
  exit: 3
  $ diktor --via-ir nest2.kel; echo "exit: $?"
  100000
  exit: 0
