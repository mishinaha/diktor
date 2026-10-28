--emit-ir-text FILE は、型検査を通したプログラムを、実行せずに KIR の正準のテキスト(IRSpec 12 節)で FILE に書く。
型検査の誤りは今までどおり 1 で終わり、FILE を作らない。
旗の引数を省くと使い方の誤り(64)で、FILE に書けなければ出力の誤り(74)である。

  $ printf 'let x: Int32 = true\n' > bad.kel
  $ diktor --emit-ir-text bad.kirt bad.kel; echo "exit: $?"; test -e bad.kirt || echo "no file"
  ! bad.kel:1:5: 型エラー: 注釈された型を満たしません(型が一致しません: Int32 と Boolean)
  exit: 1
  no file
  $ diktor --emit-ir-text 2>&1 | head -1; diktor --emit-ir-text > /dev/null 2>&1; echo "exit: $?"
  diktor: --emit-ir-text requires a path
  exit: 64
  $ printf 'let x = 1\n' > ok.kel
  $ diktor --no-prelude --emit-ir-text nodir/x.kirt ok.kel; echo "exit: $?"
  diktor: KIR のテキストを書き出せません: nodir/x.kirt: No such file or directory
  exit: 74

--emit-ir-text は実行のモードの旗なので、ほかのモードの旗と併せると使い方の誤り(64)で、FILE を作らない。

  $ diktor --type-check --emit-ir-text tc.kirt ok.kel 2>&1 | head -1; diktor --type-check --emit-ir-text tc.kirt ok.kel > /dev/null 2>&1; echo "exit: $?"; test -e tc.kirt || echo "no file"
  diktor: --emit-ir-text cannot be combined with --type-check, --dump-tokens, --dump-ast or --repl
  exit: 64
  no file
  $ diktor --dump-ast --emit-ir-text da.kirt ok.kel > /dev/null 2>&1; echo "exit: $?"; test -e da.kirt || echo "no file"
  exit: 64
  no file

最小のプログラムのファイルの全体。
見出し、単位、組み込みの型とクラスと値の表、関数、初期化の順に並ぶ。
`--no-prelude` でも、手順の無い prelude の単位を書く。

  $ printf 'let x = 1\n' > one.kel
  $ diktor --no-prelude --emit-ir-text one.kirt one.kel && cat one.kirt
  (kir 1 0 0)
  (unit "builtin" (paths))
  (unit "prelude" (paths))
  (unit "main" (paths "one.kel"))
  (type "builtin/Boolean")
  (type "builtin/Int32")
  (type "builtin/Int64")
  (type "builtin/Float64")
  (type "builtin/String")
  (type "builtin/Never")
  (type "builtin/Ref")
  (type "builtin/Array")
  (type "builtin/MutableArray")
  (class "builtin/Add" (method add 0))
  (class "builtin/Sub" (method sub 0))
  (class "builtin/Mul" (method mul 0))
  (class "builtin/Div" (method div 0))
  (class "builtin/Rem" (method rem 0))
  (class "builtin/Neg" (method neg 0))
  (class "builtin/Eq" (method eq 0))
  (class "builtin/Ord" (method lt 0) (method le 0) (method gt 0) (method ge 0))
  (class "builtin/Show" (method show 0))
  (global "builtin/Ref.new" builtin)
  (global "builtin/Ref.get" builtin)
  (global "builtin/Ref.set" builtin)
  (global "builtin/Array.length" builtin)
  (global "builtin/Array.get" builtin)
  (global "builtin/Array.each" builtin)
  (global "builtin/MutableArray.new" builtin)
  (global "builtin/MutableArray.length" builtin)
  (global "builtin/MutableArray.get" builtin)
  (global "builtin/MutableArray.set" builtin)
  (global "builtin/MutableArray.freeze" builtin)
  (global "builtin/pinned" builtin)
  (global "main/x" value i32)
  (fn "main/x" thunk yield (params) (locals) (dicts 0) (caps) (result i32) (lit i32 1))
  (init "builtin")
  (init "prelude")
  (init "main" (def_value "main/x" "main/x"))

以降のブロックは、組み込みの単位と表、空の prelude の単位を除いて示す。

  $ emit() { diktor --no-prelude --emit-ir-text "$1.kirt" "$1.kel" && grep -v '^(kir \|^(unit "builtin"\|^(unit "prelude"\|^(type "builtin/\|^(class "builtin/\|^(global "builtin/\|^(init "builtin")\|^(init "prelude")' "$1.kirt"; }

リテラル。`f64` はビット列で、文字列は 0x20 から 0x7E の外のバイトを `\xHH` で書く。
範囲外の数値リテラルは lit_error になり、評価したときに初めて実行時エラーになる。

  $ cat > lit.kel <<'EOF'
  > let a = true
  > let b: Int64 = 9223372036854775807
  > let c = -1.5
  > let d = "q\"\\\n日"
  > let k = 4294967295
  > EOF
  $ emit lit
  (unit "main" (paths "lit.kel"))
  (global "main/a" value bool)
  (global "main/b" value i64)
  (global "main/c" value f64)
  (global "main/d" value str)
  (global "main/k" value i32)
  (fn "main/a" thunk yield (params) (locals) (dicts 0) (caps) (result bool) (lit bool true))
  (fn "main/b" thunk yield (params) (locals) (dicts 0) (caps) (result i64) (lit i64 9223372036854775807))
  (fn "main/c" thunk yield (params) (locals) (dicts 0) (caps) (result f64) (lit f64 0xbff8000000000000))
  (fn "main/d" thunk yield (params) (locals) (dicts 0) (caps) (result str) (lit str "q\"\\\x0a\xe6\x97\xa5"))
  (fn "main/k" thunk yield (params) (locals) (dicts 0) (caps) (result i32) (lit_error lit_range "4294967295"))
  (init "main" (def_value "main/a" "main/a") (def_value "main/b" "main/b") (def_value "main/c" "main/c") (def_value "main/d" "main/d") (def_value "main/k" "main/k"))

クロージャと捕獲。捕獲の列は、外側の関数での読み方(dparam、env、local の順に番号の昇順)で並ぶ。
持ち上げた関数は、根の関数の記号に $ と場所の番号を付けて名指す。

  $ cat > clo.kel <<'EOF'
  > let adder(a: Int32, b: Int32): (Int32) => (Int32) => Int32 =
  >   fn(x) => fn(y) => a + x + y + b
  > EOF
  $ emit clo
  (unit "main" (paths "clo.kel"))
  (global "main/adder" fn "main/adder")
  (fn "main/adder" lambda yield
    (params i32 i32)
    (locals)
    (dicts 0)
    (caps)
    (result any)
    (closure "main/adder$0" (local 0) (local 1)))
  (fn "main/adder$0" lambda noyield
    (params i32)
    (locals)
    (dicts 0)
    (caps i32 i32)
    (result any)
    (closure "main/adder$1" (env 0) (env 1) (local 0)))
  (fn "main/adder$1" lambda noyield
    (params i32)
    (locals)
    (dicts 0)
    (caps i32 i32 i32)
    (result i32)
    (opcall "builtin/Add" add
      (dbuiltin "builtin/Add" "builtin/Int32")
      (opcall "builtin/Add" add
        (dbuiltin "builtin/Add" "builtin/Int32")
        (opcall "builtin/Add" add (dbuiltin "builtin/Add" "builtin/Int32") (env 0) (env 2))
        (local 0))
      (env 1)))
  (init "main" (def_fns "main/adder"))

束縛。仮引数のパターンは本体を letpat で包み、値の let のパターンも letpat になる。
let rec は letrec になり、群の名前のスロットを先に振る。
スロットは引数の後に、束縛する箇所がテキストに現れる順に振る。

  $ cat > bind.kel <<'EOF'
  > let f((a, b): (Int32, Int32), _: String, c: Int32): Int32 = {
  >   let (x, y) = (b, a)
  >   let rec even(n: Int32): Boolean = if n == 0 then true else odd(n - 1)
  >   and odd(n: Int32): Boolean = if n == 0 then false else even(n - 1)
  >   if even(c) then x else y
  > }
  > EOF
  $ emit bind
  (unit "main" (paths "bind.kel"))
  (global "main/f" fn "main/f")
  (fn "main/f" lambda yield
    (params any str i32)
    (locals i32 i32 i32 i32 any any)
    (dicts 0)
    (caps)
    (result i32)
    (letpat
      (record closed
        (field _item (bind 3))
        (field _item (bind 4)))
      (local 0)
      (letpat
        (record closed
          (field _item (bind 5))
          (field _item (bind 6)))
        (rec_extend _item
          (local 4)
          (rec_extend _item (local 3) (rec_empty)))
        (letrec
          (rec 7
            (closure "main/f$0" (local 8)))
          (rec 8
            (closure "main/f$1" (local 7)))
          (match
            (call ntail yield (local 7) (local 2))
            (clause (lit bool true) (local 5))
            (clause (lit bool false) (local 6)))))))
  (fn "main/f$0" lambda yield
    (params i32)
    (locals)
    (dicts 0)
    (caps any)
    (result bool)
    (match
      (opcall "builtin/Eq" eq (dbuiltin "builtin/Eq" "builtin/Int32") (local 0) (lit i32 0))
      (clause (lit bool true) (lit bool true))
      (clause
        (lit bool false)
        (call tail yield
          (env 0)
          (opcall "builtin/Sub" sub (dbuiltin "builtin/Sub" "builtin/Int32") (local 0) (lit i32 1))))))
  (fn "main/f$1" lambda yield
    (params i32)
    (locals)
    (dicts 0)
    (caps any)
    (result bool)
    (match
      (opcall "builtin/Eq" eq (dbuiltin "builtin/Eq" "builtin/Int32") (local 0) (lit i32 0))
      (clause (lit bool true) (lit bool false))
      (clause
        (lit bool false)
        (call tail yield
          (env 0)
          (opcall "builtin/Sub" sub (dbuiltin "builtin/Sub" "builtin/Int32") (local 0) (lit i32 1))))))
  (init "main" (def_fns "main/f"))

レコード。拡張は値を先に、更新は基底を先に書く(評価の順)。
タプルのパターンは closed、既定のレコードのパターンは open、...rest は rest である。

  $ cat > rec.kel <<'EOF'
  > let r = {x = 1, y = "s"}
  > let s = {x = true extends r}
  > let t = {s with y = "t"}
  > let u = (t \ x).x
  > let get(p) = p match {
  >   case {x, ...rest} => (x, rest.y)
  > }
  > let tup(q: (Int32, Int32)): Int32 = q match { case (m, n) => m + n }
  > EOF
  $ emit rec
  (unit "main" (paths "rec.kel"))
  (global "main/r" value any)
  (global "main/s" value any)
  (global "main/t" value any)
  (global "main/u" value i32)
  (global "main/get" fn "main/get")
  (global "main/tup" fn "main/tup")
  (fn "main/r" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result any)
    (rec_extend x
      (lit i32 1)
      (rec_extend y (lit str "s") (rec_empty))))
  (fn "main/s" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result any)
    (rec_extend x (lit bool true) (global "main/r")))
  (fn "main/t" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result any)
    (rec_update y (global "main/s") (lit str "t")))
  (fn "main/u" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (rec_select x
      (rec_restrict x (global "main/t"))))
  (fn "main/get" lambda yield
    (params any)
    (locals any any)
    (dicts 0)
    (caps)
    (result any)
    (match
      (local 0)
      (clause
        (record rest
          (field x (bind 1))
          (bind 2))
        (rec_extend _item
          (local 1)
          (rec_extend _item
            (rec_select y (local 2))
            (rec_empty))))))
  (fn "main/tup" lambda yield
    (params any)
    (locals i32 i32)
    (dicts 0)
    (caps)
    (result i32)
    (match
      (local 0)
      (clause
        (record closed
          (field _item (bind 1))
          (field _item (bind 2)))
        (opcall "builtin/Add" add (dbuiltin "builtin/Add" "builtin/Int32") (local 1) (local 2)))))
  (init "main" (def_value "main/r" "main/r") (def_value "main/s" "main/s") (def_value "main/t" "main/t") (def_value "main/u" "main/u") (def_fns "main/get") (def_fns "main/tup"))

辞書。前提を持つインスタンス、メソッド自身の辞書(both の B: Show)、辞書を受け取る関数の定義と値束縛、
構造的な Eq の辞書、!= の not、前置の - を含む。

  $ cat > dict.kel <<'EOF'
  > type class Pretty[A] {
  >   val pretty: (A) => String
  >   val both[B: Show]: (A, B) => String
  > }
  > newtype Box[A] = Box(A)
  > type instance[A: Show] Pretty[Box[_]] {
  >   let pretty(b) = b match { case Box(x) => show(x) }
  >   let both(b, y) = pretty(b) + show(y)
  > }
  > let twice[A: Pretty](x: A): String = pretty(x) + pretty(x)
  > let dbl = fn(x) => x + x
  > let nine = dbl(4.5)
  > let s = twice(Box(1))
  > let ne = (1, true) != (2, false)
  > let m = -(2.5)
  > EOF
  $ emit dict
  (unit "main" (paths "dict.kel"))
  (type "main/Box" (ctor Box 1))
  (class "main/Pretty" (method pretty 0) (method both 1))
  (instance "main/instance:Pretty[Box]" "main/Pretty" "main/Box" (premises 1) (method pretty 0 "main/instance:Pretty[Box].pretty") (method both 1 "main/instance:Pretty[Box].both"))
  (global "main/twice" dictabs "main/twice")
  (global "main/dbl" dictabs "main/dbl")
  (global "main/nine" value f64)
  (global "main/s" value str)
  (global "main/ne" value bool)
  (global "main/m" value f64)
  (fn "main/instance:Pretty[Box].pretty" dictabs yield
    (params)
    (locals)
    (dicts 1)
    (caps)
    (result any)
    (closure "main/instance:Pretty[Box].pretty$0" (dparam 0)))
  (fn "main/instance:Pretty[Box].pretty$0" lambda yield
    (params any)
    (locals any)
    (dicts 0)
    (caps any)
    (result str)
    (match
      (local 0)
      (clause
        (ctor "main/Box" Box
          (field 0 (bind 1)))
        (call tail yield
          (method "builtin/Show" show (env 0))
          (local 1)))))
  (fn "main/instance:Pretty[Box].both" dictabs yield
    (params)
    (locals)
    (dicts 2)
    (caps)
    (result any)
    (dictapp
      (dictabs "main/instance:Pretty[Box].both$0" (dparam 0))
      (dparam 1)))
  (fn "main/instance:Pretty[Box].both$0" dictabs yield
    (params)
    (locals)
    (dicts 1)
    (caps any)
    (result any)
    (closure "main/instance:Pretty[Box].both$1" (dparam 0) (env 0)))
  (fn "main/instance:Pretty[Box].both$1" lambda yield
    (params any any)
    (locals)
    (dicts 0)
    (caps any any)
    (result str)
    (opcall "builtin/Add" add
      (dbuiltin "builtin/Add" "builtin/String")
      (call ntail yield
        (method "main/Pretty" pretty
          (dinst "main/instance:Pretty[Box]" (env 1)))
        (local 0))
      (call ntail yield
        (method "builtin/Show" show (env 0))
        (local 1))))
  (fn "main/twice" dictabs yield
    (params)
    (locals)
    (dicts 1)
    (caps)
    (result any)
    (closure "main/twice$0" (dparam 0)))
  (fn "main/twice$0" lambda yield
    (params any)
    (locals)
    (dicts 0)
    (caps any)
    (result str)
    (opcall "builtin/Add" add
      (dbuiltin "builtin/Add" "builtin/String")
      (call ntail yield
        (method "main/Pretty" pretty (env 0))
        (local 0))
      (call ntail yield
        (method "main/Pretty" pretty (env 0))
        (local 0))))
  (fn "main/dbl" dictabs yield
    (params)
    (locals)
    (dicts 1)
    (caps)
    (result any)
    (closure "main/dbl$0" (dparam 0)))
  (fn "main/dbl$0" lambda yield
    (params any)
    (locals)
    (dicts 0)
    (caps any)
    (result any)
    (opcall "builtin/Add" add (env 0) (local 0) (local 0)))
  (fn "main/nine" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result f64)
    (call ntail noyield
      (dictapp (global "main/dbl") (dbuiltin "builtin/Add" "builtin/Float64"))
      (lit f64 0x4012000000000000)))
  (fn "main/s" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result str)
    (call ntail noyield
      (dictapp
        (global "main/twice")
        (dinst "main/instance:Pretty[Box]" (dbuiltin "builtin/Show" "builtin/Int32")))
      (construct "main/Box" Box
        (field 0 (lit i32 1)))))
  (fn "main/ne" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result bool)
    (not
      (opcall "builtin/Eq" eq
        (drecord
          (field _item (dbuiltin "builtin/Eq" "builtin/Int32"))
          (field _item (dbuiltin "builtin/Eq" "builtin/Boolean")))
        (rec_extend _item
          (lit i32 1)
          (rec_extend _item (lit bool true) (rec_empty)))
        (rec_extend _item
          (lit i32 2)
          (rec_extend _item (lit bool false) (rec_empty))))))
  (fn "main/m" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result f64)
    (opcall "builtin/Neg" neg (dbuiltin "builtin/Neg" "builtin/Float64") (lit f64 0x4004000000000000)))
  (init "main" (def_instance "main/instance:Pretty[Box]") (def_fns "main/twice") (def_dictabs "main/dbl") (def_value "main/nine" "main/nine") (def_value "main/s" "main/s") (def_value "main/ne" "main/ne") (def_value "main/m" "main/m"))

ハンドラ。返り値の型が Never の操作の節は N、背骨の外に resume の無い節は T、ほかは G である。
同じ操作の 2 つ目の節には #1 が付く。

  $ cat > hdl.kel <<'EOF'
  > effect St = { get: () => Int32, put: (Int32) => {}, quit: (Int32) => Never }
  > let st(init: Int32, body: () => Int32 @ {St}): Int32 = {
  >   let base = init
  >   body() handle {
  >     case get() => resume(base)
  >     case put(n) if n < 0 => { let r = resume(()); r + n }
  >     case put(n) => resume(())
  >     case quit(code) => code + base
  >     case return(v) => v
  >     case cancel => ()
  >   }
  > }
  > let prog(): Int32 = st(1, fn() => { perform put(perform get() + 1); perform quit(7) })
  > EOF
  $ emit hdl
  (unit "main" (paths "hdl.kel"))
  (effect "main/St" (op get 0 resume user) (op put 1 resume user) (op quit 1 never user))
  (global "main/st" fn "main/st")
  (global "main/prog" fn "main/prog")
  (fn "main/st" lambda yield
    (params i32 any)
    (locals i32)
    (dicts 0)
    (caps)
    (result i32)
    (let 2
      (local 0)
      (handle tail "main/St"
        (body "main/st$h0.body" (local 1))
        (op get T "main/st$h0.op.get" (local 2))
        (op put G "main/st$h0.op.put")
        (op put T "main/st$h0.op.put#1")
        (op quit N "main/st$h0.op.quit" (local 2))
        (return "main/st$h0.return")
        (cancel "main/st$h0.cancel"))))
  (fn "main/st$h0.body" handlebody yield
    (params)
    (locals)
    (dicts 0)
    (caps any)
    (result i32)
    (call ntail yield (env 0)))
  (fn "main/st$h0.op.get" opclause yield
    (params)
    (locals)
    (dicts 0)
    (caps i32)
    (result i32)
    (pats)
    (resume tail (env 0)))
  (fn "main/st$h0.op.put" opclause yield
    (params i32)
    (locals i32)
    (dicts 0)
    (caps)
    (result i32)
    (pats (wild))
    (guard
      (opcall "builtin/Ord" lt (dbuiltin "builtin/Ord" "builtin/Int32") (local 0) (lit i32 0)))
    (let 1
      (resume ntail (rec_empty))
      (opcall "builtin/Add" add (dbuiltin "builtin/Add" "builtin/Int32") (local 1) (local 0))))
  (fn "main/st$h0.op.put#1" opclause yield
    (params i32)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (pats (wild))
    (resume tail (rec_empty)))
  (fn "main/st$h0.op.quit" opclause yield
    (params i32)
    (locals)
    (dicts 0)
    (caps i32)
    (result i32)
    (pats (wild))
    (opcall "builtin/Add" add (dbuiltin "builtin/Add" "builtin/Int32") (local 0) (env 0)))
  (fn "main/st$h0.return" retclause yield (params i32) (locals) (dicts 0) (caps) (result i32) (local 0))
  (fn "main/st$h0.cancel" cancelclause yield (params) (locals) (dicts 0) (caps) (result any) (rec_empty))
  (fn "main/prog" lambda yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (call tail yield (global "main/st") (lit i32 1) (closure "main/prog$0")))
  (fn "main/prog$0" lambda yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (seq
      (perform "main/St" put
        (opcall "builtin/Add" add (dbuiltin "builtin/Add" "builtin/Int32") (perform "main/St" get) (lit i32 1)))
      (perform "main/St" quit (lit i32 7))))
  (init "main" (def_fns "main/st") (def_fns "main/prog"))

内側のハンドラ式の本体に書いた resume は、囲む操作節の継続を指し、末尾にならない。
その節は G になる。

  $ cat > inner.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > effect Log = { log: (Int32) => {} }
  > let f(body: () => Int32 @ {Ask}): Int32 @ {Log} =
  >   body() handle {
  >     case ask() => (resume(5)) handle { case log(n) => resume(()) }
  >   }
  > EOF
  $ emit inner
  (unit "main" (paths "inner.kel"))
  (effect "main/Ask" (op ask 0 resume user))
  (effect "main/Log" (op log 1 resume user))
  (global "main/f" fn "main/f")
  (fn "main/f" lambda yield
    (params any)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (handle tail "main/Ask"
      (body "main/f$h0.body" (local 0))
      (op ask G "main/f$h0.op.ask")))
  (fn "main/f$h0.body" handlebody yield
    (params)
    (locals)
    (dicts 0)
    (caps any)
    (result i32)
    (call ntail yield (env 0)))
  (fn "main/f$h0.op.ask" opclause yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (pats)
    (handle ntail "main/Log" (body "main/f$h1.body") (op log T "main/f$h1.op.log")))
  (fn "main/f$h1.body" handlebody yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (resume ntail (lit i32 5)))
  (fn "main/f$h1.op.log" opclause yield
    (params i32)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (pats (wild))
    (resume tail (rec_empty)))
  (init "main" (def_fns "main/f"))

トップレベルの手順。同じ名前の再束縛は #1 を付けた別の大域になる。
名前が変数でない値束縛は def_pattern、式文は run_exp で、関数の記号は $init と手順の番号である。
辞書を受け取る式文(show)は手順を作らず、番号も使わない。

  $ cat > top.kel <<'EOF'
  > newtype P = P(x: Int32, y: Int32)
  > let x = 1
  > let x = x + 1
  > let P(y = b, x = a) = P(10, 20)
  > let (_, c) = (a, b)
  > show
  > #Tag(x)
  > let _ = ???
  > EOF
  $ emit top
  (unit "main" (paths "top.kel"))
  (type "main/P" (ctor P 2))
  (global "main/x" value i32)
  (global "main/x#1" value i32)
  (global "main/a" value i32)
  (global "main/b" value i32)
  (global "main/c" value i32)
  (fn "main/x" thunk yield (params) (locals) (dicts 0) (caps) (result i32) (lit i32 1))
  (fn "main/x#1" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (opcall "builtin/Add" add (dbuiltin "builtin/Add" "builtin/Int32") (global "main/x") (lit i32 1)))
  (fn "main/$init2" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result any)
    (construct "main/P" P
      (field 0 (lit i32 10))
      (field 1 (lit i32 20))))
  (fn "main/$init3" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result any)
    (rec_extend _item
      (global "main/a")
      (rec_extend _item (global "main/b") (rec_empty))))
  (fn "main/$init4" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result any)
    (variant Tag (global "main/x#1")))
  (fn "main/$init5" thunk yield (params) (locals) (dicts 0) (caps) (result any) (hole))
  (init "main"
    (def_value "main/x" "main/x")
    (def_value "main/x#1" "main/x#1")
    (def_pattern "main/$init2"
      (globals "main/a" "main/b")
      (ctor "main/P" P
        (field 0 (bind 0))
        (field 1 (bind 1))))
    (def_pattern "main/$init3"
      (globals "main/c")
      (record closed
        (field _item (wild))
        (field _item (bind 0))))
    (run_exp "main/$init4")
    (def_pattern "main/$init5" (globals) (wild)))

extern、module の平坦化、module の中のインスタンス。
extern の大域は実装名(修飾しない元の名前)を持ち、def_fns で初期化する。

  $ cat > ext.kel <<'EOF'
  > extern "prim" let __int32_add(a: Int32, b: Int32): Int32
  > extern "C" let sin(x: Float64): Float64
  > module M {
  >   pub extern "prim" let __no_such(x: Int32): Int32
  >   pub newtype N = N(Int32)
  >   type instance Show[N] {
  >     let show(n) = n match { case N(k) => "N" }
  >   }
  > }
  > let v = M.__no_such(__int32_add(1, 2))
  > let w = show(M.N(1))
  > EOF
  $ emit ext
  (unit "main" (paths "ext.kel"))
  (type "main/M.N" (ctor N 1))
  (instance "main/instance:Show[M.N]" "builtin/Show" "main/M.N" (premises 0) (method show 0 "main/instance:Show[M.N].show"))
  (global "main/__int32_add" extern prim "__int32_add" 0)
  (global "main/sin" extern C "sin" 0)
  (global "main/M.__no_such" extern prim "__no_such" 0)
  (global "main/v" value i32)
  (global "main/w" value str)
  (fn "main/instance:Show[M.N].show" dictabs yield (params) (locals) (dicts 0) (caps) (result any) (closure "main/instance:Show[M.N].show$0"))
  (fn "main/instance:Show[M.N].show$0" lambda yield
    (params any)
    (locals i32)
    (dicts 0)
    (caps)
    (result str)
    (match
      (local 0)
      (clause
        (ctor "main/M.N" N
          (field 0 (bind 1)))
        (lit str "N"))))
  (fn "main/v" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (call ntail noyield
      (global "main/M.__no_such")
      (call ntail noyield (global "main/__int32_add") (lit i32 1) (lit i32 2))))
  (fn "main/w" thunk yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result str)
    (call ntail noyield
      (method "builtin/Show" show (dinst "main/instance:Show[M.N]"))
      (construct "main/M.N" N
        (field 0 (lit i32 1)))))
  (init "main" (def_fns "main/__int32_add") (def_fns "main/sin") (def_fns "main/M.__no_such") (def_instance "main/instance:Show[M.N]") (def_value "main/v" "main/v") (def_value "main/w" "main/w"))

import した単位の鍵は、import を書いたファイルの鍵のディレクトリからの相対パスで、.kel を残す。
検索パスで見つけた単位は @i/ で始まる。
鍵は作業ディレクトリによらず、paths(診断のための綴り)だけが変わる。

  $ mkdir -p a/lib vendor/u
  $ printf 'from "./lib/x" import x_v\nfrom "u/util" import util_v\nlet main_v = x_v + util_v\n' > a/m.kel
  $ printf 'from "../y" import y_v\npub newtype T = T(Int32)\npub let x_v: Int32 = y_v + 1\n' > a/lib/x.kel
  $ printf 'pub let y_v: Int32 = 41\n' > a/y.kel
  $ printf 'pub let util_v: Int32 = 2\n' > vendor/u/util.kel
  $ diktor --no-prelude --import-path vendor --emit-ir-text m1.kirt a/m.kel
  $ grep '^(unit\|^(type "[^b]\|^(global "[^b]\|^(init "[^bp]' m1.kirt
  (unit "builtin" (paths))
  (unit "prelude" (paths))
  (unit "y.kel" (paths "a/y.kel"))
  (unit "lib/x.kel" (paths "a/lib/x.kel"))
  (unit "@1/u/util.kel" (paths "vendor/u/util.kel"))
  (unit "main" (paths "a/m.kel"))
  (type "lib/x.kel/T" (ctor T 1))
  (global "y.kel/y_v" value i32)
  (global "lib/x.kel/x_v" value i32)
  (global "@1/u/util.kel/util_v" value i32)
  (global "main/main_v" value i32)
  (init "y.kel" (def_value "y.kel/y_v" "y.kel/y_v"))
  (init "lib/x.kel" (def_value "lib/x.kel/x_v" "lib/x.kel/x_v"))
  (init "@1/u/util.kel" (def_value "@1/u/util.kel/util_v" "@1/u/util.kel/util_v"))
  (init "main" (def_value "main/main_v" "main/main_v"))
  $ (cd a && diktor --no-prelude --import-path ../vendor --emit-ir-text ../m2.kirt m.kel)
  $ diff m1.kirt m2.kirt
  4,7c4,7
  < (unit "y.kel" (paths "a/y.kel"))
  < (unit "lib/x.kel" (paths "a/lib/x.kel"))
  < (unit "@1/u/util.kel" (paths "vendor/u/util.kel"))
  < (unit "main" (paths "a/m.kel"))
  ---
  > (unit "y.kel" (paths "y.kel"))
  > (unit "lib/x.kel" (paths "lib/x.kel"))
  > (unit "@1/u/util.kel" (paths "../vendor/u/util.kel"))
  > (unit "main" (paths "m.kel"))
  [1]

起点のファイルが基準のディレクトリ(最初のファイルのディレクトリ)の外にあれば、
その起点のディレクトリは基準からの相対パス(.. を含む)になる。
同じ名前の兄弟を import する 2 つの起点は、別の鍵を持つ。
絶対パスで書いても鍵は変わらない。

  $ mkdir -p k1/a
  $ printf 'let w: Int32 = 1\npub let q: Int32 = w\n' > k1/a/w.kel
  $ printf 'let w: Int32 = 20\npub let r: Int32 = w\n' > k1/w.kel
  $ printf 'from "./w" import q\nlet m = q\n' > k1/a/m.kel
  $ printf 'from "./w" import r\nlet c = r\n' > k1/c.kel
  $ diktor --no-prelude --emit-ir-text k1.kirt k1/a/m.kel k1/c.kel
  $ grep '^(unit "[^bp]\|^(global "[^b]' k1.kirt
  (unit "w.kel" (paths "k1/a/w.kel"))
  (unit "../w.kel" (paths "k1/w.kel"))
  (unit "main" (paths "k1/a/m.kel" "k1/c.kel"))
  (global "w.kel/w" value i32)
  (global "w.kel/q" value i32)
  (global "../w.kel/w" value i32)
  (global "../w.kel/r" value i32)
  (global "main/m" value i32)
  (global "main/c" value i32)
  $ diktor --no-prelude --emit-ir-text k1abs.kirt "$PWD/k1/a/m.kel" "$PWD/k1/c.kel"
  $ grep '^(unit "[^bpm]' k1abs.kirt | sed 's/ (paths.*//'
  (unit "w.kel"
  (unit "../w.kel"

綴りの規則で、別のファイルが同じ鍵になることがある。
シンボリックリンクの下の .. は、綴りの相殺と OS の解決で行き先が違う。
鍵が重なると、書き出さずに 64 で終える。

  $ mkdir -p k2/proj k2/elsewhere/dir
  $ ln -s ../elsewhere/dir k2/proj/sub
  $ printf 'pub let q: Int32 = 1\n' > k2/proj/x.kel
  $ printf 'pub let q2: Int32 = 2\n' > k2/elsewhere/x.kel
  $ printf 'from "../x" import q2\npub let y: Int32 = q2\n' > k2/elsewhere/dir/y.kel
  $ printf 'from "./x" import q\nfrom "./sub/y" import y\nlet m = q + y\n' > k2/proj/main.kel
  $ diktor --no-prelude --emit-ir-text k2.kirt k2/proj/main.kel; echo "exit: $?"; test -e k2.kirt || echo "no file"
  diktor: KIR の単位の鍵が重なります: x.kel(k2/proj/x.kel と k2/proj/sub/../x.kel)
  exit: 64
  no file

`runtime` の印は、プレリュードの Console の write にだけ付ける。
`--no-prelude` で起点が宣言した Console は、利用者のハンドラが処理するので `user` である。

  $ cat > con.kel <<'EOF'
  > effect Console = { write: (String) => {} }
  > let r = (perform write("x\n")) handle { case write(s) => resume() }
  > EOF
  $ diktor --no-prelude con.kel
  $ emit con | grep '^(effect'
  (effect "main/Console" (op write 1 resume user))

辞書の引数の順は、型の行をラベルの綴りの昇順にたどり、1 つの型変数の制約をクラスの表の順に並べて決める。
読む順や注釈に書いた順を変えても、使う側の辞書の列は変わらない。
構造的な Eq の辞書の項目も、ラベルの昇順に並ぶ。

  $ cat > dord.kel <<'EOF'
  > let f(r) = show(r.b) + show(r.a)
  > let g(r) = show(r.a) + show(r.b)
  > let p[A: Show + Eq](x: A): Boolean = x == x
  > let q[A: Eq + Show](x: A): Boolean = x == x
  > let v = f({a = 1, b = true}) + g({a = 1, b = true})
  > let u = p(1) && q(1)
  > let w1 = {k = 1, v = true} == {v = true, k = 1}
  > let w2 = {v = true, k = 1} == {k = 1, v = true}
  > EOF
  $ diktor --emit-ir-text dord.kirt dord.kel
  $ grep -o '(dictapp (global "main/[fgpq]").*' dord.kirt
  (dictapp (global "main/f") (dbuiltin "builtin/Show" "builtin/Int32") (dbuiltin "builtin/Show" "builtin/Boolean"))
  (dictapp (global "main/g") (dbuiltin "builtin/Show" "builtin/Int32") (dbuiltin "builtin/Show" "builtin/Boolean"))
  (dictapp (global "main/p") (dbuiltin "builtin/Eq" "builtin/Int32") (dbuiltin "builtin/Show" "builtin/Int32"))
  (dictapp (global "main/q") (dbuiltin "builtin/Eq" "builtin/Int32") (dbuiltin "builtin/Show" "builtin/Int32"))
  $ grep -A2 '(drecord' dord.kirt
      (drecord
        (field k (dbuiltin "builtin/Eq" "builtin/Int32"))
        (field v (dbuiltin "builtin/Eq" "builtin/Boolean")))
  --
      (drecord
        (field k (dbuiltin "builtin/Eq" "builtin/Int32"))
        (field v (dbuiltin "builtin/Eq" "builtin/Boolean")))

初期化の前の大域を読んだときの実行時エラーは、module の修飾を含む名前を書く。
KIR の大域の記号の修飾名と同じ名前である。

  $ cat > fwd.kel <<'EOF'
  > module M {
  >   pub let g(): Int32 = h()
  >   pub let z: Int32 = g()
  >   pub let h(): Int32 = 3
  > }
  > echoln(show(M.z))
  > EOF
  $ diktor fwd.kel; echo "exit: $?"
  実行時エラー: 未束縛の変数: M.h
  exit: 3
  $ diktor --emit-ir-text fwd.kirt fwd.kel && grep -o '(global "main/M.h")' fwd.kirt
  (global "main/M.h")

インスタンスの宣言は、辞書を受け取らない実装をメソッドの順に評価し終えてから、インスタンスを使える状態にする。
評価の間にそのインスタンスからメソッドを選ぶと、実行時エラーになる。
KIR では、この宣言は 1 つの def_instance の手順である。

  $ cat > inst0.kel <<'EOF'
  > type class Sz[A] { val sz: (A) => Int32; val k: (A) => Int32 }
  > newtype B(Int32)
  > type instance Sz[B] {
  >   let sz(b) = 1
  >   let k = { let n = sz(B(1)); fn(b) => n }
  > }
  > echoln(show(k(B(2))))
  > EOF
  $ diktor inst0.kel; echo "exit: $?"
  実行時エラー: Sz[B] のインスタンスは宣言より前の位置では使えません(実行はまだ実体を持ちません。インスタンス宣言を使用より前に置いてください)
  exit: 3
  $ diktor --emit-ir-text inst0.kirt inst0.kel && grep '^(init "main"' inst0.kirt
  (init "main" (def_instance "main/instance:Sz[B]") (run_exp "main/$init1"))

書き出しは決定的で、同じ入力から同じバイト列を出す。

  $ diktor --emit-ir-text s1.kirt sample/stubs.kel sample/sample.kel
  $ diktor --emit-ir-text s2.kirt sample/stubs.kel sample/sample.kel
  $ cmp s1.kirt s2.kirt && echo same
  same

レコードの構造的な Eq は、ラベルの順に項目を比べ、偽の項目で止まる。
r ではフィールド a が等しくないので、Y の利用者のインスタンスを呼ばない。
r2 ではフィールド a が等しいので、Y のインスタンスを呼んで実行時エラーになる。

  $ cat > req.kel <<'EOF'
  > newtype Y = Y(Int32)
  > type instance Eq[Y] { let eq(a, b) = ??? }
  > let r = {a = 1, b = Y(1)} == {a = 2, b = Y(1)}
  > echoln(show(r))
  > let r2 = {a = 1, b = Y(1)} == {a = 1, b = Y(1)}
  > EOF
  $ diktor req.kel; echo "exit: $?"
  false
  実行時エラー: ??? に到達しました
  exit: 3
  $ diktor --emit-ir-text req.kirt req.kel && grep -A 3 '^  (opcall "builtin/Eq" eq$' req.kirt | head -4
    (opcall "builtin/Eq" eq
      (drecord
        (field a (dbuiltin "builtin/Eq" "builtin/Int32"))
        (field b (dinst "main/instance:Eq[Y]")))

操作節の本体の中の match のガードには resume を書ける。
その resume は末尾でないので ntail であり、節は G になる。

  $ cat > grd.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let f(body: () => Int32 @ {Ask}): Int32 = body() handle {
  >   case ask() => 1 match { case _ if resume(1) == 2 => 3
  >                           case _ => 4 }
  > }
  > echoln(show(f(fn() => perform ask() + 1)))
  > EOF
  $ diktor grd.kel; echo "exit: $?"
  3
  exit: 0
  $ diktor --emit-ir-text grd.kirt grd.kel && grep -o '(op ask [NTG]' grd.kirt && awk '/^\(fn "main\/f\$h0.op.ask"/{p=1;print;next} /^\(/{p=0} p' grd.kirt
  (op ask G
  (fn "main/f$h0.op.ask" opclause yield
    (params)
    (locals)
    (dicts 0)
    (caps)
    (result i32)
    (pats)
    (match
      (lit i32 1)
      (clause
        (wild)
        (guard
          (opcall "builtin/Eq" eq
            (dbuiltin "builtin/Eq" "builtin/Int32")
            (resume ntail (lit i32 1))
            (lit i32 2)))
        (lit i32 3))
      (clause (wild) (lit i32 4))))

メソッド自身の辞書は、メソッドのスキーマの正準順に o に置く。
[B: Show + Eq] の o は Eq、Show の順である。

  $ cat > mo.kel <<'EOF'
  > type class Pr[A] { val pr[B: Show + Eq]: (A, B) => String }
  > newtype W = W(Int32)
  > type instance Pr[W] { let pr(w, b) = if b == b then show(b) else "" }
  > let z = pr(W(1), true)
  > let y[C: Pr](c: C): String = pr(c, 1)
  > EOF
  $ emit mo | grep -o '(method "main/Pr" pr .*'
  (method "main/Pr" pr (dinst "main/instance:Pr[W]") (dbuiltin "builtin/Eq" "builtin/Boolean") (dbuiltin "builtin/Show" "builtin/Boolean"))
  (method "main/Pr" pr (env 0) (dbuiltin "builtin/Eq" "builtin/Int32") (dbuiltin "builtin/Show" "builtin/Int32"))
