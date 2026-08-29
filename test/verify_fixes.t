敵対的検証(260829-2b)で見つけた欠陥の回帰テスト。
これらが再発すると健全性・頑健性が壊れる。詳細は doc/log/260829-2-impl.md。

行変数 [R] が行位置で使える(sample.kel:136-138 / :144-150):

  $ cat > rowvar.kel <<'EOF'
  > let fst2[A, R](t: {_item: A extends R}): A = t._item
  > echoln(fst2({_item = "hi", x = 1}))
  > echoln(fst2({x = 1, _item = "hi"}))
  > let describe[R](v: #Even | #Odd | R): String = v match {
  >   case #Even => "even"
  >   case #Odd  => "odd"
  >   case _     => "unknown"
  > }
  > echoln(describe(#Even))
  > echoln(describe(#Other))
  > EOF
  $ diktor rowvar.kel
  hi
  hi
  even
  unknown

注釈付き非値は値制限で一般化されない(run のリージョンから漏れない):

  $ cat > vr.kel <<'EOF'
  > let escaped[E](): (Int32) => Int32 @ {Console extends E} = run h {
  >   let slot: Ref[h, (Int32) => Int32] = Ref.new(fn(x) => x)
  >   let cell = Ref.new(41)
  >   let _ = Ref.set(slot, fn(x) => Ref.get(cell) + x)
  >   Ref.get(slot)
  > }
  > EOF
  $ diktor --type-check vr.kel
  ! 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

型クラスディスパッチはクラスパラメータ位置で選ぶ(第1引数の別の型に釣られない):

  $ cat > pick.kel <<'EOF'
  > type class Pick[A] { val pick: (Int32, A) => Int32 }
  > type instance Pick[Int32]  { let pick(n, a) = a }
  > type instance Pick[String] { let pick(n, a) = n }
  > echoln(show(pick(0, "boom")))
  > EOF
  $ diktor pick.kel
  0

組み込みインスタンスは実行時に差し替わらない(コヒーレンス):

  $ cat > coh.kel <<'EOF'
  > type instance Add[Int32] { let add(x, y) = __int32_sub(x, y) }
  > echoln(show(2 + 3))
  > EOF
  $ diktor coh.kel
  5

module 内の type instance が実行時に見つかる(sample.kel §13 の形):

  $ cat > modinst.kel <<'EOF'
  > module BigInt {
  >   newtype BigInt = Small(Int32)
  >   type instance Add[BigInt] { let add(x, y) = x }
  > }
  > let a = Small(1)
  > echoln(show((a + a) match { case Small(n) => n }))
  > EOF
  $ diktor modinst.kel
  1

組み込み型名の newtype 再宣言を拒否:

  $ printf 'newtype Boolean = Yes\n' > redef.kel
  $ diktor --type-check redef.kel
  ! 型エラー: 組み込み型 Boolean は newtype で再宣言できません
  [1]

extern の再宣言を拒否:

  $ printf 'extern "prim" let __int32_add(x: String, y: String): String\n' > exr.kel
  $ diktor --type-check exr.kel
  ! 型エラー: プレリュードの extern __int32_add は再宣言できません
  [1]

let rec の非関数右辺を型検査で拒否:

  $ cat > lrn.kel <<'EOF'
  > let f(): Int32 = run h {
  >   let rec r = Ref.new(0)
  >   Ref.get(r)
  > }
  > EOF
  $ diktor --type-check lrn.kel
  ! 型エラー: let rec の右辺は関数でなければなりません
  [1]

頑健性: OCaml 例外を素通しせず終了コード規約に落とす:

  $ diktor /no/such/file.kel
  diktor: ファイルを開けません: /no/such/file.kel: No such file or directory
  [64]

  $ printf 'let x = 1\n// \xff\xfe\n' > badutf8.kel
  $ diktor badutf8.kel
  字句エラー: 不正な UTF-8 バイト列です
  [2]

  $ printf 'echoln(show(1i999999999999999999999))\n' > hugesuf.kel
  $ diktor hugesuf.kel
  ! 型エラー: 数値接尾辞 1i9999 は v0 では未対応です(i32/i64/f64 を使ってください)
  [1]

  $ printf 'module A { module B { let x = 1 } }\n' > nestmod.kel
  $ diktor nestmod.kel
  ! 型エラー: module の入れ子は未対応です(M10)
  [1]

  $ cat > unkeff.kel <<'EOF'
  > effect A = { op1: () => Int32 }
  > let r = (fn() => perform op1())() handle {
  >   case Nope.op1() => resume(1)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF
  $ diktor unkeff.kel
  ! 型エラー: 未知のエフェクト: Nope
  [1]

Float64 は最短往復可能表現で表示する:

  $ cat > fl.kel <<'EOF'
  > echoln(show(0.1 + 0.2))
  > echoln(show(123456789012345.0))
  > echoln(show(1.0))
  > EOF
  $ diktor fl.kel
  0.30000000000000004
  123456789012345.0
  1.0

入れ子 run で外側リージョンの Ref は読めない(MiniLang §16-7 と同じリージョン安全性):

  $ cat > nestrun.kel <<'EOF'
  > let f(): Int32 = run h1 {
  >   let r = Ref.new(1)
  >   let x = run h2 { let s = Ref.new(2); Ref.get(r) + Ref.get(s) }
  >   x
  > }
  > EOF
  $ diktor --type-check nestrun.kel
  ! 型エラー: スコープ付きの型が一致しません: ς1 と ς2
  [1]

ブロックの Seq は文のノードを借りない(260829-3 課題 7)。借りていた頃は
末尾から2番目の文の型が Seq の型で上書きされ、数値リテラルの値化
(第14章 number_value)が壊れて実行時に落ちた:

  $ cat > seq1.kel <<'KEL'
  > let f() = { 1; "x" }
  > echoln(f())
  > KEL
  $ diktor seq1.kel
  x

  $ cat > seq2.kel <<'KEL'
  > let g() = { "a"; 1; "b" }
  > echoln(g())
  > KEL
  $ diktor seq2.kel
  b

  $ cat > seq3.kel <<'KEL'
  > let h() = { 1; () }
  > let _ = h()
  > KEL
  $ diktor seq3.kel; echo "exit: $?"
  exit: 0

return / cancel 節にガードは書けない(型検査を通ったガードが実行時に
黙って無視されていた):

  $ cat > retguard.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() => resume(1)
  >   case return(x) if x > 100 => 999
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check retguard.kel
  ! 型エラー: return 節にガードは書けません
  [1]

  $ cat > cancelguard.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() => resume(1)
  >   case return(x) => x
  >   case cancel if false => ()
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check cancelguard.kel
  ! 型エラー: cancel 節にガードは書けません
  [1]
