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
  ! vr.kel:1:60: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
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
  ! redef.kel:1:1: 型エラー: 組み込み型 Boolean は newtype で再宣言できません
  [1]

extern の再宣言を拒否:

  $ printf 'extern "prim" let __int32_add(x: String, y: String): String\n' > exr.kel
  $ diktor --type-check exr.kel
  ! exr.kel:1:1: 型エラー: プレリュードの extern __int32_add は再宣言できません
  [1]

かつてプレリュードに宣言が無かった名前も、いまは登録簿に載っていて
再宣言できない(C4。宣言漏れの名前は嘘の型で実装に到達できた):

  $ printf 'extern "prim" let __string_le(x: Int32, y: Int32): Int32\n' > exr2.kel
  $ diktor --type-check exr2.kel
  ! exr2.kel:1:1: 型エラー: プレリュードの extern __string_le は再宣言できません
  [1]

  $ printf 'extern "prim" let __int64_ge(x: Int64, y: Int64): Int32\n' > exr3.kel
  $ diktor --type-check exr3.kel
  ! exr3.kel:1:1: 型エラー: プレリュードの extern __int64_ge は再宣言できません
  [1]

ABI が実装バインドに効く(C リンケージから __* の実装には届かない。逆も):

  $ cat > abi.kel <<'KEL'
  > extern "C" let __nosuch_prim_name(x: Int32): Int32
  > echoln(show(__nosuch_prim_name(1)))
  > KEL
  $ diktor abi.kel
  実行時エラー: 未実装のプリミティブ: __nosuch_prim_name
  [3]

  $ cat > abi2.kel <<'KEL'
  > extern "prim" let cos(x: Float64): Float64
  > echoln(show(cos(0.0)))
  > KEL
  $ diktor abi2.kel
  実行時エラー: 未実装のプリミティブ: cos
  [3]

ABI 文字列そのものも検査する:

  $ printf 'extern "wat" let foo(x: Int32): Int32\n' > abi3.kel
  $ diktor --type-check abi3.kel
  ! abi3.kel:1:1: 型エラー: 未知の extern リンケージ: wat(prim か C を指定してください)
  [1]

追加した 10 本が正しい型で呼べること(プレリュード一覧の完備性の回帰):

  $ cat > prims.kel <<'KEL'
  > echoln(show(__string_le("a","b")) + show(__string_gt("a","b")) + show(__string_ge("a","a")))
  > echoln(show(__int64_le(1i64,2i64)) + show(__int64_gt(1i64,2i64)) + show(__int64_ge(2i64,2i64)))
  > echoln(show(__float64_le(1.0,2.0)) + show(__float64_gt(1.0,2.0)) + show(__float64_ge(2.0,2.0)))
  > echoln(__show_int32(42))
  > KEL
  $ diktor prims.kel
  truefalsetrue
  truefalsetrue
  truefalsetrue
  42

let rec の非関数右辺を型検査で拒否:

  $ cat > lrn.kel <<'EOF'
  > let f(): Int32 = run h {
  >   let rec r = Ref.new(0)
  >   Ref.get(r)
  > }
  > EOF
  $ diktor --type-check lrn.kel
  ! lrn.kel:2:3: 型エラー: let rec の右辺は関数でなければなりません
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
  ! 未実装: 数値接尾辞 1i999999999999999999999(v0 は i32/i64/f64 のみ)
  [4]

  $ printf 'module A { module B { let x = 1 } }\n' > nestmod.kel
  $ diktor nestmod.kel
  ! 未実装: module の入れ子(M10)
  [4]

  $ cat > unkeff.kel <<'EOF'
  > effect A = { op1: () => Int32 }
  > let r = (fn() => perform op1())() handle {
  >   case Nope.op1() => resume(1)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > EOF
  $ diktor unkeff.kel
  ! unkeff.kel:2:9: 型エラー: 未知のエフェクト: Nope
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
  ! nestrun.kel:3:48: 型エラー: スコープ付きの型が一致しません: ς1 と ς2
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
  ! retguard.kel:2:9: 型エラー: return 節にガードは書けません
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
  ! cancelguard.kel:2:9: 型エラー: cancel 節にガードは書けません
  [1]

同名メソッドを持つ型クラスの重複宣言を拒否(非修飾名の勝者が elab
(宣言順)と interp(ハッシュ順)で食い違い、誤った実体を呼ぶ /
偽の「見つかりません」を出していた):

  $ cat > mclash.kel <<'KEL'
  > type class Alpha[A] { val sz: (A) => Int32 }
  > type class Beta[A]  { val sz: (A) => Int32 }
  > KEL
  $ diktor --type-check mclash.kel
  ! mclash.kel:2:1: 型エラー: メソッド名 sz は型クラス Alpha が既に宣言しています(非修飾名が衝突するため、v0 では同名メソッドを複数のクラスに宣言できません)
  [1]

組み込みクラスのメソッド名も同じ扱い:

  $ printf 'type class MyShow[A] { val show: (A) => String }\n' > mclash2.kel
  $ diktor --type-check mclash2.kel
  ! mclash2.kel:1:1: 型エラー: メソッド名 show は型クラス Show が既に宣言しています(非修飾名が衝突するため、v0 では同名メソッドを複数のクラスに宣言できません)
  [1]

組み込みと同名のクラス再宣言は従来どおり受理(照合の上で組み込みを使う):

  $ printf 'type class Add[A] { val add: (A, A) => A }\necholn(show(2 + 3))\n' > readd.kel
  $ diktor readd.kel
  5

操作節のガードでは resume が使えない(interp はガードを resume 無しで
評価する。かつては型検査を通って実行時に落ちた):

  $ cat > gresume.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() if resume(7) > 0 => resume(1)
  >   case ask() => resume(2)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check gresume.kel
  ! gresume.kel:3:17: 型エラー: resume は操作節の中でのみ使えます
  [1]

クロージャに包んでも同じ(§11.21 の迂回にならない):

  $ cat > gresume2.kel <<'KEL'
  > effect Ask = { ask: () => Int32 }
  > let r = (perform ask() + 1) handle {
  >   case ask() if (fn(u: Unit) => resume(7))(()) > 0 => resume(1)
  >   case ask() => resume(2)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check gresume2.kel
  ! gresume2.kel:3:33: 型エラー: resume は操作節の中でのみ使えます
  [1]

組み込みキーへのユーザ instance の「受理するが採用しない」は 1 回まで。
2 回目はコヒーレンス違反(「同じキーを 2 度登録したらエラー」を組み込み
キーでも守る):

  $ cat > dupinst.kel <<'KEL'
  > type instance Add[Int32] { let add(x, y) = x }
  > type instance Add[Int32] { let add(x, y) = y }
  > KEL
  $ diktor --type-check dupinst.kel
  ! dupinst.kel:2:1: 型エラー: インスタンス Add[Int32] が二重に宣言されています(コヒーレンス違反)
  [1]

既定の節が無い操作節は型検査で拒否(B2 / D29。v0 には後送りの意味論が
無いので、全節が外れうる形を通さない):

  $ cat > guardonly.kel <<'KEL'
  > effect Ask = { ask: (Int32) => Int32 }
  > let r = (perform ask(1) + perform ask(2)) handle {
  >   case ask(n) if n == 1 => resume(100)
  >   case return(x) => x
  > }
  > echoln(show(r))
  > KEL
  $ diktor --type-check guardonly.kel
  ! guardonly.kel:2:9: 型エラー: 操作 ask の節が取りこぼします(ガードや絞り込みパターンだけの節は v0 では後送りできません)。変数パターンでガードの無い case ask(...) を最後に置いてください
  [1]

標準出力に書き出せないときも終了コード規約に落ちる(B5 / D33。既定の
flush は Format の at_exit で受け皿の外を走り、素通りして Fatal error +
2 に化けていた):

  $ printf 'echoln("hello")\n' > outerr.kel
  $ diktor outerr.kel > /dev/full
  diktor: 標準出力に書き出せません: No space left on device
  [74]

  $ diktor --type-check outerr.kel > /dev/full
  diktor: 標準出力に書き出せません: No space left on device
  [74]

return / cancel は操作名として予約(D68。handle の節分類が名前で横取り
するため、宣言できてもハンドルできない effect になっていた):

  $ printf 'effect E = { cancel: () => Int32 }\n' > opres.kel
  $ diktor --type-check opres.kel
  ! opres.kel:1:1: 型エラー: 操作名 cancel は予約されています(handle の cancel 節と衝突するため宣言できません)
  [1]

  $ printf 'effect E2 = { return: () => Int32 }\n' > opres2.kel
  $ diktor --type-check opres2.kel
  ! opres2.kel:1:1: 型エラー: 操作名 return は予約されています(handle の return 節と衝突するため宣言できません)
  [1]

終了は必ず safe_exit を通る(260829-5 M13 検証修正。exit の at_exit が
書けない出力で落ち、どの終了コードも Fatal error + 2 に化けていた):

  $ printf 'echoln("hello")\necholn(show(1 / 0))\n' > m74.kel
  $ diktor m74.kel > /dev/full
  実行時エラー: ゼロ除算です
  [3]

  $ diktor m74.kel >/dev/null 2>/dev/full
  [3]

入力の読み取りエラーも 64(with_input は open だけでなく読み取りまで包む。
ディレクトリを渡すと EISDIR は読み取りで出る):

  $ mkdir -p adir
  $ diktor adir
  diktor: ファイルを開けません: Is a directory
  [64]

SIGPIPE は無視して出力エラー 74 に落とす(D33。既定のままだとシグナル死
141 で終了コード規約の外に出る):

  $ cat > big74.kel <<'KEL'
  > let rec loop(n: Int32): Unit =
  >   (n == 0) match {
  >     case true => ()
  >     case false => { echoln("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"); loop(n - 1) }
  >   }
  > loop(100000)
  > KEL
  $ bash -c 'diktor big74.kel | head -c 100 >/dev/null; echo "code: ${PIPESTATUS[0]}"' 2>&1 | tail -1
  code: 74

操作名は英小文字始まりに限る(節の分類器が読めない名前の effect は
ハンドルできない):

  $ printf 'effect E3 = { _foo: (Int32) => Int32 }\n' > opus.kel
  $ diktor --type-check opus.kel
  ! opus.kel:1:1: 型エラー: 操作名 _foo は英小文字で始めてください(handle の節が操作名として読めません)
  [1]

Run モードの診断は stderr(D54。stdout はプログラム出力専用):

  $ printf 'let bad = 1 + true\n' > terr.kel
  $ diktor terr.kel 2>/dev/null; echo "exit: $?"
  exit: 1

--strict-exhaustive が数えるのは表示した警告だけ(E11。プレリュードの
見えない警告で無言の exit 1 になっていた):

  $ cat > wpre.kel <<'KEL'
  > newtype Opt3[A] = None3 | Some3(A)
  > let pf = fn(o) => o match { case Some3(x) => x }
  > KEL
  $ printf 'let x = 1\n' > wu.kel
  $ diktor --type-check --strict-exhaustive --prelude wpre.kel wu.kel; echo "exit: $?"
  x : Int32
  exit: 0
