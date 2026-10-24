--emit-ir FILE は、型検査を通したプログラムを、実行せずに KIR のバイナリ(IRSpec 13 節)で FILE に書く。
--run-ir FILE は、型検査をせずに FILE を読み、検証してから KIR の評価器で実行する。
--via-ir は、同じことを 1 つのプロセスの中で、ファイルを介さずに行う。
どの経路でも、標準出力、標準エラー、終了状態は木の評価器と同じになる。
木の評価器と比べるコマンドは、DIKTOR_VIA_IR=0 を付けて木の評価器で走らせる。

  $ cat > prog.kel <<'EOF'
  > newtype Shape = Circle(Float64) | Rect(Float64, Float64)
  > let area(s: Shape): Float64 = s match {
  >   case Circle(r) => 3.0 * r * r
  >   case Rect(w, h) => w * h
  > }
  > newtype L[A] = N | C(A, L[A])
  > let rec sum[A: Add](xs: L[A], z: A): A = xs match {
  >   case N => z
  >   case C(x, rest) => x + sum(rest, z)
  > }
  > let adder(n: Int32): (Int32) => Int32 = fn(x) => x + n
  > let p = {x = 1, y = "two"}
  > echoln(show(area(Circle(2.0))) + " " + show(area(Rect(2.0, 3.5))))
  > echoln(show(sum(C(1, C(2, C(3, N))), 0)))
  > echoln(sum(C("a", C("b", N)), "!"))
  > echoln(show(adder(10)(5)) + p.y)
  > extern "C" let sqrt(x: Float64): Float64
  > echoln(show(sqrt(2.0)))
  > EOF
  $ DIKTOR_VIA_IR=0 diktor prog.kel; echo "exit: $?"
  12.0 7.0
  6
  ab!
  15two
  1.4142135623730951
  exit: 0
  $ diktor --emit-ir prog.kir prog.kel; echo "exit: $?"
  exit: 0
  $ diktor --run-ir prog.kir; echo "exit: $?"
  12.0 7.0
  6
  ab!
  15two
  1.4142135623730951
  exit: 0
  $ diktor --via-ir prog.kel; echo "exit: $?"
  12.0 7.0
  6
  ab!
  15two
  1.4142135623730951
  exit: 0

実行時エラーは、それまでの出力の後に同じ文面を標準エラーに書き、3 で終わる。
型検査の警告は --emit-ir のときに出し、--run-ir は型検査をしないので出さない。

  $ cat > err.kel <<'EOF'
  > newtype T = A | B
  > let f(t: T): Int32 = t match { case A => 1 }
  > let d(x: Int32): Int32 = 10 / x
  > echoln(show(f(A)))
  > echoln(show(d(0)))
  > echoln("not reached")
  > EOF
  $ DIKTOR_VIA_IR=0 diktor err.kel; echo "exit: $?"
  ⚠ match が非網羅的です。例えば B が漏れています
  1
  実行時エラー: ゼロ除算です
  exit: 3
  $ diktor --emit-ir err.kir err.kel; echo "exit: $?"
  ⚠ match が非網羅的です。例えば B が漏れています
  exit: 0
  $ diktor --run-ir err.kir; echo "exit: $?"
  1
  実行時エラー: ゼロ除算です
  exit: 3
  $ diktor --via-ir err.kel; echo "exit: $?"
  ⚠ match が非網羅的です。例えば B が漏れています
  1
  実行時エラー: ゼロ除算です
  exit: 3

ハンドラ式も、KIR の評価器が木の評価器と同じに評価する。
評価が届かないハンドラ式は、何もしない。

  $ cat > h.kel <<'EOF'
  > effect Ask = { ask: () => Int32 }
  > let with_ask(body: () => Int32 @ {Ask}): Int32 = body() handle { case ask() => resume(1) }
  > echoln("before")
  > let r = if false then with_ask(fn() => perform ask()) else 0
  > echoln(show(r))
  > echoln(show(with_ask(fn() => perform ask())))
  > EOF
  $ diktor --emit-ir h.kir h.kel && diktor --run-ir h.kir; echo "exit: $?"
  before
  0
  1
  exit: 0

同じ入力から書いた .kir は、何度書いても同じバイト列である。
起点のファイルを絶対パスで書いても、単位の鍵(IRSpec 2.2 節)は変わらない。
変わるのは、単位の元のファイルの綴り(IRSpec 2.3 節)だけである。

  $ diktor --emit-ir prog2.kir prog.kel && cmp prog.kir prog2.kir && echo same
  same
  $ diktor --emit-ir-text rel.kirt prog.kel && diktor --emit-ir-text abs.kirt "$PWD/prog.kel" && diff rel.kirt abs.kirt
  4c4
  < (unit "main" (paths "prog.kel"))
  ---
  > (unit "main" (paths "$TESTCASE_ROOT/prog.kel"))
  [1]
  $ diktor --emit-ir s1.kir sample/stubs.kel sample/sample.kel && diktor --emit-ir s2.kir sample/stubs.kel sample/sample.kel && cmp s1.kir s2.kir && echo same
  same

--emit-ir と --emit-ir-text を併せると、両方の形を書く。

  $ diktor --emit-ir both.kir --emit-ir-text both.kirt prog.kel && cmp prog.kir both.kir && head -1 both.kirt
  (kir 0 3 0)

型検査の誤りは今までどおり 1 で終わり、FILE を作らない。
旗の引数を省くと使い方の誤り(64)で、FILE に書けなければ出力の誤り(74)である。

  $ printf 'let x: Int32 = true\n' > bad.kel
  $ diktor --emit-ir bad.kir bad.kel; echo "exit: $?"; test -e bad.kir || echo "no file"
  ! bad.kel:1:5: 型エラー: 注釈された型を満たしません(型が一致しません: Int32 と Boolean)
  exit: 1
  no file
  $ diktor --emit-ir > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --emit-ir nodir/x.kir prog.kel; echo "exit: $?"
  diktor: KIR のバイナリを書き出せません: nodir/x.kir: No such file or directory
  exit: 74

開けても書き込みに失敗すれば、出力が小さくても 74 である。

  $ diktor --emit-ir /dev/full prog.kel; echo "exit: $?"
  diktor: KIR のバイナリを書き出せません: No space left on device
  exit: 74
  $ diktor --emit-ir-text /dev/full prog.kel; echo "exit: $?"
  diktor: KIR のテキストを書き出せません: No space left on device
  exit: 74

--run-ir は入力の .kel を取らず、ほかのモードの旗やプレリュードの旗とも併せられない(64)。
読めないファイルは、ほかの入力と同じく 64 である。

  $ diktor --run-ir prog.kir prog.kel 2>&1 | head -1; diktor --run-ir prog.kir prog.kel > /dev/null 2>&1; echo "exit: $?"
  diktor: --run-ir takes no input files
  exit: 64
  $ diktor --type-check --run-ir prog.kir > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --no-prelude --run-ir prog.kir > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --via-ir --run-ir prog.kir > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --run-ir > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --run-ir missing.kir; echo "exit: $?"
  diktor: ファイルを開けません: missing.kir: No such file or directory
  exit: 64

--via-ir も実行のモードの旗なので、ほかのモードの旗や KIR を書く旗と併せると 64 である。

  $ diktor --via-ir --type-check prog.kel > /dev/null 2>&1; echo "exit: $?"
  exit: 64
  $ diktor --via-ir --emit-ir v.kir prog.kel > /dev/null 2>&1; echo "exit: $?"; test -e v.kir || echo "no file"
  exit: 64
  no file

壊れた KIR は、読み込みか検証で拒み、65 で終える。
何も実行しないので、標準出力は空である。

  $ cp prog.kir m.kir && printf '\001' | dd of=m.kir bs=1 seek=1 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 0: マジックが KIR のものではありません
  exit: 65
  $ cp prog.kir m.kir && printf '\002' | dd of=m.kir bs=1 seek=6 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 8: 版 0.2 は読めません(読めるのは 0.3 だけです)
  exit: 65
  $ cp prog.kir m.kir && printf '\001' | dd of=m.kir bs=1 seek=8 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 12: 必要な機能のビット 0x00000001 を処理できません
  exit: 65
  $ head -c 10 prog.kir > m.kir && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 0: 見出しの 16 バイトがありません
  exit: 65
  $ head -c -1 prog.kir > m.kir && diktor --run-ir m.kir 2>&1 | sed 's/位置 [0-9]*/位置 N/'
  diktor: KIR を読み込めません: 位置 N: 節 0x0b の大きさがファイルの残りを超えます
  $ head -c -1 prog.kir > m.kir && diktor --run-ir m.kir > /dev/null 2>&1; echo "exit: $?"
  exit: 65
  $ cp prog.kir m.kir && printf '\000' >> m.kir && diktor --run-ir m.kir 2>&1 | sed 's/位置 [0-9]*/位置 N/'
  diktor: KIR を読み込めません: 位置 N: 節 0x00 は定義されていません
  $ diktor --emit-ir-text prog.kirt prog.kel && diktor --run-ir prog.kirt; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 0: マジックが KIR のものではありません
  exit: 65

読み込みは通るが、検証で拒む例。
単位の鍵の main を書き換えると、単位の列の形の検査に落ちる。

  $ printf 'let f(n: Int32): Int32 = n * 2\nlet x: Int32 = 1\n' > small.kel
  $ diktor --no-prelude --emit-ir small.kir small.kel && printf '\164' | dd of=small.kir bs=1 seek=26 conv=notrunc 2> /dev/null && diktor --run-ir small.kir; echo "exit: $?"
  diktor: KIR の検証に失敗しました: 単位の列が builtin、prelude で始まり main で終わる形になっていません
  exit: 65

検証が名前と個数から確かめる規則の例。
次の試験は、--no-prelude で書いた .kir の 1 バイトを書き換え、検証の拒否を確かめる。
書き換える位置は、書き手の出す表と式の並びと、起点のファイルの名前の長さで決まる。
--no-prelude なので、位置はプレリュードの中身によらない。
ファイルの名前を変えると、元のファイルの綴りの長さの分だけ位置が動く。

  $ cat > vrules.kel <<'EOF'
  > type class C1[A] { val a: (A) => Int32 }
  > type class C2[A] { val b: (A) => Int32; val c: (A) => Int32 }
  > newtype T = T
  > type instance C1[T] { let a(t: T): Int32 = 1 }
  > type instance C2[T] { let b(t: T): Int32 = 2; let c(t: T): Int32 = 3 }
  > effect Out = { write: (String) => Int32 }
  > extern "prim" let __int32_neg[A: Show](x: A): Int32
  > let twice[A: Add](x: A): A = x + x
  > let f(x: Int32): Int32 = { let p = x + 1; let q = p * 2; q }
  > let o(): Int32 @ {Out} = perform write("x")
  > let r: Int32 = a(T) + b(T) + twice(1) + f(2) + __int32_neg(1)
  > newtype U = U1(Int32) | U2(Int32)
  > let m(u: U): Int32 = u match { case U1(x) => x case U2(y) => y }
  > let e: Boolean = {a = m(U1(1))} == {a = 1}
  > EOF
  $ diktor --no-prelude --emit-ir vrules.kir vrules.kel && diktor --run-ir vrules.kir; echo "exit: $?"
  exit: 0
  $ patch_kir() { cp "$1" m.kir && printf "$3" | dd of=m.kir bs=1 seek="$2" conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"; }

組み込みの値は、付録 A.4 の記号を付録 A.4 の順に並べたものだけである。
builtin/Array.each を builtin/Array.fach に書き換えると、文字列の表の並びは保たれるので読み込みは通り、検証が拒む。

  $ o=$(grep -boa 'Array\.each' vrules.kir | cut -d: -f1) && patch_kir vrules.kir $((o + 6)) '\146'
  diktor: KIR の検証に失敗しました: 大域の表の先頭が、付録 A の組み込みの値の並びと合いません
  exit: 65

runtime の印は、プレリュードの Console の write にだけ付く。
利用者のエフェクト main/Out の write に印を付けると拒む。

  $ patch_kir vrules.kir 970 '\002'
  diktor: KIR の検証に失敗しました: エフェクト main/Out の操作 write の runtime の印が規則と合いません
  exit: 65

スロットは、束縛の有効範囲の中でだけ読める。
1 つ目は let の初期化式が、後の let で束縛するスロットを読む。
2 つ目は match の 2 つ目の節が、1 つ目の節のパターンで束縛したスロットを読む。

  $ patch_kir vrules.kir 1233 '\002'
  diktor: KIR の検証に失敗しました: 関数 main/f: スロット 2 を束縛の有効範囲の外で読みます
  exit: 65
  $ patch_kir vrules.kir 1397 '\001'
  diktor: KIR の検証に失敗しました: 関数 main/m: スロット 1 を束縛の有効範囲の外で読みます
  exit: 65

method と opcall の辞書は、そのクラスの辞書である。
構造的な辞書は builtin/Eq の辞書で、その項目も builtin/Eq の辞書である。
組み込みのインスタンスは、付録 A.3 の組だけである。

  $ patch_kir vrules.kir 1310 '\001'
  diktor: KIR の検証に失敗しました: 関数 main/r: クラス main/C1 の辞書の位置に、クラス main/C2 のインスタンスがあります
  exit: 65
  $ patch_kir vrules.kir 1230 '\001'
  diktor: KIR の検証に失敗しました: 関数 main/f: クラス builtin/Add の辞書の位置に、クラス builtin/Sub の組み込みのインスタンスがあります
  exit: 65
  $ patch_kir vrules.kir 1231 '\000'
  diktor: KIR の検証に失敗しました: 関数 main/f: 組み込みのインスタンス builtin/Add[builtin/Boolean] は付録 A.3 にありません
  exit: 65
  $ patch_kir vrules.kir 1406 '\010'
  diktor: KIR の検証に失敗しました: 関数 main/e: クラス builtin/Show の辞書の位置に、クラス builtin/Eq の構造的な辞書があります
  exit: 65
  $ patch_kir vrules.kir 1413 '\010'
  diktor: KIR の検証に失敗しました: 関数 main/e: クラス builtin/Eq の辞書の位置に、クラス builtin/Show の組み込みのインスタンスがあります
  exit: 65

インスタンスは、クラスの各メソッドをちょうど 1 回ずつ実装する。
C1 のインスタンスのクラスを、メソッドが 2 つある C2 に書き換えると、C2 の c の実装が無い。

  $ patch_kir vrules.kir 1030 '\012'
  diktor: KIR の検証に失敗しました: インスタンス main/instance:C1[T] がクラス main/C2 のメソッド c を実装しません
  exit: 65

dictapp の頭が大域なら、渡す辞書の数は、その大域が受け取る数と同じである。
1 つ目は extern の大域が受け取る数を 1 から 2 に、2 つ目は頭を種類 fn の大域に書き換える。

  $ patch_kir vrules.kir 1083 '\002'
  diktor: KIR の検証に失敗しました: 関数 main/r: main/__int32_neg に渡す辞書の数 1 が、受け取る数 2 と違います
  exit: 65
  $ patch_kir vrules.kir 1336 '\016'
  diktor: KIR の検証に失敗しました: 関数 main/r: 辞書を受け取らない大域 main/f に辞書を渡します
  exit: 65

記号は 単位の鍵/名前 の形で、単位の鍵は単位の表にある。
次の試験は、記号の 1 バイトを書き換える。
文字列の表の並びが保たれる位置なので、読み込みは通り、検証が拒む。
1 つ目は大域の記号 main/z の / を 0 に、2 つ目は型の記号 main/W の / を 0 に、3 つ目は main/W の単位の鍵を maio に書き換える。

  $ printf 'newtype W = W(Int32)\nlet z = W(5)\n' > w.kel && diktor --no-prelude --emit-ir w.kir w.kel && diktor --run-ir w.kir; echo "exit: $?"
  exit: 0
  $ o=$(grep -boa 'main/z' w.kir | cut -d: -f1) && patch_kir w.kir $((o + 4)) '0'
  diktor: KIR の検証に失敗しました: 大域の記号 main0z が 単位の鍵/名前 の形ではありません
  exit: 65
  $ printf 'newtype W = W(Int32)\n' > t.kel && diktor --no-prelude --emit-ir t.kir t.kel && diktor --run-ir t.kir; echo "exit: $?"
  exit: 0
  $ o=$(grep -boa 'main/W' t.kir | cut -d: -f1) && patch_kir t.kir $((o + 4)) '0'
  diktor: KIR の検証に失敗しました: 型の記号 main0W が 単位の鍵/名前 の形ではありません
  exit: 65
  $ o=$(grep -boa 'main/W' t.kir | cut -d: -f1) && patch_kir t.kir $((o + 3)) 'o'
  diktor: KIR の検証に失敗しました: 型の記号 maio/W の単位の鍵 maio が単位の表にありません
  exit: 65

コンストラクタのフィールドの数は任意の u32 で書けるが、construct が書くフィールドの数と違えば拒む。
w.kir の types の節の最後のバイトが W のフィールドの数である。
そのバイトを 5 バイトの 2^32 - 1 に置き換え、節の大きさを 23 から 27 に直す。
検証はフィールドの数の大きさの領域を確保しないので、メモリを使わずに拒む。

  $ { head -c 617 w.kir; printf '\033'; head -c 640 w.kir | tail -c +619; printf '\377\377\377\377\017'; tail -c +642 w.kir; } > m.kir && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR の検証に失敗しました: 関数 main/z: コンストラクタ W のフィールドが足りません
  exit: 65

runtime の印の付いた操作を持つエフェクトは、handle できない。
Console だけを宣言するプレリュードに差し替え、利用者のエフェクト W の handle をプレリュードの Console の handle に書き換える。

  $ printf 'pub effect Console = { write: (String) => Int32 }\n' > pconsole.kel
  $ cat > hw.kel <<'EOF'
  > effect W = { write: (String) => Int32 }
  > let g(): Int32 = perform write("a") handle { case write(s) => resume(1) }
  > EOF
  $ diktor --prelude pconsole.kel --emit-ir hw.kir hw.kel && diktor --run-ir hw.kir; echo "exit: $?"
  exit: 0
  $ patch_kir hw.kir 817 '\000'
  diktor: KIR の検証に失敗しました: 関数 main/g: runtime の印の付いた操作を持つエフェクト prelude/Console を handle します
  exit: 65

ハンドラ式は、エフェクトのすべての操作の節を持たなくても検証を通る。
そのエフェクトの操作は、節の無い操作でも、内側からいちばん近いそのエフェクトのハンドラが受け取る。
どの節にも一致しなければ実行時の誤り(3)であり、外側のハンドラへ送り直さない(IRSpec 9.4 節)。
内側のハンドラの b の節の操作を a に書き換えると、内側のハンドラは a の節を 2 つ持ち、b の節を持たない。

  $ cat > two.kel <<'EOF'
  > effect Two = { a: () => Int32, b: () => Int32 }
  > let x(): Int32 @ {Two} = perform a() + perform b()
  > let inner(): Int32 @ {Two} = x() handle { case a() => resume(1) case b() => resume(2) }
  > let main: Int32 = inner() handle { case a() => resume(100) case b() => resume(20) }
  > EOF
  $ diktor --no-prelude --emit-ir two.kir two.kel && diktor --run-ir two.kir; echo "exit: $?"
  exit: 0
  $ patch_kir two.kir 925 '\000'
  実行時エラー: handle のどの節にも一致しません: Two.b()
  exit: 3

UTF-8 でない名前を持つプログラムは KIR を持たず、テキストとバイナリのどちらを求めても、何も書かずに 64 で終える。
2 つ目の起点のファイルを UTF-8 でない名前のディレクトリに置くと、そこから import した単位の鍵はディレクトリの綴りを含む(IRSpec 2.2 節)。
木の評価器は、このプログラムをそのまま実行する。

  $ d=$(printf 'd\377') && mkdir "$d" && printf 'let a = 1\n' > ua.kel && printf 'from "./w" import { w }\nlet b = w\n' > "$d/b.kel" && printf 'pub let w: Int32 = 3\n' > "$d/w.kel"
  $ d=$(printf 'd\377'); DIKTOR_VIA_IR=0 diktor ua.kel "$d/b.kel"; echo "exit: $?"
  exit: 0
  $ d=$(printf 'd\377'); diktor --emit-ir u.kir ua.kel "$d/b.kel"; echo "exit: $?"; test -e u.kir || echo "no file"
  diktor: KIR を符号化できません: UTF-8 でない名前があります: d\255/w.kel
  exit: 64
  no file
  $ d=$(printf 'd\377'); diktor --emit-ir-text u.kirt ua.kel "$d/b.kel"; echo "exit: $?"; test -e u.kirt || echo "no file"
  diktor: KIR を符号化できません: UTF-8 でない名前があります: d\255/w.kel
  exit: 64
  no file
  $ d=$(printf 'd\377'); diktor --via-ir ua.kel "$d/b.kel"; echo "exit: $?"
  diktor: KIR を符号化できません: UTF-8 でない名前があります: d\255/w.kel
  exit: 64

ノードの深さが入れ子の限度 N_nest = 100,000(IRSpec 13.9 節)を超えるプログラムは KIR を持たない。
書き手は、テキストもバイナリも書かずに 1 で終え、--via-ir も評価を始めずに 1 で終える。
n 段の `1 + (...)` の式は、深さ n + 1 のノードを持つ。
99,999 段の式は限度ちょうどの深さで、書き出して実行できる。
100,000 段の式は限度を超える。
木の評価器は、どちらもそのまま実行する。

  $ awk 'BEGIN { s = "1"; for (i = 0; i < 99999; i++) s = "1 + (" s ")"; print "let x = " s; print "echoln(show(x))" }' > nest_max.kel
  $ awk 'BEGIN { s = "1"; for (i = 0; i < 100000; i++) s = "1 + (" s ")"; print "let x = " s; print "echoln(show(x))" }' > nest_over.kel
  $ diktor --emit-ir nest_max.kir nest_max.kel && diktor --run-ir nest_max.kir; echo "exit: $?"
  100000
  exit: 0
  $ diktor --via-ir nest_max.kel; echo "exit: $?"
  100000
  exit: 0
  $ DIKTOR_VIA_IR=0 diktor nest_over.kel; echo "exit: $?"
  100001
  exit: 0
  $ diktor --emit-ir nest_over.kir nest_over.kel; echo "exit: $?"; test -e nest_over.kir || echo "no file"
  diktor: KIR を書き出せません: 処理系の限度: KIR の書き出しで入れ子が深すぎます
  exit: 1
  no file
  $ diktor --emit-ir-text nest_over.kirt nest_over.kel; echo "exit: $?"; test -e nest_over.kirt || echo "no file"
  diktor: KIR を書き出せません: 処理系の限度: KIR の書き出しで入れ子が深すぎます
  exit: 1
  no file
  $ diktor --via-ir nest_over.kel; echo "exit: $?"
  diktor: KIR を書き出せません: 処理系の限度: KIR の書き出しで入れ子が深すぎます
  exit: 1
