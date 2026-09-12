仕様が明示的に保留した項目の現状を見張る(D109)。**このファイルは diktor の
意図した挙動ではなく、仕様 §14 が TODO として保留した項目の「現状」を機械に
見張らせるためにある。** 仕様が裁定を下したらここが最初に鳴り、鳴った
ブロックの見出しが仕様の行と関係する章を教える。裁定が下りた項目の観測点は
削らず、意図した挙動のゴールデンとして通常の回帰テストへ移す。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

来歴: 2026-09-12 の仕様改訂で doc/log/260830-1-m20.md §1 の台帳 10 項目のうち
8 項目が確定した(行き先の一覧は doc/log/260912-3-sync.md §3)。ここにあった
Array 系 4 ブロック(arrayhole / eachheap / eachpure / eachclosed)は
test/region.t へ(M24)、cancelre は test/eval.t の cancelouter / cancelnores へ
(M21)、tupledefault は削除(観測点は test/typecheck.t の resugar と
test/typecheck_sample.t が持つ。M25)。以下は改訂後の §14 の TODO 12 件のうち、
diktor が観測点を置ける 4 件。Chan の署名(§14:765)、module の入れ子(:766)、
Ord[Float64] と NaN(:767-771)は cram では観測できないので記録のみ。

非 pub の let で「本体は純粋、呼び出しはどの行からでも可」を注釈で書く手段
(§14:775-776、§9)。現状は @ を省略した let が行変数に一般化され、@ {} と
明示すると呼び出し側の行まで空に縛る。sum と sum2 は表示が同じ
(Array[Int32]) => Int32 なのに、片方だけが Console の下から呼べる(第9章 §9.6
の「正直な代償」の観測点):

  $ cat > sumgen.kel <<'KEL'
  > let sum(xs: Array[Int32]): Int32 = run h {
  >   let acc = Ref.new(0)
  >   Array.each(xs, fn(x) => Ref.set(acc, Ref.get(acc) + x))
  >   Ref.get(acc)
  > }
  > let effectful(xs: Array[Int32]): Int32 @ {Console} = { echoln("go"); sum(xs) }
  > let pure_ok(xs: Array[Int32]): Int32 @ {} = sum(xs)
  > KEL
  $ diktor --type-check sumgen.kel

  $ cat > sumclosed.kel <<'KEL'
  > let sum2(xs: Array[Int32]): Int32 @ {} = 1
  > let effectful(xs: Array[Int32]): Int32 @ {Console} = { echoln("go"); sum2(xs) }
  > KEL
  $ diktor --type-check sumclosed.kel

非有限値(NaN、無限大)のリテラル(§14:772、§2)。現状は無く、文字列化の字面
nan / inf は読み戻せない(表示側は test/numeric.t の infnan):

  $ printf 'let x: Float64 = nan\n' > nanlit.kel
  $ diktor --type-check nanlit.kel

整数算術の桁あふれ(§14:773、§2)。現状は wrap-around で、実行時エラーにする
案が仕様に残っている(変換の実行時エラーとの対比は test/numeric.t の cvbig):

  $ cat > wrap.kel <<'KEL'
  > let maxi = 2147483647
  > let mini = 0 - maxi - 1
  > echoln(show(maxi + 1))
  > echoln(show(mini - 1))
  > echoln(show(maxi * 2))
  > echoln(show(9223372036854775807i64 + 1i64))
  > KEL
  $ diktor wrap.kel

不変配列の生成手段(§14:774、§10)。現状は MutableArray.freeze だけで、リテラルも
Array.new も無い(freeze の側は test/region.t の freeze / nonew):

  $ printf 'let mk(): Array[Int32] = run h { Array.new(3, 0) }\n' > nonew.kel
  $ diktor --type-check nonew.kel
  $ printf 'let xs: Array[Int32] = [1, 2, 3]\n' > arrlit.kel
  $ diktor --type-check arrlit.kel
