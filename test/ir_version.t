KIR の版は 1.0 である(IRSpec 14 節)。
--emit-ir は見出しに主版 1、副版 0、必要な機能のビット 0 を書き、--emit-ir-text は (kir 1 0 0) を書く。

  $ printf 'let f(n: Int32): Int32 = n * 2\necholn(show(f(21)))\n' > v.kel
  $ diktor --emit-ir v.kir v.kel && od -A d -t x1 -N 16 v.kir | head -1
  0000000 00 4b 49 52 01 00 00 00 00 00 00 00 0b 00 00 00
  $ diktor --emit-ir-text v.kirt v.kel && head -1 v.kirt
  (kir 1 0 0)

読み手は主版だけを比べる。
副版が 0 より大きいファイルも、必要な機能のビットが 0 なら読んで実行する。

  $ cp v.kir m.kir && printf '\001' | dd of=m.kir bs=1 seek=6 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  42
  exit: 0
  $ cp v.kir m.kir && printf '\377\377' | dd of=m.kir bs=1 seek=6 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  42
  exit: 0

副版の新しいファイルが足してよい読み飛ばせる節(id が 0x80 以上)も読み飛ばす。
次は、節の数を 12 にして、末尾に中身が 3 バイトの節 0x83 を足したものである。

  $ { head -c 12 v.kir; printf '\014\000\000\000'; tail -c +17 v.kir; printf '\203\003abc'; } > m.kir && printf '\001' | dd of=m.kir bs=1 seek=6 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  42
  exit: 0

主版が違うファイルは、副版を問わずに拒み、65 で終える。
1.0 より前の草稿の版(0.y)も主版が違う。

  $ cp v.kir m.kir && printf '\000\000\003' | dd of=m.kir bs=1 seek=4 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 8: 版 0.3 は読めません(読めるのは主版 1 の版だけです)
  exit: 65
  $ cp v.kir m.kir && printf '\002' | dd of=m.kir bs=1 seek=4 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 8: 版 2.0 は読めません(読めるのは主版 1 の版だけです)
  exit: 65

副版が新しくても、知らない機能のビットを要るファイルは拒む。

  $ cp v.kir m.kir && printf '\001\000\001' | dd of=m.kir bs=1 seek=6 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 12: 必要な機能のビット 0x00000001 を処理できません
  exit: 65
