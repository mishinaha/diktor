KIR のバージョンは 1.0 である(IRSpec 14 節)。
--emit-ir はヘッダにメジャーバージョン 1、マイナーバージョン 0、必須機能ビット 0 を書き、--emit-ir-text は (kir 1 0 0) を書く。

  $ printf 'let f(n: Int32): Int32 = n * 2\necholn(show(f(21)))\n' > v.kel
  $ diktor --emit-ir v.kir v.kel && od -A d -t x1 -N 16 v.kir | head -1
  0000000 00 4b 49 52 01 00 00 00 00 00 00 00 0b 00 00 00
  $ diktor --emit-ir-text v.kirt v.kel && head -1 v.kirt
  (kir 1 0 0)

リーダはメジャーバージョンだけを比較する。
マイナーバージョンが 0 より大きいファイルも、必須機能ビットが 0 なら読み込んで実行する。

  $ cp v.kir m.kir && printf '\001' | dd of=m.kir bs=1 seek=6 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  42
  exit: 0
  $ cp v.kir m.kir && printf '\377\377' | dd of=m.kir bs=1 seek=6 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  42
  exit: 0

マイナーバージョンが新しいファイルには、スキップできるセクション(id が 0x80 以上)が追加されていることがあり、リーダはそれを読み飛ばして実行する。
次のコマンドは、セクション数を 12 に書き換え、末尾に内容が 3 バイトのセクション 0x83 を追加したファイルを実行する。

  $ { head -c 12 v.kir; printf '\014\000\000\000'; tail -c +17 v.kir; printf '\203\003abc'; } > m.kir && printf '\001' | dd of=m.kir bs=1 seek=6 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  42
  exit: 0

メジャーバージョンが違うファイルは、マイナーバージョンによらず拒否し、終了コード 65 で終了する。
1.0 より前の草稿の版(0.y)も、メジャーバージョンが違うファイルとして拒否する。

  $ cp v.kir m.kir && printf '\000\000\003' | dd of=m.kir bs=1 seek=4 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 8: バージョン 0.3 は読めません(読めるのはメジャーバージョン 1 のバージョンだけです)
  exit: 65
  $ cp v.kir m.kir && printf '\002' | dd of=m.kir bs=1 seek=4 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 8: バージョン 2.0 は読めません(読めるのはメジャーバージョン 1 のバージョンだけです)
  exit: 65

マイナーバージョンが新しくても、未知の必須機能ビットが立っているファイルは拒否する。

  $ cp v.kir m.kir && printf '\001\000\001' | dd of=m.kir bs=1 seek=6 conv=notrunc 2> /dev/null && diktor --run-ir m.kir; echo "exit: $?"
  diktor: KIR を読み込めません: 位置 12: 必須機能ビット 0x00000001 を処理できません
  exit: 65
