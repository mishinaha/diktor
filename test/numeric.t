数値・浮動小数の一貫性(計画 260829-4 ワークストリーム A)。

Float64 → 整数の変換は NaN と範囲外を実行時エラーにする(A9。かつては
Int32.of_float / Int64.of_float 素通しで、黙って INT_MIN を返していた):

  $ printf 'echoln(show(__f64_to_i32(2.7)))\necholn(show(__f64_to_i32(0.0 - 2.7)))\n' > cvok.kel
  $ diktor cvok.kel
  2
  -2

  $ printf 'echoln(show(__f64_to_i32(0.0 / 0.0)))\n' > cvnan.kel
  $ diktor cvnan.kel
  実行時エラー: __f64_to_i32: NaN は整数に変換できません
  [3]

  $ printf 'echoln(show(__f64_to_i32(1.0e20)))\n' > cvbig.kel
  $ diktor cvbig.kel
  実行時エラー: __f64_to_i32: 変換結果が範囲外です: 1e+20
  [3]

  $ printf 'echoln(show(__f64_to_i32(1.0 / 0.0)))\n' > cvinf.kel
  $ diktor cvinf.kel
  実行時エラー: __f64_to_i32: 変換結果が範囲外です: inf
  [3]

境界: Int32 の最大・最小はちょうど変換でき、最大 + 1 は落ちる:

  $ printf 'echoln(show(__f64_to_i32(2147483647.0)))\necholn(show(__f64_to_i32(0.0 - 2147483648.0)))\n' > cvedge.kel
  $ diktor cvedge.kel
  2147483647
  -2147483648

  $ printf 'echoln(show(__f64_to_i32(2147483648.0)))\n' > cvover.kel
  $ diktor cvover.kel
  実行時エラー: __f64_to_i32: 変換結果が範囲外です: 2147483648.0
  [3]

Int64 → Int32 は従来どおり wrap-around(整数算術の裁定に揃える):

  $ printf 'echoln(show(__i64_to_i32(__f64_to_i64(2147483648.0))))\n' > cvwrap.kel
  $ diktor cvwrap.kel
  -2147483648
