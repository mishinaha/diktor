文字列はバイト列である(LangSpec §4.4)。\u と \U のエスケープはコードポイントを
UTF-8 で符号化したバイト列になり、__string_length と __string_sub はバイト単位で
数えて切り出し、echo はバイト列を検査も変換もせずに書く。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

エスケープは UTF-8 で符号化する。\u00e9 は直接書いた é と同じ 2 バイトで、
\U0001F600 は 4 バイト、\u0000 は値 0 の 1 バイトである:

  $ cat > utf8esc.kel <<'KEL'
  > echoln(show(__string_length("\u00e9")))
  > echoln(show(__string_length("é")))
  > echoln(show("\u00e9" == "é"))
  > echoln(show(__string_length("\U0001F600")))
  > echoln(show(__string_length("\u0000")))
  > KEL
  $ diktor utf8esc.kel
  2
  2
  true
  4
  1
  $ printf 'echo("\\u0000|")\n' > nul.kel
  $ diktor nul.kel | od -An -tx1
   00 7c

切り出しは文字の途中でも切れ、echo は UTF-8 として正しくないバイト列もそのまま書く:

  $ cat > utf8cut.kel <<'KEL'
  > echo(__string_sub("\u00e9", 0, 1))
  > echo("|")
  > echo(__string_sub("\U0001F600", 1, 2))
  > KEL
  $ diktor utf8cut.kel | od -An -tx1
   c3 7c 9f 98

比較はバイトの辞書順なので、é(先頭バイト 0xc3)は z(0x7a)より大きい:

  $ printf 'echoln(show("\\u00e9" < "z"))\n' > utf8cmp.kel
  $ diktor utf8cmp.kel
  false
