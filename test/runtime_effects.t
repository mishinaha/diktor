ランタイム提供エフェクトのハンドル禁止(M20 / I4 / D63)。Async は仕様の
明文(sample.kel:480)、Console は同じ扱いを提案中。かつては出力を黙って
消す恒等ハンドラが書けた。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

  $ cat > quiet.kel <<'KEL'
  > let quiet[A, E](body: () => A @ {Console extends E}): A @ E =
  >   body() handle {
  >     case write(s) => resume({})
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check quiet.kel
  ! quiet.kel:2:3: 型エラー: エフェクト Console はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:342, :453)。出力先を変えたいときは Print をハンドルしてください(プレリュードの with_stdout が Print を Console へ翻訳します)
  [1]

修飾しても同じ:

  $ cat > quietq.kel <<'KEL'
  > let quiet[A, E](body: () => A @ {Console extends E}): A @ E =
  >   body() handle {
  >     case Console.write(s) => resume({})
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check quietq.kel
  ! quietq.kel:2:3: 型エラー: エフェクト Console はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:342, :453)。出力先を変えたいときは Print をハンドルしてください(プレリュードの with_stdout が Print を Console へ翻訳します)
  [1]

  $ cat > sched.kel <<'KEL'
  > let sched[A, E](body: () => A @ {Async extends E}): A @ E =
  >   body() handle {
  >     case yield_() => resume({})
  >     case sleep(ms) => resume({})
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check sched.kel
  ! sched.kel:2:3: 型エラー: エフェクト Async はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:480。スケジューラは書けません)
  [1]

--no-prelude で自前の effect Console を宣言した場合は禁止しない
(禁止の判定は「ランタイム行に名前があり、かつプレリュード所有」):

  $ cat > ownconsole.kel <<'KEL'
  > effect Console = { write: (String) => {} }
  > let quiet[A, E](body: () => A @ {Console extends E}): A @ E =
  >   body() handle {
  >     case write(s) => resume({})
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check --no-prelude ownconsole.kel
  quiet : (() => A @ {Console extends R1}) => A

Console はハンドル候補からも外れるので、File のつもりの case write(s)
1 本は Console に黙って解決されず、意図の取り違えが診断になる:

  $ cat > filewrite.kel <<'KEL'
  > effect File = { read: (Int32) => String, write: (String) => Int32 }
  > let h[A, E](b: () => A @ {File extends E}): A @ E =
  >   b() handle {
  >     case write(s) => resume(0)
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check filewrite.kel
  ! filewrite.kel:3:3: 型エラー: ハンドラが操作を網羅していません: File の read が漏れています
  [1]

perform は禁止しない(sample.kel:453 がトップレベルの perform write を
書いており、プレリュードの echo / echoln も同じ):

  $ printf 'perform write("direct\\n")\n' > pw.kel
  $ diktor pw.kel
  direct
