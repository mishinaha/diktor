ランタイム提供エフェクトのハンドル禁止(M20 / I4 / D63)。仕様 sample.kel:538 が
Console を名指しで定める。かつては出力を黙って消す恒等ハンドラが書けた。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

  $ cat > quiet.kel <<'KEL'
  > let quiet[A, E](body: () => A @ {Console extends E}): A @ E =
  >   body() handle {
  >     case write(s) => resume({})
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check quiet.kel
  ! quiet.kel:2:3: 型エラー: エフェクト Console はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:466, :538)。出力先を変えたいときは Print をハンドルしてください(プレリュードの with_stdout が Print を Console へ翻訳します)
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
  ! quietq.kel:2:3: 型エラー: エフェクト Console はランタイムが提供するため、ユーザはハンドルできません(仕様 sample.kel:466, :538)。出力先を変えたいときは Print をハンドルしてください(プレリュードの with_stdout が Print を Console へ翻訳します)
  [1]

Async は標準環境に無い。利用者が宣言したものは普通のエフェクトで、ハンドルできる:

  $ cat > asyncuser.kel <<'KEL'
  > effect Async = { yield_: () => Unit, sleep: (Int64) => Unit }
  > let sched[A, E](body: () => A @ {Async extends E}): A @ E =
  >   body() handle {
  >     case yield_() => resume({})
  >     case sleep(ms) => resume({})
  >   }
  > echoln(show(sched(fn() => { perform yield_(); 1 })))
  > KEL
  $ diktor asyncuser.kel
  1

トップレベルには残せない:

  $ printf 'effect Async = { yield_: () => Unit, sleep: (Int64) => Unit }\nperform yield_()\n' > asynctop.kel
  $ diktor --type-check asynctop.kel
  ! asynctop.kel:2:1: 型エラー: エフェクト Async をここでは実行できません(ラベル Async がありません(行は閉じています))
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

perform は禁止しない(sample.kel:662 がトップレベルの perform write を
書いており、プレリュードの echo / echoln も同じ):

  $ printf 'perform write("direct\\n")\n' > pw.kel
  $ diktor pw.kel
  direct

ランタイム行に載るのは名簿 toplevel_effects(Console / Blocking)のうち
プレリュード所有のものだけ(M20 検証。Blocking だけは組み込み登録なので
--no-prelude でも所有のまま — test/blocking_top.t の bnp。
かつては名前だけで張られ、--no-prelude や差し替えプレリュードの世界で
自前の effect Console を宣言すると、型はユーザの署名・実行はランタイムの
実装という食い違いが起き、型検査を通ったプログラムが実行時に落ちた):

  $ cat > np3.kel <<'KEL'
  > effect Console = { write: (Int32) => Int32 }
  > let r = perform write(42)
  > KEL
  $ diktor --type-check --no-prelude np3.kel
  ! np3.kel:2:9: 型エラー: エフェクト Console をここでは実行できません(ラベル Console がありません(行は閉じています))
  [1]
  $ printf 'effect Nothing = { nope: () => {} }\n' > mypre.kel
  $ diktor --prelude mypre.kel --type-check np3.kel
  ! np3.kel:2:9: 型エラー: エフェクト Console をここでは実行できません(ラベル Console がありません(行は閉じています))
  [1]

自前の Console を自前でハンドルする形は従来どおり通る:

  $ cat > npok.kel <<'KEL'
  > effect Console = { write: (String) => {} }
  > let quiet[A, E](body: () => A @ {Console extends E}): A @ E =
  >   body() handle {
  >     case write(s) => resume({})
  >     case return(x) => x
  >   }
  > let n = quiet(fn() => { perform write("x"); 7 })
  > KEL
  $ diktor --type-check --no-prelude npok.kel
  quiet : (() => A @ {Console extends R1}) => A
  n : Int32

Fs はランタイムの名簿に無い普通の名前なので、操作つきで宣言して自前で
ハンドルできる:

  $ cat > ownfs.kel <<'KEL'
  > effect Fs = { touch: (String) => Int32 }
  > let with_fs[A, E](body: () => A @ {Fs extends E}): A @ E =
  >   body() handle {
  >     case touch(p) => resume(0)
  >     case return(x) => x
  >   }
  > let n = with_fs(fn() => perform touch("x"))
  > KEL
  $ diktor --type-check ownfs.kel
  with_fs : (() => A @ {Fs extends R1}) => A
  n : Int32
