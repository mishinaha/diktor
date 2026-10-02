Blocking はトップレベルに残せる(仕様 §9 / §12、D88)。かつてはトップレベル行が
{Console, Async} だけで、@ Blocking の付いた関数を pinned 無しでは呼べなかった。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

  $ cat > btop.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > echoln(show(sqrt(16.0)))
  > KEL
  $ diktor btop.kel
  4.0

pinned で落とすこともできる(仕様 §12)。落とさずに純粋な行へ持ち込むのは
従来どおり拒否:

  $ cat > bpure.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > let pure_sqrt(x: Float64): Float64 @ {} = pinned(fn() => sqrt(x))
  > let bad(x: Float64): Float64 @ {} = sqrt(x)
  > KEL
  $ diktor --type-check bpure.kel
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  pure_sqrt : (Float64) => Float64
  ! bpure.kel:3:37: 型エラー: ラベル Blocking がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を通すなら行変数を型パラメータに取ってください。§9)
  [1]

注釈した行に Blocking が無ければ、閉じた行に Blocking が無いという診断で落ちる:

  $ cat > bann.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > let g(x: Float64): Float64 @ Console = { echo("x"); sqrt(x) }
  > KEL
  $ diktor --type-check bann.kel
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  ! bann.kel:2:53: 型エラー: ラベル Blocking がありません(行は閉じています)
  [1]

Blocking は操作を持たないので handle の対象にできない(禁止の名指しでは
なく「属しません」で落ちる — ランタイム提供の名簿とは別扱い):

  $ cat > bh.kel <<'KEL'
  > let f[A, E](b: () => A @ {Blocking extends E}): A @ E =
  >   b() handle {
  >     case Blocking.nope() => resume({})
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check bh.kel
  ! bh.kel:2:3: 型エラー: 操作 nope はエフェクト Blocking に属しません
  [1]

Blocking に操作を足す宣言は拒否する(標準環境の名前なので再宣言できない):

  $ printf 'effect Blocking = { block: (String) => Int32 }\n' > bbad.kel
  $ diktor --type-check bbad.kel
  ! bbad.kel:1:1: 型エラー: 標準環境の effect Blocking は再宣言できません
  [1]

--no-prelude でも Blocking は組み込み登録なのでトップレベル行に残る:

  $ cat > bnp.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > let r = sqrt(16.0)
  > KEL
  $ diktor --type-check --no-prelude bnp.kel
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  r : Float64
