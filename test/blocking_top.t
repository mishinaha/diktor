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

注釈した行に Blocking が無ければ、剛い行に足せないという従来の診断:

  $ cat > bann.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > let g(x: Float64): Float64 @ Console = { echo("x"); sqrt(x) }
  > KEL
  $ diktor --type-check bann.kel
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  ! bann.kel:2:53: 型エラー: 行 ς1 は注釈で固定された行変数なので、ラベル Blocking を足せません(注釈側に Blocking を(必要なら引数つきで)書き足してください)
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

操作を足した再宣言は照合で落ちる(Heap と同じ組み込みラベル):

  $ printf 'effect Blocking = { block: (String) => Int32 }\n' > bbad.kel
  $ diktor --type-check bbad.kel
  ! bbad.kel:1:1: 型エラー: effect Blocking の宣言がプレリュードの宣言と一致しません(操作が違います: プレリュードは操作を持ちません)
  [1]

--no-prelude でも Blocking は組み込み登録なのでトップレベル行に残る:

  $ cat > bnp.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > let r = sqrt(16.0)
  > KEL
  $ diktor --type-check --no-prelude bnp.kel
  sqrt : (Float64) => Float64 @ {Blocking extends R1}
  r : Float64
