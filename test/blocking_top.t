Blocking はトップレベルで許されるエフェクトに含まれる(sample.kel §9、§12、第11章 §11.30)。そのため、
@ Blocking の付いた関数を、pinned を使わずにトップレベルから呼び出せる。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

  $ cat > btop.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > echoln(show(sqrt(16.0)))
  > KEL
  $ diktor btop.kel
  4.0

pinned で Blocking を行から取り除くこともできる(sample.kel §12)。取り除かずに純粋な行の本体で
呼び出すと、型エラーになる:

  $ cat > bpure.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > let pure_sqrt(x: Float64): Float64 @ {} = pinned(fn() => sqrt(x))
  > let bad(x: Float64): Float64 @ {} = sqrt(x)
  > KEL
  $ diktor --type-check bpure.kel
  sqrt : (Float64) => Float64 @ {Blocking}
  pure_sqrt : (Float64) => Float64 @ {}
  ! bpure.kel:3:37: 型エラー: ラベル Blocking がありません(行は閉じています)(この位置の行は空 = 純粋です — 注釈の @ {} か、高階の引数の行が @ {} だからです(入れ子の矢印の @ 省略も @ {} と読みます)。行を伝えるなら行変数を型パラメータに取ってください。§9)
  [1]

型注釈に書いた閉じた行に Blocking がなければ、ラベル Blocking がないことを報告する型エラーになる:

  $ cat > bann.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > let g(x: Float64): Float64 @ Console = { echo("x"); sqrt(x) }
  > KEL
  $ diktor --type-check bann.kel
  sqrt : (Float64) => Float64 @ {Blocking}
  ! bann.kel:2:53: 型エラー: ラベル Blocking がありません(行は閉じています)
  [1]

Blocking は操作を持たないので、handle の対象にできない。ユーザがハンドルできないエフェクトの一覧(第7章 §7.3 の runtime_effects)には
入っていないので、ハンドルを禁止する診断ではなく、`操作 nope はエフェクト Blocking に属しません` の診断になる:

  $ cat > bh.kel <<'KEL'
  > let f[A, E](b: () => A @ {Blocking extends E}): A @ E =
  >   b() handle {
  >     case Blocking.nope() => resume({})
  >     case return(x) => x
  >   }
  > KEL
  $ diktor --type-check bh.kel
  ! bh.kel:3:10: 型エラー: 操作 nope はエフェクト Blocking に属しません
  [1]

Blocking に操作を追加する宣言は拒否する(標準環境の名前なので再宣言できない):

  $ printf 'effect Blocking = { block: (String) => Int32 }\n' > bbad.kel
  $ diktor --type-check bbad.kel
  ! bbad.kel:1:1: 型エラー: 標準環境の effect Blocking は再宣言できません
  [1]

Blocking は組み込みとして登録してあるので、--no-prelude でもトップレベルの行に残る:

  $ cat > bnp.kel <<'KEL'
  > extern "C" let sqrt(x: Float64): Float64 @ Blocking
  > let r = sqrt(16.0)
  > KEL
  $ diktor --type-check --no-prelude bnp.kel
  sqrt : (Float64) => Float64 @ {Blocking}
  r : Float64
