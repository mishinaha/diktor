仕様が「入れない」と決めたものを、入っていないことで固定する(§0 / §3 / §7)。
このファイルが鳴ったら、機能が足されたか、文法が動いたかのどちらか。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

or パターンは入れない(§7。パターンの文法に | を出さなければ、必要に
なってから足しても既存の文法と衝突しない):

  $ cat > orpat.kel <<'KEL'
  > let f(v: #Even | #Odd): Int32 = v match {
  >   case #Even | #Odd => 1
  > }
  > KEL
  $ diktor --type-check orpat.kel
  orpat.kel:2:14: パースエラー(付近のトークンを確認してください)
  [2]

節パターンの型注釈も現状は無い(§7。将来入れるなら、矢印を含む型注釈は
括弧必須。字句層が型の終わりを決められないため):

  $ cat > patannot.kel <<'KEL'
  > let f(x: Int32): Int32 = x match {
  >   case n: Int32 => n
  > }
  > KEL
  $ diktor --type-check patannot.kel
  patannot.kel:2:9: パースエラー(付近のトークンを確認してください)
  [2]

レコード更新の基底は小文字始まりの識別子 1 個(§3 が基底を識別子 1 個に
限り、大小は裁定 D113 が決める)。§0 の `{` の読み分けが IDENT の直後の
with だけを見るので基底に式は書けず、大文字始まりは字句分類を通るので
意味アクションが構文エラーで落とす。基底を式にしたいときは let で束縛
する:

  $ printf 'let p = {origin = {x = 1.0}}\nlet q = {p.origin with x = 3.0}\n' > updbase.kel
  $ diktor --type-check updbase.kel
  updbase.kel:2:19: パースエラー(付近のトークンを確認してください)
  [2]

  $ printf 'let f(n: Int32) = {x = n}\nlet q = {f(1) with x = 3}\n' > updbase2.kel
  $ diktor --type-check updbase2.kel
  updbase2.kel:2:15: パースエラー(付近のトークンを確認してください)
  [2]

  $ printf 'let p = {x = 1}\nlet q = {P with x = 3}\n' > updbase3.kel
  $ diktor --type-check updbase3.kel
  updbase3.kel:3:1: 構文エラー: レコード更新の基底は小文字始まりの識別子 1 個です
  [2]

(小文字の基底が通ることは test/typecheck.t / test/eval.t / test/ast.t /
test/tokens.t の `{p with …}` のブロックが固定している。)

識別子の大小(§0。型名・コンストラクタ・エフェクト名・モジュール名は大文字
始まり、操作名は小文字始まり。文法が構造的に強制する):

  $ printf 'type foo = Int32\n' > case1.kel
  $ diktor --type-check case1.kel
  case1.kel:1:6: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'newtype foo = Bar\n' > case2.kel
  $ diktor --type-check case2.kel
  case2.kel:1:9: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'effect foo = { op: () => {} }\n' > case3.kel
  $ diktor --type-check case3.kel
  case3.kel:1:8: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'module foo { }\n' > case4.kel
  $ diktor --type-check case4.kel
  case4.kel:1:8: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'effect E = { Op: () => {} }\n' > case5.kel
  $ diktor --type-check case5.kel
  case5.kel:1:14: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'newtype T = ctor(Int32)\n' > case6.kel
  $ diktor --type-check case6.kel
  case6.kel:1:13: パースエラー(付近のトークンを確認してください)
  [2]

型パラメータの束縛子はこの規則の例外で、大小を問わない(裁定 D110)。大小は型の
表示に現れないので、小文字で束縛しても大文字で束縛しても同じ型が出る。リージョン
変数を型パラメータの位置に小文字で書けるのもこの例外による。run が導入する
リージョン変数のほうは小文字に限り、大文字始まりも _ も構文エラーになる(小文字の
run h が通ることは test/region.t / test/parallel.t が固定している):

  $ printf 'let f[a](x: a): a = x\n' > case7.kel
  $ diktor --type-check case7.kel
  f : (A) => A
  $ printf 'let f[A](x: A): A = x\n' > case7b.kel
  $ diktor --type-check case7b.kel
  f : (A) => A
  $ printf 'let use[h, A](r: Ref[h, A]): A @ Heap[h] = Ref.get(r)\n' > case7c.kel
  $ diktor --type-check case7c.kel
  use : (Ref[A, B]) => B @ {Heap[A] extends R1}
  $ printf 'let g(): Int32 = run H { 1 }\n' > case8.kel
  $ diktor --type-check case8.kel
  case8.kel:1:22: パースエラー(付近のトークンを確認してください)
  [2]
  $ printf 'let g(): Int32 = run _ { 1 }\n' > case9.kel
  $ diktor --type-check case9.kel
  case9.kel:1:22: パースエラー(付近のトークンを確認してください)
  [2]

(スーパークラスの拒否は test/classes.t、Zero / One が無いことは型クラス表に
そもそも項目が無いことで、Char が無いことは test/numeric.t で固定している。)
