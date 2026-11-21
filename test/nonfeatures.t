仕様が導入しないと決めた機能が、処理系に入っていないことを固定する(sample.kel の §0、§3、§7 と LangSpec)。
このファイルのテストが失敗したら、機能が追加されたか、文法が変わったかのどちらかである。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

or パターンは導入しない(sample.kel の §7)。パターンの文法に | を入れないでおけば、
必要になってから追加しても既存の文法と衝突しない:

  $ cat > orpat.kel <<'KEL'
  > let f(v: #Even | #Odd): Int32 = v match {
  >   case #Even | #Odd => 1
  > }
  > KEL
  $ diktor --type-check orpat.kel
  orpat.kel:2:14: 構文エラー: 付近のトークンを確認してください
  [2]

節のパターンには型注釈を書けない(sample.kel の §7、LangSpec §11.1)。将来導入する場合は、矢印を含む型注釈に
括弧を必須にする。字句解析の段階では、型がどこで終わるかを決められないためである:

  $ cat > patannot.kel <<'KEL'
  > let f(x: Int32): Int32 = x match {
  >   case n: Int32 => n
  > }
  > KEL
  $ diktor --type-check patannot.kel
  patannot.kel:2:9: 構文エラー: 付近のトークンを確認してください
  [2]

レコード更新の更新元(診断では「基底」)は、小文字で始まる識別子 1 個に限る(sample.kel の §3)。
sample.kel の §0 の `{` の判別は IDENT の直後の with だけを見るので、更新元に式は書けない。
大文字で始まる識別子は `{` の判別を通過するので、
構文解析の意味動作が構文エラーにする。更新元に式を使いたいときは、let で束縛
する:

  $ printf 'let p = {origin = {x = 1.0}}\nlet q = {p.origin with x = 3.0}\n' > updbase.kel
  $ diktor --type-check updbase.kel
  updbase.kel:2:19: 構文エラー: 付近のトークンを確認してください
  [2]

  $ printf 'let f(n: Int32) = {x = n}\nlet q = {f(1) with x = 3}\n' > updbase2.kel
  $ diktor --type-check updbase2.kel
  updbase2.kel:2:15: 構文エラー: 付近のトークンを確認してください
  [2]

  $ printf 'let p = {x = 1}\nlet q = {P with x = 3}\n' > updbase3.kel
  $ diktor --type-check updbase3.kel
  updbase3.kel:2:10: 構文エラー: レコード更新の基底は小文字始まりの識別子 1 個です
  [2]

(小文字で始まる更新元を受理することは、test/typecheck.t、test/eval.t、test/ast.t、
test/tokens.t のレコード更新のブロックが固定している。)

識別子の大文字と小文字の規則を確かめる(sample.kel の §0)。型名、コンストラクタ、エフェクト名、モジュール名は大文字で
始め、操作名は小文字で始める。この区別は文法が強制する:

  $ printf 'type foo = Int32\n' > case1.kel
  $ diktor --type-check case1.kel
  case1.kel:1:6: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'newtype foo = Bar\n' > case2.kel
  $ diktor --type-check case2.kel
  case2.kel:1:9: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'effect foo = { op: () => {} }\n' > case3.kel
  $ diktor --type-check case3.kel
  case3.kel:1:8: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'module foo { }\n' > case4.kel
  $ diktor --type-check case4.kel
  case4.kel:1:8: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'effect E = { Op: () => {} }\n' > case5.kel
  $ diktor --type-check case5.kel
  case5.kel:1:14: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'newtype T = ctor(Int32)\n' > case6.kel
  $ diktor --type-check case6.kel
  case6.kel:1:13: 構文エラー: 付近のトークンを確認してください
  [2]

型パラメータの束縛子はこの規則の対象外で、大文字で始めても小文字で始めてもよい(sample.kel の §0、
sample.kel:50-51)。この違いは型の表示に現れず、小文字で束縛しても大文字で
束縛しても同じ型が表示される(case7c のリージョンの位置の変数は h と表示される)。
リージョン変数を型パラメータの位置に小文字で書けるのも、束縛子がこの規則の対象外だからである。run が導入する
リージョン変数は小文字で始まる識別子に限り、大文字で始まる名前も _ も構文エラーになる(sample.kel:52)。
小文字の run h を受理することは test/region.t が固定している:

  $ printf 'let f[a](x: a): a = x\n' > case7.kel
  $ diktor --type-check case7.kel
  f : (A) => A
  $ printf 'let f[A](x: A): A = x\n' > case7b.kel
  $ diktor --type-check case7b.kel
  f : (A) => A
  $ printf 'let use[h, A](r: Ref[h, A]): A @ Heap[h] = Ref.get(r)\n' > case7c.kel
  $ diktor --type-check case7c.kel
  use : (Ref[h, A]) => A @ {Heap[h]}
  $ printf 'let g(): Int32 = run H { 1 }\n' > case8.kel
  $ diktor --type-check case8.kel
  case8.kel:1:22: 構文エラー: 付近のトークンを確認してください
  [2]
  $ printf 'let g(): Int32 = run _ { 1 }\n' > case9.kel
  $ diktor --type-check case9.kel
  case9.kel:1:22: 構文エラー: 付近のトークンを確認してください
  [2]

予約語は、レコードのラベルの位置でも識別子として使えない。{run: …} を書けない理由は
矢印ではない。下の入力には矢印がないが、それでも run の位置で構文エラーになる。
run をラベルにできないのは、run が予約語(第2章 §2.4)だからである。フィールド名を変えれば
書ける(test/annot_rows.t の nestrec が {go: () => Unit} を固定している)。
LangSpec §2.2 が予約語の一覧を示し、レコードのラベルを含めて、
識別子を書く位置には使えないと定めている:

  $ printf 'let f(r: {run: Int32}): Int32 = 1\n' > kwlabel.kel
  $ diktor --type-check kwlabel.kel
  kwlabel.kel:1:11: 構文エラー: 予約語 run はここには書けません(予約語は識別子に使えません)
  [2]

(スーパークラスを拒否することは test/classes.t が、Char がないことは test/numeric.t が固定している。
Zero と One は、型クラスの表にそもそも項目がない。)

標準環境(LangSpec §16)に、ファイル操作のプリミティブと Fs エフェクトはない:

  $ printf 'let h = __open("a")\n' > fsprim.kel
  $ diktor --type-check fsprim.kel
  ! fsprim.kel:1:9: 型エラー: 未束縛の変数: __open
  [1]
  $ printf 'let h = __read\n' > fsprim2.kel
  $ diktor --type-check fsprim2.kel
  ! fsprim2.kel:1:9: 型エラー: 未束縛の変数: __read
  [1]
  $ printf 'let h = __write\n' > fsprim3.kel
  $ diktor --type-check fsprim3.kel
  ! fsprim3.kel:1:9: 型エラー: 未束縛の変数: __write
  [1]
  $ printf 'let h = __close\n' > fsprim4.kel
  $ diktor --type-check fsprim4.kel
  ! fsprim4.kel:1:9: 型エラー: 未束縛の変数: __close
  [1]
  $ printf 'let f(): Unit @ Fs = ()\n' > fs.kel
  $ diktor --type-check fs.kel
  ! fs.kel:1:17: 型エラー: 未知のエフェクト: Fs
  [1]

derive structural はない(LangSpec §12.5)。構造的な比較は Eq に組み込まれている:

  $ cat > derive.kel <<'KEL'
  > type class C[A] {
  >   val c: (A) => Int32
  >   derive structural
  > }
  > KEL
  $ diktor --type-check derive.kel
  derive.kel:3:3: 構文エラー: 付近のトークンを確認してください
  [2]

derive は予約語ではない:

  $ printf 'let derive = 1\necholn(show(derive))\n' > deriveid.kel
  $ diktor deriveid.kel
  1

par と par_map は標準環境にない(LangSpec §16):

  $ printf 'let p = par(fn() => 1, fn() => 2)\n' > par.kel
  $ diktor --type-check par.kel
  ! par.kel:1:9: 型エラー: 未束縛の変数: par
  [1]
  $ printf 'let q = par_map\n' > parmap.kel
  $ diktor --type-check parmap.kel
  ! parmap.kel:1:9: 型エラー: 未束縛の変数: par_map
  [1]

型エイリアスと newtype のパラメータには制約を書けない(LangSpec §12.1):

  $ printf 'type P[A: Show] = (A, A)\n' > aliascons.kel
  $ diktor --type-check aliascons.kel
  ! aliascons.kel:1:1: 型エラー: 型エイリアス P の型パラメータ A には型クラスの制約を書けません
  [1]
  $ printf 'newtype Box[A: Show] = Box(A)\n' > ntcons.kel
  $ diktor --type-check ntcons.kel
  ! ntcons.kel:1:1: 型エラー: newtype Box の型パラメータ A には型クラスの制約を書けません
  [1]

関数の型パラメータには制約を書ける:

  $ cat > fncons.kel <<'KEL'
  > newtype Box[A] = Box(A)
  > let f[A: Show](b: Box[A]): String = b match { case Box(x) => show(x) }
  > echoln(f(Box(2)))
  > KEL
  $ diktor fncons.kel
  2

newtype の右辺に ??? は書けない(LangSpec §10.1):

  $ printf 'newtype Hidden = ???\n' > nthole.kel
  $ diktor --type-check nthole.kel
  nthole.kel:1:18: 構文エラー: 付近のトークンを確認してください
  [2]

値束縛には型パラメータを書けない(LangSpec 付録 A.8)。文法の binding の値束縛の形は
typarams を持たない:

  $ cat > valtyparam.kel <<'KEL'
  > let x[A]: List[A] = Nil
  > KEL
  $ diktor --type-check valtyparam.kel
  valtyparam.kel:1:9: 構文エラー: 付近のトークンを確認してください
  [2]

無名関数には返り値の型を注釈できない(付録 A.8)。文法の exp の fn の形は、返り値の型と
エフェクト行を持たない:

  $ cat > fnret.kel <<'KEL'
  > let f = fn(x: Int32): Int32 => x
  > KEL
  $ diktor --type-check fnret.kel
  fnret.kel:1:21: 構文エラー: 付近のトークンを確認してください
  [2]

type class の型パラメータは省略できない(付録 A.8):

  $ cat > classnoparam.kel <<'KEL'
  > type class C { val c: (Int32) => Int32 }
  > KEL
  $ diktor --type-check classnoparam.kel
  classnoparam.kel:1:14: 構文エラー: 付近のトークンを確認してください
  [2]

extern は関数束縛の形だけを持ち、値束縛の形を持たない(付録 A.8):

  $ cat > externval.kel <<'KEL'
  > extern "C" let sqrt: (Float64) => Float64
  > KEL
  $ diktor --type-check externval.kel
  externval.kel:1:20: 構文エラー: 付近のトークンを確認してください
  [2]
