pub で @ を省略した宣言の本体は純粋で(LangSpec §13.2)、本体がエフェクトを起こすと
「pub な宣言はエフェクトを起こせません」と報告する。値束縛では、注釈と初期化式の
頭の行どうしの単一化の失敗にこの文言を付ける。関数適用では、呼び出しの位置の行の
尾部が pub で省略した @ の表す本体の行で(run などがその上にラベルを積んだ行を含む)、
呼び出し先が矢印で、失敗が行に由来し、剛定数の漏れではないときにこの文言を付ける。以下のブロックは、
この文言が付く形と付かない形を並べる。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

値束縛の注釈の頭の @ を省略すると、初期化式が返す関数がエフェクトを起こす形は
pub の規則を名指して拒否する(pubvaleff)。入れ子の矢印の行に @ {} と書き、内側の関数が
エフェクトを起こす形(pubvalinner)と、返り値のレコードのフィールドが違う形(pubvalrec)は、
pub の規則を名指さず、「注釈された型を満たしません」で拒否する:

  $ cat > pubvaleff.kel <<'KEL'
  > module M {
  >   pub let g: (Int32) => Int32 = fn(x) => { echoln("a"); x }
  > }
  > KEL
  $ diktor --type-check pubvaleff.kel
  ! pubvaleff.kel:2:11: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]
  $ cat > pubvalinner.kel <<'KEL'
  > module M {
  >   pub let g: (Int32) => (Int32) => Int32 @ {} = fn(x) => fn(y) => { echoln("a"); y }
  > }
  > KEL
  $ diktor --type-check pubvalinner.kel
  ! pubvalinner.kel:2:11: 型エラー: 注釈された型を満たしません(ラベル Console がありません(行は閉じています))
  [1]
  $ cat > pubvalrec.kel <<'KEL'
  > module M {
  >   pub let g: (Int32) => {a: Int32} = fn(x) => {b = x}
  > }
  > KEL
  $ diktor --type-check pubvalrec.kel
  ! pubvalrec.kel:2:11: 型エラー: 注釈された型を満たしません(ラベル a がありません(行は閉じています))
  [1]

pubvalarg は引数のレコードのフィールドが違う形、pubvalvariant は返り値のヴァリアントの
選択肢が違う形で、どちらも「注釈された型を満たしません」で拒否する:

  $ cat > pubvalarg.kel <<'KEL'
  > module M {
  >   pub let g: ({a: Int32}) => Int32 = fn(r: {b: Int32}) => r.b
  > }
  > KEL
  $ diktor --type-check pubvalarg.kel
  ! pubvalarg.kel:2:11: 型エラー: 注釈された型を満たしません(ラベル a がありません(行は閉じています))
  [1]
  $ cat > pubvalvariant.kel <<'KEL'
  > module M {
  >   pub let g: (Int32) => #A | #B = fn(x) => #C
  > }
  > KEL
  $ diktor --type-check pubvalvariant.kel
  ! pubvalvariant.kel:2:11: 型エラー: 注釈された型を満たしません(ラベル C がありません(行は閉じています))
  [1]

返り値のフィールドが違い、初期化式が返す関数がエフェクトも起こす形(pubvalboth)は、
フィールドの失敗を報告する:

  $ cat > pubvalboth.kel <<'KEL'
  > module M {
  >   pub let g: (Int32) => {a: Int32} = fn(x) => { echoln("a"); {b = x} }
  > }
  > KEL
  $ diktor --type-check pubvalboth.kel
  ! pubvalboth.kel:2:11: 型エラー: 注釈された型を満たしません(ラベル a がありません(行は閉じています))
  [1]

let rec の値束縛では、初期化式が返す関数がエフェクトを起こす pubrecvaleff は pub の規則を
名指して拒否する。返り値のフィールドが違う pubrecvalrec は、元の報告だけで拒否する:

  $ cat > pubrecvaleff.kel <<'KEL'
  > module M {
  >   pub let rec g: (Int32) => Int32 = fn(x) => { echoln("a"); x }
  > }
  > KEL
  $ diktor --type-check pubrecvaleff.kel
  ! pubrecvaleff.kel:2:15: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]
  $ cat > pubrecvalrec.kel <<'KEL'
  > module M {
  >   pub let rec g: (Int32) => {a: Int32} = fn(x) => {b = x}
  > }
  > KEL
  $ diktor --type-check pubrecvalrec.kel
  ! pubrecvalrec.kel:2:15: 型エラー: ラベル a がありません(行は閉じています)
  [1]

関数束縛の本体の run の中で、単相のフィールドの関数を呼ぶと、ヒープのラベルが
フィールドの関数の行に入ろうとして、スコープの外に漏れる。pub の付いた pubrunleak も、
pub を外した runleak も、同じ漏れの文言で報告する:

  $ cat > pubrunleak.kel <<'KEL'
  > let idf[A](x: A): A = x
  > module M {
  >   let r = idf({go = fn(u: Int32) => u + 1})
  >   pub let f(): Int32 = run h { r.go(1) }
  > }
  > KEL
  $ diktor --type-check pubrunleak.kel
  idf : (A) => A
  M.r : {go: (Int32) => Int32}
  ! pubrunleak.kel:4:32: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]
  $ sed 's/pub let f/let f/' pubrunleak.kel > runleak.kel
  $ diktor --type-check runleak.kel
  idf : (A) => A
  M.r : {go: (Int32) => Int32}
  ! runleak.kel:4:28: 型エラー: スコープ付きの型 ς1 がスコープの外に漏れています
  [1]

run の本体で、Console を起こす引数の関数を呼ぶ形(pubruneff)は、pub の規則を名指して拒否する:

  $ cat > pubruneff.kel <<'KEL'
  > module M {
  >   pub let f(g: () => Int32 @ {Console}): Int32 = run h { g() }
  > }
  > KEL
  $ diktor --type-check pubruneff.kel
  ! pubruneff.kel:2:58: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]

呼び出し先が型パラメータ F の値のとき、失敗は行ではなく呼び出し先の型による。
pub で @ を省略した pubrigidcall は pub の規則を名指さず、@ {} と書いた purerigidcall は
行が空の位置の案内を添えない:

  $ cat > pubrigidcall.kel <<'KEL'
  > module M {
  >   pub let f[F](g: F): Int32 = g()
  > }
  > KEL
  $ diktor --type-check pubrigidcall.kel
  ! pubrigidcall.kel:2:31: 型エラー: スコープ付きの型が一致しません: ς1 と _A => _B @ {}
  [1]
  $ cat > purerigidcall.kel <<'KEL'
  > let f[F](g: F): Int32 @ {} = g()
  > KEL
  $ diktor --type-check purerigidcall.kel
  ! purerigidcall.kel:1:30: 型エラー: スコープ付きの型が一致しません: ς1 と _A => _B @ {}
  [1]
