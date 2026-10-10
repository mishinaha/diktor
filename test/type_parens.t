型の位置の括弧(LangSpec §3.1、§8)。カンマの無い (A) はグループ化で、
1 要素タプル型は (A,) と書く。式の (e) とパターンの (p) と同じ規則である。

  $ cat > group.kel <<'EOF'
  > let a: (Int32) = 1
  > let b: (Int32,) = (1,)
  > let c: ((Int32, String)) = (1, "x")
  > let d: (((Int32))) = 2
  > let e: (Int32, (String)) = (1, "y")
  > let v: #Foo((Int32)) = #Foo(1)
  > EOF
  $ diktor --type-check group.kel
  a : Int32
  b : (Int32,)
  c : (Int32, String)
  d : Int32
  e : (Int32, String)
  v : #Foo(Int32)

(A) を 1 要素タプルのつもりで書いた注釈は、要素の型そのものになる:

  $ echo 'let f(t: (Int32)): Int32 = t._0' > tuple1.kel
  $ diktor --type-check tuple1.kel
  ! tuple1.kel:1:28: 型エラー: 型が一致しません: Int32 と {_item: _A extends _R1}
  [1]

@ は最も内側の矢印に付く。外側の矢印に @ を書くときは、内側の矢印を括弧で囲む。
関数束縛でも、返り値の矢印を括弧で囲めば、その後ろの @ は関数自身の行になる。
表示も、外側の矢印に行を表示するときは内側の矢印を括弧で囲む:

  $ cat > outer.kel <<'EOF'
  > let inner(x: Int32): (Int32) => Int32 @ {} = fn(y) => x + y
  > let outer(x: Int32): ((Int32) => Int32) @ Console = { echoln("outer"); fn(y) => x + y }
  > let both(x: Int32): ((Int32) => Int32 @ Console) @ Console = { echoln("both"); fn(y) => { echoln("in"); x + y } }
  > type Curried = (Int32) => ((Int32) => Int32) @ Console
  > EOF
  $ diktor --type-check outer.kel
  inner : (Int32) => (Int32) => Int32 @ {}
  outer : (Int32) => ((Int32) => Int32 @ {}) @ {Console extends R1}
  both : (Int32) => ((Int32) => Int32 @ {Console}) @ {Console extends R1}

括弧で囲んだ矢印は、型適用の頭やヴァリアント和の要素にはならない:

  $ echo 'let x: ((Int32) => Int32) | #A = ???' > grpunion.kel
  $ diktor --type-check grpunion.kel
  ! grpunion.kel:1:8: 型エラー: ヴァリアント和の要素になれない型です: (Int32) => Int32 @ {}
  [1]
