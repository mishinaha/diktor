--dump-ast のゴールデンテストである。構文解析が行う脱糖(第3章)の結果を固定する。
出力が変わったときは dune promote で更新し、差分を必ず目で確認すること。

タプルと引数リストを _item の行にする脱糖(第3章 §3.5)と、t._N の脱糖(第3章 §3.4):

  $ cat > tuple.kel <<'EOF'
  > let t = (1, "a", true)
  > let one = (1,)
  > let grouped = (1)
  > let first = t._0
  > let second = t._1
  > let f = fn(x, y) => x
  > let call = f(1, 2)
  > EOF
  $ diktor --dump-ast tuple.kel
  (dlet
   (binding t = (extend _item 1 (extend _item "a" (extend _item true {})))))
  (dlet (binding one = (extend _item 1 {})))
  (dlet (binding grouped = 1))
  (dlet (binding first = (select _item t)))
  (dlet (binding second = (select _item (restrict _item t))))
  (dlet (binding f = (fn (x y) x)))
  (dlet (binding call = (apply f (extend _item 1 (extend _item 2 {})))))

レコードの演算(フィールドの省略記法、with による更新、extends、フィールドの除去):

  $ cat > record.kel <<'EOF'
  > let r = {x = 1, y = 2}
  > let pan = {x, y}
  > let upd = {r with x = 3}
  > let ext = {z = 4 extends r}
  > let res = r \ x
  > let sel = r.x
  > EOF
  $ diktor --dump-ast record.kel
  (dlet (binding r = (extend x 1 (extend y 2 {}))))
  (dlet (binding pan = (extend x x (extend y y {}))))
  (dlet (binding upd = (update x 3 r)))
  (dlet (binding ext = (extend z 4 r)))
  (dlet (binding res = (restrict x r)))
  (dlet (binding sel = (select x r)))

ヴァリアント(#Foo の引数を 1 つの行にまとめる)と、match とガード:

  $ cat > variant.kel <<'EOF'
  > let v = #Point(1, 2)
  > let e = #Empty
  > let m = v match {
  >   case #Point(x, y) if x == y => x
  >   case _ => 0
  > }
  > EOF
  $ diktor --dump-ast variant.kel
  (dlet (binding v = (#Point (extend _item 1 (extend _item 2 {})))))
  (dlet (binding e = (#Empty {})))
  (dlet
   (binding m =
    (match v (case (#Point (precord (_item= x) (_item= y))) if (== x y) => x)
     (case _ => 0))))

Construct と Apply の区別(パスの最後の要素が大文字で始まるかどうかで決める。第3章 §3.6):

  $ cat > path.kel <<'EOF'
  > let a = Some(1)
  > let b = Cons(tail = Nil)
  > let c = Parser.bind(p, f)
  > let d = Parser.Parser(g)
  > let e = Db.Conn.exec(q)
  > EOF
  $ diktor --dump-ast path.kel
  (dlet (binding a = (construct Some 1)))
  (dlet (binding b = (construct Cons (tail= Nil))))
  (dlet (binding c = (apply Parser.bind (extend _item p (extend _item f {})))))
  (dlet (binding d = (construct Parser.Parser g)))
  (dlet (binding e = (apply Db.Conn.exec (extend _item q {}))))

with の糖衣構文。パターンが _ なら 0 引数の継続、それ以外なら 1 引数の継続を、引数の行の最も内側の RecordEmpty に差し込む(第3章 §3.8):

  $ cat > with.kel <<'EOF'
  > let f = fn() => {
  >   with x = bind(p)
  >   with _ = guard(x)
  >   pure(x)
  > }
  > EOF
  $ diktor --dump-ast with.kel
  (dlet
   (binding f =
    (fn ()
     (apply bind
      (extend _item p
       (extend _item
        (fn (x)
         (apply guard
          (extend _item x
           (extend _item (fn () (apply pure (extend _item x {}))) {})))) {}))))))

ブロックの Let と Seq の入れ子と、let のパターン束縛:

  $ cat > block2.kel <<'EOF'
  > let f = fn() => {
  >   let a = 1
  >   g(a)
  >   let (x, y) = pair()
  >   h(x)
  >   y
  > }
  > EOF
  $ diktor --dump-ast block2.kel
  (dlet
   (binding f =
    (fn ()
     (let (binding a = 1)
      (seq (apply g (extend _item a {}))
       (let (binding (precord (_item= x) (_item= y)) = (apply pair {}))
        (seq (apply h (extend _item x {})) y)))))))

宣言(newtype の略記、effect、class、instance、extern、型エイリアス):

  $ cat > decls.kel <<'EOF'
  > type Pair = (Int32, String)
  > type Req: EffectRow = {ReqId, Logger}
  > newtype UserId(Int32)
  > newtype List[A] = Nil | Cons(A, tail: List[A])
  > effect Console = { read: () => String, write: (String) => Unit }
  > type class Eq[A] {
  >   val eq: (A, A) => Boolean
  > }
  > type instance Eq[Point] {
  >   let eq(a, b) = true
  > }
  > extern "prim" let __int32_add(x: Int32, y: Int32): Int32
  > pub newtype Parser[A]
  > EOF
  $ diktor --dump-ast decls.kel
  (type Pair = (row (_item: Int32) (_item: String)))
  (type Req : EffectRow = (row ReqId Logger))
  (newtype UserId (UserId Int32))
  (newtype List (A) (Nil) (Cons A (tail: (tapp List A))))
  (effect Console (read: (=> () String)) (write: (=> (String) Unit)))
  (class Eq (A) (val eq : (=> (A A) Boolean)))
  (instance Eq (Point) (dlet (binding eq (params a b) = true)))
  (extern "prim" __int32_add (params (pannot x Int32) (pannot y Int32)) :
   Int32)
  (newtype-pub Parser (A))

構文エラー(終了コード 2):

  $ cat > bad.kel <<'EOF'
  > let x = = 1
  > EOF
  $ diktor --dump-ast bad.kel
  bad.kel:1:9: 構文エラー: 付近のトークンを確認してください
  [2]

sample.kel の全文を構文解析できること(コピー元のバージョンは test/sample/README.md に書いてある):

  $ diktor --dump-ast sample/sample.kel | wc -l
  343
  $ diktor --dump-ast sample/sample.kel | sed -n '1,3p'
  (type MyInt = Int32)
  (type Point = (row (x: Float64) (y: Float64)))
  (type Pair = (row (_item: Int32) (_item: String)))

二項演算子は、第7章 §7.2 の 1 つの表から求めたソース上の表記で出力する(第4章 §4.2):

  $ cat > ops.kel <<'KEL'
  > let arith = fn(a, b) => a + b - a * b / a
  > let cmp = fn(a, b) => (a == b, a != b, a < b, a <= b, a > b, a >= b)
  > let bools = fn(p, q) => (p && q, p || q, !p)
  > KEL
  $ diktor --dump-ast ops.kel
  (dlet (binding arith = (fn (a b) (- (+ a b) (/ (* a b) a)))))
  (dlet
   (binding cmp =
    (fn (a b)
     (extend _item (== a b)
      (extend _item (!= a b)
       (extend _item (< a b)
        (extend _item (<= a b)
         (extend _item (> a b) (extend _item (>= a b) {})))))))))
  (dlet
   (binding bools =
    (fn (p q)
     (extend _item (&& p q) (extend _item (|| p q) (extend _item (! p) {}))))))
