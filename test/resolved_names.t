型検査が解決したトップレベルの値の実体を、評価器がそのまま使う。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

--prelude で差し替えたプレリュードの module の中の非修飾名 foo は、
利用者のプログラムに同名のトップレベルの値 foo があっても、module の foo を指す。
型検査は r を Int32 として通し、実行も module の foo の値 1 から r = 2 を作る:

  $ cat > pmpre.kel <<'KEL'
  > type Unit = {}
  > effect Console = { write: (String) => Unit }
  > let echoln(message: String): Unit @ Console = perform write(message + "\n")
  > module PM {
  >   let foo: Int32 = 1
  >   pub let get(): Int32 = foo
  > }
  > KEL
  $ cat > pmuse.kel <<'KEL'
  > let foo: String = "user"
  > let r: Int32 = PM.get() + 1
  > echoln(show(r))
  > echoln(foo)
  > KEL
  $ diktor --prelude pmpre.kel --type-check pmuse.kel
  foo : String
  r : Int32
  _ : {}
  _ : {}
  $ diktor --prelude pmpre.kel pmuse.kel
  2
  user

同名の再束縛では、それより前に定義した関数は前の束縛を、後に定義した関数は新しい束縛を指す:

  $ cat > rebind.kel <<'KEL'
  > let x: Int32 = 1
  > let f(): Int32 = x
  > let x: Int32 = 2
  > let g(): Int32 = x
  > echoln(show(f()))
  > echoln(show(g()))
  > KEL
  $ diktor rebind.kel
  1
  2

前方参照の署名は、最初に宣言した同名の束縛を指す。
後で同名を再束縛しても、前方参照した関数は最初の束縛を呼び続ける:

  $ cat > fwdrebind.kel <<'KEL'
  > let g(): Int32 @ Console = z()
  > let z(): Int32 @ Console = 1
  > let z(): Int32 @ Console = 2
  > echoln(show(g()))
  > echoln(show(z()))
  > KEL
  $ diktor fwdrebind.kel
  1
  2

クラスメソッドと同名のトップレベルの束縛は、それより後の非修飾名だけを覆う。
修飾名はメソッドを指したままである:

  $ cat > methshadow.kel <<'KEL'
  > type class C[A] { val cm: (A) => Int32 }
  > type instance C[Int32] { let cm(x: Int32): Int32 = x + 1 }
  > let a(): Int32 = cm(1)
  > let cm(x: Int32): Int32 = 100
  > let b(): Int32 = cm(1)
  > let c(): Int32 = C.cm(1)
  > echoln(show(a()))
  > echoln(show(b()))
  > echoln(show(c()))
  > KEL
  $ diktor methshadow.kel
  2
  100
  2

定義より前に評価される位置から前方参照すると、実行時エラーになる:

  $ cat > early.kel <<'KEL'
  > let early(): Int32 @ Console = late()
  > let v: Int32 = early()
  > let late(): Int32 @ Console = 3
  > KEL
  $ diktor early.kel
  実行時エラー: 未束縛の変数: late
  [3]
