pub の完全注釈検査と「@ 省略 = 純粋」(M16 / H6、D44)。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

注釈が欠けていると拒否(引数・返り値。let rec / extern も同じ規則):

  $ printf 'pub let f(x) = x\n' > pub1.kel
  $ diktor --type-check pub1.kel
  ! pub1.kel:1:9: 型エラー: pub な宣言には完全な型注釈が必要です(引数に型注釈がありません)
  [1]
  $ printf 'pub let f(x: Int32) = x\n' > pub2.kel
  $ diktor --type-check pub2.kel
  ! pub2.kel:1:9: 型エラー: pub な宣言には完全な型注釈が必要です(返り値の型注釈がありません)
  [1]
  $ printf 'pub extern "prim" let myp(x: Int32)\n' > pub7.kel
  $ diktor --type-check pub7.kel
  ! pub7.kel:1:1: 型エラー: pub な宣言には完全な型注釈が必要です(返り値の型注釈がありません)
  [1]

@ 省略の pub はエフェクトを起こせない(本体には Rigid の行が見える。
文言は pub の規則を名指しで案内する):

  $ cat > pub3.kel <<'KEL'
  > effect Logger = { log: (String) => Unit }
  > pub let f(x: Int32): Int32 = { perform log("no"); x }
  > KEL
  $ diktor --type-check pub3.kel
  ! pub3.kel:2:32: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください)
  [1]
  $ cat > pub9.kel <<'KEL'
  > effect Logger = { log: (String) => Unit }
  > pub let rec f(n: Int32): Int32 = { perform log("x"); n }
  > KEL
  $ diktor --type-check pub9.kel
  ! pub9.kel:2:36: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください)
  [1]

@ 省略の pub はどんな行の文脈からでも呼べる(公開スキーマは Generic。
sample.kel:451 と同形 — この形が通ることが H6 の受け入れ条件):

  $ cat > pub4.kel <<'KEL'
  > newtype Resp = R(String)
  > effect ReqId  = { req_id: () => String }
  > effect Logger = { log: (String) => Unit }
  > module Db { pub let query(q: String): Resp = ??? }
  > pub let handle_req(q: String): Resp @ {ReqId, Logger} = {
  >   perform log("handling " + perform req_id())
  >   Db.query(q)
  > }
  > KEL
  $ diktor --type-check pub4.kel
  Db.query : (String) => Resp
  handle_req : (String) => Resp @ {ReqId, Logger extends R1}

  $ cat > pub5.kel <<'KEL'
  > pub let twice(x: Int32): Int32 = x + x
  > let use[E](): Int32 @ E = twice(21)
  > echoln(show(use()))
  > KEL
  $ diktor pub5.kel
  42

pub の値束縛と pub let rec(注釈が完全なら通る):

  $ cat > pub8.kel <<'KEL'
  > pub let rec fac(n: Int32): Int32 = n match { case 0 => 1 case _ => n * fac(n - 1) }
  > pub let v: Int32 = fac(5)
  > echoln(show(v))
  > KEL
  $ diktor pub8.kel
  120
