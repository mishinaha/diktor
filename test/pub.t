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

@ 省略の pub はエフェクトを起こせない(本体の行は @ {} と同じ閉じた空の行。
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
sample.kel:652-655 と同形 — この形が通ることが H6 の受け入れ条件):

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

注釈の中の矢印にも @ が要る(§13。省略の意味は @ {} に決まっているが、
公開 API では純粋を意図したのか書き忘れたのかを読み手が区別できなければ
ならない。M26 より前の根拠は健全性だった — 中の矢印の省略 @ が推論任せの
行になり、同じ pub 署名・同じ表示型のまま本体の変更だけで呼び出し側が
壊れた(M16 検証)。いまは入れ子の省略 @ は @ {} に確定している):

  $ printf 'pub let apply2(f: () => Unit, x: Int32): Int32 = x\n' > pub11.kel
  $ diktor --type-check pub11.kel
  ! pub11.kel:1:9: 型エラー: pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]
行変数を明示すれば、エフェクトのあるコールバックを取る pub も書ける(こちらが正道。
入れ子の矢印で @ を省略したコールバックは @ {} と読むので、エフェクトのある関数を渡せない):

  $ printf 'pub let apply3[E](f: () => Unit @ E, x: Int32): Int32 @ E = { f(); x }\necholn(show(apply3(fn() => (), 41) + 1))\n' > pub12.kel
  $ diktor pub12.kel
  42

pub let rec の相互再帰(@ 省略)は、どの束縛の本体も閉じた空の行で検査するので通る
(M16 検証。かつては束縛ごとに別の剛定数の行になり、相互呼び出しが単一化できず落ちた):

  $ cat > pub13.kel <<'KEL'
  > pub let rec ping(n: Int32): Int32 = n match { case 0 => 0 case m => pong(m - 1) }
  > and pong(n: Int32): Int32 = n match { case 0 => 1 case m => ping(m - 1) }
  > echoln(show(ping(5)))
  > KEL
  $ diktor pub13.kel
  1

エフェクトつき関数の呼び出しにも pub の規則を名指しで案内する(M16 検証。
かつては一般文言「行型ではありません: ς1」だけだった)。非一般化の
トップレベル束縛(パターン束縛など)を呼ぶ形は、その束縛の行が空に決まって通る:

  $ printf 'pub let f(x: Int32): Int32 = { echoln("hi"); x }\n' > pub14.kel
  $ diktor --type-check pub14.kel
  ! pub14.kel:1:32: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]
handle や run の本体の中で起こしたエフェクトも、pub の規則を名指しして案内する:

  $ printf 'pub let f(): Unit = { echo("a"); () } handle { case print(m) => resume(()) }\n' > pubh.kel
  $ diktor --type-check pubh.kel
  ! pubh.kel:1:23: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]
  $ printf 'pub let g(): Int32 = run h { echo("a"); 1 }\n' > pubr.kel
  $ diktor --type-check pubr.kel
  ! pubr.kel:1:30: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]

  $ cat > pub15.kel <<'KEL'
  > let (helper, k) = (fn(x: Int32) => x, 0)
  > pub let go(n: Int32): Int32 = helper(n)
  > KEL
  $ diktor --type-check pub15.kel
  go : (Int32) => Int32

pub な newtype のフィールドの矢印にも @ が要る(§13 / M26。省略の意味は @ {} に
決まっているが、公開 API では意図と書き忘れを読み分けられなければならない):

  $ printf 'module P { pub newtype Parser[A] = Parser((String) => Option[A]) }\n' > pubnt.kel
  $ diktor --type-check pubnt.kel
  ! pubnt.kel:1:12: 型エラー: pub な newtype のフィールドには完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]
  $ printf 'module P { pub newtype Parser[A] = Parser((String) => Option[A] @ {}) }\n' > pubnt2.kel
  $ diktor --type-check pubnt2.kel
