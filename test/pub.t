pub な宣言に完全な型注釈を要求する検査と、@ を省略した pub な宣言を純粋と読む規則のテストである。

  $ export PATH="$TESTDIR/../_build/install/default/bin:$PATH"

引数か返り値の型注釈が欠けていると拒否する(let rec と extern も同じ規則である):

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

@ を省略した pub な宣言は、エフェクトを起こせない。本体の行は @ {} と同じ、閉じた空の行である。
診断のメッセージは、pub の規則を明記して案内する:

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

@ を省略した pub な宣言は @ {} と読む。呼び出しには使用時に行を開く規則が適用されるので、どの行の文脈からでも
呼べる(sample.kel:654-657 と同じ形である):

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
  Db.query : (String) => Resp @ {}
  handle_req : (String) => Resp @ {ReqId, Logger}

  $ cat > pub5.kel <<'KEL'
  > pub let twice(x: Int32): Int32 = x + x
  > let use[E](): Int32 @ E = twice(21)
  > echoln(show(use()))
  > KEL
  $ diktor pub5.kel
  42

pub の値束縛と pub let rec は、型注釈が完全なら型検査に通る:

  $ cat > pub8.kel <<'KEL'
  > pub let rec fac(n: Int32): Int32 = n match { case 0 => 1 case _ => n * fac(n - 1) }
  > pub let v: Int32 = fac(5)
  > echoln(show(v))
  > KEL
  $ diktor pub8.kel
  120

注釈の中の入れ子の矢印にも @ が必要である(sample.kel の §13、LangSpec §15.2)。
入れ子の矢印で @ を省略した場合の意味は、@ {} に決まっている。
しかし公開 API では、純粋を意図したのか書き忘れたのかを、読者が区別できなければ
ならない。そのため、pub な宣言では入れ子の矢印の @ を省略できず、
省略すると、完全な型注釈がないという型エラーになる:

  $ printf 'pub let apply2(f: () => Unit, x: Int32): Int32 = x\n' > pub11.kel
  $ diktor --type-check pub11.kel
  ! pub11.kel:1:9: 型エラー: pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]
行変数を明示すれば、コールバックを受け取る pub の関数も書ける。エフェクトを起こす関数を受け取るには、
この書き方を使う(入れ子の矢印に @ {} と書いたコールバックには、エフェクトを起こす関数を渡せない):

  $ printf 'pub let apply3[E](f: () => Unit @ E, x: Int32): Int32 @ E = { f(); x }\necholn(show(apply3(fn() => (), 41) + 1))\n' > pub12.kel
  $ diktor pub12.kel
  42

pub let rec の相互再帰で @ を省略した形は、どの束縛の本体も閉じた空の行で検査するので、
相互の呼び出しの行が一致して、型検査に通る:

  $ cat > pub13.kel <<'KEL'
  > pub let rec ping(n: Int32): Int32 = n match { case 0 => 0 case m => pong(m - 1) }
  > and pong(n: Int32): Int32 = n match { case 0 => 1 case m => ping(m - 1) }
  > echoln(show(ping(5)))
  > KEL
  $ diktor pub13.kel
  1

エフェクトを起こす関数の呼び出しで失敗した場合も、pub の規則を明記して案内し、
元の報告(`ラベル Console がありません(行は閉じています)`)を添える。
一般化されないトップレベルの束縛(パターン束縛など)の関数を呼ぶ形は、その束縛の行が空の行に決まるので、
型検査に通る(下の pub15):

  $ printf 'pub let f(x: Int32): Int32 = { echoln("hi"); x }\n' > pub14.kel
  $ diktor --type-check pub14.kel
  ! pub14.kel:1:32: 型エラー: pub な宣言はエフェクトを起こせません(@ を明示するか pub を外してください。元の報告: ラベル Console がありません(行は閉じています))
  [1]
handle や run の本体の中で起こしたエフェクトも、pub の規則を明記して案内する:

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
  go : (Int32) => Int32 @ {}

pub な newtype のフィールドの矢印にも @ が必要である(sample.kel の §13)。省略した場合の意味は @ {} に
決まっているが、公開 API では、意図した省略と書き忘れを読者が区別できなければならない:

  $ printf 'module P { pub newtype Parser[A] = Parser((String) => Option[A]) }\n' > pubnt.kel
  $ diktor --type-check pubnt.kel
  ! pubnt.kel:1:43: 型エラー: pub な newtype のフィールドには完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]
  $ printf 'module P { pub newtype Parser[A] = Parser((String) => Option[A] @ {}) }\n' > pubnt2.kel
  $ diktor --type-check pubnt2.kel

注釈に書いた型エイリアスの本体の矢印にも @ が必要である。型エイリアスは展開して読むので、矢印を
型エイリアスの中に書いても要求は変わらない。診断は、@ のない矢印を本体に書いた型エイリアスの名前を示す:

  $ cat > pubalias.kel <<'KEL'
  > type F = (Int32) => Int32
  > type G = F
  > pub let h(g: G): Int32 = g(1)
  > KEL
  $ diktor --type-check pubalias.kel
  ! pubalias.kel:3:9: 型エラー: pub な宣言には完全な型注釈が必要です(型エイリアス F の本体の矢印に @ がありません)
  [1]
  $ printf 'type F = (Int32) => Int32\npub newtype Box = Box(F)\n' > pubaliasnt.kel
  $ diktor --type-check pubaliasnt.kel
  ! pubaliasnt.kel:2:23: 型エラー: pub な newtype のフィールドには完全な型注釈が必要です(型エイリアス F の本体の矢印に @ がありません)
  [1]

型エイリアスの型引数に書いた矢印は、注釈に直接書いた矢印として扱う。本体の矢印に @ が
あれば型検査に通る。本体で使わないパラメータに渡した型引数の矢印も調べる:

  $ printf 'type G[A] = (A) => Int32 @ {}\npub let h(f: G[(Int32) => Int32]): Int32 = 0\n' > pubaliasarg.kel
  $ diktor --type-check pubaliasarg.kel
  ! pubaliasarg.kel:2:9: 型エラー: pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]
  $ printf 'type G[A] = (A) => Int32 @ {}\npub let h(f: G[Int32]): Int32 = f(1)\n' > pubaliasarg2.kel
  $ diktor --type-check pubaliasarg2.kel
  h : ((Int32) => Int32 @ {}) => Int32 @ {}
  $ printf 'type K[A] = Int32\npub let h(x: K[(Int32) => Int32]): Int32 = x + 1\n' > pubaliasarg3.kel
  $ diktor --type-check pubaliasarg3.kel
  ! pubaliasarg3.kel:2:9: 型エラー: pub な宣言には完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]
  $ printf 'type K[A] = Int32\npub newtype Box = Box(K[(Int32) => Int32])\n' > pubaliasarg4.kel
  $ diktor --type-check pubaliasarg4.kel
  ! pubaliasarg4.kel:2:23: 型エラー: pub な newtype のフィールドには完全な型注釈が必要です(注釈の中の矢印に @ がありません)
  [1]

pubaliasmod では、module M の中の pub let h の注釈の F は M.F を指す。
M.F の本体の矢印には @ があるので、型検査に通る:

  $ cat > pubaliasmod.kel <<'KEL'
  > type F = (Int32) => Int32
  > module M {
  >   type F = (Int32) => Int32 @ {}
  >   pub let h(f: F): Int32 = f(1)
  > }
  > echoln(show(M.h(fn(x) => x + 1)))
  > KEL
  $ diktor pubaliasmod.kel
  2

型エイリアスの本体の名前は、型エイリアスを宣言した位置で解決する(LangSpec §15.1)。
次の 2 つでは、module M の中の pub type G = F の F が M.F を指し、
module の外の pub let h が M.G を使う。
pubaliasmod2 は M.F の矢印に @ があるので、型検査に通る。
pubaliasmod3 は M.F の矢印に @ がないので、外の F に @ があっても拒否する:

  $ printf 'type F = (Int32) => Int32\nmodule M {\n  type F = (Int32) => Int32 @ {}\n  pub type G = F\n}\npub let h(g: M.G): Int32 = g(1)\n' > pubaliasmod2.kel
  $ diktor --type-check pubaliasmod2.kel
  h : ((Int32) => Int32 @ {}) => Int32 @ {}
  $ printf 'type F = (Int32) => Int32 @ {}\nmodule M {\n  type F = (Int32) => Int32\n  pub type G = F\n}\npub let h(g: M.G): Int32 = g(1)\n' > pubaliasmod3.kel
  $ diktor --type-check pubaliasmod3.kel
  ! pubaliasmod3.kel:6:9: 型エラー: pub な宣言には完全な型注釈が必要です(型エイリアス M.F の本体の矢印に @ がありません)
  [1]

import した型エイリアスにも、同じ要求を適用する:

  $ mkdir -p pubaliasimp
  $ printf 'pub type F = (Int32) => Int32\n' > pubaliasimp/lib.kel
  $ printf 'from "./lib" import F\npub let h(f: F): Int32 = f(1)\n' > pubaliasimp/main.kel
  $ diktor --type-check pubaliasimp/main.kel
  ! pubaliasimp/main.kel:2:9: 型エラー: pub な宣言には完全な型注釈が必要です(型エイリアス F の本体の矢印に @ がありません)
  [1]

使う位置から見えない型エイリアスの本体は調べない。可視性の診断を先に出す:

  $ printf 'module M {\n  type F = (Int32) => Int32\n}\npub let h(f: M.F): Int32 = f(1)\n' > pubaliasvis.kel
  $ diktor --type-check pubaliasvis.kel
  ! pubaliasvis.kel:4:14: 型エラー: 型 M.F は module M の外からは参照できません(pub を付けてください)
  [1]

型パラメータは、同じ名前の型エイリアスを隠す:

  $ cat > pubaliastp.kel <<'KEL'
  > type A = (Int32) => Int32
  > pub let idf[A](x: A): A = x
  > type class Desc[T] { val desc: (T) => String }
  > type instance[A: Show] Desc[List[_]] {
  >   let desc(x: List[A]): String = show(x)
  > }
  > echoln(desc(Cons(1i32, Cons(2i32, Nil))))
  > echoln(show(idf(3)))
  > KEL
  $ diktor pubaliastp.kel
  [1, 2]
  3
