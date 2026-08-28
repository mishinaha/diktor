sample.kel 全体回帰(計画 §9.2 / M9-M10 完了条件)。
stubs.kel を前置した無改変 sample.kel の全文が --type-check を通り(警告ゼロ)、
トップレベル式文(handle と capture)が期待どおり評価される。
変更時は dune promote で更新し、必ず目視レビューすること。

  $ diktor --type-check sample/stubs.kel sample/sample.kel
  Db.query : (String) => Resp
  sqrt : (Float64) => Float64
  each : (List[A], (A) => {}) => {}
  heavy : (Int32) => Int32
  audit_log : ({query: String}, Resp) => {}
  handle_client : (Conn) => {} @ {Async extends R1}
  a : Int32
  b : Int64
  c : Int64
  d : Int32
  e : Float64
  sum_xy : ({x: Float64, y: Float64 extends R1}) => Float64
  with_z : ({extends R1}) => {z: Float64 extends R1}
  move_x : ({x: Float64 extends R1}, Float64) => {x: Float64 extends R1}
  outer_x : () => Float64
  make_point : (Float64, Float64) => {x: Float64, y: Float64}
  swap : ((A, B)) => (B, A)
  fst : ({_item: A extends R1}) => A
  describe : (#Even | #Odd | R1) => String
  report : (#NotFound(String) | #Denied(String) | #Syntax((Int32, Int32))) => String
  some_one : () => Option[Int32]
  get_or : (Option[A], A) => A
  list_length : (List[A]) => Int32
  twice_sum_xy : ({x: Float64, y: Float64}) => Float64
  dist : ({x: Float64, y: Float64}) => Float64
  head_and_rest : ({_item: A extends R1}) => A
  inc_all : (List[Int32]) => List[Int32]
  count_if : (List[A], (A) => Boolean) => Int32
  is_even : (Int32) => Boolean
  is_odd : (Int32) => Boolean
  fma : [A: Add + Mul] (A, A, A) => A
  same_point : ({x: Float64, y: Float64}, {x: Float64, y: Float64}) => Boolean
  same_pair : ((Int32, String), (Int32, String)) => Boolean
  user_names : (List[{id: String, name: String}]) => List[String] @ {Print extends R1}
  println : (String) => {} @ {Print extends R1}
  _ : {}
  capture : (() => A @ {Print extends R1}) => {value: A, output: String}
  try_ : (() => A @ {Fail extends R1}) => #Ok(A) | #Err(String)
  with_file : (String, () => A @ {File extends R1}) => A
  copy : (String, String) => {} @ {Console extends R1}
  Parser.bind : (Parser.Parser[A], (A) => Parser.Parser[B]) => Parser.Parser[B]
  Parser.pure : (A) => Parser.Parser[A]
  Parser.token : (String) => Parser.Parser[String]
  parens : () => Parser.Parser[(String, String)]
  handle_request : ({query: String}) => Resp @ {ReqId, Logger, Tracer, Db, Async extends R1}
  _ : {}
  sum : (Array[Int32]) => Int32
  par_map : (Array[A], (A) => B) => Array[B]
  par : (() => A, () => B) => (A, B)
  scope : (() => A @ {Nursery, Async extends R1}) => A @ {Async extends R1}
  serve : (List[Conn]) => {} @ {Async extends R1}
  with_timeout : (Int64, () => A @ {Deadline extends R1}) => Option[A] @ {Async extends R1}
  handle_audited : ({query: String}) => Resp @ {ReqId, Logger, Tracer, Db, Background, Async extends R1}
  crunch : (Array[Int32]) => Int32 @ {Async extends R1}
  channel : (Int32) => Chan[A]
  send : (Chan[A], A) => {} @ {Async extends R1}
  recv : (Chan[A]) => A @ {Async extends R1}
  sin : (Float64) => Float64
  sqlite_step : (Stmt) => Int32 @ {Blocking extends R1}
  pinned : (() => A @ {Blocking extends R1}) => A
  BigInt.parse : (String) => BigInt.BigInt
  BigInt.normalize : (BigInt.BigInt) => BigInt.BigInt
  big_sum : () => BigInt.BigInt

実行(トップレベル式文: sample.kel:357 の handle と :454 の capture):

  $ diktor sample/stubs.kel sample/sample.kel
  test
  test
