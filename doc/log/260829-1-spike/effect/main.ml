(* ============================================================
   Keleut / Diktor 実装計画 §8.4 エフェクトハンドラ設計の実証 spike
   OCaml 5.2.1 / Effect.Deep
   ============================================================ *)

(* ---------- 値表現(計画 §8.2 の縮小版) ---------- *)
type value =
  | VUnit
  | VInt of int
  | VStr of string
  | VRec of (string * value) list
  | VVariant of string * value

let rec show = function
  | VUnit -> "()"
  | VInt n -> string_of_int n
  | VStr s -> "\"" ^ String.escaped s ^ "\""
  | VRec fs ->
      "{" ^ String.concat ", " (List.map (fun (l, v) -> l ^ " = " ^ show v) fs) ^ "}"
  | VVariant (l, v) -> "#" ^ l ^ "(" ^ show v ^ ")"

(* ---------- 計画 §8.4 の実装プロトコル ---------- *)
type _ Effect.t += Op : string * value list -> value Effect.t

exception Unwind of int * value   (* ハンドラインスタンス id * 保留中の節の値 *)
exception Keleut_error of string  (* ??? ホール / 実行時エラー相当 *)
exception Resume_twice_guard

(* ---------- ログ ---------- *)
let log_buf = Buffer.create 256
let log fmt = Printf.ksprintf (fun s -> Buffer.add_string log_buf (s ^ "\n")) fmt
let take_log () = let s = Buffer.contents log_buf in Buffer.clear log_buf; s

let inst_counter = ref 0
let new_inst () = incr inst_counter; !inst_counter

type op_clause = value list -> (value -> value) -> value

(* -----------------------------------------------------------
   handle: 計画 §8.4 のプロトコル + 「節が例外で異常脱出したとき
   捨てた継続を discontinue する」修正を入れた版
   ----------------------------------------------------------- *)
let handle_gen ~inst ~name ~(ops : (string * op_clause) list) ?ret ?cancel
    ~(guard_resume : bool) ~(protect_clause : bool) (body : unit -> value) : value =
  let open Effect.Deep in
  match_with body ()
    { retc = (fun v -> match ret with None -> v | Some f -> f v)
    ; exnc =
        (fun e ->
          match e with
          | Unwind (i, v) when i = inst ->
              (* 自分が継続を捨てたことによる正常完了。cancel は走らせない *)
              v
          | _ ->
              (match cancel with
               | None -> ()
               | Some c -> (
                   log "    [%s] cancel 節を実行" name;
                   try c () with
                   | e' -> log "    [%s] cancel 節の例外を抑制: %s" name (Printexc.to_string e')));
              raise e)
    ; effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Op (opname, args) when List.mem_assoc opname ops ->
              Some
                (fun (k : (a, value) continuation) ->
                  let f = List.assoc opname ops in
                  let used = ref false in
                  let resume v =
                    if guard_resume && !used then raise Resume_twice_guard;
                    used := true;
                    continue k v
                  in
                  if protect_clause then (
                    match f args resume with
                    | result ->
                        if !used then result
                        else discontinue k (Unwind (inst, result))
                    | exception e ->
                        if !used then raise e
                        else (
                          log "    [%s] 節が例外脱出 → 捨てた継続を discontinue" name;
                          discontinue k e))
                  else
                    let result = f args resume in
                    if !used then result else discontinue k (Unwind (inst, result)))
          | _ -> None)
    }

let handle ~name ~ops ?ret ?cancel body =
  handle_gen ~inst:(new_inst ()) ~name ~ops ?ret ?cancel ~guard_resume:false
    ~protect_clause:true body

(* 計画の文面どおり(節の例外を保護しない)版 *)
let _handle_naive ~name ~ops ?ret ?cancel body =
  handle_gen ~inst:(new_inst ()) ~name ~ops ?ret ?cancel ~guard_resume:false
    ~protect_clause:false body

(* inst を AST ノード単位で固定した場合の版(同一ハンドラの入れ子で誤動作するか) *)
let handle_fixed_inst ~inst ~name ~ops ?ret ?cancel body =
  handle_gen ~inst ~name ~ops ?ret ?cancel ~guard_resume:false ~protect_clause:true body

(* ---------- Keleut 側の関数(sample.kel を直訳) ---------- *)
let perform_op name args = Effect.perform (Op (name, args))
let println s = ignore (perform_op "print" [ VStr (s ^ "\n") ])
let throw s = perform_op "throw" [ VStr s ]

let arg1_str = function [ VStr s ] -> s | _ -> failwith "arity"

(* capture (sample.kel:364-371) *)
let capture body =
  handle ~name:"capture"
    ~ops:
      [ ( "print",
          fun args resume ->
            let msg = arg1_str args in
            match resume VUnit with
            | VRec [ ("value", v); ("output", VStr o) ] ->
                VRec [ ("value", v); ("output", VStr (msg ^ o)) ]
            | other -> failwith ("capture: unexpected " ^ show other) ) ]
    ~ret:(fun x -> VRec [ ("value", x); ("output", VStr "") ])
    body

(* try_ (sample.kel:377-383) *)
let try_ ?(h = handle) body =
  h ~name:"try_"
    ~ops:[ ("throw", fun args _resume -> VVariant ("Err", VStr (arg1_str args))) ]
    ~ret:(fun x -> VVariant ("Ok", x))
    body

(* with_file (sample.kel:395-408) *)
let open_count = ref 0

let with_file ?(h = handle) ?(cancel_body = fun _path -> ()) path body =
  incr open_count;
  let fh = !open_count in
  log "  __open(%s) -> h%d" path fh;
  let close () = log "  __close(%s / h%d)" path fh in
  h
    ~name:("with_file " ^ path)
    ~ops:
      [ ("read", (fun _ resume -> resume (VStr ("contents of " ^ path))));
        ( "write",
          fun args resume ->
            log "  __write(h%d, %S)" fh (arg1_str args);
            resume VUnit ) ]
    ~ret:(fun x -> close (); x)
    ~cancel:(fun () -> close (); cancel_body path)
    body

(* ---------- テスト駆動 ---------- *)
let section n title = Printf.printf "\n===== TEST %s: %s =====\n" n title
let out fmt = Printf.printf fmt

let run_catch f =
  match f () with
  | v -> Printf.printf "結果: %s\n" (show v)
  | exception e -> Printf.printf "例外で脱出: %s\n" (Printexc.to_string e)

let () = Printexc.register_printer (function
  | Unwind (i, v) -> Some (Printf.sprintf "Unwind(%d, %s)" i (show v))
  | Keleut_error s -> Some (Printf.sprintf "Keleut_error(%s)" s)
  | Effect.Unhandled (Op (n, _)) -> Some (Printf.sprintf "Effect.Unhandled(Op %s)" n)
  | _ -> None)

(* === 1. capture === *)
let test1 () =
  section "1" "capture: resume の返り値 = handle 式全体の値";
  let v = capture (fun () -> println "a"; println "b"; VInt 42) in
  out "結果: %s\n" (show v);
  out "期待: {value = 42, output = \"a\\nb\\n\"}\n";
  out "一致: %b\n"
    (v = VRec [ ("value", VInt 42); ("output", VStr "a\nb\n") ])

(* === 2. try_ === *)
let test2 () =
  section "2" "try_: resume を呼ばず節を抜ける → 自動巻き戻し";
  out "正常系: ";
  run_catch (fun () -> try_ (fun () -> VInt 7));
  out "異常系: ";
  run_catch (fun () -> try_ (fun () -> ignore (throw "boom"); VInt 7));
  out "巻き戻し後に後続が実行されないこと: ";
  run_catch (fun () ->
      try_ (fun () ->
          ignore (throw "boom");
          log "  !!! これは実行されてはいけない !!!";
          VInt 7));
  print_string (take_log ())

(* === 3. with_file 2枚重ね + throw → close が LIFO === *)
let test3 () =
  section "3" "with_file 2枚重ね、内側で throw → close の LIFO 順";
  let v =
    try_ (fun () ->
        with_file "outer.txt" (fun () ->
            with_file "inner.txt" (fun () ->
                ignore (perform_op "write" [ VStr "hello" ]);
                ignore (throw "boom");
                VInt 0)))
  in
  print_string (take_log ());
  out "結果: %s\n" (show v);
  section "3b" "with_file 2枚重ね、正常終了 → close は return 節で LIFO";
  let v2 =
    try_ (fun () ->
        with_file "outer.txt" (fun () ->
            with_file "inner.txt" (fun () ->
                ignore (perform_op "read" []);
                VInt 99)))
  in
  print_string (take_log ());
  out "結果: %s\n" (show v2)

(* === 4a. resume 二重呼び出し === *)
let test4a () =
  section "4a" "resume 二重呼び出し → Continuation_already_resumed";
  let body () =
    handle ~name:"twice"
      ~ops:
        [ ( "print",
            fun _args resume ->
              let _ = resume VUnit in
              let _ = resume VUnit in
              VUnit ) ]
      (fun () -> println "x"; VInt 1)
  in
  run_catch body

(* === 4b. 節が例外脱出したとき捨てた継続が discontinue されるか === *)
let test4b () =
  section "4b" "節が例外脱出 → 捨てた継続の cancel が走るか(修正版 vs 計画どおりの版)";
  let scenario protect =
    (* Fail ハンドラの節が ??? に到達して例外脱出する。
       継続の中には with_file が居るので、close が走らないと資源が漏れる *)
    let failing_handler body =
      handle_gen ~inst:(new_inst ()) ~name:"failing"
        ~ops:[ ("throw", fun _ _resume -> raise (Keleut_error "??? に到達")) ]
        ~guard_resume:false ~protect_clause:protect body
    in
    try failing_handler (fun () ->
            with_file "resource.txt" (fun () -> ignore (throw "boom"); VInt 0))
    with e ->
      log "  最外周が捕捉: %s" (Printexc.to_string e);
      VUnit
  in
  out "--- 修正版(節を try で包み discontinue) ---\n";
  ignore (scenario true);
  print_string (take_log ());
  out "--- 計画の文面どおり(包まない) ---\n";
  ignore (scenario false);
  print_string (take_log ())

(* === 4c. handler 自身の cancel は effc から raise すると走らない === *)
let test4c () =
  section "4c" "節が例外脱出したとき、そのハンドラ自身の cancel 節が走るか";
  let scenario protect =
    let failing_handler body =
      handle_gen ~inst:(new_inst ()) ~name:"failing"
        ~ops:[ ("throw", fun _ _resume -> raise (Keleut_error "??? に到達")) ]
        ~cancel:(fun () -> log "  ★ failing 自身の cancel が走った")
        ~guard_resume:false ~protect_clause:protect body
    in
    try failing_handler (fun () -> ignore (throw "boom"); VInt 0)
    with e -> log "  最外周が捕捉: %s" (Printexc.to_string e); VUnit
  in
  out "--- 修正版(discontinue する) ---\n";
  ignore (scenario true);
  print_string (take_log ());
  out "--- 計画の文面どおり(effc から素の raise) ---\n";
  ignore (scenario false);
  print_string (take_log ())

(* === 5. ネストした handle: 最内一致 === *)
let test5 () =
  section "5" "同一操作を扱うハンドラの入れ子 → 最内が捕まえる";
  let tag t body =
    handle ~name:("tag " ^ t)
      ~ops:
        [ ( "print",
            fun args resume ->
              log "  [%s] print %S" t (arg1_str args);
              resume VUnit ) ]
      body
  in
  let v = tag "outer" (fun () -> tag "inner" (fun () -> println "hello"; VInt 5)) in
  print_string (take_log ());
  out "結果: %s\n" (show v);
  out "--- 内側が扱わない操作は外へ抜けるか ---\n";
  let tag2 t body =
    handle ~name:("tag " ^ t)
      ~ops:
        [ ( "print",
            fun args resume ->
              log "  [%s] print %S" t (arg1_str args);
              resume VUnit ) ]
      body
  in
  let inner_only body =
    handle ~name:"only-throw"
      ~ops:[ ("throw", fun args _ -> VVariant ("Err", VStr (arg1_str args))) ]
      body
  in
  let v2 = tag2 "outer" (fun () -> inner_only (fun () -> println "via outer"; VInt 6)) in
  print_string (take_log ());
  out "結果: %s\n" (show v2)

(* === 6. inst が AST ノード単位だと誤動作するか === *)
let test6 () =
  section "6" "Unwind の inst をハンドラ活性化ごとに採番する必要があるか";
  (* 同じ AST ノード(= 同じ inst)のハンドラを 2 枚重ね、外側が継続を捨てる *)
  let mk inst tagname body =
    handle_fixed_inst ~inst ~name:tagname
      ~ops:
        [ ( "throw",
            fun args _resume ->
              log "  [%s] throw 節: 継続を捨てる" tagname;
              VVariant ("Err", VStr (arg1_str args)) ) ]
      ~ret:(fun x -> VVariant ("Ok", x))
      body
  in
  (* 外側の throw を出したいので、内側は別の操作しか扱わないようにする *)
  let mk_inner inst tagname body =
    handle_fixed_inst ~inst ~name:tagname
      ~ops:[ ("other", fun _ resume -> resume VUnit) ]
      ~ret:(fun x -> VVariant ("Ok", x))
      body
  in
  out "--- inst を共有(AST ノード単位)した場合 ---\n";
  let v =
    mk 9999 "H(outer)" (fun () ->
        mk_inner 9999 "H(inner)" (fun () ->
            ignore (throw "boom");
            VInt 0))
  in
  print_string (take_log ());
  out "結果: %s   (期待 #Err(\"boom\"), 内側が横取りすると #Ok(#Err(...)) 等になる)\n" (show v);
  out "--- inst を活性化ごとに採番した場合 ---\n";
  let v2 =
    mk (new_inst ()) "H(outer)" (fun () ->
        mk_inner (new_inst ()) "H(inner)" (fun () ->
            ignore (throw "boom");
            VInt 0))
  in
  print_string (take_log ());
  out "結果: %s\n" (show v2)

(* === 7. cancel 節の実行文脈: 外側ハンドラが有効か / 巻き戻し中のハンドラが再入するか === *)
let logger body =
  handle ~name:"logger"
    ~ops:
      [ ( "print",
          fun args resume ->
            log "  [logger] %s" (String.trim (arg1_str args));
            resume VUnit ) ]
    body

let test7a () =
  section "7a" "cancel 節から、さらに外側のハンドラの操作を perform";
  let v =
    logger (fun () ->
        try_ (fun () ->
            with_file "a.txt"
              ~cancel_body:(fun p -> println ("cancel 中に print: " ^ p))
              (fun () -> ignore (throw "boom"); VInt 0)))
  in
  print_string (take_log ());
  out "結果: %s\n" (show v)

let test7b () =
  section "7b" "cancel 節から、いま巻き戻しを起こしている当のハンドラの操作を perform";
  let n = ref 0 in
  let v2 =
    try
      logger (fun () ->
          try_ (fun () ->
              with_file "b.txt"
                ~cancel_body:(fun _ ->
                  incr n;
                  log "  cancel 中に throw を perform する (%d 回目)" !n;
                  if !n > 5 then (log "  ...5回で打ち切り(ループしている)"; raise Exit);
                  ignore (throw "second"))
                (fun () -> ignore (throw "boom"); VInt 0)))
    with e -> log "  例外脱出: %s" (Printexc.to_string e); VUnit
  in
  print_string (take_log ());
  out "結果: %s\n" (show v2)

(* === 8. 未処理エフェクト === *)
let test8 () =
  section "8" "Effect.Unhandled の挙動";
  (match perform_op "nobody" [] with
   | v -> out "結果: %s\n" (show v)
   | exception e -> out "1) ハンドラ皆無: %s\n" (Printexc.to_string e));
  (* ハンドラはあるが effc が None を返す場合 *)
  (match
     with_file "c.txt" (fun () -> perform_op "nobody" [])
   with
   | v -> out "結果: %s\n" (show v)
   | exception e -> out "2) 無関係なハンドラの中: %s\n" (Printexc.to_string e));
  print_string (take_log ());
  out "   (cancel 節が走ったか上のログで確認)\n";
  (* Unhandled から操作名を取り出せるか *)
  (try ignore (perform_op "nobody" [ VInt 1 ]) with
   | Effect.Unhandled (Op (n, args)) ->
       out "3) 操作名の取り出し: op=%s args=[%s]\n" n
         (String.concat "; " (List.map show args))
   | e -> out "3) 取り出せず: %s\n" (Printexc.to_string e))

(* === 9. スタック消費(末尾でない resume) === *)
let test9 () =
  section "9" "末尾でない resume のスタック消費(§8.4「既知の限界」)";
  (* 非末尾 resume: 節が resume の後に仕事をする(capture と同じ形、O(1) 版) *)
  let counting n =
    handle ~name:"counting"
      ~ops:
        [ ( "print",
            fun _args resume ->
              match resume VUnit with
              | VInt m -> VInt (m + 1)
              | v -> v ) ]
      ~ret:(fun _ -> VInt 0)
      (fun () ->
        for _ = 1 to n do println "x" done;
        VUnit)
  in
  (* 末尾 resume: 節の末尾が resume(e) *)
  let tailing n =
    handle ~name:"tailing"
      ~ops:[ ("print", fun _args resume -> resume VUnit) ]
      ~ret:(fun _ -> VInt 0)
      (fun () ->
        for _ = 1 to n do println "x" done;
        VUnit)
  in
  let attempt label f n =
    let t0 = Unix.gettimeofday () in
    match f n with
    | VInt d -> out "  %-12s n=%-9d OK (%d) %.2fs\n" label n d (Unix.gettimeofday () -. t0)
    | _ -> out "  %-12s n=%-9d shape\n" label n
    | exception Stack_overflow -> out "  %-12s n=%-9d Stack_overflow\n" label n
    | exception e -> out "  %-12s n=%-9d %s\n" label n (Printexc.to_string e)
  in
  List.iter (attempt "非末尾resume" counting) [ 1_000; 100_000; 1_000_000; 10_000_000 ];
  List.iter (attempt "末尾resume" tailing) [ 1_000; 100_000; 1_000_000; 10_000_000 ]

(* === 10. 深い再帰: ハンドラ本体(fiber スタック)の伸長 === *)
let test10 () =
  section "10" "fiber の中での深い非末尾再帰(fiber スタックは伸びるか)";
  let rec depth n = if n = 0 then 0 else 1 + depth (n - 1) in
  let attempt n =
    match
      handle ~name:"deep" ~ops:[ ("print", fun _ r -> r VUnit) ]
        (fun () -> VInt (depth n))
    with
    | VInt d -> out "  depth=%-9d OK (%d)\n" n d
    | _ -> ()
    | exception Stack_overflow -> out "  depth=%-9d Stack_overflow\n" n
  in
  List.iter attempt [ 100_000; 1_000_000; 10_000_000 ]

(* === 11. 小さな事実確認 === *)
let test11 () =
  section "11" "小さな事実確認";
  let chk name f =
    match f () with
    | s -> out "  %-42s => %s\n" name s
    | exception e -> out "  %-42s => 例外 %s\n" name (Printexc.to_string e)
  in
  chk "Int64.of_string \"0xFFFFFFFFFFFFFFFF\"" (fun () ->
      Int64.to_string (Int64.of_string "0xFFFFFFFFFFFFFFFF"));
  chk "Int64.of_string \"18446744073709551615\"" (fun () ->
      Int64.to_string (Int64.of_string "18446744073709551615"));
  chk "Int64.of_string \"9223372036854775807\"" (fun () ->
      Int64.to_string (Int64.of_string "9223372036854775807"));
  chk "Int64.of_string \"9223372036854775808\"" (fun () ->
      Int64.to_string (Int64.of_string "9223372036854775808"));
  chk "Int64.of_string \"0b1010_1010\"" (fun () ->
      Int64.to_string (Int64.of_string "0b1010_1010"));
  chk "Int64.of_string \"0o777\"" (fun () -> Int64.to_string (Int64.of_string "0o777"));
  chk "Int64.of_string \"1_000_000\"" (fun () ->
      Int64.to_string (Int64.of_string "1_000_000"));
  chk "Int64.of_string \"-0x8000000000000000\"" (fun () ->
      Int64.to_string (Int64.of_string "-0x8000000000000000"));
  chk "Int32.of_string \"0xFFFFFFFF\"" (fun () ->
      Int32.to_string (Int32.of_string "0xFFFFFFFF"));
  chk "Int32.of_string \"4294967295\"" (fun () ->
      Int32.to_string (Int32.of_string "4294967295"));
  chk "Int32.of_string \"2147483648\"" (fun () ->
      Int32.to_string (Int32.of_string "2147483648"));
  chk "float_of_string \"1_000.5\"" (fun () ->
      string_of_float (float_of_string "1_000.5"));
  chk "float_of_string \"1e10\"" (fun () -> string_of_float (float_of_string "1e10"));
  chk "float_of_string \"0x1p3\"" (fun () -> string_of_float (float_of_string "0x1p3"));
  chk "float_of_string \"1.\"" (fun () -> string_of_float (float_of_string "1."));
  chk "Int64.of_string \"010\" (8進の罠)" (fun () ->
      Int64.to_string (Int64.of_string "010"));
  chk "Buffer.add_utf_8_uchar 存在確認" (fun () ->
      let b = Buffer.create 8 in
      Buffer.add_utf_8_uchar b (Uchar.of_int 0x3042);
      Buffer.add_utf_8_uchar b (Uchar.of_int 0x1F600);
      Printf.sprintf "%S (%d bytes)" (Buffer.contents b) (Buffer.length b));
  chk "Uchar.of_int 0xD800 (サロゲート)" (fun () ->
      string_of_int (Uchar.to_int (Uchar.of_int 0xD800)));
  chk "Uchar.of_int 0x110000" (fun () ->
      string_of_int (Uchar.to_int (Uchar.of_int 0x110000)))

(* === 9b. 真の末尾 resume(effc が直接 continue を末尾発行)との比較 === *)
let test9b () =
  section "9b" "真の末尾 resume(節を try で包まない)とのコスト比較";
  let open Effect.Deep in
  let pure_tail n =
    match_with
      (fun () -> for _ = 1 to n do println "x" done; VInt 0)
      ()
      { retc = (fun v -> v);
        exnc = (fun e -> raise e);
        effc =
          (fun (type a) (eff : a Effect.t) ->
            match eff with
            | Op ("print", _) -> Some (fun (k : (a, value) continuation) -> continue k VUnit)
            | _ -> None) }
  in
  List.iter
    (fun n ->
      let t0 = Unix.gettimeofday () in
      match pure_tail n with
      | VInt _ -> out "  真の末尾 n=%-9d OK %.2fs\n" n (Unix.gettimeofday () -. t0)
      | _ -> ()
      | exception Stack_overflow -> out "  真の末尾 n=%-9d Stack_overflow\n" n)
    [ 1_000; 100_000; 1_000_000; 10_000_000 ]

(* === 9c. どこがコストか(try 包み vs 単に非末尾) === *)
let test9c () =
  section "9c" "コスト要因の切り分け(n=1,000,000)";
  let open Effect.Deep in
  let variant label mk =
    let t0 = Unix.gettimeofday () in
    let _ = mk 1_000_000 in
    out "  %-56s %.3fs\n" label (Unix.gettimeofday () -. t0)
  in
  let mk ~protect ~use_result n =
    match_with
      (fun () -> for _ = 1 to n do println "x" done; VInt 0)
      ()
      { retc = (fun v -> v);
        exnc = (fun e -> raise e);
        effc =
          (fun (type a) (eff : a Effect.t) ->
            match eff with
            | Op ("print", _) ->
                Some
                  (fun (k : (a, value) continuation) ->
                    let used = ref false in
                    let resume v = used := true; continue k v in
                    if protect then (
                      match (if use_result then (match resume VUnit with VInt m -> VInt m | v -> v)
                             else resume VUnit)
                      with
                      | r -> if !used then r else discontinue k (Unwind (0, r))
                      | exception e -> if !used then raise e else discontinue k e)
                    else
                      let r =
                        if use_result then (match resume VUnit with VInt m -> VInt m | v -> v)
                        else resume VUnit
                      in
                      if !used then r else discontinue k (Unwind (0, r)))
            | _ -> None) }
  in
  variant "A: effc が直接 continue(真の末尾)" (fun n ->
      match_with (fun () -> for _ = 1 to n do println "x" done; VInt 0) ()
        { retc = (fun v -> v); exnc = (fun e -> raise e);
          effc = (fun (type a) (eff : a Effect.t) ->
            match eff with
            | Op ("print", _) -> Some (fun (k : (a, value) continuation) -> continue k VUnit)
            | _ -> None) });
  variant "B: used フラグ + 非末尾(try 無し)" (mk ~protect:false ~use_result:false);
  variant "C: used フラグ + try 包み" (mk ~protect:true ~use_result:false);
  variant "D: 節が resume の結果を使う(capture 相当)" (mk ~protect:true ~use_result:true)

(* === 12. return 節(retc)の実行文脈 === *)
let test12 () =
  section "12" "return 節(retc)の実行文脈: 自分のハンドラは外れているか";
  let v =
    logger (fun () ->
        handle ~name:"eater"
          ~ops:[ ("print", fun args resume -> log "  [eater] %s" (String.trim (arg1_str args)); resume VUnit) ]
          ~ret:(fun x ->
            (* return 節が、自分が扱っているはずの print を perform する *)
            println "return 節から print";
            x)
          (fun () -> println "本体から print"; VInt 1))
  in
  print_string (take_log ());
  out "結果: %s   (return 節の print を [eater] が拾えば再入、[logger] が拾えば外側文脈)\n" (show v)

(* === 13. 数値の追加事実 === *)
let test13 () =
  section "13" "符号なしリテラル(10進)の解釈";
  let chk name f =
    match f () with
    | s -> out "  %-46s => %s\n" name s
    | exception e -> out "  %-46s => 例外 %s\n" name (Printexc.to_string e)
  in
  chk "Int64.of_string \"0u18446744073709551615\"" (fun () ->
      Printf.sprintf "%Ld (unsigned %Lu)"
        (Int64.of_string "0u18446744073709551615")
        (Int64.of_string "0u18446744073709551615"));
  chk "Int32.of_string \"0u4294967295\"" (fun () ->
      Printf.sprintf "%ld (unsigned %lu)"
        (Int32.of_string "0u4294967295") (Int32.of_string "0u4294967295"));
  chk "Int64.of_string \"0u18446744073709551616\" (範囲外)" (fun () ->
      Int64.to_string (Int64.of_string "0u18446744073709551616"));
  chk "Int64.of_string \"0x1_0000_0000\"" (fun () ->
      Int64.to_string (Int64.of_string "0x1_0000_0000"));
  chk "Int64.of_string \"0x1FFFFFFFFFFFFFFFF\" (65bit)" (fun () ->
      Int64.to_string (Int64.of_string "0x1FFFFFFFFFFFFFFFF"));
  chk "Int64.of_string \"\" " (fun () -> Int64.to_string (Int64.of_string ""));
  chk "Int64.of_string \"1_\" (末尾 _)" (fun () ->
      Int64.to_string (Int64.of_string "1_"));
  chk "Int64.of_string \"_1\" (先頭 _)" (fun () ->
      Int64.to_string (Int64.of_string "_1"));
  chk "float_of_string \"1e400\" (overflow)" (fun () ->
      string_of_float (float_of_string "1e400"));
  chk "float_of_string \"nan\"" (fun () -> string_of_float (float_of_string "nan"));
  chk "float_of_string \"0x10\" (16進整数を float に)" (fun () ->
      string_of_float (float_of_string "0x10"))

(* === 14. ハンドラ自身の節が継続を捨てたとき return も cancel も走らない === *)
let test14 () =
  section "14" "自分の節が継続を捨てたとき、自分の return/cancel は走らない(資源漏れ)";
  (* with_file 相当だが、read 節が「EOF なら継続を捨てて #Eof を返す」実装 *)
  let with_file_giveup path body =
    log "  __open(%s)" path;
    handle ~name:("wf " ^ path)
      ~ops:
        [ ("read", fun _ _resume -> VVariant ("Eof", VUnit)) ]
      ~ret:(fun x -> log "  return 節: __close(%s)" path; x)
      ~cancel:(fun () -> log "  cancel 節: __close(%s)" path)
      body
  in
  let v = with_file_giveup "x.txt" (fun () -> ignore (perform_op "read" []); VInt 1) in
  print_string (take_log ());
  out "結果: %s  (__close が一度も出ていなければ資源漏れ)\n" (show v)

let tests =
  [ ("1", test1); ("2", test2); ("3", test3); ("4a", test4a); ("4b", test4b);
    ("4c", test4c); ("5", test5); ("6", test6); ("7a", test7a); ("7b", test7b);
    ("8", test8); ("9", test9); ("9b", test9b); ("9c", test9c); ("10", test10); ("11", test11);
    ("12", test12); ("13", test13); ("14", test14) ]

let () =
  let sel = if Array.length Sys.argv > 1 then Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) else List.map fst tests in
  List.iter (fun name ->
      match List.assoc_opt name tests with
      | Some f -> f (); flush stdout
      | None -> Printf.printf "no such test: %s\n" name) sel;
  print_newline ()
