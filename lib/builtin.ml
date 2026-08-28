(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * __* プリミティブの実装、組み込みクラスメソッドの実装、
 * ランタイムエフェクトハンドラ(with_runtime)と出力シンク(計画 §8.1, §8.6)。
 *)
open Syntax
open Value

let arg_values v = List.map snd (record_fields v)

let arg1 v = match arg_values v with [ a ] -> a | _ -> runtime_error "プリミティブの引数が1個ではありません"

let arg2 v = match arg_values v with [ a; b ] -> (a, b) | _ -> runtime_error "プリミティブの引数が2個ではありません"

let as_i32 = function VInt32 n -> n | v -> runtime_error ("Int32 ではありません: " ^ show v)

let as_i64 = function VInt64 n -> n | v -> runtime_error ("Int64 ではありません: " ^ show v)

let as_f64 = function VFloat64 f -> f | v -> runtime_error ("Float64 ではありません: " ^ show v)

let as_text = function VText s -> s | v -> runtime_error ("String ではありません: " ^ show v)

let as_bool = function VBool b -> b | v -> runtime_error ("Boolean ではありません: " ^ show v)

(* Float64 の最短往復可能表現(string_of_float の %.12g は精度を落とす)。
   %.NNg を桁を上げながら試し、読み戻して一致する最小桁を採る *)
let float_repr f =
  if Float.is_integer f && Float.abs f < 1e16 then Printf.sprintf "%.1f" f
  else
    let rec go p =
      if p > 17 then Printf.sprintf "%.17g" f
      else
        let s = Printf.sprintf "%.*g" p f in
        if float_of_string s = f then s else go (p + 1)
    in
    go 1

(* ---- テスト用のメモリ上ダミーファイルシステム(§8.6) ---- *)

let fs : (string, string) Hashtbl.t = Hashtbl.create 8

let handles : (int32, string) Hashtbl.t = Hashtbl.create 8

let next_handle = ref 0l

(* ---- __* プリミティブ表(名前 → 実装)。型は prelude.kel の extern 宣言が与える ---- *)

let i32_bin f = fun v -> let a, b = arg2 v in VInt32 (f (as_i32 a) (as_i32 b))

let i64_bin f = fun v -> let a, b = arg2 v in VInt64 (f (as_i64 a) (as_i64 b))

let f64_bin f = fun v -> let a, b = arg2 v in VFloat64 (f (as_f64 a) (as_f64 b))

let i32_cmp f = fun v -> let a, b = arg2 v in VBool (f (Int32.compare (as_i32 a) (as_i32 b)) 0)

let i64_cmp f = fun v -> let a, b = arg2 v in VBool (f (Int64.compare (as_i64 a) (as_i64 b)) 0)

let f64_cmp f = fun v -> let a, b = arg2 v in VBool (f (compare (as_f64 a) (as_f64 b)) 0)

let div_check_i32 a b = if b = 0l then runtime_error "ゼロ除算です" else Int32.div a b

let div_check_i64 a b = if b = 0L then runtime_error "ゼロ除算です" else Int64.div a b

let rem_check_i32 a b = if b = 0l then runtime_error "ゼロ除算です" else Int32.rem a b

let rem_check_i64 a b = if b = 0L then runtime_error "ゼロ除算です" else Int64.rem a b

let prims : (string * (t -> t)) list =
  [
    ("__int32_add", i32_bin Int32.add);
    ("__int32_sub", i32_bin Int32.sub);
    ("__int32_mul", i32_bin Int32.mul);
    ("__int32_div", i32_bin div_check_i32);
    ("__int32_rem", i32_bin rem_check_i32);
    ("__int32_neg", fun v -> VInt32 (Int32.neg (as_i32 (arg1 v))));
    ("__int32_eq", i32_cmp ( = ));
    ("__int32_lt", i32_cmp ( < ));
    ("__int32_le", i32_cmp ( <= ));
    ("__int32_gt", i32_cmp ( > ));
    ("__int32_ge", i32_cmp ( >= ));
    ("__int64_add", i64_bin Int64.add);
    ("__int64_sub", i64_bin Int64.sub);
    ("__int64_mul", i64_bin Int64.mul);
    ("__int64_div", i64_bin div_check_i64);
    ("__int64_rem", i64_bin rem_check_i64);
    ("__int64_neg", fun v -> VInt64 (Int64.neg (as_i64 (arg1 v))));
    ("__int64_eq", i64_cmp ( = ));
    ("__int64_lt", i64_cmp ( < ));
    ("__int64_le", i64_cmp ( <= ));
    ("__int64_gt", i64_cmp ( > ));
    ("__int64_ge", i64_cmp ( >= ));
    ("__float64_add", f64_bin ( +. ));
    ("__float64_sub", f64_bin ( -. ));
    ("__float64_mul", f64_bin ( *. ));
    ("__float64_div", f64_bin ( /. ));
    ("__float64_neg", fun v -> VFloat64 (-.as_f64 (arg1 v)));
    ("__float64_eq", fun v -> let a, b = arg2 v in VBool (as_f64 a = as_f64 b) (* IEEE: NaN <> NaN *));
    ("__float64_lt", f64_cmp ( < ));
    ("__float64_le", f64_cmp ( <= ));
    ("__float64_gt", f64_cmp ( > ));
    ("__float64_ge", f64_cmp ( >= ));
    ("__string_concat", fun v -> let a, b = arg2 v in VText (as_text a ^ as_text b));
    ("__string_eq", fun v -> let a, b = arg2 v in VBool (String.equal (as_text a) (as_text b)));
    ("__string_lt", fun v -> let a, b = arg2 v in VBool (String.compare (as_text a) (as_text b) < 0));
    ("__string_le", fun v -> let a, b = arg2 v in VBool (String.compare (as_text a) (as_text b) <= 0));
    ("__string_gt", fun v -> let a, b = arg2 v in VBool (String.compare (as_text a) (as_text b) > 0));
    ("__string_ge", fun v -> let a, b = arg2 v in VBool (String.compare (as_text a) (as_text b) >= 0));
    ("__string_length", fun v -> VInt32 (Int32.of_int (String.length (as_text (arg1 v)))));
    ( "__string_sub",
      fun v ->
        match arg_values v with
        | [ s; pos; len ] -> (
            try VText (String.sub (as_text s) (Int32.to_int (as_i32 pos)) (Int32.to_int (as_i32 len)))
            with Invalid_argument _ -> runtime_error "__string_sub: 範囲外です")
        | _ -> runtime_error "__string_sub の引数が3個ではありません" );
    ("__i32_to_i64", fun v -> VInt64 (Int64.of_int32 (as_i32 (arg1 v))));
    ("__i32_to_f64", fun v -> VFloat64 (Int32.to_float (as_i32 (arg1 v))));
    ("__i64_to_i32", fun v -> VInt32 (Int64.to_int32 (as_i64 (arg1 v))));
    ("__i64_to_f64", fun v -> VFloat64 (Int64.to_float (as_i64 (arg1 v))));
    ("__f64_to_i32", fun v -> VInt32 (Int32.of_float (as_f64 (arg1 v))));
    ("__f64_to_i64", fun v -> VInt64 (Int64.of_float (as_f64 (arg1 v))));
    ("__show_int32", fun v -> VText (Int32.to_string (as_i32 (arg1 v))));
    ("__panic", fun v -> runtime_error ("panic: " ^ as_text (arg1 v)));
    (* extern "C" の既知名テーブル(M10。真の C FFI は延期、§2.1 §12) *)
    ("sin", fun v -> VFloat64 (sin (as_f64 (arg1 v))));
    ("cos", fun v -> VFloat64 (cos (as_f64 (arg1 v))));
    ("sqrt", fun v -> VFloat64 (sqrt (as_f64 (arg1 v))));
    ("exp", fun v -> VFloat64 (exp (as_f64 (arg1 v))));
    ("log", fun v -> VFloat64 (log (as_f64 (arg1 v))));
    ( "__open",
      fun v ->
        let path = as_text (arg1 v) in
        next_handle := Int32.add !next_handle 1l;
        Hashtbl.replace handles !next_handle path;
        VInt32 !next_handle );
    ( "__read",
      fun v ->
        let h = as_i32 (arg1 v) in
        let path = try Hashtbl.find handles h with Not_found -> runtime_error "__read: 無効なハンドルです" in
        VText (Option.value ~default:"" (Hashtbl.find_opt fs path)) );
    ( "__write",
      fun v ->
        let h, s = arg2 v in
        let path = try Hashtbl.find handles (as_i32 h) with Not_found -> runtime_error "__write: 無効なハンドルです" in
        Hashtbl.replace fs path (Option.value ~default:"" (Hashtbl.find_opt fs path) ^ as_text s);
        unit );
    ( "__close",
      fun v ->
        Hashtbl.remove handles (as_i32 (arg1 v));
        unit );
  ]

let find_prim name = List.assoc_opt name prims

(* ---- 組み込みクラスメソッドの実装表: (クラス, 型構成子, メソッド) → 実装 ---- *)

let builtin_method cls con meth : (t -> t) option =
  let p name = find_prim name in
  match (cls, con, meth) with
  | "Add", "Int32", "add" -> p "__int32_add"
  | "Add", "Int64", "add" -> p "__int64_add"
  | "Add", "Float64", "add" -> p "__float64_add"
  | "Add", "String", "add" -> p "__string_concat"
  | "Sub", "Int32", "sub" -> p "__int32_sub"
  | "Sub", "Int64", "sub" -> p "__int64_sub"
  | "Sub", "Float64", "sub" -> p "__float64_sub"
  | "Mul", "Int32", "mul" -> p "__int32_mul"
  | "Mul", "Int64", "mul" -> p "__int64_mul"
  | "Mul", "Float64", "mul" -> p "__float64_mul"
  | "Div", "Int32", "div" -> p "__int32_div"
  | "Div", "Int64", "div" -> p "__int64_div"
  | "Div", "Float64", "div" -> p "__float64_div"
  | "Eq", "Int32", "eq" -> p "__int32_eq"
  | "Eq", "Int64", "eq" -> p "__int64_eq"
  | "Eq", "Float64", "eq" -> p "__float64_eq"
  | "Eq", "String", "eq" -> p "__string_eq"
  | "Eq", "Boolean", "eq" -> Some (fun v -> let a, b = arg2 v in VBool (as_bool a = as_bool b))
  | "Ord", "Int32", m -> p ("__int32_" ^ m)
  | "Ord", "Int64", m -> p ("__int64_" ^ m)
  | "Ord", "Float64", m -> p ("__float64_" ^ m)
  | "Ord", "String", m -> p ("__string_" ^ m)
  | "Show", "Int32", "show" -> Some (fun v -> VText (Int32.to_string (as_i32 (arg1 v))))
  | "Show", "Int64", "show" -> Some (fun v -> VText (Int64.to_string (as_i64 (arg1 v))))
  | "Show", "Float64", "show" -> Some (fun v -> VText (float_repr (as_f64 (arg1 v))))
  | "Show", "String", "show" -> Some (fun v -> VText (as_text (arg1 v)))
  | "Show", "Boolean", "show" -> Some (fun v -> VText (string_of_bool (as_bool (arg1 v))))
  | _ -> None

(* ---- ランタイムエフェクトハンドラ(最外周の1枚、§8.4) ---- *)

let op_console_write = Type.intern "Console.write"

let op_async_yield = Type.intern "Async.yield_"

let op_async_sleep = Type.intern "Async.sleep"

let with_runtime ~(sink : string -> unit) (f : unit -> t) : t =
  Effect.Deep.match_with f ()
    {
      retc = Fun.id;
      exnc = raise;
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Op (op, args) when op = op_console_write ->
              Some
                (fun (k : (a, _) Effect.Deep.continuation) ->
                  sink (as_text (arg1 args));
                  Effect.Deep.continue k unit)
          | Op (op, _) when op = op_async_yield || op = op_async_sleep ->
              (* v0: 型 + 実行時 no-op(§2.1 §11) *)
              Some (fun k -> Effect.Deep.continue k unit)
          | _ -> None);
    }
