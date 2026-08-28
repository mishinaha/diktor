(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * 値表現とレコード演算(計画 §8.2)。
 * Unit / タプルを専用コンストラクタにしない: 仕様の「同一物」をそのまま実装に写す。
 * ここを崩すと等価・パターン・印字・行演算の全部に分岐が波及する(§13-2)。
 *)
open Aux
open Syntax
module T = Tree.Tree
module SMap = Map.Make (String)

type t =
  | VBool of bool
  | VInt32 of int32
  | VInt64 of int64
  | VFloat64 of float
  | VText of string
  | VRecord of (oid * t) list (* Scoped Labels: 重複可・順序つき。先頭が最新。Unit = VRecord [] *)
  | VVariant of oid * t (* ペイロードは常に単値 *)
  | VData of { d_type : oid; d_ctor : oid; d_fields : t array }
  | VClosure of closure
  | VPrim of prim
  | VRef of t ref
  | VArray of t array

and closure = {
  mutable c_env : env; (* let rec のバックパッチのため mutable *)
  c_params : T.pat list;
  c_body : T.exp;
}

and prim = { p_name : string; p_fn : t -> t (* 引数レコードを受け取る *) }

and env = { globals : (string, t) Hashtbl.t; locals : t SMap.t; resume : resume option }

(* resume は second-class(D19)。値ではなく env 経由で操作節の本体だけに見える *)
and resume = {
  r_k : (t, t) Effect.Deep.continuation;
  mutable r_used : bool;
  mutable r_alive : bool;
}

(* エフェクトのプロトコル(§8.4): 完全操作名 oid * 引数レコード *)
type _ Effect.t += Op : oid * t -> t Effect.t

(* ハンドラ活性化 id * 保留中の節の値(§8.4 の自動巻き戻し) *)
exception Unwind of oid * t

exception Runtime_error of string

let runtime_error msg = raise (Runtime_error msg)

(* ---- レコード演算(Scoped Labels、§8.2) ---- *)

let record_fields = function VRecord fs -> fs | _ -> runtime_error "レコードではない値へのレコード演算"

(* 最左の label を選択 *)
let record_select v label =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then x else go rest
  in
  go (record_fields v)

let record_extend v label x = VRecord ((label, x) :: record_fields v)

(* 最左の label を1つ消す(隠れていた同名が復活する) *)
let record_restrict v label =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then rest else (l, x) :: go rest
  in
  VRecord (go (record_fields v))

(* 選択 + 制限(パターン照合用) *)
let record_take v label =
  let rec go acc = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, x) :: rest -> if l = label then (x, VRecord (List.rev_append acc rest)) else go ((l, x) :: acc) rest
  in
  go [] (record_fields v)

(* 最左の label をその場で差し替える(物理フィールド順を保つ、§8.2) *)
let record_update v label x =
  let rec go = function
    | [] -> runtime_error ("レコードにラベル " ^ Type.name_of label ^ " がありません")
    | (l, y) :: rest -> if l = label then (l, x) :: rest else (l, y) :: go rest
  in
  VRecord (go (record_fields v))

let unit = VRecord []

(* ---- 印字(実行時エラーの表示用) ---- *)

let rec show v =
  match v with
  | VBool b -> string_of_bool b
  | VInt32 n -> Int32.to_string n
  | VInt64 n -> Int64.to_string n
  | VFloat64 f -> string_of_float f
  | VText s -> "\"" ^ String.escaped s ^ "\""
  | VRecord fs ->
      if fs = [] then "()"
      else if List.for_all (fun (l, _) -> l = Type.l_item) fs then
        "(" ^ String.concat ", " (List.map (fun (_, x) -> show x) fs) ^ ")"
      else "{" ^ String.concat ", " (List.map (fun (l, x) -> Type.name_of l ^ " = " ^ show x) fs) ^ "}"
  | VVariant (l, VRecord []) -> "#" ^ Type.name_of l
  | VVariant (l, p) -> "#" ^ Type.name_of l ^ "(" ^ show p ^ ")"
  | VData { d_ctor; d_fields; _ } ->
      if Array.length d_fields = 0 then Type.name_of d_ctor
      else Type.name_of d_ctor ^ "(" ^ String.concat ", " (Array.to_list (Array.map show d_fields)) ^ ")"
  | VClosure _ -> "<fn>"
  | VPrim p -> "<prim " ^ p.p_name ^ ">"
  | VRef _ -> "<ref>"
  | VArray a -> "[" ^ String.concat ", " (Array.to_list (Array.map show a)) ^ "]"
