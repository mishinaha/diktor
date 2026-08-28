(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * 宣言のみの葉(計画 §8.1)。演算子→クラスメソッド表(sample.kel:279-283)と
 * ランタイム提供エフェクト集合。elab と interp が共有する唯一の定義点。
 *)
open Syntax

(* 演算子の意味。短絡(&& ||)と否定(!=)という2つの例外が表の中に閉じる(D9) *)
type op_sem =
  | OpMethod of string * string (* クラス名, メソッド名 *)
  | OpMethodNot of string * string (* Eq.eq の否定(!=) *)
  | OpBool (* Boolean 組み込み(短絡するため型クラスにできない) *)

let bin_op_sem = function
  | Add -> OpMethod ("Add", "add")
  | Sub -> OpMethod ("Sub", "sub")
  | Mul -> OpMethod ("Mul", "mul")
  | Div -> OpMethod ("Div", "div")
  | Eq -> OpMethod ("Eq", "eq")
  | Ne -> OpMethodNot ("Eq", "eq")
  | Lt -> OpMethod ("Ord", "lt")
  | Le -> OpMethod ("Ord", "le")
  | Gt -> OpMethod ("Ord", "gt")
  | Ge -> OpMethod ("Ord", "ge")
  | And | Or -> OpBool

let show_bin_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Eq -> "=="
  | Ne -> "!="
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | And -> "&&"
  | Or -> "||"

(* トップレベルの初期 eff はランタイム提供エフェクトの閉じた行(§7.6) *)
let runtime_effects = [ "Console"; "Async" ]
