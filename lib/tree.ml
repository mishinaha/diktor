(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *)
open Aux

(* elab が解決した結果を interp に渡す窓口(§4.2)。
   これが無いと elab と interp が同じ解決を二重実装しドリフトする *)
type resolved =
  | ROp of oid (* perform / handle 操作節: 完全操作名("Console.write")の oid *)
  | RReturnClause (* handle の return 節 *)
  | RCancelClause (* handle の cancel 節 *)
  | RCtorOrder of int array (* Construct: 実引数位置 → 宣言フィールド順 *)

module ElabData = struct
  type t = {
    oid : oid;
    loc : Location.span;
    mutable ty_field : Syntax.Type.ty option;
    mutable resolved : resolved option;
  }

  let allocate loc = { oid = new_oid (); loc; ty_field = None; resolved = None }
end

(* Syntax.Make はアプリカティブファンクタなので、Parser.Make(ElabData) 側の
   Tree と型が一致する(計画 §7.1) *)
module Tree = Syntax.Make (ElabData)

let data (d, _) = d

let loc_of (d, _) = d.ElabData.loc

let oid_of (d, _) = d.ElabData.oid

let get_ty (d, _) = match d.ElabData.ty_field with Some t -> t | None -> bug "get_ty: node not elaborated"

let set_ty (d, _) t = d.ElabData.ty_field <- Some t

let get_resolved (d, _) = d.ElabData.resolved

let set_resolved (d, _) r = d.ElabData.resolved <- Some r
