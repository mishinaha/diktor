(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *)

let concat_list_option = function None -> [] | Some xs -> xs

type oid = int

let current_oid = ref 0

let new_oid () =
  let ret = !current_oid in
  current_oid := ret + 1;
  ret

let with_oid x = (new_oid (), x)

exception NotImplemented of string

let noimpl feat = raise (NotImplemented feat)

exception Panic of string

let bug msg = raise (Panic ("[BUG] " ^ msg))

exception Type_error of string

let type_error msg = raise (Type_error msg)
