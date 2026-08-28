(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *)

type t = Lexing.position

type span = { start : Lexing.position; finish : Lexing.position }

let dummy_span = { start = Lexing.dummy_pos; finish = Lexing.dummy_pos }

let show_span { start; finish } =
  let line p = p.Lexing.pos_lnum in
  let col p = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  if start == Lexing.dummy_pos then "<unknown>"
  else if line start = line finish then Printf.sprintf "%d:%d-%d" (line start) (col start) (col finish)
  else Printf.sprintf "%d:%d-%d:%d" (line start) (col start) (line finish) (col finish)
