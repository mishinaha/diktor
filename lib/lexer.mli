(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *)
module Make (Data : Syntax.Data) : sig
  type context

  type t = { read : unit -> Parser.Make(Data).token; context : context ref; lexbuf : Sedlexing.lexbuf }

  val from_sedlex : Sedlexing.lexbuf -> t

  val from_string : string -> t

  val from_channel : in_channel -> t

  val from_filename : string -> t

  val parse : (Parser.Make(Data).token, 'a) MenhirLib.Convert.traditional -> t -> 'a
end
