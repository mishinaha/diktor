(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * M1 のスタブ。M2 で spike(doc/log/260829-1-spike/menhir/lex.ml)を下敷きに
 * 全面実装する(トークン総入れ替え、ブレース再分類層、ASI、コメント、数値/文字列)。
 * 旧 Orphos レキサ(3トークンバッファ + ASI region 機構)は git 履歴 f0cafd4 を参照。
 *)
module Make (Data : Syntax.Data) = struct
  module Parser = Parser.Make (Data)

  type t = { lexbuf : Sedlexing.lexbuf }

  let from_sedlex lexbuf = { lexbuf }

  let from_string source = Sedlexing.Utf8.from_string source |> from_sedlex

  let from_channel channel = Sedlexing.Utf8.from_channel channel |> from_sedlex

  let from_filename filename = open_in_bin filename |> from_channel

  (* (token, 開始位置, 終了位置) の三つ組で運ぶ(D16) *)
  let read t =
    let sp, ep = Sedlexing.lexing_positions t.lexbuf in
    (Parser.EOF, sp, ep)

  let parse rule lexer = MenhirLib.Convert.Simplified.traditional2revised rule (fun () -> read lexer)
end
