(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * parse → elab → eval のドライバと CLI(計画 §8.7)。
 * 終了コード: 0 正常 / 1 型エラー / 2 パースエラー / 3 実行時エラー / 4 未実装 / 64 使用法エラー。
 * テストがサブプロセスなしで叩けるよう、CLI とテストは同じ関数を通す。
 *)
open Aux

let usage =
  "usage: diktor [OPTIONS] FILE.kel...\n\
   \  --type-check         型検査のみ。トップレベル束縛の型を \"name : type\" で出力\n\
   \  --dump-tokens        ASI 適用後のトークン列を出力\n\
   \  --dump-ast           脱糖後の AST を S 式で出力\n\
   \  --no-prelude / --prelude PATH\n\
   \  --strict-exhaustive  網羅性・到達不能警告をエラー化\n"

type mode = Run | TypeCheck | DumpTokens | DumpAst

type options = {
  o_mode : mode;
  o_prelude : string option; (* Some PATH で差し替え *)
  o_no_prelude : bool;
  o_strict_exhaustive : bool;
  o_files : string list;
}

let default_options = { o_mode = Run; o_prelude = None; o_no_prelude = false; o_strict_exhaustive = false; o_files = [] }

let parse_args args =
  let rec go opts = function
    | [] -> if opts.o_files = [] then Error "no input files" else Ok { opts with o_files = List.rev opts.o_files }
    | "--type-check" :: rest -> go { opts with o_mode = TypeCheck } rest
    | "--dump-tokens" :: rest -> go { opts with o_mode = DumpTokens } rest
    | "--dump-ast" :: rest -> go { opts with o_mode = DumpAst } rest
    | "--no-prelude" :: rest -> go { opts with o_no_prelude = true } rest
    | "--prelude" :: path :: rest -> go { opts with o_prelude = Some path } rest
    | "--prelude" :: [] -> Error "--prelude requires a path"
    | "--strict-exhaustive" :: rest -> go { opts with o_strict_exhaustive = true } rest
    | arg :: _ when String.length arg > 0 && arg.[0] = '-' -> Error ("unknown option: " ^ arg)
    | file :: rest -> go { opts with o_files = file :: opts.o_files } rest
  in
  go default_options args

module Lexer' = Lexer.Make (Tree.ElabData)
module Parser' = Parser.Make (Tree.ElabData)

(* main が捕まえて exit 2 にする(位置は整形済み) *)
exception Parse_error of string

let show_pos pos =
  Printf.sprintf "%s:%d:%d" pos.Lexing.pos_fname pos.Lexing.pos_lnum (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1)

let dump_tokens_file file =
  let lexer = Lexer'.from_filename file in
  Lexer'.all_tokens lexer
  |> List.iter (fun e -> Printf.printf "%4d  %s\n" e.Lexer'.sp.Lexing.pos_lnum (Lexer'.show_token e.Lexer'.tok))

let parse_with lexer =
  try Lexer'.parse Parser'.program lexer with
  | Parser'.Error ->
      raise (Parse_error (Printf.sprintf "%s: パースエラー(付近のトークンを確認してください)" (show_pos lexer.Lexer'.last_sp)))
  | Syntax.Syntax_error msg ->
      raise (Parse_error (Printf.sprintf "%s: 構文エラー: %s" (show_pos lexer.Lexer'.last_sp) msg))

let parse_file file = parse_with (Lexer'.from_filename file)

let parse_string ~filename source =
  let lexbuf = Sedlexing.Utf8.from_string source in
  Sedlexing.set_filename lexbuf filename;
  parse_with (Lexer'.from_sedlex lexbuf)

(* プレリュード(§8.6): 既定は埋め込み、--prelude PATH で差し替え、--no-prelude で空 *)
let load_prelude options =
  if options.o_no_prelude then []
  else
    let source =
      match options.o_prelude with
      | Some path -> In_channel.with_open_bin path In_channel.input_all
      | None -> Prelude_embed.source
    in
    parse_string ~filename:"<prelude>" source

(* quiet = Run モード: 型行は出さず、警告だけ stderr に出す *)
let type_check_files ?(quiet = false) options =
  let prelude = load_prelude options in
  let decls = List.concat_map parse_file options.o_files in
  let put line = if quiet then (if String.length line > 0 && line.[0] = '\xe2' then prerr_endline line) else print_endline line in
  match Elab.type_check ~prelude decls with
  | lines, None ->
      List.iter put lines;
      if options.o_strict_exhaustive && !Elab.warnings <> [] then exit 1;
      (prelude, decls)
  | lines, Some err ->
      List.iter put lines;
      print_endline err;
      exit 1

let run_with options =
  match options.o_mode with
  | DumpTokens -> List.iter dump_tokens_file options.o_files
  | DumpAst -> List.iter (fun file -> Dump.dump_decls stdout (parse_file file)) options.o_files
  | TypeCheck -> ignore (type_check_files options)
  | Run ->
      let prelude, decls = type_check_files ~quiet:true options in
      Interp.cancel_log := (fun msg -> Printf.eprintf "cancel 節で例外が抑制されました: %s\n" msg);
      Interp.run ~sink:print_string (prelude @ decls)

let main () =
  match parse_args (Array.to_list Sys.argv |> List.tl) with
  | Error msg ->
      Printf.eprintf "diktor: %s\n%s" msg usage;
      exit 64
  | Ok options -> (
      try run_with options with
      | NotImplemented feat ->
          Printf.eprintf "未実装: %s\n" feat;
          exit 4
      | Lexer.Lex_error (msg, pos) ->
          Printf.eprintf "%s: 字句エラー: %s\n" (show_pos pos) msg;
          exit 2
      | Parse_error msg ->
          prerr_endline msg;
          exit 2
      | Value.Runtime_error msg ->
          Printf.eprintf "実行時エラー: %s\n" msg;
          exit 3
      | Effect.Unhandled (Value.Op (op, _)) ->
          Printf.eprintf "未処理のエフェクト操作: %s\n" (Syntax.Type.name_of op);
          exit 3
      | Panic msg ->
          prerr_endline msg;
          exit 3 )
