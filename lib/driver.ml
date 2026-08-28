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

let run_with options =
  match options.o_mode with
  | Run | TypeCheck | DumpTokens | DumpAst -> noimpl "driver (M2 以降で実装)"

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
      | Panic msg ->
          prerr_endline msg;
          exit 3 )
