(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *)
open Syntax

module Make (Data : Syntax.Data) = struct
  module Parser = Parser.Make (Data)
  open Parser

  let is_auto_semi_followed = function
    | IF _ | MATCH _ | FN _ | LET _ | LBRACKET _ | NUMBERSIGN _ | LCBRACKET _ | GRAVE_ACCENT _ | PLUS _ | HYPHEN _
    | EXCLAMATION _ | AMPERSAND _ | ASTERISK _ | BIG_PLUS _ | BIG_HYPHEN _ | RAISE _ | LAZY _ | TILDE _
    | UPPER_IDENTIFIER _ | LOWER_IDENTIFIER _ | LPAREN _ | TEXT _ | NUMBER _ | BOOL _ | TYPE _ | VAL _ | EXCEPTION _ ->
        true
    | _ -> false

  let is_followed_by_auto_semi = function
    | END _ | RBRACKET _ | RCBRACKET _ | BIG_PLUS _ | BIG_HYPHEN _ | UPPER_IDENTIFIER _ | LOWER_IDENTIFIER _
    | RPAREN _ | TEXT _ | NUMBER _ | BOOL _ ->
        true
    | _ -> false

  type auto_semi_region_type = TopLevel | InCbracket | InParen | InPatternClause

  type context = {
    ahead2 : Parser.token option;
    ahead : Parser.token option;
    current : Parser.token option;
    auto_semi_regions : auto_semi_region_type list;
  }

  let new_context () = ref { ahead2 = None; ahead = None; current = None; auto_semi_regions = [ TopLevel ] }

  let rollback = Sedlexing.rollback

  let lexeme = Sedlexing.Utf8.lexeme

  let lexeme_char = Sedlexing.lexeme_char

  let loc lexbuf =
    let start, _ = Sedlexing.lexing_positions lexbuf in
    start

  let rec read_newline lexbuf =
    match%sedlex lexbuf with
    | '\n' ->
        Sedlexing.new_line lexbuf;
        read_newline lexbuf
    | ' ' | '\t' -> read_newline lexbuf
    | _ ->
        rollback lexbuf;
        NL (loc lexbuf)

  let read_unicode_escape lexbuf limit =
    let rec loop acc = function
      | i when i = limit -> Uchar.of_int acc
      | i -> (
          let ret base_char base_value =
            loop
              ((acc * 16) + (Uchar.to_int (Sedlexing.lexeme_char lexbuf 0) - Char.code base_char) + base_value)
              (i + 1)
          in
          match%sedlex lexbuf with
          | '0' .. '9' -> ret '0' 0
          | 'a' .. 'f' -> ret 'a' 10
          | 'A' .. 'F' -> ret 'A' 10
          | _ -> failwith "unexpecd end of unicode escape" )
    in
    loop 0 0

  let read_escape lexbuf =
    match%sedlex lexbuf with
    | 'u' -> read_unicode_escape lexbuf 4
    | 'U' -> read_unicode_escape lexbuf 8
    | '\'' -> Uchar.of_char '\''
    | '"' -> Uchar.of_char '"'
    | '\\' -> Uchar.of_char '\\'
    | 'a' -> Uchar.of_int 0x07
    | 'b' -> Uchar.of_char '\b'
    | 'f' -> Uchar.of_int 0x0c
    | 'n' -> Uchar.of_char '\n'
    | 'r' -> Uchar.of_char '\r'
    | 't' -> Uchar.of_char '\t'
    | 'v' -> Uchar.of_int 0x0b
    | _ -> failwith "Invalid escape sequence"

  let read_text lexbuf =
    let buf = Buffer.create 1024 in
    let rec aux () =
      match%sedlex lexbuf with
      | '"' -> Buffer.contents buf
      | eof -> failwith "unexpeted EOF"
      | '\\' ->
          Buffer.add_utf_8_uchar buf (read_escape lexbuf);
          aux ()
      | any ->
          Buffer.add_string buf (lexeme lexbuf);
          aux ()
      | _ -> failwith "unreachable"
    in
    aux ()

  let read_precision lexbuf =
    let rec aux acc =
      match%sedlex lexbuf with
      | '0' .. '9' -> aux ((acc * 10) + Uchar.to_int (lexeme_char lexbuf 0) - Char.code '0')
      | _ -> acc
    in
    aux 0

  let read_number lexbuf radix =
    let ret m e n = ((m, e), n) in
    let read_digit_char base_char base_value = Uchar.to_int (lexeme_char lexbuf 0) - Char.code base_char + base_value in
    let rec proceed m e n base_char base_value reading_exponent =
      let digit_value = read_digit_char base_char base_value in
      if radix < digit_value then (
        rollback lexbuf;
        ret m e n )
      else aux ((m * radix) + digit_value) (if reading_exponent then e + 1 else e) n reading_exponent
    and aux m e n reading_exponent =
      match%sedlex lexbuf with
      | '0' .. '9' -> proceed m e n '0' 0 reading_exponent
      | 'a' .. 'e' -> proceed m e n 'a' 10 reading_exponent
      | 'A' .. 'F' -> proceed m e n 'A' 10 reading_exponent
      | '.' ->
          if reading_exponent then (
            rollback lexbuf;
            ret m e n )
          else aux m e QType true
      | 'i' -> ret m e (IntType (read_precision lexbuf))
      | 'u' -> ret m e (IntType (read_precision lexbuf))
      | 'f' ->
          if radix = 10 then ret m e (FloatType (read_precision lexbuf))
          else (
            rollback lexbuf;
            ret m e n )
      | _ -> ret m e n
    in
    aux 0 0 ZType false

  let rec read_raw_token lexbuf =
    let loc () = loc lexbuf in
    match%sedlex lexbuf with
    | Plus (' ' | '\t') -> read_raw_token lexbuf
    | '\n' ->
        Sedlexing.new_line lexbuf;
        read_newline lexbuf
    (* three character symbols *)
    | ":+:" -> COLON_PLUS_COLON (loc ())
    | ":-:" -> COLON_HYPHEN_COLON (loc ())
    (* two character symbols *)
    | "!=" -> EXCLAMATION_EQ (loc ())
    | "&&" -> BIG_AMPERSAND (loc ())
    | "++" -> BIG_PLUS (loc ())
    | "+:" -> PLUS_COLON (loc ())
    | "+=" -> PLUS_EQ (loc ())
    | "," -> COMMA (loc ())
    | "--" -> BIG_HYPHEN (loc ())
    | "-:" -> HYPHEN_COLON (loc ())
    | "-=" -> HYPHEN_EQ (loc ())
    | "->" -> HYPHEN_GREATER (loc ())
    | ":+" -> COLON_PLUS (loc ())
    | ":-" -> COLON_HYPHEN (loc ())
    | "::" -> BIG_COLON (loc ())
    | ":=" -> COLON_EQ (loc ())
    | "<<" -> BIG_LESS (loc ())
    | "==" -> BIG_EQ (loc ())
    | "=>" -> EQ_GREATER (loc ())
    | ">>" -> BIG_GREATER (loc ())
    | "[" -> LBRACKET (loc ())
    | "]" -> RBRACKET (loc ())
    | "|>" -> VERTICAL_GREATER (loc ())
    | "||" -> BIG_VERTICAL (loc ())
    (* raw identifiers starting with uppercase character *)
    | 'A' .. 'Z', Star ('a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9') -> UPPER_IDENTIFIER (loc (), lexeme lexbuf)
    (* raw identifiers starting with lowercase or lowline character, or keyword *)
    | ('a' .. 'z' | '_'), Star ('a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9') -> (
        match lexeme lexbuf with
        | "and" -> AND (loc ())
        | "as" -> AS (loc ())
        | "case" -> CASE (loc ())
        | "effect" -> EFFECT (loc ())
        | "else" -> ELSE (loc ())
        | "end" -> END (loc ())
        | "exception" -> EXCEPTION (loc ())
        | "false" -> BOOL (loc (), false)
        | "fn" -> FN (loc ())
        | "given" -> GIVEN (loc ())
        | "handle" -> HANDLE (loc ())
        | "if" -> IF (loc ())
        | "interface" -> INTERFACE (loc ())
        | "lazy" -> LAZY (loc ())
        | "let" -> LET (loc ())
        | "match" -> MATCH (loc ())
        | "module" -> MODULE (loc ())
        | "of" -> OF (loc ())
        | "raise" -> RAISE (loc ())
        | "rec" -> REC (loc ())
        | "then" -> THEN (loc ())
        | "true" -> BOOL (loc (), true)
        | "type" -> TYPE (loc ())
        | "val" -> VAL (loc ())
        | "when" -> WHEN (loc ())
        | "where" -> WHERE (loc ())
        | "with" -> WITH (loc ())
        | id -> LOWER_IDENTIFIER (loc (), id) )
    (* quoted lower-identifier *)
    | "${", Sub (any, '}'), '}' ->
        let s = lexeme lexbuf in
        LOWER_IDENTIFIER (loc (), String.sub s 2 (String.length s - 3))
    (* quoted upper-identifier *)
    | "$[", Sub (any, ']'), ']' ->
        let s = lexeme lexbuf in
        UPPER_IDENTIFIER (loc (), String.sub s 2 (String.length s - 3))
    (* lower identifier prefixed with $ *)
    | '$', ('a' .. 'z' | '_'), Star ('a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9') ->
        let s = lexeme lexbuf in
        LOWER_IDENTIFIER (loc (), String.sub s 1 (String.length s - 1))
    (* upper identifier prefixed with $ *)
    | '$', 'A' .. 'Z', Star ('a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9') ->
        let s = lexeme lexbuf in
        UPPER_IDENTIFIER (loc (), String.sub s 1 (String.length s - 1))
    (* one character symbols *)
    | "-" -> HYPHEN (loc ())
    | '!' -> EXCLAMATION (loc ())
    | '#' -> NUMBERSIGN (loc ())
    | '%' -> PERCENT (loc ())
    | '&' -> AMPERSAND (loc ())
    | '(' -> LPAREN (loc ())
    | ')' -> RPAREN (loc ())
    | '*' -> ASTERISK (loc ())
    | '+' -> PLUS (loc ())
    | '.' -> DOT (loc ())
    | '/' -> SOLIDUS (loc ())
    | ':' -> COLON (loc ())
    | ';' -> SEMI (loc ())
    | '<' -> LESS (loc ())
    | '=' -> EQ (loc ())
    | '>' -> GREATER (loc ())
    | '@' -> AT (loc ())
    | '\'' -> SINGLE_QUOTE (loc ())
    | '^' -> CIRCUMFLEX (loc ())
    | '_' -> LOWLINE (loc ())
    | '_' -> LOWLINE (loc ())
    | '`' -> GRAVE_ACCENT (loc ())
    | '{' -> LCBRACKET (loc ())
    | '|' -> VERTICAL (loc ())
    | '}' -> RCBRACKET (loc ())
    | '~' -> TILDE (loc ())
    | '"' -> TEXT (loc (), read_text lexbuf)
    | "0", '0' .. '7' ->
        rollback lexbuf;
        NUMBER (loc (), read_number lexbuf 8)
    | "0x" -> NUMBER (loc (), read_number lexbuf 16)
    | "0b" -> NUMBER (loc (), read_number lexbuf 2)
    | '0' .. '9' ->
        rollback lexbuf;
        NUMBER (loc (), read_number lexbuf 10)
    | _ -> EOF (loc ())

  let rec read_token lexbuf region_in_sync context =
    match (region_in_sync, context) with
    | _, { contents = { current = None; ahead = None; ahead2 = None; _ } } ->
        context := { !context with ahead2 = Some (read_raw_token lexbuf) };
        read_token lexbuf false context
    | true, { contents = { current = None; ahead = None; ahead2 = Some ahead2; _ } } ->
        context := { !context with ahead2 = Some (read_raw_token lexbuf); ahead = Some ahead2 };
        read_token lexbuf false context
    | true, { contents = { current = None; ahead = Some ahead; ahead2 = Some ahead2; _ } } ->
        context := { !context with ahead2 = Some (read_raw_token lexbuf); ahead = Some ahead2; current = Some ahead };
        read_token lexbuf false context
    | false, { contents = { ahead2 = Some (LCBRACKET _); auto_semi_regions = regions; _ } } ->
        context := { !context with auto_semi_regions = InCbracket :: regions };
        read_token lexbuf true context
    | false, { contents = { ahead2 = Some (LPAREN _ | LBRACKET _); auto_semi_regions = regions; _ } } ->
        context := { !context with auto_semi_regions = InParen :: regions };
        read_token lexbuf true context
    | ( false,
        { contents = { ahead2 = Some (RCBRACKET _ | RPAREN _ | RBRACKET _); auto_semi_regions = _ :: regions_tail; _ } }
      ) ->
        context := { !context with auto_semi_regions = regions_tail };
        read_token lexbuf true context
    | false, { contents = { ahead2 = Some (CASE _); auto_semi_regions = regions; _ } } ->
        context := { !context with auto_semi_regions = InPatternClause :: regions };
        read_token lexbuf true context
    | false, { contents = { ahead2 = Some (HYPHEN_GREATER _); auto_semi_regions = InPatternClause :: regions_tail; _ } }
      ->
        context := { !context with auto_semi_regions = regions_tail };
        read_token lexbuf true context
    | false, { contents = { ahead2 = Some (NL _); auto_semi_regions = (InParen | InPatternClause) :: _; _ } } ->
        (* skip NL inside autoinsertion-disabled region *)
        context := { !context with ahead2 = Some (read_raw_token lexbuf) };
        read_token lexbuf false context
    | false, context -> read_token lexbuf true context
    | true, { contents = { current = Some current; ahead = Some (NL _); ahead2 = Some ahead2; _ } }
      when is_auto_semi_followed current && is_followed_by_auto_semi ahead2 ->
        context := { !context with current = None };
        current
    | true, { contents = { current = Some current; ahead = Some (NL _); ahead2 = Some _; _ } } ->
        (* skip NL that is not between auto_semi_followed and followed_by_auto_semi *)
        context := { !context with current = None; ahead = Some current };
        read_token lexbuf true context
    | true, { contents = { current = Some current; ahead = Some _; ahead2 = Some _; _ } } ->
        context := { !context with current = None };
        current
    | true, { contents = { current = Some _; ahead2 = None; _ } }
    | true, { contents = { current = Some _; ahead = None; _ } }
    | true, { contents = { ahead = Some _; ahead2 = None; _ } } ->
        failwith "unreachable"

  type t = { read : unit -> Parser.token; context : context ref; lexbuf : Sedlexing.lexbuf }

  let from_sedlex (lexbuf : Sedlexing.lexbuf) : t =
    let context = new_context () in
    { read = (fun () -> read_token lexbuf true context); context; lexbuf }

  let from_string source = Sedlexing.Utf8.from_string source |> from_sedlex

  let from_channel channel = Sedlexing.Utf8.from_channel channel |> from_sedlex

  let from_filename filename = open_in_bin filename |> from_channel

  let parse rule lexer =
    let lex () =
      let old_pos, _ = lexer.lexbuf |> Sedlexing.lexing_positions in
      let token = lexer.read () in
      let new_pos, _ = lexer.lexbuf |> Sedlexing.lexing_positions in
      (token, old_pos, new_pos)
    in
    MenhirLib.Convert.Simplified.traditional2revised rule lex
end
