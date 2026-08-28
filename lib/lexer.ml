(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * Keleut レキサ(計画 §5)。3層構成:
 *   1. read_raw_token — sedlex の生トークン(`{` は LBRACE_BLOCK をプレースホルダに使う)
 *   2. 再分類層(§5.3)— pop 時に `{` を NL を跨ぐ2トークン先読みで 3-way 分類する。
 *      先読みしたトークンはキューに残り、自分の番が来たとき個別に再分類される
 *   3. ASI 層(§5.4)— region スタック + can_end/can_begin 述語で NL を文区切りに昇格/破棄
 * 参照実装: doc/log/260829-1-spike/menhir/lex.ml(sample.kel 全文で検証済み)
 *)
open Syntax

(* 字句エラー *)
exception Lex_error of string * Lexing.position

(* ---- 数値リテラル(D13, §5.5)。lexeme を受け取る純関数 ---- *)

let parse_number text =
  let len = String.length text in
  let has_radix_prefix = len >= 2 && text.[0] = '0' && (match text.[1] with 'x' | 'o' | 'b' -> true | _ -> false) in
  (* 接尾辞の開始位置: 基数接頭辞つきは i/u のみ(16進の f は数字)、10進は i/u/f *)
  let suffix_at =
    let is_suffix_char c = c = 'i' || c = 'u' || (c = 'f' && not has_radix_prefix) in
    let rec find i = if i >= len then None else if is_suffix_char text.[i] then Some i else find (i + 1) in
    find (if has_radix_prefix then 2 else 0)
  in
  let lexically_float body =
    (not has_radix_prefix) && String.exists (fun c -> c = '.' || c = 'e' || c = 'E') body
  in
  match suffix_at with
  | None -> { n_text = text; n_is_float = lexically_float text; n_suffix = None }
  | Some i ->
      let body = String.sub text 0 i in
      let width = int_of_string (String.sub text (i + 1) (len - i - 1)) in
      let suffix = match text.[i] with 'i' -> NsInt width | 'u' -> NsUInt width | _ -> NsFloat width in
      let is_float = match suffix with NsFloat _ -> true | _ -> lexically_float body in
      { n_text = body; n_is_float = is_float; n_suffix = Some suffix }

let show_number { n_text; n_suffix; _ } =
  let suffix =
    match n_suffix with
    | None -> ""
    | Some (NsInt w) -> "i" ^ string_of_int w
    | Some (NsUInt w) -> "u" ^ string_of_int w
    | Some (NsFloat w) -> "f" ^ string_of_int w
  in
  n_text ^ suffix

(* ---- sedlex 正規表現 ---- *)

let digit = [%sedlex.regexp? '0' .. '9']

let hex_digit = [%sedlex.regexp? '0' .. '9' | 'a' .. 'f' | 'A' .. 'F']

let idchar = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9']

let int_suffix = [%sedlex.regexp? ('i' | 'u'), Plus digit]

let dec_number =
  [%sedlex.regexp?
    ( digit,
      Star (digit | '_'),
      Opt ('.', digit, Star (digit | '_')),
      Opt (('e' | 'E'), Opt ('+' | '-'), Plus digit),
      Opt (('i' | 'u' | 'f'), Plus digit) )]

let hex_number = [%sedlex.regexp? "0x", hex_digit, Star (hex_digit | '_'), Opt int_suffix]

let oct_number = [%sedlex.regexp? "0o", '0' .. '7', Star ('0' .. '7' | '_'), Opt int_suffix]

let bin_number = [%sedlex.regexp? "0b", ('0' | '1'), Star ('0' | '1' | '_'), Opt int_suffix]

module Make (Data : Syntax.Data) = struct
  module Parser = Parser.Make (Data)
  open Parser

  let lexeme = Sedlexing.Utf8.lexeme

  let cur_pos lexbuf = fst (Sedlexing.lexing_positions lexbuf)

  (* ---- 生トークン層 ---- *)

  let keyword_or_ident = function
    | "_" -> LOWLINE (* 単独の _ のみ。_item / _0 は識別子(§5.1) *)
    | "and" -> AND
    | "case" -> CASE
    | "class" -> CLASS
    | "derive" -> DERIVE
    | "effect" -> EFFECT
    | "extends" -> EXTENDS
    | "extern" -> EXTERN
    | "false" -> BOOL false
    | "fn" -> FN
    | "handle" -> HANDLE
    | "if" -> IF
    | "instance" -> INSTANCE
    | "let" -> LET
    | "match" -> MATCH
    | "module" -> MODULE
    | "newtype" -> NEWTYPE
    | "perform" -> PERFORM
    | "pub" -> PUB
    | "rec" -> REC
    | "resume" -> RESUME
    | "run" -> RUN
    | "true" -> BOOL true
    | "type" -> TYPE
    | "val" -> VAL
    | "with" -> WITH
    | id -> LOWER_IDENTIFIER id

  (* 連続する改行・空白を1個の NL に潰す(改行の行カウントは sedlex 3.x が自動追跡する。
     コメントは潰さない — 後続のコメント処理がもう1個 NL を出しうるが、ASI 層が自然に破棄する) *)
  let rec skip_newlines lexbuf =
    match%sedlex lexbuf with
    | '\n' -> skip_newlines lexbuf
    | Plus (' ' | '\t' | '\r') -> skip_newlines lexbuf
    | _ -> Sedlexing.rollback lexbuf

  (* 入れ子ブロックコメント。改行を含んでいたかを返す(§5.2) *)
  let read_block_comment lexbuf =
    let saw_nl = ref false in
    let rec go depth =
      if depth = 0 then !saw_nl
      else
        match%sedlex lexbuf with
        | "/*" -> go (depth + 1)
        | "*/" -> go (depth - 1)
        | '\n' ->
            saw_nl := true;
            go depth
        | eof -> raise (Lex_error ("unterminated block comment", cur_pos lexbuf))
        | any -> go depth
        | _ -> raise (Lex_error ("unterminated block comment", cur_pos lexbuf))
    in
    go 1

  let skip_rest_of_line lexbuf = match%sedlex lexbuf with Star (Compl '\n') -> () | _ -> ()

  let read_unicode_escape lexbuf limit =
    let rec loop acc i =
      if i = limit then
        if Uchar.is_valid acc then Uchar.of_int acc
        else raise (Lex_error ("invalid unicode escape (out of range or surrogate)", cur_pos lexbuf))
      else
        let ret base_char base_value =
          loop ((acc * 16) + (Uchar.to_int (Sedlexing.lexeme_char lexbuf 0) - Char.code base_char) + base_value) (i + 1)
        in
        match%sedlex lexbuf with
        | '0' .. '9' -> ret '0' 0
        | 'a' .. 'f' -> ret 'a' 10
        | 'A' .. 'F' -> ret 'A' 10
        | _ -> raise (Lex_error ("unexpected end of unicode escape", cur_pos lexbuf))
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
    | _ -> raise (Lex_error ("invalid escape sequence", cur_pos lexbuf))

  let read_text lexbuf =
    let buf = Buffer.create 64 in
    let rec aux () =
      match%sedlex lexbuf with
      | '"' -> Buffer.contents buf
      | eof -> raise (Lex_error ("unterminated string literal", cur_pos lexbuf))
      | '\\' ->
          Buffer.add_utf_8_uchar buf (read_escape lexbuf);
          aux ()
      | '\n' ->
          Buffer.add_char buf '\n';
          aux ()
      | any ->
          Buffer.add_string buf (lexeme lexbuf);
          aux ()
      | _ -> raise (Lex_error ("unterminated string literal", cur_pos lexbuf))
    in
    aux ()

  type entry = { tok : token; sp : Lexing.position; ep : Lexing.position }

  let rec read_raw_token lexbuf =
    let here tok =
      let sp, ep = Sedlexing.lexing_positions lexbuf in
      { tok; sp; ep }
    in
    match%sedlex lexbuf with
    | Plus (' ' | '\t' | '\r') -> read_raw_token lexbuf
    | '\n' ->
        let sp, ep = Sedlexing.lexing_positions lexbuf in
        skip_newlines lexbuf;
        { tok = NL; sp; ep }
    | "//", Star (Compl '\n') -> read_raw_token lexbuf
    | "/*" -> if read_block_comment lexbuf then here NL else read_raw_token lexbuf
    | "#!" ->
        (* shebang はオフセット0のときだけ(§5.2) *)
        if Sedlexing.lexeme_start lexbuf = 0 then (
          skip_rest_of_line lexbuf;
          read_raw_token lexbuf)
        else raise (Lex_error ("stray '#!'", cur_pos lexbuf))
    | "???" -> here HOLE
    | "..." -> here DOTDOTDOT
    | "=>" -> here EQ_GREATER
    | "==" -> here BIG_EQ
    | "!=" -> here EXCLAMATION_EQ
    | "<=" -> here LESS_EQ
    | ">=" -> here GREATER_EQ
    | "&&" -> here BIG_AMPERSAND
    | "||" -> here BIG_VERTICAL
    | 'A' .. 'Z', Star idchar -> here (UPPER_IDENTIFIER (lexeme lexbuf))
    | ('a' .. 'z' | '_'), Star idchar -> here (keyword_or_ident (lexeme lexbuf))
    | '#', 'A' .. 'Z', Star idchar ->
        let s = lexeme lexbuf in
        here (HASH_IDENT (String.sub s 1 (String.length s - 1)))
    | hex_number | oct_number | bin_number | dec_number -> here (NUMBER (parse_number (lexeme lexbuf)))
    | '"' ->
        let sp, _ = Sedlexing.lexing_positions lexbuf in
        let s = read_text lexbuf in
        let _, ep = Sedlexing.lexing_positions lexbuf in
        { tok = TEXT s; sp; ep }
    | '(' -> here LPAREN
    | ')' -> here RPAREN
    | '[' -> here LBRACKET
    | ']' -> here RBRACKET
    | '{' -> here LBRACE_BLOCK (* 未分類プレースホルダ。再分類層が確定する *)
    | '}' -> here RBRACE
    | '=' -> here EQ
    | ':' -> here COLON
    | ',' -> here COMMA
    | ';' -> here SEMI
    | '.' -> here DOT
    | '@' -> here AT
    | '+' -> here PLUS
    | '-' -> here HYPHEN
    | '*' -> here ASTERISK
    | '/' -> here SOLIDUS
    | '!' -> here EXCLAMATION
    | '<' -> here LESS
    | '>' -> here GREATER
    | '|' -> here VERTICAL
    | '\\' -> here BACKSLASH
    | eof -> here EOF
    | any -> raise (Lex_error ("unexpected character: " ^ lexeme lexbuf, cur_pos lexbuf))
    | _ -> raise (Lex_error ("unexpected input", cur_pos lexbuf))

  (* ---- 再分類層 + ASI 層 ---- *)

  (* region(§5.4-2):
     RBlock = 文区切り region(LBRACE_BLOCK)、
     RSuppress = NL 抑止 region(丸/角括弧・LBRACE_RECORD・LBRACE_TYPE)、
     RClause = case パターン(EQ_GREATER で pop。既存バグ 0.2-14 の修正) *)
  type region = RTop | RBlock | RSuppress | RClause

  type t = {
    lexbuf : Sedlexing.lexbuf;
    mutable pending : entry list; (* 生トークンの先読みキュー(先頭が次) *)
    mutable regions : region list;
    mutable prev : token option; (* 直前に消費者へ渡した有意トークン *)
    mutable last_sp : Lexing.position; (* 直近に消費者へ渡したトークンの位置(エラー報告用) *)
    mutable last_ep : Lexing.position;
  }

  let from_sedlex lexbuf =
    {
      lexbuf;
      pending = [];
      regions = [ RTop ];
      prev = None;
      last_sp = Lexing.dummy_pos;
      last_ep = Lexing.dummy_pos;
    }

  let from_string source = Sedlexing.Utf8.from_string source |> from_sedlex

  let from_channel channel = Sedlexing.Utf8.from_channel channel |> from_sedlex

  let from_filename filename =
    let lexbuf = Sedlexing.Utf8.from_channel (open_in_bin filename) in
    Sedlexing.set_filename lexbuf filename;
    from_sedlex lexbuf

  let rec peek t i =
    if List.length t.pending <= i then (
      t.pending <- t.pending @ [ read_raw_token t.lexbuf ];
      peek t i)
    else List.nth t.pending i

  (* NL を飛ばして k 個目(0始まり)の有意トークンを覗く *)
  let peek_sig t k =
    let rec go i k =
      let e = peek t i in
      match e.tok with NL -> go (i + 1) k | _ -> if k = 0 then e else go (i + 1) (k - 1)
    in
    go 0 k

  let is_ident_tok = function LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ -> true | _ -> false

  (* §5.3 の表。t1 = `{` の次、t2 = その次(NL スキップ) *)
  let classify_brace t =
    let t1 = (peek_sig t 0).tok in
    match t1 with
    | RBRACE | EXTENDS -> LBRACE_RECORD
    | _ when is_ident_tok t1 -> (
        match (peek_sig t 1).tok with
        | COLON -> LBRACE_TYPE
        | EQ | COMMA | WITH | EXTENDS -> LBRACE_RECORD
        | _ -> LBRACE_BLOCK)
    | _ -> LBRACE_BLOCK

  let pop_reclassified t =
    let e =
      match t.pending with
      | e :: rest ->
          t.pending <- rest;
          e
      | [] -> read_raw_token t.lexbuf
    in
    match e.tok with LBRACE_BLOCK -> { e with tok = classify_brace t } | _ -> e

  (* §5.4-1 の述語(既存バグ 0.2-12: 中身を入れ替えたうえで改名済み) *)

  (* NL の前に来てよい = 文終端になれる *)
  let can_end_statement = function
    | RPAREN | RBRACKET | RBRACE | LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ | HASH_IDENT _ | NUMBER _ | TEXT _
    | BOOL _ | HOLE ->
        true
    | _ -> false

  (* NL の後で文を開始できる。AND / CASE / MATCH / HANDLE / DOT / BACKSLASH /
     EXTENDS / VERTICAL / 二項演算子群は意図的に除外(行継続、§5.4) *)
  let can_begin_statement = function
    | LET | TYPE | NEWTYPE | EFFECT | MODULE | PUB | EXTERN | VAL | DERIVE | WITH | PERFORM | RESUME | RUN | FN
    | LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ | HASH_IDENT _ | NUMBER _ | TEXT _ | BOOL _ | HOLE | EXCLAMATION
    | LBRACE_BLOCK | LBRACE_RECORD | LBRACE_TYPE | LPAREN ->
        true
    | _ -> false

  let rec read_token t =
    let e = pop_reclassified t in
    match e.tok with
    | NL -> (
        match t.regions with
        | (RSuppress | RClause) :: _ -> read_token t
        | _ ->
            let keep =
              match t.prev with
              | Some p -> can_end_statement p && can_begin_statement (peek_sig t 0).tok
              | None -> false
            in
            if keep then (
              t.prev <- Some NL;
              e)
            else read_token t)
    | tok ->
        (match tok with
        | LPAREN | LBRACKET | LBRACE_RECORD | LBRACE_TYPE -> t.regions <- RSuppress :: t.regions
        | LBRACE_BLOCK -> t.regions <- RBlock :: t.regions
        | RPAREN | RBRACKET | RBRACE -> (
            match t.regions with _ :: (_ :: _ as tl) -> t.regions <- tl | _ -> ())
        | CASE -> t.regions <- RClause :: t.regions
        | EQ_GREATER -> (
            (* 既知の制限: ガード内の fn(x) => は内側の => で先に pop する(§5.4-3) *)
            match t.regions with RClause :: (_ :: _ as tl) -> t.regions <- tl | _ -> ())
        | _ -> ());
        t.prev <- Some tok;
        e

  (* ---- 消費者 API ---- *)

  let read t =
    let e = read_token t in
    t.last_sp <- e.sp;
    t.last_ep <- e.ep;
    (e.tok, e.sp, e.ep)

  let parse rule lexer = MenhirLib.Convert.Simplified.traditional2revised rule (fun () -> read lexer)

  (* --dump-tokens 用: ASI 適用後のトークン列を EOF まで *)
  let all_tokens t =
    let rec go acc =
      let e = read_token t in
      match e.tok with EOF -> List.rev (e :: acc) | _ -> go (e :: acc)
    in
    go []

  let show_token = function
    | AND -> "and"
    | AT -> "@"
    | ASTERISK -> "*"
    | BACKSLASH -> "\\"
    | BIG_AMPERSAND -> "&&"
    | BIG_EQ -> "=="
    | BIG_VERTICAL -> "||"
    | BOOL b -> string_of_bool b
    | CASE -> "case"
    | CLASS -> "class"
    | COLON -> ":"
    | COMMA -> ","
    | DERIVE -> "derive"
    | DOT -> "."
    | DOTDOTDOT -> "..."
    | EFFECT -> "effect"
    | EOF -> "<EOF>"
    | EQ -> "="
    | EQ_GREATER -> "=>"
    | EXCLAMATION -> "!"
    | EXCLAMATION_EQ -> "!="
    | EXTENDS -> "extends"
    | EXTERN -> "extern"
    | FN -> "fn"
    | GREATER -> ">"
    | GREATER_EQ -> ">="
    | HANDLE -> "handle"
    | HASH_IDENT s -> "#" ^ s
    | HOLE -> "???"
    | HYPHEN -> "-"
    | IF -> "if"
    | INSTANCE -> "instance"
    | LBRACE_BLOCK -> "{blk"
    | LBRACE_RECORD -> "{rec"
    | LBRACE_TYPE -> "{ty"
    | LBRACKET -> "["
    | LESS -> "<"
    | LESS_EQ -> "<="
    | LET -> "let"
    | LOWER_IDENTIFIER s -> s
    | LOWLINE -> "_"
    | LPAREN -> "("
    | MATCH -> "match"
    | MODULE -> "module"
    | NEWTYPE -> "newtype"
    | NL -> "<NL>"
    | NUMBER n -> show_number n
    | PERFORM -> "perform"
    | PLUS -> "+"
    | PUB -> "pub"
    | RBRACE -> "}"
    | RBRACKET -> "]"
    | REC -> "rec"
    | RESUME -> "resume"
    | RPAREN -> ")"
    | RUN -> "run"
    | SEMI -> ";"
    | SOLIDUS -> "/"
    | TEXT s -> "\"" ^ String.escaped s ^ "\""
    | TYPE -> "type"
    | UPPER_IDENTIFIER s -> s
    | VAL -> "val"
    | VERTICAL -> "|"
    | WITH -> "with"
end
