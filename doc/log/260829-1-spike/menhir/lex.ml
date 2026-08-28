(* 手書きレキサ (spike 用)。sedlex を使わず、計画書 §5.2-§5.5 の規則を再現する:
   - コメント (// と入れ子 /* */)、shebang
   - `{` の 3-way 再分類 (§5.3, NL を跨いだ 2 トークン先読み)
   - ASI (§5.4, region スタック + can_end/can_begin 述語)
   本番実装ではないが、文法の実証に必要な範囲は忠実にする。 *)

open Kel

type tok = { t : token; line : int }

exception Lex_error of string * int

let is_digit c = c >= '0' && c <= '9'
let is_lower c = c >= 'a' && c <= 'z'
let is_upper c = c >= 'A' && c <= 'Z'
let is_ident_start c = is_lower c || is_upper c || c = '_'
let is_ident c = is_ident_start c || is_digit c

let keyword = function
  | "let" -> Some LET
  | "rec" -> Some REC
  | "and" -> Some AND
  | "type" -> Some TYPE
  | "class" -> Some CLASS
  | "instance" -> Some INSTANCE
  | "newtype" -> Some NEWTYPE
  | "effect" -> Some EFFECT
  | "module" -> Some MODULE
  | "pub" -> Some PUB
  | "extern" -> Some EXTERN
  | "fn" -> Some FN
  | "match" -> Some MATCH
  | "handle" -> Some HANDLE
  | "case" -> Some CASE
  | "if" -> Some IF
  | "perform" -> Some PERFORM
  | "resume" -> Some RESUME
  | "run" -> Some RUN
  | "with" -> Some WITH
  | "extends" -> Some EXTENDS
  | "derive" -> Some DERIVE
  | "val" -> Some VAL
  | "true" -> Some (BOOL true)
  | "false" -> Some (BOOL false)
  | _ -> None

(* ---------- pass 1: 生トークン列 (LBRACE_BLOCK は未分類のプレースホルダ) ---------- *)

let raw_tokens (src : string) : tok list =
  let n = String.length src in
  let out = ref [] in
  let line = ref 1 in
  let emit t = out := { t; line = !line } :: !out in
  let i = ref 0 in
  (* shebang *)
  if n >= 2 && src.[0] = '#' && src.[1] = '!' then
    while !i < n && src.[!i] <> '\n' do incr i done;
  while !i < n do
    let c = src.[!i] in
    if c = '\n' then (emit NL; incr line; incr i)
    else if c = ' ' || c = '\t' || c = '\r' then incr i
    else if c = '/' && !i + 1 < n && src.[!i + 1] = '/' then
      while !i < n && src.[!i] <> '\n' do incr i done
    else if c = '/' && !i + 1 < n && src.[!i + 1] = '*' then begin
      (* 入れ子ブロックコメント。改行を含んでいたら NL 1 個として振る舞う (§5.2) *)
      let depth = ref 0 in
      let saw_nl = ref false in
      let fin = ref false in
      while not !fin do
        if !i >= n then raise (Lex_error ("unterminated block comment", !line));
        if !i + 1 < n && src.[!i] = '/' && src.[!i + 1] = '*' then (incr depth; i := !i + 2)
        else if !i + 1 < n && src.[!i] = '*' && src.[!i + 1] = '/' then begin
          decr depth; i := !i + 2; if !depth = 0 then fin := true
        end else begin
          if src.[!i] = '\n' then (saw_nl := true; incr line);
          incr i
        end
      done;
      if !saw_nl then emit NL
    end
    else if c = '"' then begin
      incr i;
      let b = Buffer.create 16 in
      let fin = ref false in
      while not !fin do
        if !i >= n then raise (Lex_error ("unterminated string", !line));
        (match src.[!i] with
         | '"' -> fin := true; incr i
         | '\\' ->
           if !i + 1 >= n then raise (Lex_error ("bad escape", !line));
           Buffer.add_char b src.[!i + 1]; i := !i + 2
         | ch -> (if ch = '\n' then incr line); Buffer.add_char b ch; incr i)
      done;
      emit (TEXT (Buffer.contents b))
    end
    else if is_digit c then begin
      let s = !i in
      while !i < n && (is_ident src.[!i]) do incr i done;
      (* 小数点 + 指数 *)
      if !i < n && src.[!i] = '.' && !i + 1 < n && is_digit src.[!i + 1] then begin
        incr i;
        while !i < n && is_ident src.[!i] do incr i done
      end;
      emit (NUMBER (String.sub src s (!i - s)))
    end
    else if is_ident_start c then begin
      let s = !i in
      while !i < n && is_ident src.[!i] do incr i done;
      let w = String.sub src s (!i - s) in
      if w = "_" then emit LOWLINE
      else match keyword w with
        | Some t -> emit t
        | None -> if is_upper w.[0] then emit (UPPER_IDENTIFIER w) else emit (LOWER_IDENTIFIER w)
    end
    else if c = '#' then begin
      incr i;
      if !i < n && is_upper src.[!i] then begin
        let s = !i in
        while !i < n && is_ident src.[!i] do incr i done;
        emit (HASH_IDENT (String.sub src s (!i - s)))
      end else raise (Lex_error ("stray '#'", !line))
    end
    else begin
      let two = if !i + 1 < n then String.sub src !i 2 else "" in
      let three = if !i + 2 < n then String.sub src !i 3 else "" in
      match three with
      | "???" -> emit HOLE; i := !i + 3
      | "..." -> emit DOTDOTDOT; i := !i + 3
      | _ ->
        (match two with
         | "=>" -> emit EQ_GREATER; i := !i + 2
         | "==" -> emit BIG_EQ; i := !i + 2
         | "!=" -> emit EXCLAMATION_EQ; i := !i + 2
         | "<=" -> emit LESS_EQ; i := !i + 2
         | ">=" -> emit GREATER_EQ; i := !i + 2
         | "&&" -> emit BIG_AMPERSAND; i := !i + 2
         | "||" -> emit BIG_VERTICAL; i := !i + 2
         | _ ->
           incr i;
           (match c with
            | '(' -> emit LPAREN | ')' -> emit RPAREN
            | '[' -> emit LBRACKET | ']' -> emit RBRACKET
            | '{' -> emit LBRACE_BLOCK (* 未分類 *) | '}' -> emit RBRACE
            | '=' -> emit EQ | ':' -> emit COLON | ',' -> emit COMMA | ';' -> emit SEMI
            | '.' -> emit DOT | '@' -> emit AT | '+' -> emit PLUS | '-' -> emit HYPHEN
            | '*' -> emit ASTERISK | '/' -> emit SOLIDUS | '!' -> emit EXCLAMATION
            | '<' -> emit LESS | '>' -> emit GREATER | '|' -> emit VERTICAL
            | '\\' -> emit BACKSLASH
            | _ -> raise (Lex_error (Printf.sprintf "unexpected char %C" c, !line))))
    end
  done;
  emit EOF;
  List.rev !out

(* ---------- pass 2: `{` の 3-way 再分類 (§5.3) ---------- *)

let reclassify (ts : tok array) : unit =
  let n = Array.length ts in
  let next_sig from =
    let j = ref from in
    while !j < n && ts.(!j).t = NL do incr j done;
    if !j < n then Some !j else None
  in
  for i = 0 to n - 1 do
    if ts.(i).t = LBRACE_BLOCK then begin
      let cls =
        match next_sig (i + 1) with
        | None -> LBRACE_BLOCK
        | Some j ->
          let t1 = ts.(j).t in
          let t2 = match next_sig (j + 1) with Some k -> Some ts.(k).t | None -> None in
          let is_ident = function LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ -> true | _ -> false in
          (match t1 with
           | RBRACE -> LBRACE_RECORD
           | EXTENDS -> LBRACE_RECORD
           | _ when is_ident t1 ->
             (match t2 with
              | Some COLON -> LBRACE_TYPE
              | Some (EQ | COMMA | WITH | EXTENDS) -> LBRACE_RECORD
              | _ -> LBRACE_BLOCK)
           | _ -> LBRACE_BLOCK)
      in
      ts.(i) <- { ts.(i) with t = cls }
    end
  done

(* ---------- pass 3: ASI (§5.4) ---------- *)

type region = Top | InBrace | InParen | InClause

let can_end_statement = function
  | RPAREN | RBRACKET | RBRACE
  | LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ | HASH_IDENT _
  | NUMBER _ | TEXT _ | BOOL _ | HOLE -> true
  | _ -> false

let can_begin_statement = function
  | LET | TYPE | NEWTYPE | EFFECT | MODULE | PUB | EXTERN
  (* [FIX-11] 計画書 §5.4 の一覧に無いが、クラス本体の項目を分けるのに必須 *)
  | VAL | DERIVE
  | WITH | PERFORM | RESUME | RUN | FN
  | LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ | HASH_IDENT _
  | NUMBER _ | TEXT _ | BOOL _ | HOLE | EXCLAMATION
  | LBRACE_BLOCK | LBRACE_RECORD | LBRACE_TYPE | LPAREN -> true
  | _ -> false

let asi (ts : tok array) : tok list =
  let n = Array.length ts in
  let out = ref [] in
  let stack = ref [ Top ] in
  let prev = ref None in
  let next_sig from =
    let j = ref from in
    while !j < n && ts.(!j).t = NL do incr j done;
    if !j < n then Some ts.(!j).t else None
  in
  for i = 0 to n - 1 do
    let tk = ts.(i) in
    match tk.t with
    | NL ->
      let head = List.hd !stack in
      let keep =
        (match head with
         | InParen | InClause -> false
         | _ ->
           (match !prev, next_sig (i + 1) with
            | Some p, Some nx -> can_end_statement p && can_begin_statement nx
            | _ -> false))
      in
      if keep then (out := tk :: !out; prev := Some NL)
    | t ->
      (match t with
       | LPAREN | LBRACKET -> stack := InParen :: !stack
       | LBRACE_BLOCK | LBRACE_RECORD | LBRACE_TYPE -> stack := InBrace :: !stack
       | RPAREN | RBRACKET | RBRACE ->
         (match !stack with _ :: (_ :: _ as tl) -> stack := tl | _ -> ())
       | CASE -> stack := InClause :: !stack
       | EQ_GREATER ->
         (match !stack with
          | InClause :: (_ :: _ as tl) -> stack := tl
          | _ -> ())
       | _ -> ());
      out := tk :: !out;
      prev := Some t
  done;
  List.rev !out

let tokenize src =
  let ts = Array.of_list (raw_tokens src) in
  reclassify ts;
  asi ts

let show = function
  | LET -> "let" | REC -> "rec" | AND -> "and" | TYPE -> "type" | CLASS -> "class"
  | INSTANCE -> "instance" | NEWTYPE -> "newtype" | EFFECT -> "effect" | MODULE -> "module"
  | PUB -> "pub" | EXTERN -> "extern" | FN -> "fn" | MATCH -> "match" | HANDLE -> "handle"
  | CASE -> "case" | IF -> "if" | PERFORM -> "perform" | RESUME -> "resume" | RUN -> "run"
  | WITH -> "with" | EXTENDS -> "extends" | DERIVE -> "derive" | VAL -> "val"
  | BOOL b -> string_of_bool b
  | LOWER_IDENTIFIER s -> s | UPPER_IDENTIFIER s -> s | TEXT s -> "\"" ^ s ^ "\""
  | NUMBER s -> s | HASH_IDENT s -> "#" ^ s
  | LPAREN -> "(" | RPAREN -> ")" | LBRACKET -> "[" | RBRACKET -> "]"
  | LBRACE_BLOCK -> "{blk" | LBRACE_RECORD -> "{rec" | LBRACE_TYPE -> "{ty" | RBRACE -> "}"
  | EQ -> "=" | COLON -> ":" | COMMA -> "," | SEMI -> ";" | DOT -> "." | AT -> "@"
  | PLUS -> "+" | HYPHEN -> "-" | ASTERISK -> "*" | SOLIDUS -> "/" | EXCLAMATION -> "!"
  | LESS -> "<" | GREATER -> ">" | VERTICAL -> "|" | BACKSLASH -> "\\"
  | EQ_GREATER -> "=>" | BIG_EQ -> "==" | EXCLAMATION_EQ -> "!=" | LESS_EQ -> "<="
  | GREATER_EQ -> ">=" | BIG_AMPERSAND -> "&&" | BIG_VERTICAL -> "||"
  | HOLE -> "???" | DOTDOTDOT -> "..." | LOWLINE -> "_" | NL -> "<NL>" | EOF -> "<EOF>"
