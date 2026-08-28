(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * トークンは計画 §5.1 の 64 個。文法本体は M3 で spike
 * (doc/log/260829-1-spike/menhir/kel.mly)を下敷きに実装する。
 * 旧 Orphos 文法は git 履歴 f0cafd4 を参照。
 *)
%parameter <Data : Syntax.Data>
%{
(* Workaround ocaml/dune#2450 *)
module Diktor = struct end

module Tree = Syntax.Make(Data)
%}

(* 維持(44個) *)
%token AND AT ASTERISK BIG_AMPERSAND BIG_EQ BIG_VERTICAL CASE COLON COMMA DOT
%token EFFECT EOF EQ EQ_GREATER EXCLAMATION EXCLAMATION_EQ FN GREATER HANDLE
%token HYPHEN IF LBRACKET LESS LET LOWLINE LPAREN MATCH MODULE NL PLUS RBRACKET
%token REC RPAREN SEMI SOLIDUS TYPE VAL VERTICAL WITH
%token <bool> BOOL
%token <string> LOWER_IDENTIFIER UPPER_IDENTIFIER TEXT
%token <Syntax.number> NUMBER

(* 新設(20個) *)
%token LBRACE_BLOCK LBRACE_RECORD LBRACE_TYPE RBRACE
%token BACKSLASH DOTDOTDOT LESS_EQ GREATER_EQ HOLE
%token CLASS INSTANCE DERIVE EXTENDS EXTERN NEWTYPE PERFORM PUB RESUME RUN
%token <string> HASH_IDENT

%start <Syntax.Make(Data).decl list> program

%%

program: EOF { [] }
