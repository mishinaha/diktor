(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
 *
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * M1 の最小文法。M3 で spike(doc/log/260829-1-spike/menhir/kel.mly)を
 * 下敷きに全面実装する。旧 Orphos 文法は git 履歴 f0cafd4 を参照。
 *)
%parameter <Data : Syntax.Data>
%{
(* Workaround ocaml/dune#2450 *)
module Diktor = struct end

module Tree = Syntax.Make(Data)
%}

%token EOF

%start <Syntax.Make(Data).decl list> program

%%

program: EOF { [] }
