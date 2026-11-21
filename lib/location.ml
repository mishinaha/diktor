(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* ## 1.19 位置(location.ml)

   location.ml は第1章を補う最後のファイルである。
   宣言は 3 つ、コードは数行だけだが、AST の全ノードがこの `span` を持つ(§1.13)。

   位置には `Lexing.position` をそのまま使い、`span` は始点と終点の 2 つの位置を持つ。
   行と桁の表現を独自に作らないのは、
   `Lexing.position` が sedlex と Menhir の両方で使える共通の型だからである。
   字句層はトークンを `(トークン, 始点, 終点)` の三つ組で渡し、
   Menhir の `$sloc` がそのまま `span` になる。
   トークン自身は位置をペイロードとして持たない。

   ### 全ノードの位置と、その表示

   エラーに位置を表示するには、全ノードが位置を持っている必要がある。
   一部のノードにだけ後から位置を追加する方法では足りない。
   位置を表示したくなるノードは、たいてい位置を持っていないノードだからである。
   そのため `Data.allocate` は `span` を引数に取り(§1.13)、すべてのノードが位置を持つ。

   第5章の `ElabData.loc` に入った位置を、第11章の `at_node` が型エラーに付ける。
   それを本節の `show_pos` / `start_of` が `ファイル:行:桁` の形式に整形する。
   第16章は、字句エラーと構文エラーの位置も同じ `show_pos` で表示する。

   本節は開始位置を表示する関数だけを置き、範囲全体や終端を表示する関数は置かない。
   そうした関数を使う診断がなく、使われない関数の書式は誰にも検証されないからである。 *)

type span = { start : Lexing.position; finish : Lexing.position }

(* 位置を ファイル:行:桁 の形式の文字列にして返す。桁は行頭からのコードポイントの差 + 1 で、
   バイトの差ではない。sedlex の Utf8 がコードポイントで数えるからである(第16章 §16.3) *)
let show_pos (p : Lexing.position) =
  Printf.sprintf "%s:%d:%d" p.Lexing.pos_fname p.Lexing.pos_lnum (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1)

(* span の開始位置を表示用の文字列にして返す。位置が Lexing.dummy_pos なら None を返す。
   終端は表示しない。長い span の終端まで書くと、診断の本文より位置のほうが長くなるからである *)
let start_of { start; _ } = if start == Lexing.dummy_pos then None else Some (show_pos start)
