(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* ## 1.19 位置 — location.ml

   第1章の最後の脇役です。宣言は 4 つ、コードは 12 行しかありませんが、
   この 12 行のために AST の形が決まりました (§1.13)。

   位置は `Lexing.position` をそのまま使い、`span` で始点と終点を
   組にします。独自の行・桁の表現を作らないのは、`Lexing.position` が
   sedlex と Menhir の両方の共通通貨だからです。字句層は
   `(トークン, 始点, 終点)` の三つ組でトークンを運び、Menhir の
   `$sloc` がそのまま `span` になります (D16)。以前はトークン自身が
   位置をペイロードとして持っていて、位置が 2 トークンぶんずれる
   バグの温床でした。

   ### なぜ全ノードに持たせたのか

   エラーに位置を出すには、位置は**全ノード**に必要です。後から
   一部のノードにだけ足すことはできません。足したい場所は
   たいてい、位置を持っていないノードだからです。MiniLang のまとめも
   「型に出所(ソース位置)を持たせるのは、実用上は最重要の改善点」と
   書いています。だから `Data.allocate` の引数を `unit` から `span` に
   変え (§1.13)、すべてのノードが位置の置き場所を持つようにしました。

   接続は**済んでいます**(E1 / D53)。第5章の `ElabData.loc` に入った
   全ノードの位置を、第11章の `at_node` が型エラーに貼り、この章の
   `show_pos` / `start_of` が `ファイル:行:桁` に整形します。字句エラーと
   構文エラー(第16章)も同じ `show_pos` の定義で出ます。

   ### 細部

   `dummy_span` の判定に `==`(物理等価)を使っています。
   `Lexing.dummy_pos` は 1 個の共有された値なので、これが真になるのは
   `dummy_span` 由来の位置だけです。構造比較でも同じ結果になりますが、
   意図が「同じ値か」ではなく「あの穴埋めそのものか」なので
   物理等価のほうが正確です。

   桁は 1 起点です (`pos_cnum - pos_bol + 1`)。行が同じなら
   `行:桁-桁`、またぐなら `行:桁-行:桁` と縮めます。長い span を
   2 行ぶん書くと、エラーメッセージの本文より位置のほうが長くなります。 *)

type t = Lexing.position

type span = { start : Lexing.position; finish : Lexing.position }

let dummy_span = { start = Lexing.dummy_pos; finish = Lexing.dummy_pos }

let show_span { start; finish } =
  let line p = p.Lexing.pos_lnum in
  let col p = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  if start == Lexing.dummy_pos then "<unknown>"
  else if line start = line finish then Printf.sprintf "%d:%d-%d" (line start) (col start) (col finish)
  else Printf.sprintf "%d:%d-%d:%d" (line start) (col start) (line finish) (col finish)

(* 位置の表示 ファイル:行:桁(E1 / D53)。桁は行頭からのコードポイント差 + 1 —
   バイト差ではないこと(sedlex の Utf8 がコードポイントで数える)は第16章
   §16.3 の実測が根拠で、その不変条件はこの定義に引き継がれた *)
let show_pos (p : Lexing.position) =
  Printf.sprintf "%s:%d:%d" p.Lexing.pos_fname p.Lexing.pos_lnum (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1)

(* span の開始位置の表示。穴埋め(dummy)なら None。終端は出さない —
   長い span を 2 行ぶん書くと、本文より位置のほうが長くなる *)
let start_of { start; _ } = if start == Lexing.dummy_pos then None else Some (show_pos start)
