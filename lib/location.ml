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

   正直に書いておくと、**接続はまだ終わっていません**。
   第5章の `ElabData.loc` には全ノードの位置が入っていますが、
   第11章の型エラーはまだ `ファイル:行` を前置していません。
   字句エラーと構文エラー (第16章) は位置つきで出ます。
   残っているのは配線だけで、置き場所の設計はここで済んでいます。

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
