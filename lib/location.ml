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

   かつてここには `type t`(旧実装がトークンに載せていた位置の型)、
   `dummy_span`、範囲ごと印字する `show_span` がありましたが、E1 の配線が
   `show_pos` / `start_of`(開始位置だけを `ファイル:行:桁` で出す)で
   完成したため、呼び出し元の無い 3 つは消しました (M19 / G1f)。範囲の
   終端を見せる診断が要るようになったら、そのときの書式で書き直すほうが
   よい — 使われない関数の書式は誰にも検証されません。 *)

type span = { start : Lexing.position; finish : Lexing.position }

(* 位置の表示 ファイル:行:桁(E1 / D53)。桁は行頭からのコードポイント差 + 1 —
   バイト差ではないこと(sedlex の Utf8 がコードポイントで数える)は第16章
   §16.3 の実測が根拠で、その不変条件はこの定義に引き継がれた *)
let show_pos (p : Lexing.position) =
  Printf.sprintf "%s:%d:%d" p.Lexing.pos_fname p.Lexing.pos_lnum (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1)

(* span の開始位置の表示。穴埋め(dummy)なら None。終端は出さない —
   長い span を 2 行ぶん書くと、本文より位置のほうが長くなる *)
let start_of { start; _ } = if start == Lexing.dummy_pos then None else Some (show_pos start)
