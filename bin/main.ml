(* Copyright (C) 2018 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第16章 付録 — 実行形の入口

   本文は第16章 (lib/driver.ml) の §16.9 にあります。ここはそこで語った
   方針の実物です。

   dune は実行形 (このディレクトリ) とライブラリ (lib/) を分けており、
   実行形が持つモジュールはこの 1 つだけ。中身も 1 行だけです。

   その 1 行に処理を足したくなったら、足す先は必ずライブラリ側です。
   ここに書いた処理は、Diktor をライブラリとして使う人からも、
   `Driver.eval_string` を呼ぶテストからも見えません。CLI だけが通る道が
   できた瞬間に、計画 §8.7 の「CLI とテストが同じ経路を通る」という約束が、
   コンパイルエラーを 1 つも出さずに静かに壊れます。

   > 実行形の main には、ライブラリの関数を 1 つ呼ぶ以上のことを書かない。 *)
let () = Diktor.Driver.main ()
