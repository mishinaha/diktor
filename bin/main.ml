(* Copyright (C) 2018 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第16章の付録 実行形の入口

   解説は第16章(lib/driver.ml)の §16.9 にある。
   このファイルは、そこで述べた方針の実例である。

   dune は実行形(このディレクトリ)とライブラリ(lib/)を分けている。
   実行形が持つモジュールはこの 1 つだけで、中身も 1 行だけである。

   実行形の main には、ライブラリの関数を 1 つ呼ぶこと以外は書かない。
   処理を足したくなったら、ライブラリの側に足す。
   ここに処理を書くと、その処理は CLI だけが通り、
   `Driver.eval_string` などの API で Diktor をライブラリとして使うプログラムは通らない。
   CLI と API の経路がこうして分かれても、コンパイルエラーは 1 つも出ないので、
   分かれたことに気づけない。 *)
let () = Diktor.Driver.main ()
