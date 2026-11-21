(* Copyright (C) 2018 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第16章の付録 実行ファイルのエントリポイント

   解説は第16章(lib/driver.ml)の §16.9 にある。
   このファイルは、そこで述べた方針の実例である。

   dune は実行ファイル(このディレクトリ)とライブラリ(lib/)を分けている。
   実行ファイルが持つモジュールはこの 1 つだけで、内容も 1 行だけである。

   実行ファイルの main には、ライブラリの関数を 1 つ呼ぶこと以外は書かない。
   処理を追加したくなったら、ライブラリの側に追加する。
   ここに処理を書くと、その処理を通るのは CLI だけになり、
   `Driver.eval_string` などの API で Diktor をライブラリとして使うプログラムは通らない。
   CLI と API の経路がこうして分かれても、コンパイルエラーは 1 つも出ないので、
   分かれたことに気づけない。 *)
let () = Diktor.Driver.main ()
