(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* ## 1.18 通し番号と例外の語彙 — aux.ml

   第1章の脇役です。実装のどこからでも開かれるので、置くものを
   厳しく絞ってあります — **通し番号**と**例外の語彙**だけです。

   ### oid

   `oid` は単なる `int` です。名前のインターン (§1.2)、型変数の識別
   (`vid`)、カインド変数 (`k_id`)、AST ノード (第5章の `ElabData.oid`) が
   同じカウンタを共有します。

   共有してよいのか、という疑問はもっともです。答えは「よい」。
   `oid` は**等値比較と表の鍵にしか使いません**。番号空間を分けても
   検査が強くなるわけではなく、型が 3 つ増えて変換が要るだけです。
   ある番号が何を指すかは、その番号を持っているフィールドが決めます。

   単調増加なので、番号の大小には意味があります — 小さいほど早く
   作られた、それだけです。第9章 (show.ml) は `vid` を採番表の**鍵**に
   使いますが、見せる名前は出現順のアルファベットに振り直します。
   番号をそのまま印字すると、同じプログラムでも前に何を型検査したかで
   表示が変わってしまうからです。

   `with_oid` と `concat_list_option` は小道具です。

   ### 例外の 3 系統

   例外の種類が、そのまま**誰の誤りか**の分類になっています。
   ここを混ぜると、内部矛盾がユーザ向けのエラーに化けて、
   バグが見えなくなります。

   | 例外 | 誰の誤りか | 投げる関数 | 終了コード |
   |---|---|---|---|
   | `Type_error` | ユーザのプログラム | `type_error` | 1 |
   | `NotImplemented` | v0 の未対応機能 | `noimpl` | 4 |
   | `Panic` | **実装の不変条件違反** | `bug` | 3 |

   `Panic` のメッセージには `[BUG]` が前置されます。これが出たら
   Diktor 側の欠陥であって、ユーザのプログラムがどう書かれていても
   出てはいけません。§1.8 の `row_append` が「左側が開いた行」で
   `bug` を呼ぶのがその典型で、そこへ到達しないことは呼び出し側
   (第11章)が保証しています。

   `NotImplemented` を `Type_error` と分けているのは、
   「書けるが未対応」と「書いてはいけない」を利用者が区別できる
   ようにするためです。`1u8` は前者(D13 により受理して未対応)、
   `1 + true` は後者です。

   終了コードの全体像 — 2 が字句・構文エラー、3 が実行時の異常、
   64 が使い方の誤り — は第16章 (driver.ml) にまとめてあります。 *)

let concat_list_option = function None -> [] | Some xs -> xs

type oid = int

let current_oid = ref 0

let new_oid () =
  let ret = !current_oid in
  current_oid := ret + 1;
  ret

let with_oid x = (new_oid (), x)

exception NotImplemented of string

let noimpl feat = raise (NotImplemented feat)

exception Panic of string

let bug msg = raise (Panic ("[BUG] " ^ msg))

exception Type_error of string

let type_error msg = raise (Type_error msg)
