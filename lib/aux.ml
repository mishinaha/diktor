(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* ## 1.18 通し番号と例外の語彙(aux.ml)

   aux.ml は第1章を補うファイルである。
   実装のどこからでも開かれるので、置くものを通し番号と例外の語彙の 2 つに絞っている。

   ### oid

   `oid` はただの `int` である。
   名前のインターン(§1.2)、型変数の識別子(`vid`)、カインド変数(`k_id`)、
   AST のノード(第5章の `ElabData.oid`)が、同じカウンタを共有する。

   カウンタを共有しても差し支えない。
   `oid` は等値比較と表の鍵にしか使わないからである。
   番号空間を分けても検査は強くならず、型が 3 つ増えて変換が要るだけである。
   ある番号が何を指すかは、その番号を持つフィールドが決める。

   番号は単調に増えるので、大小には意味がある。
   ただし、その意味は小さい番号ほど早く作られたということだけである。
   第9章(show.ml)は `vid` を採番表の鍵に使うが、
   利用者に見せる名前は出現順のアルファベットに振り直す。
   番号をそのまま印字すると、同じプログラムでも、
   それより前に何を型検査したかで表示が変わるからである。

   ### 例外の 3 系統

   例外の種類は、誰の誤りかの分類に対応する。
   この分類を混ぜると、実装の内部矛盾が利用者向けのエラーとして現れ、実装の誤りが見えなくなる。

   | 例外 | 誰の誤りか | 投げる関数 | 終了コード |
   |---|---|---|---|
   | `Type_error` | 利用者のプログラム | `type_error` | 1 |
   | `Type_error_at` | 同上(位置つき) | 第11章の `at_node` | 1 |
   | `NotImplemented` | Diktor が実装していない機能 | `noimpl` | 4 |
   | `NotImplemented_at` | 同上(位置つき) | 第11章の `at_node` | 4 |
   | `Panic` | 実装の不変条件違反 | `bug` | 3 |

   `bug` は `Panic` のメッセージに `[BUG]` を前置する。
   `Panic` は Diktor 側の欠陥を表し、利用者のプログラムがどう書かれていても出てはならない。
   典型は §1.8 の `row_append` で、左側が開いた行で右側が空でないときに `bug` を呼ぶ。
   そこへ到達しないことは、呼び出し側の第11章が保証している。

   `NotImplemented` を `Type_error` と分けるのは、
   書けるが実装されていないものと、書いてはならないものを、利用者が区別できるようにするためである。
   `1u8`、`Int8`、`module` の入れ子、`cancel(reason)` は、Diktor が実装していない機能である。
   第11章はこれらに対して `noimpl` を呼び、第16章は終了コード 4 で終える。
   `1 + true` は書いてはならないものなので、第8章の `add_class` が `type_error` を呼び、
   第16章は終了コード 1 で終える。
   利用者は終了コードを見れば、Diktor の未実装に当たったのか、
   プログラムを書き直す必要があるのかが分かる。

   `noimpl` の例外も、型エラーと同じ診断の流れに乗る。
   第11章の `type_check` が `NotImplemented` を捕まえ、そこまでに出せた型の行と未実装の診断を返す。
   第16章はそれを、型の行に続く `! ファイル:行:桁: 未実装: …` の行(位置が無いときは `! 未実装: …`)として印字し、
   終了コード 4 で終える。
   受け皿の第16章にしか捕まえる節が無いと、そこまでの型の行がすべて消える。
   そのため、第11章と第16章の両方に節を置く(§16.8)。

   終了コードの全体は、第16章(driver.ml)の §16.8 にまとめてある。
   表に無い終了コードは、2 が字句エラーと構文エラー、64 が使い方の誤り、74 が出力の失敗である。
   3 は `Panic` のほか、実行時エラーにも使う。 *)


type oid = int

let current_oid = ref 0

let new_oid () =
  let ret = !current_oid in
  current_oid := ret + 1;
  ret


exception NotImplemented of string

let noimpl feat = raise (NotImplemented feat)

exception Panic of string

let bug msg = raise (Panic ("[BUG] " ^ msg))

exception Type_error of string

let type_error msg = raise (Type_error msg)

(* 位置つきの型エラー。第11章の at_node が、
   位置なしの Type_error に最内ノードの span を貼って投げ直す。
   Type_error を捕まえる節は 3 種類に分かれ、それぞれ次の義務を負う。
   (a) 精緻化を包んで握り潰す節(signature_of_binding、newtype と型エイリアスの投機)と、
   (b) 受け皿(Elab.type_check、Driver.type_check_files の平坦化、Driver.main)は、
   Type_error_at も必ず捕まえる。
   (c) Unify の関数(unify、rewrite_row)だけを包む節は、言い換えるにせよ握り潰すにせよ、
   Type_error_at を捕まえなくてよい。
   Unify は位置を知らないので、そこから Type_error_at は出ない *)
exception Type_error_at of Location.span * string

(* 位置つきの未実装。at_node は NotImplemented にも同じ規則で span を貼る *)
exception NotImplemented_at of Location.span * string
