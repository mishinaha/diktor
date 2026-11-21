(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* ## 1.18 通し番号と例外の語彙(aux.ml)

   aux.ml は第1章を補うファイルである。
   実装の多くのファイルが `open` するので、置くものを通し番号と例外の語彙の 2 つに絞っている。

   ### oid

   `oid` はただの `int` である。
   名前のインターン(§1.2)、型変数の識別子(`vid`)、カインド変数(`k_id`)、
   AST のノード(第5章の `ElabData.oid`)が、同じカウンタを共有する。

   `oid` は等値比較と表のキーにしか使わないので、カウンタを共有しても差し支えない。
   番号空間を分けても検査は強くならず、型が 3 つ増えて変換が必要になるだけである。
   ある番号が何を指すかは、その番号を持つフィールドが決める。

   番号は単調に増えるので、大小には意味がある。
   ただし、その意味は小さい番号ほど早く作られたということだけである。
   第9章(show.ml)は `vid` を採番表のキーに使うが、
   ユーザに見せる名前は出現順のアルファベットに振り直す。
   番号をそのまま表示すると、同じプログラムでも、
   それより前に何を型検査したかで表示が変わるからである。

   ### 例外の 3 系統

   例外の種類は、誰の誤りかの分類に対応する。
   この分類を混ぜると、実装の内部矛盾がユーザ向けのエラーとして現れ、処理系のバグが見えなくなる。

   | 例外 | 誰の誤りか | 投げる関数 | 終了コード |
   |---|---|---|---|
   | `Type_error` | ユーザのプログラム | `type_error` | 1 |
   | `Type_error_at` | 同上(位置つき) | 第11章の `at_node` | 1 |
   | `NotImplemented` | Diktor が実装していない機能 | `noimpl` | 4 |
   | `NotImplemented_at` | 同上(位置つき) | 第11章の `at_node` | 4 |
   | `Panic` | 実装の不変条件違反 | `bug` | 3 |

   `bug` は `Panic` のメッセージの先頭に `[BUG]` を付ける。
   `Panic` は Diktor のバグを表し、ユーザのプログラムがどう書かれていても出てはならない。
   典型は §1.8 の `row_append` で、左側が開いた行で右側が空でないときに `bug` を呼ぶ。
   そこへ到達しないことは、呼び出し元の第11章が保証している。

   `NotImplemented` を `Type_error` と分けるのは、
   書けるが実装されていないものと、書いてはならないものを、ユーザが区別できるようにするためである。
   Diktor が未実装として報告するのは、`cancel(reason)` と、`module` の入れ子、
   `module` の中の `effect` 宣言、`type class` 宣言、式文である。
   第11章はこれらに対して `noimpl` を呼び、第16章は終了コード 4 で終了する。
   `1 + true` は書いてはならないものなので、第8章の `add_class` が `type_error` を呼び、
   第16章は終了コード 1 で終了する。
   言語にない数値の接尾辞(`1u8`)も書いてはならないものであり、
   第11章の `number_ty` が `type_error` を呼ぶ。
   ユーザは終了コードを見れば、Diktor が実装していない機能を使ったのか、
   プログラムを書き直す必要があるのかが分かる。

   `noimpl` の例外も、型エラーと同じ経路で診断になる。
   第11章の `type_check` と `type_check_units` が `NotImplemented` を捕捉し、
   そこまでに出せた型を表示する行と、未実装の診断を返す。
   ユーザのプログラムの `module` の平坦化は `type_check_units` の中で行うので、
   `module` についての未実装も同じ扱いになる。
   プレリュードの平坦化で起きたものだけは型検査の関数の外で投げられ、
   第16章の `type_check_files_units` が同じ書式で報告する(§16.8)。
   第16章は、型を表示する行に続けて、
   診断を `! ファイル:行:桁: 未実装: …` の行(位置がないときは `! 未実装: …`)として出力し、
   終了コード 4 で終了する。
   捕捉する節が第16章の最上位の例外ハンドラにしかないと、
   そこまでに出せた型を表示する行がすべて失われる。
   そのため、第11章と第16章の両方に節を置く(§16.8)。

   終了コードの全体は、第16章(driver.ml)の §16.8 にまとめてある。
   上の表にない終了コードは、2 が字句エラーと構文エラー、64 が使い方のエラー、
   65 が不正な KIR、74 が入出力エラーである。
   1 は import のエラーにも使い、3 は `Panic` のほか、実行時エラーにも使う。 *)


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
   位置なしの Type_error に最も内側のノードの span を付けて投げ直す。
   Type_error を捕捉する節は次の 3 種類で、Type_error_at の扱いが異なる。
   (a) 精緻化を try で囲み、例外を黙って捨てる節
   (signature_of_binding と、newtype と型エイリアスの試行)。
   Type_error_at も必ず捕捉する。
   (b) 最上位の例外ハンドラ(Elab.type_check、Driver.type_check_files_units の平坦化、Driver.main)。
   Type_error_at も必ず捕捉する。
   (c) Unify の関数(unify、rewrite_row)だけを try で囲む節。
   メッセージを言い換える場合も、例外を黙って捨てる場合も、
   Type_error_at を捕捉しなくてよい。
   unify と rewrite_row は位置を知らないので、そこから Type_error_at は出ない。
   Unify のうち Type_error_at を出すのは、
   数値リテラルの既定化(generalize と default_numerics)だけで、
   どちらも (c) の節の中からは呼ばれない *)
exception Type_error_at of Location.span * string

(* 位置つきの未実装。at_node は NotImplemented にも同じ規則で span を付ける *)
exception NotImplemented_at of Location.span * string

(* import 文のエラー(パス、読み込み、名前の解決)。位置は import 文か import の名前である *)
exception Import_error of Location.span * string
