(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第2章 字句解析

   本章は、文字の並びをトークンの並びに変える字句解析を実装する。
   本章の大半は、字句解析を 1 つの層にまとめない理由の説明である。
   字句解析は次の 3 つの層に分かれている。

   | 層 | 入口 | 処理 |
   |---|---|---|
   | 1. 生トークン | `read_raw_token` | 文字を 62 種のトークンに変える。`{` は分類しない |
   | 2. 再分類 | `pop_reclassified` | `{` をブロック、レコード、レコード型のどれかに決める |
   | 3. ASI | `read_token` | region スタックを見て、改行を文区切りに昇格させるか捨てる |

   トークン型は全部で 64 種ある(第3章(parser.mly)の `%token` 宣言)。
   層 1 が出すのはそのうち 62 種で、残る `LBRACE_RECORD` と `LBRACE_TYPE` は層 2 だけが作る。

   Keleut の字句には扱いにくい性質が 2 つある。
   改行が意味を持つことと、`{` が 3 通りの意味を持つことである(仕様 sample.kel:20-29)。
   前者は ASI(automatic semicolon insertion、自動セミコロン挿入)で、
   後者は 2 トークンの先読みで解決する。
   層を分けるのは、この 2 つが互いに影響するからである。

   - 層 3 は層 2 の結果を使う。
     `{` がブロックなら文区切りの region を、
     レコードやレコード型なら改行を抑止する region を積むので、
     分類の済んでいない `{` からは積む region を決められない。
   - 層 2 は改行をまたいで 2 トークン先を覗く。
     この先読みは層 3 より下で行う必要がある。
     ASI の層で先読みすると、まだ消費者(トークンを受け取る側)に渡していないトークンのために、
     region や直前のトークンが動いてしまう。

   本章は次の不変条件を守る。
   region を動かすのは、トークンを消費者に渡すときだけである。
   トークンを先読みで覗いただけでは、状態は何も動かない。

   この不変条件を守るために、層 1 は状態を持たない写像にしておく。
   層 1 は `{` を `LBRACE_BLOCK` という仮の印で返し、層 2 はそれを pop するときに 1 回だけ分類する。
   先読みで覗いた `{` は、未分類のままキューに残る。
   層 2 は、その `{` の番が来たときに、あらためて個別に分類する。
   そのため、入れ子の `{` も特別な扱いなしに正しく分類できる。

   本章は、数値リテラルの表現 `number` / `num_suffix` を前章(syntax.ml)から受け取り、
   トークン型を `Parser` モジュールから受け取る。
   `Parser` は、Menhir が第3章(parser.mly)から生成するモジュールである。
   消費者に渡すのは `(tok, sp, ep)` の三つ組で、これがそのまま Menhir の `$sloc` になる。
   トークン自身は位置を持たない。

   字句解析の結果は、`test/tokens.t` のゴールデン(`--dump-tokens` の出力)で固定する。
   ASI と `{` の分類を固定する手段は、このゴールデンだけである。
   このゴールデンは、sample.kel 全文をトークン化したときのトークンの数と末尾も固定している。

   字句解析の途中で本章のコードが投げる例外は `Lex_error` だけで、メッセージと位置を持つ。
   第16章(driver.ml)がこれを終了コード 2 のエラーとして報告する。
   ほかに、driver の別の分岐が受ける例外が 2 つある。
   1 つは、不正な UTF-8 バイト列に対して sedlex のデコーダが投げる `Sedlexing.MalFormed` で、
   これも終了コード 2 になる(§2.6)。
   もう 1 つは `Sys_error` である。
   `from_filename` は、`In_channel.with_open_bin` が投げる `Sys_error` を捕まえ、
   ファイル名を付けて投げ直す。
   ファイルを開けない、または読めないときは、この例外によって終了コード 64 になる。 *)
open Syntax

exception Lex_error of string * Lexing.position

(* ## 2.1 数値リテラルは値ではなく表記を運ぶ

   `parse_number` は lexeme の文字列だけを受け取り、
   `{ n_text; n_is_float; n_suffix }` を返す純関数である。
   `parse_number` は文字列を数値へ変換しない。
   この時点では、リテラルの型がまだ決まっていないからである。
   `42` がどの型になるかは、リテラルに付けた述語つきの未定変数が、
   一般化の時点で既定の型に落ちるまで決まらない(仕様 §2)。
   字句解析の時点で `Int32.of_string` を呼ぶと、その決定を先取りすることになる。
   実際の変換は、第14章(interp.ml)が精緻化で解決した型を見て行い、範囲外の値は実行時エラーにする。

   接尾辞の切り出しには注意点が 1 つある。
   16 進では `f` が数字なので、`0xff` の `f` を接尾辞の始まりと読んではならない。
   基数接頭辞があるときは `i` / `u` だけを接尾辞の印とし、走査の開始位置も接頭辞の後ろにずらす。
   `f` を接尾辞の印に加えるのは 10 進のときだけである。

   `n_is_float` は 2 つの経路で決まる。
   接尾辞が `f` なら小数である。
   接尾辞が無いか `f` 以外なら、本体に `.` か `e` / `E` が現れるか(字句として小数かどうか)で決める。
   基数接頭辞つきのリテラルは小数にならない。
   第11章(elab.ml)は、この判定で `Integral` と `Fractional` のどちらの述語を付けるかを決める。

   ビット幅の読み取りには `int_of_string_opt` を使う。
   `int_of_string` を使うと、`1i999999999999999999999` のような桁あふれで、
   `Failure` が字句層から漏れる。
   この例外は、第16章の終了コードの規約では最後の受け皿に落ち、内部エラー(終了コード 3)になる。
   `parse_number` は解釈できない幅を -1 に落とし、
   第11章の `number_ty` がそれを未実装エラー(終了コード 4)として報告する。
   ただし、本体が小数のリテラルに整数の接尾辞が付いているときは、幅を見る前に型エラーになる。
   こうして、字句解析の途中で本章が投げる例外を `Lex_error` だけに保つ。
   番兵に -1 を使うのは、幅の字句が `Plus digit` なので負の幅をソースに書けず、
   -1 がどの実装の幅とも衝突しないからである。
   番兵に正の値(たとえば 9999)を使うと、利用者が `1i9999` と書いた場合と桁あふれを区別できない。

   符号はリテラルに含めない。
   `-1` は `HYPHEN` と `NUMBER` の 2 トークンとして出し、
   第3章の前置の規則が `n_text` の先頭に `-` を足して 1 つの負のリテラルに畳む。
   字句解析で `-` を数値に含めると、`1-2` が引き算に見えなくなるためである。
   AST の上では、単項マイナス演算子が存在しないという sample.kel:94 の意味論がそのまま保たれる。

   `show_number` は表記を組み立て直さず、原文を連結する。
   `number` は本体の原文 `n_text` と接尾辞の原文 `n_suffix_text` を持っている(第1章)。
   ゴールデンテストの出力にも型エラーの文面にも、この原文がそのまま出る。
   解釈済みの `n_suffix` から表記を組み立て直すと、桁あふれの接尾辞や、
   `1i032` のような先頭のゼロが、書いたとおりに出ない。 *)

let parse_number text =
  let len = String.length text in
  let has_radix_prefix = len >= 2 && text.[0] = '0' && (match text.[1] with 'x' | 'o' | 'b' -> true | _ -> false) in
  (* 接尾辞の開始位置。基数接頭辞つきは i/u だけ(16 進の f は数字)、10 進は i/u/f *)
  let suffix_at =
    let is_suffix_char c = c = 'i' || c = 'u' || (c = 'f' && not has_radix_prefix) in
    let rec find i = if i >= len then None else if is_suffix_char text.[i] then Some i else find (i + 1) in
    find (if has_radix_prefix then 2 else 0)
  in
  let lexically_float body =
    (not has_radix_prefix) && String.exists (fun c -> c = '.' || c = 'e' || c = 'E') body
  in
  match suffix_at with
  | None -> { n_text = text; n_is_float = lexically_float text; n_suffix = None; n_suffix_text = "" }
  | Some i ->
      let body = String.sub text 0 i in
      let raw = String.sub text i (len - i) in
      (* 解釈できない幅は -1 に落とし、第11章の number_ty へ回す。number_ty は、本体が小数で
         接尾辞が整数なら型エラーにし、そうでなければ未実装エラーにする。字句は Plus digit
         なので負の幅はソースに書けず、-1 はどの実装の幅とも衝突しない番兵になる *)
      let width = match int_of_string_opt (String.sub text (i + 1) (len - i - 1)) with Some w -> w | None -> -1 in
      let suffix = match text.[i] with 'i' -> NsInt width | 'u' -> NsUInt width | _ -> NsFloat width in
      let is_float = match suffix with NsFloat _ -> true | _ -> lexically_float body in
      { n_text = body; n_is_float = is_float; n_suffix = Some suffix; n_suffix_text = raw }

let show_number { n_text; n_suffix_text; _ } = n_text ^ n_suffix_text

(* ## 2.2 sedlex の正規表現

   桁区切りの `_` はどの基数でも使え、小数点と指数を持てるのは 10 進だけである。
   先頭の `0` を 8 進の印にはしない。
   `010` は 10 進の 10 であり、8 進は `0o` で書く。

   小数部は省略できる。
   `1.` は 1.0、`1.e5` は 1e5 である。
   小数部の規則を `Opt ('.', Opt (digit, Star (digit | '_')))` と書き、
   小数点の直後に `Star` を直接置かないのは、
   `1._1` の全体が 1 つの数値にならないようにするためである。
   小数点の直後が数字でなければ小数部は空になり、そこで数値が切れる。
   最長一致の結果、`1._1` や `1.foo` は数値リテラルと識別子の 2 つに読まれ、
   数値リテラルへのレコード射影は書けない。
   数値は行を持たない値なので、書けなくなるプログラムはない。
   先頭の小数点(`.5`)は認めない。
   `.5` を認めると `t._0` の射影と読み分ける必要が生じるので、
   仕様が `t.0` を避けたのと同じ理由で避ける(sample.kel:174-175)。
   どちらの規則も、`test/tokens.t` の dot5 / projnum が固定している。

   `int_suffix` は基数つきの側だけで使い、
   10 進の側は正規表現の中に `('i' | 'u' | 'f'), Plus digit` を直接書く。
   §2.1 で述べた 16 進の `f` と同じ理由である。
   16 進には浮動小数の接尾辞を書けない(`f` も `3` も `2` も 16 進の数字なので、
   `f32` は数値の本体に含まれる)。
   `parse_number` の判定と字句の規則は、同じ境界で数値を切る。 *)

let digit = [%sedlex.regexp? '0' .. '9']

let hex_digit = [%sedlex.regexp? '0' .. '9' | 'a' .. 'f' | 'A' .. 'F']

let idchar = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9']

let int_suffix = [%sedlex.regexp? ('i' | 'u'), Plus digit]

let dec_number =
  [%sedlex.regexp?
    ( digit,
      Star (digit | '_'),
      (* 小数部は省略できる(1. も 1.5 も書ける)。Star を直接置かず Opt (digit, Star ...)
         とするのは、1._1 の全体が 1 つの数値にならないようにするため *)
      Opt ('.', Opt (digit, Star (digit | '_'))),
      Opt (('e' | 'E'), Opt ('+' | '-'), Plus digit),
      Opt (('i' | 'u' | 'f'), Plus digit) )]

let hex_number = [%sedlex.regexp? "0x", hex_digit, Star (hex_digit | '_'), Opt int_suffix]

let oct_number = [%sedlex.regexp? "0o", '0' .. '7', Star ('0' .. '7' | '_'), Opt int_suffix]

let bin_number = [%sedlex.regexp? "0b", ('0' | '1'), Star ('0' | '1' | '_'), Opt int_suffix]

(* ## 2.3 ファンクタと位置の運び方

   `Data` は第1章(syntax.ml)の付随データのファンクタで、AST のノードに何を付けるかを決める。
   字句解析器は AST を作らないが、トークン型を持つのは Menhir が生成した `Parser` なので、
   同じパラメータを通す必要がある。

   字句解析器は、`Sedlexing.lexing_positions` が返す開始位置と終了位置の対を、
   そのまま `{ tok; sp; ep }` に載せて運ぶ。
   位置はトークン型ではなく、先読みキューの要素が持つ。
   先読みしたトークンは、自分の位置と一緒にキューに並ぶ。
   そのため、先読みの深さにかかわらず、消費者に渡す位置はそのトークン自身の位置になる。 *)

module Make (Data : Syntax.Data) = struct
  module Parser = Parser.Make (Data)
  open Parser

  let lexeme = Sedlexing.Utf8.lexeme

  let cur_pos lexbuf = fst (Sedlexing.lexing_positions lexbuf)

(* ## 2.4 キーワード表と、裸のアンダースコア

   識別子はまとめて読んでから表を引く。
   表に無ければ `LOWER_IDENTIFIER` である。
   `return`、`cancel`、`structural`、`Type`、`EffectRow` はキーワードにせず、
   普通の識別子として読む。
   予約語を増やさないためである。
   これらの語の意味は、使われた位置で決まる。
   たとえば `case return(x)` や `derive structural` を解釈するのは第11章(elab.ml)である。

   表の 1 行目は `_` である。
   `case _ =>` も `List[_]` も `LOWLINE` を使う。
   ところが、識別子の正規表現は長さ 1 の `_` にもマッチする。
   `LOWLINE` を識別子とは別の正規表現の分岐で読もうとすると、
   同じ長さでマッチする識別子の分岐との順序に左右される(§2.7)。
   一方、`_item`(タプルのラベル)や `_0` は識別子のままでなければならないので、
   正規表現から `_` を除くこともできない。
   そこで、識別子として読んだ後、単独の `_` だけをこの表で `LOWLINE` に振り替える。 *)

  (* ---- 生トークン層 ---- *)

  let keyword_or_ident = function
    | "_" -> LOWLINE (* 単独の _ だけ。_item や _0 は識別子のまま *)
    | "and" -> AND
    | "case" -> CASE
    | "class" -> CLASS
    | "derive" -> DERIVE
    | "effect" -> EFFECT
    | "extends" -> EXTENDS
    | "extern" -> EXTERN
    | "false" -> BOOL false
    | "fn" -> FN
    | "handle" -> HANDLE
    | "if" -> IF
    | "instance" -> INSTANCE
    | "let" -> LET
    | "match" -> MATCH
    | "module" -> MODULE
    | "newtype" -> NEWTYPE
    | "perform" -> PERFORM
    | "pub" -> PUB
    | "rec" -> REC
    | "resume" -> RESUME
    | "run" -> RUN
    | "true" -> BOOL true
    | "type" -> TYPE
    | "val" -> VAL
    | "with" -> WITH
    | id -> LOWER_IDENTIFIER id

(* ## 2.5 空白、コメント、shebang と行番号

   改行は捨てない。
   ASI の層が使うので、`NL` として上の層に渡す。
   ただし、連続する改行は 1 個に潰す。
   潰さないと空行の数だけ空の文区切りができ、文法の側が余分な区切りを読み飛ばさなければならない。
   CR は空白の一種として読み飛ばすので、CRLF では LF だけが改行として働き、
   単独の CR は改行にならない(仕様 §0)。
   文字列リテラルの中の CR は、`read_text` がそのまま値に入れる。
   `test/tokens.t` の crlf / cronly / crstr が、この 3 つの振る舞いを固定している。

   行番号の数え方には注意が要る。
   sedlex 3.x は改行を自動で数え、行頭のオフセットをバッファの側で更新する。
   そのため、`'\n'` を見るたびに `Sedlexing.new_line` を呼ぶと行番号を二重に数え、
   2 行目が 3 行目として報告される。
   このずれはエラーにならないので気づきにくい。
   `test/tokens.t` のゴールデンは行番号つきで出力を固定しているので、この種のずれを検出できる。

   コメントは 2 種類ある。
   `//` は行末まで読み飛ばすが、改行は消費しない。
   改行を消費すると、ASI が文区切りを作れなくなるからである。
   `/* */` は入れ子を数え、EOF に達したら「unterminated block comment」の字句エラーにする。

   改行を含むブロックコメントは、`NL` 1 個として扱う。
   コメントを足しただけで前後の行がつながってしまうのを防ぐためである。
   改行を含まないブロックコメントは、空白と同じように読み飛ばし、`NL` を出さない。
   改行を含んでいたかどうかは、`read_block_comment` が真偽値で返す。

   層 1 が出す生のトークン列では、`NL` が連続しない。
   連続する改行を潰すのは層 1 の `skip_newlines` で、行コメントとブロックコメントもまたいで潰す。
   層 3 の ASI も `can_end_statement NL` が偽であることを使って余分な `NL` を捨てるが、
   これは保険である。
   この不変条件が、先読みキューの長さを定数に抑える(§2.8)。

   `#!` は、オフセット 0 にあるときだけ shebang として行末まで読み飛ばし、
   それ以外の位置では字句エラーにする。
   Keleut の `#` はコメントの記号ではなく、構造的ヴァリアントの印(`#Even` など)である。
   `#` で始まる行をコメントとして読み飛ばす規則にすると、行頭に置いた `#Even` が読めなくなる。 *)

  (* 入れ子のブロックコメントを読み、改行を含んでいたかを返す。
     skip_newlines より前に置くのは、相互再帰にしないため(こちらは
     skip_newlines を呼ばない) *)
  let read_block_comment lexbuf =
    let saw_nl = ref false in
    let rec go depth =
      if depth = 0 then !saw_nl
      else
        match%sedlex lexbuf with
        | "/*" -> go (depth + 1)
        | "*/" -> go (depth - 1)
        | '\n' ->
            saw_nl := true;
            go depth
        | eof -> raise (Lex_error ("unterminated block comment", cur_pos lexbuf))
        | any -> go depth
        | _ -> raise (Lex_error ("unterminated block comment", cur_pos lexbuf))
    in
    go 1

  (* 連続する改行と空白を 1 個の NL に潰す。トークンは作らない
     (行番号は sedlex 3.x が自動で数える)。
     ここへ来た時点で NL を 1 個出すと決まっているので、後に続くコメントが
     2 個目の NL を作る理由はない。そこで行コメントもブロックコメントもまたいで潰す。
     これで、生のトークン列で NL が連続しないという不変条件が成り立ち、先読みキューの
     長さが高々 4(NL + t1 + NL + t2)に収まる。コメントをまたがずに潰すと、
     コメント行が続く分だけキューが伸び、先読みの仕事が二次になる *)
  let rec skip_newlines lexbuf =
    match%sedlex lexbuf with
    | '\n' -> skip_newlines lexbuf
    | Plus (' ' | '\t' | '\r') -> skip_newlines lexbuf
    | "//", Star (Compl '\n') -> skip_newlines lexbuf
    | "/*" ->
        ignore (read_block_comment lexbuf : bool);
        skip_newlines lexbuf
    | _ -> Sedlexing.rollback lexbuf

  let skip_rest_of_line lexbuf = match%sedlex lexbuf with Star (Compl '\n') -> () | _ -> ()

(* ## 2.6 文字列とエスケープ

   `read_unicode_escape` は 16 進の数字を 1 桁ずつ読んで値 `acc` に積み上げ、
   指定の桁数(`limit`)を読み終えたら、`Uchar.is_valid` で検査してから `Uchar.of_int` を呼ぶ。
   `Uchar.of_int` は、サロゲート(たとえば `0xD800`)や範囲外の値に `Invalid_argument` を投げる。
   検査を省くと、`\uD800` と書いただけで `Invalid_argument` が字句層から漏れる。
   `is_valid` は範囲外とサロゲートの域の両方を拒否するので、`\uD800` は普通の字句エラーになる。

   字句エラーも、不正な UTF-8 バイト列(`Sedlexing.MalFormed`)も、終了コードは 2 である。
   どちらもソースを読めなかったという同じ種類の失敗なので、同じ番号にしている
   (型エラーは 1、ファイルを開けないときは 64)。

   `read_text` は `Buffer.add_utf_8_uchar` で文字列を組み立てる。
   エスケープの集合(`\u` `\U` と `\a\b\f\n\r\t\v`、引用符と逆斜線)は仕様 §2 が定める。
   文字列には生の改行も含められる。
   `test/tokens.t` の esc / rawnl / surr / oor / badesc は、
   集合のすべてのエスケープと生の改行を受け付けることと、
   サロゲート、範囲外の値、未知のエスケープを拒否することを固定している。 *)

  let read_unicode_escape lexbuf limit =
    let rec loop acc i =
      if i = limit then
        if Uchar.is_valid acc then Uchar.of_int acc
        else raise (Lex_error ("invalid unicode escape (out of range or surrogate)", cur_pos lexbuf))
      else
        let ret base_char base_value =
          loop ((acc * 16) + (Uchar.to_int (Sedlexing.lexeme_char lexbuf 0) - Char.code base_char) + base_value) (i + 1)
        in
        match%sedlex lexbuf with
        | '0' .. '9' -> ret '0' 0
        | 'a' .. 'f' -> ret 'a' 10
        | 'A' .. 'F' -> ret 'A' 10
        | _ -> raise (Lex_error ("unexpected end of unicode escape", cur_pos lexbuf))
    in
    loop 0 0

  let read_escape lexbuf =
    match%sedlex lexbuf with
    | 'u' -> read_unicode_escape lexbuf 4
    | 'U' -> read_unicode_escape lexbuf 8
    | '\'' -> Uchar.of_char '\''
    | '"' -> Uchar.of_char '"'
    | '\\' -> Uchar.of_char '\\'
    | 'a' -> Uchar.of_int 0x07
    | 'b' -> Uchar.of_char '\b'
    | 'f' -> Uchar.of_int 0x0c
    | 'n' -> Uchar.of_char '\n'
    | 'r' -> Uchar.of_char '\r'
    | 't' -> Uchar.of_char '\t'
    | 'v' -> Uchar.of_int 0x0b
    | _ -> raise (Lex_error ("invalid escape sequence", cur_pos lexbuf))

  let read_text lexbuf =
    let buf = Buffer.create 64 in
    let rec aux () =
      match%sedlex lexbuf with
      | '"' -> Buffer.contents buf
      | eof -> raise (Lex_error ("unterminated string literal", cur_pos lexbuf))
      | '\\' ->
          Buffer.add_utf_8_uchar buf (read_escape lexbuf);
          aux ()
      | '\n' ->
          Buffer.add_char buf '\n';
          aux ()
      | any ->
          Buffer.add_string buf (lexeme lexbuf);
          aux ()
      | _ -> raise (Lex_error ("unterminated string literal", cur_pos lexbuf))
    in
    aux ()

(* ## 2.7 生トークン層

   `entry` は、トークンと開始位置と終了位置の三つ組である。
   層 2 と層 3 はこの型の値だけを扱い、
   `Sedlexing.lexbuf` に触れるのは `read_raw_token` までである。

   sedlex は最長一致で分岐を選び、同じ長さの候補が複数あるときだけ先に書かれた分岐を採る。
   したがって、`=>` を `=` より先に置く必要はない(長さで決まる)。
   §2.4 で `_` を別の分岐ではなく表で振り替えるのは、`_` が識別子の分岐と長さ 1 で並ぶからである。
   複数文字の記号を上にまとめているのは、読みやすさのための整理である。

   末尾では、`eof` と `any` を別の分岐にしている。
   `eof` だけが `EOF` を返し、`any` に落ちた文字は「unexpected character」の字句エラーにする。
   知らない文字を `EOF` として返すと、パーサにはそこでファイルが終わったように見え、
   その先のエラーメッセージがすべて的外れになる。

   一方で、`any` に落ちた文字をそのままメッセージに出すと、不可視の文字では診断が読めなくなる。
   その代表が BOM(U+FEFF)である。
   仕様 §0 は、文字列リテラルとコメントの外にある BOM を、位置によらず字句エラーと定めている。
   BOM を生のまま出すと、`unexpected character: ` の後ろに見えない 3 バイトが並ぶだけで、
   ゴールデンにも固定できない(エディタや差分ツールが黙って壊す)。
   そこで `any` の分岐は、次の文字だけを `U+XXXX` の表記で出し、それ以外の文字は字面のまま出す。

   - BOM
   - 制御文字(U+0000〜U+001F と U+007F〜U+009F。U+007F は DEL)
   - NBSP(U+00A0)とソフトハイフン(U+00AD)
   - ゼロ幅の文字(U+200B〜U+200F)
   - 行区切りと双方向制御(U+2028〜U+202E)
   - ワードジョイナと不可視演算子(U+2060〜U+2064)

   `test/tokens.t` の bom 群が、各区間の代表を固定している。
   全角空白(U+3000)のように空白として見える文字は、字面のまま出す。
   この集合は Unicode の分類から機械的に引いたものではなく、
   字面のままでは診断に使えない文字を列挙したものである。

   文字列リテラルとコメントの中の文字は `any` の分岐に来ないので、この扱いの対象外である。
   文字列の中の BOM は値の一部になり、コメントの中の BOM は読み飛ばされる。

   `{` だけは分類を決めずに `LBRACE_BLOCK` を返す。
   この `LBRACE_BLOCK` はブロックであるという判断ではなく、未分類の印である。
   次の層が必ず上書きする。
   専用の未分類トークンを作らないのは、`token` 型は Menhir の側の定義で、
   文法に現れないトークンを増やすと `--strict` の未使用警告に引っかかるためである。 *)

  type entry = { tok : token; sp : Lexing.position; ep : Lexing.position }

  let rec read_raw_token lexbuf =
    let here tok =
      let sp, ep = Sedlexing.lexing_positions lexbuf in
      { tok; sp; ep }
    in
    match%sedlex lexbuf with
    | Plus (' ' | '\t' | '\r') -> read_raw_token lexbuf
    | '\n' ->
        let sp, ep = Sedlexing.lexing_positions lexbuf in
        skip_newlines lexbuf;
        { tok = NL; sp; ep }
    | "//", Star (Compl '\n') -> read_raw_token lexbuf
    | "/*" ->
        (* 改行を含むコメントは NL 1 個として扱う(§2.5)。位置は潰す前に取っておく
           (ゴールデンが NL の位置を固定している)。直後の改行とコメントを潰すのは
           '\n' の分岐と同じく、生の NL を連続させないため *)
        if read_block_comment lexbuf then (
          let sp, ep = Sedlexing.lexing_positions lexbuf in
          skip_newlines lexbuf;
          { tok = NL; sp; ep })
        else read_raw_token lexbuf
    | "#!" ->
        (* shebang として読むのはオフセット 0 のときだけ *)
        if Sedlexing.lexeme_start lexbuf = 0 then (
          skip_rest_of_line lexbuf;
          read_raw_token lexbuf)
        else raise (Lex_error ("stray '#!'", cur_pos lexbuf))
    | "???" -> here HOLE
    | "..." -> here DOTDOTDOT
    | "=>" -> here EQ_GREATER
    | "==" -> here BIG_EQ
    | "!=" -> here EXCLAMATION_EQ
    | "<=" -> here LESS_EQ
    | ">=" -> here GREATER_EQ
    | "&&" -> here BIG_AMPERSAND
    | "||" -> here BIG_VERTICAL
    | 'A' .. 'Z', Star idchar -> here (UPPER_IDENTIFIER (lexeme lexbuf))
    | ('a' .. 'z' | '_'), Star idchar -> here (keyword_or_ident (lexeme lexbuf))
    | '#', 'A' .. 'Z', Star idchar ->
        let s = lexeme lexbuf in
        here (HASH_IDENT (String.sub s 1 (String.length s - 1)))
    | hex_number | oct_number | bin_number | dec_number -> here (NUMBER (parse_number (lexeme lexbuf)))
    | '"' ->
        let sp, _ = Sedlexing.lexing_positions lexbuf in
        let s = read_text lexbuf in
        let _, ep = Sedlexing.lexing_positions lexbuf in
        { tok = TEXT s; sp; ep }
    | '(' -> here LPAREN
    | ')' -> here RPAREN
    | '[' -> here LBRACKET
    | ']' -> here RBRACKET
    | '{' -> here LBRACE_BLOCK (* 未分類の印。再分類層が分類を決める *)
    | '}' -> here RBRACE
    | '=' -> here EQ
    | ':' -> here COLON
    | ',' -> here COMMA
    | ';' -> here SEMI
    | '.' -> here DOT
    | '@' -> here AT
    | '+' -> here PLUS
    | '-' -> here HYPHEN
    | '*' -> here ASTERISK
    | '/' -> here SOLIDUS
    | '!' -> here EXCLAMATION
    | '<' -> here LESS
    | '>' -> here GREATER
    | '|' -> here VERTICAL
    | '\\' -> here BACKSLASH
    | eof -> here EOF
    | any ->
        (* 不可視の文字と制御文字は、字面を出しても診断にならない。代表は BOM(U+FEFF)で、
           生のまま出すとゴールデンにも固定できない。\n \t \r は上の分岐が先に取るので
           ここには来ない。集合は §2.7 の本文と test/tokens.t の bom 群にも列挙してあり、
           この 3 か所を一致させる *)
        let cp = Uchar.to_int (Sedlexing.lexeme_char lexbuf 0) in
        let invisible =
          cp = 0xFEFF
          || cp < 0x20
          || (cp >= 0x7F && cp <= 0xA0)
          || cp = 0xAD
          || (cp >= 0x200B && cp <= 0x200F)
          || (cp >= 0x2028 && cp <= 0x202E)
          || (cp >= 0x2060 && cp <= 0x2064)
        in
        let shown = if invisible then Printf.sprintf "U+%04X" cp else lexeme lexbuf in
        raise (Lex_error ("unexpected character: " ^ shown, cur_pos lexbuf))
    | _ -> raise (Lex_error ("unexpected input", cur_pos lexbuf))

(* ## 2.8 字句解析器の状態と先読みキュー

   `lexbuf` のほかに、層 2 と層 3 が共有する状態が 5 つある。

   - `pending`：生トークンの先読みキュー。先頭が次に消費者へ渡すトークンである
   - `regions`：ASI の region スタック。底は常に `RTop` である
   - `prev`：直前に消費者へ渡したトークン(区切りに昇格した `NL` を含む)。`NL` の判定に使う
   - `last_sp` / `last_ep`：直前に渡したトークンの開始位置と終了位置。
     第16章(driver.ml)が `last_sp` を構文エラーの報告に使う。
     `last_ep` はどこからも読まれていない

   `peek t i` は、キューが足りなければ生トークンを継ぎ足して i 番目を返す。
   `peek_sig t k` は、`NL` を飛ばして k 個目の有意トークンを覗く。
   `{` の分類でも、次の有意トークンが文を始められるかという ASI の判定でも、
   改行をまたいで先読みする必要がある。

   末尾への追加 `t.pending @ [...]` はキューの長さに比例する仕事をするが、
   キューの長さが定数なので問題にならない。
   キューの長さを定数に抑えるのは、生のトークン列で NL が連続しないという §2.5 の不変条件である。
   `peek_sig` が覗く必要があるのは、高々 4 要素(NL + t1 + NL + t2)である。
   有意トークンの間にも NL が 1 個入りうるが、間に何行のコメントがあっても、
   層 1 がそれを 1 個の NL に潰す。
   この不変条件が無いと、キューの長さは改行とコメントの続く行数に比例して伸び、
   先読みの仕事が二次になる。
   `{` の分類だけでなく、トップレベルの ASI の `can_begin_statement` の判定も同じ先読みを通る。

   先読みも章の冒頭に置いた不変条件を守る。
   `peek` は `pending` に足すだけで、`regions` にも `prev` にも触れない。
   覗いたトークンは、後で自分の番が来たときに、あらためて `read_token` を通る。 *)

  (* ---- 再分類層 + ASI 層 ---- *)

  (* region の種類。
     RBlock は文区切りの region(LBRACE_BLOCK)、
     RSuppress は NL を抑止する region(丸括弧、角括弧、LBRACE_RECORD、LBRACE_TYPE)、
     RClause は case のパターンとガード(EQ_GREATER で pop する)。
     RClause の int は、まだ矢印の来ていない fn の本数で、
     節の矢印と fn の矢印を見分けるための唯一の状態である *)
  type region = RTop | RBlock | RSuppress | RClause of int

  type t = {
    lexbuf : Sedlexing.lexbuf;
    mutable pending : entry list; (* 生トークンの先読みキュー(先頭が次) *)
    mutable regions : region list;
    mutable prev : token option; (* 直前に消費者へ渡したトークン(昇格した NL を含む) *)
    mutable last_sp : Lexing.position; (* 直前に消費者へ渡したトークンの位置(エラー報告用) *)
    mutable last_ep : Lexing.position;
  }

  let from_sedlex lexbuf =
    {
      lexbuf;
      pending = [];
      regions = [ RTop ];
      prev = None;
      last_sp = Lexing.dummy_pos;
      last_ep = Lexing.dummy_pos;
    }

  let from_string source = Sedlexing.Utf8.from_string source |> from_sedlex

  let from_channel channel = Sedlexing.Utf8.from_channel channel |> from_sedlex

  let from_filename filename =
    (* チャネルはここで閉じる。sedlex の from_channel は遅延して読むので、
       開いたまま渡すと閉じる機会が無く、入力ファイルの数だけ fd がプロセスの
       終了まで残る。先に全文を読んで文字列の字句解析器に渡すと、parse_string と
       経路もそろう。input_all はパイプでも正しく読む(in_channel_length は使えない) *)
    let source =
      try In_channel.with_open_bin filename In_channel.input_all
      with Sys_error msg ->
        (* 読み出しの段(Is a directory など)の Sys_error はファイル名を含まない
           ので、ファイル名を付ける。付けないと、複数のファイルを指定したときに
           どれが原因か分からない。open の段のものは含むので、二重には付けない *)
        let has_name =
          String.length msg >= String.length filename && String.sub msg 0 (String.length filename) = filename
        in
        raise (Sys_error (if has_name then msg else filename ^ ": " ^ msg))
    in
    let lexbuf = Sedlexing.Utf8.from_string source in
    Sedlexing.set_filename lexbuf filename;
    from_sedlex lexbuf

  let rec peek t i =
    (* キューの長さは §2.5 の不変条件で高々 4 に抑えられている。万一それが破れても
       List.length で二次にならないよう、長さを数えずに構造で判定する *)
    let rec has l i = match (l, i) with _ :: _, 0 -> true | _ :: tl, i -> has tl (i - 1) | [], _ -> false in
    if has t.pending i then List.nth t.pending i
    else (
      t.pending <- t.pending @ [ read_raw_token t.lexbuf ];
      peek t i)

  (* NL を飛ばして k 個目(0 始まり)の有意トークンを覗く *)
  let peek_sig t k =
    let rec go i k =
      let e = peek t i in
      match e.tok with NL -> go (i + 1) k | _ -> if k = 0 then e else go (i + 1) (k - 1)
    in
    go 0 k

  let is_ident_tok = function LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ -> true | _ -> false

(* ## 2.9 再分類層で `{` を 3 通りに読み分ける

   読み分けの規則は sample.kel:20-29 が定める。
   `{` の次の有意トークンを t1、その次を t2 として、次の表で分類する。

   | t1 | t2 | 分類 |
   |---|---|---|
   | `}` | (見ない) | `LBRACE_RECORD`(空。Unit 値、空レコード、空タプル) |
   | `extends` | (見ない) | `LBRACE_RECORD`(`{extends R}`。行変数だけのレコード) |
   | 識別子 | `:` | `LBRACE_TYPE`(レコード型) |
   | 識別子 | `=` / `,` / `with` / `extends` | `LBRACE_RECORD` |
   | それ以外(識別子の次が `}` の場合を含む) | | `LBRACE_BLOCK` |

   仕様 §0 は、3 つの文脈にある `{ ... }` を、
   上の表のどれに分類されてもエフェクト行(または宣言の本体)として読むと定めている。
   3 つの文脈とは、`@` の直後、EffectRow のエイリアスの右辺、effect 宣言の本体である。
   本実装は、この 3 つの文脈でも先読みを止めない。
   `{Print}` は識別子の次が `}` なので `LBRACE_BLOCK`、`{Print, Fs2}` は `LBRACE_RECORD`、
   `{ print: … }` は `LBRACE_TYPE` と、文脈ではなく先読みで分類する。
   それでも同じ構文木になるのは、第3章の `%inline lbrace` が 3 種を束ねて受け、
   意味の層が要素の形から決めるからである(§3.23)。
   仕様は、3 種を同じ構文木で表して意味の層で区別してよいことと、
   先読みを止める実装でも結果が同じになることを定めている(sample.kel:26-28)。
   この等価性は、`test/tokens.t` の effbrace / effield が固定している。

   2 トークンの先読みで足りるのは、Keleut に代入演算子が無いからである。
   `{x = 1}` の `=` は、レコードのフィールドの `=` でしかありえない。
   `r.f = v` のような代入を加えると、`=` がどちらの意味かを 2 トークンでは決められなくなり、
   この読み分けが成り立たない。
   仕様が「代入演算子は加えない」と定めているのはこのためである。

   この設計には制限が 2 つある。

   1. `{x}` はブロックであって、レコードではない(sample.kel:29 の規則。識別子の次が `}` である)。
      フィールドが 1 個のレコードをパンニングで書くときは、末尾にカンマを付けて `{x,}` と書く
      (t2 が `,` なのでレコードに分類される)。
      `{x = x}` と書いてもよい。
   2. `{base with ...}` の base(更新の基底)は識別子 1 個に限る。
      `{p.x with ...}` は t2 が `.` なのでブロックに分類される。
      分類は字句解析の時点で決まっているので、文法の側で base を式にしても意味がない。
      この表は識別子の大文字と小文字を区別しないので、
      `{P with x = 3}` もレコードに分類されて第3章へ届く。
      大文字で始まる基底を拒否するのは、`record_exp` の意味アクションである(第3章の §3.20)。
      ここで大文字と小文字を分けると表が 5 行に収まらなくなるので、この分担にしている。
      仕様 §3 も、更新の基底を小文字で始まる識別子 1 個に限っている。

   分類は、`pop_reclassified` がトークンを pop するときに 1 回だけ行う。
   `classify_brace` を呼ぶ時点で `{` はすでにキューから外れているので、
   `peek_sig t 0` がそのまま t1 になる。
   先読みで覗いた `{` は生のままキューに残り、自分が pop されるときに、
   自分の位置から改めて分類される。
   そのため、入れ子の `{` も余分な状態なしに正しく分類できる。

   文法は、どの分類で来ても意味が同じ位置では、3 種を束ねた `%inline lbrace` で受ける。
   型、パターン、instance の本体、クラスの本体、module の本体、effect 宣言の本体、`run` の本体、
   match と handle の本体がそうした位置である。
   分類を使い分けるのは式の位置だけである。
   3 種に分けても、Menhir の conflict は 0 のままである(第3章 §3.13)。 *)

  (* §2.9 の表。t1 は `{` の次、t2 はその次の有意トークン(NL は飛ばす) *)
  let classify_brace t =
    let t1 = (peek_sig t 0).tok in
    match t1 with
    | RBRACE | EXTENDS -> LBRACE_RECORD
    | _ when is_ident_tok t1 -> (
        match (peek_sig t 1).tok with
        | COLON -> LBRACE_TYPE
        | EQ | COMMA | WITH | EXTENDS -> LBRACE_RECORD
        | _ -> LBRACE_BLOCK)
    | _ -> LBRACE_BLOCK

  let pop_reclassified t =
    let e =
      match t.pending with
      | e :: rest ->
          t.pending <- rest;
          e
      | [] -> read_raw_token t.lexbuf
    in
    match e.tok with LBRACE_BLOCK -> { e with tok = classify_brace t } | _ -> e

(* ## 2.10 ASI 層の 2 つの述語

   改行を文区切りに昇格させるかどうかは、次の論理積で決める。
   直前のトークンが文を終えられ、かつ次の有意トークンが文を始められるなら、その改行を区切りにする。
   そうでなければ改行を捨てる。

   `can_end_statement` は、値として完結しているトークンの集合である。
   閉じ括弧、識別子、リテラル、`???` がこれにあたる。
   二項演算子はこの集合に入っていないので、`1 + ⏎ 2` のように演算子で終わる行は次の行につながる。
   `can_begin_statement` は、宣言のキーワードと、式を始められるトークンの集合である。

   `can_begin_statement` から除いたトークンは、前の行の続きとして扱われる。
   除いたトークンと、除いた目的は次のとおりである。

   - `AND`：`let rec f(x) = ... ⏎ and g(x) = ...` を 1 つの宣言につなぐ
   - `CASE`：節の並びを改行で区切らない(節の区切りは `case` 自身)
   - `MATCH` / `HANDLE`：後置なので、改行してから書ける
   - `DOT` / `BACKSLASH`：メソッドチェーンとレコードの制限を行の途中で折り返す
   - `EXTENDS` / `VERTICAL`：`extends` の直前と、`#X | #Y` の `|` の直前で改行できる
   - 二項演算子：`1 ⏎ + 2` のように、演算子で始まる行を前の行につなぐ

   `DOT` は除いているが、行末の `1.` は文を終えられる。
   `1.` は `1` と `DOT` の 2 トークンではなく、1 個の `NUMBER` だからである(§2.2)。

   逆に `LPAREN` は `can_begin_statement` に含めている。
   これは、行頭の `(` を前の行の続きとみなさないという sample.kel:295 の規則の実装である。
   `VAL` と `DERIVE` も含めている。
   これらが無いと、クラスの本体の `derive structural` の前で改行が捨てられ、パースエラーになる。

   最も基本的な形である `let x = 1 ⏎ let y = 2` に区切りが入ることは、
   `test/tokens.t` の最初の例が確かめている。

   ### region スタック

   述語だけでは足りない。
   改行に意味があるかどうかは、改行が現れた場所で決まる。

   | region | 積む契機 | 改行の扱い |
   |---|---|---|
   | `RTop` | 最初から積んである。pop しない | 述語で判定する |
   | `RBlock` | `LBRACE_BLOCK` | 述語で判定する |
   | `RSuppress` | `(` `[` `LBRACE_RECORD` `LBRACE_TYPE` | 常に捨てる |
   | `RClause` | `case` | 常に捨てる(`=>` まで。fn の矢印は数えて見送る) |

   レコードとレコード型の中で改行が文区切りになることはないので、
   `{` の 3 分割をそのまま region の分割に使う。
   たとえば `{r ⏎ with l = e}` は、`with` が文を始められるトークンなので、
   `RBlock` の中なら改行が区切りになってしまう。
   実際には `{` がレコードに分類されて `RSuppress` を積むので、この改行は捨てられる。
   エフェクト行は `LBRACE_BLOCK` に分類されることもあるが、
   エフェクト行の中の改行は区切りにならない。
   `{` や `,` の直後では直前のトークンが文を終えられず、
   `,`、`extends`、`}` の直前では次のトークンが文を始められないからである。
   `test/tokens.t` の effnl がこの振る舞いを固定している。

   `RClause` は、`case` から `=>` までのパターンとガードを覆う。
   ここで改行が区切りになると、`case x if f ⏎ (x) => x` が書けない。
   `f` は文を終えられ、`(` は文を始められるので、述語だけではこの改行が区切りになる。
   文法の節は `=>` を使うので、pop の契機は `EQ_GREATER` である。

   ASI の層は、括弧に包まれた `=>` を節の矢印と取り違えない。
   `(` と `[` は `RSuppress` を、`{` は `RBlock` を積むので、括弧の中の `=>` の時点では、
   スタックの先頭は `RClause` ではない。
   そのため、次の例の内側の `=>` は region を動かさない。

   ```
   case Some(x) if pred(fn(y) => y) =>   // 内側の => は region を動かさない
   ```

   括弧の深さは region スタックが実質的に見ているので、
   見分けが要るのは、ガードの最上位に括弧で包まずに置いたラムダの矢印だけである。
   `RClause` は、まだ矢印の来ていない `fn` の本数を数え、その本数だけ矢印を見送る。
   見分けないと、ラムダの矢印で region が早く pop し、続く改行が区切りになってパースエラーになる。
   この形のガードは Boolean にならないので、型の付くプログラムには現れず、影響は診断の質にとどまる。

   節のパターンには型注釈の構文が無い(`test/nonfeatures.t` の patannot)。
   仮に `case p: T =>` の形で型注釈を導入しても、型注釈の中の矢印はこのカウンタでは見分けられない。
   そのため仕様 §7 は、節の最上位に現れる `=>` を節の矢印とし、
   節のパターンに型注釈を導入する場合には、矢印を含む型注釈に括弧を必須にすると定めている。

   構文の壊れた入力で、`fn` の矢印が来ないまま節が終わると、カウンタが残り、
   `RClause` が矢印では pop されない。
   ASI の層は、閉じ括弧を受け取ると先頭に残った `RClause` を強制的に取り除くので、
   ずれはその閉じ括弧までで止まる。
   この処理が無いと、region が 1 枚深いまま、ファイルの末尾まで NL が捨てられる。

   閉じ括弧の pop には守るべき不変条件がある。
   `_ :: (_ :: _ as tl)` と書いてあるとおり、残りが 1 個のときは pop しない。
   そのため `RTop` はスタックから消えず、括弧が釣り合わないソースでもスタックは空にならない。
   `EQ_GREATER` の側の `RClause :: (_ :: _ as tl)` も同じ形で、
   さらに先頭が `RClause` のときだけという条件が付く。
   そのため、節の外にある普通のラムダの `=>` は region を動かさない。

   最後に、昇格した `NL` を渡すときは `t.prev <- Some NL` とする。
   `can_end_statement NL` は偽なので、仮に `NL` が続いても 2 個目は捨てられ、
   区切りが 2 つ並ぶことはない。
   文法の側の `items` も余分な `;` や `NL` を読み飛ばすが、それに頼らずに済む。 *)

  (* ASI の 2 つの述語(§2.10) *)

  (* NL の前に来てよいトークン。文の終わりになれる *)
  let can_end_statement = function
    | RPAREN | RBRACKET | RBRACE | LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ | HASH_IDENT _ | NUMBER _ | TEXT _
    | BOOL _ | HOLE ->
        true
    | _ -> false

  (* NL の後で文を始められるトークン。AND / CASE / MATCH / HANDLE / DOT / BACKSLASH /
     EXTENDS / VERTICAL / 二項演算子は、前の行の続きにするために除いている *)
  let can_begin_statement = function
    | LET | TYPE | NEWTYPE | EFFECT | MODULE | PUB | EXTERN | VAL | DERIVE | WITH | PERFORM | RESUME | RUN | FN
    | LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ | HASH_IDENT _ | NUMBER _ | TEXT _ | BOOL _ | HOLE | EXCLAMATION
    | LBRACE_BLOCK | LBRACE_RECORD | LBRACE_TYPE | LPAREN ->
        true
    | _ -> false

  let rec read_token t =
    let e = pop_reclassified t in
    match e.tok with
    | NL -> (
        match t.regions with
        | (RSuppress | RClause _) :: _ -> read_token t
        | _ ->
            let keep =
              match t.prev with
              | Some p -> can_end_statement p && can_begin_statement (peek_sig t 0).tok
              | None -> false
            in
            if keep then (
              t.prev <- Some NL;
              e)
            else read_token t)
    | tok ->
        (match tok with
        | LPAREN | LBRACKET | LBRACE_RECORD | LBRACE_TYPE -> t.regions <- RSuppress :: t.regions
        | LBRACE_BLOCK -> t.regions <- RBlock :: t.regions
        | RPAREN | RBRACKET | RBRACE -> (
            (* 節の region は閉じ括弧をまたげない。壊れた入力(fn の矢印が来ないまま
               節が終わる形)でカウンタが残り、RClause が pop されなかった場合も、
               ここで先に強制的に取り除き、以降の対応のずれを防ぐ。これが無いと、
               region が 1 枚深いまま、ファイルの末尾まで NL が捨てられる *)
            (match t.regions with
            | RClause _ :: (_ :: _ as tl) -> t.regions <- tl
            | _ -> ());
            match t.regions with _ :: (_ :: _ as tl) -> t.regions <- tl | _ -> ())
        | CASE -> t.regions <- RClause 0 :: t.regions
        | FN -> (
            (* 節のガードの最上位にある fn を数える。括弧の中の fn では先頭が
               RSuppress で、節の本体なら RClause は pop 済みなので、
               ここが数えるのはガードの最上位の fn だけ *)
            match t.regions with RClause n :: tl -> t.regions <- RClause (n + 1) :: tl | _ -> ())
        | EQ_GREATER -> (
            (* 節の矢印か fn の矢印かを見分ける。RClause が数えている fn の本数だけ
               矢印を見送り、残りが 0 のときに pop する。括弧の深さは region スタックが
               すでに見ている(§2.10)。括弧の内側の => では先頭が RSuppress なので、
               RClause は動かない *)
            match t.regions with
            | RClause n :: (_ :: _ as tl) -> if n > 0 then t.regions <- RClause (n - 1) :: tl else t.regions <- tl
            | _ -> ())
        | _ -> ());
        t.prev <- Some tok;
        e

(* ## 2.11 消費者 API

   Menhir の revised API は `unit -> token * position * position` の関数を求める。
   `read` がその関数で、あわせて直前に渡したトークンの開始位置と終了位置を状態に控える
   (そのうち開始位置を構文エラーの報告に使うのは第16章(driver.ml)である)。
   `parse` は、`traditional2revised` で包むだけの薄い層である。

   `all_tokens` は `--dump-tokens` のための出口で、ASI を適用した後のトークン列を EOF まで集める。
   3 つの層すべてを通した結果をそのまま見られるので、ゴールデンテストはこの出口を使う。 *)

  (* ---- 消費者 API ---- *)

  let read t =
    let e = read_token t in
    t.last_sp <- e.sp;
    t.last_ep <- e.ep;
    (e.tok, e.sp, e.ep)

  let parse rule lexer = MenhirLib.Convert.Simplified.traditional2revised rule (fun () -> read lexer)

  (* --dump-tokens 用。ASI を適用した後のトークン列を EOF まで集める *)
  let all_tokens t =
    let rec go acc =
      let e = read_token t in
      match e.tok with EOF -> List.rev (e :: acc) | _ -> go (e :: acc)
    in
    go []

(* ## 2.12 トークンの表示

   `show_token` はほぼ機械的な表だが、3 か所に説明が要る。
   `{blk`、`{rec`、`{ty` は、再分類の結果を目で見るための表記である。
   この表記があるので、`test/tokens.t` のゴールデンが分類の回帰テストになる。
   `<NL>` として現れるのは、ASI が昇格させた改行だけである(捨てた改行は列に現れない)。
   `<EOF>` は、列の最後に 1 個だけ現れる。

   数値は `show_number`(§2.1)で原文の表記を出すので、桁区切りも接尾辞も書いたとおりに出る。
   文字列だけは、`String.escaped` を通して引用符で囲んで出力する。
   ゴールデンの中で、ほかのトークンと見分けられるようにするためである。 *)

  let show_token = function
    | AND -> "and"
    | AT -> "@"
    | ASTERISK -> "*"
    | BACKSLASH -> "\\"
    | BIG_AMPERSAND -> "&&"
    | BIG_EQ -> "=="
    | BIG_VERTICAL -> "||"
    | BOOL b -> string_of_bool b
    | CASE -> "case"
    | CLASS -> "class"
    | COLON -> ":"
    | COMMA -> ","
    | DERIVE -> "derive"
    | DOT -> "."
    | DOTDOTDOT -> "..."
    | EFFECT -> "effect"
    | EOF -> "<EOF>"
    | EQ -> "="
    | EQ_GREATER -> "=>"
    | EXCLAMATION -> "!"
    | EXCLAMATION_EQ -> "!="
    | EXTENDS -> "extends"
    | EXTERN -> "extern"
    | FN -> "fn"
    | GREATER -> ">"
    | GREATER_EQ -> ">="
    | HANDLE -> "handle"
    | HASH_IDENT s -> "#" ^ s
    | HOLE -> "???"
    | HYPHEN -> "-"
    | IF -> "if"
    | INSTANCE -> "instance"
    | LBRACE_BLOCK -> "{blk"
    | LBRACE_RECORD -> "{rec"
    | LBRACE_TYPE -> "{ty"
    | LBRACKET -> "["
    | LESS -> "<"
    | LESS_EQ -> "<="
    | LET -> "let"
    | LOWER_IDENTIFIER s -> s
    | LOWLINE -> "_"
    | LPAREN -> "("
    | MATCH -> "match"
    | MODULE -> "module"
    | NEWTYPE -> "newtype"
    | NL -> "<NL>"
    | NUMBER n -> show_number n
    | PERFORM -> "perform"
    | PLUS -> "+"
    | PUB -> "pub"
    | RBRACE -> "}"
    | RBRACKET -> "]"
    | REC -> "rec"
    | RESUME -> "resume"
    | RPAREN -> ")"
    | RUN -> "run"
    | SEMI -> ";"
    | SOLIDUS -> "/"
    | TEXT s -> "\"" ^ String.escaped s ^ "\""
    | TYPE -> "type"
    | UPPER_IDENTIFIER s -> s
    | VAL -> "val"
    | VERTICAL -> "|"
    | WITH -> "with"
end
