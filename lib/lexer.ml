(* Copyright (C) 2018-2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第2章 — 字句解析: 3 層と ASI

   文字の並びをトークンの並びに変える仕事を、この章は 3 つの層に分けます。
   1 つにまとめられなかった理由がこの章のほとんどを占めるので、まず結論を
   置きます。

   | 層 | 入口 | 仕事 |
   |---|---|---|
   | 1. 生トークン | `read_raw_token` | 文字 → 62 種のトークン。`{` は未分類のまま |
   | 2. 再分類 | `pop_reclassified` | `{` をブロック / レコード / レコード型に確定 |
   | 3. ASI | `read_token` | region スタックを見て、改行を文区切りに昇格するか捨てる |

   トークン型そのものは全部で 64 種あります(第3章 (parser.mly) の `%token`
   宣言。計画 §5.1 の「81 個 → 64 個」)。層 1 が出せるのはそのうち 62 種で、
   残る `LBRACE_RECORD` / `LBRACE_TYPE` は層 2 だけが作ります。

   Keleut には 2 つの厄介な性質があります。**改行が意味を持つ**ことと、
   **`{` が 3 通りの意味を持つ**ことです(仕様 sample.kel:20-27、計画 §5.3)。
   前者は ASI (automatic semicolon insertion、自動セミコロン挿入)、
   後者は 2 トークン先読みで解きます。層を分ける動機はこの 2 つの相互作用です。

   - 層 3 は層 2 の結果に**依存します**。`{` がブロックなら文区切り region を、
     レコード / レコード型なら改行抑止 region を積むので、分類が済んでいない
     `{` を見ても region を決められません。
   - 層 2 は改行を跨いで 2 トークン先を覗きます。この先読みが層 3 より**下**で
     起きることが要点です。もし ASI 層で先読みすると、まだ消費者に渡していない
     トークンのために region や直前トークンが動いてしまいます。

   > region を動かすのは、トークンを消費者に配達する瞬間だけ。
   > 覗いただけのトークンは何も動かさない。

   この不変条件を守るために、層 1 は状態を持たない写像に保ち、`{` は
   `LBRACE_BLOCK` というプレースホルダで返しておいて、分類は pop の瞬間に
   1 回だけ行います。先読みで覗いたトークンはキューに残り、自分の番が来たとき
   個別に再分類されるので、入れ子の `{` も特別扱いなしに通ります。

   前章 (syntax.ml) からは数値リテラルの表現 `number` / `num_suffix` を、
   Menhir が生成する第3章 (parser.mly) の `Parser` モジュールからはトークン型を
   受け取ります。渡すのは `(tok, sp, ep)` の三つ組で、これがそのまま Menhir の
   `$sloc` になります(D16。トークン自身に位置を持たせるのはやめました)。

   全規則は spike の手書きレキサ `doc/log/260829-1-spike/menhir/lex.ml` で
   sample.kel 全文に当て、この sedlex 版が同じ 2526 トークンを出すことを
   確認しています。ゴールデンは `test/tokens.t`(`--dump-tokens` の出力)で、
   ASI とブレース分類を固定する唯一の手段です。

   この層のコードが**自ら投げる**失敗は `Lex_error` ただ 1 つで、メッセージと
   位置を添えます。第16章 (driver.ml) がこれを終了コード 2 に整形します。
   ただし「この層を通り抜ける」失敗はほかに 2 つあります。不正な UTF-8 バイト列
   に対して sedlex のデコーダが投げる `Sedlexing.MalFormed`(こちらも 2 — §2.6)
   と、`from_filename` の `In_channel.with_open_bin` が投げる `Sys_error`(ファイルを開け
   なかった、で 64)で、どちらも driver 側の別の枝が受けます。 *)
open Syntax

exception Lex_error of string * Lexing.position

(* ## 2.1 数値リテラルは値ではなく表記を運ぶ(D13、計画 §5.5)

   `parse_number` は lexeme の文字列だけを受け取り、`{ n_text; n_is_float;
   n_suffix }` を返す純関数です。**数値へは変換しません。** 変換できないから
   です。`42` がどの型になるかは、リテラルに付いた述語つき単一化変数が
   一般化の時点で既定値に落ちるまで決まりません(sample.kel §2、D8)。
   字句の時点で `Int32.of_string` を呼んでしまうと、その決定を先取りする
   ことになります。実際の変換は第14章 (interp.ml) が elab の解決型を見て
   行い、範囲外は実行時エラーになります。

   接尾辞の切り出しには 1 つだけ注意点があります。**16 進では `f` が数字**
   なので、`0xff` の `f` を接尾辞の始まりと読んではいけません。基数接頭辞が
   あるときは `i` / `u` だけを接尾辞の印とし、走査の開始位置も接頭辞の後ろに
   ずらします。10 進のときだけ `f` を加えます。

   `n_is_float` は 2 つの経路で決まります。接尾辞が `f` ならそれが答え、
   そうでなければ本体に `.` か `e` / `E` が現れるか(= 字句として小数)で決め、
   基数接頭辞つきは決して小数になりません。この判定は第11章 (elab.ml) が
   Integral と Fractional のどちらの述語を貼るかに直結します。

   ビット幅の `int_of_string_opt` は、敵対的検証(260829-2b、頑健性)で
   `1i999999999999999999999` を食わせて見つけた穴の修正です。以前は
   `int_of_string` をそのまま呼んでいたので、桁あふれの `Failure` が
   字句層から素通しで飛び、OCaml の未捕捉例外としてクラッシュしていました。
   いまは解釈できない幅を **-1** に落とし、第11章の `number_ty` が
   「v0 では未対応の接尾辞」として未実装エラー(終了コード 4、G6)に
   整形します。センチネルが -1 なのは、字句の幅が Plus digit で負の幅はソースに
   書けない — つまり**どの実装幅とも衝突しない**からです。最初は 9999 に
   落としていましたが、9999 はユーザが実際に書ける幅なので、`1i9999` と
   書いた場合と桁あふれが区別できませんでした。

   > 字句層が投げてよい例外は `Lex_error` だけ。それ以外は終了コード規約から漏れる。

   符号はここに入りません。`-1` は `HYPHEN` と `NUMBER` の 2 トークンとして
   出し、第3章の前置規則が `n_text` の先頭に `-` を足して 1 つの負リテラルに
   畳みます(D13)。字句で `-` を吸うと `1-2` が引き算に見えなくなるためで、
   AST の上では「単項マイナス演算子が存在しない」という sample.kel:82 の
   意味論がそのまま保たれます。

   `show_number` は、いまや復元ではなく**原文の連結**です。number は
   接尾辞の原文 `n_suffix_text` を持っていて(第1章)、ゴールデンテストと
   型エラーの文面はそれをそのまま出します。かつては解釈済みの `n_suffix`
   から表記を再構成していたので、桁あふれの接尾辞が `1i9999` に、先頭
   ゼロの `1i032` が `1i32` に化けていました。

   > 診断に出す字面は、再構成するのではなく取っておく。 *)

let parse_number text =
  let len = String.length text in
  let has_radix_prefix = len >= 2 && text.[0] = '0' && (match text.[1] with 'x' | 'o' | 'b' -> true | _ -> false) in
  (* 接尾辞の開始位置: 基数接頭辞つきは i/u のみ(16進の f は数字)、10進は i/u/f *)
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
      (* 解釈できない幅は -1 に落として elab の型エラーへ回す(頑健性、260829-2b)。
         字句は Plus digit なので負の幅はソースに書けない = どの実装幅とも
         衝突しない真のセンチネル *)
      let width = match int_of_string_opt (String.sub text (i + 1) (len - i - 1)) with Some w -> w | None -> -1 in
      let suffix = match text.[i] with 'i' -> NsInt width | 'u' -> NsUInt width | _ -> NsFloat width in
      let is_float = match suffix with NsFloat _ -> true | _ -> lexically_float body in
      { n_text = body; n_is_float = is_float; n_suffix = Some suffix; n_suffix_text = raw }

let show_number { n_text; n_suffix_text; _ } = n_text ^ n_suffix_text

(* ## 2.2 sedlex の正規表現

   桁区切り `_` はどの基数でも許し、10 進だけが小数点と指数を持ちます。
   意図的に落としたものが 1 つあります。**先頭 `0` の 8 進表記**です。
   `010` が 8 になる罠は持ち込まない、8 進が要るなら `0o` と書く、という
   裁定です(計画 §5.5)。

   小数部は省略できます (D25) — `1.` は 1.0、`1.e5` は 1e5 です。規則を
   `Opt ('.', Opt (digit, Star (digit | '_')))` と書き、`Star` を小数点の
   直後に**直接置かない**のは、`1._1` が丸ごと 1 つの数値に吸われない
   ためです(小数点の直後が数字でなければ小数部は空で、そこで数値が
   切れます)。最長一致の帰結として `1._1` / `1.foo` は「数値リテラル +
   識別子」に読まれ、数値リテラルへのレコード射影は書けなくなりますが、
   数値は行を持たない値なので失うプログラムはありません。先頭小数点
   (`.5`)は入れません — `t._0` の射影と読み分けが要る形は、仕様が
   `t.0` を避けたのと同じ理由で避けます (sample.kel:151-152)。
   どちらも `test/tokens.t` の dot5 / projnum がゴールデンにしています。

   `int_suffix` を基数つきの側だけに使い、10 進側は正規表現の中に
   `('i' | 'u' | 'f'), Plus digit` を直接書いているのは、2.1 で述べた
   16 進の `f` と同じ理由です。16 進に浮動小数の接尾辞は書けません
   (`f` も `3` も `2` も 16 進数字なので、`f32` は数値本体に吸われます)。
   `parse_number` の判定と字句の規則が同じ線で切れている、ということです。 *)

let digit = [%sedlex.regexp? '0' .. '9']

let hex_digit = [%sedlex.regexp? '0' .. '9' | 'a' .. 'f' | 'A' .. 'F']

let idchar = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z' | '_' | '0' .. '9']

let int_suffix = [%sedlex.regexp? ('i' | 'u'), Plus digit]

let dec_number =
  [%sedlex.regexp?
    ( digit,
      Star (digit | '_'),
      (* 小数部は省略可(D25): 1. も 1.5 も。Opt (digit, Star ...) であって
         Star を直接置かないのは、1._1 が丸ごと 1 つの数値にならないため *)
      Opt ('.', Opt (digit, Star (digit | '_'))),
      Opt (('e' | 'E'), Opt ('+' | '-'), Plus digit),
      Opt (('i' | 'u' | 'f'), Plus digit) )]

let hex_number = [%sedlex.regexp? "0x", hex_digit, Star (hex_digit | '_'), Opt int_suffix]

let oct_number = [%sedlex.regexp? "0o", '0' .. '7', Star ('0' .. '7' | '_'), Opt int_suffix]

let bin_number = [%sedlex.regexp? "0b", ('0' | '1'), Star ('0' | '1' | '_'), Opt int_suffix]

(* ## 2.3 ファンクタと位置の運び方

   `Data` は第1章 (syntax.ml) の付随データファンクタで、AST ノードに何を
   貼るかを決めます。レキサ自身は AST を作りませんが、トークン型を持つのが
   Menhir 生成の `Parser` である以上、同じパラメータを通す必要があります。

   位置は `Sedlexing.lexing_positions` が返す開始 / 終了の対をそのまま
   `{ tok; sp; ep }` に載せて運びます。旧実装はトークン自身に
   `Location.t` を持たせたうえで 3 トークン先読みしていたため、`parse` の
   返す位置が 2 トークンずれていました(既存バグ 0.2-9)。位置をトークンから
   剥がし、キューの要素に付け替えたことでこのずれは構造的に消えています。 *)

module Make (Data : Syntax.Data) = struct
  module Parser = Parser.Make (Data)
  open Parser

  let lexeme = Sedlexing.Utf8.lexeme

  let cur_pos lexbuf = fst (Sedlexing.lexing_positions lexbuf)

(* ## 2.4 キーワード表と、裸のアンダースコア

   識別子はまとめて読んでから表を引きます。表に無ければ
   `LOWER_IDENTIFIER` です。`return` / `cancel` / `structural` / `Type` /
   `EffectRow` を**キーワードにしない**のは意図的で、文脈で普通の識別子
   として受けます(計画 §5.1)。予約語は少ないほど良い。

   1 行目の `_` が要点です。旧実装では識別子の正規表現が長さ 1 の `_` にも
   マッチし、`LOWLINE` の分岐と長さで並んだため、先に書かれた識別子側が
   常に勝って `LOWLINE` は一度も生成されていませんでした(既存バグ 0.2-13)。
   `case _ =>` も `List[_]` も `LOWLINE` に依存しているので、これは文法側から
   見ると致命的です。
   いまは識別子として読んだうえで、**単独の `_` だけ**をこの表で
   `LOWLINE` に振り替えます。`_item`(タプルのラベル)や `_0` は識別子の
   ままである必要があるので、正規表現から裸の `_` を除くのではなく、
   表で分けるのが正しい形でした。 *)

  (* ---- 生トークン層 ---- *)

  let keyword_or_ident = function
    | "_" -> LOWLINE (* 単独の _ のみ。_item / _0 は識別子(計画 §5.1) *)
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

(* ## 2.5 空白・コメント・shebang — そして行番号の罠

   改行は捨てられません。ASI 層が使うので `NL` として上に渡します。ただし
   **連続する改行は 1 個に潰します**。潰さないと空行の数だけ空の文区切りが
   生まれ、文法側が余分な区切りを読み飛ばす負担を負います。
   CR は空白の一種として読み飛ばすので、CRLF は LF だけが改行として働き、
   単独の CR は改行になりません(仕様 §0)。文字列リテラルの中の CR は
   `read_text` がそのまま値に入れます。`test/tokens.t` の crlf / cronly /
   crstr がこの 3 つを固定しています。

   ここで実際に踏んだ罠を 1 つ。

   > **sedlex 3.x は改行を自動追跡する。手で `new_line` を呼ぶと行番号が二重に数えられる。**

   ocamllex 育ちの手は `'\n'` を見るたびに `Sedlexing.new_line` を呼びたく
   なりますが、sedlex 3.x はバッファ側で行頭オフセットを更新済みです。
   併用すると 2 行目が 3 行目として報告され、しかも**エラーが出ないので
   気づきにくい**。ゴールデン `test/tokens.t` が行番号つきで固定されている
   のは、この種の静かなずれを回帰させないためでもあります。

   コメントは 2 種類あります。`//` は行末まで読み飛ばしますが、**改行は
   消費しません**。消費すると ASI が文区切りを作れなくなるからです。
   `/* */` は入れ子を数え、EOF に達したら「unterminated block comment」に
   します。そして 1 つ細工があります。

   > 改行を含むブロックコメントは、`NL` 1 個として振る舞う。

   コメントを足しただけで前後の行が結合したら理不尽です。逆に、改行を
   含まないコメントは行の途中に置いたのと同じ扱いにします。この判定を
   `read_block_comment` が真偽値で返しています。そして **生の `NL` は
   連続しません** (M18 / D58) — 潰すのは層 1 の仕事で、`skip_newlines` が
   行コメントもブロックコメントも跨いで潰します。層 3 の ASI が
   `can_end_statement NL = false` で余分を捨てるのは保険であって仕様では
   ありません(かつてはこの保険に頼っており、それが §2.8 の二次コストの
   入口でした)。

   `#!` はオフセット 0 のときだけ shebang として行末までスキップし、
   それ以外の位置では字句エラーです。`#` は構造的ヴァリアントの印なので、
   ここを緩めると `#Even` の読みと衝突します。 *)

  (* 入れ子ブロックコメント。改行を含んでいたかを返す(計画 §5.2)。
     skip_newlines より前に置くのは相互再帰にしないため(こちらは
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

  (* 連続する改行・空白を1個の NL に潰す。トークンは作らない
     (改行の行カウントは sedlex 3.x が自動追跡する)。
     ここへ来た時点で NL を 1 個出すと決まっているので、後続のコメントが
     2 個目の NL を作る理由はない — 行コメントもブロックコメントも跨いで
     潰す。これが「生トークン列に NL は連続しない」不変条件(M18 / D58)で、
     先読みキューの長さを高々 4(NL + t1 + NL + t2)の定数に抑える。かつては
     コメントを跨がず、コメント 64000 行で先読みが二次の 34 秒だった *)
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

(* ## 2.6 文字列とエスケープ — `Uchar.is_valid` が守っているもの

   `read_unicode_escape` は 16 進を桁ごとに読んで積み上げ、最後に
   **`Uchar.is_valid` で検査してから** `Uchar.of_int` を呼びます。この検査は
   飾りではありません。`Uchar.of_int 0xD800` は `Invalid_argument` を投げる
   ことを実測しており(計画 §5.6)、素通しすると**サロゲート 1 個でクラッシュ
   する**インタプリタになります。`is_valid` は範囲外とサロゲート域の両方を
   落とすので、`\uD800` は普通の字句エラーになります。

   字句エラーは第16章 (driver.ml) が受けて**終了コード 2**に整形します。
   ソースが不正な UTF-8 バイト列だったときも同じ 2 で、こちらは sedlex の
   デコーダが投げる `Sedlexing.MalFormed` を driver が捕まえます。
   どちらも「読めなかった」という同じ種類の失敗なので、同じ番号に寄せて
   あります(型エラーは 1、ファイルが開けないのは 64)。

   ついでに、旧実装の `read_unicode_escape` は積み上げた値 `acc` ではなく
   ループカウンタ `i` を返していました(既存バグ 0.2-1)。`A` が
   `A` ではなく制御文字になるという、テストが 1 本あれば即座に落ちる
   種類の欠陥です。

   `read_text` は `Buffer.add_utf_8_uchar` で組み立てます。エスケープ集合
   (`\u` `\U` と `\a\b\f\n\r\t\v`、および引用符と逆斜線)は旧実装のものを
   そのまま踏襲し、仕様 §2 が同じ集合を明文化しました。生の改行を文字列に
   含められるのは意図的です。集合の全員、生の改行、サロゲート・範囲外・
   未知のエスケープの拒否は `test/tokens.t` の esc / rawnl / surr / oor /
   badesc がゴールデンにしています。 *)

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

   `entry` はトークンと開始 / 終了位置の三つ組です。以降の 2 層はこの型の
   値だけを扱い、`Sedlexing.lexbuf` に触れるのは `read_raw_token` までです。

   sedlex の選択規則は**最長一致**で、同じ長さの候補が複数あるときだけ
   先に書かれた分岐を採ります。したがって `=>` を `=` より先に置くことは
   実は必須ではありません(長さで決着します)。順序が本当に効くのは長さが
   並んだときだけで、旧実装の裸の `_` はまさにそこで壊れていました(§2.4)。
   多文字記号を上にまとめてあるのは、読む人のための整理です。

   末尾の 2 分岐が旧実装との最大の違いです。旧レキサは catch-all を
   `| _ -> EOF` にしていたため、**知らない文字はすべて EOF に化けて**
   いました。`\` がその実例で、パーサからは「そこでファイルが終わった」
   ように見えます。いまは `eof` と `any` を分け、`any` は
   「unexpected character」として字句エラーにします。

   > 読めない入力を EOF と嘘をつくレキサは、その先のすべてのエラーメッセージを壊す。

   この教訓には対があります。`any` に落ちた文字を**そのまま**メッセージに
   出すと、不可視の文字では診断が読めなくなります。実例が BOM(U+FEFF)で、
   仕様 §0 は先頭の BOM を字句エラーと定めていますが、生のまま出すと
   `unexpected character: ` の後ろに見えない 3 バイトが並ぶだけで、
   ゴールデンにも焼けません(エディタや差分ツールが黙って壊します)。
   そこで `any` の分岐は、BOM・C0 制御文字・DEL と C1 制御文字・NBSP(U+00A0)・
   ソフトハイフン(U+00AD)・ゼロ幅系(U+200B〜U+200F)・行区切りと双方向制御
   (U+2028〜U+202E)・ワードジョイナと不可視演算子(U+2060〜U+2064)だけを
   `U+XXXX` の表記に落とし、それ以外は従来どおり字面を出します
   (`test/tokens.t` の bom 群が各区間の代表を固定しています)。全角空白
   (U+3000)のように空白として見える文字は字面のままです — 集合を Unicode の
   分類から機械的に引くのではなく、ゴールデンで困った文字を列挙する方針です。
   `any` まで落ちた BOM は先頭でも途中でも同じ字句エラーになります — 仕様が
   定めているのは先頭だけですが、読めないことに変わりはありません(D102)。
   文字列リテラルとコメントの中は `any` に来ないので対象外で、文字列の中の
   BOM は値の一部になり、コメントの中の BOM は読み飛ばされます。

   > 読めた不可視文字をそのまま出すレキサは、診断を読めなくする。

   `{` だけは確定させずに `LBRACE_BLOCK` を置きます。これは
   「ブロックである」という判断ではなく**未分類の印**で、次の層が必ず
   上書きします。専用の未分類トークンを作らなかったのは、`token` 型は
   Menhir 側の定義であり、文法に現れないトークンを増やすと `--strict` の
   未使用警告に引っかかるためです。 *)

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
        (* 改行入りコメント = NL 1 個(§2.5)。位置は**潰す前に**確保する
           (ゴールデンが NL の位置を固定している)。直後の改行・コメントを
           潰すのは '\n' 分岐と同じ理由 — 生 NL を連続させない(D58) *)
        if read_block_comment lexbuf then (
          let sp, ep = Sedlexing.lexing_positions lexbuf in
          skip_newlines lexbuf;
          { tok = NL; sp; ep })
        else read_raw_token lexbuf
    | "#!" ->
        (* shebang はオフセット0のときだけ(計画 §5.2) *)
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
    | '{' -> here LBRACE_BLOCK (* 未分類プレースホルダ。再分類層が確定する *)
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
        (* 不可視・制御文字は字面を出しても診断にならない。BOM (U+FEFF) が
           その筆頭で、生のまま出すとゴールデンにも焼けない (M21 / F-C6)。
           \n \t \r は上の分岐が先に取るのでここには来ない。集合は §2.7 の
           本文と test/tokens.t の bom 群に列挙してあり、ここと 3 か所で
           一致させる *)
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

(* ## 2.8 レキサの状態と先読みキュー

   `lexbuf` のほかに、上 2 層が共有する状態が 5 つあります。

   - `pending` — 生トークンの先読みキュー。先頭が次に配達されるもの。
   - `regions` — ASI の region スタック。**底は必ず `RTop`**。
   - `prev` — 直前に**消費者へ渡した**有意トークン。`NL` の判定に使う。
   - `last_sp` / `last_ep` — 直近に渡したトークンの位置。構文エラー報告用。

   `peek t i` はキューが足りなければ生トークンを継ぎ足して i 番目を返します。
   `peek_sig t k` は `NL` を飛ばして k 個目の有意トークンを覗きます。**先読みが
   改行を跨ぐ**のは、`{` の分類でも ASI の「次に文を始められるか」の判定でも
   必要だからです。

   末尾追加 `t.pending @ [...]` はキューの長さに対して二次ですが、
   **キューの長さが定数**なので実害になりません。定数で抑えているのは
   §2.5 の不変条件「生トークン列に NL は連続しない」(M18 / D58)です —
   `peek_sig` が覗く必要があるのは高々 4 要素(NL + t1 + NL + t2。有意
   トークンの**間**にも NL は 1 個立ちうる)で、間に何個コメント行が
   あっても層 1 が潰します。
   かつてはこの不変条件が無く、「伸び方がソースの見た目に比例する程度に
   収まるから実害が無い」と説明していました。その根拠は誤りです — 長さが
   線形に伸びれば仕事は二次になり、実測ではコメント 64000 行の入力で
   34 秒かかりました(`{` の分類だけでなく、トップレベルの ASI の
   `can_begin_statement` も同じ道を通ります)。

   ここでも章頭に置いた不変条件が効いています。`peek` は `pending` に足すだけで、
   `regions` にも `prev` にも触れません。覗かれたトークンは後で自分の番が
   来たときに、あらためて `read_token` を通ります。 *)

  (* ---- 再分類層 + ASI 層 ---- *)

  (* region(計画 §5.4-2):
     RBlock = 文区切り region(LBRACE_BLOCK)、
     RSuppress = NL 抑止 region(丸/角括弧・LBRACE_RECORD・LBRACE_TYPE)、
     RClause = case パターン(EQ_GREATER で pop。既存バグ 0.2-14 の修正)。
     RClause の int は、まだ矢印の来ていない fn の本数(M18 / D57)。
     節の矢印と fn の矢印を見分ける唯一の状態 *)
  type region = RTop | RBlock | RSuppress | RClause of int

  type t = {
    lexbuf : Sedlexing.lexbuf;
    mutable pending : entry list; (* 生トークンの先読みキュー(先頭が次) *)
    mutable regions : region list;
    mutable prev : token option; (* 直前に消費者へ渡した有意トークン *)
    mutable last_sp : Lexing.position; (* 直近に消費者へ渡したトークンの位置(エラー報告用) *)
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
    (* チャネルはここで閉じる(M18 / F8)。sedlex の from_channel は遅延
       読みなので、開いたまま渡すと閉じる機会が無く、入力ファイルの数だけ
       fd がプロセス終了まで残る。先に全文を読んで文字列レキサに委ねると
       parse_string と経路も揃う。input_all はパイプでも正しく読む
       (in_channel_length は使えない) *)
    let source =
      try In_channel.with_open_bin filename In_channel.input_all
      with Sys_error msg ->
        (* 読み出し段(Is a directory 等)の Sys_error はファイル名を
           含まない。open 段のものは含むので二重には付けない(M18 検証 —
           複数ファイル指定でどれが原因か分からなかった) *)
        let has_name =
          String.length msg >= String.length filename && String.sub msg 0 (String.length filename) = filename
        in
        raise (Sys_error (if has_name then msg else filename ^ ": " ^ msg))
    in
    let lexbuf = Sedlexing.Utf8.from_string source in
    Sedlexing.set_filename lexbuf filename;
    from_sedlex lexbuf

  let rec peek t i =
    (* キュー長は不変条件 D58 で高々 4 に抑えられているが、万一破れた
       ときに List.length で二次に戻らないよう、構造判定にしてある *)
    let rec has l i = match (l, i) with _ :: _, 0 -> true | _ :: tl, i -> has tl (i - 1) | [], _ -> false in
    if has t.pending i then List.nth t.pending i
    else (
      t.pending <- t.pending @ [ read_raw_token t.lexbuf ];
      peek t i)

  (* NL を飛ばして k 個目(0始まり)の有意トークンを覗く *)
  let peek_sig t k =
    let rec go i k =
      let e = peek t i in
      match e.tok with NL -> go (i + 1) k | _ -> if k = 0 then e else go (i + 1) (k - 1)
    in
    go 0 k

  let is_ident_tok = function LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ -> true | _ -> false

(* ## 2.9 再分類層 — `{` を 3 通りに読み分ける

   sample.kel:20-27 が仕様です。`{` の次を t1、その次を t2 として:

   | t1 | t2 | 種別 |
   |---|---|---|
   | `}` | — | `LBRACE_RECORD`(空。Unit 値 / 空レコード / 空タプル) |
   | `extends` | — | `LBRACE_RECORD`(`{extends R}` — 行変数だけのレコード) |
   | 識別子 | `:` | `LBRACE_TYPE`(レコード型) |
   | 識別子 | `=` / `,` / `with` / `extends` | `LBRACE_RECORD` |
   | それ以外(識別子 `}` を含む) | | `LBRACE_BLOCK` |

   仕様 §0 は、`@` の直後・EffectRow エイリアスの右辺・effect 宣言の本体の
   3 文脈では先読みせずにエフェクト行(または宣言本体)と読む、と書いて
   います。実装はその 3 文脈でも先読みを止めません。`{Print}` は識別子 `}`
   なので `LBRACE_BLOCK`、`{Print, Fs2}` は `LBRACE_RECORD`、`{ print: … }` は
   `LBRACE_TYPE` と、文脈ではなく先読みで分類されます。それでも同じ木に
   なるのは、第3章の `%inline lbrace` が 3 種を束ねて受け、意味の層が要素の
   形から決めるからです(§3.23)。仕様の「先読みしない」は読み手のための
   説明で、観測できる差はありません。この等価性は `test/tokens.t` の
   effbrace / effield がゴールデンにしています(M21 / F-B6)。

   2 トークンで足りるのは、**Keleut に代入演算子が存在しない**からです。
   `{x = 1}` の `=` はレコードのフィールドでしかありえません。もし将来
   `r.f = v` を足したら、この読み分けは即座に壊れます。仕様が
   「入れないこと」と書いているのはそのためで、実装側からも同じ結論です。

   > `{` の 3 分割は「代入が無い」ことに支えられている。代入を足すなら別の設計が要る。

   この設計には正直な代償が 2 つあります。

   1. **`{x}` はブロックであってレコードではない**(sample.kel:27 の裁定
      そのもの — 識別子の次が `}`)。単一フィールドのパンニングは末尾
      カンマで `{x,}` と書けます(t2 が `,` なのでレコードに分類される。
      D56 の帰結)。もちろん `{x = x}` でも同じです。
   2. **`{base with ...}` の base は小文字識別子 1 個に限る**。`{p.x with ...}`
      は t2 が `.` なのでブロックに分類されます。文法側で base を式にしても
      無駄で、字句の時点で決着しています。sample.kel の用例はすべて単一
      識別子なので実害はありませんが、仕様側の制限として計画 §12 に記録
      しました。

   分類は `pop_reclassified` が **pop の瞬間に 1 回だけ**行います。
   `classify_brace` が呼ばれる時点で `{` はすでにキューから外れているので、
   `peek_sig t 0` がそのまま t1 になります。先読みで覗いた `{` はキューに
   生のまま残り、自分が pop されるときに自分の位置から改めて分類されます。
   これで入れ子の `{` も余分な状態なしに正しく分かれます。

   文法側は、対立候補が無い位置(型・パターン・instance 本体・クラス本体・
   module 本体・effect 宣言本体・`run` の本体)を `%inline lbrace` の union
   非終端で受けます。3 分割しても Menhir の conflict は 0 のままです
   (spike S1 で確認)。分類が要るのは式位置だけです。 *)

  (* 計画 §5.3 の表。t1 = `{` の次、t2 = その次(NL スキップ) *)
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

(* ## 2.10 ASI 層 — 2 つの述語

   改行を文区切りに昇格させるかどうかは、たった 1 つの論理積で決めます。

   > 直前のトークンが文を終えられて、かつ次の有意トークンが文を始められるなら、
   > その改行は区切り。そうでなければ捨てる。

   `can_end_statement` は「値として完結しているもの」の集合です。閉じ括弧、
   識別子、リテラル、`???`。`can_begin_statement` は宣言キーワードと、
   式を始められるトークンの集合です。

   **除外した側にこそ設計があります。** ここに入れなかったトークンは
   「前の行の続き」として扱われます。

   - `AND` — `let rec f(x) = ... ⏎ and g(x) = ...` が繋がる。最重要。
   - `CASE` — 節の並びは改行で区切らない(区切りは `case` 自身)。
   - `MATCH` / `HANDLE` — 後置なので、改行してから書ける。
   - `DOT` / `BACKSLASH` — メソッドチェーンとレコード制限の折り返し。
   - `EXTENDS` / `VERTICAL` — 行の続きと `#X | #Y` の折り返し。
   - 二項演算子群 — `1 + ⏎ 2` が繋がる。

   なお行末の `1.` は、小数部の省略 (D25、§2.2) を入れてからは 1 個の
   NUMBER なので文を終えられます。以前は `1` + `DOT` の 2 トークンに
   割れ、DOT が除外側なので改行が捨てられていました — 浮動小数リテラルで
   文が終わるいまの読みのほうが正しい形です。

   逆に `LPAREN` は**入れて**あります。sample.kel:257 の「行頭の `(` は
   前の行の継続とみなさない(改行が優先される)」の実装です。`VAL` と
   `DERIVE` も入れました。無いとクラス本体の `derive structural` の前で
   改行が落ちてパースエラーになることを実測しています(計画 §5.4-1)。

   ここは旧実装が壊れていた場所でもあります。2 つの述語の中身が名前と
   逆で、しかも呼び出しも逆に当てていたため、`let x = 1 ⏎ let y = 2` に
   区切りが入りませんでした(既存バグ 0.2-12)。**最も普通のケースで ASI が
   効いていなかった**わけです。中身を入れ替えたうえで改名し、
   `test/tokens.t` の先頭にこの 2 行を回帰として置いてあります。

   ### region スタック

   述語だけでは足りません。「いま改行に意味があるか」は場所で決まります。

   | region | いつ積むか | 改行の扱い |
   |---|---|---|
   | `RTop` | 最初から。**決して pop しない** | 述語で判定 |
   | `RBlock` | `LBRACE_BLOCK` | 述語で判定 |
   | `RSuppress` | `(` `[` `LBRACE_RECORD` `LBRACE_TYPE` | 常に捨てる |
   | `RClause` | `case` | 常に捨てる(`=>` まで。fn の矢印は数えて見送る) |

   レコード・レコード型・エフェクト行の中で改行が文区切りになることは
   絶対にないので、`{` の 3 分割がそのまま region の分割になります。
   これは分割の副産物ですが、効果は大きい。旧計画が「既知のトレードオフ」
   としていた `{r ⏎ with l = e}` の問題が、分割によって消えました。

   `RClause` は `case` から `=>` までのパターンとガードを覆います。
   ここで改行が区切りになると `case Some(x) ⏎ if x == 1 => x` が書けません。
   pop の引き金は `EQ_GREATER` です。旧実装は `HYPHEN_GREATER` で pop する
   つもりでいましたが、文法側の節は `=>` を使っており、region は正規の
   経路では決して pop されず、閉じ括弧の pop に偶然救われていました
   (既存バグ 0.2-14)。

   **節の最上位の `=>` は常に節の矢印です**(M18 / D57)。`(` `[` は
   `RSuppress` を、`{` は `RBlock` を積むので、括弧に包まれた矢印は先頭を
   `RClause` でなくしてくれます。つまり

   ```
   case Some(x) if pred(fn(y) => y) =>   // 内側の => は region を動かさない
   ```

   は最初から無事でした。region スタックが実質的に括弧の深さを見ている
   からです。唯一見分けが要るのは、ガードの**最上位**に括弧に包まず置いた
   ラムダの矢印で、これは `RClause` が「まだ矢印の来ていない `fn` の本数」を
   数えて見送ります。かつてはこの見分けが無く、最上位の `fn(y) => y` の
   矢印で region が早期 pop し、続きの改行に区切りが入ってパースエラーに
   なりました(型の付くプログラムでは踏めない — その形のガードは必ず
   Boolean でない — ので、症状は診断品質の差だけでしたが、6 行で消えます)。
   なお、かつて本文がここに挙げていた `case x: (Int32) => Int32 => e` という
   例は**そもそも書けません** — 節パターンに型注釈の構文が無く、`:` の位置で
   パースエラーになります(実測)。将来 `case p: T =>` を導入するなら、
   型注釈の中の矢印はこのカウンタでは見分けられないので、「型注釈内の
   矢印には括弧必須」を仕様側の規則として引き受けるのが正しい形です (D57)。
   仕様 §7 は 2026-09-12 の改訂でその規則を将来の形として明文化し、
   現状は無いことを `test/nonfeatures.t` の patannot が固定しています。
   副作用を 1 つ正直に: 構文の壊れた入力で `fn` の矢印が来ないまま節が
   終わると、カウンタが残って `RClause` が矢印では pop されません。
   閉じ括弧が先頭の `RClause` を強制解消するので、ずれはその閉じ括弧
   までで止まります(強制解消が無かったときは region が 1 枚深いまま
   **ファイル末尾まで** NL が落ちました — 検証で実測)。

   閉じ括弧の pop には守るべき不変条件があります。`_ :: (_ :: _ as tl)` と
   書いてあるとおり、**残り 1 個のときは pop しません**。つまり `RTop` は
   決してスタックから消えず、括弧が釣り合わないソースでもスタックが空に
   なりません。`EQ_GREATER` 側の `RClause :: (_ :: _ as tl)` も同じ形で、
   さらに「先頭が `RClause` のときだけ」という条件が付くので、節の外にある
   普通のラムダの `=>` は region を動かしません。

   最後に、昇格した `NL` を渡すときは `t.prev <- Some NL` を置きます。
   これで連続する改行の 2 個目は `can_end_statement NL` が偽になって捨てられ、
   区切りが 2 つ並ぶことがありません。文法側の `items` は余分な `;` / `NL` を
   読み飛ばす形にしてありますが(計画 §5.4)、それに頼らずに済みます。 *)

  (* 計画 §5.4-1 の述語(既存バグ 0.2-12: 中身を入れ替えたうえで改名済み) *)

  (* NL の前に来てよい = 文終端になれる *)
  let can_end_statement = function
    | RPAREN | RBRACKET | RBRACE | LOWER_IDENTIFIER _ | UPPER_IDENTIFIER _ | HASH_IDENT _ | NUMBER _ | TEXT _
    | BOOL _ | HOLE ->
        true
    | _ -> false

  (* NL の後で文を開始できる。AND / CASE / MATCH / HANDLE / DOT / BACKSLASH /
     EXTENDS / VERTICAL / 二項演算子群は意図的に除外(行継続、計画 §5.4) *)
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
            (* 節 region は閉じ括弧を跨げない。壊れた入力(fn の矢印が来ない
               まま節が終わる形)でカウンタが残り RClause が落ちなかった
               場合も、ここで先に強制解消して以降の対応ずれを防ぐ(M18 検証 —
               かつては 1 枚深いままファイル末尾まで NL が落ちた) *)
            (match t.regions with
            | RClause _ :: (_ :: _ as tl) -> t.regions <- tl
            | _ -> ());
            match t.regions with _ :: (_ :: _ as tl) -> t.regions <- tl | _ -> ())
        | CASE -> t.regions <- RClause 0 :: t.regions
        | FN -> (
            (* 節のガード最上位の fn を数える(D57)。括弧内の fn は先頭が
               RSuppress、節本体なら pop 済みなので、ここが動くのは
               ガード最上位だけ *)
            match t.regions with RClause n :: tl -> t.regions <- RClause (n + 1) :: tl | _ -> ())
        | EQ_GREATER -> (
            (* 節の矢印か fn の矢印か。RClause が数えている fn の分だけ矢印を
               見送り、余ったところで pop する(D57)。深さは region スタックが
               既に見ている(§2.10)。括弧の内側の => は先頭が RSuppress なので
               安全 *)
            match t.regions with
            | RClause n :: (_ :: _ as tl) -> if n > 0 then t.regions <- RClause (n - 1) :: tl else t.regions <- tl
            | _ -> ())
        | _ -> ());
        t.prev <- Some tok;
        e

(* ## 2.11 消費者 API

   Menhir の revised API は `unit -> token * position * position` を求めます。
   `read` がそれで、ついでに直近の位置を状態に控えます(構文エラーの報告に
   使うのは第16章 (driver.ml) です)。`parse` は `traditional2revised` で
   包むだけの薄い層です。

   `all_tokens` は `--dump-tokens` のための出口で、**ASI 適用後**の列を
   EOF まで集めます。3 層すべてを通した結果をそのまま見られるので、
   ゴールデンテストはここを使います。字句の仕様は散文では固定できません。
   固定できるのはこの出力だけです。 *)

  (* ---- 消費者 API ---- *)

  let read t =
    let e = read_token t in
    t.last_sp <- e.sp;
    t.last_ep <- e.ep;
    (e.tok, e.sp, e.ep)

  let parse rule lexer = MenhirLib.Convert.Simplified.traditional2revised rule (fun () -> read lexer)

  (* --dump-tokens 用: ASI 適用後のトークン列を EOF まで *)
  let all_tokens t =
    let rec go acc =
      let e = read_token t in
      match e.tok with EOF -> List.rev (e :: acc) | _ -> go (e :: acc)
    in
    go []

(* ## 2.12 トークンの表示

   ほぼ機械的な表ですが、3 か所だけ読み方があります。`{blk` `{rec` `{ty` は
   再分類の結果を目で見るための表記で、これがあるおかげで
   `test/tokens.t` のゴールデンが分類の回帰テストになります。`<NL>` は
   ASI が**昇格させた**改行だけが現れます(捨てられた改行は列に無い)。
   `<EOF>` は最後に必ず 1 個。

   数値は `show_number`(§2.1)で表記を復元するので、桁区切りも接尾辞も
   書いたとおりに出ます。文字列だけは `String.escaped` を通した引用符つきで
   出力します。ゴールデンの中で他のトークンと見分けが付くようにするためです。 *)

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
