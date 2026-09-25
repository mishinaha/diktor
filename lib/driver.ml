(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第16章 ドライバと終了コード規約

   本章は最後の章である。
   ここまでの 15 章が作った部品を 1 本の流れにつなぎ、
   コマンドライン、標準出力、シェルが見る終了コードという外部との接点に結びつける。
   本章に新しいアルゴリズムは無い。
   本章が定めるのは入出力の規約と、その規約を破らないための処理である。

   ## 配線図

   ```
   argv ──parse_args──▶ options
   FILE.kel ──Lexer(第2章)──▶ トークン列 ──Parser(第3章)──▶ decl list
   Prelude_embed.source ──(まったく同じ経路)──▶ prelude の decl list
                                  │
                                  ▼
                   Elab.flatten_modules(第11章。module の平坦化)
                                  │
                                  ▼
                   Elab.type_check ~prelude(第11章) ──▶ 型の行 + 警告
                                  │
                                  ▼
                   Interp.run ~sink(第14章)
                                  │
                                  ▼
                   Builtin.with_runtime(第13章)が Console.write を sink へ
   ```

   本章が前章(第15章、prelude.kel)から受け取るのは、
   文字列定数に埋め込まれたプレリュードのソースである。
   本章が外へ渡すのは、標準出力と標準エラーに書き出す行、および 1 つの終了コードである。

   本章の設計は次の 3 点にまとめられる。

   - 旗はモードを選ぶだけにし、処理そのものは各章の関数に任せる。
   - CLI と API は同じ関数を通す。
     API は終了コードの層を外して公開する。
     CLI との違いは §16.5 にまとめる。
   - どの例外も本章の外へ出さない。
     例外が 1 つでも外へ出ると、終了コードの規約が守られなくなる。

   3 点目は §16.8 で扱う。 *)
open Aux

(* ## 16.1 旗とモード

   旗は 6 つ、モードは 4 つある。

   | 旗 | 効き先 | 働き |
   |---|---|---|
   | (なし) | `Run` | 型検査してから評価する |
   | `--type-check` | `TypeCheck` | 型検査だけを行い、束縛の型を宣言順に印字する |
   | `--dump-tokens` | `DumpTokens` | ASI 適用後のトークン列を印字する |
   | `--dump-ast` | `DumpAst` | 脱糖後の AST を S 式で印字する |
   | `--no-prelude` | `o_no_prelude` | プレリュードを空にする |
   | `--prelude PATH` | `o_prelude` | 埋め込みのプレリュードの代わりに PATH を読む |
   | `--strict-exhaustive` | `o_strict_exhaustive` | 網羅性と到達不能の警告をエラーにする |

   `usage` の文字列は、使い方の唯一の説明である。
   テスト test/smoke.t は、この文字列をそのまま期待値に持つ。
   文言を変えるとゴールデンテストが落ちるので、旗を足して説明を書き忘れることを防げる。

   `--dump-tokens` は、ASI とブレース再分類(第2章)の結果を機械的に固定するための旗である。
   ASI の判断を目に見える形で固定できるのは、トークン列のゴールデンテストだけである。

   `--no-prelude` は、プレリュードの不具合を切り分けるための旗である。
   第15章 §15.1 で述べたとおり、プレリュードは起動のたびに全文がパースされ型検査されるので、
   処理系の機構が動いていることを確かめるカナリアの役目を持つ。
   その裏返しとして、プレリュード自身の不具合はすべてのテストに混ざる。

   `mode` は排他で、モードの旗を並べると最後のものが勝つ。
   `o_prelude` と `o_no_prelude` は独立ではなく、
   両方を書くと `--no-prelude` が勝つ(§16.4 の `load_prelude` の分岐)。 *)
let usage =
  "usage: diktor [OPTIONS] FILE.kel...\n\
   \  --type-check         型検査のみ。トップレベル束縛の型を \"name : type\" で出力\n\
   \  --dump-tokens        ASI 適用後のトークン列を出力\n\
   \  --dump-ast           脱糖後の AST を S 式で出力\n\
   \  --no-prelude / --prelude PATH\n\
   \  --strict-exhaustive  網羅性・到達不能警告をエラー化\n"

type mode = Run | TypeCheck | DumpTokens | DumpAst

type options = {
  o_mode : mode;
  o_prelude : string option; (* Some PATH で差し替え *)
  o_no_prelude : bool;
  o_strict_exhaustive : bool;
  o_files : string list;
}

let default_options = { o_mode = Run; o_prelude = None; o_no_prelude = false; o_strict_exhaustive = false; o_files = [] }

(* ## 16.2 引数解析

   引数解析に cmdliner は使わない。
   Diktor の依存は menhir と sedlex の 2 つに限っており、
   6 つの旗のためにその範囲を広げる価値はない。
   代わりに、引数リストを頭から読んでいく末尾再帰の `go` を書く。

   `go` の形には要点が 2 つある。

   1 つ目に、`go` は例外ではなく `Result` を返す。
   使い方の誤りは異常事態ではなく、普通の分岐である。
   呼び出し側(§16.8 の `main`)が `Error` を受け取り、使い方を印字して終了コード 64 を返す。
   この形なら、引数解析だけを単体で呼んでも副作用が無い。

   2 つ目に、節の順序が意味を持つ場所が 1 つだけある。
   ハイフンで始まる未知の引数を拒む節は、既知の旗すべての後ろ、ファイル名の節の前に置く。
   前に出すと `--type-check` まで未知の旗として弾かれ、
   後ろに下げると `--typo-check` が入力ファイル名として通ってしまう。
   この節のガードは、添字 0 を取る前に長さを調べる。
   空文字列の引数に添字 0 を取ると例外になるからである。
   空文字列の引数はファイル名として扱われる。
   そのファイルを開く段で `Input_error`(§16.3)が起き、§16.8 の受け皿が終了コード 64 を返す。

   最後に `List.rev` でファイルの順序を戻す。
   畳み込みはファイルを逆順に積むからである。
   ファイルの順序には意味がある。
   複数のファイルは、指定した順に連結して処理する。
   仕様 sample.kel の回帰テストは、この順序を使ってスタブを sample.kel の前に置く。 *)
let parse_args args =
  let rec go opts = function
    | [] -> if opts.o_files = [] then Error "no input files" else Ok { opts with o_files = List.rev opts.o_files }
    | "--type-check" :: rest -> go { opts with o_mode = TypeCheck } rest
    | "--dump-tokens" :: rest -> go { opts with o_mode = DumpTokens } rest
    | "--dump-ast" :: rest -> go { opts with o_mode = DumpAst } rest
    | "--no-prelude" :: rest -> go { opts with o_no_prelude = true } rest
    | "--prelude" :: path :: rest -> go { opts with o_prelude = Some path } rest
    | "--prelude" :: [] -> Error "--prelude requires a path"
    | "--strict-exhaustive" :: rest -> go { opts with o_strict_exhaustive = true } rest
    | arg :: _ when String.length arg > 0 && arg.[0] = '-' -> Error ("unknown option: " ^ arg)
    | file :: rest -> go { opts with o_files = file :: opts.o_files } rest
  in
  go default_options args

(* ## 16.3 前段の実体化と、パースエラーの整形

   字句解析器(第2章)とパーサ(第3章)は、AST のノードに貼るデータをパラメータに取るファンクタである。
   本章は第5章の `Tree.ElabData` を渡して、両者を実体化する。
   この処理系が木に精緻化(elaboration)用のデータを書き込むことは、次の 2 行で決まる。
   別の用途で別のデータを貼るときは、別の実体化を作ればよい。 *)
module Lexer' = Lexer.Make (Tree.ElabData)
module Parser' = Parser.Make (Tree.ElabData)

(* `Parse_error` は、位置まで整形し終えた 1 行を運ぶための、本章専用の例外である。
   menhir が投げる `Parser'.Error` は情報を持たず、どこで詰まったかは、
   字句解析器が覚えている最後のトークンの位置からしか取れない。
   パーサと字句解析器の両方を扱うのは本章だけなので、
   両者の情報を結びつけて整形できるのも本章だけである。

   `main` は `Parse_error` を受け取って印字し、終了コード 2 を返す(§16.8)。 *)
exception Parse_error of string

(* 入力を開けない誤りだけを、この例外に閉じ込める。
   受け皿に届く裸の Sys_error は、出力に書き出せない誤りを表す。
   こう分けておけば、例外の文字列を調べて誤りの種類を推測しなくて済む。
   入力を開く場所を足したときは、with_input で包む。
   包み忘れると、その Sys_error は出力エラーとして終了コード 74 になる *)
exception Input_error of string

let with_input f = try f () with Sys_error msg -> raise (Input_error msg)

(* 出力の書き出しも終了コードの規約に含まれる。
   exit の do_at_exit は Format の標準フォーマッタを flush する。
   stdout や stderr に書けないときは、この flush で Sys_error が起きて受け皿の外に飛び、
   Fatal error と終了コード 2 になる。
   つまり exit 自身が例外を投げうる。
   そこで終了はすべて safe_exit を通す。
   safe_exit は、呼び出し側が決めた終了コードを受け取り、フォーマッタを無効にし、
   チャネルをできる範囲で flush してから、その終了コードで exit する。
   フォーマッタを無効にするのは行儀のよい手ではない。
   しかし Unix._exit を使うには依存に unix を足す必要があり、§16.2 の依存の方針に反する *)
let null_formatter_out =
  {
    Format.out_string = (fun _ _ _ -> ());
    out_flush = (fun () -> ());
    out_newline = (fun () -> ());
    out_spaces = (fun _ -> ());
    out_indent = (fun _ -> ());
  }

let safe_exit n =
  Format.pp_set_formatter_out_functions Format.std_formatter null_formatter_out;
  Format.pp_set_formatter_out_functions Format.err_formatter null_formatter_out;
  (* stdout、stderr の順に flush して、プログラムの出力が診断より先に来る順序を保つ。
     cram は両者を 1 本に併合するからである。flush の失敗は握りつぶす。
     終了コードはもう決まっており、Fatal error と終了コード 2 で上書きさせない *)
  (try flush stdout with Sys_error _ -> ());
  (try flush stderr with Sys_error _ -> ());
  exit n

let die_output msg =
  Printf.eprintf "diktor: 標準出力に書き出せません: %s\n" msg;
  safe_exit 74

let flush_stdout_or_die () = match flush stdout with () -> () | exception Sys_error msg -> die_output msg

(* 位置は `ファイル:行:桁` の形で示す。
   桁は、行頭からのコードポイントの差に 1 を足したもので、バイトの差ではない。
   第2章がそのまま運んでくる `Sedlexing.lexing_positions` はコードポイント単位で数えるので、
   多バイト文字を含む行でも桁はずれない。
   たとえば `あいう` を含む行と `abc` を含む行では、同じ位置の誤りが同じ桁に出る。

   ただし、ずれないのはコードポイントの数までである。
   結合文字も、全角文字も、異体字セレクタも 1 と数えるので、
   エディタが表示する桁とは食い違うことがある。
   表示上の桁まで合わせるには表示幅の表が要り、誤りの位置を示すという目的に対しては割に合わない。 *)
let show_pos = Location.show_pos

(* `dump_tokens_file` は `--dump-tokens` の本体である。
   第2章の 3 層のうち、ASI を通したいちばん外側の列を出力する。
   素のトークン列を出力しても、ASI の判断を固定するという目的を果たせない。 *)
let dump_tokens_file file =
  (* from_filename はファイルを一括で読む。open と読み出しの両方の段で起きる
     Sys_error を入力エラーにするため、この段を with_input で包む。印字は包まない。
     印字の失敗を入力エラーと取り違えないためである *)
  let tokens =
    try with_input (fun () -> Lexer'.all_tokens (Lexer'.from_filename file))
    with Sedlexing.MalFormed ->
      (* parse_with(§16.3)と同じく、ファイル名を付けて報告する *)
      raise (Parse_error (file ^ ": 字句エラー: 不正な UTF-8 バイト列です"))
  in
  List.iter (fun e -> Printf.printf "%4d  %s\n" e.Lexer'.sp.Lexing.pos_lnum (Lexer'.show_token e.Lexer'.tok)) tokens

(* `parse_with` は、パースの入口を 1 つにまとめる関数である。
   上流からは 3 種類の失敗が来る。

   - `Parser'.Error`：menhir が次に進む節を選べなかった(文法に合わない)
   - `Syntax.Syntax_error`：文法は通ったが、脱糖(第3章)が形を拒否した
   - `Sedlexing.MalFormed`：入力が不正な UTF-8 バイト列である

   利用者から見ると、どれも入力を読めなかったという誤りなので、1 行にそろえて `Parse_error` にする。
   前の 2 つには位置を付ける。
   `MalFormed` では位置が失われているので、ファイル名だけを付ける。
   字句解析器の `Lexer.Lex_error` はここでは受けず、§16.8 の受け皿がそのまま受ける。
   種類ごとに区別して報告したくなったときは、この関数で分ければよい。
   分岐点を 1 か所に集めてあるのはそのためである。 *)
let parse_with lexer =
  try Lexer'.parse Parser'.program lexer with
  | Sedlexing.MalFormed ->
      (* 位置は失われているが、ファイル名は分かる。複数のファイルを渡したときに
         どれが壊れているかが分かるよう、ファイル名を付ける *)
      raise (Parse_error (Printf.sprintf "%s: 字句エラー: 不正な UTF-8 バイト列です" lexer.Lexer'.last_sp.Lexing.pos_fname))
  | Parser'.Error ->
      raise (Parse_error (Printf.sprintf "%s: パースエラー(付近のトークンを確認してください)" (show_pos lexer.Lexer'.last_sp)))
  | Syntax.Syntax_error msg ->
      raise (Parse_error (Printf.sprintf "%s: 構文エラー: %s" (show_pos lexer.Lexer'.last_sp) msg))

(* パースの駆動全体を with_input で包む。
   ディレクトリを渡したときの EISDIR などの読み取りエラーは、
   open ではなく読み取りの段で起きるからである *)
let parse_file file = with_input (fun () -> parse_with (Lexer'.from_filename file))

(* `parse_string` は、エラー行に表示するファイル名を引数で受け取る。
   山括弧つきの名前(`<prelude>` や `<string>`)は、実在のファイルではないことを示す印で、
   利用者がその名前のファイルを探さないようにするためのものである。

   山括弧の名前は、実在しないもの(埋め込みのプレリュードと文字列の API)だけに使う。
   `--prelude PATH` で差し替えたプレリュードは実在するファイルなので、実在のパスを名乗る。
   そのため、差し替えたプレリュードに誤りがあるとき、
   利用者はエラー行から自分の渡したパスを読み取れる。 *)
let parse_string ~filename source =
  let lexbuf = Sedlexing.Utf8.from_string source in
  Sedlexing.set_filename lexbuf filename;
  parse_with (Lexer'.from_sedlex lexbuf)

(* ## 16.4 プレリュードの読み込み

   第15章(prelude.kel)は、ビルド時に OCaml の文字列定数へ埋め込まれ、`Prelude_embed.source` になる。
   そのため、インストールされた diktor は実行時にプレリュードのファイルを探さず、
   単一の実行ファイルで完結する。

   プレリュードの出所は 3 つあり、優先順位は次のとおりである。

   1. `--no-prelude`：空の宣言列。何よりも優先する
   2. `--prelude PATH`：PATH の中身を読む。開けなければ §16.8 が終了コード 64 にする
   3. 既定：埋め込みの文字列

   入口の関数は、ユーザのファイルとプレリュードとで異なる。
   ユーザのファイルは `parse_file` を通り、
   プレリュードは出所がファイルでも文字列でも `parse_string` を通る。
   どちらも最後は `parse_with` に合流し、プレリュードだけが通る特別な字句解析器やパーサは無い。
   `--prelude PATH` の場合に `load_prelude` が `In_channel` でファイルを読み、
   中身を文字列として同じ入口へ入れるのはそのためである。

   差し替えたプレリュードは `module` を含みうるので、
   通常の入力と同じく平坦化(第11章)を通す必要がある。
   ただし `load_prelude` は構文木のまま返し、平坦化は呼び出し側が行う(CLI の経路では §16.6)。
   読み込みと平坦化を分けているので、呼び出し側は、
   プレリュードとユーザの宣言の両方に同じ前処理を掛ける責任を負う。
   §16.5 の API も、プレリュードとユーザの宣言の両方を平坦化する。 *)
let load_prelude options =
  if options.o_no_prelude then []
  else
    let source =
      match options.o_prelude with
      (* --prelude PATH は実在のファイルなので、実在のパスを名乗る。
         山括弧の印は、実在しないもの(埋め込みと文字列の API)だけに使う *)
      | Some path ->
          (path, with_input (fun () -> In_channel.with_open_bin path In_channel.input_all))
      | None -> ("<prelude>", Prelude_embed.source)
    in
    let filename, source = source in
    parse_string ~filename source

(* ## 16.5 サブプロセスなしで呼べる API

   API は CLI と同じ経路を通す。
   経路が分かれると、API を通したテストは通るのに CLI は壊れている、という状態が起こりうる。
   本節は、文字列を受け取って結果を返す関数を 2 つ公開する。

   - `type_check_string`：(出力行の一覧, エラー行 option) を返す
   - `eval_string ~sink`：出力先を引数で受け取り、型エラーなら `Error` を返す

   `~sink` で出力先を渡せるので、標準出力を横取りしなくても出力を検査できる。
   第13章のランタイムハンドラが `sink` につながっており、
   `Console.write` の出力は `sink` に渡した関数へ流れる。

   前処理は CLI と同じである。
   `embedded_prelude` が平坦化まで済ませるので、
   プレリュードとユーザの宣言の両方が `flatten_modules` を通ってから型検査に入る。

   ただし、CLI から意図して外してあるものが 3 つある。

   - 終了コードの層。
     型エラーは `exit 1` ではなく値として返る。
     §16.8 の受け皿も無いので、パースの誤り(`Parse_error`)、
     平坦化の誤り(`Aux.Type_error` や `NotImplemented`)、実行時の誤りは値にならず、
     例外のまま呼び出し側へ出る。
   - `--strict-exhaustive` の判定
   - `Interp.cancel_log` の設置(§16.7)

   逆に、API だけが行う処理が 1 つある。
   API は再入するので、先頭で `Decls.reset` を呼んで宣言表を戻す。

   回帰テストは cram で書かれ、実行形を起動して検査する。
   リポジトリの中に、この API を呼ぶコードは無い。
   この API は、Diktor をライブラリとして組み込むプログラムと、
   サブプロセスを起動せずに検査したいテストのための入口である。 *)
(* CLI の経路(§16.6)と同じ前処理を通す。
   平坦化を省くと、プレリュードに module が入ったときに、
   API の経路だけが型検査の内部エラー(平坦化されていない module)で落ちる *)
let embedded_prelude () = Elab.flatten_modules (parse_string ~filename:"<prelude>" Prelude_embed.source)

(* 出力行と診断を整形する。
   行の種別は第11章が値で運び、見た目は本章が決める。
   型の行は `name : type` の形にし、警告は `⚠`、エラーは `!` で始めて、
   先頭の 1 文字で種別を読み分けられる形を保つ *)
let render_line = function Elab.Binding s -> s | Elab.Warning s -> "⚠ " ^ s

let render_error (e : Elab.error) =
  (* start_of を通す。穴埋め(dummy)の span なら、位置なしの形になる *)
  match Option.bind e.Elab.e_loc Location.start_of with
  | Some pos -> Printf.sprintf "! %s: %s: %s" pos e.Elab.e_word e.Elab.e_msg
  | None -> Printf.sprintf "! %s: %s" e.Elab.e_word e.Elab.e_msg

(* 型検査だけを行い、(出力行, エラー行 option) を返す *)
let type_check_string ?(prelude = true) source =
  (* 再入する API なので、宣言表を戻してから始める。順序は reset、flatten、
     type_check である。reset を flatten の後に置くと、flatten が張った同義語が
     消える。CLI の経路は 1 プロセスで 1 プログラムしか処理しないので、reset を呼ばない *)
  Decls.reset ();
  let pre = if prelude then embedded_prelude () else [] in
  let decls = Elab.flatten_modules (parse_string ~filename:"<string>" source) in
  let lines, err = Elab.type_check ~prelude:pre decls in
  (List.map render_line lines, Option.map render_error err)

(* 型検査と評価を行う。出力は sink へ送り、型エラーのときは Error を返す *)
let eval_string ?(prelude = true) ~sink source =
  Decls.reset ();
  let pre = if prelude then embedded_prelude () else [] in
  let decls = Elab.flatten_modules (parse_string ~filename:"<string>" source) in
  match Elab.type_check ~prelude:pre decls with
  | _, Some err -> Error (render_error err)
  | _, None ->
      Interp.run ~sink (pre @ decls);
      Ok ()

(* ## 16.6 型検査の入口と、警告の行き先

   本章は、プレリュードとユーザのファイルを別々に平坦化してから第11章へ渡す。
   2 つを分けたまま渡すのは、型検査器がプレリュードだけを `in_prelude` の下で処理し、
   プレリュード所有の印を付けるためである(第15章(prelude.kel)の §15.2)。
   この印があるので、仕様 sample.kel が `Unit` や `Console` や `Fs` をもう一度宣言しても、
   二重宣言にならない。

   ### 行の種別は値で運ばれてくる

   `--type-check` では型の行をそのまま印字する。
   `Run` では型の行は要らないが、警告は捨てない。
   そこで `Run` のとき(`type_check_files` の `quiet` が真のとき)は、警告だけを標準エラーへ出す。
   警告かどうかは、第11章が返す `out_line` の値をパターン照合して判定する。
   行は `Binding` か `Warning` かの値として届き、`⚠ ` の前置は本章の `render_line` が最後に付ける。

   行の種別は値で持ち、見た目は出口で 1 度だけ作る。
   表示用の文字列から種別を読み取ると、見た目を変えたときに判定が壊れる。
   見た目を変えなくても、読み取り方によっては誤判定が起きる。
   たとえば、警告記号 U+26A0 の UTF-8 の先頭バイトは `\xe2` なので、
   行の先頭バイトだけで判定すると、
   U+2000 から U+2FFF までのどの文字で始まる行も警告と見なしてしまう。

   ### 2 つの脱出口

   `--strict-exhaustive` は、型エラーが無く警告が残った場合に終了コード 1 を返す。
   網羅性検査(第10章)の警告を CI のゲートに使うための旗である。
   既定で警告のままにしてあるのは、網羅性の指摘が誤りの断定ではなく、
   見落としの可能性の報告だからである。
   警告を誤りとして扱うかどうかは、利用者が選ぶ。
   なお、仕様 sample.kel の全文は警告を 1 つも出さずに通る。

   型エラーのときは、そこまでに出せた行と誤りの行を印字して、終了コード 1 で終わる。
   このとき `type_check_files` は例外を投げず、`safe_exit` を通して `exit` を直接呼ぶ。
   `exit` は脱出に例外を使わないので、§16.8 の受け皿に横取りされない。
   例外で抜けると、型エラーが受け皿の `Panic` や `Type_error` の節に入り、
   別の終了コードになりうる。 *)

(* quiet は Run モードを表す。型の行は出さず、警告だけを stderr に出す。
   行の種別は、表示文字列ではなく out_line の値で判定する *)
let type_check_files ?(quiet = false) options =
  (* 平坦化の診断も、出力先をモード単位で決める規約に乗せる。素通しにすると、
     --type-check でも平坦化の「! 未実装:」だけが stderr に出て、規約が二通りになる。
     平坦化は型検査より前のパスなので、平坦化の診断より前に型の行が無いのは構造どおりである *)
  let report (err : Elab.error) =
    (if quiet then (
       flush_stdout_or_die ();
       try prerr_endline (render_error err) with Sys_error _ -> ())
     else print_endline (render_error err));
    flush_stdout_or_die ();
    safe_exit err.Elab.e_exit
  in
  let flatten ds =
    try Elab.flatten_modules ds with
    | Aux.Type_error_at (loc, msg) -> report { Elab.e_loc = Some loc; e_word = "型エラー"; e_exit = 1; e_msg = msg }
    | Aux.Type_error msg -> report { Elab.e_loc = None; e_word = "型エラー"; e_exit = 1; e_msg = msg }
    | Aux.NotImplemented_at (loc, feat) -> report { Elab.e_loc = Some loc; e_word = "未実装"; e_exit = 4; e_msg = feat }
    | NotImplemented feat -> report { Elab.e_loc = None; e_word = "未実装"; e_exit = 4; e_msg = feat }
  in
  let prelude = flatten (load_prelude options) in
  let decls = flatten (List.concat_map parse_file options.o_files) in
  let put l =
    if quiet then (
      match l with
      | Elab.Warning _ ->
          (* stderr へ書く直前に stdout を flush する。stdout はバッファつきで、
             stderr は行ごとに flush されるので、flush を挟まないと、両者を 1 本に
             併合する cram で順序が入れ替わる。stderr が壊れていても診断はできる
             範囲で出すだけにして、プログラムの実行は続ける *)
          flush_stdout_or_die ();
          (try prerr_endline (render_line l) with Sys_error _ -> ())
      | Elab.Binding _ -> ())
    else print_endline (render_line l)
  in
  match Elab.type_check ~prelude decls with
  | lines, None ->
      List.iter put lines;
      (* --strict-exhaustive が数えるのは、利用者に見せた警告(返ってきた行)だけである。
         大域の Elab.warnings を数えると、表示しないプレリュードの警告のせいで、
         警告を 1 行も出さずに終了コード 1 で終わる、という理由の分からない失敗になる *)
      if options.o_strict_exhaustive && List.exists (function Elab.Warning _ -> true | _ -> false) lines then (
        flush_stdout_or_die ();
        safe_exit 1);
      (prelude, decls)
  | lines, Some err ->
      List.iter put lines;
      (* 出力先はモード単位で決める。--type-check はレポートなので全部を stdout へ出す。
         Run は stdout をプログラムの出力専用にし、診断を stderr へ出す *)
      (if quiet then (
         flush_stdout_or_die ();
         try prerr_endline (render_error err) with Sys_error _ -> ())
       else print_endline (render_error err));
      flush_stdout_or_die ();
      safe_exit err.Elab.e_exit

(* ## 16.7 結線

   どの段まで通すかは、モードごとに異なる。

   | モード | 字句 | 構文 | 平坦化 | 型検査 | 評価 |
   |---|---|---|---|---|---|
   | `DumpTokens` | ○ | × | × | × | × |
   | `DumpAst` | ○ | ○ | × | × | × |
   | `TypeCheck` | ○ | ○ | ○ | ○ | × |
   | `Run` | ○ | ○ | ○ | ○ | ○ |

   ダンプ系のモードは、意図して型検査を通さない。
   型が付かないプログラムの字句と構文を見るための旗なので、型検査で止まると役に立たない。
   `DumpAst` が平坦化も飛ばすのは、脱糖した直後の木を見せるためである。
   平坦化は module を展開して名前を書き換えるので、平坦化を通すと、
   パーサが何を作ったかが見えなくなる。

   `Run` は型検査を先に通し、その結果を評価へ渡す。
   型が付かないプログラムは実行しない。

   評価の直前に、`Interp.cancel_log` を差し込む。
   `cancel` 節の中で起きた例外は、巻き戻しを最後まで進めるために抑制するしかないが、
   黙って捨てるとデバッグできなくなる。
   そこで、抑制した例外を本章が標準エラーに印字する。
   印字を第14章ではなく本章で行うのは、何をどう見せるかを出口の側で決めるためである。
   ただし、例外から文言への変換は第14章の `run_cancel` にある。
   既知の例外(`Runtime_error` / `Unwind` / `Sys_error`)だけが日本語の文言になり、
   それ以外は `Printexc` の表現のまま印字される。
   `Printexc` の表現が出ていれば、それは内部エラーの印である。

   評価に渡すのは、連結した `prelude @ decls` である。
   型検査はプレリュード所有の印を付けるために 2 つを区別したが、実行時には区別する理由が無い。 *)
let run_with options =
  (match options.o_mode with
  | DumpTokens -> List.iter dump_tokens_file options.o_files
  | DumpAst -> List.iter (fun file -> Dump.dump_decls stdout (parse_file file)) options.o_files
  | TypeCheck -> ignore (type_check_files options)
  | Run ->
      let prelude, decls = type_check_files ~quiet:true options in
      Interp.cancel_log :=
        (fun msg ->
          (* stderr へ書く直前に stdout を flush する(§16.8 の出力先の規約) *)
          flush_stdout_or_die ();
          try Printf.eprintf "cancel 節で例外が抑制されました: %s\n" msg; flush stderr with Sys_error _ -> ());
      Interp.run ~sink:print_string (prelude @ decls));
  (* モードの最後に stdout を flush し切る。受け皿の中で flush して、
     失敗を終了コード 74 にするためである(§16.8 の不変条件) *)
  flush_stdout_or_die ()

(* ## 16.8 終了コード規約

   diktor の終了コードは、次の規約に従う。

   | コード | 意味 | 出所 |
   |---|---|---|
   | 0 | 正常終了 | `run_with` が最後まで走った |
   | 1 | 型エラー | 第11章の診断、`Aux.Type_error`、`--strict-exhaustive` |
   | 2 | 構文エラー、字句エラー | `Parse_error`、`Lex_error`、不正な UTF-8 |
   | 3 | 実行時エラー | `Runtime_error`、未処理のエフェクト、再帰過多、メモリ不足、内部異常 |
   | 4 | 未実装(仕様にあって Diktor が実装していない機能) | `Aux.NotImplemented`(1u8、Int8、module の入れ子など) |
   | 64 | 使い方の誤り | 引数解析の失敗、入力ファイルを開けない |
   | 74 | 出力に書き出せない | 標準出力への flush の失敗 |

   64 は BSD の sysexits の EX_USAGE、74 は EX_IOERR である。
   独自の番号を選ぶより、既にある慣習に従うほうがシェルスクリプトから扱いやすい。
   74 をプログラムの誤り(3)と分けているのは、
   出力先の故障がプログラムの責任ではないからである。

   ### すべての例外を受ける理由

   OCaml は、捕まえられなかった例外を致命的エラーとして印字し、終了コード 2 で終わる。
   2 は、この規約では構文エラーと字句エラーの番号である。
   `main` が例外を素通しすると、存在しないファイルもメモリ不足も深すぎる再帰も、
   すべて構文エラーとして報告される。
   しかも、OCaml の例外名とバックトレースが利用者に見える。
   そこで `main` は、`run_with` を囲む 1 つの `try` 式ですべての例外を受け、
   規約どおりの診断と終了コードに変える。
   本章では、この `try` 式を受け皿と呼ぶ。
   主な入力に対する報告は次のとおりである。

   | 入力 | 診断 | 終了コード |
   |---|---|---|
   | 存在しないファイル | ファイルを開けません | 64 |
   | 不正な UTF-8 バイト列 | 字句エラー | 2 |
   | module の入れ子、module 内の effect | 未実装 | 4 |
   | 深すぎる再帰 | 実行時エラー | 3 |
   | 巨大な割り当て | 実行時エラー | 3 |
   | 標準出力に書けない(/dev/full) | 出力エラー | 74 |

   表の 3 行目の未実装は、第11章の `flatten_modules` が投げる。
   平坦化は `type_check` の外で走るので、その例外は型検査器の診断の流れを通らない。
   CLI では §16.6 の `type_check_files` が平坦化の例外を受け、
   型検査の診断と同じ書式と出力先で報告する。
   平坦化以外の場所で `type_check` の外へ投げられたものは、
   受け皿の `Aux.Type_error` と `NotImplemented` の節が受ける。

   ### 守るべき不変条件

   - 受け皿は、`run_with` を丸ごと囲む 1 枚だけである。
     そのため、型検査中の再帰過多も評価中の再帰過多も、同じ終了コード 3 になる。
     フェーズごとに終了コードを分けるには、受け皿を分割する必要がある。
   - 規約を最終的に保証するのは、最後の catch-all である。
     OCaml は例外パターンの網羅性を検査しないので、
     新しい例外に節を足し忘れてもコンパイルエラーにならない。
     catch-all は、規約の外の例外をすべて内部エラー(終了コード 3)にする。
     個別の節は、よい文言を出すためにある。
     `Value.Op` 以外の `Unhandled`、`Continuation_already_resumed`、漏れた `Unwind` の専用の節は、
     内部異常に名前を与えるための防御の分岐である。
   - 診断の流れに乗せる例外は、`Elab.type_check` にも節が要る。
     受け皿だけに節を足すと、そこまでに出せた型の行がすべて消える。
     `NotImplemented` は両方に節がある。
     `type_check` の中で起きた `NotImplemented` は、診断の流れに乗る。
     平坦化で起きたものは §16.6 の `type_check_files` が受け、
     それ以外で外へ出たものはこの受け皿が受ける。
   - 入力を開く場所は、`with_input` で包む。
     受け皿は `Sys_error` を、出力に書き出せない誤りとして扱う(§16.3 の `Input_error` による分離)。
     そのため、包み忘れた入力エラーは誤って終了コード 74 で報告される。
   - モードの最後と exit の前に flush し切る。
     既定の flush は Format の at_exit で受け皿の外を走るので、
     失敗すると Fatal error と終了コード 2 になる。
     `flush_stdout_or_die` は受け皿の中で flush し、失敗を終了コード 74 にする。

   最後に、出力先の規約を示す。
   出力先はモード単位で決める。

   | モード | 型の行 | 警告 | 型エラー |
   |---|---|---|---|
   | --type-check | stdout | stdout | stdout |
   | Run | 出さない | stderr | stderr |

   --type-check はレポートを出すモードなので、全部を stdout に出す。
   型の行と誤りの行を、1 本の流れとして比較できるようにするためである。
   Run は stdout をプログラムの出力専用にし、診断を混ぜない。
   受け皿が捕まえる誤りは、どちらのモードでも stderr に出す。
   stderr へ書き出す前には、stdout を flush する。
   flush を挟まないと、両者を 1 本に併合する cram で順序が入れ替わる。 *)
let main () =
  (* SIGPIPE は無視する。既定のままだと、diktor f.kel | head の diktor がシグナルで終了し
     (128 + 13 = 141)、終了コードの規約の外に出る。無視すれば、書き込みが EPIPE で失敗して
     Sys_error を投げ、出力エラーの 74 で終わる *)
  (try Sys.set_signal Sys.sigpipe Sys.Signal_ignore with Invalid_argument _ -> ());
  match parse_args (Array.to_list Sys.argv |> List.tl) with
  | Error msg ->
      Printf.eprintf "diktor: %s\n%s" msg usage;
      safe_exit 64
  | Ok options -> (
      try
        run_with options;
        (* 正常終了も safe_exit を通す。通さないと、書けない stderr に警告が残ったときに
           at_exit の flush が失敗し、終了コード 0 が 2 になる *)
        safe_exit 0
      with
      | NotImplemented feat ->
          Printf.eprintf "! 未実装: %s\n" feat;
          safe_exit 4
      | Aux.NotImplemented_at (loc, feat) ->
          Printf.eprintf "! %s: 未実装: %s\n" (show_pos loc.Location.start) feat;
          safe_exit 4
      | Lexer.Lex_error (msg, pos) ->
          Printf.eprintf "%s: 字句エラー: %s\n" (show_pos pos) msg;
          safe_exit 2
      | Parse_error msg ->
          prerr_endline msg;
          safe_exit 2
      | Input_error msg ->
          Printf.eprintf "diktor: ファイルを開けません: %s\n" msg;
          safe_exit 64
      | Sys_error msg ->
          (* 入力側の誤りは Input_error に閉じ込めてあるので、ここへ来るのは出力側の誤りである *)
          die_output msg
      | Sedlexing.MalFormed ->
          Printf.eprintf "字句エラー: 不正な UTF-8 バイト列です\n";
          safe_exit 2
      | Aux.Type_error_at (loc, msg) ->
          (* type_check の外で投げられた型エラー(位置つき)。
             CLI では、平坦化の型エラーを type_check_files が先に受ける *)
          Printf.eprintf "! %s: 型エラー: %s\n" (show_pos loc.Location.start) msg;
          safe_exit 1
      | Aux.Type_error msg ->
          (* 同上(位置なし) *)
          Printf.eprintf "! 型エラー: %s\n" msg;
          safe_exit 1
      | Out_of_memory ->
          Printf.eprintf "実行時エラー: メモリ不足です\n";
          safe_exit 3
      | Value.Runtime_error msg ->
          Printf.eprintf "実行時エラー: %s\n" msg;
          safe_exit 3
      | Effect.Unhandled (Value.Op (op, _)) ->
          Printf.eprintf "未処理のエフェクト操作: %s\n" (Syntax.Type.name_of op);
          safe_exit 3
      | Effect.Unhandled _ ->
          (* 評価器が起こすエフェクトは Value.Op の 1 種類だけなので、ここへ来たら内部異常である *)
          Printf.eprintf "実行時エラー: 未処理のエフェクトです(内部エラー)\n";
          safe_exit 3
      | Effect.Continuation_already_resumed ->
          (* アフィン検査(§14.10 の r_used)をすり抜けた二重の再開を受ける *)
          Printf.eprintf "実行時エラー: 継続を二重に再開しました(内部エラー)\n";
          safe_exit 3
      | Value.Unwind _ ->
          (* 自動巻き戻しがハンドラの外へ漏れた場合(§14.10 の inst の採番が破れたとき) *)
          Printf.eprintf "実行時エラー: ハンドラの外へ巻き戻しが漏れました(内部エラー)\n";
          safe_exit 3
      | Stack_overflow ->
          Printf.eprintf "実行時エラー: スタックオーバーフロー(再帰が深すぎます)\n";
          safe_exit 3
      | Panic msg ->
          Printf.eprintf "%s\n" msg;
          safe_exit 3
      (* 受け皿の最後の catch-all の節。これが無いと、節に無い例外は OCaml の既定で
         終了コード 2 になり、この規約では構文エラーと区別できず、例外名も利用者に見える。
         節の足し忘れはコンパイルエラーにならないので、ここですべてを受ける。exit は
         脱出のための例外を投げない(Stdlib.exit は do_at_exit のあと sys_exit で終わる)ので、
         この節が他の節の exit を横取りすることはない *)
      | ex ->
          Printf.eprintf "内部エラー: 予期しない例外です: %s\n" (Printexc.to_string ex);
          safe_exit 3 )

(* ## 16.9 bin/main.ml の 1 行の入口

   実行形のソースは 1 行である。

   ```ocaml
   let () = Diktor.Driver.main ()
   ```

   dune は実行形(bin/)とライブラリ(lib/)を分けており、
   実行形は `(modules main)` の 1 モジュールだけを持つ。
   この分け方で、次の 3 つが得られる。

   - ライブラリだけを、他の OCaml プログラムから使える。
     §16.5 の API が意味を持つのは、この分割があるからである。
   - cram テストが実行形を依存に取れる。
     テストが `%{bin:diktor}` を依存に取ると、ライブラリも自動的にビルドされる。
   - 入口が 1 か所に固まり、リンクの単位がはっきりする。

   main.ml には、ライブラリの関数を 1 つ呼ぶ以上のことを書かない。
   引数の前処理や環境変数の読み取りを main.ml に書くと、
   その処理はライブラリの利用者から見えなくなる。
   §16.5 の API を呼ぶプログラムは main.ml を通らないので、CLI と API の経路が分かれる。
   しかも、経路が分かれてもコンパイルエラーは 1 つも出ない。

   ## 16.10 この章のまとめ

   本章はアルゴリズムを含まない。
   しかし、処理系を外から見たときの振る舞いは本章だけが決める。
   たとえば、存在しないファイルを渡されたときに何を報告し、どの終了コードで終わるかは、
   本章が決める。
   本章の設計は、章の冒頭に挙げた 3 点に沿っている。

   1. 旗はモードを選ぶだけである。
      各モードは既存の関数を並べ替えて呼ぶだけで、ドライバ固有の処理を持たない。
   2. 経路を分岐させない。
      プレリュードもユーザのファイルも同じ `parse_with` に合流し、
      CLI も API も同じ `Elab.type_check` を通る。
      ただし、合流点の手前の前処理(平坦化など)がそろっていなければ、経路は合流点より前で分かれる。
      そのため、§16.5 の API も CLI と同じく、プレリュードとユーザの宣言の両方を平坦化する。
   3. 受け皿から例外を漏らさない。
      漏れた例外は OCaml の既定で終了コード 2 になり、終了コードの表と食い違う。
      規約の外の例外は最後の catch-all が受け、出力の flush も受け皿の中で済ませる(§16.8)。 *)
