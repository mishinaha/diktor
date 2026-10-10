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
   - CLI の経路では、どの例外も `main` の外へ出さない。
     例外が 1 つでも外へ出ると、終了コードの規約が守られなくなる。

   3 点目は §16.8 で扱う。 *)
open Aux

(* ## 16.1 旗とモード

   旗は 7 つ、モードは 5 つある。

   | 旗 | 効き先 | 働き |
   |---|---|---|
   | (なし) | `Run` | 型検査してから評価する |
   | `--type-check` | `TypeCheck` | 型検査だけを行い、束縛の型を宣言順に印字する |
   | `--dump-tokens` | `DumpTokens` | ASI 適用後のトークン列を印字する |
   | `--dump-ast` | `DumpAst` | 脱糖後の AST を S 式で印字する |
   | `--repl` | `Repl` | 標準入力から入力を読み、入力ごとに型検査して実行する(§16.6b) |
   | `--no-prelude` | `o_no_prelude` | プレリュードを空にする |
   | `--prelude PATH` | `o_prelude` | 埋め込みのプレリュードの代わりに PATH を読む |
   | `--strict-exhaustive` | `o_strict_exhaustive` | 網羅性と到達不能の警告をエラーにする(`--repl` では効かない) |
   | `--import-path DIR` | `o_import_path` | import の検索パスに DIR を足す。繰り返して書け、書いた順に探す(§16.3b) |

   `usage` の文字列は、使い方の唯一の説明である。
   テスト test/smoke.t は、この文字列をそのまま期待値に持つ。
   文言を変えるとゴールデンテストが落ちるので、旗を足して説明を書き忘れることを防げる。

   `--dump-tokens` は、ASI とブレース再分類(第2章)の結果を機械的に固定するための旗である。
   ASI の判断を目に見える形で固定できるのは、トークン列のゴールデンテストだけである。

   `--no-prelude` は、プレリュードの不具合を切り分けるための旗である。
   第15章 §15.1 で述べたとおり、`TypeCheck` と `Run` のモードでは、
   プレリュードは起動のたびに全文がパースされ型検査されるので、
   処理系の機構が動いていることを確かめるカナリアの役目を持つ。
   その裏返しとして、埋め込みのプレリュード自身の不具合は、
   この 2 つのモードで `--no-prelude` も `--prelude PATH` も渡さないすべてのテストに混ざる。

   `mode` は排他で、モードの旗を並べると最後のものが勝つ。
   `o_prelude` と `o_no_prelude` は独立ではなく、
   両方を書くと `--no-prelude` が勝つ(§16.4 の `load_prelude` の分岐)。 *)
let usage =
  "usage: diktor [OPTIONS] FILE.kel...\n\
   \  --type-check         型検査のみ。トップレベル束縛の型を \"name : type\" で出力\n\
   \  --dump-tokens        ASI 適用後のトークン列を出力\n\
   \  --dump-ast           脱糖後の AST を S 式で出力\n\
   \  --repl               対話的に実行する(FILE は不要)\n\
   \  --no-prelude / --prelude PATH\n\
   \  --strict-exhaustive  網羅性・到達不能警告をエラー化\n\
   \  --import-path DIR    import の検索パスに DIR を足す(繰り返せる)\n"

type mode = Run | TypeCheck | DumpTokens | DumpAst | Repl

type options = {
  o_mode : mode;
  o_prelude : string option; (* Some PATH で差し替え *)
  o_no_prelude : bool;
  o_strict_exhaustive : bool;
  o_files : string list;
  o_import_path : string list; (* --import-path DIR。書いた順 *)
}

let default_options =
  { o_mode = Run; o_prelude = None; o_no_prelude = false; o_strict_exhaustive = false; o_files = []; o_import_path = [] }

(* ## 16.2 引数解析

   引数解析に cmdliner は使わない。
   Diktor の依存は menhir と sedlex の 2 つに限っており(OCaml の配布物に含まれる `unix` を除く。§16.3b)、
   少数の旗のためにその範囲を広げる価値はない。
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
   連結したファイル群は 1 個の起点の単位で、各ファイルの先頭の import は、
   起点の先頭に集めたものとして扱う(§16.3b)。
   連結したファイルのどれかを import すると誤りにする。
   同じ宣言が起点と依存先の両方に現れるからである。
   仕様 sample.kel の回帰テストは、この順序を使ってスタブを sample.kel の前に置く。
   言語仕様は複数のファイルの扱いを定めない。
   この連結は diktor の取り決めである。 *)
let parse_args args =
  let rec go opts = function
    | [] ->
        if opts.o_files = [] && opts.o_mode <> Repl then Error "no input files"
        else if opts.o_files <> [] && opts.o_mode = Repl then Error "--repl takes no input files"
        else Ok { opts with o_files = List.rev opts.o_files }
    | "--type-check" :: rest -> go { opts with o_mode = TypeCheck } rest
    | "--repl" :: rest -> go { opts with o_mode = Repl } rest
    | "--dump-tokens" :: rest -> go { opts with o_mode = DumpTokens } rest
    | "--dump-ast" :: rest -> go { opts with o_mode = DumpAst } rest
    | "--no-prelude" :: rest -> go { opts with o_no_prelude = true } rest
    | "--prelude" :: path :: rest -> go { opts with o_prelude = Some path } rest
    | "--prelude" :: [] -> Error "--prelude requires a path"
    | "--strict-exhaustive" :: rest -> go { opts with o_strict_exhaustive = true } rest
    | "--import-path" :: dir :: rest -> go { opts with o_import_path = opts.o_import_path @ [ dir ] } rest
    | "--import-path" :: [] -> Error "--import-path requires a directory"
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
   上流から来る失敗のうち、この関数が受けるのは次の 4 種類である。

   - `Parser'.Error`：menhir が次に進む節を選べなかった(文法に合わない)
   - `Syntax.Syntax_error`：文法は通ったが、脱糖(第3章)が形を拒否した
   - `Syntax.Syntax_error_at`：同じく脱糖が形を拒否し、誤りの位置を指定した
   - `Sedlexing.MalFormed`：入力が不正な UTF-8 バイト列である

   利用者から見ると、どれも入力を読めなかったという誤りなので、1 行にそろえて `Parse_error` にする。
   前の 3 つには位置を付ける。
   `Syntax_error_at` には指定された位置を、ほかの 2 つには最後に読んだトークンの位置を使う。
   `MalFormed` では位置が失われているので、ファイル名だけを付ける。
   字句解析器の `Lexer.Lex_error` はここでは受けず、§16.8 の受け皿がそのまま受ける。
   種類ごとに区別して報告したくなったときは、この関数で分ければよい。
   分岐点を 1 か所に集めてあるのはそのためである。 *)
let parse_unit_with lexer =
  try Lexer'.parse Parser'.program lexer with
  | Sedlexing.MalFormed ->
      (* 位置は失われているが、ファイル名は分かる。複数のファイルを渡したときに
         どれが壊れているかが分かるよう、ファイル名を付ける *)
      raise (Parse_error (Printf.sprintf "%s: 字句エラー: 不正な UTF-8 バイト列です" lexer.Lexer'.last_sp.Lexing.pos_fname))
  | Parser'.Error ->
      raise (Parse_error (Printf.sprintf "%s: パースエラー(付近のトークンを確認してください)" (show_pos lexer.Lexer'.last_sp)))
  | Syntax.Syntax_error msg ->
      raise (Parse_error (Printf.sprintf "%s: 構文エラー: %s" (show_pos lexer.Lexer'.last_sp) msg))
  | Syntax.Syntax_error_at (pos, msg) -> raise (Parse_error (Printf.sprintf "%s: 構文エラー: %s" (show_pos pos) msg))

(* import はコマンド行で渡したファイルにだけ書ける。プレリュードと文字列の API は、
   相対パスの基準になるファイルを持たないので、import があれば構文エラーにする *)
let parse_with lexer =
  match parse_unit_with lexer with
  | [], ds -> ds
  | im :: _, _ ->
      raise
        (Parse_error
           (Printf.sprintf "%s: 構文エラー: import はコマンド行で渡したファイルにだけ書けます"
              (show_pos im.Syntax.im_loc.Location.start)))

(* パースの駆動全体を with_input で包む。
   ディレクトリを渡したときの EISDIR などの読み取りエラーは、
   open ではなく読み取りの段で起きるからである *)
let parse_file file = with_input (fun () -> parse_unit_with (Lexer'.from_filename file))

(* ## 16.3b import 先の読み込み

   コマンド行で渡したファイル群(起点)から import をたどり、依存する単位を集める。
   起点の各ファイルの import を書いた順に、深さ優先でたどる。
   単位の列は帰りがけ順(依存される側が先)で、同じファイルは 1 回だけ読む。
   循環は、訪問中のファイルの列で検出する。

   ファイルの同一性は、シンボリックリンクを解決した絶対パス(`Unix.realpath`)で決める。
   別の綴りやリンクで同じファイルを 2 回読み込むと、型が別物になり、初期化も 2 回になるからである。
   `unix` は OCaml の配布物に含まれるので、
   §16.2 の依存の方針(menhir と sedlex に限る)の対象外とする。

   利用者に見せるパス(`u_display`)は、絶対パスではなく次の綴りにする。
   cram の出力に作業ディレクトリが現れないようにするためである。

   - 起点は、コマンド行に書いた引数のままである。
   - 相対パスの import は、import を書いたファイルの表示のディレクトリにパスと `.kel` を連結し、
     `.` の成分を除き、`..` を直前の成分と相殺した綴りである。直前の成分が無い `..` は残す。
   - 検索パスの import は、`--import-path` に書いたディレクトリにパスと `.kel` を連結し、
     相対パスと同じく `.` と `..` を相殺した綴りである。

   相殺した綴りが同じファイルを指さないとき(シンボリックリンクの下の `..`)は、
   開くパスから `.` の成分だけを除いた綴りを使う。

   字句解析器にはこの綴りをファイル名として渡すので、診断の位置もこの綴りになる。
   開くのは、相殺をしない連結のパス(`u_path`)である。
   シンボリックリンクの下の `..` は、綴りの相殺と OS の解決で行き先が違いうるからである。

   パスの形の規則は次のとおりである。
   区切りは `/` に固定し、コロン(`kel:` などの前置の予約)と絶対パスは書けない。
   拡張子 `.kel` は処理系が付けるので、パスに書くと誤りにする。
   相対パスは、先頭の `./` 1 個か `../` の繰り返しで始め、その後の成分に空、`.`、`..` は書けない。
   それ以外は検索パスの中を探し、複数のディレクトリで見つかれば誤りにする。
   検索パスの順序で結果が変わらないようにするためである。 *)
let import_error loc msg = raise (Aux.Import_error (loc, msg))

type unit_src = {
  u_id : string; (* realpath。同一性の判定だけに使う *)
  u_display : string;
  u_path : string;
  u_imports : Syntax.import_decl list;
  u_decls : Tree.Tree.decl list;
  mutable u_targets : (Syntax.import_decl * string) list; (* import 文と、行き先の同一性 *)
}

let normalize_display p =
  let rec go acc = function
    | [] -> List.rev acc
    | ("" | ".") :: rest -> go acc rest
    | ".." :: rest -> ( match acc with x :: acc' when x <> ".." -> go acc' rest | _ -> go (".." :: acc) rest)
    | c :: rest -> go (c :: acc) rest
  in
  let s = String.concat "/" (go [] (String.split_on_char '/' p)) in
  if String.length p > 0 && p.[0] = '/' then "/" ^ s else s

(* パスの形を検査し、(相対なら Some 上る段数、検索パスなら None) と残りの成分を返す *)
let split_import_path loc src =
  if src = "" then import_error loc "import のパスが空です";
  if String.contains src ':' then
    import_error loc ("import のパスにコロンは書けません(\"kel:\" などの前置は予約されています): " ^ src);
  if String.contains src '\\' then import_error loc ("import のパスの区切りは / です: " ^ src);
  if src.[0] = '/' then import_error loc ("import のパスに絶対パスは書けません: " ^ src);
  if Filename.check_suffix src ".kel" then import_error loc ("import のパスに拡張子 .kel は書きません: " ^ src);
  let comps = String.split_on_char '/' src in
  (match comps with "." :: ".." :: _ -> import_error loc ("import のパスの ./ と ../ は混ぜられません: " ^ src) | _ -> ());
  let rel, rest =
    match comps with
    | "." :: rest -> (Some 0, rest)
    | ".." :: _ ->
        let rec ups n = function ".." :: rest -> ups (n + 1) rest | rest -> (Some n, rest) in
        ups 0 comps
    | _ -> (None, comps)
  in
  if rest = [] then import_error loc ("import のパスにファイル名がありません: " ^ src);
  List.iter (fun c -> if c = "" || c = "." || c = ".." then import_error loc ("import のパスの成分が不正です: " ^ src)) rest;
  (rel, rest)

let realpath p = with_input (fun () -> try Unix.realpath p with Unix.Unix_error (e, _, _) -> raise (Sys_error (p ^ ": " ^ Unix.error_message e)))

(* 相殺した綴りが同じファイルを指さないとき(シンボリックリンクの下の .. など)は、
   相殺しない開くパスをそのまま表示に使う。別の実在のファイルの名前で診断を出さないためである *)
let faithful_display ~id ~path display =
  (* . の成分を除くことは、シンボリックリンクがあっても行き先を変えない *)
  let undotted =
    let comps = List.filter (fun c -> c <> "." && c <> "") (String.split_on_char '/' path) in
    (if String.length path > 0 && path.[0] = '/' then "/" else "") ^ String.concat "/" comps
  in
  match Unix.realpath display with
  | r when r = id -> display
  | _ -> undotted
  | exception Unix.Unix_error _ -> undotted

(* import 文の行き先を (開くパス, 表示, 同一性) で返す *)
let resolve_import ~import_path (importer : unit_src) (im : Syntax.import_decl) =
  let loc = im.Syntax.im_loc and src = im.Syntax.im_source in
  let rel, comps = split_import_path loc src in
  let file = String.concat "/" comps ^ ".kel" in
  match rel with
  | Some ups ->
      let prefix = if ups = 0 then "./" else String.concat "" (List.init ups (fun _ -> "../")) in
      let path = Filename.concat (Filename.dirname importer.u_path) (prefix ^ file) in
      let display = normalize_display (Filename.dirname importer.u_display ^ "/" ^ prefix ^ file) in
      if Sys.file_exists path then
        let id = realpath path in
        (path, faithful_display ~id ~path display, id)
      else import_error loc (Printf.sprintf "import 先が見つかりません: %s(%s)" src display)
  | None -> (
      let found =
        List.filter_map
          (fun d ->
            let path = Filename.concat d file in
            if Sys.file_exists path then
              let id = realpath path in
              Some (path, faithful_display ~id ~path (normalize_display ((if d = "" then "." else d) ^ "/" ^ file)), id)
            else None)
          import_path
      in
      (* 同じファイルを複数の検索パスの綴りで見つけたものは 1 つと数える *)
      let distinct =
        List.fold_left (fun acc ((_, _, id) as c) -> if List.exists (fun (_, _, id') -> id' = id) acc then acc else acc @ [ c ]) [] found
      in
      match distinct with
      | [ c ] -> c
      | [] -> import_error loc ("import 先が検索パスに見つかりません: " ^ src)
      | cs ->
          import_error loc
            (Printf.sprintf "import 先が検索パスに複数あります: %s(%s)" src (String.concat "、" (List.map (fun (_, d, _) -> d) cs))))

let read_unit ~path ~display ~id =
  let imports, decls =
    with_input (fun () ->
        try parse_unit_with (Lexer'.from_filename ~display path)
        with Sys_error msg when String.starts_with ~prefix:path msg ->
          (* 開く段の誤りは開くパスを含むので、表示の綴りに替える *)
          raise (Sys_error (display ^ String.sub msg (String.length path) (String.length msg - String.length path))))
  in
  { u_id = id; u_display = display; u_path = path; u_imports = imports; u_decls = decls; u_targets = [] }

(* (依存する単位の帰りがけ順の列, 起点のファイルの列) を返す *)
let load_units options =
  let roots = List.map (fun f -> read_unit ~path:f ~display:f ~id:(realpath f)) options.o_files in
  let root_ids = List.map (fun u -> u.u_id) roots in
  let finished : (string, unit) Hashtbl.t = Hashtbl.create 8 in
  let order = ref [] in
  (* stack は訪問中の (同一性, 表示) の列で、先頭が最も新しい *)
  let rec visit stack (u : unit_src) =
    List.iter
      (fun (im : Syntax.import_decl) ->
        let path, display, id = resolve_import ~import_path:options.o_import_path u im in
        u.u_targets <- u.u_targets @ [ (im, id) ];
        (if List.exists (fun (id', _) -> id' = id) stack then
           let rec from = function [] -> [] | ((id', _) :: _) as l when id' = id -> l | _ :: rest -> from rest in
           let cycle = List.map snd (from (List.rev stack)) @ [ display ] in
           import_error im.Syntax.im_loc ("import が循環しています: " ^ String.concat " → " cycle));
        if List.mem id root_ids then import_error im.Syntax.im_loc ("コマンド行で連結したファイルは import できません: " ^ im.Syntax.im_source);
        if not (Hashtbl.mem finished id) then (
          let dep = read_unit ~path ~display ~id in
          visit ((id, display) :: stack) dep;
          Hashtbl.replace finished id ();
          order := dep :: !order))
      u.u_imports
  in
  List.iter (fun r -> visit [ (r.u_id, r.u_display) ] r) roots;
  (List.rev !order, roots)

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

   入口の関数は、利用者のファイルとプレリュードとで異なる。
   利用者のファイルは `parse_file` を通り、
   プレリュードは出所がファイルでも文字列でも `parse_string` を通る。
   どちらも最後は `parse_with` に合流し、プレリュードだけが通る特別な字句解析器やパーサは無い。
   `--prelude PATH` の場合に `load_prelude` が `In_channel` でファイルを読み、
   中身を文字列として同じ入口へ入れるのはそのためである。

   差し替えたプレリュードは `module` を含みうるので、
   通常の入力と同じく平坦化(第11章)を通す必要がある。
   ただし `load_prelude` は構文木のまま返し、平坦化は呼び出し側が行う(CLI の経路では §16.6)。
   読み込みと平坦化を分けているので、呼び出し側は、
   プレリュードと利用者の宣言の両方に同じ前処理を掛ける責任を負う。
   §16.5 の API も、プレリュードと利用者の宣言の両方を平坦化する。 *)
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
   プレリュードと利用者の宣言の両方が `flatten_modules` を通ってから型検査に入る。

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
let embedded_prelude () =
  Elab.flatten_modules ~unit:Decls.std_unit (parse_string ~filename:"<prelude>" Prelude_embed.source)

(* 出力行と診断を整形する。
   行の種別は第11章が値で運び、見た目は本章が決める。
   型の行は第11章が `name : type` の形で渡すので、そのまま出す。
   警告には `⚠ ` を、エラーには `! ` を前置して、先頭の 1 文字で種別を読み分けられる形を保つ *)
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

   本章は、プレリュードを平坦化し、
   利用者の単位の列(§16.3b)とともに第11章の `type_check_units` へ渡す。
   利用者の単位の平坦化は、第11章が単位ごとに行う。
   import した名前を、平坦化の名前の検査に含めるためである。
   `--type-check` が印字する束縛の行は起点のものだけで、警告はどの単位のものも出す。
   起点でない単位の警告には、ファイル名を前置する。
   プレリュードを利用者の単位と分けたまま渡すのは、
   型検査器がプレリュードだけを `in_prelude` の下で処理し、
   プレリュード所有の印を付けるためである(第15章(prelude.kel)の §15.2)。
   この印があるので、利用者が `Unit` や `Console` を宣言したときに、
   二重宣言ではなく標準環境の名前の再宣言として報告できる。

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
  let flatten ?unit ds =
    try Elab.flatten_modules ?unit ds with
    | Aux.Type_error_at (loc, msg) -> report { Elab.e_loc = Some loc; e_word = "型エラー"; e_exit = 1; e_msg = msg }
    | Aux.Type_error msg -> report { Elab.e_loc = None; e_word = "型エラー"; e_exit = 1; e_msg = msg }
    | Aux.NotImplemented_at (loc, feat) -> report { Elab.e_loc = Some loc; e_word = "未実装"; e_exit = 4; e_msg = feat }
    | NotImplemented feat -> report { Elab.e_loc = None; e_word = "未実装"; e_exit = 4; e_msg = feat }
  in
  let prelude = flatten ~unit:Decls.std_unit (load_prelude options) in
  let deps, roots =
    try load_units options
    with Aux.Import_error (loc, msg) -> report { Elab.e_loc = Some loc; e_word = "import エラー"; e_exit = 1; e_msg = msg }
  in
  (* 依存する単位に、帰りがけ順に 1 から番号を振る。起点は 0 である *)
  let ids = Hashtbl.create 8 in
  List.iteri
    (fun i u ->
      Hashtbl.replace ids u.u_id (i + 1);
      Hashtbl.replace Decls.unit_paths (i + 1) u.u_display)
    deps;
  Hashtbl.replace Decls.unit_paths Decls.root_unit (String.concat "、" (List.map (fun u -> u.u_display) roots));
  let targets u = List.map (fun (im, id) -> (im, Hashtbl.find ids id)) u.u_targets in
  let units =
    List.map (fun u -> { Elab.su_id = Hashtbl.find ids u.u_id; su_imports = targets u; su_decls = u.u_decls }) deps
    @ [ { Elab.su_id = Decls.root_unit; su_imports = List.concat_map targets roots; su_decls = List.concat_map (fun u -> u.u_decls) roots } ]
  in
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
  match Elab.type_check_units ~prelude units with
  | lines, None, flat ->
      List.iter put lines;
      (* --strict-exhaustive が数えるのは、利用者に見せた警告(返ってきた行)だけである。
         大域の Elab.warnings を数えると、表示しないプレリュードの警告のせいで、
         警告を 1 行も出さずに終了コード 1 で終わる、という理由の分からない失敗になる *)
      if options.o_strict_exhaustive && List.exists (function Elab.Warning _ -> true | _ -> false) lines then (
        flush_stdout_or_die ();
        safe_exit 1);
      prelude :: flat
  | lines, Some err, _ ->
      List.iter put lines;
      (* 出力先はモード単位で決める。--type-check はレポートなので全部を stdout へ出す。
         Run は stdout をプログラムの出力専用にし、診断を stderr へ出す *)
      (if quiet then (
         flush_stdout_or_die ();
         try prerr_endline (render_error err) with Sys_error _ -> ())
       else print_endline (render_error err));
      flush_stdout_or_die ();
      safe_exit err.Elab.e_exit

(* ## 16.6b 対話的な実行

   `--repl` は、標準入力から宣言と式文を読み、入力ごとに型検査して実行し、結果を表示する。
   プレリュードは起動時に 1 回だけ処理し、前の入力の束縛を後の入力から使える。

   ### 入力の終わり

   行を読むたびに、まだ確定していない行をつないだ文字列を、ファイルと同じ開始記号でパースする。
   通れば、その入力を確定する。
   構文エラーの位置のトークンが `EOF` なら、続きの行を待つ。
   字句解析器は最後に渡したトークンを `prev` に持つので、`Parser'.Error` を受けた時点の
   `prev = Some EOF` で判定できる。
   閉じていない文字列リテラルとブロックコメントの字句エラーも、続きの行を待つ。
   それ以外の構文エラーは、その入力を捨てて報告する。
   この規則では、次の行で始まる継続(`let rec … and`、行頭の二項演算子、行頭の `.` や `match`)は、
   前の行で入力が確定するので続きにならない。

   ### 失敗した入力の取り消し

   型エラー(平坦化の型エラーを含む)の入力は、宣言表(第6章 §6.14 の写し)、
   単一化のセルの書き換え(第1章 §1.5 の記録)、型の環境を、入力の前に戻す。
   実行時エラーの入力は、さらに評価器の書き込みを入力の単位で戻す(第14章 §14.16)。
   型の側も入力の前に戻すのは、途中まで実行した環境と型の環境が食い違わないようにするためである。
   出力は戻さない。

   ### 結果の表示

   束縛した名前ごとに `名前 : 型 = 値` を出し、式文は名前の代わりに `_` を書く。
   型が `{}` の式文は何も出さない(`echoln(...)` のたびに `_ : {} = ()` が出るのを避ける)。
   値は、型の頭が newtype で、その型が `Show` を満たすときだけ `Show.show` で表示する。
   満たすかどうかは、型検査器に `Show` の制約を足して確かめ、足した書き換えはすぐ戻す。
   それ以外は `Value.show` で表示する。
   組み込みの `Show[String]` は引用符を付けないので、
   文字列を `Show.show` で出すと識別子と区別できない。

   ### Print とトップレベル

   対話的な実行だけ、トップレベルの行に `Print` を足し、最も外側のハンドラが `Print.print` を
   出力先へ送る(第13章 §13.6)。
   トップレベルの `println` の呼び出しが、ハンドラなしでそのまま印字される。
   `Print` を行に足すのも送るのも、`Print` をプレリュードが所有するときだけである。

   ### コマンドと出力先

   入力の途中でない行が `:` で始まれば、コマンドとして扱う。
   `:quit`(`:q`)は終了し、`:reset` はプレリュードだけを処理した状態に戻し、
   `:type 式` は式を型検査して一般化した型を表示する(評価せず、型検査の書き換えは必ず戻す)。

   結果、診断、プログラムの出力は、すべて標準出力に出す。
   入力と応答の対が単位なので、1 本の流れにする。
   プロンプトは、標準入力が端末のときだけ出す(`In_channel.isatty` は Stdlib にあり、
   `unix` を要さない)。
   入力の終わりか `:quit` で終了コード 0 で終わり、
   型エラーや実行時エラーではセッションを終えない。 *)

type parse_result = Complete of Tree.Tree.decl list | Incomplete | Failed of string

let try_parse ~line ?(col = 0) source =
  let lexbuf = Sedlexing.Utf8.from_string source in
  (* col は、入力の行の中で source が始まる位置(:type の後ろの式なら、:type の長さ) *)
  Sedlexing.set_position lexbuf { Lexing.pos_fname = "<stdin>"; pos_lnum = line; pos_bol = -col; pos_cnum = 0 };
  Sedlexing.set_filename lexbuf "<stdin>";
  let lx = Lexer'.from_sedlex lexbuf in
  match Lexer'.parse Parser'.program lx with
  | [], ds -> Complete ds
  | im :: _, _ ->
      Failed (Printf.sprintf "%s: 構文エラー: import は対話的な実行では書けません" (show_pos im.Syntax.im_loc.Location.start))
  | exception Parser'.Error ->
      if lx.Lexer'.prev = Some Lexer'.Parser.EOF then Incomplete
      else Failed (Printf.sprintf "%s: パースエラー(付近のトークンを確認してください)" (show_pos lx.Lexer'.last_sp))
  | exception Lexer.Lex_error (("unterminated string literal" | "unterminated block comment"), _) -> Incomplete
  | exception Lexer.Lex_error (msg, pos) -> Failed (Printf.sprintf "%s: 字句エラー: %s" (show_pos pos) msg)
  | exception Syntax.Syntax_error msg -> Failed (Printf.sprintf "%s: 構文エラー: %s" (show_pos lx.Lexer'.last_sp) msg)
  | exception Syntax.Syntax_error_at (pos, msg) -> Failed (Printf.sprintf "%s: 構文エラー: %s" (show_pos pos) msg)
  | exception Sedlexing.MalFormed -> Failed "<stdin>: 字句エラー: 不正な UTF-8 バイト列です"

(* 実行時エラーの文言。§16.8 の受け皿と同じ文言にそろえる *)
let runtime_message = function
  | Value.Runtime_error msg -> "実行時エラー: " ^ msg
  | Effect.Unhandled (Value.Op (op, _)) -> "未処理のエフェクト操作: " ^ Syntax.Type.display_of op
  | Stack_overflow -> "実行時エラー: スタックオーバーフロー(再帰が深すぎます)"
  | Out_of_memory -> "実行時エラー: メモリ不足です"
  | Panic msg -> msg
  | ex -> "内部エラー: 予期しない例外です: " ^ Printexc.to_string ex

(* 単一化の記録を有効にして f を呼び、f が積んだ書き換えをすぐ戻す *)
let probe f =
  let open Syntax.Type in
  let saved_on = !trailing and saved = !trail in
  trailing := true;
  trail := [];
  let undo () =
    List.iter (fun g -> g ()) !trail;
    trail := saved;
    trailing := saved_on
  in
  match f () with
  | r ->
      undo ();
      r
  | exception ex ->
      undo ();
      raise ex

let show_value ty v =
  let open Syntax.Type in
  let shows =
    match repr ty with
    | TCon (c, _) when Hashtbl.mem Decls.datas c -> (
        try probe (fun () -> Unify.add_class ty (intern "Show"); true) with Aux.Type_error _ | Aux.Type_error_at _ -> false)
    | _ -> false
  in
  if shows then
    (* 型から Show の証拠を組み、辞書にしてメソッドを選ぶ。型の決まらない部分の辞書は DPending になる *)
    let env = { Value.globals = Hashtbl.create 1; locals = Value.SMap.empty; resume = None } in
    let d = Interp.eval_ev env (Unify.display_evidence (intern "Show") ty) in
    match Interp.apply (Interp.select_method ~cls:(intern "Show") d "show" []) (Value.VRecord [ (l_item, v) ]) with
    | Value.VText s -> s
    | v -> Value.show v
  else Value.show v

let repl options =
  let print_owned () = Decls.prelude_owned "effect" (Syntax.Type.intern "Print") in
  let toplevel_extra = [ "Print" ] in
  let start () =
    let prelude = Elab.flatten_modules ~unit:Decls.std_unit (load_prelude options) in
    let tenv = Elab.start_session ~prelude () in
    let sess = Interp.start_session ~print:(print_owned ()) ~sink:print_string prelude in
    (tenv, sess)
  in
  let tenv0, sess0 = start () in
  let tenv = ref tenv0 and sess = ref sess0 in
  let session_vals : (string, unit) Hashtbl.t = Hashtbl.create 64 in
  let line_no = ref 0 in
  let buf = Buffer.create 256 in
  let start_line = ref 1 in
  (* 宣言表の写しと単一化の記録を取って f を呼び、f が `Undo を返したら戻す *)
  let with_undo f =
    let restore = Decls.snapshot () and restore_elab = Elab.snapshot () in
    Syntax.Type.trailing := true;
    Syntax.Type.trail := [];
    let undo () =
      List.iter (fun g -> g ()) !Syntax.Type.trail;
      restore ();
      restore_elab ()
    in
    let finish () =
      Syntax.Type.trailing := false;
      Syntax.Type.trail := []
    in
    match f () with
    | `Undo ->
        undo ();
        finish ()
    | `Keep -> finish ()
    | exception ex ->
        undo ();
        finish ();
        raise ex
  in
  let print_lines lines = List.iter (fun l -> match l with Elab.Warning _ -> print_endline (render_line l) | _ -> ()) lines in
  let print_type_error = function
    | Aux.Type_error_at (loc, msg) -> print_endline (render_error { Elab.e_loc = Some loc; e_word = "型エラー"; e_exit = 1; e_msg = msg })
    | Aux.Type_error msg -> print_endline (render_error { Elab.e_loc = None; e_word = "型エラー"; e_exit = 1; e_msg = msg })
    | Aux.NotImplemented_at (loc, feat) -> print_endline (render_error { Elab.e_loc = Some loc; e_word = "未実装"; e_exit = 4; e_msg = feat })
    | Aux.NotImplemented feat -> print_endline (render_error { Elab.e_loc = None; e_word = "未実装"; e_exit = 4; e_msg = feat })
    | ex -> raise ex
  in
  let process ds =
    with_undo @@ fun () ->
    match Elab.flatten_modules ~session_vals ds with
    | exception ((Aux.Type_error_at _ | Aux.Type_error _ | Aux.NotImplemented_at _ | Aux.NotImplemented _) as ex) ->
        print_type_error ex;
        `Undo
    | decls -> (
        match Elab.check_input ~toplevel_extra !tenv decls with
        | Error (lines, e) ->
            print_lines lines;
            print_endline (render_error e);
            `Undo
        | Ok (lines, env') -> (
            print_lines lines;
            (* 束縛の型は実体で引く。名前で引くと、1 入力の中で同じ名前を 2 回束縛したとき、
               前の束縛に後の束縛の型が付く *)
            let show shown =
              List.iter
                (fun (x, src, v) ->
                  let ty =
                    match src with
                    | `Exp e -> Tree.get_ty e
                    | `Ref g -> (
                        match Elab.lookup_top_type g with Some t -> t | None -> bug ("REPL の束縛の型が見つかりません: " ^ x))
                  in
                  let unit_ty = match Syntax.Type.repr ty with Syntax.Type.TRecord r -> Syntax.Type.repr r = Syntax.Type.TRowEmpty | _ -> false in
                  if not (x = "_" && unit_ty) then
                    Printf.printf "%s : %s = %s\n" (Syntax.Type.display x) (Show.show ty) (show_value ty v))
                shown
            in
            match Interp.exec_input ~print:(print_owned ()) ~show !sess ~sink:print_string decls with
            | () ->
                tenv := env';
                List.iter (fun x -> Hashtbl.replace session_vals x ()) (Elab.toplevel_value_names decls);
                `Keep
            | exception ex ->
                flush_stdout_or_die ();
                print_endline (runtime_message ex);
                `Undo))
  in
  let type_of_expr col src =
    match try_parse ~line:!line_no ~col src with
    | Complete [ (_, Tree.Tree.DExp e) ] ->
        with_undo (fun () ->
            (match Elab.type_of_expr ~toplevel_extra !tenv e with
            | Ok t -> print_endline (Show.show t)
            | Error err -> print_endline (render_error err));
            `Undo)
    | Complete _ -> print_endline ":type には式を 1 つ書いてください"
    | Incomplete -> print_endline ":type の式が途中で終わっています"
    | Failed msg -> print_endline msg
  in
  let command line =
    (* 行末の空白と CR は読み飛ばす *)
    let n = ref (String.length line) in
    while !n > 0 && match line.[!n - 1] with ' ' | '\t' | '\r' -> true | _ -> false do
      decr n
    done;
    let line = String.sub line 0 !n and n = !n in
    if line = ":quit" || line = ":q" then `Quit
    else if line = ":reset" then (
      Decls.reset ();
      Hashtbl.reset session_vals;
      let t, s = start () in
      tenv := t;
      sess := s;
      `Go)
    else if n > 6 && String.sub line 0 6 = ":type " then (
      type_of_expr 6 (String.sub line 6 (n - 6));
      `Go)
    else (
      print_endline ("未知のコマンド: " ^ line);
      `Go)
  in
  let interactive = In_channel.isatty stdin in
  let rec loop () =
    if interactive then (
      print_string (if Buffer.length buf = 0 then "> " else ". ");
      flush_stdout_or_die ());
    match In_channel.input_line stdin with
    | None ->
        if Buffer.length buf > 0 then (
          if interactive then print_newline ();
          match try_parse ~line:!start_line (Buffer.contents buf) with
          | Failed msg -> print_endline msg
          | _ -> print_endline "<stdin>: 入力が途中で終わっています")
        else if interactive then print_newline ()
    | Some line ->
        incr line_no;
        if Buffer.length buf = 0 && String.length line > 0 && line.[0] = ':' then (
          match command line with
          | `Quit -> ()
          | `Go ->
              flush_stdout_or_die ();
              loop ())
        else (
          if Buffer.length buf = 0 then start_line := !line_no;
          Buffer.add_string buf line;
          Buffer.add_char buf '\n';
          (match try_parse ~line:!start_line (Buffer.contents buf) with
          | Incomplete -> ()
          | Failed msg ->
              Buffer.clear buf;
              print_endline msg
          | Complete ds ->
              Buffer.clear buf;
              process ds);
          flush_stdout_or_die ();
          loop ())
  in
  loop ()

(* ## 16.7 結線

   どの段まで通すかは、モードごとに異なる。

   | モード | 字句 | 構文 | 読み込み | 平坦化 | 型検査 | 評価 |
   |---|---|---|---|---|---|---|
   | `DumpTokens` | ○ | × | × | × | × | × |
   | `DumpAst` | ○ | ○ | × | × | × | × |
   | `TypeCheck` | ○ | ○ | ○ | ○ | ○ | × |
   | `Run` | ○ | ○ | ○ | ○ | ○ | ○ |

   読み込みは、import をたどって依存する単位を集める段である(§16.3b)。
   ダンプ系のモードは import をたどらず、渡したファイルだけを読む。

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
  | DumpAst ->
      List.iter
        (fun file ->
          let imports, decls = parse_file file in
          Dump.dump_imports stdout imports;
          Dump.dump_decls stdout decls)
        options.o_files
  | TypeCheck -> ignore (type_check_files options)
  | Repl ->
      Interp.cancel_log :=
        (fun msg -> try Printf.printf "cancel 節で例外が抑制されました: %s\n" msg with Sys_error _ -> ());
      repl options
  | Run ->
      let units = type_check_files ~quiet:true options in
      Interp.cancel_log :=
        (fun msg ->
          (* stderr へ書く直前に stdout を flush する(§16.8 の出力先の規約) *)
          flush_stdout_or_die ();
          try Printf.eprintf "cancel 節で例外が抑制されました: %s\n" msg; flush stderr with Sys_error _ -> ());
      Interp.run_units ~sink:print_string units);
  (* モードの最後に stdout を flush し切る。受け皿の中で flush して、
     失敗を終了コード 74 にするためである(§16.8 の不変条件) *)
  flush_stdout_or_die ()

(* ## 16.8 終了コード規約

   diktor の終了コードは、次の規約に従う。

   | コード | 意味 | 出所 |
   |---|---|---|
   | 0 | 正常終了 | `run_with` が最後まで走った |
   | 1 | 型エラー、import エラー | 第11章の診断、`Aux.Type_error`、`--strict-exhaustive`、§16.3b の `Import_error` |
   | 2 | 構文エラー、字句エラー | `Parse_error`、`Lex_error`、不正な UTF-8 |
   | 3 | 実行時エラー | `Runtime_error`、未処理のエフェクト、再帰過多、メモリ不足、内部異常 |
   | 4 | 未実装(Diktor が実装していない機能) | `Aux.NotImplemented`(1u8、Int8、module の入れ子など) |
   | 64 | 使い方の誤り | 引数解析の失敗、入力ファイルや import 先を開けない |
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
          Printf.eprintf "未処理のエフェクト操作: %s\n" (Syntax.Type.display_of op);
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
      プレリュードも利用者のファイルも同じ `parse_with` に合流し、
      CLI も API も同じ `Elab.type_check` を通る。
      ただし、合流点の手前の前処理(平坦化など)がそろっていなければ、経路は合流点より前で分かれる。
      そのため、§16.5 の API も CLI と同じく、プレリュードと利用者の宣言の両方を平坦化する。
   3. 受け皿から例外を漏らさない。
      漏れた例外は OCaml の既定で終了コード 2 になり、終了コードの表と食い違う。
      規約の外の例外は最後の catch-all が受け、出力の flush も受け皿の中で済ませる(§16.8)。 *)
