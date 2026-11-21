(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第16章 ドライバと終了コード規約

   本章は、ほかの章が作った部品を 1 本の流れにつなぎ、
   コマンド行、標準出力、シェルが見る終了コードという外部との接点に結びつける。
   つなぐ部品は、第15章までの字句解析、構文解析、型検査、評価器、プレリュードと、
   第17章から第22章までの KIR の書き出し、読み込み、検証、評価器である。
   本章に新しいアルゴリズムはない。
   本章が定めるのは入出力の規約と、その規約を破らないための処理である。

   ## 処理の流れ

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

   図は、KIR を使わない実行の流れを簡略に示している。
   CLI は、単位の並びを扱う `Elab.type_check_units` と `Interp.run_units` を呼ぶ(§16.6、§16.7)。
   図の `Elab.type_check` と `Interp.run` を呼ぶのは、§16.5 の API である。
   KIR の経路は §16.6c で扱う。

   本章が前章(第15章、prelude.kel)から受け取るのは、
   文字列定数に埋め込まれたプレリュードのソースである。
   本章が外へ渡すのは、標準出力と標準エラーに書き出す行と、1 つの終了コードである。

   本章の設計は次の 3 点にまとめられる。

   - オプションはモードを選ぶだけにし、処理そのものは各章の関数に任せる。
   - CLI と API は同じ関数を通す。
     API は終了コードの層を外して公開する。
     CLI との違いは §16.5 にまとめる。
   - CLI の経路では、どの例外も `main` の外へ出さない。
     例外が 1 つでも外へ出ると、終了コードの規約が守られなくなる。

   3 点目は §16.8 で扱う。 *)
open Aux

(* ## 16.1 オプションとモード

   オプションは 14 個、モードは 6 つある。
   `usage` の文字列は、オプションを「旗」と書いている。

   | オプション | 設定先 | 動作 |
   |---|---|---|
   | (なし) | `Run` | 型検査してから評価する |
   | `--type-check` | `TypeCheck` | 型検査だけを行い、束縛の型を宣言順に出力する |
   | `--dump-tokens` | `DumpTokens` | ASI 適用後のトークン列を出力する |
   | `--dump-ast` | `DumpAst` | 脱糖後の AST を S 式で出力する |
   | `--repl` | `Repl` | 標準入力から入力を読み、入力ごとに型検査して実行する(§16.6b) |
   | `--no-prelude` | `o_no_prelude` | プレリュードを空にする |
   | `--prelude PATH` | `o_prelude` | 埋め込みのプレリュードの代わりに PATH を読む |
   | `--strict-exhaustive` | `o_strict_exhaustive` | 網羅性と到達不能の警告をエラーにする(`--repl` では効果がない) |
   | `--import-path DIR` | `o_import_path` | import の検索パスに DIR を追加する。繰り返し指定でき、指定した順に探す(§16.3b) |
   | `--emit-ir-text FILE` | `o_emit_ir_text` | 型検査の後、評価せずに KIR の正準なテキストを FILE に書く(§16.6)。`--type-check`、`--dump-tokens`、`--dump-ast`、`--repl` とは併用できない |
   | `--emit-ir FILE` | `o_emit_ir` | 型検査の後、評価せずに KIR のバイナリを FILE に書く(§16.6c)。併用の制限は `--emit-ir-text` と同じで、両方を指定すれば両方の形式で書く |
   | `--run-ir FILE` | `o_run_ir` | 型検査をせずに KIR のバイナリを読み、検証してから第22章の評価器で評価する(§16.6c)。入力の `.kel` も、`--max-depth` 以外のオプションも指定できない |
   | `--via-ir` | `o_via_ir` | 型検査の後、KIR を書き出し、符号化し、読み戻し、検証してから第22章の評価器で評価する(§16.6c) |
   | `--max-depth N` | `o_max_depth` | 第22章の評価器の論理的な深さの上限を N にする。第14章の評価器には影響しない |
   | `--dump-ir-tables` | `DumpIrTables` | KIR の組み込みの表を出力する(§16.6c)。入力ファイルも、KIR を書き出すオプション、`--run-ir`、`--via-ir` も指定できない |

   環境変数 `DIKTOR_VIA_IR` が `1` のときは、
   モードのオプションも、KIR を書き出すオプションも、`--run-ir` も指定していない実行(`Run`)を、
   `--via-ir` を指定した実行と同じように扱う。
   ほかのモードでは、この環境変数を調べない。
   cram のテスト全体を KIR の経路で実行し直すとき(test/dune の別名 `runtest-via-ir`)に、
   `--type-check` や `--repl` のブロックまで KIR の経路に変えないためである。

   `usage` の文字列は、使い方の唯一の説明である。
   テスト test/smoke.t は、この文字列をそのまま期待出力に持つ。
   文字列を変えるとこのゴールデンテストが失敗するので、
   オプションを追加して説明を書き忘れることを防げる。

   `--dump-tokens` は、ASI とブレース再分類(第2章)の結果をテストで固定するためのオプションである。
   ASI の判断を目に見える形で固定できるのは、トークン列のゴールデンテストだけである。

   `--no-prelude` は、プレリュードの不具合を切り分けるためのオプションである。
   第15章 §15.1 で述べたとおり、`TypeCheck` と `Run` のモードでは、
   起動のたびにプレリュードの全文を構文解析し、型検査する。
   そのためプレリュードは、処理系の主な機構が動くことを毎回確かめる役目を持つ。
   その反面、埋め込みのプレリュード自身の不具合は、
   この 2 つのモードで `--no-prelude` も `--prelude PATH` も渡さないすべてのテストに影響する。

   `mode` は排他で、モードのオプションを複数指定すると、最後のものが優先される。
   `o_prelude` と `o_no_prelude` は独立ではなく、
   両方を指定すると `--no-prelude` が優先される(§16.4 の `load_prelude` の分岐)。 *)
let usage =
  "usage: diktor [OPTIONS] FILE.kel...\n\
   \  --type-check         型検査のみ。トップレベル束縛の型を \"name : type\" で出力\n\
   \  --dump-tokens        ASI 適用後のトークン列を出力\n\
   \  --dump-ast           脱糖後の AST を S 式で出力\n\
   \  --repl               対話的に実行する(FILE は不要)\n\
   \  --no-prelude / --prelude PATH\n\
   \  --strict-exhaustive  網羅性・到達不能警告をエラー化\n\
   \  --import-path DIR    import の検索パスに DIR を足す(繰り返せる)\n\
   \  --emit-ir-text FILE  型検査の後、実行せずに KIR の正準のテキストを FILE に書く\n\
   \  --emit-ir FILE       型検査の後、実行せずに KIR のバイナリを FILE に書く\n\
   \  --run-ir FILE        KIR のバイナリを読み、検証してから実行する(入力の .kel とは併用できない)\n\
   \  --via-ir             KIR を書き出して読み戻し、検証してから KIR の評価器で実行する\n\
   \  --max-depth N        KIR の評価器の論理的な深さの限度(既定は 1048576)\n\
   \  --dump-ir-tables     KIR の組み込みの表を出力\n\
   \  環境変数 DIKTOR_VIA_IR=1 は、旗の無い実行を --via-ir にする\n"

type mode = Run | TypeCheck | DumpTokens | DumpAst | Repl | DumpIrTables

type options = {
  o_mode : mode;
  o_prelude : string option; (* Some PATH で差し替え *)
  o_no_prelude : bool;
  o_strict_exhaustive : bool;
  o_files : string list;
  o_import_path : string list; (* --import-path DIR。指定した順 *)
  o_emit_ir_text : string option; (* --emit-ir-text FILE *)
  o_emit_ir : string option; (* --emit-ir FILE *)
  o_run_ir : string option; (* --run-ir FILE *)
  o_via_ir : bool; (* --via-ir *)
  o_max_depth : int option; (* --max-depth N *)
}

let default_options =
  { o_mode = Run; o_prelude = None; o_no_prelude = false; o_strict_exhaustive = false; o_files = []; o_import_path = [];
    o_emit_ir_text = None; o_emit_ir = None; o_run_ir = None; o_via_ir = false; o_max_depth = None;
  }

(* ## 16.2 引数解析

   引数解析に cmdliner は使わない。
   Diktor が依存するライブラリは menhir と sedlex の 2 つに限っている
   (OCaml の配布物に含まれる `unix` は数えない。§16.3b)。
   少数のオプションのために依存を増やす価値はない。
   代わりに、引数のリストを先頭から読んでいく末尾再帰の関数 `go` を書く。

   `go` の実装には要点が 2 つある。

   1 つ目に、`go` は例外を投げず、`Result` を返す。
   使い方のエラーは異常事態ではなく、通常の分岐である。
   呼び出し元(§16.8 の `main`)が `Error` を受け取り、使い方の説明を出力して終了コード 64 を返す。
   そのため、引数解析だけを単体で呼んでも副作用がない。

   2 つ目に、節の順序が意味を持つ箇所が 1 つだけある。
   ハイフンで始まる未知の引数を拒否する節は、既知のオプションすべての後ろ、
   ファイル名の節の前に置く。
   既知のオプションの前に置くと `--type-check` まで未知のオプションとして拒否され、
   ファイル名の節の後ろに置くと `--typo-check` が入力ファイル名として受理される。
   この節のガードは、添字 0 の文字を読む前に長さを調べる。
   空文字列の添字 0 を読むと例外になるからである。
   空文字列の引数はファイル名として扱う。
   そのファイルを開く段階で `Input_error`(§16.3)が起き、
   §16.8 の最上位の例外ハンドラが終了コード 64 を返す。

   最後に `List.rev` でファイルの順序を戻す。
   `go` はファイル名をリストの先頭に追加していくので、リストが逆順になっているからである。
   ファイルの順序には意味がある。
   複数のファイルは、指定した順に連結して処理する。
   連結したファイル群は 1 個の単位(起点。§16.3b)になり、各ファイルの先頭の import は、
   起点の先頭に集めたものとして扱う。
   連結したファイルのどれかを import すると、エラーになる。
   同じ宣言が起点と依存先の両方に現れるからである。
   仕様 sample.kel の回帰テストは、この順序を使ってスタブを sample.kel の前に置く。
   言語仕様は複数のファイルの扱いを定めていない。
   この連結は diktor 独自の規則である。 *)
(* `--max-depth` の値は、10 進の数字だけで書いた 1 以上の整数である。
   符号、`0x`、`_` を含む表記は受理しない(`int_of_string` はこれらを受理する)。
   上限は `max_int / 2` である。
   予備の深さを足した上限(第22章 §22.6)がオーバーフローしない大きさにしてある。 *)
let max_depth_of_string s =
  if s = "" || not (String.for_all (fun c -> c >= '0' && c <= '9') s) then None
  else match int_of_string_opt s with Some n when n >= 1 && n <= max_int / 2 -> Some n | _ -> None

let parse_args args =
  let rec go opts = function
    | [] ->
        let emits = opts.o_emit_ir_text <> None || opts.o_emit_ir <> None in
        if opts.o_files <> [] && opts.o_mode = Repl then Error "--repl takes no input files"
        else if opts.o_files <> [] && opts.o_mode = DumpIrTables then Error "--dump-ir-tables takes no input files"
        else if opts.o_files <> [] && opts.o_run_ir <> None then Error "--run-ir takes no input files"
        else if opts.o_files = [] && opts.o_mode <> Repl && opts.o_mode <> DumpIrTables && opts.o_run_ir = None then Error "no input files"
        else if opts.o_mode = DumpIrTables && (emits || opts.o_run_ir <> None || opts.o_via_ir) then
          Error "--dump-ir-tables cannot be combined with --emit-ir, --emit-ir-text, --run-ir or --via-ir"
        else if opts.o_emit_ir_text <> None && opts.o_mode <> Run then
          Error "--emit-ir-text cannot be combined with --type-check, --dump-tokens, --dump-ast or --repl"
        else if opts.o_emit_ir <> None && opts.o_mode <> Run then
          Error "--emit-ir cannot be combined with --type-check, --dump-tokens, --dump-ast or --repl"
        else if
          opts.o_run_ir <> None
          && (opts.o_mode <> Run || emits || opts.o_via_ir || opts.o_no_prelude || opts.o_prelude <> None || opts.o_strict_exhaustive || opts.o_import_path <> [])
        then Error "--run-ir cannot be combined with other modes, --emit-ir, --emit-ir-text, --via-ir or the prelude, import and exhaustiveness options"
        else if opts.o_via_ir && (opts.o_mode <> Run || emits) then
          Error "--via-ir cannot be combined with --type-check, --dump-tokens, --dump-ast, --repl, --dump-ir-tables, --emit-ir or --emit-ir-text"
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
    | "--emit-ir-text" :: file :: rest -> go { opts with o_emit_ir_text = Some file } rest
    | "--emit-ir-text" :: [] -> Error "--emit-ir-text requires a path"
    | "--emit-ir" :: file :: rest -> go { opts with o_emit_ir = Some file } rest
    | "--emit-ir" :: [] -> Error "--emit-ir requires a path"
    | "--run-ir" :: file :: rest -> go { opts with o_run_ir = Some file } rest
    | "--run-ir" :: [] -> Error "--run-ir requires a path"
    | "--via-ir" :: rest -> go { opts with o_via_ir = true } rest
    | "--max-depth" :: n :: rest -> (
        match max_depth_of_string n with
        | Some d -> go { opts with o_max_depth = Some d } rest
        | None -> Error ("--max-depth requires a positive integer: " ^ n))
    | "--max-depth" :: [] -> Error "--max-depth requires a positive integer"
    | "--dump-ir-tables" :: rest -> go { opts with o_mode = DumpIrTables } rest
    | arg :: _ when String.length arg > 0 && arg.[0] = '-' -> Error ("unknown option: " ^ arg)
    | file :: rest -> go { opts with o_files = file :: opts.o_files } rest
  in
  go default_options args

(* ## 16.3 フロントエンドのファンクタの適用と、字句エラーと構文エラーの整形

   字句解析器(第2章)とパーサ(第3章)は、
   AST のノードに付けるデータをパラメータに取るファンクタである。
   本章は、両方のファンクタに第5章の `Tree.ElabData` を適用する。
   この処理系が木に精緻化(elaboration)用のデータを書き込むことは、次の 2 行で決まる。
   別の用途で別のデータを付けるときは、そのデータを適用したモジュールを別に作ればよい。 *)
module Lexer' = Lexer.Make (Tree.ElabData)
module Parser' = Parser.Make (Tree.ElabData)

(* `Parse_error` は、位置まで整形し終えた 1 行のメッセージを持つ、本章専用の例外である。
   §16.3a の `parse_program` が投げる `Parser'.Error` は情報を持たない。
   構文解析がどこで止まったかは、字句解析器が記録しているトークンの位置からしか分からない。
   §16.3 の `parse_error_message` が、字句解析器が記録している直近のトークンから、
   報告する位置を決める。
   直前で数値リテラルの直後に隙間なく別のトークンが続いていれば、数値の開始位置を使い(第2章 §2.14)、
   そうでなければ第2章 §2.11 の `error_positions` の位置を使う。
   止まる直前のパーサの状態を調べるのは、§16.3a の `parse_program` だけである。
   パーサと字句解析器の両方を扱うのは本章だけなので、
   両者の情報を合わせてメッセージを整形できるのも本章だけである。

   `main` は `Parse_error` を受け取ってメッセージを出力し、終了コード 2 を返す(§16.8)。 *)
exception Parse_error of string

(* 入力を開けないエラーだけを、この例外にする。
   最上位の例外ハンドラ(§16.8)が Sys_error のまま受け取るのは、
   出力の書き出しに失敗したときのエラーである。
   こう分けておけば、例外の文字列を調べてエラーの種類を推測しなくて済む。
   入力を開く箇所を追加するときは、with_input で囲む。
   囲み忘れると、その Sys_error は出力エラーとして終了コード 74 になる *)
exception Input_error of string

let with_input f = try f () with Sys_error msg -> raise (Input_error msg)

(* 出力の書き出しも終了コードの規約に含まれる。
   exit が実行する do_at_exit は、Format の標準フォーマッタを flush する。
   stdout や stderr に書けないときは、この flush で Sys_error が起きる。
   この例外は最上位の例外ハンドラの外で起きるので、Fatal error と終了コード 2 になる。
   つまり exit 自身が例外を投げることがある。
   そこで、終了はすべて safe_exit を通す。
   safe_exit は、呼び出し元が決めた終了コードを受け取り、
   フォーマッタの出力関数を何もしない関数に替え、
   チャネルをできる範囲で flush してから、その終了コードで exit する。
   フォーマッタを無効にするのは、望ましい方法ではない。
   Unix._exit を使えば do_at_exit を通らずに終了できるが(unix は §16.3b のとおり依存の方針の対象外である)、
   ここでは終了の経路を exit にそろえることを優先し、
   失敗することがあるフォーマッタの flush だけを止める *)
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
  (* stdout、stderr の順に flush して、プログラムの出力が診断より先に出る順序を保つ。
     cram は両者を 1 本にまとめて比較するからである。
     flush の失敗は無視する。
     終了コードはすでに決まっており、Fatal error と終了コード 2 で上書きさせない *)
  (try flush stdout with Sys_error _ -> ());
  (try flush stderr with Sys_error _ -> ());
  exit n

let die_output msg =
  Printf.eprintf "diktor: 標準出力に書き出せません: %s\n" msg;
  safe_exit 74

let flush_stdout_or_die () = match flush stdout with () -> () | exception Sys_error msg -> die_output msg

(* 位置は `ファイル:行:桁` の形式で示す。
   桁は、行頭からのコードポイント数に 1 を足したもので、バイト数から求めたものではない。
   第2章がそのまま渡す `Sedlexing.lexing_positions` はコードポイント単位で数えるので、
   マルチバイト文字を含む行でも桁はずれない。
   たとえば `あいう` を含む行と `abc` を含む行では、同じ位置のエラーが同じ桁になる。

   ただし、合うのはコードポイント数までである。
   結合文字も、全角文字も、異体字セレクタも 1 と数えるので、
   エディタが表示する桁とは食い違うことがある。
   表示上の桁まで合わせるには文字ごとの表示幅の表が必要で、
   エラーの位置を示すという目的には見合わない。 *)
let show_pos = Location.show_pos

(* `dump_tokens_file` は `--dump-tokens` の本体である。
   第2章の 3 つの層のうち、ASI を適用した最も外側の層のトークン列を出力する。
   ASI を適用する前のトークン列を出力しても、ASI の判断を固定するという目的を果たせない。 *)
let dump_tokens_file file =
  (* from_filename はファイルを一括で読む。
     開くときと読むときの両方で起きる Sys_error を入力エラーにするため、
     この呼び出しを with_input で囲む。
     出力は囲まない。
     出力の失敗を入力エラーと取り違えないためである *)
  let tokens = with_input (fun () -> Lexer'.all_tokens (Lexer'.from_filename file)) in
  List.iter (fun e -> Printf.printf "%4d  %s\n" e.Lexer'.sp.Lexing.pos_lnum (Lexer'.show_token e.Lexer'.tok)) tokens

(* ## 16.3a 増分 API で進めるパーサと、予約語の誤用

   パーサは menhir の表形式(`--table`)で生成し、増分 API で 1 トークンずつ進める。
   こうすると、文法に合わないトークンを読んだとき、その直前のパーサの状態が残っている。
   `parse_program` はその状態を使い、エラーの種類を 1 つだけ判別する。
   予約語を識別子の位置に書いたエラーである。
   判別したときは、予約語の名前と位置を付けた `Syntax_error_at` を投げる。
   それ以外のエラーでは `Parser'.Error` を投げる。

   判別の条件は、文法に合わなかったトークンが予約語(第2章 §2.13)で、
   それを同じ名前の識別子に置き換えると、次のトークンまで読み進められることである。
   `let then = 1` は、`then` を識別子にすると `=` まで進めるので、このエラーとして報告する。
   メッセージは、予約語をその位置に書けないことを先に述べ、識別子に使えないことを括弧の中に添える。
   前置の形で書いた `handle { ... } with { ... }` や `match(x) { ... }`、
   順序を逆にした `import { b } from ...` も、
   識別子に置き換えると呼び出しや末尾ブロックとして読み進められるので、
   この条件を満たす。
   これらは識別子のつもりで書いたものではないので、識別子に使えないとだけ述べると原因から外れる。
   次のトークンまで調べるのは、予約語を予約語として書いたが位置が違う入力を除くためである。
   `1 + if c then 1 else 2` の `if` や、宣言の後ろに書いた `from` がその例である。
   これらは識別子に置き換えても次のトークン(`c` や文字列)で先へ進めなくなるので、
   汎用のメッセージになる。

   次のトークンまで調べても除けない形がある。
   `1 + if (c) then 1 else 2` の `if` は、識別子に置き換えると `(` まで進める。
   そこで、文法に合わなかった位置に `(` を置けば、その直後に同じ予約語を置けるときも、
   汎用のメッセージにする。
   これは、`if` や `fn` のように式を始める予約語を、
   括弧で囲まずに演算子のオペランドに書いた形である。
   `true` と `false` はこの判定の対象にしない。
   `let true = 1` の `true` は、`(` の後ろならパターンとして置けるが、
   識別子の位置に書いたエラーだからである。

   条件はもう 1 つある。
   `{then = 1}` の `{` は、第2章 §2.9 の表が `then` を識別子として扱わないので、
   ブロックに分類される。
   ブロックの中では識別子の次に `=` を置けないので、上の条件を満たさない。
   そこで、文法に合わなかった予約語の直前が `{blk` で、次のトークンが `=` か `,` のときも、
   このエラーとして報告する。
   §2.9 の表がレコードに分類する形を、予約語についても同じように扱うためである。

   次のトークンを読むと、字句解析器が記録している直前のトークンとその位置が進む。
   汎用のメッセージはその位置を使う。
   対話的な実行(REPL)は、直前のトークンが `EOF` かどうかで、続きの行を待つかどうかを決める(§16.6b)。
   そこで、`read` が更新する状態(第2章 §2.8)のうち、直前のトークンと位置に関わる 6 つ
   (`prev`、`last_sp`、`last_ep`、`before_ep`、`before_cont`、`recent`)を、
   次のトークンを読む前に保存しておき、
   読んだ直後に戻す。
   残りの `pending` と `regions` は戻さない。
   次のトークンで字句エラーが起きたときと、置き換えた後の意味動作が構文エラーを投げたときは、
   条件を満たさなかったものとして扱う。
   置き換えた後の還元は意味動作を実行して木のノードを作るが、その木は捨てる。 *)
module I = Parser'.MenhirInterpreter

(* 識別子に置き換えた状態から、次の入力を求めるところまで進める *)
let rec advance cp =
  match cp with
  | I.Shifting _ | I.AboutToReduce _ -> advance (I.resume cp)
  | _ -> cp

let misused_reserved_word lexer ~after_brace before (tok, sp, ep) =
  match Lexer'.reserved_word tok with
  | None -> None
  | Some w ->
      let prev = lexer.Lexer'.prev and last_sp = lexer.Lexer'.last_sp and last_ep = lexer.Lexer'.last_ep in
      let before_ep = lexer.Lexer'.before_ep and before_cont = lexer.Lexer'.before_cont in
      let recent = lexer.Lexer'.recent in
      let next = match Lexer'.read lexer with next, nsp, _ -> Some (next, nsp) | exception Lexer.Lex_error _ -> None in
      lexer.Lexer'.prev <- prev;
      lexer.Lexer'.last_sp <- last_sp;
      lexer.Lexer'.last_ep <- last_ep;
      lexer.Lexer'.before_ep <- before_ep;
      lexer.Lexer'.before_cont <- before_cont;
      lexer.Lexer'.recent <- recent;
      let continues (next, nsp) =
        match advance (I.offer before (Lexer'.Parser.LOWER_IDENTIFIER w, sp, ep)) with
        | I.InputNeeded _ as cp -> I.acceptable cp next nsp
        | _ -> false
        | exception Syntax.Syntax_error_at _ -> false
      in
      let record_label = function Lexer'.Parser.EQ, _ | Lexer'.Parser.COMMA, _ -> after_brace | _ -> false in
      let operand () =
        match advance (I.offer before (Lexer'.Parser.LPAREN, sp, sp)) with
        | I.InputNeeded _ as cp -> I.acceptable cp tok sp
        | _ -> false
        | exception Syntax.Syntax_error_at _ -> false
      in
      let literal = match tok with Lexer'.Parser.BOOL _ -> true | _ -> false in
      match next with
      | Some n when (continues n || record_label n) && (literal || not (operand ())) -> Some (w, sp)
      | _ -> None

let parse_program lexer =
  let rec run last prev_tok cp =
    match cp with
    | I.InputNeeded _ ->
        let triple = Lexer'.read lexer in
        run (Some (cp, triple)) (Option.map (fun (_, (t, _, _)) -> t) last) (I.offer cp triple)
    | I.Shifting _ | I.AboutToReduce _ -> run last prev_tok (I.resume cp)
    | I.Accepted v -> v
    | I.HandlingError _ | I.Rejected -> (
        let after_brace = prev_tok = Some Lexer'.Parser.LBRACE_BLOCK in
        match Option.bind last (fun (before, triple) -> misused_reserved_word lexer ~after_brace before triple) with
        | Some (w, sp) ->
            raise (Syntax.Syntax_error_at (sp, Printf.sprintf "予約語 %s はここには書けません(予約語は識別子に使えません)" w))
        | None -> raise Parser'.Error)
  in
  (* 開始位置は空の lexbuf の位置(1 行目の 0 桁)である。
     この位置がノードの位置になるのは、開始直後に空の規則を還元したときだけである *)
  run None None (Parser'.Incremental.program (Lexing.from_string "").Lexing.lex_curr_p)

(* `parse_unit_with` は、構文解析の失敗を 1 か所で受ける関数である。
   ファイルを読む `parse_file` と `read_unit`(§16.3b)も、
   文字列を読む `parse_string` が呼ぶ `parse_with` も、この関数を通る。
   対話的な実行(§16.6b)だけは、`parse_program` を自分で呼ぶ。
   この関数が受ける失敗は、次の 3 種類である。

   - `Parser'.Error`：§16.3a の `parse_program` で、menhir のパーサが次の動作を選べず、
     予約語の誤用でもなかった(入力が文法に合わない)
   - `Syntax.Syntax_error_at`：文法には合ったが、脱糖(第3章)がその形を拒否し、
     エラーの位置を指定した。
     §16.3a の `parse_program` が、予約語を識別子の位置に書いたエラーを報告するときもこれを投げる
   - `Stack_overflow` と `Out_of_memory`：構文解析がスタックかメモリの上限を超えた。
     診断の種別は `処理系の限度` である

   ユーザから見ると、どれも入力を読めなかったというエラーなので、
   1 行のメッセージにそろえて `Parse_error` にする。
   先の 2 つには位置を付ける。
   `Syntax_error_at` には、指定された位置を使う。
   `Parser'.Error` の位置とメッセージは、`parse_error_message` が決める。
   直前で数値リテラルの直後に隙間なく別のトークンが続いていたときは(第2章 §2.14)、
   数値の開始位置を示し、数値とその直後に続く文字列をメッセージに書く。
   そうでなければ、第2章の `error_positions` で位置を決める。
   直前のトークンが後ろに続きを必要とし、文法に合わなかったトークンが次の行以降にあるときは、
   直前のトークンの終わりを主な位置にし、合わなかったトークンの位置を本文に添える。
   それ以外のときは、合わなかったトークンの位置を使う。

   構文解析が上限を超えるのは、意味動作が呼ぶ関数に非末尾の再帰があるからである。
   たとえば、ブロックの文の並びをまとめる `block_of_items` と、
   引数の並びからレコードを組み立てる `record_of_args` は、並びの長さに比例してスタックを使う。
   上限を超えた時点の最後のトークンは、長い並びの終わりの近くにあるだけで、エラーの位置ではない。
   そこで、このメッセージにはファイル名だけを付ける。
   `Stack_overflow` と `Out_of_memory` をここで受けるのは、
   型検査や評価の段階で上限を超えた場合と区別し、
   読み込みの段階の失敗として終了コード 2 で報告するためである。
   字句解析器の `Lexer.Lex_error` はここでは受けず、§16.8 の最上位の例外ハンドラがそのまま受ける。
   不正な UTF-8 バイト列も、第2章が位置付きの `Lex_error` に変えてから投げるので、
   同じハンドラが受ける。
   失敗を種類ごとに区別して報告する必要が出たときは、この関数で分ければよい。
   失敗を受ける箇所を 1 つにまとめてあるのはそのためである。 *)
let read_limit_message file = function
  | Out_of_memory -> file ^ ": 処理系の限度: 構文解析でメモリが不足しました"
  | _ -> file ^ ": 処理系の限度: 構文解析で再帰が深すぎます(スタックオーバーフロー)"

let parse_error_message lx =
  match Lexer'.glued_number lx with
  | Some (n, sp, next) ->
      Printf.sprintf "%s: 構文エラー: 数値リテラル %s の直後に %s が続いています(数値リテラルの綴りを確認してください)"
        (show_pos sp) (Lexer.show_number n) next
  | None -> (
      match Lexer'.error_positions lx with
      | pos, None -> Printf.sprintf "%s: 構文エラー: 付近のトークンを確認してください" (show_pos pos)
      | pos, Some next ->
          Printf.sprintf "%s: 構文エラー: この位置の後ろ、%d:%d のトークンが文法に合いません" (show_pos pos)
            next.Lexing.pos_lnum
            (next.Lexing.pos_cnum - next.Lexing.pos_bol + 1))

let parse_unit_with lexer =
  try parse_program lexer with
  | Parser'.Error -> raise (Parse_error (parse_error_message lexer))
  | Syntax.Syntax_error_at (pos, msg) -> raise (Parse_error (Printf.sprintf "%s: 構文エラー: %s" (show_pos pos) msg))
  | (Stack_overflow | Out_of_memory) as ex -> raise (Parse_error (read_limit_message lexer.Lexer'.last_sp.Lexing.pos_fname ex))

(* import はコマンド行で渡したファイルと、そこから import したファイルにだけ書ける。
   プレリュードと文字列の API は、相対パスの基準になるファイルを持たないので、
   import があれば構文エラーにする *)
let parse_with lexer =
  match parse_unit_with lexer with
  | [], ds -> ds
  | im :: _, _ ->
      raise
        (Parse_error
           (Printf.sprintf "%s: 構文エラー: import はコマンド行で渡したファイルにだけ書けます"
              (show_pos im.Syntax.im_loc.Location.start)))

(* 構文解析の全体を with_input で囲む。
   ディレクトリを渡したときの EISDIR などの読み取りエラーは、
   ファイルを開くときではなく、読むときに起きるからである *)
let parse_file file = with_input (fun () -> parse_unit_with (Lexer'.from_filename file))

(* ## 16.3b import 先の読み込み

   コマンド行で渡したファイル群(起点)から import をたどり、依存する単位を集める。
   起点の各ファイルの import を、書いた順に深さ優先でたどる。
   単位は帰りがけ順(依存される側が先)に並べ、同じファイルは 1 回だけ読む。
   循環は、訪問中のファイルのリストで検出する。

   2 つのパスが同じファイルを指すかどうかは、
   シンボリックリンクを解決した絶対パス(`Unix.realpath`)で判定する。
   同じファイルを別の表記のパスやリンクから 2 回読み込むと、
   型が別物になり、初期化も 2 回行われるからである。
   本節では、この絶対パス(`realpath` で得たパス)を「正規化したパス」(`u_id`)と呼ぶ。
   `unix` は OCaml の配布物に含まれるので、
   §16.2 の依存の方針(menhir と sedlex に限る)の対象外とする。

   ユーザに見せるパスは、絶対パスではなく次のパスにする。
   cram の出力に作業ディレクトリが現れないようにするためである。
   本節では、このパスを「表示用のパス」(`u_display`)と呼ぶ。

   - 起点は、コマンド行に書いた引数のままである。
   - 相対パスの import は、次の手順で作る。
     import を書いたファイルの表示用のパスからディレクトリの部分を取り、
     そこに import のパスと `.kel` を連結する。
     連結したパスから `.` の要素を取り除き、`..` を直前の要素とともに取り除く。
     直前の要素がない `..` は残す。
   - 検索パスの import は、`--import-path` に指定したディレクトリに import のパスと `.kel` を連結し、
     相対パスの場合と同じく `.` と `..` を取り除いたパスである。

   `..` を取り除いたパスが、実際に開くパスと同じファイルを指さないとき(シンボリックリンクの下の `..`)は、
   実際に開くパスから `.` の要素だけを取り除いたパスを使う。

   字句解析器には表示用のパスをファイル名として渡すので、診断の位置も表示用のパスで出る。
   実際に開くパス(`u_path`)は、`..` を取り除かずに連結したパスである。
   シンボリックリンクの下の `..` は、パスの文字列から取り除いた結果と OS が解決した結果とで、
   指すファイルが違うことがあるからである。

   import のパスの書き方の規則は次のとおりである。
   区切りは `/` に固定する。
   コロンと絶対パスは書けない。
   コロンは、`kel:` などの接頭辞のために予約している。
   拡張子 `.kel` は処理系が付けるので、パスに書くとエラーになる。
   相対パスは、先頭の `./` 1 個か `../` の繰り返しで始め、
   その後の要素に空の要素、`.`、`..` は書けない。
   それ以外のパスは検索パスの中を探し、複数のディレクトリで見つかればエラーにする。
   検索パスの順序で結果が変わらないようにするためである。 *)
let import_error loc msg = raise (Aux.Import_error (loc, msg))

type unit_src = {
  u_id : string; (* realpath。同じファイルかどうかの判定だけに使う *)
  u_display : string;
  u_path : string;
  u_imports : Syntax.import_decl list;
  u_decls : Tree.Tree.decl list;
  mutable u_targets : (Syntax.import_decl * string) list; (* import 文と、解決先の正規化したパス *)
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

(* import のパスの書き方を検査し、
   (相対パスなら Some 先頭の ../ の個数、検索パスなら None) と残りの要素を返す *)
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

(* .. を取り除いた表示用のパスが、
   実際に開くパスと同じファイルを指さないとき(シンボリックリンクの下の .. など)は、
   実際に開くパスから . の要素だけを取り除いたものを表示用のパスにする。
   別の実在するファイルの名前で診断を出さないためである *)
let faithful_display ~id ~path display =
  (* . の要素を取り除いても、シンボリックリンクの有無によらず、パスが指すファイルは変わらない *)
  let undotted =
    let comps = List.filter (fun c -> c <> "." && c <> "") (String.split_on_char '/' path) in
    (if String.length path > 0 && path.[0] = '/' then "/" else "") ^ String.concat "/" comps
  in
  match Unix.realpath display with
  | r when r = id -> display
  | _ -> undotted
  | exception Unix.Unix_error _ -> undotted

(* import 文の解決先を (実際に開くパス, 表示用のパス, 正規化したパス) で返す *)
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
      (* 検索パスの複数のディレクトリで同じファイルを見つけたときは、1 つと数える *)
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
          (* ファイルを開くときのエラーメッセージは実際に開くパスで始まるので、表示用のパスに置き換える *)
          raise (Sys_error (display ^ String.sub msg (String.length path) (String.length msg - String.length path))))
  in
  { u_id = id; u_display = display; u_path = path; u_imports = imports; u_decls = decls; u_targets = [] }

(* (依存する単位を帰りがけ順に並べたリスト, 起点のファイルのリスト) を返す *)
let load_units options =
  let roots = List.map (fun f -> read_unit ~path:f ~display:f ~id:(realpath f)) options.o_files in
  let root_ids = List.map (fun u -> u.u_id) roots in
  let finished : (string, unit) Hashtbl.t = Hashtbl.create 8 in
  let order = ref [] in
  (* stack は訪問中の (正規化したパス, 表示用のパス) のリストで、先頭が最も新しい *)
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

(* `parse_string` は、エラーの行に表示するファイル名を引数で受け取る。
   山括弧付きの名前(`<prelude>` や `<string>`)は、実在のファイルではないことを示す。
   ユーザがその名前のファイルを探さないようにするためである。

   山括弧付きの名前は、実在しないもの(埋め込みのプレリュードと文字列の API)だけに使う。
   `--prelude PATH` で差し替えたプレリュードは実在するファイルなので、実在のパスをファイル名にする。
   そのため、差し替えたプレリュードにエラーがあるとき、
   ユーザはエラーの行から自分の渡したパスを読み取れる。 *)
let parse_string ~filename source =
  let lexbuf = Sedlexing.Utf8.from_string source in
  Sedlexing.set_filename lexbuf filename;
  parse_with (Lexer'.from_sedlex lexbuf)

(* ## 16.4 プレリュードの読み込み

   第15章(prelude.kel)は、ビルド時に OCaml の文字列定数へ埋め込まれ、`Prelude_embed.source` になる。
   そのため、インストールした diktor は実行時にプレリュードのファイルを探さず、
   実行ファイル 1 つだけで動く。

   プレリュードの入手元は 3 つあり、優先順位は次のとおりである。

   1. `--no-prelude`：空の宣言列。最も優先する
   2. `--prelude PATH`：PATH の内容を読む。開けなければ §16.8 が終了コード 64 にする
   3. 既定：埋め込みの文字列

   構文解析を呼ぶ関数は、ユーザのファイルとプレリュードとで異なる。
   ユーザのファイルは `read_unit`(§16.3b)か `parse_file` を通り、
   プレリュードは、ファイルから読んだものも埋め込みの文字列も `parse_string` を通る。
   どれも最後は `parse_unit_with`(§16.3)に合流し、
   プレリュードだけが通る特別な字句解析器やパーサはない。
   `--prelude PATH` の場合に `load_prelude` が `In_channel` でファイルを読み、
   内容を文字列として `parse_string` に渡すのはそのためである。

   差し替えたプレリュードは `module` を含むことがあるので、
   通常の入力と同じく平坦化(第11章)を通す必要がある。
   ただし `load_prelude` は構文木のまま返し、平坦化は呼び出し元が行う(CLI の経路では §16.6)。
   読み込みと平坦化を分けているので、
   プレリュードとユーザの宣言の両方に同じ前処理を行う責任は、呼び出し元にある。
   §16.5 の API も、プレリュードとユーザの宣言の両方を平坦化する。 *)
let load_prelude options =
  if options.o_no_prelude then []
  else
    let source =
      match options.o_prelude with
      (* --prelude PATH は実在のファイルなので、実在のパスをファイル名にする。
         山括弧付きの名前は、実在しないもの(埋め込みと文字列の API)だけに使う *)
      | Some path ->
          (path, with_input (fun () -> In_channel.with_open_bin path In_channel.input_all))
      | None -> ("<prelude>", Prelude_embed.source)
    in
    let filename, source = source in
    parse_string ~filename source

(* ## 16.5 サブプロセスなしで呼べる API

   API は CLI と同じ経路を通す。
   経路が分かれると、API を通したテストは通るのに CLI は壊れている、という状態が起きることがある。
   本節は、文字列を受け取って結果を返す関数を 2 つ公開する。

   - `type_check_string`：(出力行の一覧, エラー行 option) を返す
   - `eval_string ~sink`：出力先を引数で受け取り、型エラーなら `Error` を返す

   `~sink` で出力先を渡せるので、標準出力を差し替えなくても出力を検査できる。
   第13章のランタイムハンドラが `sink` につながっており、
   `Console.write` の出力は `sink` に渡した関数へ送られる。

   前処理は CLI と同じである。
   `embedded_prelude` が平坦化まで済ませるので、
   プレリュードとユーザの宣言の両方が `flatten_modules` を通ってから型検査に入る。

   ただし、CLI にあって API にはないものが 3 つある。
   どれも意図して外してある。

   - 終了コードの層。
     型エラーは `exit 1` にならず、値として返る。
     §16.8 の最上位の例外ハンドラもないので、構文解析のエラー(`Parse_error`)、
     平坦化のエラー(`Aux.Type_error` や `NotImplemented`)、実行時エラーは値にならず、
     例外のまま呼び出し元へ出る。
   - `--strict-exhaustive` の判定
   - `Interp.cancel_log` の設定(§16.7)

   逆に、API だけが行う処理が 1 つある。
   API は同じプロセスから何度も呼ばれるので、先頭で `Decls.reset` を呼んで宣言表を初期状態に戻す。

   回帰テストは cram で書いてあり、実行ファイルを起動して検査する。
   リポジトリの中に、この API を呼ぶコードはない。
   この API は、Diktor をライブラリとして組み込むプログラムと、
   サブプロセスを起動せずに検査したいテストのためのものである。 *)
(* CLI の経路(§16.6)と同じ前処理を通す。
   平坦化を省くと、プレリュードに module が入ったときに、
   API の経路だけが型検査の内部エラー(平坦化されていない module)になる *)
let embedded_prelude () =
  Elab.flatten_modules ~unit:Decls.std_unit (parse_string ~filename:"<prelude>" Prelude_embed.source)

(* 出力行と診断を整形する。
   行の種別は第11章が値として渡し、表示の形式は本章が決める。
   束縛の型を表示する行は、第11章が `name : type` の形式で渡すので、そのまま出力する。
   警告には `⚠ ` を、エラーには `! ` を先頭に付け、先頭の 1 文字で種別を判別できる形式を保つ *)
let render_line = function Elab.Binding s -> s | Elab.Warning s -> "⚠ " ^ s

let render_error (e : Elab.error) =
  (* start_of を通す。位置を持たない仮(dummy)の span なら、位置なしの形式になる *)
  match Option.bind e.Elab.e_loc Location.start_of with
  | Some pos -> Printf.sprintf "! %s: %s: %s" pos e.Elab.e_word e.Elab.e_msg
  | None -> Printf.sprintf "! %s: %s" e.Elab.e_word e.Elab.e_msg

(* 型検査だけを行い、(出力行, エラー行 option) を返す *)
let type_check_string ?(prelude = true) source =
  (* 同じプロセスから何度も呼ばれる API なので、宣言表を初期状態に戻してから始める。
     順序は reset、flatten、type_check である。
     reset を flatten の後に置くと、flatten が登録した別名が消える。
     CLI でファイルを処理する経路は、1 プロセスで 1 プログラムしか処理しないので、reset を呼ばない *)
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

(* ## 16.6 型検査の呼び出しと、警告の出力先

   本章は、プレリュードを平坦化し、
   ユーザの単位の並び(§16.3b)とともに第11章の `type_check_units` へ渡す。
   ユーザの単位の平坦化は、第11章が単位ごとに行う。
   import した名前を、平坦化が行う名前の検査の対象に含めるためである。
   `--type-check` が出力する束縛の行は起点のものだけで、警告はどの単位のものも出力する。
   起点でない単位の警告には、先頭にファイル名を付ける。
   プレリュードをユーザの単位と分けたまま渡すのは、
   型検査器がプレリュードだけを `in_prelude` を立てた状態で処理し、
   そこで宣言した名前をプレリュード所有として記録するためである(第15章(prelude.kel)の §15.2)。
   この記録があるので、ユーザが `Unit` や `Console` を宣言したときに、
   二重宣言ではなく標準環境の名前の再宣言として報告できる。

   ### 行の種別は値として渡される

   `--type-check` では、束縛の型を表示する行をそのまま出力する。
   `Run` ではこの行は不要だが、警告は捨てない。
   そこで `Run` のとき(`type_check_files` の `quiet` が真のとき)は、警告だけを標準エラーへ出力する。
   警告かどうかは、第11章が返す `out_line` の値をパターン照合して判定する。
   行は `Binding` か `Warning` の値として渡され、先頭の `⚠ ` は本章の `render_line` が最後に付ける。

   行の種別は値で持ち、表示用の文字列は出力の直前に 1 度だけ作る。
   表示用の文字列から種別を読み取ると、表示の形式を変えたときに判定が壊れる。
   形式を変えなくても、読み取り方によっては誤判定が起きる。
   たとえば、警告の記号 U+26A0 の UTF-8 の先頭バイトは `\xe2` なので、
   行の先頭バイトだけで判定すると、
   U+2000 から U+2FFF までのどの文字で始まる行も警告と見なしてしまう。

   ### 終了コード 1 で終了する 2 つの場合

   `--strict-exhaustive` は、型エラーがなく警告が残った場合に終了コード 1 を返す。
   網羅性検査(第10章)の警告を CI の合否の判定に使うためのオプションである。
   既定で警告のままにしてあるのは、網羅性の指摘が誤りの断定ではなく、
   見落としの可能性の報告だからである。
   警告をエラーとして扱うかどうかは、ユーザが選ぶ。
   なお、仕様 sample.kel の全文は、警告を 1 つも出さずに型検査に通る。

   型エラーのときは、そこまでに出力できた行とエラーの行を出力して、終了コード 1 で終了する。
   このとき `type_check_files` は例外を投げず、`safe_exit` を通して `exit` を呼ぶ。
   `exit` は例外を使わずにプロセスを終了するので、§16.8 の最上位の例外ハンドラを通らない。
   例外で抜けると、型エラーがこのハンドラの `Panic` や `Type_error` の節に入り、
   別の終了コードになることがある。 *)

(* quiet は Run モードを表す。
   束縛の型を表示する行は出さず、警告だけを stderr に出す。
   行の種別は、表示用の文字列ではなく out_line の値で判定する *)
let type_check_files_units ?(quiet = false) options =
  (* プレリュードの平坦化の診断と import エラーも、
     出力先をモード単位で決める規約(§16.8)に従って出力する。
     平坦化の例外を最上位の例外ハンドラに任せると、
     --type-check でも平坦化の「! 未実装:」だけが stderr に出て、出力先の規約が 2 通りになる。
     どちらも型検査より前に行う処理なので、これらの診断より前に型を表示する行は出ない *)
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
  (* 依存する単位に、帰りがけ順に 1 から番号を付ける。
     起点の番号は 0 である *)
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
          (* stderr へ書き出す前に stdout を flush する。
             stdout はバッファ付きで、stderr は行ごとに flush されるので、
             flush を挟まないと、両者を 1 本にまとめて比較する cram で順序が入れ替わる。
             stderr に書けないときは警告を捨て、プログラムの実行を続ける *)
          flush_stdout_or_die ();
          (try prerr_endline (render_line l) with Sys_error _ -> ())
      | Elab.Binding _ -> ())
    else print_endline (render_line l)
  in
  match Elab.type_check_units ~prelude units with
  | lines, None, flat ->
      List.iter put lines;
      (* --strict-exhaustive が数えるのは、ユーザに見せた警告(返ってきた行)だけである。
         グローバルな Elab.warnings を数えると、表示しないプレリュードの警告があるときに、
         警告を 1 行も出さないまま終了コード 1 で終了し、ユーザには失敗の理由が分からない *)
      if options.o_strict_exhaustive && List.exists (function Elab.Warning _ -> true | _ -> false) lines then (
        flush_stdout_or_die ();
        safe_exit 1);
      (prelude :: flat, deps, roots)
  | lines, Some err, _ ->
      List.iter put lines;
      (* 出力先はモード単位で決める。
         --type-check は型検査の結果を表示するモードなので、すべてを stdout へ出す。
         Run は stdout をプログラムの出力専用にし、診断を stderr へ出す *)
      (if quiet then (
         flush_stdout_or_die ();
         try prerr_endline (render_error err) with Sys_error _ -> ())
       else print_endline (render_error err));
      flush_stdout_or_die ();
      safe_exit err.Elab.e_exit

let type_check_files ?quiet options =
  let units, _, _ = type_check_files_units ?quiet options in
  units

(* ### KIR の単位のキー

   `--emit-ir-text`、`--emit-ir`、`--via-ir` は、型検査を済ませた単位の並びを第18章に渡し、
   KIR のプログラムを作る。
   単位のキー(診断では「鍵」)は、コマンド行と import 文から決める(IRSpec 2.2 節)。
   キーは基準のディレクトリからの相対パスなので、作業ディレクトリや絶対パスの表記はキーに現れない。

   - 基準のディレクトリ `B` は、コマンド行の最初のファイルの `dirname` に、
     下の正規化を適用したものである。
   - 起点のファイルのディレクトリは、そのファイルの `dirname` を同じ規則で正規化し、
     `B` からの相対パスで表したものである。
     `B` と共通する先頭の要素を取り除き、`B` に残った要素の数だけ `..` を置いて、
     残りの要素を続ける。
     一方だけが絶対パスのときと、`B` に残った要素に `..` があるときは、
     パスの文字列からは相対パスを決められない。
     そのときは、両方のディレクトリの `realpath` から同じ規則で相対パスを作る。
   - 相対パスの import のキーは、import を書いたファイルのキーのディレクトリ、import のパス、
     `.kel` を連結して正規化したものである。
   - 検索パスの import のキーは、`@i/`、import のパス、`.kel` を連結したものである。
     `i` は、そのファイルが見つかった `--import-path` のディレクトリのうち、
     最も前のものの番号(1 始まり)である。

   正規化は、空の要素と `.` を取り除き、`..` を直前の要素とともに取り除く。
   ただし、直前の要素がないとき、直前の要素が `..` のとき、
   直前の要素が先頭の要素で検索パスの接頭辞(`@` と数字)のときは、`..` を残す。
   キーは、各ファイルに最初に到達した import 文から決める。
   たどる順序は、起点のファイルはコマンド行に書いた順、
   各ファイルの import は書いた順の深さ優先である。
   §16.3b の `load_units` が単位を読む順序と同じである。

   この規則だけでは、異なる 2 つのファイルが同じキーになることがある。
   シンボリックリンクの下の `..` は、パスの文字列から取り除いた結果と OS が解決した結果とで、
   指すファイルが違うことがあるからである。
   キーが重なると、KIR のシンボルが参照先の宣言を一意に指せない。
   そのときは KIR を書き出さず、`diktor: KIR の単位の鍵が重なります` で始まる行を標準エラーに出力して、
   終了コード 64 で終了する。 *)
let is_search_mark c =
  String.length c > 1 && c.[0] = '@' && String.for_all (fun ch -> ch >= '0' && ch <= '9') (String.sub c 1 (String.length c - 1))

let key_components p =
  let rec go acc = function
    | [] -> List.rev acc
    | ("" | ".") :: rest -> go acc rest
    | ".." :: rest -> (
        match acc with
        | [ x ] when is_search_mark x -> go (".." :: acc) rest
        | x :: acc' when x <> ".." -> go acc' rest
        | _ -> go (".." :: acc) rest)
    | c :: rest -> go (c :: acc) rest
  in
  go [] (String.split_on_char '/' p)

let key_normalize p = String.concat "/" (key_components p)

let key_dir k = match String.rindex_opt k '/' with Some i -> String.sub k 0 i | None -> ""

let is_absolute p = String.length p > 0 && p.[0] = '/'

(* 正規化したディレクトリ b から d への相対パスを、要素のリストで返す。
   b に残った要素に .. があれば相対パスを決められないので、None を返す *)
let relative_components b d =
  let rec strip b d = match (b, d) with x :: b', y :: d' when x = y -> strip b' d' | _ -> (b, d) in
  let b', d' = strip b d in
  if List.mem ".." b' then None else Some (List.map (fun _ -> "..") b' @ d')

let unit_keys options deps roots =
  let first = match options.o_files with f :: _ -> f | [] -> "." in
  let base_dir = Filename.dirname first in
  let base = key_components base_dir in
  let root_dir f =
    let dir = Filename.dirname f in
    let textual = if is_absolute base_dir = is_absolute dir then relative_components base (key_components dir) else None in
    let comps =
      match textual with
      | Some cs -> cs
      | None -> (
          match relative_components (key_components (realpath base_dir)) (key_components (realpath dir)) with
          | Some cs -> cs
          | None -> bug ("KIR の単位の鍵: 起点のディレクトリの相対パスを決められません: " ^ f))
    in
    String.concat "/" comps
  in
  let keys = Hashtbl.create 8 in
  let by_id = Hashtbl.create 8 in
  List.iter (fun u -> Hashtbl.replace by_id u.u_id u) deps;
  let key_of dir (im : Syntax.import_decl) id =
    let src = im.Syntax.im_source in
    match split_import_path im.Syntax.im_loc src with
    | Some _, _ -> key_normalize ((if dir = "" then "" else dir ^ "/") ^ src ^ ".kel")
    | None, comps ->
        let file = String.concat "/" comps ^ ".kel" in
        let rec find i = function
          | [] -> bug ("KIR の単位の鍵: 検索パスに見つかりません: " ^ src)
          | d :: rest ->
              let path = Filename.concat d file in
              if Sys.file_exists path && realpath path = id then "@" ^ string_of_int i ^ "/" ^ src ^ ".kel" else find (i + 1) rest
        in
        find 1 options.o_import_path
  in
  let rec visit dir u =
    List.iter
      (fun (im, id) ->
        if not (Hashtbl.mem keys id) then (
          let k = key_of dir im id in
          Hashtbl.replace keys id k;
          visit (key_dir k) (Hashtbl.find by_id id)))
      u.u_targets
  in
  List.iter2 (fun r f -> visit (root_dir f) r) roots options.o_files;
  let result = List.map (fun u -> (Hashtbl.find keys u.u_id, u.u_display)) deps in
  (* 異なるファイルが同じキーになったら、KIR を書き出さずに終了コード 64 で終了する *)
  let owner = Hashtbl.create 8 in
  List.iter
    (fun (k, d) ->
      match Hashtbl.find_opt owner k with
      | Some d0 ->
          (try Printf.eprintf "diktor: KIR の単位の鍵が重なります: %s(%s と %s)\n" k d0 d with Sys_error _ -> ());
          safe_exit 64
      | None -> Hashtbl.replace owner k d)
    result;
  result

(* 型検査の後に KIR のプログラムを作る。
   単位は、プレリュード、import した単位、起点の順に並べる *)
let ir_program options =
  let units, deps, roots = type_check_files_units ~quiet:true options in
  let prelude_paths = if options.o_no_prelude then [] else [ Option.value ~default:"<prelude>" options.o_prelude ] in
  let metas = (("prelude", prelude_paths) :: List.map (fun (k, d) -> (k, [ d ])) (unit_keys options deps roots)) @ [ ("main", options.o_files) ] in
  let srcs = List.map2 (fun (k, ps) ds -> { Ir_write.us_key = k; us_paths = ps; us_decls = ds }) metas units in
  Ir_write.program srcs

(* 出力先のファイルに書けないときは、標準出力に書けないときと同じく終了コード 74 で終了する。
   メッセージには、書き出せなかったものが KIR のテキストかバイナリかを書く。
   with_open_bin は最後の flush のエラーを捨てるので、書き終えたら自分で flush する *)
let write_ir_file what file write =
  match Out_channel.with_open_bin file (fun oc -> write oc; Out_channel.flush oc) with
  | () -> ()
  | exception Sys_error msg ->
      (try Printf.eprintf "diktor: KIR の%sを書き出せません: %s\n" what msg with Sys_error _ -> ());
      safe_exit 74

(* ## 16.6c KIR の経路

   KIR を扱うオプションは、第18章から第22章までの部品を次のようにつなぐ。

   | オプション | 型検査 | 書き出し | 符号化 | 読み込み | 検証 | 評価 |
   |---|---|---|---|---|---|---|
   | `--emit-ir-text FILE` | ○ | ○ | テキスト(第19章) | × | × | × |
   | `--emit-ir FILE` | ○ | ○ | バイナリ(第20章) | × | × | × |
   | `--run-ir FILE` | × | × | × | ○ | ○ | 第22章 |
   | `--via-ir` | ○ | ○ | バイナリ | ○ | ○ | 第22章 |

   `--via-ir` は、自分で書いたバイナリを、ファイルを介さずにそのまま読み戻す。
   読み戻したプログラムを第22章で評価した結果が第14章の結果と一致すれば、
   書き出し、符号化、読み込み、検証、
   評価のどの段階もプログラムの意味を変えていないことの証拠になる。

   終了コードは次のとおりである。

   - 型検査までのエラーは、KIR のオプションを指定しない `Run` と同じ終了コードになる(1、2、4、64)。
   - UTF-8 でない名前があるプログラムは、KIR を持たない(KIR では表せない。IRSpec 13.4 節)。
     原因は入力の名前にあるので、テキストとバイナリのどちらを書くときも、
     何も書かずに終了コード 64 で終了する。
     そのため、テキストだけを書くときも、先にバイナリへ符号化して名前を検査する。
     それ以外の符号化のエラーは書き出しのバグなので、内部エラーとして終了コード 3 で終了する。
   - ノードの深さが入れ子の上限(IRSpec 13.9 節)を超えるプログラムも、KIR を持たない。
     どのリーダも、そのファイルを拒否するからである。
     型検査の段階の深すぎる入れ子と同じく処理系の上限を超えた場合なので、
     診断の種別は `処理系の限度` である。
     テキストもバイナリも書かずに、終了コード 1 で終了する。
     `--via-ir` も、評価を始めずに終了コード 1 で終了する。
   - 読み込みか検証が KIR を拒否したときは、終了コード 65 で終了する。
     65 は BSD の sysexits の EX_DATAERR である。
     `--via-ir` で自分の書いたバイナリが拒否されたときも、同じく 65 で終了する。
     読み込みか検証の途中でスタックを使い切ったときやメモリが不足したときも、65 で終了する。
   - 評価のエラーは、第14章と同じ例外で最上位の例外ハンドラに届き、同じ終了コードになる(§16.8)。
     第22章は論理的な深さを数え、上限を超えたら実行時エラー(終了コード 3)にする。
     上限は `--max-depth N` で変えられ、既定は第22章の `default_max_depth` である。
   - 第22章の評価器は、非末尾呼び出しのたびに OCaml のスタックも使う。
     1 段あたりの使用量は、その関数の中で呼び出しを囲む式の入れ子が深いほど増える。
     そこで評価の前に OCaml のスタックの上限を `ir_stack_limit` まで引き上げ、
     論理的な深さの上限より先にスタックを使い切る場合を減らす。
     それでも使い切ったときは、ほかの経路と同じくスタックオーバーフローの実行時エラー(終了コード 3)になる。
     環境変数 `OCAMLRUNPARAM` か `CAMLRUNPARAM` が `l` を指定しているときは、上限を変えず、
     その値に従う。

   `--dump-ir-tables` は、KIR の組み込みの表(IRSpec 付録 A)を出力する。
   出力するのは、第18章と第13章が実際に使う表そのものである。
   出力を付録 A と比べれば、付録 A と実装の食い違いが分かる。 *)
let encode_ir prog =
  match Ir_bin.encode_exn prog with
  | data -> data
  | exception Ir_bin.Name_error msg ->
      flush_stdout_or_die ();
      (try Printf.eprintf "diktor: KIR を符号化できません: %s\n" msg with Sys_error _ -> ());
      safe_exit 64
  | exception Ir_bin.Limit_error msg ->
      flush_stdout_or_die ();
      (try Printf.eprintf "diktor: KIR を書き出せません: %s\n" msg with Sys_error _ -> ());
      safe_exit 1
  | exception Ir_bin.Encode_error msg -> bug ("KIR を符号化できません: " ^ msg)

let emit_ir options =
  let prog = ir_program options in
  let data = encode_ir prog in
  Option.iter (fun file -> write_ir_file "テキスト" file (fun oc -> Ir_text.output oc prog)) options.o_emit_ir_text;
  Option.iter (fun file -> write_ir_file "バイナリ" file (fun oc -> Out_channel.output_string oc data)) options.o_emit_ir

(* 読み込みか検証が KIR を拒否したことを報告し、終了コード 65 で終了する。
   標準出力を先に flush する(§16.8 の出力先の規約) *)
let reject_ir what msg =
  flush_stdout_or_die ();
  (try Printf.eprintf "diktor: %s: %s\n" what msg with Sys_error _ -> ());
  safe_exit 65

(* 読み込みか検証がメモリを使い尽くしたときも、不正な KIR と同じく終了コード 65 で終了する *)
let load_ir data =
  match Ir_bin.decode data with
  | Error msg -> reject_ir "KIR を読み込めません" msg
  | exception Out_of_memory -> reject_ir "KIR を読み込めません" "処理系の限度: KIR の読み込みでメモリが不足しました"
  | Ok prog -> (
      match Ir_check.check prog with
      | Ok () -> prog
      | Error msg -> reject_ir "KIR の検証に失敗しました" msg
      | exception Out_of_memory -> reject_ir "KIR の検証に失敗しました" "処理系の限度: KIR の検証でメモリが不足しました")

let set_cancel_log () =
  Interp.cancel_log :=
    fun msg ->
      (* stderr へ書く直前に stdout を flush する(§16.8 の出力先の規約) *)
      flush_stdout_or_die ();
      try Printf.eprintf "cancel 節で例外が抑制されました: %s\n" msg; flush stderr with Sys_error _ -> ()

(* 第22章の評価器に与える OCaml のスタックの上限で、単位はワードである。
   8 GiB に相当する *)
let ir_stack_limit = 1 lsl 30

let stack_limit_given () =
  let given v = List.exists (fun x -> String.length x > 2 && String.sub x 0 2 = "l=") (String.split_on_char ',' v) in
  List.exists (fun n -> match Sys.getenv_opt n with Some v -> given v | None -> false) [ "OCAMLRUNPARAM"; "CAMLRUNPARAM" ]

let eval_ir options prog =
  set_cancel_log ();
  (if not (stack_limit_given ()) then
     let g = Gc.get () in
     if g.Gc.stack_limit < ir_stack_limit then Gc.set { g with Gc.stack_limit = ir_stack_limit });
  Ir_eval.run ?max_depth:options.o_max_depth ~sink:print_string prog

let run_ir options file =
  let data = with_input (fun () -> In_channel.with_open_bin file In_channel.input_all) in
  eval_ir options (load_ir data)

let via_ir options =
  let prog = ir_program options in
  eval_ir options (load_ir (encode_ir prog))

(* 環境変数 DIKTOR_VIA_IR は、モードのオプションも KIR のオプションも指定しない `Run` にだけ影響する(§16.1) *)
let via_ir_requested options = options.o_via_ir || Sys.getenv_opt "DIKTOR_VIA_IR" = Some "1"

(* 組み込みの表を、IRSpec 付録 A の節の順に、1 行に 1 項目ずつ出力する。
   インスタンスのメソッドは、クラスの順、型の順、メソッドの順に並べる。
   プリミティブ以外で実装したメソッドは、実装の列を `-` にする *)
let dump_ir_tables () =
  List.iter (fun t -> Printf.printf "type builtin/%s\n" t) Ir_write.builtin_types;
  List.iter (fun (c, ms) -> Printf.printf "class builtin/%s %s\n" c (String.concat " " ms)) Ir_write.builtin_classes;
  let impls = Builtin.builtin_method_prims @ List.map (fun (k, _) -> (k, "-")) Builtin.builtin_method_direct in
  List.iter
    (fun (c, ms) ->
      List.iter
        (fun t ->
          List.iter
            (fun m -> match List.assoc_opt (c, t, m) impls with Some p -> Printf.printf "method %s %s %s %s\n" c t m p | None -> ())
            ms)
        Ir_write.builtin_types)
    Ir_write.builtin_classes;
  List.iter (fun v -> Printf.printf "value builtin/%s\n" v) Ir_write.builtin_values;
  List.iter (fun (p, _) -> Printf.printf "prim %s\n" p) Builtin.prims;
  List.iter (fun (p, _) -> Printf.printf "c %s\n" p) Builtin.c_prims

(* ## 16.6b 対話的な実行

   `--repl` は、標準入力から宣言と式文を読み、入力ごとに型検査して実行し、結果を表示する。
   プレリュードは起動時に 1 回だけ処理する。
   前の入力の束縛は、後の入力から使える。

   ### 入力の終わり

   行を読むたびに、まだ確定していない行をつないだ文字列を、ファイルと同じ開始記号で構文解析する。
   構文解析に成功すれば、その入力を確定する。
   構文エラーの位置のトークンが `EOF` なら、続きの行を待つ。
   字句解析器は最後に渡したトークンを `prev` に持つので、
   `Parser'.Error` を受けた時点で `prev = Some EOF` かどうかを調べれば判定できる。
   閉じていない文字列リテラルとブロックコメントの字句エラーでも、続きの行を待つ。
   それ以外の構文エラーと字句エラーは、その入力を捨てて報告する。
   報告する位置は、ファイルと同じく §16.3 の `parse_error_message` が決める。
   続きを待った入力が次の行で文法に合わなくなったときは、
   報告する位置が前の行の終わりになることがある。
   第2章 §2.11 の `error_positions` が、前の行の末尾の改行を、
   行の続きとして捨てた改行と判定したときである。
   ブロックの中で文の区切りになった改行の後ろで文法に合わなくなったときは、
   汎用のメッセージが、合わなかったトークンの位置を指す。
   予約語の誤用の判定(§16.3a)は、
   予約語を識別子に置き換えて次のトークンまで読み進められることを条件にする。
   入力ごとに別々に構文解析するので、次のトークンが `EOF` のことがある。
   そのときは、置き換えた入力がそこで終われることが判定の条件の 1 つになる。
   構文解析に成功した時点で入力を確定するので、
   次の行で始まる継続(`let rec … and`、行頭の二項演算子、行頭の `.` や `match`)は、
   前の入力の続きにならない。

   ### 失敗した入力の取り消し

   型検査が拒否した入力(平坦化のエラーを含む型エラー、未実装、`処理系の限度`)では、
   宣言表(第6章 §6.14 のコピー)、
   単一化のセルの書き換え(第1章 §1.5 の記録)、型の環境を、入力の前の状態に戻す。
   実行時エラーになった入力では、さらに、
   その入力で評価器が行った書き込みもまとめて戻す(第14章 §14.15)。
   型の側も入力の前に戻すのは、途中まで実行した環境と型の環境が食い違わないようにするためである。
   出力は戻さない。

   ### 結果の表示

   束縛した名前ごとに `名前 : 型 = 値` の行を出力する。
   式文では、名前の代わりに `_` を書く。
   型が `{}` の式文では何も出力しない。
   `echoln(...)` のたびに `_ : {} = ()` が出るのを避けるためである。
   値を `Show.show` で表示するのは、
   型の先頭の型構成子が宣言表 `datas` にあり(`newtype` で宣言した型と、組み込みのデータ型)、
   その型が `Show` を満たすときだけである。
   満たすかどうかは、型検査器に `Show` の制約を追加して確かめ、追加による書き換えはすぐに戻す。
   それ以外の値は `Value.show` で表示する。
   組み込みの `Show[String]` は引用符を付けないので、
   文字列を `Show.show` で表示すると識別子と区別できないからである。
   関数の値は、組み込みの関数も含めて `<fn>` と表示する。
   辞書を受け取る値(制約付きで一般化した値束縛と式文)は、型の決まっていない辞書を渡して評価し、
   その結果の値を表示する。
   この条件を満たして `Show.show` を使うときも、
   `Show.show` に渡すのは評価した後の値である。
   初期化式は構文上の値なので、この評価は停止し、エフェクトを起こさない。
   初期化式が穴に到達したときだけ、値の代わりに `<unevaluated>` を出力する。

   ### Print とトップレベル

   対話的な実行でだけ、トップレベルのエフェクト行に `Print` を追加し、
   最も外側のハンドラが `Print.print` を出力先へ送る(第13章 §13.6)。
   そのため、トップレベルで `println` を呼ぶと、ハンドラを書かなくてもそのまま出力される。
   `Print` をエフェクト行に追加するのも出力先へ送るのも、
   `Print` をプレリュードが所有するときだけである。

   ### コマンドと出力先

   入力の途中でない行が `:` で始まれば、コマンドとして扱う。
   `:quit`(`:q`)は、セッションを終了する。
   `:reset` は、プレリュードだけを処理した状態に戻す。
   `:type 式` は、式を型検査して一般化した型を表示する。
   式は評価せず、型検査による書き換えは必ず戻す。
   それ以外のコマンドには、`未知のコマンド: ` で始まる行を出力する。

   結果、診断、プログラムの出力は、すべて標準出力に出力する。
   入力と応答が対になるので、出力を 1 本の流れにまとめる。
   プロンプトは、標準入力が端末のときだけ出力する
   (`In_channel.isatty` は Stdlib にあり、`unix` を必要としない)。
   入力の終わりか `:quit` で、終了コード 0 で終了する。
   型エラーや実行時エラーでは、セッションを終了しない。
   標準入力を読めないとき(閉じている、ディレクトリである、
   O_NONBLOCK の付いた空のパイプであるなど)は、
   `diktor: 標準入力を読めません: ` に理由を続けた行を stderr に出力し、終了コード 74 で終了する。
   O_NONBLOCK の付いた空のパイプでは `Sys_blocked_io` が投げられるので、
   理由には EAGAIN の説明を書く。
   どちらの例外も、行を読んだその場で受ける。
   最上位の例外ハンドラ(§16.8)に届くと、
   `Sys_error` は出力エラー(標準出力に書き出せない)として報告され(§16.3)、
   `Sys_blocked_io` は内部エラーとして報告されるからである。 *)

type parse_result = Complete of Tree.Tree.decl list | Incomplete | Failed of string

let try_parse ~line ?(col = 0) source =
  let lexbuf = Sedlexing.Utf8.from_string source in
  (* col は、入力の行の中で source が始まる位置を、行頭からの文字数で表す。
     :type の後ろの式なら、:type と空白 1 個の長さの 6 である *)
  Sedlexing.set_position lexbuf { Lexing.pos_fname = "<stdin>"; pos_lnum = line; pos_bol = -col; pos_cnum = 0 };
  Sedlexing.set_filename lexbuf "<stdin>";
  let lx = Lexer'.from_sedlex lexbuf in
  match parse_program lx with
  | [], ds -> Complete ds
  | im :: _, _ ->
      Failed (Printf.sprintf "%s: 構文エラー: import は対話的な実行では書けません" (show_pos im.Syntax.im_loc.Location.start))
  | exception Parser'.Error ->
      if lx.Lexer'.prev = Some Lexer'.Parser.EOF then Incomplete
      else Failed (parse_error_message lx)
  | exception Lexer.Lex_error (msg, _) when msg = Lexer.unterminated_text_msg || msg = Lexer.unterminated_comment_msg ->
      Incomplete
  | exception Lexer.Lex_error (msg, pos) -> Failed (Printf.sprintf "%s: 字句エラー: %s" (show_pos pos) msg)
  | exception Syntax.Syntax_error_at (pos, msg) -> Failed (Printf.sprintf "%s: 構文エラー: %s" (show_pos pos) msg)
  | exception ((Stack_overflow | Out_of_memory) as ex) -> Failed (read_limit_message "<stdin>" ex)

(* 実行時エラーのメッセージを返す。
   §16.8 の最上位の例外ハンドラと同じメッセージにそろえる *)
let runtime_message = function
  | Value.Runtime_error msg -> "実行時エラー: " ^ msg
  | Effect.Unhandled (Value.Op (op, _)) -> "未処理のエフェクト操作: " ^ Syntax.Type.display_of op
  | Stack_overflow -> "実行時エラー: スタックオーバーフロー(再帰が深すぎます)"
  | Out_of_memory -> "実行時エラー: メモリ不足です"
  | Panic msg -> msg
  | ex -> "内部エラー: 予期しない例外です: " ^ Printexc.to_string ex

(* 単一化の書き換えの記録を有効にして f を呼び、f が行った書き換えをすぐに元に戻す *)
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

(* 辞書を受け取る値は、型の決まっていない辞書(DPending)を渡して評価してから表示する。
   初期化式は構文上の値なので、評価は停止し、エフェクトを起こさない。
   穴に到達して実行時エラーになったときは None を返し、呼び出し元が <unevaluated> と表示する *)
let force_for_display v =
  match v with
  | Value.VDictAbs da -> (
      match da.Value.da_fn (List.init da.Value.da_arity (fun _ -> Value.VDict Value.DPending)) with
      | v -> Some v
      | exception Value.Runtime_error _ -> None)
  | v -> Some v

let show_value ty v =
  match force_for_display v with
  | None -> "<unevaluated>"
  | Some v ->
      let open Syntax.Type in
      let shows =
        match repr ty with
        | TCon (c, _) when Hashtbl.mem Decls.datas c -> (
            try probe (fun () -> Unify.add_class ty (intern "Show"); true) with Aux.Type_error _ | Aux.Type_error_at _ -> false)
        | _ -> false
      in
      if shows then
        (* 型から Show の証拠を作り、それを評価して辞書にし、show メソッドを選ぶ。
           型の決まらない部分の辞書は DPending になる *)
        let env = { Value.globals = Hashtbl.create 1; locals = Value.SMap.empty; dicts = Value.DMap.empty; resume = None } in
        let d = Interp.eval_ev env (Unify.display_evidence (intern "Show") ty) in
        match Interp.apply (Interp.select_method ~cls:(intern "Show") d "show" []) (Value.VRecord [ (l_item, v) ]) with
        | Value.VText s -> s
        | v -> Value.show ~fn_name:false v
      else Value.show ~fn_name:false v

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
  (* 宣言表と第11章の状態のコピーを取り、単一化の書き換えの記録を有効にして f を呼ぶ。
     f が `Undo を返すか例外を投げたら、f を呼ぶ前の状態に戻す *)
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
            (* 束縛の型は、名前ではなく参照先の宣言で引く。
               名前で引くと、1 つの入力の中で同じ名前を 2 回束縛したときに、
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
    (* 行末の空白、タブ、CR は取り除く *)
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
    | exception Sys_error msg ->
        Printf.eprintf "diktor: 標準入力を読めません: %s\n" msg;
        safe_exit 74
    | exception Sys_blocked_io ->
        Printf.eprintf "diktor: 標準入力を読めません: %s\n" (Unix.error_message Unix.EAGAIN);
        safe_exit 74
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

(* ## 16.7 モードごとの処理の流れ

   どの段階まで実行するかは、モードごとに異なる。

   | モード | 字句 | 構文 | 読み込み | 平坦化 | 型検査 | 評価 |
   |---|---|---|---|---|---|---|
   | `DumpTokens` | ○ | × | × | × | × | × |
   | `DumpAst` | ○ | ○ | × | × | × | × |
   | `TypeCheck` | ○ | ○ | ○ | ○ | ○ | × |
   | `Run` | ○ | ○ | ○ | ○ | ○ | ○ |
   | `DumpIrTables` | × | × | × | × | × | × |

   `Repl` は表にない。
   入力ごとに字句解析、構文解析、平坦化、型検査、評価を行い、import は受理しない(§16.6b)。
   `Run` に KIR のオプションを指定したときの経路は、§16.6c の表にある。
   `--run-ir` は字句解析から型検査までを行わず、KIR を読んで検証してから評価する。

   読み込みは、import をたどって依存する単位を集める段階である(§16.3b)。
   ダンプ系のモードは import をたどらず、コマンド行で渡したファイルだけを読む。

   ダンプ系のモードは、意図して型検査を行わない。
   型検査に通らないプログラムの字句と構文を見るためのオプションなので、
   型検査で止まると役に立たない。
   `DumpAst` が平坦化も行わないのは、脱糖した直後の木を見せるためである。
   平坦化は module を展開して名前を書き換えるので、平坦化の後の木からは、
   パーサが作った木が分からない。

   `Run` は先に型検査を行い、その結果を評価へ渡す。
   型検査に通らないプログラムは実行しない。

   評価の直前に、`Interp.cancel_log` を設定する。
   `cancel` 節の中で起きた例外は、巻き戻しを最後まで進めるために抑制するしかないが、
   黙って捨てるとデバッグできなくなる。
   そこで、抑制した例外を本章が標準エラーに出力する。
   対話的な実行では、標準出力に出力する。
   出力を第14章ではなく本章で行うのは、何をどこに出力するかを、
   外部との接点を扱う本章で決めるためである。
   ただし、例外からメッセージへの変換は、第14章と第22章の評価器のそれぞれの `run_cancel` が行う。
   既知の例外(`Runtime_error` / `Unwind` / `Sys_error`)だけが日本語のメッセージになり、
   それ以外は `Printexc` の表現のまま出力される。
   `Printexc` の表現が出力されたときは、内部エラーが起きている。

   第14章の評価器に渡すのは、プレリュードを先頭に置いた単位の並びである。
   型検査は、プレリュードが宣言した名前をプレリュード所有として記録するために、
   プレリュードをほかの単位と区別する。
   評価器は区別せず、先頭の単位から順に実行する。 *)
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
  | DumpIrTables -> dump_ir_tables ()
  | Run when options.o_emit_ir_text <> None || options.o_emit_ir <> None -> emit_ir options
  | Run when options.o_run_ir <> None -> run_ir options (Option.get options.o_run_ir)
  | Run when via_ir_requested options -> via_ir options
  | Run ->
      let units = type_check_files ~quiet:true options in
      set_cancel_log ();
      Interp.run_units ~sink:print_string units);
  (* モードの最後に stdout を flush し切る。
     最上位の例外ハンドラの中で flush して、失敗を終了コード 74 にするためである(§16.8 の不変条件) *)
  flush_stdout_or_die ()

(* ## 16.8 終了コード規約

   diktor の終了コードは、次の規約に従う。

   | コード | 意味 | 発生元 |
   |---|---|---|
   | 0 | 正常終了 | `run_with` が最後まで実行された |
   | 1 | 型エラー、import エラー | 第11章の診断、`Aux.Type_error`、`--strict-exhaustive`、§16.3b の `Import_error`、KIR の入れ子の上限 |
   | 2 | 構文エラー、字句エラー | `Parse_error`、`Lex_error`(不正な UTF-8 を含む) |
   | 3 | 実行時エラー | `Runtime_error`、未処理のエフェクト、深すぎる再帰、メモリ不足、内部エラー |
   | 4 | 未実装(Diktor が実装していない機能) | `Aux.NotImplemented`(module の入れ子、cancel(reason) など) |
   | 64 | 使い方のエラー | 引数解析の失敗、入力ファイルや import 先を開けない、UTF-8 でない名前を KIR に書けない、KIR の単位のキーが重なる |
   | 65 | 不正な KIR | `--run-ir` と `--via-ir` の読み込みと検証が拒否した(§16.6c) |
   | 74 | 入出力のエラー | 標準出力への flush の失敗、KIR のファイルを書き出せない、対話的な実行で標準入力を読めない |

   言語にない数値の接尾辞(`1u8`)と、言語になく宣言もされていない数値型の名前(`Int8`)は、
   未実装ではなく第11章の型エラーであり、終了コードは 1 である。

   深すぎる再帰とメモリ不足は、処理系の上限を超えたことを表し、起きた段階のエラーとして扱う。
   終了コードは、ソースの読み込み(字句解析と構文解析)の段階では 2、
   型検査の段階では 1、評価の段階では 3 である。
   KIR を書き出す段階で 1 になるのは、入れ子の上限を超えたときである(§16.6c)。
   この段階のスタックの使い切りとメモリ不足は、受けるハンドラがないので最上位の例外ハンドラに届き、
   3 になる。
   KIR の読み込みと検証の段階では、スタックの使い切りもメモリ不足も 65 である(§16.6c)。
   表の 3 の行にある深すぎる再帰とメモリ不足は、評価の段階のものと、
   どの段階のハンドラも受けなかったものである。

   64 は BSD の sysexits の EX_USAGE、65 は EX_DATAERR、74 は EX_IOERR である。
   独自の番号を選ぶより、すでにある慣習に従うほうがシェルスクリプトから扱いやすい。
   74 をプログラムのエラー(3)と分けているのは、
   標準入出力の故障がプログラムの責任ではないからである。

   ### すべての例外を受ける理由

   OCaml は、どのハンドラも受けなかった例外を致命的エラーとして出力し、終了コード 2 で終了する。
   2 は、この規約では構文エラーと字句エラーの番号である。
   `main` が例外をそのまま通すと、存在しないファイルもメモリ不足も深すぎる再帰も、
   すべて構文エラーと同じ終了コードで報告される。
   しかも、OCaml の例外名とバックトレースがユーザに見える。
   そこで `main` は、`run_with` を囲む 1 つの `try` 式ですべての例外を受け、
   規約どおりの診断と終了コードに変える。
   本章では、この `try` 式を最上位の例外ハンドラと呼ぶ。
   主な入力に対する報告は次のとおりである。

   | 入力 | 診断 | 終了コード |
   |---|---|---|
   | 存在しないファイル | ファイルを開けません | 64 |
   | 不正な UTF-8 バイト列 | 字句エラー | 2 |
   | module の入れ子、module 内の effect | 未実装 | 4 |
   | 評価の段階の深すぎる再帰 | 実行時エラー | 3 |
   | 評価の段階の巨大な確保 | 実行時エラー | 3 |
   | 構文解析の段階の長すぎる並び | 処理系の限度 | 2 |
   | 型検査の段階の深すぎる入れ子 | 処理系の限度 | 1 |
   | KIR に書けないほど深い入れ子 | 処理系の限度 | 1 |
   | 標準出力に書けない(/dev/full) | 出力エラー | 74 |

   表の「module の入れ子、module 内の effect」の行の未実装は、第11章の `flatten_modules` が投げる。
   プレリュードの平坦化は型検査の関数の外で行うので、その例外は型検査器の診断の流れを通らない。
   CLI では §16.6 の `type_check_files_units` がプレリュードの平坦化の例外を受け、
   型検査の診断と同じ書式と出力先で報告する。
   ユーザの単位の平坦化は第11章の `type_check_units` の中で行うので、
   その例外は型検査の診断として返る。
   それ以外の箇所で型検査の関数の外へ投げられたものは、
   最上位の例外ハンドラの `Aux.Type_error` と `NotImplemented` の節が受ける。

   ### 守るべき不変条件

   - 最上位の例外ハンドラは、`run_with` の全体を囲む 1 つだけである。
     このハンドラの `Stack_overflow` と `Out_of_memory` の節は、
     各段階のハンドラが受けなかったものを受け、
     終了コード 3 にする。
     評価の段階の深すぎる再帰とメモリ不足がそれにあたる。
     読み込みの段階と型検査の段階のものは、それぞれの段階のハンドラが診断に変える。
     読み込みの段階では §16.3 の `parse_unit_with` が受け、
     字句エラーや構文エラーと同じ終了コード 2 にする。
     対話的な実行では §16.6b の `try_parse` が受ける。
     型検査の段階では第11章の `type_check`、`type_check_units`、`catch_input_errors` が
     `limit_error` で診断に変え、型検査での拒否と同じ終了コード 1 にする。
     対話的な実行でも、入力の構文解析と型検査が上限を超えたときは入力の拒否として報告し、
     セッションは続く。
     各段階のハンドラの外で上限を超えたものも最上位の例外ハンドラに届き、終了コード 3 になる。
     対話的な実行の開始時に行うプレリュードの型検査(`Elab.start_session`)、`--dump-ast` の出力、
     KIR を書き出す段階のスタックの使い切りとメモリ不足がそれにあたる。
   - 規約を最終的に保証するのは、最後の catch-all の節である。
     OCaml は例外パターンの網羅性を検査しないので、
     新しい例外の節を追加し忘れてもコンパイルエラーにならない。
     catch-all の節は、規約にない例外をすべて内部エラー(終了コード 3)にする。
     個別の節は、分かりやすいメッセージを出すためにある。
     `Value.Op` 以外の `Unhandled`、`Continuation_already_resumed`、漏れた `Unwind` の専用の節は、
     内部エラーの種類をメッセージで示すための防御的な分岐である。
   - 診断の流れに乗せる例外には、第11章の `type_check`、`type_check_units`、
     `catch_input_errors` にも節が必要である。
     最上位の例外ハンドラだけに節を追加すると、
     そこまでに出力できたはずの型を表示する行がすべて失われる。
     `NotImplemented` は両方に節がある。
     第11章のこれらの関数の中で起きた `NotImplemented` は、診断の流れに乗る。
     プレリュードの平坦化で起きたものは §16.6 の `type_check_files_units` が受け、
     それ以外で外へ出たものは最上位の例外ハンドラが受ける。
   - 入力を開く箇所は、`with_input` で囲む。
     最上位の例外ハンドラは `Sys_error` を、
     出力エラーとして扱う(§16.3 の `Input_error` による分離)。
     そのため、囲み忘れた箇所の入力エラーは、誤って終了コード 74 で報告される。
   - モードの最後と exit の前に flush し切る。
     既定の flush は Format の at_exit が最上位の例外ハンドラの外で実行するので、
     失敗すると Fatal error と終了コード 2 になる。
     `flush_stdout_or_die` は最上位の例外ハンドラの中で flush し、失敗を終了コード 74 にする。

   出力先は、次の表のとおりモード単位で決める。

   | モード | 型を表示する行 | 警告 | 型エラー |
   |---|---|---|---|
   | --type-check | stdout | stdout | stdout |
   | Run | 出さない | stderr | stderr |

   `--type-check` は型検査の結果を表示するモードなので、型を表示する行も診断もすべて stdout に出す。
   型を表示する行とエラーの行を、1 本の流れとして比較できるようにするためである。
   Run は stdout をプログラムの出力専用にし、診断を混ぜない。
   最上位の例外ハンドラが受けるエラーは、どちらのモードでも stderr に出す。
   stderr へ書き出す前には、stdout を flush する。
   flush を挟まないと、両者を 1 本にまとめて比較する cram で順序が入れ替わる。 *)
let main () =
  (* SIGPIPE は無視する。
     既定のままだと、diktor f.kel | head の diktor がシグナルで終了し(128 + 13 = 141)、
     終了コードが規約にない値になる。
     無視すれば、書き込みが EPIPE で失敗して Sys_error を投げ、
     出力エラーとして終了コード 74 で終了する *)
  (try Sys.set_signal Sys.sigpipe Sys.Signal_ignore with Invalid_argument _ -> ());
  (* 標準出力の O_NONBLOCK を外す。
     親プロセスが非ブロッキングのパイプを渡すと、
     読み取る側のプロセスが遅れてパイプがいっぱいになったときに、書き込みが Sys_blocked_io を投げる。
     この例外が最上位の例外ハンドラまで伝わると、
     最後の節が内部エラーとして受け、終了コード 3 を選ぶ。
     続く safe_exit の flush は Sys_error だけを無視するので、
     パイプがいっぱいのままなら、そこでも Sys_blocked_io が投げられる。
     この例外は最上位の例外ハンドラの外へ出るので、出力が途中で切れ、終了コードは規約に合わない 2 になる。
     O_NONBLOCK を外せば、いっぱいになったパイプへの書き込みは、読み取る側のプロセスを待つ。
     オープンファイル記述は親プロセスと共有しているので、親プロセスの側の O_NONBLOCK も外れる。
     標準出力が閉じているときの失敗は無視し、後の書き込みのエラー(終了コード 74)に任せる *)
  (try Unix.clear_nonblock Unix.stdout with Unix.Unix_error _ -> ());
  match parse_args (Array.to_list Sys.argv |> List.tl) with
  | Error msg ->
      Printf.eprintf "diktor: %s\n%s" msg usage;
      safe_exit 64
  | Ok options -> (
      try
        run_with options;
        (* 正常終了も safe_exit を通す。
           通さないと、stderr に書けずに警告がバッファに残っているとき、
           at_exit の flush が失敗して、終了コードが 0 ではなく 2 になる *)
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
          (* 入力のエラーは Input_error に分けてあるので、ここに来るのは出力のエラーである *)
          die_output msg
      | Aux.Type_error_at (loc, msg) ->
          (* 型検査の関数の外で投げられた、位置付きの型エラーを受ける。
             CLI では、プレリュードの平坦化の型エラーを type_check_files_units が先に受ける *)
          Printf.eprintf "! %s: 型エラー: %s\n" (show_pos loc.Location.start) msg;
          safe_exit 1
      | Aux.Type_error msg ->
          (* 位置のない型エラーを受ける。
             事情は Type_error_at の節と同じである *)
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
          (* 評価器が起こすエフェクトは Value.Op の 1 種類だけなので、ここに来たら内部エラーである *)
          Printf.eprintf "実行時エラー: 未処理のエフェクトです(内部エラー)\n";
          safe_exit 3
      | Effect.Continuation_already_resumed ->
          (* アフィン検査(§14.9 の r_used)が検出できなかった二重の再開を受ける *)
          Printf.eprintf "実行時エラー: 継続を二重に再開しました(内部エラー)\n";
          safe_exit 3
      | Value.Unwind _ ->
          (* 自動巻き戻しがハンドラの外へ漏れた場合を受ける。
             §14.9 の inst の採番が正しくないときに起きる *)
          Printf.eprintf "実行時エラー: ハンドラの外へ巻き戻しが漏れました(内部エラー)\n";
          safe_exit 3
      | Stack_overflow ->
          Printf.eprintf "実行時エラー: スタックオーバーフロー(再帰が深すぎます)\n";
          safe_exit 3
      | Panic msg ->
          Printf.eprintf "%s\n" msg;
          safe_exit 3
      (* 最上位の例外ハンドラの最後にある catch-all の節である。
         この節がないと、どの節にも合わない例外は OCaml の既定の動作で終了コード 2 になり、
         この規約では構文エラーと区別できず、例外名もユーザに見える。
         節の追加し忘れはコンパイルエラーにならないので、ここですべてを受ける。
         exit は例外を使わずにプロセスを終了する(Stdlib.exit は do_at_exit の後、sys_exit で終了する)。
         そのため、ほかの節が呼んだ exit を、この節が例外として受けることはない *)
      | ex ->
          Printf.eprintf "内部エラー: 予期しない例外です: %s\n" (Printexc.to_string ex);
          safe_exit 3 )

(* ## 16.9 bin/main.ml の 1 行のエントリポイント

   実行ファイルのソースは 1 行である。

   ```ocaml
   let () = Diktor.Driver.main ()
   ```

   dune は実行ファイル(bin/)とライブラリ(lib/)を分けており、
   実行ファイルは `(modules main)` の 1 モジュールだけを持つ。
   この分け方には、次の 3 つの利点がある。

   - ライブラリだけを、ほかの OCaml プログラムから使える。
     §16.5 の API を使えるのは、この分割があるからである。
   - cram テストが実行ファイルに依存できる。
     テストが `%{bin:diktor}` に依存すると、ライブラリも自動的にビルドされる。
   - エントリポイントが 1 か所にまとまり、リンクの単位が明確になる。

   main.ml には、ライブラリの関数を 1 つ呼ぶこと以外を書かない。
   引数の前処理や環境変数の読み取りを main.ml に書くと、
   その処理は、Diktor をライブラリとして使うプログラムからは使えない。
   §16.5 の API を呼ぶプログラムは main.ml を通らないので、CLI と API の経路が分かれる。
   しかも、経路が分かれてもコンパイルエラーは 1 つも出ない。

   ## 16.10 この章のまとめ

   本章はアルゴリズムを含まない。
   しかし、処理系を外から見たときの動作は本章だけが決める。
   たとえば、存在しないファイルを渡されたときに何を報告し、どの終了コードで終了するかは、
   本章が決める。
   本章の設計は、章の冒頭に挙げた 3 点に沿っている。

   1. オプションはモードを選ぶだけである。
      各モードは各章の関数を順に呼ぶだけで、処理そのものはドライバに書かない。
   2. 経路を分岐させない。
      プレリュードもユーザのファイルも同じ `parse_unit_with` に合流する。
      CLI の `Elab.type_check_units` も API の `Elab.type_check` も、
      第11章の同じ関数(`check_prelude` と `check_unit`)で型検査する。
      ただし、合流点の手前の前処理(平坦化など)がそろっていなければ、経路は合流点より前で分かれる。
      そのため、§16.5 の API も CLI と同じく、プレリュードとユーザの宣言の両方を平坦化する。
   3. 最上位の例外ハンドラから例外を漏らさない。
      漏れた例外は OCaml の既定の動作で終了コード 2 になり、終了コードの表と食い違う。
      規約にない例外は最後の catch-all の節が受け、
      出力の flush も最上位の例外ハンドラの中で済ませる(§16.8)。 *)
