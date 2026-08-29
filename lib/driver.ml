(* Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
   SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception *)

(* # 第16章 — ドライバと終了コード規約

   最後の章です。ここまでの 15 章が作った部品を 1 本の線につなぎ、外の世界 —
   コマンドライン、標準出力、そしてシェルが見る終了コード — に接続します。
   新しいアルゴリズムは 1 つも出てきません。出てくるのは規約と、規約を
   破らないための配管だけです。

   ## 配線図

   ```
   argv ──parse_args──▶ options
   FILE.kel ──Lexer(第2章)──▶ トークン列 ──Parser(第3章)──▶ decl list
   Prelude_embed.source ──(まったく同じ経路)──▶ prelude の decl list
                                  │
                                  ▼
                   Elab.flatten_modules(第11章。module の平坦化、裁定 D21)
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

   前章 (第15章、prelude.kel) から受け取るもの: 文字列定数に埋め込まれた
   プレリュードのソース。外へ渡すもの: 標準出力と標準エラーへの行、そして
   終了コード 1 つ。

   この章の主題は 3 行にまとめられます。

   - **旗はモードを選ぶだけ**にし、処理そのものは各章の関数に任せる。
   - **CLI とテストは同じ関数を通す**。終了コードの層を外した API を公開する
     (揃いきっていない点は §16.5 に正直に書きます)。
   - **どの例外もこの章の外へ出さない**。出た瞬間、終了コード規約が嘘になる。

   3 つ目が §16.8 の本題で、敵対的検証 (実装記録 260829-2b) が最も多くの欠陥を
   見つけた場所でもあります。 *)
open Aux

(* ## 16.1 旗とモード

   旗は 6 つ、モードは 4 つです。

   | 旗 | 効き先 | 何をするか |
   |---|---|---|
   | (なし) | `Run` | 型検査してから評価する |
   | `--type-check` | `TypeCheck` | 型検査だけ。束縛の型を宣言順に印字 |
   | `--dump-tokens` | `DumpTokens` | ASI 適用後のトークン列 |
   | `--dump-ast` | `DumpAst` | 脱糖後の AST を S 式で |
   | `--no-prelude` | `o_no_prelude` | プレリュードを空にする |
   | `--prelude PATH` | `o_prelude` | 埋め込みの代わりに PATH を読む |
   | `--strict-exhaustive` | `o_strict_exhaustive` | 網羅性・到達不能の警告をエラー化 |

   `usage` の文字列は「使い方の唯一の説明」で、テスト test/smoke.t が
   この文字列をそのまま期待値に持っています。文言を変えるとゴールデンが
   落ちるのは意図どおりで、旗を足して説明を書き忘れる事故を防ぎます。

   `--dump-tokens` を最初から用意したのは、**ASI とブレース再分類 (第2章) の
   正しさを機械的に固定できる手段が他にない**からです (計画 §9.2)。トークン列の
   ゴールデンだけが、暗黙のセミコロン挿入の判断を目に見える形で凍らせます。

   `--no-prelude` は第15章のカナリアの裏返しです。プレリュードが常に読まれる
   ということは、プレリュード自身の不具合がすべてのテストに混ざるということ。
   切り分けの逃げ道を 1 つ残しておきます。

   `mode` は排他で、旗を並べたら最後のものが勝ちます。`o_prelude` と
   `o_no_prelude` は直交ではなく、両方書いたら `--no-prelude` が勝ちます
   (§16.4 の分岐がそう書かれています)。 *)
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

(* ## 16.2 引数解析 — 手書きの畳み込み

   cmdliner は入れません。裁定 D15 で「依存は menhir と sedlex の 2 つだけ」と
   決めてあり、6 つの旗のためにその線を越える価値はないからです。代わりに
   引数リストを頭から食べる末尾再帰の `go` を書きます。

   形の要点は 2 つです。

   **例外ではなく `Result` を返す。** 使い方の誤りは異常事態ではなく、ごく普通の
   分岐です。呼び出し側 (§16.8 の `main`) が `Error` を受けて使い方を印字し
   終了コード 64 を返す — この流れなら、引数解析だけを単体で呼んでも副作用が
   ありません。

   **節の順序が意味を持つ場所が 1 つだけある。** ハイフンで始まる未知の引数を
   拒む節は、既知の旗すべての**後ろ**、ファイル名の節の**前**になければ
   なりません。前に出せば `--type-check` まで未知の旗として弾かれ、後ろに
   下げれば `--typo-check` が入力ファイル名として通ってしまいます。
   さらにこの節のガードは長さを先に見ています。空文字列の引数に対して
   添字 0 を取ると例外になるからで、空文字列はファイル名として扱われ、
   開く段で拾われます (§16.8 の `Sys_error`)。

   最後に `List.rev` でファイルの順序を戻します。畳み込みは逆順に積むためですが、
   順序が意味を持つこと自体が仕様です。複数ファイルは宣言順に連結処理され、
   仕様 sample.kel の回帰ではスタブを前置するのに使います (計画 §9.2)。 *)
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

   字句解析器 (第2章) とパーサ (第3章) は、AST のノードに貼るデータを
   パラメータに取るファンクタです。ここで第5章の `Tree.ElabData` を渡して
   実体化する — つまり「この処理系は精緻化 (elaboration) 用のデータを木に
   書き込む」という決定が、実際に効くのはこの 2 行です。別の用途で別のものを
   貼りたければ、別の実体化を作れば済みます。 *)
module Lexer' = Lexer.Make (Tree.ElabData)
module Parser' = Parser.Make (Tree.ElabData)

(* `Parse_error` は「位置まで整形し終えた 1 行」を運ぶための、この章専用の
   例外です。整形をここでやる理由がはっきりしています。menhir が投げる
   `Parser'.Error` は情報を持たず、どこで詰まったかは字句解析器が覚えている
   最後のトークン位置からしか取れません。パーサと字句解析器の両方を握って
   いるのはこの層だけなので、両者を結びつけられるのもここだけです。

   `main` は受け取って印字し、終了コード 2 を返すだけになります (§16.8)。 *)
exception Parse_error of string

(* 入力を開けない誤りだけをこの例外に閉じ込める(B5)。受け皿に届く裸の
   Sys_error は「出力に書き出せない」を意味する — 文字列を覗いて種類を
   当てるのをやめるための分離。入力を開く場所を新設したら必ず with_input で
   包むこと(包み忘れると、その Sys_error は出力エラーとして 74 に化ける) *)
exception Input_error of string

let with_input f = try f () with Sys_error msg -> raise (Input_error msg)

(* 出力の書き出しは終了コード規約の一部(B5 / D33)。
   exit の do_at_exit は Format の標準フォーマッタを flush し、書けない
   stdout / stderr ではそこで Sys_error が受け皿の外に飛んで Fatal error +
   終了コード 2 に化ける — つまり **exit 自身が例外を投げうる**。だから
   終了は必ず safe_exit を通す: 終了コードを決めたらフォーマッタを無効化し、
   チャネルは best-effort で flush してから exit する。無効化は行儀の良く
   ない手だが、Unix._exit の依存追加(D15 違反)よりよい *)
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
  (* stdout → stderr の順(cram は両者を 1 本に併合するので、プログラム
     出力 → 診断の順序を保つ)。失敗は握る — 終了コードはもう決まっていて、
     Fatal error + 2 に上書きさせない *)
  (try flush stdout with Sys_error _ -> ());
  (try flush stderr with Sys_error _ -> ());
  exit n

let die_output msg =
  Printf.eprintf "diktor: 標準出力に書き出せません: %s\n" msg;
  safe_exit 74

let flush_stdout_or_die () = match flush stdout with () -> () | exception Sys_error msg -> die_output msg

(* 位置は ファイル:行:桁。桁は行頭からの**コードポイント差** + 1 です。バイト差
   ではありません — 第2章がそのまま運んでくる `Sedlexing.lexing_positions` は
   コードポイント単位で数えるので、多バイト文字を含む行でも桁はずれません
   (実測: `あいう` を含む行と `abc` を含む行で、同じ位置の誤りが同じ桁に出ます)。

   ずれないのはコードポイントの数まで、という留保は付きます。結合文字も
   全角の表示幅も異体字セレクタも 1 と数えるので、エディタが見せる桁とは
   食い違い得ます。そこまで合わせるには表示幅の表を持つ必要があり、
   誤りの位置を指すという目的に対しては割に合いません。 *)
let show_pos = Location.show_pos

(* `--dump-tokens` の実体。第2章の 3 層のうち、ASI を通した**いちばん外側**の
   列を出します。ここが素のトークン列だと、暗黙のセミコロン挿入を固定する
   という目的を果たしません。 *)
let dump_tokens_file file =
  (* 読み取りは遅延で走る(Sedlexing は open の後、字句解析の駆動中に読む)ので、
     open だけでなくトークン列の実体化まで with_input で包む。印字は包まない —
     出力エラーを入力エラーと誤分類しないため(検証の指摘) *)
  let tokens = with_input (fun () -> Lexer'.all_tokens (Lexer'.from_filename file)) in
  List.iter (fun e -> Printf.printf "%4d  %s\n" e.Lexer'.sp.Lexing.pos_lnum (Lexer'.show_token e.Lexer'.tok)) tokens

(* 入口を 1 つにたたむ関数です。上流からは 2 種類の失敗が来ます。

   - `Parser'.Error` — menhir が次に進む節を選べなかった (文法に合わない)
   - `Syntax.Syntax_error` — 文法は通ったが、脱糖 (第3章) が形を拒否した

   利用者にとってはどちらも「読めませんでした」なので、位置つきの 1 行に
   そろえて `Parse_error` にします。区別を残したい日が来たら、ここで分ければ
   よい — 分岐点を 1 か所に集めておく価値はそこにあります。 *)
let parse_with lexer =
  try Lexer'.parse Parser'.program lexer with
  | Sedlexing.MalFormed ->
      (* 位置は失われているがファイル名は分かる(検証の指摘: 複数ファイルで
         どれが壊れているか分からなかった) *)
      raise (Parse_error (Printf.sprintf "%s: 字句エラー: 不正な UTF-8 バイト列です" lexer.Lexer'.last_sp.Lexing.pos_fname))
  | Parser'.Error ->
      raise (Parse_error (Printf.sprintf "%s: パースエラー(付近のトークンを確認してください)" (show_pos lexer.Lexer'.last_sp)))
  | Syntax.Syntax_error msg ->
      raise (Parse_error (Printf.sprintf "%s: 構文エラー: %s" (show_pos lexer.Lexer'.last_sp) msg))

(* パースの駆動ごと with_input で包む — 読み取りエラー(ディレクトリを渡した
   ときの EISDIR 等)は open ではなく読み取りで出る *)
let parse_file file = with_input (fun () -> parse_with (Lexer'.from_filename file))

(* 文字列版は、エラー行に見せる名前を自分で決めます。山括弧つきの名前
   (prelude や string) は「実在のファイルではない」という印で、
   利用者がその名前でファイルを探さないようにするための慣習です。

   規約はこう読みます: **山括弧は実在しないもの(埋め込み・文字列 API)
   専用**。`--prelude PATH` で差し替えたプレリュードは実在するファイル
   なので、実在のパスを名乗ります(E9)。かつては差し替え側も `<prelude>` を
   名乗り、実在するファイルの誤りが `<prelude>:2:1: パースエラー…` と出て、
   利用者が自分の渡したパスを画面から拾えませんでした。 *)
let parse_string ~filename source =
  let lexbuf = Sedlexing.Utf8.from_string source in
  Sedlexing.set_filename lexbuf filename;
  parse_with (Lexer'.from_sedlex lexbuf)

(* ## 16.4 プレリュードの読み込み

   第15章はビルド時に OCaml の文字列定数へ埋め込まれ、`Prelude_embed.source`
   になります (計画 §8.6)。だからインストールされた diktor は、実行時に
   プレリュードのファイルを探しに行きません。単一の実行ファイルで完結します。

   出所は 3 択で、優先順位は次のとおりです。

   1. `--no-prelude` — 空の宣言列。何より優先される
   2. `--prelude PATH` — その中身を読む。開けなければ §16.8 が終了コード 64 に落とす
   3. 既定 — 埋め込みの文字列

   入口の関数こそ違いますが (ユーザのファイルは `parse_file`、プレリュードは
   出所がファイルでも文字列でも `parse_string`)、どちらも `parse_with` に
   合流します。**プレリュードだけが通る特別扱いの字句解析器やパーサは
   ありません。** 2 の場合に自分で `In_channel` を叩いているのはそのためで、
   ファイルから読んだ中身も文字列として同じ入口へ入れています。

   検証で気づいた点が 1 つ。差し替えたプレリュードが `module` を含むことは
   あり得るので、通常入力と同じく平坦化 (第11章) を通す必要があります。
   ただしこの関数は構文木のまま返し、平坦化するのは呼び出し側です
   (CLI 経路は §16.6)。読み込みと平坦化を分けたぶん、「呼び出し側がプレリュードと
   ユーザ宣言の両方に同じ前処理を掛けたか」を人間が見張ることになりました。
   実際、§16.5 の API では見張りに失敗しています。 *)
let load_prelude options =
  if options.o_no_prelude then []
  else
    let source =
      match options.o_prelude with
      (* --prelude PATH は実在のファイルなので、実在のパスを名乗る(E9)。
         山括弧の印は「実在しないもの」(埋め込み・文字列 API)専用 *)
      | Some path ->
          (path, with_input (fun () -> In_channel.with_open_bin path In_channel.input_all))
      | None -> ("<prelude>", Prelude_embed.source)
    in
    let filename, source = source in
    parse_string ~filename source

(* ## 16.5 サブプロセスなしで叩ける API

   計画 §8.7 の要求は「CLI とテストが同じ経路を通ること」でした。別経路を
   作ると、テストが通っても CLI が壊れている状態が起こり得ます。そこで
   文字列を受けて結果を返す関数を 2 つ公開します。

   - `type_check_string` — (出力行の一覧, エラー行 option) を返す
   - `eval_string ~sink` — 出力先を引数で受け取り、型エラーなら `Error` を返す

   `~sink` を差せることが肝で、標準出力を横取りしなくても出力を検証できます。
   第13章のランタイムハンドラがここに繋がっていて、`Console.write` はこの
   関数へ流れます。

   正直に書いておくと、この 2 つは CLI と**まったく同じ**経路ではありません。
   意図して外したのは終了コードの層で、型エラーは `exit 1` ではなく値として
   返り、`--strict-exhaustive` の判定と `Interp.cancel_log` の設置 (§16.7) は
   効きません。ここまでは設計です。

   前処理はいまや CLI と**同じ**です (E10) — `embedded_prelude` が平坦化まで
   済ませるので、プレリュードとユーザ宣言の両方が `flatten_modules` を
   通ってから型検査に入ります。意図して外してあるのは上の 3 つ(終了コードの
   層・`--strict-exhaustive`・`Interp.cancel_log`)だけ、と言い切れる状態に
   なりました。かつてはプレリュードだけ未平坦化で、プレリュードに `module`
   が入った日に API 経路だけが壊れる形が残っていました。

   また実装記録 260829-2 の乖離 6 でテスト機構が cram 一本になったため、
   現在の回帰テストは実行形を叩いています。この API は、Diktor をライブラリ
   として埋め込む利用者と、将来サブプロセスを避けたいテストのために
   残してあります。 *)
(* CLI 経路(§16.6)と同じ前処理を通す — 平坦化を落とすと、プレリュードに
   module が入った日に API 経路だけ exit 4 になる(E10) *)
let embedded_prelude () = Elab.flatten_modules (parse_string ~filename:"<prelude>" Prelude_embed.source)

(* 出力行と診断の整形。種別は第11章が値で運び、見た目はここで決める(D54)。
   型行 name : type / 警告 ⚠ / エラー ! — 先頭 1 文字で読み分けられる形を保つ *)
let render_line = function Elab.Binding s -> s | Elab.Warning s -> "⚠ " ^ s

let render_error (e : Elab.error) =
  (* start_of 経由にする — dummy span なら位置なしの形に落ちる(ガードの実配線) *)
  match Option.bind e.Elab.e_loc Location.start_of with
  | Some pos -> Printf.sprintf "! %s: %s: %s" pos e.Elab.e_word e.Elab.e_msg
  | None -> Printf.sprintf "! %s: %s" e.Elab.e_word e.Elab.e_msg

(* 型検査のみ。(出力行, エラー行 option) *)
let type_check_string ?(prelude = true) source =
  let pre = if prelude then embedded_prelude () else [] in
  let decls = Elab.flatten_modules (parse_string ~filename:"<string>" source) in
  let lines, err = Elab.type_check ~prelude:pre decls in
  (List.map render_line lines, Option.map render_error err)

(* 型検査 + 評価。出力は sink へ。型エラー時は Error を返す *)
let eval_string ?(prelude = true) ~sink source =
  let pre = if prelude then embedded_prelude () else [] in
  let decls = Elab.flatten_modules (parse_string ~filename:"<string>" source) in
  match Elab.type_check ~prelude:pre decls with
  | _, Some err -> Error (render_error err)
  | _, None ->
      Interp.run ~sink (pre @ decls);
      Ok ()

(* ## 16.6 型検査の入口と、警告の行き先

   プレリュードとユーザのファイルを別々に平坦化してから第11章へ渡します。
   2 つを分けたまま渡すのは、型検査器がプレリュードだけを `in_prelude` の
   下で処理して「プレリュード所有」の印を付けるためです
   (第15章 (prelude.kel) の §15.2)。
   この印があるおかげで、仕様 sample.kel が `Unit` や `Console` を
   もう一度宣言しても二重宣言にならずに済みます。

   ### 行の種別は値で運ばれてくる

   `--type-check` では型の行がそのまま欲しく、`Run` では型の行は邪魔ですが
   警告は捨てたくない。そこで `quiet` のときは警告だけを標準エラーへ
   逃がします。判定は第11章が返す `out_line` の**構造照合**です — 行は
   `Binding` か `Warning` かの値として届き、`⚠ ` の前置はこの章の
   `render_line` が最後に貼ります(D54)。

   かつては表示済み文字列の**先頭バイト**を覗いていました。警告記号
   U+26A0 の UTF-8 先頭バイトが `\xe2` だから 1 バイト比較で済む — 短くて
   速い代わりに、U+2000 から U+2FFF までのどの文字で始まる行も警告と
   見なされていました。だから種別を値で持たせたのです。

   > 出力の種類を文字列の見た目で判定すると、いつか見た目が変わって壊れる。
   > だから種別は値で持ち、見た目は出口で 1 度だけ作る。

   ### 2 つの脱出口

   `--strict-exhaustive` は「型エラーは無かったが警告が残った」場合に終了
   コード 1 を返します。網羅性検査 (第10章) の警告を CI のゲートに使うための
   旗です。既定で警告のままにしてあるのは、網羅性の指摘が「間違い」ではなく
   「見落としかもしれない」という報告だからで、締めるかどうかは利用者に
   選ばせます。ちなみに仕様 sample.kel の全文は警告ゼロで通ります。

   型エラーのときは、そこまでに出せた行と誤りの行を印字して終了コード 1。
   ここで `exit` を直接呼んでいることに意味があります。`exit` は例外ではないので、
   §16.8 の受け皿に横取りされません。もし例外で抜けていたら、型エラーが
   `Panic` や `Type_error` の節に吸い込まれて別のコードになり得ました。 *)

(* quiet = Run モード: 型行は出さず、警告だけ stderr に出す。
   種別は値で判定する — 表示文字列の先頭バイトを覗いていた頃は、
   U+2000〜U+2FFF で始まる任意の行が警告扱いだった(D54) *)
let type_check_files ?(quiet = false) options =
  (* 平坦化の診断も出力先のモード規約(D54)に乗せる。素通しにすると
     --type-check の「! 未実装:」だけが stderr に出て規約が二股になる
     (検証の指摘)。平坦化は型検査より前のパスなので、その診断より前に
     型の行が無いのは構造どおり *)
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
          (* stderr へ書く直前に stdout を flush する(D54)。stdout は
             バッファつき・stderr は行ごとに flush されるので、挟まないと
             両者を 1 本に併合する cram で順序が入れ替わる。stderr が
             壊れていても診断は best-effort — プログラムの実行は続ける *)
          flush_stdout_or_die ();
          (try prerr_endline (render_line l) with Sys_error _ -> ())
      | Elab.Binding _ -> ())
    else print_endline (render_line l)
  in
  match Elab.type_check ~prelude decls with
  | lines, None ->
      List.iter put lines;
      (* --strict-exhaustive が数えるのは「利用者に見せた警告」= 返って
         きた行だけ(D54 / E11)。大域の Elab.warnings を数えると、表示
         されないプレリュードの警告で「警告を 1 行も出さずに exit 1」
         という理由の分からない失敗になる(--prelude で実測) *)
      if options.o_strict_exhaustive && List.exists (function Elab.Warning _ -> true | _ -> false) lines then (
        flush_stdout_or_die ();
        safe_exit 1);
      (prelude, decls)
  | lines, Some err ->
      List.iter put lines;
      (* 出力先はモード単位(D54): --type-check はレポートなので全部
         stdout、Run は stdout をプログラム出力専用にして診断は stderr *)
      (if quiet then (
         flush_stdout_or_die ();
         try prerr_endline (render_error err) with Sys_error _ -> ())
       else print_endline (render_error err));
      flush_stdout_or_die ();
      safe_exit err.Elab.e_exit

(* ## 16.7 結線

   モードごとに、どこまで通すかが違います。

   | モード | 字句 | 構文 | 平坦化 | 型検査 | 評価 |
   |---|---|---|---|---|---|
   | `DumpTokens` | ○ | — | — | — | — |
   | `DumpAst` | ○ | ○ | — | — | — |
   | `TypeCheck` | ○ | ○ | ○ | ○ | — |
   | `Run` | ○ | ○ | ○ | ○ | ○ |

   ダンプ系が型検査を通らないのは**わざと**です。型が付かないプログラムの
   字句と構文を見るための旗なので、型検査で止まったら用を成しません。
   `DumpAst` が平坦化も飛ばすのは、見たいのが脱糖直後の木だからです。
   平坦化は module を潰して名前を書き換えてしまうので、通してしまうと
   「パーサが何を作ったか」が見えなくなります。

   `Run` は型検査を先に通し、その結果を評価へ渡します。型が付かないものは
   走らせない — 静的型付き言語の処理系として当然の順序ですが、ダンプ系との
   対比で見るとこの 1 行が方針の表明になっています。

   評価の直前に `Interp.cancel_log` を差し込みます。`cancel` 節の中で起きた
   例外は、巻き戻しを完了させるために握り潰さざるを得ませんが、黙って
   捨てるとデバッグ不能になります。敵対的検証では、ここが生の OCaml 例外
   表現をそのまま吐いていました。文言を与える場所が第14章ではなくこの章
   なのは、**何をどう見せるかは出口の責任**だからです。ただし例外から
   文言への写しは第14章の `run_cancel` にあり、既知の例外(`Runtime_error` /
   `Unwind` / `Sys_error`)だけが日本語になります — 未知のものは Printexc の
   表現のまま残り、それは内部エラーの印です。

   評価に渡すのは連結した `prelude @ decls` です。型検査は所有印のために
   2 つを区別しましたが、実行時に区別する理由はありません。 *)
let run_with options =
  (match options.o_mode with
  | DumpTokens -> List.iter dump_tokens_file options.o_files
  | DumpAst -> List.iter (fun file -> Dump.dump_decls stdout (parse_file file)) options.o_files
  | TypeCheck -> ignore (type_check_files options)
  | Run ->
      let prelude, decls = type_check_files ~quiet:true options in
      Interp.cancel_log :=
        (fun msg ->
          (* stderr へ書く直前の flush(D54 の順序規約はここにも効く) *)
          flush_stdout_or_die ();
          try Printf.eprintf "cancel 節で例外が抑制されました: %s\n" msg; flush stderr with Sys_error _ -> ());
      Interp.run ~sink:print_string (prelude @ decls));
  (* モードの最後に必ず flush し切る(§16.8 の受け皿の中で。B5) *)
  flush_stdout_or_die ()

(* ## 16.8 終了コード規約 — 例外を 1 か所で受け止める

   diktor の終了コードは規約です。

   | コード | 意味 | 出所 |
   |---|---|---|
   | 0 | 正常終了 | `run_with` が最後まで走った |
   | 1 | 型エラー | 第11章の診断、`Aux.Type_error`、`--strict-exhaustive` |
   | 2 | 構文・字句エラー | `Parse_error`、`Lex_error`、不正な UTF-8 |
   | 3 | 実行時エラー | `Runtime_error`、未処理エフェクト、再帰過多、メモリ不足、内部異常 |
   | 4 | 未実装(仕様にあって v0 に無い) | `Aux.NotImplemented`(1u8 / Int8 / module の入れ子 等) |
   | 64 | 使い方の誤り | 引数解析の失敗、入力ファイルを開けない |
   | 74 | 出力に書き出せない | 標準出力への flush の失敗(D33) |

   64 は BSD の sysexits の EX_USAGE、74 は EX_IOERR です。独自の番号を
   選ぶより、既にある慣習に乗るほうがシェルスクリプトから扱いやすい。
   74 がプログラムの誤り(3)と分かれているのは、出力先が壊れているのは
   プログラムの責任ではないからです。

   ### なぜ全部の例外を受けるのか

   ここが敵対的検証 260829-2b で最も収穫のあった場所です。理由は OCaml の
   既定の振る舞いにあります。**捕まえられなかった例外は、致命的エラーとして
   印字されたうえで終了コード 2 を返します。** そして 2 は、この規約では
   「構文・字句エラー」です。

   つまり素通しした例外はすべて「パースエラー」に化けます。存在しない
   ファイルを渡したら構文エラー、メモリが尽きても構文エラー、再帰が深すぎても
   構文エラー。しかも OCaml の例外名とバックトレースが利用者に漏れます。

   検証はここを狙い、実機で再現した順に潰しました。

   | 入力 | 素通しだったときの見え方 | いまの見え方 |
   |---|---|---|
   | 存在しないファイル | 例外名が漏れて 2 | ファイルを開けません、64 |
   | 不正な UTF-8 バイト列 | 例外名が漏れて 2 | 字句エラー、2 |
   | module の入れ子 / module 内の effect | 例外名が漏れて 2 | 未実装、4 |
   | 深すぎる再帰 | 例外名が漏れて 2 | 実行時エラー、3 |
   | 巨大な割り当て | 例外名が漏れて 2 | 実行時エラー、3 |
   | 標準出力が書けない(/dev/full) | 例外名が漏れて 2 | 出力エラー、74 |

   3 行目が地味に効きます。第11章の `flatten_modules` は `type_check` の
   **外**で走るので、そこが投げる `Type_error` は型検査器の診断経路を通りません。
   `Aux.Type_error` の節はそのために置かれています。

   ### 守るべき不変条件

   - **`run_with` を丸ごと囲む。** 受け皿を分割していないので、型検査中の
     再帰過多も評価中の再帰過多も同じ 3 になります。フェーズごとに分けたければ
     受け皿を割る必要がある — v0 は 1 枚で妥協しています。
   - **規約の担保は最後の catch-all が担う。** OCaml は例外パターンの
     網羅性を検査しないので、「新しい例外には節を足す」という規律は人間の
     記憶にしか無い — 足し忘れた例外は素通りして 2 に化けていました。
     いまは規約外の例外はすべて「内部エラー + 3」に落ちます。具体的な節は
     良い文言のためにあり、規約のためにあるのは最後の 1 枚です。
     `Value.Op` 以外の `Unhandled`、`Continuation_already_resumed`、
     漏れた `Unwind` の専用節は、内部異常に名前を与える防御枝です。
   - **診断の流れに乗る例外は `Elab.type_check` にも節が要る。** 受け皿
     だけに足すと、そこまでに出せた型の行が全部消える(§16.6 の
     「型の行と誤りの行を 1 本の流れで」が壊れる)。`NotImplemented` は
     両方に節がある — type_check の中で起きれば診断の流れに乗り、
     `flatten_modules` のように外で起きればこの受け皿が受ける。
   - **入力を開く場所は必ず `with_input` で包む。** 受け皿の `Sys_error` は
     「出力に書き出せない」と読む(§16.3 の `Input_error` の分離)ので、
     包み忘れた入力エラーは 74 と誤って報告されます。
   - **モードの最後と exit の前に flush し切る。** 既定の flush は Format の
     at_exit で受け皿の外を走り、失敗が Fatal error + 2 に化けます(B5 で
     実測)。`flush_stdout_or_die` が受け皿の中で 74 に落とします。

   > 終了コードの規約は、最後の受け皿が漏れていない限りでしか規約ではない。

   最後に印字先の話を 1 つ。出力先は**モード単位**の規約です(D54)。

   | モード | 型行 | 警告 | 型エラー |
   |---|---|---|---|
   | --type-check | stdout | stdout | stdout |
   | Run | 出さない | stderr | stderr |

   --type-check はレポートモードなので、型の行と誤りの行を 1 本の流れとして
   比較できるよう全部 stdout。Run は stdout を**プログラムの出力専用**にし、
   診断を混ぜません(かつては Run でも型エラーが stdout に出て、プログラムの
   出力に診断が混ざりました)。この受け皿が捕まえる誤りは従来どおり stderr。
   stderr へ書く直前には必ず stdout を flush します — 挟まないと、両者を
   1 本に併合する cram で順序が入れ替わります。 *)
let main () =
  (* SIGPIPE は無視する(D33)。既定のままだと diktor f.kel | head が
     シグナル死(128 + 13 = 141)になり、終了コード規約の外に出る。
     無視すれば書き込みが EPIPE = Sys_error になり、出力エラー 74 に落ちる *)
  (try Sys.set_signal Sys.sigpipe Sys.Signal_ignore with Invalid_argument _ -> ());
  match parse_args (Array.to_list Sys.argv |> List.tl) with
  | Error msg ->
      Printf.eprintf "diktor: %s\n%s" msg usage;
      safe_exit 64
  | Ok options -> (
      try
        run_with options;
        (* 正常終了も safe_exit を通す — 落とすと、書けない stderr に警告が
           残ったとき at_exit の flush が落ちて 0 が 2 に化ける(実測) *)
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
          (* 入力側は Input_error に閉じ込めてある。ここへ来るのは出力側(B5) *)
          die_output msg
      | Sedlexing.MalFormed ->
          Printf.eprintf "字句エラー: 不正な UTF-8 バイト列です\n";
          safe_exit 2
      | Aux.Type_error_at (loc, msg) ->
          (* flatten_modules など type_check の外で投げられる型エラー(位置つき) *)
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
          (* 評価器が起こすエフェクトは Value.Op 1 種類。ここへ来たら内部異常 *)
          Printf.eprintf "実行時エラー: 未処理のエフェクトです(内部エラー)\n";
          safe_exit 3
      | Effect.Continuation_already_resumed ->
          (* アフィン検査(§14.10 の r_used)を潜り抜けた場合の床 *)
          Printf.eprintf "実行時エラー: 継続を二重に再開しました(内部エラー)\n";
          safe_exit 3
      | Value.Unwind _ ->
          (* 自動巻き戻しがハンドラの外へ漏れた(§14.10 の inst 採番の破れ) *)
          Printf.eprintf "実行時エラー: ハンドラの外へ巻き戻しが漏れました(内部エラー)\n";
          safe_exit 3
      | Stack_overflow ->
          Printf.eprintf "実行時エラー: スタックオーバーフロー(再帰が深すぎます)\n";
          safe_exit 3
      | Panic msg ->
          Printf.eprintf "%s\n" msg;
          safe_exit 3
      (* 最後の 1 枚。ここが無いと、節に無い例外は OCaml の既定で終了コード 2 —
         この規約では「構文エラー」— に化け、例外名も漏れる。足し忘れが
         コンパイルエラーにならない以上、床を張るしかない。exit は例外を
         投げない(Stdlib.exit は do_at_exit + sys_exit)ので、この節が
         他の節の exit を横取りすることはない *)
      | ex ->
          Printf.eprintf "内部エラー: 予期しない例外です: %s\n" (Printexc.to_string ex);
          safe_exit 3 )

(* ## 16.9 bin/main.ml — 1 行の入口

   実行形のソースは 1 行です。

   ```ocaml
   let () = Diktor.Driver.main ()
   ```

   dune は実行形 (bin/) とライブラリ (lib/) を分けており、実行形は
   `(modules main)` の 1 モジュールだけを持ちます。この分け方で 3 つのことが
   同時に得られます。

   - **ライブラリだけを他の OCaml プログラムから使える。** §16.5 の API が
     意味を持つのはこの分割があるからです。
   - **cram テストが実行形を要求できる。** テストは `%{bin:diktor}` を依存に
     取り、ライブラリのビルドはその依存として自動的に引かれます。
   - **入口が 1 か所に固定される。** リンク単位が明確になります。

   そして最も大事なのは、**ここに何も書かないこと**が設計だという点です。
   引数の前処理でも環境変数の読み取りでも、main.ml に書き始めた瞬間、
   その処理はライブラリの利用者から見えなくなります。テストは
   `Driver.eval_string` を呼び、CLI は main.ml の追加処理つきで動く —
   計画 §8.7 の「CLI とテストが同じ経路を通る」という約束が、
   コンパイルエラーを 1 つも出さずに静かに壊れます。

   > 実行形の main には、ライブラリの関数を 1 つ呼ぶ以上のことを書かない。

   ## 16.10 この章を出るときに持って行くもの

   全 16 章のうち、この章だけはアルゴリズムを 1 つも含みません。それでも
   独立した章に値するのは、**外から見た処理系の振る舞いはここでしか決まらない**
   からです。型推論がどれほど正しくても、存在しないファイルに構文エラーを
   返す処理系は信用されません。

   持ち帰る 3 つ。

   1. **旗はモードを選ぶだけ。** 各モードは既存の関数を並べ替えて呼ぶだけで、
      ドライバ固有の処理を持たない。
   2. **経路を分岐させない。** プレリュードもユーザのファイルも同じ
      `parse_with` に合流し、テストも CLI も同じ `Elab.type_check` を通る。
      それでも §16.5 のように、合流点の**手前**の前処理が揃わない形で
      分岐は忍び込む。合流点を作ったら、そこまでの道も見張ること。
   3. **受け皿を漏らさない。** 例外が 1 つ漏れるたびに、終了コードの表が
      1 行ずつ嘘になっていく。規約の底は catch-all が支え、出力の flush まで
      受け皿の中で済ませる(§16.8)。 *)
