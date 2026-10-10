# Diktor

Diktor は OCaml で書かれた Keleut プログラミング言語のブートストラップインタプリタです。
パース → 型推論 → 木を辿る評価(tree-walking)を実装しており、将来のセルフホスト版 Keleut
コンパイラのテストオラクルとなることを目指しています。

このリポジトリは元々(2018〜2019年)Orphos プログラミング言語のフロントエンドとして
始まり、2026年に Keleut の実装として再出発しました。実装計画は
`doc/log/260829-1-plan.md` を参照してください。

言語仕様は親リポジトリ `keleut` にあります(本リポジトリはその git submodule です):

- `../doc/sample.kel` — 表層構文と言語設計(コメントが仕様)
- `../doc/LangSpec.md` — 言語仕様の本文(構文、型規則、評価規則、標準環境)
- `../reference/MiniLang.scala` — 型推論器のリファレンス実装

`lib` と `test` の記事本文が引く `sample.kel:NNN` は、`test/sample/sample.kel`
の行番号です。その取り込み元の版(親のリビジョン、blob SHA、md5)は
`test/sample/README.md` に記録してあります。仕様が改訂されたら
`test/sample/sample.kel` の同期と同時に付け替えます。`doc/log` の過去エントリの
行番号は当時のまま残します(書き換えると記録が読めなくなるため)。

`--dump-ast` の S 式と `--dump-tokens` のトークン列は diktor 固有の診断用の出力で、
仕様は形式を定めていません。`test/ast.t` や `test/tokens.t` などがゴールデンで固定
していますが、実装の都合で変わります。他の実装との読み合わせには使えません。

# 教材として読む(文芸的プログラミング)

ソースコードは `../reference/MiniLang.scala` と同じ文芸的プログラミングの流儀で
書かれています。日本語の散文が主、コードが従で、各ファイルが 1 章に対応します。
実装全体の見取り図は第1章(`lib/syntax.ml`)の冒頭にあります。読む順序:

| 章 | ファイル | 内容 |
|---|---|---|
| 第1章 | `lib/syntax.ml`(+ `aux.ml` / `location.ml`) | 型・カインド・行・AST。全体の見取り図 |
| 第2章 | `lib/lexer.ml` | 字句解析(3 層と ASI) |
| 第3章 | `lib/parser.mly` | 構文解析と脱糖 |
| 第4章 | `lib/dump.ml` | AST を目で見る(--dump-ast) |
| 第5章 | `lib/tree.ml` | 精緻化木(型検査の結果を書き込む木) |
| 第6章 | `lib/decls.ml` | 宣言環境 |
| 第7章 | `lib/prims.ml` | 演算子と組み込みエフェクトの表 |
| 第8章 | `lib/unify.ml` | 単一化 |
| 第9章 | `lib/show.ml` | 型の表示 |
| 第10章 | `lib/exhaust.ml` | 網羅性検査(Maranget) |
| 第11章 | `lib/elab.ml` | 型推論の本体 |
| 第12章 | `lib/value.ml` | 実行時の値 |
| 第13章 | `lib/builtin.ml` | プリミティブと組み込み実行環境 |
| 第14章 | `lib/interp.ml` | 評価器(Keleut のエフェクトを OCaml 5 のエフェクトで写す) |
| 第15章 | `lib/prelude.kel` | プレリュード(Keleut 自身で書いた唯一の章) |
| 第16章 | `lib/driver.ml`(+ `bin/main.ml`) | ドライバと終了コード規約 |

各章は Markdown 記事に変換できます(列 0 の `(* … *)` ブロック、`.kel` は
`//` 行が記事本文になります):

```sh
awk -f tools/weave.awk lib/unify.ml > unify.md
```

コメントを編集したときは、`tools/` の 2 つの Python 3 スクリプトで確かめられます。
記事は一文ごとに改行して書き、長い文は `litwrap.py` で読点の直後で折り返します。
`litcheck.py` は、コメントを除いたコードが HEAD から変わっていないことと、
コメントの字句(`"` や対にならない `(*` を含まないか)と記事ブロックの形式を検査します。

```sh
python3 tools/litwrap.py lib/unify.ml
python3 tools/litcheck.py            # FILE を省くと lib と bin の全ソース
```

規約の詳細(コメントの機械的な形式、コード不変の検証方法)は
`doc/log/260829-3-literate.md` を参照してください。
ocamlformat / `dune fmt` は列 0 ブロックを再インデントして規約を壊すため、
このリポジトリでは掛けないでください。

# ビルド

1. opam をインストールし、OCaml >= 5.2 のスイッチを作成する。
2. `opam install dune menhir sedlex`
3. `dune build`
4. `dune runtest`

# コマンド行

`diktor` を引数なしで実行すると、旗の一覧が表示されます。

ファイルを複数並べると、diktor は書いた順に連結した 1 個のファイルを起点として
扱います。言語仕様(`../doc/LangSpec.md` §15.4)は起点を 1 個のファイルとし、この
連結を定めていません。各ファイルの先頭の import は、連結したファイルの先頭に
集めたものとして扱い、相対パスはその import を書いたファイルの位置を基準にします。
連結したファイルは 1 個のファイルとして型検査するので、ファイルの間でも `pub` の
区別はなく、トップレベルの名前とコンストラクタ名は全体で一意でなければなりません。
連結したファイルのどれかを import すると、import エラーになります。
`test/typecheck_sample.t` は、この連結でスタブ `test/sample/stubs.kel` を
`sample.kel` の前に置きます。

# テスト

ゴールデンテストは `test/` 以下にあります。期待出力を変更したときは
`dune promote` でゴールデンファイルを更新し、その更新は実装の変更とは
別のコミットにしてください。

`test/sample/sample.kel` は `../doc/sample.kel` の無改変コピーです。取り込み元の
リビジョン・blob SHA・md5 は `test/sample/README.md` に記録してあり、同じファイルに
同期手順と、無改変であることを git の blob SHA で検証する 1 行があります。
sample.kel 本体には何も書き足しません。

# 名前の由来

Diktor という名前は Robert A. Heinlein の小説 _By His Bootstraps_(邦題
『時の門』)の登場人物に由来します。Diktor の目標が他の実装のブートストラップを
助けることだからです。
