# Diktor

Diktor は OCaml で書かれた Keleut プログラミング言語のブートストラップインタプリタです。
パース → 型推論 → 木を辿る評価(tree-walking)を実装しており、将来のセルフホスト版 Keleut
コンパイラのテストオラクルとなることを目指しています。

このリポジトリは元々(2018〜2019年)Orphos プログラミング言語のフロントエンドとして
始まり、2026年に Keleut の実装として再出発しました。実装計画は
`doc/log/260829-1-plan.md` を参照してください。

言語仕様は親リポジトリ `keleut` にあります(本リポジトリはその git submodule です):

- `../reference/sample.kel` — 表層構文と言語設計(コメントが仕様)
- `../reference/MiniLang.scala` — 型推論器のリファレンス実装

# 教材として読む(文芸的プログラミング)

ソースコードは `../reference/MiniLang.scala` と同じ文芸的プログラミングの流儀で
書かれています。日本語の散文が主、コードが従で、各ファイルが 1 章に対応します。
実装全体の見取り図は第1章(`lib/syntax.ml`)の冒頭にあります。読む順序:

| 章 | ファイル | 内容 |
|---|---|---|
| 第1章 | `lib/syntax.ml`(+ `aux.ml` / `location.ml`) | 型・カインド・行・AST。全体の見取り図 |
| 第2章 | `lib/lexer.ml` | 字句解析 — 3 層と ASI |
| 第3章 | `lib/parser.mly` | 構文解析と脱糖 |
| 第4章 | `lib/dump.ml` | AST を目で見る(--dump-ast) |
| 第5章 | `lib/tree.ml` | 精緻化木 — 型検査は木への書き込み |
| 第6章 | `lib/decls.ml` | 宣言環境 — 名前の世界 |
| 第7章 | `lib/prims.ml` | 演算子と組み込みエフェクトの表 |
| 第8章 | `lib/unify.ml` | 単一化 — 推論器の心臓部 |
| 第9章 | `lib/show.ml` | 型の表示 |
| 第10章 | `lib/exhaust.ml` | 網羅性検査 (Maranget) |
| 第11章 | `lib/elab.ml` | 型推論の本体 |
| 第12章 | `lib/value.ml` | 実行時の値 |
| 第13章 | `lib/builtin.ml` | プリミティブと組み込み実行環境 |
| 第14章 | `lib/interp.ml` | 評価器 — OCaml 5 のエフェクトで Keleut のエフェクトを写す |
| 第15章 | `lib/prelude.kel` | プレリュード — Keleut 自身で書く最初のページ |
| 第16章 | `lib/driver.ml`(+ `bin/main.ml`) | ドライバと終了コード規約 |

各章は Markdown 記事に変換できます(列 0 の `(* … *)` ブロック、`.kel` は
`//` 行が記事本文になります):

```sh
awk -f tools/weave.awk lib/unify.ml > unify.md
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

# テスト

ゴールデンテストは `test/` 以下にあります。期待出力を変更したときは
`dune promote` でゴールデンファイルを更新し、その更新は実装の変更とは
別のコミットにしてください。

`test/sample/sample.kel` は `../reference/sample.kel` の無改変コピーで、
冒頭コメントに取り込み元のリビジョンを記録しています。同期するときは
ファイルを再コピーし、そのリビジョン注記を更新してください。

# 名前の由来

Diktor という名前は Robert A. Heinlein の小説 _By His Bootstraps_(邦題
『時の門』)の登場人物に由来します。Diktor の目標が他の実装のブートストラップを
助けることだからです。
