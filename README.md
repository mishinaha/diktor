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
