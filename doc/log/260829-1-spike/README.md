# 260829-1 計画の spike 成果物

260829-1-plan.md の立案時に実施した2本の spike のコード。リポジトリのビルドに巻き込まないよう
`dune` / `dune-project` は `.txt` にリネームしてある。実行するときは一時ディレクトリにコピーして
リネームを戻し、`dune build` すること。

## menhir/ — R1 spike(`{` 3分割文法の conflict 実証)

- `kel.mly` — Keleut 骨格文法。**`menhir --strict --explain` で conflict 0**。
  計画本文の文法スケッチに対する修正箇所に `[FIX-n]` コメントが付いている(計画書 §6 参照)。
- `lex.ml` — `{` 3分割再分類 + ASI を含む手書きレキサ(sedlex 不使用の簡易版)。
- `t/pos.kel` — 計画記載の全構文の正例。
- 実績: `reference/sample.kel` 全文 2526 トークンのパースに成功。

## effect/ — R3 spike(OCaml 5 Effect.Deep でのハンドラ意味論実証)

- `main.ml` — 計画書 §8.4 のプロトコル(Op 効果 / Unwind(inst,v) / discontinue+exnc / one-shot)の
  実装と、sample.kel の capture / try_ / with_file(cancel の LIFO)等 14 テスト。
- `full_run.txt` — 全テストの実行出力。
- 実績: コア主張はすべて再現。節の例外脱出時の discontinue と、活性化ごとの inst 採番が
  必須であることを発見(計画書 §8.4 に反映済み)。
