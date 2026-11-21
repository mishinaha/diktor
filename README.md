# Diktor

Diktor は、OCaml で書いた Keleut プログラミング言語の参照インタプリタです。
字句解析、構文解析、型推論と、構文木を直接たどる評価器を実装しています。
Keleut の主な実装である RustKeleut のテストオラクル(差分テストで結果を比べる基準)と、中間言語 KIR の参照実装を兼ねます。

このリポジトリは、2018〜2019 年に Orphos プログラミング言語のフロントエンドとして始まり、2026 年に Keleut の実装として再出発しました。
設計と実装の記録は `doc/log/` にあります。

言語仕様は親リポジトリ `keleut` にあります。
このリポジトリは、その親リポジトリの git submodule です。

- `../doc/sample.kel` — 表層構文と言語設計(コメントが仕様)
- `../doc/LangSpec.md` — 言語仕様の本文(構文、型規則、評価規則、標準環境)
- `../reference/MiniLang.scala` — 型推論器の参照実装(親リポジトリの追跡対象ではないので、クローンしただけでは手に入りません)

`lib` のコメントと `test` の説明の行が参照する `sample.kel:NNN` は、`test/sample/sample.kel` の行番号です。
このファイルの取り込み元の版(親のリビジョン、blob SHA、md5)は、`test/sample/README.md` に記録してあります。
仕様を改訂したときは、`test/sample/sample.kel` を同期するのと同じ変更で、これらの行番号も更新します。
`doc/log` の過去の記録にある行番号は、当時のまま残します。
書き換えると、その記録が当時のどの行を指していたのかを読み取れなくなるからです。

`--dump-ast` の S 式と `--dump-tokens` のトークン列は診断用の出力で、仕様は形式を定めていません。
形式は、`test/ast.t` や `test/tokens.t` などのゴールデンテスト(期待出力との比較)で固定しています。
RustKeleut の `keleut dump ast` と `keleut dump tokens` も同じ形式で出力するので、この 2 つの出力を差分テストに使います。
形式を変えるときは、RustKeleut も同時に変更します。

# 教材として読む(文芸的プログラミング)

ソースコードは、`../reference/MiniLang.scala` と同じ文芸的プログラミングの形式で書いてあります。
日本語の説明文が主で、コードが従です。
各ファイルが 1 章に対応します。
実装全体の構成は、第1章(`lib/syntax.ml`)の冒頭に書いてあります。
次の表の順に読みます。

| 章 | ファイル | 内容 |
|---|---|---|
| 第1章 | `lib/syntax.ml`(+ `aux.ml` / `location.ml`) | 型、カインド、行、AST。全体の構成 |
| 第2章 | `lib/lexer.ml` | 字句解析(3 層と ASI) |
| 第3章 | `lib/parser.mly` | 構文解析と脱糖 |
| 第4章 | `lib/dump.ml` | AST を目で見る(`--dump-ast`) |
| 第5章 | `lib/tree.ml` | 精緻化木(型検査の結果を書き込む木) |
| 第6章 | `lib/decls.ml` | 宣言環境 |
| 第7章 | `lib/prims.ml` | 演算子と組み込みエフェクトの表 |
| 第8章 | `lib/unify.ml` | 単一化 |
| 第9章 | `lib/show.ml` | 型の表示 |
| 第10章 | `lib/exhaust.ml` | 網羅性検査(Maranget) |
| 第11章 | `lib/elab.ml` | 型推論の本体 |
| 第12章 | `lib/value.ml` | 実行時の値 |
| 第13章 | `lib/builtin.ml` | プリミティブと組み込み実行環境 |
| 第14章 | `lib/interp.ml` | 評価器(Keleut のエフェクトを OCaml 5 のエフェクトで実現する) |
| 第15章 | `lib/prelude.kel` | プレリュード(Keleut で書いた唯一の章) |
| 第16章 | `lib/driver.ml`(+ `bin/main.ml`) | ドライバと終了コード規約 |
| 第17章 | `lib/ir.ml` | KIR の型 |
| 第18章 | `lib/ir_write.ml` | 精緻化木から KIR への書き出し |
| 第19章 | `lib/ir_text.ml` | KIR の正準なテキスト |
| 第20章 | `lib/ir_bin.ml` | KIR のバイナリ |
| 第21章 | `lib/ir_check.ml` | KIR の検証 |
| 第22章 | `lib/ir_eval.ml` | KIR の評価器 |

表の「脱糖」は糖衣構文の展開を、「正準なテキスト」は一意に決まるテキスト表現(canonical)を指します。

各章は Markdown の記事に変換できます。
`.ml` と `.mly` では列 0 から始まる `(* … *)` のブロックが、`.kel` では `//` で始まる行が、記事の説明文になります。
それ以外の行はコードブロックに入ります。

```sh
awk -f tools/weave.awk lib/unify.ml > unify.md
```

コメントを編集したときは、`tools/` にある 2 つの Python 3 スクリプトで、折り返しと形式の検査を行います。
説明のブロックは一文ごとに改行して書き、長い文は `litwrap.py` で読点の直後で折り返します。
`litcheck.py` は、次の 4 点を検査します。

- コメントを取り除いたコードが HEAD から変わっていないこと
- コメントの中に `"` と `{|` がなく、コメントの入れ子が閉じていること
- 説明のブロックの継続行が空白 3 個で始まること
- 表の行を除くコメントの行が表示幅 120 桁に収まること

このほかに、経緯の記述や番号などがコメントに残っていると警告します。
警告は終了コードに影響しません。

```sh
python3 tools/litwrap.py lib/unify.ml
python3 tools/litcheck.py            # FILE を省くと lib と bin の全ソース
```

規約の詳細(コメントの形式と、コードが変わっていないことの検証方法)は、`doc/log/260829-3-literate.md` を参照してください。
ocamlformat と `dune fmt` は、列 0 のブロックのインデントを変えて規約を壊すので、このリポジトリでは実行しないでください。

# ビルド

1. opam をインストールし、OCaml >= 5.2 のスイッチを作成します。
2. `opam install dune menhir sedlex`
3. `dune build`
4. `dune runtest`

# コマンド行

`diktor` を引数なしで実行すると、使い方のエラー(終了コード 64)になり、オプションの一覧を標準エラーに表示します。

コマンド行にファイルを複数並べると、Diktor は、書いた順に連結した 1 個のファイルを起点(コマンド行で渡したファイル)として扱います。
言語仕様(`../doc/LangSpec.md` §15.4)は起点を 1 個のファイルとしていて、この連結を定めていません。
連結は Diktor が独自に決めた動作です。

- 各ファイルの先頭の import は、連結したファイルの先頭に集めたものとして扱い、相対パスは、その import を書いたファイルの位置を基準にします。
- 連結したファイルは 1 個のファイルとして型検査するので、ファイルの間でも `pub` の区別はなく、型、コンストラクタ、エフェクトの名前は全体で一意でなければなりません。
- トップレベルの値は、同じファイルの中と同じく、後の宣言が前の宣言を隠します(シャドーイング)。
- 連結したファイルのどれかを import すると、import エラーになります。

`test/typecheck_sample.t` は、この連結を使って、スタブ `test/sample/stubs.kel` を `sample.kel` の前に置きます。

# テスト

ゴールデンテストは `test/` の下にあります。
期待出力を変更したときは、`dune promote` でゴールデンファイルを更新します。
その更新は、実装の変更とは別のコミットにしてください。

`test/sample/sample.kel` は、`../doc/sample.kel` を変更せずにコピーしたものです。
取り込み元のリビジョン、blob SHA、md5 は `test/sample/README.md` に記録してあります。
同じファイルに、同期の手順と、コピーが元と一致することを git の blob SHA で検証するコマンドも書いてあります。
`test/sample/sample.kel` は手で編集しません。

# 名前の由来

Diktor という名前は、Robert A. Heinlein の小説 _By His Bootstraps_(邦題『時の門』)の登場人物に由来します。
ほかの実装のブートストラップを助けることが、Diktor の目標だからです。
