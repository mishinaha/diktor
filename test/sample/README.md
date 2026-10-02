# sample.kel の無改変コピー

- コピー元: 親リポジトリ `keleut` の `doc/sample.kel`(2026-09-12 に旧 `reference/` から `doc/` へ移動し、
  追跡対象になった。移動コミットは親の 2fd2d2e)
- コピー元リビジョン: aaa178f(親の `spec: sample.kel の §8 と §13 を import に合わせる`。
  357 行の後に孤児規則の 1 行を足し、421 行の `Eq[List[_]]` のインスタンスを標準ライブラリの形を示す
  コメントにし、§13 の冒頭の 1 行をファイルの名前空間と import の説明の 7 行に替え、835 行のコメントを
  書き直し、import の TODO を除いて 881 行になった)。その前の 0527b65 は 476-492 行の注釈の読み方と、
  793 行の `sin` の綴り(`@ {}`)、797 行のコメントを書き直し、決着した TODO の 2 行を除いて 874 行に
  なった。33c803f は 726 行のコメントだけを書き換え、d8c872a は 876 行のまま 54 行を置き換えた
  (標準環境の名前を再宣言していた行、`derive structural`、`newtype X = ???`、`Fs` と `__open` などの
  ファイルのプリミティブを除き、ファイルの例を `extern "C"` の `file_open` などで書き直し、
  `extern "C"` の `sin` の型を `[E] … @ E` に書き換えた)
- コピー元 blob: 3f1137878f4b463f099ccdaf53e98fb42eb07b5d(md5: 0ee9df0cc7dcb6baf176a4ce07f5b873)
- 同期手順:

      git -C .. show <親のリビジョン>:doc/sample.kel > test/sample/sample.kel
      chmod 755 test/sample/sample.kel
      dune runtest            # typecheck_sample.t / ast.t / tokens.t が落ちる
      dune promote            # 目視レビューしてから、実装の変更とは別コミットで

  この README のリビジョン・blob・md5 を同じコミットで更新する。
- 無改変であることの検証(親を手元に持っているときの 1 行):

      test "$(git rev-parse HEAD:test/sample/sample.kel)" = "$(git -C .. rev-parse <親のリビジョン>:doc/sample.kel)"

  blob SHA が一致すれば、コピーは 1 バイトも違わない。md5 は git を持たない読み手のための冗長な記録である。
- 本体は決して手で編集しない(計画 260829-1 §9.2)。
- sample.kel が宣言せずに使う名前のスタブは stubs.kel に置く(M9 で整備、260912-1 で追補)。
