# sample.kel の無改変コピー

- コピー元: 親リポジトリ `keleut` の `doc/sample.kel`(2026-09-12 に旧 `reference/` から `doc/` へ移動し、
  追跡対象になった。移動コミットは親の 2fd2d2e)
- コピー元リビジョン: 0527b65(親の `spec: 最外の矢印の @ {} も公開の型で開く(§6.3 / §13.2 / §17、sample.kel の 3 回目の改訂)`。
  476-492 行の注釈の読み方と、793 行の `sin` の綴り(`@ {}`)、797 行のコメントを書き直し、
  決着した TODO の 2 行を除いて 874 行になった)。その前の 33c803f は 726 行のコメントだけを書き換え、
  d8c872a は 876 行のまま 54 行を置き換えた(標準環境の名前を再宣言していた行、`derive structural`、
  `newtype X = ???`、`Fs` と `__open` などのファイルのプリミティブを除き、ファイルの例を `extern "C"` の
  `file_open` などで書き直し、`extern "C"` の `sin` の型を `[E] … @ E` に書き換えた)
- コピー元 blob: e57fdc8592d84f237e8fdd2d245ad074e7fd3ac8(md5: c4c7890afc9a46a15367a16567e640a8)
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
