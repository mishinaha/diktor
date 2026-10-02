# sample.kel の無改変コピー

- コピー元: 親リポジトリ `keleut` の `doc/sample.kel`(2026-09-12 に旧 `reference/` から `doc/` へ移動し、
  追跡対象になった。移動コミットは親の 2fd2d2e)
- コピー元リビジョン: d8c872a(親の `spec: sample.kel を削除、Blocking 既定、末尾ブロックに合わせて改訂する`。
  876 行のまま 54 行を置き換えた。コメントのほかに、標準環境の名前を再宣言していた行、`derive structural`、
  `newtype X = ???`、`Fs` と `__open` などのファイルのプリミティブを除き、ファイルの例を `extern "C"` の
  `file_open` などで書き直し、`extern "C"` の `sin` の型を `[E] … @ E` に書き換えた)
- コピー元 blob: 41f6883fbdb342c64597d7ade54b592c46b0a244(md5: 9326fd9bf55f0a0a46383dd21c296135)
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
