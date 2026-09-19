# sample.kel の無改変コピー

- コピー元: 親リポジトリ `keleut` の `doc/sample.kel`(2026-09-12 に旧 `reference/` から `doc/` へ移動し、
  追跡対象になった。移動コミットは親の 2fd2d2e)
- コピー元リビジョン: 8b64d4f(親の `spec: Float64 の文字列化の最短、EffectRow の名前の位置、識別子の大小、BOM、{ の 3 文脈を書く(§2 / §1 / §0)`。
  計画 260919-1 の M32 が入れた `spec:` コミット 10 本(0a5b239〜8b64d4f)の最後。bab469c の 776 行から 846 行になった。
  増えた 70 行はすべてコメント行で、実行される Keleut のコードは 1 行も変わっていない)
- コピー元 blob: b0a00b871c5913a15b983c41fcb9548115b258aa(md5: f42f41a166b866a871e3837f0cf4fa93)
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
