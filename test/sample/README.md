# sample.kel の無改変コピー

- コピー元: 親リポジトリ `keleut` の `doc/sample.kel`(2026-09-12 に旧 `reference/` から `doc/` へ移動し、
  追跡対象になった。移動コミットは親の 2fd2d2e)
- コピー元リビジョン: f4314a1(親の `spec: 入れ子の run と引数の可変配列の扱いを実装に合わせる(§10 / §14.1)`。
  その前の e2ed841 でコメントを平易な日本語に書き直して 846 行から 874 行になり、3f0d904、1cf5791、f4314a1 は
  コメントを数行書き換えただけで行数は変わらない。どれもコメントだけの変更で、コメントを除いたコードは 1 行も変わっていない)
- コピー元 blob: 20d31e9613f71815c5e85687673080ec017e35e4(md5: ebb9d04d8accdf95aa6bb5ef1820e644)
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
