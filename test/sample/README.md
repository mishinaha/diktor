# sample.kel の無改変コピー

- コピー元: 親リポジトリ `keleut` の `doc/sample.kel`(2026-09-12 に旧 `reference/` から `doc/` へ移動し、
  追跡対象になった。移動コミットは親の 2fd2d2e)
- コピー元リビジョン: 35fd429(親の `spec: sample.kel を操作名の解決、Neg と Rem、型位置の括弧、案 U、条件式、辞書渡しに合わせて改める`。
  計画 261010-1 の 6 項目に合わせて 33 行を置き換えた。コードの変更は 624 行の `perform File.write` だけで、
  881 行のまま)。その前の 2ff868d は 843 行のコメントだけを書き換えた(881 行のまま)。その前の aaa178f は、357 行の後に孤児規則の 1 行を足し、
  421 行の `Eq[List[_]]` のインスタンスを標準ライブラリの形を示すコメントにし、§13 の冒頭の 1 行を
  ファイルの名前空間と import の説明の 7 行に替え、835 行のコメントを書き直し、import の TODO を除いて
  881 行になった。0527b65 は 476-492 行の注釈の読み方と、
  793 行の `sin` の綴り(`@ {}`)、797 行のコメントを書き直し、決着した TODO の 2 行を除いて 874 行に
  なった。33c803f は 726 行のコメントだけを書き換え、d8c872a は 876 行のまま 54 行を置き換えた
  (標準環境の名前を再宣言していた行、`derive structural`、`newtype X = ???`、`Fs` と `__open` などの
  ファイルのプリミティブを除き、ファイルの例を `extern "C"` の `file_open` などで書き直し、
  `extern "C"` の `sin` の型を `[E] … @ E` に書き換えた)
- コピー元 blob: 18dabb1007e2db9763e80a1cc47c827d940a0192(md5: 1197570abe8651462ba8c55cca6fa319)
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
