# 260919-1 のスパイク差分

計画 `doc/log/260919-1-plan.md` の設計時に、diktor(HEAD e9dc352)と親の `doc/sample.kel`(bab469c)の写しの上で取った差分。答え合わせに使い、そのまま適用しない(計画 §11)。ヘッダは `a/` `b/` 形式で、写しの中で `patch -p1` で当たる。

| ファイル | 内容 | 状態 |
|---|---|---|
| `H.patch` | H.4(P20): `lib/parser.mly` のレコード更新の基底を小文字始まりに限る | HEAD の写しで build / runtest 緑 |
| `H-p29-alt.patch` | H.6 の採らなかった案 D(予約語をラベル位置で通す) | build 緑だがセレクタが書けない。記録用 |
| `I.patch` | I.1 / I.4 / I.5 / I.6 / I.7: `lib/elab.ml` と `test/classes.t` | HEAD の写しで緑。J2.patch とは 3 ハンクが衝突する |
| `I-merged.patch` | I.1 の 3 ハンクを J2.4 の上に合成した形(統合スパイク) | combined.patch の一部 |
| `J1.patch` | J1.5(V19): `lib/elab.ml` の `elab_eff` の最後の枝の照合 | HEAD の写しで緑 |
| `J2.patch` | J2.4(V17 / V20)と J2.5(V18): `lib/elab.ml` と `test/kinds.t` | HEAD の写しで緑(fwdrow の 2 行が動く) |
| `K.patch` | K.8(P28)と K.9(P18): `lib/decls.ml` / `lib/elab.ml` / `lib/interp.ml` / `lib/prelude.kel` | HEAD の写しで緑 |
| `K-a.patch` / `K-b.patch` | K.patch を K.8a + K.9 と K.8b(defer)に分けたもの | 統合スパイク |
| `R11.patch` | J1.5 の文言を J2.4 の形に揃えた差分(`I-merged.patch` の後に当てる) | 統合スパイク |
| `combined.patch` | 6 本を積んだ統合スパイクの全差分(I.5 の拒否を除き、K.8b を**含む**、J1.5 の文言を J2.4 に揃えた形。K.8b を外した木は `patch -R -p1 < K-b.patch` で得る) | 統合スパイク。HEAD e9dc352 に `patch -p1 --dry-run` で reject ゼロ |
| `J1-spec.patch` | 親の `doc/sample.kel` への J1 の 13 行 | 親の写し |
| `spec-all.patch` | 親の `doc/sample.kel` への §9 の 27 改訂の統合 | 親の写し。行数と付け替え表は計画 §15 |
| `remap.csv` / `bare_refs.csv` | 行番号参照の付け替え表(系統 1)と裸の行参照の判別表(系統 2) | 計画 §9.4 |
