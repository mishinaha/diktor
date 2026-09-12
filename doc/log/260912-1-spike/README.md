# 260912-1 のスパイク差分

計画 `doc/log/260912-1-plan.md` の設計調査(2026-09-12)で、diktor(HEAD 3ed3353)の写しに実装して `dune runtest` まで通した差分。基準は HEAD の `lib/` と `test/`。ヘッダは `a/`(HEAD)と `b/`(写し)の形式で、HEAD の写しの中で `patch -p1` で当たる(5 本とも `--dry-run` で reject ゼロを確認済み)。

| ファイル | ワークストリーム | 触るもの | 備考 |
|---|---|---|---|
| `A.patch` | A 配列の分離(§3、M24) | `lib/decls.ml` / `lib/value.ml` / `lib/interp.ml`、`test/region.t`(新設)/ `eval.t` / `parallel.t` / `spec_gaps.t` | 全 21 本の cram が緑。計画の `region.t` にはこの差分に無い 3 ブロック(publen / pubget / parget)がある |
| `B.patch` | B 注釈した行の読み方(§4、M26) | `lib/elab.ml` / `lib/decls.ml`、`test/typecheck_m6.t` / `parallel.t` / `verify_fixes.t` / `sample/sample.kel` / `ast.t` / `tokens.t` | **B4(newtype のカインド推論)を含むが、計画は C の設計(`C.patch`)に置き換えた**。新規 cram `test/annot_rows.t` は含まれていない(期待出力は計画 §4 の本文が正)。`sample/sample.kel` への `@ {}` 追加は M25 の同期で入る |
| `C.patch` | C カインド推論(§5、M23 と M28) | `lib/elab.ml` / `lib/decls.ml`、`test/typecheck_m21c.t`(新設。計画では `kinds.t` に改名) | C1〜C7 全部入り。M23 は C1〜C4、M28 は C5〜C7 |
| `D.patch` | D `Fs` とランタイム提供エフェクト(§6、M21 の D-c と M27) | `lib/prelude.kel` / `lib/prims.ml` / `lib/elab.ml`、`test/fs_effect.t` / `blocking_top.t`(新設) | 名簿の名前は `toplevel_only_effects`(計画は `toplevel_effects`)。`typecheck_sample.t` の旧写しが落ちる状態のまま(M25 の同期が前提) |
| `E.patch` | E 前提つきインスタンス(§7、M22) | `lib/parser.mly` / `lib/syntax.ml` / `lib/dump.ml` / `lib/elab.ml`、`test/premise.t`(新設) | 既存 20 本のゴールデン不変。E2(スーパークラスの文言 `elab.ml:2401`)は含まれていない(M21 の F-C3) |

使い方の注意:

- 答え合わせに使い、そのまま適用して済ませない。B と C は `elab_type` の同じ枝(`EApply`)を触り、B4 の分は C に負ける。各パッチの文芸化本文の更新は計画の「文芸化本文の更新」節が正で、パッチ側は最小限しか書いていない。
- パッチ内の `.t` の期待出力は写しで `dune promote` した実測。本実装後に改めて promote し、目視する(260829-4 §16 の規律)。
- 写し自体(ビルド済みバイナリと実測に使った `.kel`)はセッションの一時領域にあり、保存していない。計画本文の `<scratchpad>` はその領域を指す。
