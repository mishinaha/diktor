# 260926-1 のスパイク差分と実測のプログラム

計画 `doc/log/260926-1-plan.md` の設計のときに、diktor(HEAD cb13a13)の写しの上で取った差分と、実測に使ったプログラムである。
答え合わせに使い、そのまま適用しない(計画 §9、§10)。
差分の見出しは `a/` と `b/` の形で、diktor の写しの中で `patch -p1` を使って当てる。
`langspec.patch` だけは親リポジトリ keleut の b4ddf6a に当てる。

## 差分

| ファイル | 内容 | 状態 |
|---|---|---|
| `i1.patch` | V39 の推奨案 B3。`lib/elab.ml` の `elab_handle` で操作節の引数パターンを先に型付け、`Exhaust.missing` で総和性を判定する。コメントと cram(`test/eval.t`、`test/typecheck_m7.t`)を含む | cb13a13 の写しで build と runtest が緑 |
| `i1-b1.patch` | V39 の案 B1(`irrefutable_pat` を名前で広げる) | 採らない。値の無い型の警告が消える |
| `i1-b2.patch` | V39 の案 B2(総和性の検査専用の判定を名前で引く) | 採らない。所有者が別の規則を採るときの代案 |
| `i1-b3-perarg.patch` | V39 の案 B3 で、引数ごとに `missing` を呼ぶ形(コメントは未整備) | 採らない。n7 だけが推奨案と違う |
| `i1-c.patch` | V39 の案 C(節の集まりを `missing` と `useful` に渡す。コメントは未整備) | 採らない。P47 の材料 |
| `i2.patch` | V40。`test/verify_fixes.t` の vr の前書きの書き直しと、vrgen、vrgenv、vrgen2 | cb13a13 のコードで緑 |
| `i2-fix.patch` | V40 と V41 の推奨案 e4。`lib/elab.ml` の `elab_binding`、`lib/unify.ml` の `lower_levels` とその記事、`test/verify_fixes.t`(`lib/elab.ml` と `lib/syntax.ml` のコメントの書き直しは含まない) | cb13a13 の写しで緑 |
| `i2-revert.patch` | 値制限の条件に `annotated` を戻す(元の欠陥の再現) | 検証用。vrgen だけが落ちる |
| `i2-fix-e0.patch`、`i2-fix-e1.patch`、`i2-fix-e2.patch`、`i2-fix-e6.patch` | V41 の案 e0、e1、e2、e6(`i2-fix-e2.patch` は古い版のテストを含む) | 採らない。計画 §4 の (3) |
| `i3.patch` | V42 の推奨案 E。`lib/decls.ml`、`lib/elab.ml`、`test/visibility.t` | cb13a13 の写しで緑 |
| `i3-c.patch` | V42 の案 C | 採らない。cb13a13 で受理され、案 E でも受理のままの 9 本も拒否する(計画 §5 の (3)) |
| `i4.patch` | V43 の推奨案 A。`lib/elab.ml` の `check_resume_static`、コメント 4 ファイル、`test/verify_fixes.t` | cb13a13 の写しで緑 |
| `i4-probe.patch` | 操作節の本体の中の関数束縛を数える計測用のビルド | 検証用 |
| `combined.patch` | `i2-fix.patch`、`i4.patch`、`i3.patch`、`i1.patch` を積んだ統合スパイク | cb13a13 の写しで緑。sample の型検査は 64 行で不変 |
| `langspec.patch` | 親の `doc/LangSpec.md` への §7 の改訂(必須、推奨、任意をすべて含む) | 親の b4ddf6a に `git apply --check` で当たる。1274 行が 1292 行になる |

## 実測のプログラム

| ファイル | 内容 |
|---|---|
| `cases-V39.txt` | V39 の調査と反証に使ったプログラム |
| `cases-V40-V41.txt` | V40 と V41 の調査と反証に使ったプログラム |
| `cases-V42.txt` | V42 の行列(位置 × 書き方 × pub の有無)、追加の調査、反証に使ったプログラム |
| `cases-V43.txt` | V43 の調査と反証に使ったプログラム |

各プログラムは `==== 調査/e14.kel ====` のような見出しの行で区切ってある。
見出しの前半は、調査で書いたか反証で書いたかを表す。
同じ名前で中身が同じものは 1 つにまとめた。
`cases-V39.txt` の e04、e05、e15、e16、e19、e20 は、中身の違う同名のものを「調査/」と「反証/」の両方に残した。
`cases-V43.txt` の d4、d5、d6 と d2 は、計画 §6 の (7) の本文と同じ版である。
計画の本文で `e14` や `leak1` のように名前だけで呼ぶプログラムは、ここにある。
cram のブロックの名前(visrow1、lfresume など)で呼ぶプログラムは、差分の中の cram にある。
