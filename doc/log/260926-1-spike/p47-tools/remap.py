#!/usr/bin/env python3
"""sample.kel の行参照を分類し、挿入による付け替えを計算・照合・適用する。
使い方: remap.py <木の根> <旧 sample.kel> <新 sample.kel> <挿入位置 K(この行の後に挿入)> <挿入行数 D> <csv 出力> [--apply]
"""
import re, subprocess, sys, os, csv, collections
root, oldp, newp, K, D, out = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
apply = "--apply" in sys.argv
old = open(oldp, encoding="utf-8").read().split("\n")
new = open(newp, encoding="utf-8").read().split("\n")
if old[-1] == "": old.pop()
if new[-1] == "": new.pop()
files = subprocess.run(["git", "-C", root, "ls-files", "lib", "bin", "test", "README.md", "tools"],
                       capture_output=True, text=True, check=True).stdout.split()
files = [f for f in files if f != "test/sample/sample.kel"]
RA = re.compile(r"sample\.kel:(\d+)(?:-(\d+))?")
RB = re.compile(r"(?<![0-9A-Za-z_./\[\]:])(§\d+)?:(\d+)(?:-(\d+))?")
rows = []
edits = collections.defaultdict(list)  # (file) -> [(ln, start, end, newtext)]
def shift(n): return n + D if n > K else n
for f in sorted(files):
    path = os.path.join(root, f)
    try:
        text = open(path, encoding="utf-8").read()
    except UnicodeDecodeError:
        continue
    for ln, line in enumerate(text.split("\n"), 1):
        hits = []
        for m in RA.finditer(line):
            hits.append(("A", m, m.start(1) - 1, m.end()))  # 置換範囲は ":N(-M)" の部分
        for m in RB.finditer(line):
            hits.append(("B", m, m.start(2) - 1, m.end()))
        hits.sort(key=lambda h: h[2])
        a_positions = [h[1].end() for h in hits if h[0] == "A"]
        for kind, m, s, e in hits:
            if kind == "A":
                a, b = int(m.group(1)), int(m.group(2) or m.group(1))
                form = "sample.kel:N-M" if m.group(2) else "sample.kel:N"
            else:
                a, b = int(m.group(2)), int(m.group(3) or m.group(2))
                prev_a = [p for p in a_positions if p <= m.start()]
                if m.group(1):
                    form = "§N:M"
                elif prev_a:
                    gap = line[prev_a[-1]:m.start()]
                    form = "一覧の2つめ以降(, :N)" if re.fullmatch(r"(, ?:\d+(-\d+)?)*, ?", gap) else "同じ行の二次参照(:N)"
                else:
                    form = "接頭辞のない裸の :N"
                if m.group(3): form += "(範囲)"
            # 場所
            if f.endswith(".t"):
                place = "cram の期待出力" if line.startswith("  ") and not line.startswith("  $") and not line.startswith("  >") else ("cram のコマンド" if line.startswith("  ") else "cram の前書き")
            elif f.endswith((".ml", ".mly")):
                place = "診断文字列" if line[:m.start()].count('"') % 2 == 1 else "コメント"
            elif f.endswith(".kel"):
                place = "コメント"
            else:
                place = "文書"
            if b <= K:
                cls = "512 行以前(不変)"
                na, nb = a, b
            elif a > K:
                cls = "513 行以降(+%d)" % D
                na, nb = a + D, b + D
            else:
                cls = "512 と 513 をまたぐ"
                na, nb = a, b + D
            if a < 1 or b > len(old):
                ok = "範囲外"
            elif cls.startswith("512 と"):
                ok = "要判断"
            else:
                ok = "一致" if old[a-1:b] == new[na-1:nb] else "不一致"
            oldtxt = m.group(0)
            if kind == "A":
                newtxt = "sample.kel:%d" % na + ("-%d" % nb if m.group(2) else "")
            else:
                newtxt = (m.group(1) or "") + ":%d" % na + ("-%d" % nb if m.group(3) else "")
            how = "不変" if (na, nb) == (a, b) else {"cram の期待出力": "promote", "診断文字列": "付け替え(診断文字列)"}.get(place, "付け替え(本文)")
            rows.append(dict(file=f, line=ln, old=oldtxt, new=newtxt, form=form, place=place, cls=cls, check=ok, how=how,
                             old_first=old[a-1].strip()[:60] if 1 <= a <= len(old) else ""))
            if (na, nb) != (a, b) and place != "cram の期待出力":
                repl = line[s:e]
                nr = ":%d" % na + ("-%d" % nb if (m.group(2) if kind == "A" else m.group(3)) else "")
                edits[f].append((ln, s, e, nr))
with open(out, "w", encoding="utf-8", newline="") as fp:
    w = csv.writer(fp)
    w.writerow(["ファイル", "行", "旧", "新", "形", "場所", "区分", "適用", "照合", "旧の行の先頭"])
    for r in rows:
        w.writerow([r["file"], r["line"], r["old"], r["new"], r["form"], r["place"], r["cls"], r["how"], r["check"], r["old_first"]])
print("total", len(rows))
for key in ["cls", "form", "place", "how", "check"]:
    print("--", key); 
    for k, v in collections.Counter(r[key] for r in rows).most_common(): print("  ", v, k)
print("-- shifted by form"); 
for k, v in collections.Counter((r["form"], r["place"]) for r in rows if r["cls"].startswith("513")).most_common(): print("  ", v, k)
print("-- shifted by file")
for k, v in sorted(collections.Counter(r["file"] for r in rows if r["cls"].startswith("513")).items()): print("  ", v, k)
print("edits", sum(len(v) for v in edits.values()), "in", len(edits), "files")
if apply:
    for f, es in edits.items():
        path = os.path.join(root, f)
        lines = open(path, encoding="utf-8").read().split("\n")
        for ln, s, e, nr in sorted(es, key=lambda x: (x[0], -x[1])):
            L = lines[ln-1]
            lines[ln-1] = L[:s] + nr + L[e:]
        open(path, "w", encoding="utf-8").write("\n".join(lines))
    print("applied")
