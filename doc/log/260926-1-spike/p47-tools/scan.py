#!/usr/bin/env python3
"""sample.kel の行参照を走査する。引数: 木の根。出力: 候補の一覧(TSV)。"""
import re, subprocess, sys, os
root = sys.argv[1]
files = subprocess.run(["git", "-C", root, "ls-files", "lib", "bin", "test", "README.md", "tools"],
                       capture_output=True, text=True, check=True).stdout.split()
files = [f for f in files if f != "test/sample/sample.kel"]
RA = re.compile(r"sample\.kel:(\d+)(?:-(\d+))?")
RB = re.compile(r"(?<![0-9A-Za-z_./\[\]:])(§\d+)?:(\d+)(?:-(\d+))?")
for f in sorted(files):
    try:
        text = open(os.path.join(root, f), encoding="utf-8").read()
    except UnicodeDecodeError:
        continue
    for ln, line in enumerate(text.split("\n"), 1):
        for m in RA.finditer(line):
            print("\t".join(["A", f, str(ln), str(m.start()), m.group(0), m.group(1), m.group(2) or m.group(1), line.strip()[:160]]))
        for m in RB.finditer(line):
            print("\t".join(["B", f, str(ln), str(m.start()), m.group(0), m.group(2), m.group(3) or m.group(2), line.strip()[:160]]))
