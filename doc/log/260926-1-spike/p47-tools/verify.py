import re, subprocess, sys, os
def refs(root, sample):
    S = open(sample, encoding="utf-8").read().split("\n")
    files = subprocess.run(["git","-C",root,"ls-files","lib","bin","test","README.md","tools"],capture_output=True,text=True).stdout.split()
    RA = re.compile(r"sample\.kel:(\d+)(?:-(\d+))?")
    RB = re.compile(r"(?<![0-9A-Za-z_./\[\]:])(§\d+)?:(\d+)(?:-(\d+))?")
    out = []
    for f in sorted(files):
        if f == "test/sample/sample.kel": continue
        try: t = open(os.path.join(root,f),encoding="utf-8").read()
        except UnicodeDecodeError: continue
        for ln, line in enumerate(t.split("\n"),1):
            hs=[]
            for m in RA.finditer(line): hs.append((m.start(), int(m.group(1)), int(m.group(2) or m.group(1))))
            for m in RB.finditer(line): hs.append((m.start(), int(m.group(2)), int(m.group(3) or m.group(2))))
            for s,a,b in sorted(hs): out.append((f, ln, tuple(S[a-1:b])))
    return out
A = refs(sys.argv[1], sys.argv[2]); B = refs(sys.argv[3], sys.argv[4])
print(len(A), len(B), "same" if A == B else "DIFF")
for x, y in zip(A, B):
    if x != y: print("mismatch", x[:2], y[:2])
