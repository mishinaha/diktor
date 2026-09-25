#!/usr/bin/env python3
"""文芸化された Diktor のソースのコメントを検査する。

  python3 tools/litcheck.py [--base REV | --old FILE] [--quiet] [FILE...]

FILE を省くと lib/*.ml、lib/parser.mly、lib/prelude.kel、bin/main.ml を調べる。
コメントだけを編集したつもりの変更を、コミットの前に確かめるための道具である。
ファイルごとに次を調べる。

  code    コメントを除いたコードのトークン列が、REV(既定は HEAD)の同じファイル、
          または --old で渡したファイルと一致するか
  lex     コメントの入れ子が閉じているか。コメントの中に " や {| が無いか
          (OCaml はコメントの中も字句解析するので、これらはビルドを壊しうる)。
          prelude.kel に埋め込みの終端 |prelude} が無いか
  block   列 0 の記事ブロックの継続行が空白 3 個で始まるか(tools/weave.awk の前提)
  width   表の行を除くコメント行が表示幅 120 桁に収まるか
  marker  コメントの本文に、経緯の記述、裁定などの番号、です・ます体、空虚な語が
          残っていないか。「」とバッククォートとコードブロックの中は調べない。
          目安の警告で、終了コードには影響しない

code / lex / block / width のどれかが失敗すると、終了コードは 1 になる。
"""
import argparse
import glob
import os
import re
import subprocess
import sys
import unicodedata

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_FILES = ["lib/*.ml", "lib/parser.mly", "lib/prelude.kel", "bin/main.ml"]
HARD_WIDTH = 120

CHAR_RE = re.compile(
    r"'(?:\\[\\'\"ntbr ]|\\[0-9]{3}|\\x[0-9a-fA-F]{2}|\\o[0-7]{3}|\\u\{[0-9a-fA-F]+\}|[^\\'\n])'"
)
QSTR_OPEN = re.compile(r"\{([a-z_]*)\|")

MARKERS = [
    ("番号", r"(?<![A-Za-z0-9_])(?:[MDVPRGHBACEFJKL]|D-H)[0-9]+[a-z]?(?![A-Za-z0-9_\]\[])"),
    ("計画", r"計画"),
    ("MiniLang", r"MiniLang|お手本"),
    ("経緯", r"かつて|以前は|以前の|当初|最初の実装|修正済み|検証で|で増え|で直し|直した|まで走って|変更前|旧実装|昔の"
             r"|もともと|元々|いまは|今は|v0"),
    ("です・ます", r"です[。、）)]|ます[。、）)]|でした|ました|ません[。、]|ください|でしょう"),
    ("空虚な語", r"心臓部|肝[でだはがを]|見どころ|鉄則|正直|地味|偶然ではない|偶然ではありません|不可欠|核心|掘り下げ"
               r"|において|という観点|重要なのは|正面から|本質的|美学|哲学|宿命|真理|極致"),
    ("ダッシュ", r"—"),
]


def display_width(s):
    return sum(2 if unicodedata.east_asian_width(c) in "WF" else 1 for c in s)


def lex_ocaml(src):
    """OCaml / menhir のソースを字句解析し、(コード, コメントの列, 字句の問題の列) を返す。

    コードはコメントを空白 1 個に置き換えた文字列、コメントの列は (開始行, 本文) である。
    文字列リテラル、引用文字列 {id|…|id}、文字リテラルの中の (* は数えない。
    """
    code = []
    comments = []
    errors = []
    n = len(src)
    pos = 0
    line = 1

    def advance(k):
        nonlocal pos, line
        seg = src[pos:pos + k]
        line += seg.count("\n")
        pos += k
        return seg

    def read_string():
        start = pos
        advance(1)
        while pos < n:
            c = src[pos]
            if c == "\\":
                advance(2)
            elif c == '"':
                advance(1)
                return src[start:pos]
            else:
                advance(1)
        errors.append("閉じていない文字列がある")
        return src[start:pos]

    def read_quoted(m):
        start = pos
        advance(m.end() - m.start())
        close = "|" + m.group(1) + "}"
        j = src.find(close, pos)
        if j < 0:
            errors.append("閉じていない引用文字列 {%s| がある" % m.group(1))
            advance(n - pos)
        else:
            advance(j + len(close) - pos)
        return src[start:pos]

    while pos < n:
        if src.startswith("(*", pos) and not src.startswith("(*)", pos):
            start_line = line
            depth = 0
            body = []
            closed = False
            while pos < n:
                if src.startswith("(*", pos):
                    depth += 1
                    body.append(advance(2))
                elif src.startswith("*)", pos):
                    depth -= 1
                    body.append(advance(2))
                    if depth == 0:
                        closed = True
                        break
                elif src[pos] == '"':
                    errors.append('%d 行: コメントの中に " がある' % line)
                    body.append(read_string())
                elif QSTR_OPEN.match(src, pos):
                    errors.append("%d 行: コメントの中に {| がある" % line)
                    body.append(read_quoted(QSTR_OPEN.match(src, pos)))
                elif src[pos] == "'":
                    m = CHAR_RE.match(src, pos)
                    body.append(advance(m.end() - m.start() if m else 1))
                else:
                    body.append(advance(1))
            if not closed:
                errors.append("%d 行から始まるコメントが閉じていない" % start_line)
            comments.append((start_line, "".join(body)))
            code.append(" ")
            continue
        c = src[pos]
        prev = src[pos - 1] if pos > 0 else " "
        after_ident = prev.isalnum() or prev in "_'"
        if c == '"':
            code.append(read_string())
            continue
        m = QSTR_OPEN.match(src, pos)
        if m and not after_ident:
            code.append(read_quoted(m))
            continue
        if c == "'" and not after_ident:
            m = CHAR_RE.match(src, pos)
            if m:
                code.append(advance(m.end() - m.start()))
                continue
        if src.startswith("*)", pos):
            errors.append("%d 行: コメントの外に *) がある" % line)
        code.append(advance(1))
    return "".join(code), comments, errors


def lex_kel(src):
    """Keleut のソースを行ごとに見て、// から行末までをコメントとして取り出す。"""
    code_lines = []
    comments = []
    errors = []
    for ln, raw in enumerate(src.split("\n"), 1):
        out = []
        j = 0
        in_string = False
        while j < len(raw):
            c = raw[j]
            if in_string:
                out.append(c)
                if c == "\\" and j + 1 < len(raw):
                    out.append(raw[j + 1])
                    j += 2
                    continue
                if c == '"':
                    in_string = False
            elif c == '"':
                in_string = True
                out.append(c)
            elif raw.startswith("//", j):
                comments.append((ln, raw[j:]))
                break
            else:
                out.append(c)
            j += 1
        code_lines.append("".join(out))
    if "|prelude}" in src:
        errors.append("|prelude} がある(埋め込みの終端と衝突する)")
    return "\n".join(code_lines), comments, errors


def nesting_delta(line):
    """行の中の (* と *) を先頭から順に数え、入れ子の深さの増減を返す。"""
    delta = 0
    k = 0
    while k < len(line):
        if line.startswith("(*", k):
            delta += 1
            k += 2
        elif line.startswith("*)", k):
            delta -= 1
            k += 2
        else:
            k += 1
    return delta


def check_blocks(src):
    """列 0 の記事ブロックで、継続行が空白 3 個で始まっていない行を返す。"""
    problems = []
    in_block = False
    depth = 0
    for ln, l in enumerate(src.split("\n"), 1):
        first = False
        if not in_block and l.startswith("(*"):
            in_block = True
            first = True
            depth = 0
        if not in_block:
            continue
        if not first and l.strip() and not l.startswith("   "):
            problems.append(ln)
        depth += nesting_delta(l)
        if depth <= 0:
            in_block = False
    return problems


def comment_lines(comments):
    lines = set()
    for start, body in comments:
        lines.update(range(start, start + body.count("\n") + 1))
    return lines


def check_width(src, comments):
    lines = comment_lines(comments)
    return [ln for ln, l in enumerate(src.split("\n"), 1)
            if ln in lines and not l.lstrip().lstrip("/").lstrip().startswith("|")
            and display_width(l) > HARD_WIDTH]


def check_markers(comments):
    hits = []
    for start, body in comments:
        fence = False
        for off, l in enumerate(body.split("\n")):
            if l.strip().lstrip("/").strip().startswith("```"):
                fence = not fence
                continue
            if fence:
                continue
            text = re.sub(r"「[^」]*」", "「」", l)
            text = re.sub(r"`[^`]*`", "``", text)
            for name, pat in MARKERS:
                for m in re.finditer(pat, text):
                    hits.append((start + off, name, m.group(0), l.strip()))
    return hits


def repo_path(path):
    return os.path.relpath(os.path.abspath(path), ROOT)


def old_source(path, base, old_file):
    if old_file:
        with open(old_file, encoding="utf-8") as f:
            return f.read()
    rel = repo_path(path)
    r = subprocess.run(["git", "-C", ROOT, "show", "%s:%s" % (base, rel)], capture_output=True, text=True)
    if r.returncode != 0:
        return None
    return r.stdout


def check_file(path, base, old_file, quiet):
    name = repo_path(path) if not old_file else path
    with open(path, encoding="utf-8") as f:
        new = f.read()
    old = old_source(path, base, old_file)
    if old is None:
        print("[%s] %s に同じファイルが無い" % (name, base))
        return False
    lex = lex_kel if path.endswith(".kel") else lex_ocaml
    old_code, _, _ = lex(old)
    new_code, comments, lex_errors = lex(new)
    ok = True
    status = []
    details = []

    old_tokens, new_tokens = old_code.split(), new_code.split()
    if old_tokens == new_tokens:
        status.append("code: 一致(%d トークン)" % len(new_tokens))
    else:
        ok = False
        k = 0
        while k < min(len(old_tokens), len(new_tokens)) and old_tokens[k] == new_tokens[k]:
            k += 1
        status.append("code: 不一致(先頭から %d トークン目)" % k)
        details.append("  旧: " + " ".join(old_tokens[max(0, k - 8):k + 8]))
        details.append("  新: " + " ".join(new_tokens[max(0, k - 8):k + 8]))
    if lex_errors:
        ok = False
        status.append("lex: %d 件" % len(lex_errors))
        details.extend("  " + e for e in lex_errors)
    if not path.endswith(".kel"):
        bad = check_blocks(new)
        if bad:
            ok = False
            status.append("block: %d 行" % len(bad))
            details.append("  継続行が空白 3 個で始まっていない行: " + ", ".join(map(str, bad[:20])))
    wide = check_width(new, comments)
    if wide:
        ok = False
        status.append("width: %d 行" % len(wide))
        details.append("  %d 桁を超える行: %s" % (HARD_WIDTH, ", ".join(map(str, wide[:20]))))
    hits = check_markers(comments)
    status.append("marker: %d 件" % len(hits))

    print("[%s] %s" % (name, " / ".join(status)))
    for d in details:
        print(d)
    if not quiet:
        for ln, name, word, l in hits:
            print("  %d: [%s] %s … %s" % (ln, name, word, l[:90]))
    return ok


def main():
    p = argparse.ArgumentParser(description="文芸化された Diktor のソースのコメントを検査する")
    p.add_argument("files", nargs="*", help="検査するファイル(省くと lib と bin の全ソース)")
    g = p.add_mutually_exclusive_group()
    g.add_argument("--base", default="HEAD", help="コードを比べる版(既定は HEAD)")
    g.add_argument("--old", help="コードを比べる元のファイル(1 ファイルの検査で使う)")
    p.add_argument("--quiet", action="store_true", help="marker の個々の報告を省く")
    a = p.parse_args()
    files = a.files or [f for pat in DEFAULT_FILES for f in sorted(glob.glob(os.path.join(ROOT, pat)))]
    if a.old and len(files) != 1:
        p.error("--old は FILE を 1 つだけ渡すときに使う")
    ok = True
    for f in files:
        ok = check_file(f, a.base, a.old, a.quiet) and ok
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
