#!/usr/bin/env python3
"""文芸化された Diktor のソースの記事ブロックで、長い行を読点の直後で折り返す。

  python3 tools/litwrap.py [--width N] [--hard N] [--check] FILE...

記事ブロックは、.ml / .mly では列 0 から始まる (* … *)、.kel では行頭の // 行である。
記事は一文ごとに改行して書き、このスクリプトで長い文だけを折り返す。

- 表示幅が --width(既定 100 桁、全角 1 字を 2 桁と数える)を超える行は、
  幅に収まる最後の読点の直後で折り返す。
- 読点で折り返せず、行が --hard(既定 120 桁)を超えるときだけ、
  バッククォートと「」の外の半角空白で折り返す。
- 表の行(| で始まる)、見出し、コードブロックの中は折り返さない。
- 箇条書きの続きの行は、項目の本文の位置まで字下げする。

折り返しても --hard を超える行は報告する。
--check を付けると、ファイルを書き換えず、折り返しが必要な行があれば終了コード 1 を返す。
関数の中の字下げされたコメントは対象にしない(手で折り返す)。
"""
import argparse
import re
import sys
import unicodedata

LIST_RE = re.compile(r"^(\s*)([-*] |[0-9]+\. )")


def display_width(s):
    return sum(2 if unicodedata.east_asian_width(c) in "WF" else 1 for c in s)


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


def split_point(line, width, hard):
    """line を折り返す位置(次の行の先頭になる添字)を返す。折り返さないなら None。"""
    comma = None
    comma_hard = None
    space = None
    in_code = False
    quote = 0
    w = 0
    for i, c in enumerate(line):
        w += 2 if unicodedata.east_asian_width(c) in "WF" else 1
        if w > hard:
            break
        if c == "`":
            in_code = not in_code
        elif c == "「":
            quote += 1
        elif c == "」":
            quote = max(0, quote - 1)
        elif c == "、" and not in_code and i + 1 < len(line):
            if w <= width:
                comma = i + 1
            comma_hard = i + 1
        elif c == " " and not in_code and quote == 0 and line[:i].strip():
            space = i
    # 行頭に近すぎる位置で折ると短い行が残るので、幅の 3 分の 1 より後ろを選ぶ
    third = width // 3
    if comma is not None and display_width(line[:comma]) >= third:
        return comma
    if display_width(line) <= hard:
        return None
    for cand in (comma_hard, space):
        if cand is not None and display_width(line[:cand]) >= third:
            return cand
    return comma_hard or space


def wrap(prefix, body, width, hard):
    """記事の 1 行(行頭の prefix と本文 body)を折り返し、行の列を返す。"""
    m = LIST_RE.match(body)
    indent = m.group(1) + " " * len(m.group(2)) if m else re.match(r"^\s*", body).group(0)
    out = []
    rest = body
    while display_width(prefix + rest) > width:
        p = split_point(prefix + rest, width, hard)
        if p is None or p <= len(prefix):
            break
        head, tail = rest[:p - len(prefix)].rstrip(), rest[p - len(prefix):].lstrip()
        if not tail:
            break
        out.append(prefix + head)
        rest = indent + tail
    out.append(prefix + rest)
    return out


def article_lines(path, lines):
    """記事の行を (行番号, 行頭, 本文, 行末) で、それ以外の行を (行番号, None, 行, None) で返す。"""
    kel = path.endswith(".kel")
    in_block = False
    depth = 0
    for ln, l in enumerate(lines, 1):
        if kel:
            m = re.match(r"^//( ?)(.*)$", l)
            if m:
                yield ln, ("// " if m.group(2) else "//"), m.group(2), ""
            else:
                yield ln, None, l, None
            continue
        if not in_block and l.startswith("(*"):
            in_block = True
            depth = 0
        if not in_block:
            yield ln, None, l, None
            continue
        depth += nesting_delta(l)
        ended = depth <= 0
        if ended:
            in_block = False
        if l.startswith("(* ") or l.startswith("   "):
            prefix, body = l[:3], l[3:]
        else:
            yield ln, None, l, None
            continue
        closing = ""
        if ended and body.endswith(" *)"):
            body, closing = body[:-3], " *)"
        yield ln, prefix, body, closing


def process(path, width, hard, check):
    with open(path, encoding="utf-8") as f:
        src = f.read()
    out = []
    over = []
    fence = False
    for ln, prefix, body, closing in article_lines(path, src.split("\n")):
        if prefix is None:
            fence = False if path.endswith(".kel") else fence
            out.append(body)
            continue
        if prefix == "(* ":
            fence = False
        whole = prefix + body + closing
        stripped = body.strip()
        if stripped.startswith("```"):
            fence = not fence
            out.append(whole)
            continue
        if fence or stripped.startswith("|") or stripped.startswith("#") or display_width(whole) <= width:
            if display_width(whole) > hard:
                over.append((ln, "表・見出し・コード", whole))
            out.append(whole)
            continue
        # 記事ブロックの 1 行目は "(* " で始まるので、続きの行は空白 3 個にする
        cont = "   " if prefix == "(* " else prefix
        wrapped = wrap(cont, body + closing, width, hard)
        wrapped[0] = prefix + wrapped[0][len(cont):]
        over.extend((ln, "折り返せない", w) for w in wrapped if display_width(w) > hard)
        out.extend(wrapped)
    new = "\n".join(out)
    for ln, why, l in over:
        print("%s:%d: %s(幅 %d): %s" % (path, ln, why, display_width(l), l.strip()[:60]))
    if check:
        if new != src:
            print("%s: 折り返しが必要な行がある" % path)
        return new == src
    if new != src:
        with open(path, "w", encoding="utf-8") as f:
            f.write(new)
    return True


def main():
    p = argparse.ArgumentParser(description="記事ブロックの長い行を読点の直後で折り返す")
    p.add_argument("files", nargs="+", help="折り返すファイル")
    p.add_argument("--width", type=int, default=100, help="読点で折り返し始める表示幅(既定 100)")
    p.add_argument("--hard", type=int, default=120, help="空白でも折り返す表示幅(既定 120)")
    p.add_argument("--check", action="store_true", help="書き換えずに、折り返しが必要なら終了コード 1 を返す")
    a = p.parse_args()
    ok = True
    for f in a.files:
        ok = process(f, a.width, a.hard, a.check) and ok
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
