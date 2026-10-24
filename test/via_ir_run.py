#!/usr/bin/env python3
# Copyright (C) 2019 Takezoe,Tomoaki <tomoaki3478@res.ac>
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
"""cram の試験を、KIR の経路(DIKTOR_VIA_IR=1)で走らせ直す。

test/dune の別名 runtest-via-ir が呼ぶ。
dune の cram は、.t のファイルを単位にしか除外できず、規則が作った .t も走らせない。
そこで、dune の cram と同じ形のシェルスクリプトを本スクリプトが組み、
期待値との差を unified diff で印字する。

- 各 .t は、sample/ の写しだけを置いた空のディレクトリで、1 本の sh として走る。
  コマンドの出力は 2>&1 で 1 本にし、0 でない終了状態は [N] の行にする。
  出力からは、端末の色の指定(ESC から次の m まで)と、
  シェルの誤りの文面の頭に付くスクリプトの位置を除く。
  作業ディレクトリの絶対パスは $TESTCASE_ROOT に置き換える。
  出力は LF で行に切り、LF の直前の CR を 1 つ落とす。
  これらは dune の cram の振る舞いに合わせたものである。
- .t の読み方も dune の cram に合わせる。
  コマンドの始まりは `  $ ` で始まる行だけで、`  $` だけの行は出力の行である。
  コマンドに続かない出力の行は、読んで捨てる。
- 環境変数 DIKTOR_VIA_IR を 1 にして走らせる。
  除外の一覧(via-ir-exclude.txt)に載ったコマンドだけは、その前後で 0 に戻す。
  除外したコマンドも走らせ、期待値と比べる。
  後のコマンドが、除外したコマンドの作ったファイルを使うことがあるからである。

除外の一覧の各行は「ファイル名:行番号 理由」で、行番号は .t の中の `  $ ` の行である。
# から行末までは注釈である。
一覧の行が .t のコマンドの行を指していなければ、誤りにする。

終了状態は、差が無ければ 0、差があれば 1、使い方の誤りなら 2 である。

本スクリプトを手で走らせるときは、diktor/_build/default/test を作業ディレクトリにする。
--tree は DIKTOR_VIA_IR=0 で走らせ、本スクリプトが dune の cram と同じ結果を出すことを確かめる。
--list は、差のあるコマンドを「ファイル名:行番号」と出力で 1 行ずつ印字する(除外の一覧を作るときに使う)。
"""

import argparse
import concurrent.futures
import difflib
import os
import re
import shutil
import subprocess
import sys
import tempfile


def parse_cram(text):
    """.t の行を、注釈、コマンド、期待の出力に分ける。

    戻り値は項目の列で、各項目は ("comment", 行) か ("command", 行番号, 行の列, 期待の出力の列) である。

    読み方は dune の cram の字句解析器(cram_lexer.mll)と同じで、行ごとに 3 つの状態を移る。
    初めの状態では、`  $ ` で始まる行がコマンドの始まりで、
    `  > ` で始まる行と `  >` だけの行が続きの行である。
    コマンドを読むと、初めの状態に戻る。
    初めの状態で 2 つの空白で始まるほかの行を読むと、出力の状態に移る。
    `  $` だけの行も、2 つの空白で始まるので出力の行になる。
    初めの状態のそのほかの行は注釈で、注釈の状態に移る。
    コマンドの直後の `  > ` で始まる行はコマンドの続きになるので、
    初めの状態で注釈になるのは、コマンドに続かない `  > ` の行である。

    注釈の状態では、2 つの空白で始まらない行がすべて注釈である。
    2 つの空白で始まる行で、初めの状態に戻る。
    そのため、コマンドの直後の空白 1 つだけの行は注釈になり、
    その後に続く `  $ ` の行は、新しいコマンドになる。

    出力の状態では、2 つの空白で始まる行が出力の行である。
    コマンドの直後から続く出力の行だけが、そのコマンドの期待の出力になる。
    注釈の後の出力の行は、どのコマンドにも付かないので、読んで捨てる。
    捨てた行は、走らせた後の .t に現れないので、期待値との差になる。
    出力の状態の空白 1 つだけの行は、取っておく。
    次に `  $ ` の行が来れば、取っておいた行は捨てる。
    ファイルが終わるか、ほかの行が来れば、取っておいた行は注釈になる。
    空白 1 つで始まりほかの文字が続く行は注釈で、取っておいた行とともに注釈の状態に移る。
    """
    items = []
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    state = "block"
    cur = None
    pending = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if state == "output":
            if line.startswith("  $ "):
                pending = []
                state = "block"
                continue
            if line == " ":
                pending.append(line)
                i += 1
                continue
            if line.startswith("  "):
                if cur is not None:
                    cur.append(line)
                i += 1
                continue
            items.extend(("comment", c) for c in pending)
            if pending:
                cur = None
                state = "comment"
            else:
                state = "block"
            pending = []
            if line.startswith(" "):
                items.append(("comment", line))
                cur = None
                state = "comment"
                i += 1
            continue
        if state == "comment":
            if line.startswith("  "):
                state = "block"
                continue
            items.append(("comment", line))
            i += 1
            continue
        if line.startswith("  $ "):
            start = i + 1
            cmd = [line[4:]]
            i += 1
            while i < len(lines) and (lines[i].startswith("  > ") or lines[i] == "  >"):
                cmd.append(lines[i][4:])
                i += 1
            cur = []
            items.append(("command", start, cmd, cur))
        elif line.startswith("  ") and not (line.startswith("  > ") or line == "  >"):
            if cur is not None:
                cur.append(line)
            state = "output"
            i += 1
        else:
            items.append(("comment", line))
            cur = None
            state = "comment"
            i += 1
    items.extend(("comment", c) for c in pending)
    return items


def split_lines(s):
    """dune の Stdune の split_lines と同じく、出力を行に切る。

    LF で切り、LF の直前の CR を 1 つ落とす。
    LF の無い最後の部分は、空か CR 1 つだけなら捨て、ほかは CR を含めてそのまま残す。
    """
    parts = s.split("\n")
    last = parts.pop()
    lines = [p[:-1] if p.endswith("\r") else p for p in parts]
    if last not in ("", "\r"):
        lines.append(last)
    return lines


def lf_lines(s):
    """改行を残したまま、s を LF だけで行に切る。

    str.splitlines は CR でも切るので、CR を含む行の差を正しく印字できない。
    """
    parts = s.split("\n")
    lines = [p + "\n" for p in parts[:-1]]
    if parts[-1]:
        lines.append(parts[-1])
    return lines


ANSI_RE = re.compile(r"\x1b[^m]*(?:m|\Z)")


def sanitize(out, main, cmd_file, root, tmp):
    """コマンドの出力を、dune の cram の sanitize と同じ順に整える。

    端末の色の指定を除き、作業ディレクトリと TMPDIR の絶対パスを置き換え、
    行の頭のスクリプトの位置を除く。
    スクリプトの位置は、dash が `.` で読んだスクリプトの誤りに付ける
    「<親のスクリプト>: N: <コマンドのスクリプト>: 」と、
    bash の付ける「<コマンドのスクリプト>: line N: 」である。
    スクリプトは作業ディレクトリの外に置くので、パスの置き換えはスクリプトの位置に当たらない。
    """
    out = ANSI_RE.sub("", out)
    out = out.replace(root, "$TESTCASE_ROOT").replace(tmp, "$TMPDIR")
    line_no = r"[1-9][0-9]*"
    prefix = re.compile(
        "^(?:"
        + re.escape(main) + ": " + line_no + ": " + re.escape(cmd_file) + ": "
        + "|"
        + re.escape(cmd_file) + ": line " + line_no + ": "
        + ")",
        re.M,
    )
    return prefix.sub("", out)


def load_excludes(path):
    """除外の一覧を {(ファイル名, 行番号): 理由} に読む。"""
    excludes = {}
    with open(path, encoding="utf-8") as f:
        for n, raw in enumerate(f, 1):
            line = raw.split("#", 1)[0].strip()
            if not line:
                continue
            m = re.fullmatch(r"([^:\s]+\.t):(\d+)\s+(\S.*)", line)
            if not m:
                sys.exit(f"{path}:{n}: 「ファイル名:行番号 理由」の形ではありません: {raw.rstrip()}")
            key = (m.group(1), int(m.group(2)))
            if key in excludes:
                sys.exit(f"{path}:{n}: 同じコマンドが 2 度載っています: {m.group(1)}:{m.group(2)}")
            excludes[key] = m.group(3)
    return excludes


def run_one(name, src_dir, bin_dir, excluded_lines, via_ir):
    with open(os.path.join(src_dir, name), encoding="utf-8", newline="") as f:
        original = f.read()
    items = parse_cram(original)
    commands = [it for it in items if it[0] == "command"]
    work = tempfile.mkdtemp(prefix="via_ir_")
    try:
        root = os.path.join(work, "root")
        meta = os.path.join(work, "meta")
        tmp = os.path.join(work, "tmp")
        os.makedirs(root)
        os.makedirs(meta)
        os.makedirs(tmp)
        sample = os.path.join(src_dir, "sample")
        if os.path.isdir(sample):
            os.makedirs(os.path.join(root, "sample"))
            for e in os.listdir(sample):
                if e.endswith(".kel"):
                    shutil.copy(os.path.join(sample, e), os.path.join(root, "sample", e))
        script = ["trap 'exit 0' EXIT"]
        for k, (_, line, cmd, _) in enumerate(commands):
            cmd_file = os.path.join(meta, f"{k}.sh")
            with open(cmd_file, "w", encoding="utf-8") as f:
                f.write("\n".join(cmd) + "\n")
            out_file = os.path.join(meta, f"{k}.output")
            code_file = os.path.join(meta, f"{k}.code")
            if via_ir and line in excluded_lines:
                script.append("DIKTOR_VIA_IR=0; export DIKTOR_VIA_IR")
            script.append(f". '{cmd_file}' > '{out_file}' 2>&1")
            script.append(f"printf '%d' $? > '{code_file}'")
            if via_ir and line in excluded_lines:
                script.append("DIKTOR_VIA_IR=1; export DIKTOR_VIA_IR")
        main = os.path.join(meta, "main.sh")
        with open(main, "w", encoding="utf-8") as f:
            f.write("\n".join(script) + "\n")
        env = dict(os.environ)
        env.pop("TESTDIR", None)
        env["PATH"] = bin_dir + os.pathsep + env.get("PATH", "")
        env["LC_ALL"] = "C"
        env["TMPDIR"] = tmp
        env["DIKTOR_VIA_IR"] = "1" if via_ir else "0"
        subprocess.run(["sh", main], cwd=root, env=env, stdin=subprocess.DEVNULL, check=False)
        result = []
        mismatches = []
        k = 0
        for it in items:
            if it[0] == "comment":
                result.append(it[1])
                continue
            _, line, cmd, expected = it
            result.append("  $ " + cmd[0])
            result.extend("  > " + c for c in cmd[1:])
            first = len(result)
            code_file = os.path.join(meta, f"{k}.code")
            if not os.path.exists(code_file):
                result.append("  ***** UNREACHABLE *****")
            else:
                with open(os.path.join(meta, f"{k}.output"), "rb") as f:
                    out = f.read().decode("utf-8", errors="surrogateescape")
                out = sanitize(out, main, os.path.join(meta, f"{k}.sh"), root, tmp)
                # dune の cram と同じく、最後の改行の有無は区別しない
                result.extend("  " + l for l in split_lines(out))
                with open(code_file) as f:
                    code = int(f.read() or "0")
                if code != 0:
                    result.append(f"  [{code}]")
            if result[first:] != expected:
                mismatches.append((line, result[first:]))
            k += 1
        corrected = "".join(r + "\n" for r in result)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    if corrected == original:
        return name, None, []
    diff = difflib.unified_diff(
        lf_lines(original),
        lf_lines(corrected),
        fromfile=f"a/{name}",
        tofile=f"b/{name}.corrected",
    )
    return name, "".join(diff), mismatches


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--diktor", required=True, help="diktor の実行形")
    ap.add_argument("--exclude", required=True, help="除外の一覧")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--tree", action="store_true", help="DIKTOR_VIA_IR=0 で走らせる(本スクリプト自身の検査)")
    ap.add_argument("--list", action="store_true", help="差のあるコマンドを「ファイル名:行番号」で 1 行ずつ印字する")
    ap.add_argument("tests", nargs="*", help="試験のファイル。省くと作業ディレクトリの *.t のすべて")
    args = ap.parse_args()
    bin_dir = os.path.dirname(os.path.abspath(args.diktor))
    if os.path.basename(args.diktor) != "diktor":
        sys.exit("--diktor には diktor という名前の実行形を渡してください")
    tests = args.tests or sorted(e for e in os.listdir(".") if e.endswith(".t") and not e.startswith(".") and os.path.isfile(e))
    src_dir = os.path.dirname(os.path.abspath(tests[0]))
    names = sorted(os.path.basename(t) for t in tests)
    excludes = load_excludes(args.exclude)
    by_file = {}
    for (name, line), _ in excludes.items():
        by_file.setdefault(name, set()).add(line)
    bad = False
    for name, lines in sorted(by_file.items()):
        if name not in names:
            print(f"{args.exclude}: 試験にないファイルです: {name}", file=sys.stderr)
            bad = True
            continue
        with open(os.path.join(src_dir, name), encoding="utf-8", newline="") as f:
            starts = {it[1] for it in parse_cram(f.read()) if it[0] == "command"}
        for line in sorted(lines - starts):
            print(f"{args.exclude}: {name}:{line} はコマンドの行ではありません", file=sys.stderr)
            bad = True
    if bad:
        return 2
    failed = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futures = [ex.submit(run_one, n, src_dir, bin_dir, by_file.get(n, set()), not args.tree) for n in names]
        for fut in futures:
            name, diff, mismatches = fut.result()
            if diff:
                failed.append(name)
                if args.list:
                    for line, got in mismatches:
                        print(f"{name}:{line}\t" + " | ".join(g.strip() for g in got))
                else:
                    sys.stdout.write(diff)
    if failed:
        print(f"via-ir: {len(failed)} 個の試験に差があります: {' '.join(failed)}", file=sys.stderr)
        return 1
    print(f"via-ir: {len(names)} 個の試験に差はありません(除外 {len(excludes)} 個のコマンド)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
