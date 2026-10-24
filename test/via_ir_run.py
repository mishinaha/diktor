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
  作業ディレクトリの絶対パスは $TESTCASE_ROOT に置き換える。
  これらは dune の cram の振る舞いに合わせたものである。
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
    """
    items = []
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("  $ ") or line == "  $":
            start = i + 1
            cmd = [line[4:]]
            i += 1
            while i < len(lines) and (lines[i].startswith("  > ") or lines[i] == "  >"):
                cmd.append(lines[i][4:])
                i += 1
            out = []
            while (
                i < len(lines)
                and lines[i].startswith("  ")
                and not (lines[i].startswith("  $ ") or lines[i] == "  $")
            ):
                out.append(lines[i])
                i += 1
            items.append(("command", start, cmd, out))
        else:
            items.append(("comment", line))
            i += 1
    return items


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
    with open(os.path.join(src_dir, name), encoding="utf-8") as f:
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
                out = out.replace(root, "$TESTCASE_ROOT").replace(tmp, "$TMPDIR")
                if out:
                    # dune の cram と同じく、最後の改行の有無は区別しない
                    out_lines = out.split("\n")
                    if out.endswith("\n"):
                        out_lines.pop()
                    result.extend("  " + l for l in out_lines)
                with open(code_file) as f:
                    code = int(f.read() or "0")
                if code != 0:
                    result.append(f"  [{code}]")
            if result[first:] != expected:
                mismatches.append((line, result[first:]))
            k += 1
        corrected = "\n".join(result) + "\n"
    finally:
        shutil.rmtree(work, ignore_errors=True)
    if corrected == original:
        return name, None, []
    diff = difflib.unified_diff(
        original.splitlines(keepends=True),
        corrected.splitlines(keepends=True),
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
        with open(os.path.join(src_dir, name), encoding="utf-8") as f:
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
