#!/usr/bin/awk -f
# 文芸化された Diktor のソースを Markdown 記事に変換する(tangle の逆、weave)。
#
#   awk -f tools/weave.awk lib/unify.ml > unify.md
#
# 規約(doc/log/260829-3-literate.md 参照):
# - .ml / .mly: 列 0 から始まる (* … *) ブロックコメントが記事本文。
#   開始行は「(* 」、継続行は空白 3 個、最終行は「 *)」で終わる。
#   それ以外の行はコードフェンスに入る。入れ子の (* … *) はコード例として許す。
# - .kel: 行頭が「// 」の行が記事本文(MiniLang.scala と同じ)。

function flushcode() { if (incode) { print "```"; incode = 0 } }

BEGIN { inprose = 0; incode = 0; depth = 0 }

FNR == 1 { linemode = (FILENAME ~ /\.kel$/) ? 1 : 0 }

linemode == 1 {
  if ($0 ~ /^\/\//) {
    flushcode()
    out = $0
    sub(/^\/\/ ?/, "", out)
    print out
  } else if ($0 ~ /[^ \t]/) {
    if (!incode) { print "```keleut"; incode = 1 }
    print
  } else {
    print ""
  }
  next
}

{
  if (!inprose && $0 ~ /^\(\*/) {
    flushcode()
    inprose = 1
    depth = 0
    # 先頭のライセンスヘッダは記事に載せない
    skipping = (FNR == 1 && $0 ~ /^\(\* Copyright/) ? 1 : 0
  }
  if (inprose) {
    # 入れ子コメントを数え、ブロック全体が閉じたところで本文を終える
    tmp = $0
    while (1) {
      o = index(tmp, "(*"); c = index(tmp, "*)")
      if (o == 0 && c == 0) break
      if (o != 0 && (c == 0 || o < c)) { depth++; tmp = substr(tmp, o + 2) }
      else { depth--; tmp = substr(tmp, c + 2) }
    }
    out = $0
    sub(/^\(\* ?/, "", out)
    sub(/^   /, "", out)
    if (depth == 0) sub(/ ?\*\)[ \t]*$/, "", out)
    if (!skipping) print out
    if (depth == 0) { inprose = 0; skipping = 0 }
    next
  }
  if ($0 ~ /[^ \t]/) {
    if (!incode) { print "```ocaml"; incode = 1 }
    print
  } else {
    print ""
  }
}

END { flushcode() }
