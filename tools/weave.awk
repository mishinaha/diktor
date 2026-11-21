#!/usr/bin/awk -f
# 文芸的プログラミングの形式で書いた Diktor のソースを、Markdown の記事に変換する。
# 文芸的プログラミングで weave と呼ぶ操作で、コードだけを取り出す tangle の逆に当たる。
#
#   awk -f tools/weave.awk lib/unify.ml > unify.md
#
# 入力の形式は次のとおりである。
# - .ml / .mly: 列 0 から始まる (* … *) のブロックコメントが、記事の説明文になる。
#   1 行目は「(* 」で始まり、継続行は空白 3 個で始まり、最後の行は「 *)」で終わる。
#   行頭の「(* 」と空白 3 個、行末の「 *)」は取り除いて出力する。
#   ブロックの中の入れ子の (* … *) は、コード例としてそのまま出力する。
#   それ以外の行は ocaml のコードブロックに入れる。空行はそのまま出力し、空行だけではコードブロックを始めない。
# - .kel: // で始まる行が記事の説明文になる。// とその直後の空白 1 個は取り除く。
#   それ以外の行は、.ml と同じように keleut のコードブロックに入れる。

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
    # ファイルの 1 行目が「(* Copyright」で始まるとき、そのブロックはライセンスの表示なので出力しない
    skipping = (FNR == 1 && $0 ~ /^\(\* Copyright/) ? 1 : 0
  }
  if (inprose) {
    # (* と *) を数えて入れ子の深さを求め、ブロック全体が閉じた行で説明文を終える
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
