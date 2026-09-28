#!/usr/bin/env bash
# Regenerate every generated row table of ArithS/Necessitation and diff it against the tracked file.
# Exit 0 iff every generated file is byte-identical to what is checked in. Never runs lake.
# Usage: arith/scripts/regen_all.sh            (from anywhere; restores the tree afterwards)
set -u
cd "$(dirname "$0")/.." || exit 2
if [ -n "$(git status --porcelain -- ArithS)" ]; then echo "ArithS has uncommitted changes; commit or stash first" >&2; exit 2; fi
TMP=$(mktemp -d); trap 'rm -rf "$TMP"; git checkout -q -- ArithS' EXIT
fail=0
check() { # $1 = tracked path, $2 = freshly generated path
  if cmp -s "$1" "$2"; then printf "  ok      %s\n" "$1"; else printf "  DIFFERS %s (%s lines)\n" "$1" "$(diff "$1" "$2" | grep -c '^[<>]')"; fail=1; fi; }
# in-place writers: run, compare against HEAD, restore
for g in gen_cert gen_frag1 gen_frag2 gen_indrec gen_numid gen_proaxm gen_prologue; do
  python3 "scripts/$g.py" >/dev/null 2>&1 || { echo "  ERROR   $g failed" >&2; fail=1; continue; }
done
for f in CertRows Frag1Rows Frag2Rows IndRecRows NumIdRows ProAxmRows PrologueRows; do
  git show "HEAD:arith/ArithS/Necessitation/$f.lean" > "$TMP/$f.lean" 2>/dev/null || git show "HEAD:ArithS/Necessitation/$f.lean" > "$TMP/$f.lean"
  check "$TMP/$f.lean" "ArithS/Necessitation/$f.lean" | sed "s|$TMP/|ArithS/Necessitation/|"
done
git checkout -q -- ArithS
# argv writers: generate into TMP, compare
python3 scripts/gen_frag.py "$TMP/Frag.lean" "$TMP/RowInstB.lean" >/dev/null 2>&1 || { echo "  ERROR   gen_frag failed" >&2; fail=1; }
check ArithS/Necessitation/Lib/Frag.lean "$TMP/Frag.lean"
check ArithS/Necessitation/RowInstB.lean "$TMP/RowInstB.lean"
cp scripts/RowInst.lean.head "$TMP/RowInst.lean.head"
python3 scripts/gen_rowinst.py "$TMP/RowInst.lean" >/dev/null 2>&1 || { echo "  ERROR   gen_rowinst failed" >&2; fail=1; }
check ArithS/Necessitation/RowInst.lean "$TMP/RowInst.lean"
[ $fail -eq 0 ] && echo "all generated files are in sync" || echo "OUT OF SYNC: edit the generator (or its .head), regenerate, rebuild ArithS, re-check the census" >&2
exit $fail
