#!/usr/bin/env bash
# Build the part 2 executable `ncert` (the compiled certificate checker) without a lakefile stanza.
#
# Usage:  tools/ncert_build.sh OUTDIR      (OUTDIR is created; it receives obj/*.o and ncert)
#
# 1. `lake build NonUniqueEuler.Verify.Main` (Lean -> C for Main and its imports);
# 2. collects the import closure of NonUniqueEuler.Verify.Main (it must be core only:
#    the script refuses if a Mathlib module appears);
# 3. compiles each C file with `leanc -O3 -DNDEBUG` and links OUTDIR/ncert.
#
# With the stanza
#   [[lean_exe]]
#   name = "ncert"
#   root = "NonUniqueEuler.Verify.Main"
# in lakefile.toml, `lake build ncert` / `lake exe ncert ...` does the same.
set -euo pipefail
OUT="${1:?usage: tools/ncert_build.sh OUTDIR}"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
cd "$(dirname "$0")/.."
LEANC="$(dirname "$(elan which lean 2>/dev/null || command -v lean)")/leanc"
[ -x "$LEANC" ] || LEANC="$HOME/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/leanc"
lake build NonUniqueEuler.Verify.Main
IR=.lake/build/ir
mkdir -p "$OUT/obj"
# import closure of Main inside NonUniqueEuler (breadth first)
todo="NonUniqueEuler.Verify.Main"
seen=""
while [ -n "$todo" ]; do
  set -- $todo; m="$1"; shift; todo="$*"
  case " $seen " in *" $m "*) continue;; esac
  seen="$seen $m"
  f="$(echo "$m" | tr . /).lean"
  for imp in $(sed -n 's/^import[[:space:]]\{1,\}\([A-Za-z0-9_.]*\).*/\1/p' "$f"); do
    case "$imp" in
      NonUniqueEuler.*) todo="$todo $imp";;
      Init*|Std*|Lean*) ;;
      *) echo "ncert_build: $m imports $imp (not core): refusing" >&2; exit 1;;
    esac
  done
done
objs=""
for m in $seen; do
  c="$IR/$(echo "$m" | tr . /).c"
  o="$OUT/obj/$(echo "$m" | tr . _).o"
  if [ ! -f "$o" ] || [ "$c" -nt "$o" ]; then
    echo "leanc $c"
    "$LEANC" -c -O3 -DNDEBUG "$c" -o "$o"
  fi
  objs="$objs $o"
done
"$LEANC" -o "$OUT/ncert" $objs
echo "built $OUT/ncert from:$seen"
