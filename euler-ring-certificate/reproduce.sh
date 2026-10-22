#!/bin/sh
# Reproduce the whole verification: environment check, exact checks, unit tests, the two sector-3
# certifications, and the exact re-check of the outputs.  Usage: ./reproduce.sh [JOBS] [OUTDIR]
# Runs from the source tree without installing the package (python-flint==0.9.0 must be installed).
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
JOBS=${1:-8}
OUT=${2:-out}
PY=${PYTHON:-python3}
export PYTHONPATH="$HERE/src${PYTHONPATH:+:$PYTHONPATH}"
export PYTHONDONTWRITEBYTECODE=1
"$PY" -m ringcert env
"$PY" -m ringcert all --jobs "$JOBS" --out "$OUT"
"$PY" -m ringcert check "$OUT"
"$PY" -m ringcert compare "$OUT" "$HERE/expected" || echo "(compare is diagnostic only; see README)"
