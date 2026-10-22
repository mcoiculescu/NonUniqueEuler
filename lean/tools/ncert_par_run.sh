#!/usr/bin/env bash
# Start the FULL multithreaded certificate run in the background and return at once.
#
#   ncert par  evaluates  checkCorePar defaultPrec certLits
#   (= Verify.check Verify.cert by `check_eq_checkCorePar`, NonUniqueEuler/Verify/Data/CellsPar.lean)
#
# Usage:  tools/ncert_par_run.sh NCERT_DIR [THREADS]      (default THREADS = 6)
#   NCERT_DIR contains the executable built by `tools/ncert_build.sh NCERT_DIR`.
#
# Environment of the run:
#   LEAN_NUM_THREADS=THREADS  size of the Lean runtime thread pool (read by lean_init_task_manager;
#                             unset = number of hardware threads)
#   MallocNanoZone=1          macOS nano malloc zone; GMP allocates through the system malloc, and
#                             without it the threads contend in malloc (about 1.6x the CPU time)
#   nice -n 10, nohup, and on macOS caffeinate -i (no idle sleep while it runs)
#
# Output (in NCERT_DIR):
#   par_all.log  stderr: a header, then for every cell as it finishes the JSON records of its
#                certified sub-cells and a line "[ELAPSED s, k/261 cells] cell i of N1'/N2': ...",
#                then the lines RESULT N1' / RESULT N2'
#   par_all.out  stdout: "checkCorePar defaultPrec certLits = check cert = true|false  (T s)",
#                then "exit code 0|1" (0 iff true)
set -euo pipefail
DIR="${1:?usage: tools/ncert_par_run.sh NCERT_DIR [THREADS]}"
NT="${2:-6}"
cd "$DIR"
[ -x ./ncert ] || { echo "ncert_par_run: no executable $DIR/ncert" >&2; exit 1; }
for f in par_all.log par_all.out; do
  [ ! -e "$f" ] || { echo "ncert_par_run: $DIR/$f exists; move it away first" >&2; exit 1; }
done
CAF=""
if command -v caffeinate >/dev/null 2>&1; then CAF="caffeinate -i"; fi
nohup $CAF env MallocNanoZone=1 LEAN_NUM_THREADS="$NT" nice -n 10 \
  sh -c './ncert par > par_all.out 2> par_all.log; echo "exit code $?" >> par_all.out' \
  < /dev/null > /dev/null 2>&1 &
echo "started (pid $!): progress  tail -f $DIR/par_all.log ; result  $DIR/par_all.out"
