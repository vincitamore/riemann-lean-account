#!/usr/bin/env bash
# Runs Lean's own checker, leanchecker --fresh, where one run of it covers a whole import
# closure in practical time: on the module of Mathlib that declares the statement
# RiemannHypothesis, and on Mathlib itself. One process replays the module's whole closure into
# an empty environment, on one thread. Our replay is then run on the same root, and the two
# must agree. Needs Mathlib compiled (setup.sh); it does not need the archive's build.
#
# Usage, from the working directory of setup.sh:
#   bash stock.sh /path/to/this/verify/replay results-dir
# Output in results-dir: stock.txt (its first line is the SHA-256 of the replay program used),
# stock-fresh-<root>.log, replay-<root>/.
. "$HOME/.elan/env"
prog=$(cd "$1" && pwd); out=$(mkdir -p "$2" && cd "$2" && pwd)
ulimit -s unlimited 2>/dev/null
cd lean || exit 1
TIMEFORMAT='elapsed %R s, processor time %U s user and %S s system'
(cd "$prog" && lake build replay >/dev/null 2>&1) || { echo "the replay program does not build"; exit 1; }
echo "replay program sha256 $(sha256sum "$prog/ReplayMain.lean" | cut -d' ' -f1)" > "$out/stock.txt"
for root in ${FRESH_ROOTS:-Mathlib.NumberTheory.LSeries.RiemannZeta Mathlib}; do
  { time lake env leanchecker --fresh "$root" > "$out/stock-fresh-$root.log" 2>&1; } 2> "$out/stock-time.tmp"; code=$?
  echo "leanchecker --fresh $root: exit $code; $(cat "$out/stock-time.tmp")" | tee -a "$out/stock.txt"
  rm -rf "$out/replay-$root"; mkdir -p "$out/replay-$root"
  { time LEAN_ABORT_ON_PANIC=1 lake env "$prog/.lake/build/bin/replay" "$out/replay-$root" "$root" > "$out/replay-$root/log.txt" 2>&1; } 2> "$out/stock-time.tmp"; code=$?
  echo "replay $root: exit $code; $(cat "$out/stock-time.tmp"); $(grep -E '^(constants|replayed|failed) ' "$out/replay-$root/replay-summary.txt" | tr '\n' ' ')" | tee -a "$out/stock.txt"
done
rm -f "$out/stock-time.tmp"
