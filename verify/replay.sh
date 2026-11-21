#!/usr/bin/env bash
# After the build: replays the declarations a module imports (all but the unsafe and partial
# ones) through the kernel, from an empty environment, and compares the environment the kernel
# built with the compiled files (replay/ReplayMain.lean). The module is Main unless a third
# argument names another; for Main the five theorems are reported on by name.
# The replay of Main used up to about 30 GB beyond the page cache on 28 threads; set
# LEAN_NUM_THREADS to choose the number.
# Usage, from the working directory of setup.sh:
#   bash replay.sh /path/to/this/verify/replay out-dir [root-module]
. "$HOME/.elan/env"
prog=$(cd "$1" && pwd); out=$(mkdir -p "$2" && cd "$2" && pwd); root=${3:-Main}
(cd "$prog" && lake build replay) || exit 1
ulimit -s 1048576 2>/dev/null || ulimit -s unlimited 2>/dev/null
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-$(nproc)}
export LEAN_ABORT_ON_PANIC=1
targets=""
[ "$root" = Main ] && targets="riemannHypothesis riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive"
{
  echo "program sha256 $(sha256sum "$prog/ReplayMain.lean" | cut -d' ' -f1)"
  echo "toolchain $(cd lean && lean --version)"
  echo "root $root"
  echo "threads $LEAN_NUM_THREADS"
  echo "compiled files of the archive: $(find lean/.lake/build/lib/lean -name '*.olean' | wc -l)"
  echo "sha256 of the compiled file of Main: $(sha256sum lean/.lake/build/lib/lean/Main.olean | cut -d' ' -f1)"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$out/replay-provenance.txt"
cd lean || exit 1
TIMEFORMAT='elapsed %R s, processor time %U s user and %S s system'
{ time lake env "$prog/.lake/build/bin/replay" "$out" "$root" $targets 2> "$out/replay-stderr.txt"; } 2> "$out/replay-time.txt"
code=$?
echo "REPLAY-EXIT $code"
cat "$out/replay-time.txt" >> "$out/replay-provenance.txt"
echo "exit code $code" >> "$out/replay-provenance.txt"
exit $code
