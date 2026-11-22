#!/usr/bin/env bash
# After sample.sh and "independent.sh sample": what the two sample steps covered, and the names
# they could not finish.
#
# leanchecker and lean4lean, in their ordinary mode, take a name as a prefix: they check the
# module of that name and every module whose name extends it, and they import the whole import
# closure once for each of those modules, all at the same time (LeanChecker.lean and lean4lean's
# Main.lean: `target.isPrefixOf m`, one task a module). For a name with many modules under it
# that takes more memory than a machine may have, and the system kills the process (exit code
# 137), which is no verdict of the checker.
#
# This script
#   1. lists, for every name of the sample, the modules whose names extend it
#      (sample-prefixes.txt: one line "<name> <module>" for each);
#   2. tests the two routes of step 3 on two modules of verify/hostile/, one that every checker
#      must accept and one that every checker must reject (lines "route-test ...");
#   3. for every name whose process ended with a code other than 0, calls the checker's own
#      function for one module, `replayFromImports`, on the module of that name and on each
#      module under it, one at a time. The function is the one the command itself calls for
#      each module. For leanchecker it is taken from the toolchain's compiled LeanChecker
#      module and called from a two-line file that Lean elaborates. For lean4lean it is taken
#      from the Lean4Lean library and called from a short program run with `lean --run` in
#      lean4lean's own package, so Lean's interpreter runs lean4lean's code there and it is
#      slower than the compiled command.
#
# Usage, from the working directory of setup.sh, after hostile.sh has built verify/hostile:
#   bash sample-exact.sh results-dir /path/to/verify/hostile
# Output in results-dir: sample-prefixes.txt and sample-exact.txt. The latter begins with the
# SHA-256 of this script and of the lean4lean binary and the files read; then the lines of
# step 2; then, for step 3, one line for each module:
#   <checker> <name given to the sample> <module> <exit code> <seconds> <what the checker printed last>
# and it ends with the container's count of processes killed for memory before and after. The
# script stops if a sample file is missing or a route test gives the wrong verdict.
. "$HOME/.elan/env"
self=$(cd "$(dirname "$0")" && pwd)/$(basename "$0")
work=$(pwd); out=$(cd "$1" && pwd); hostile=$(cd "$2" && pwd) || { echo "sample-exact.sh: no hostile directory"; exit 1; }
for f in sample.txt independent-sample.txt sample-modules.txt; do
  [ -f "$out/$f" ] || { echo "sample-exact.sh: $out/$f is missing"; exit 1; }
done
l4lbin="$work/lean4lean/.lake/build/bin/lean4lean"
hbase=$(cd "$hostile" && lake env printenv LEAN_PATH)
cd lean || exit 1
export LEAN_ABORT_ON_PANIC=1
lib=.lake/build/lib/lean
under() {  # the modules whose names extend the name $1, from the compiled files
  d="$lib/$(echo "$1" | tr . /)"
  [ -d "$d" ] && find "$d" -name '*.olean' | sed "s|^$lib/||; s|\.olean\$||" | tr / . | LC_ALL=C sort
}
while read -r name; do
  under "$name" | sed "s|^|$name |"
done < "$out/sample-modules.txt" > "$out/sample-prefixes.txt"

base=$(lake env printenv LEAN_PATH)
tmp="$work/sample-exact-work"; mkdir -p "$tmp"
oom() { awk '$1 == "oom_kill" {print $2}' /sys/fs/cgroup/memory.events 2>/dev/null; }
before=$(oom)
{
  echo "script sha256 $(sha256sum "$self" | cut -d' ' -f1)"
  echo "lean4lean binary sha256 $(sha256sum "$l4lbin" | cut -d' ' -f1), last written $(date -u -r "$l4lbin" +%Y-%m-%dT%H:%M:%SZ)"
  echo "read sample.txt ($(awk '$2 != 0' "$out/sample.txt" | wc -l) with a code other than 0) and independent-sample.txt ($(awk '$2 != 0' "$out/independent-sample.txt" | wc -l))"
  echo "started $(date -u +%Y-%m-%dT%H:%M:%SZ), one process at a time"
} > "$out/sample-exact.txt"

# the two routes of step 3
run_leanchecker() {  # module, log, search path
  printf 'import LeanChecker\n#eval unsafe replayFromImports `%s\n' "$1" > "$tmp/One.lean"
  LEAN_PATH="$3" lean "$tmp/One.lean" > "$2" 2>&1 < /dev/null
}
cat > "$tmp/L4LOne.lean" <<'EOL'
import Lean4Lean.Replay
open Lean
/-- lean4lean's function for one module, on exactly the module named. The search path for the
compiled files to check is taken from TARGET_LEAN_PATH. -/
unsafe def main (args : List String) : IO UInt32 := do
  let sp := ((← IO.getEnv "TARGET_LEAN_PATH").getD "").splitOn ":" |>.filter (· ≠ "") |>.map System.FilePath.mk
  searchPathRef.set (sp ++ [(← findSysroot) / "lib" / "lean"])
  let n ← Lean4Lean.Replay.replayFromImports args.head!.toName
  IO.println s!"checked {n} declarations"
  return 0
EOL
run_lean4lean() {  # module, log, search path
  (cd "$work/lean4lean" && TARGET_LEAN_PATH="$3" lake env lean --run "$tmp/L4LOne.lean" "$1" > "$2" 2>&1 < /dev/null)
}
last() { tr -d '\r' < "$1" | grep -v '^$' | tail -n 1 | cut -c1-80; }

# step 2: each route on a module to accept and a module to reject
for c in leanchecker lean4lean; do
  run_$c Hostile.Honest "$tmp/route-$c-Honest.log" "$hbase"; a=$?
  run_$c Hostile.FalseTheorem "$tmp/route-$c-FalseTheorem.log" "$hbase"; r=$?
  echo "route-test $c Hostile.Honest exit $a (0 required): $(last "$tmp/route-$c-Honest.log")" >> "$out/sample-exact.txt"
  echo "route-test $c Hostile.FalseTheorem exit $r (not 0 required): $(last "$tmp/route-$c-FalseTheorem.log")" >> "$out/sample-exact.txt"
  if [ "$a" != 0 ] || [ "$r" = 0 ]; then echo "sample-exact.sh: the route for $c gives the wrong verdict on a test module"; exit 1; fi
done

# step 3
exact() {  # name of the checker, the file of its first runs
  awk '$2 != 0 {print $1}' "$2" | while read -r name; do
    { echo "$name"; under "$name"; } | while read -r m; do
      s=$(date +%s)
      run_$1 "$m" "$tmp/$1-$m.log" "$base"; code=$?
      echo "$1 $name $m $code $(( $(date +%s) - s )) $(last "$tmp/$1-$m.log")" >> "$out/sample-exact.txt"
    done
  done
}
exact leanchecker "$out/sample.txt"
exact lean4lean "$out/independent-sample.txt"
echo "ended $(date -u +%Y-%m-%dT%H:%M:%SZ); processes killed for memory in the container ${before:-unknown} -> $(oom)" >> "$out/sample-exact.txt"
cat "$out/sample-exact.txt"
