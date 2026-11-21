#!/usr/bin/env bash
# After the build and cut.sh: runs Lean's own checker, leanchecker in its ordinary mode, on a
# sample of the archive's modules, one process a module. In that mode the module's own
# declarations are replayed against its imports, which are trusted. The sample is Main and N
# modules drawn from the modules that hold a declaration of the dependency cone
# (cut-modules.txt), by a fixed shuffle so that the choice can be repeated. Each line of the
# output gives a module, the checker's exit code and the seconds it took; the time is nearly
# all import, which is why the whole archive cannot be covered this way.
#
# Usage, from the working directory of setup.sh:
#   bash sample.sh results-dir N [processes]
# where results-dir holds cut-modules.txt. Output: sample.txt and sample-summary.txt there.
. "$HOME/.elan/env"
out=$(cd "$1" && pwd); n=${2:-500}; par=${3:-8}
cd lean || exit 1
{ echo Main; shuf -n "$n" --random-source=<(yes) "$out/cut-modules.txt"; } > "$out/sample-modules.txt"
start=$(date +%s)
xargs -P "$par" -I{} sh -c 's=$(date +%s); lake env leanchecker "$1" > /dev/null 2>&1 < /dev/null; echo "$1 $? $(( $(date +%s) - s ))"' _ {} \
  < "$out/sample-modules.txt" > "$out/sample.txt"
{
  echo "modules checked $(wc -l < "$out/sample.txt") (Main and $n drawn from the $(wc -l < "$out/cut-modules.txt") modules of the cone)"
  echo "accepted $(awk '$2 == 0' "$out/sample.txt" | wc -l)"
  echo "not accepted $(awk '$2 != 0' "$out/sample.txt" | wc -l)"
  echo "Main $(awk '$1 == "Main" {print ($2 == 0) ? "accepted" : "not accepted"}' "$out/sample.txt")"
  echo "seconds, summed over the modules $(awk '{s += $3} END {print s}' "$out/sample.txt")"
  echo "processes at a time $par"
  echo "elapsed seconds $(( $(date +%s) - start ))"
} > "$out/sample-summary.txt"
cat "$out/sample-summary.txt"
