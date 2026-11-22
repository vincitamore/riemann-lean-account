#!/usr/bin/env bash
# After the build and cut.sh: runs Lean's own checker, leanchecker in its ordinary mode, on a
# sample of names of the archive's modules, one process a name. In that mode the checker takes
# the name as a prefix: the declarations of the module of that name, and of every module whose
# name extends it, are replayed against the module's imports, which are trusted, and the
# import closure is imported once for each of those modules, all at once. The sample is Main
# and N names drawn from the modules that hold a declaration of the dependency cone
# (cut-modules.txt), by a fixed selection (shuf with a constant random source) so that the
# choice can be repeated. Each line of the output gives a name, the checker's exit code and
# the elapsed seconds its process took; the time is nearly all import, which is why the whole
# archive cannot be covered this way. What the checker printed on each name is kept, a panic
# is made fatal, and the container's count of processes killed for memory is read before and
# after: a process the system kills ends with code 137, which is no verdict (sample-exact.sh).
#
# Usage, from the working directory of setup.sh:
#   bash sample.sh results-dir N [processes]
# where results-dir holds cut-modules.txt. Output there: sample-modules.txt, sample.txt,
# sample-summary.txt and sample-logs/.
. "$HOME/.elan/env"
out=$(cd "$1" && pwd); n=${2:-500}; par=${3:-8}
cd lean || exit 1
{ echo Main; shuf -n "$n" --random-source=<(yes) "$out/cut-modules.txt"; } > "$out/sample-modules.txt"
rm -rf "$out/sample-logs"; mkdir -p "$out/sample-logs"
oom() { awk '$1 == "oom_kill" {print $2}' /sys/fs/cgroup/memory.events 2>/dev/null; }
before=$(oom); start=$(date +%s)
export LEAN_ABORT_ON_PANIC=1
xargs -P "$par" -I{} sh -c 's=$(date +%s); lake env leanchecker "$1" > "$2/sample-logs/$1.log" 2>&1 < /dev/null; echo "$1 $? $(( $(date +%s) - s ))"' _ {} "$out" \
  < "$out/sample-modules.txt" > "$out/sample.txt"
after=$(oom)
{
  echo "modules checked $(wc -l < "$out/sample.txt") (Main and $n drawn from the $(grep -c '' "$out/cut-modules.txt") modules of the cone)"
  echo "accepted $(awk '$2 == 0' "$out/sample.txt" | wc -l)"
  echo "not accepted $(awk '$2 != 0' "$out/sample.txt" | wc -l)"
  echo "Main $(awk '$1 == "Main" {print ($2 == 0) ? "accepted" : "not accepted"}' "$out/sample.txt")"
  echo "seconds, summed over the modules $(awk '{s += $3} END {print s}' "$out/sample.txt")"
  echo "processes at a time $par"
  echo "elapsed seconds $(( $(date +%s) - start ))"
  echo "processes killed for memory in the container during the step ${before:-unknown} -> ${after:-unknown}"
  echo "logs that mention a panic $(grep -l -a PANIC "$out/sample-logs"/*.log 2>/dev/null | wc -l)"
} > "$out/sample-summary.txt"
cat "$out/sample-summary.txt"
