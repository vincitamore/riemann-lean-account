#!/usr/bin/env bash
# After the build: writes the facts of the build that the paper quotes, from the logs and from
# the built tree. Nothing in it is typed by hand.
# Usage, from the working directory of setup.sh:
#   bash summary.sh build.log [mathlib-build.log [janitor.log]] > build-summary.txt
. "$HOME/.elan/env"
log=$1; mlog=${2:-}; jlog=${3:-}
echo "MACHINE"
grep -m1 'model name' /proc/cpuinfo
echo "threads available $(nproc)"
echo "memory $(awk '/MemTotal/ {printf "%.0f GB", $2 / 1048576}' /proc/meminfo)"
echo "BUILD OF Main ($log)"
grep -a -m1 '^START ' "$log"
grep -a 'Build completed successfully' "$log" | tail -1
grep -a '^LAKE-EXIT ' "$log" | tail -1
grep -a '^END ' "$log" | tail -1
echo "oleans $(find lean/.lake/build/lib/lean -name '*.olean' | wc -l)"
echo "failed-marks $(grep -a -c '✖' "$log")"
echo "error-lines $(grep -a -c -E '^[0-9]+ error:' "$log")"
echo "warnings $(grep -a -c 'warning:' "$log")"
echo "compiled-bytes $(find lean/.lake/build/lib/lean -type f -printf '%s\n' | awk '{s += $1} END {print s}')"
if [ -n "$jlog" ]; then
  echo "disk-peak-GB $(grep -a -o 'disk [0-9.]*G used' "$jlog" | grep -o '[0-9.]*' | sort -n | tail -1)"
  echo "setup-files-measured $(awk '$2 == "removed" && $4 == "bytes" {n += $3; b += $5} END {printf "%d files %d bytes\n", n, b}' "$jlog")"
fi
echo "TOOLCHAIN AND PACKAGES"
cat lean/lean-toolchain
(cd lean && lean --version)
grep -E '"(name|inputRev|rev)"' lean/lake-manifest.json
if [ -n "$mlog" ]; then
  echo "BUILD OF Mathlib FROM SOURCE ($mlog)"
  grep -a -m1 '^MATHLIB-START ' "$mlog"
  grep -a 'Build completed successfully' "$mlog" | tail -1
  grep -a '^MATHLIB-EXIT ' "$mlog" | tail -1
  grep -a '^MATHLIB-END ' "$mlog" | tail -1
  echo "mathlib-jobs $(grep -a -o 'Build completed successfully ([0-9]* jobs)' "$mlog" | tail -1 | grep -o '[0-9]*')"
  echo "mathlib-modules-built $(grep -a -c ' Built Mathlib' "$mlog")"
  echo "packages-modules-built $(grep -a -c ' Built ' "$mlog")"
  echo "lines of the log that mention a cache, a download or a release:"
  grep -a -i -E 'cache|download|fetch|release' "$mlog" | sed 's/^/  /'
  echo "(end of those lines)"
fi
