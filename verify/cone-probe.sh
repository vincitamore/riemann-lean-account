#!/usr/bin/env bash
# After the build and mathlib-diff.sh: are the constants of Mathlib that differ between the build
# from source and the community's cached build in the dependency cone of riemannHypothesis?
#
# The lists that cut.sh writes cover the archive's declarations only. This script takes every
# name that mathlib-diff.txt lists (in one build only, or with a statement or a value that
# differs) and asks the program cut/ConeProbe.lean, which computes the cone as CutMain.lean
# does, whether each is a constant of the built environment and whether it is in the cone. The
# environment is the one built here, from source, so a name that only the cached build has is
# reported as not a constant of this build.
#
# Usage, from the working directory of setup.sh:
#   bash cone-probe.sh /path/to/this/verify/cut out-dir
# where out-dir holds mathlib-diff.txt. Output: out-dir/cone-probe.txt.
. "$HOME/.elan/env"
self=$(cd "$(dirname "$0")" && pwd)/$(basename "$0")
prog=$(cd "$1" && pwd); out=$(cd "$2" && pwd)
[ -f "$out/mathlib-diff.txt" ] || { echo "cone-probe.sh: $out/mathlib-diff.txt is missing"; exit 1; }
(cd "$prog" && lake build coneprobe) || exit 1
# the names: the lines "  <kind> <module> <name>" of the sections of mathlib-diff.txt
grep -a '^  [A-Z][-up] ' "$out/mathlib-diff.txt" | cut -d' ' -f5- | LC_ALL=C sort -u > "$out/cone-probe-names.tmp"
{
  echo "script sha256 $(sha256sum "$self" | cut -d' ' -f1)"
  echo "program sha256 $(sha256sum "$prog/ConeProbe.lean" | cut -d' ' -f1)"
  echo "names taken from mathlib-diff.txt: $(wc -l < "$out/cone-probe-names.tmp")"
  (cd lean && lake env "$prog/.lake/build/bin/coneprobe" "$out/cone-probe-names.tmp"); echo "CONE-PROBE-EXIT $?"
} > "$out/cone-probe.txt" 2>&1
rm -f "$out/cone-probe-names.tmp"
cat "$out/cone-probe.txt"
