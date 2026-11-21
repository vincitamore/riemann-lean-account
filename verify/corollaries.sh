#!/usr/bin/env bash
# After the build: compiles the two Lean files of this repository's lean/ directory against the
# built archive. Corollaries.lean proves three immediate corollaries of the top theorems and
# prints their axioms; Targets.lean states propositions and proves nothing.
# Usage, from the working directory of setup.sh:
#   bash corollaries.sh /path/to/this/lean results-dir
. "$HOME/.elan/env"
src=$(cd "$1" && pwd); out=$(mkdir -p "$2" && cd "$2" && pwd)
cd lean || exit 1
{ lake env lean "$src/Corollaries.lean"; echo "COR-EXIT $?"; } > "$out/corollaries.txt" 2>&1
{ lake env lean "$src/Targets.lean"; echo "TARGETS-EXIT $?"; } > "$out/targets.txt" 2>&1
cat "$out/corollaries.txt" "$out/targets.txt"
