#!/usr/bin/env bash
# Runs an independent implementation of Lean's kernel where it can be run in practical time.
#
# lean4lean (https://github.com/digama0/lean4lean) is a type checker for Lean 4 written in Lean 4.
# Type inference, definitional equality and the checking of inductive types are its own, and not
# the code of the kernel inside Lean, which is written in C++. It does use Lean's representation
# of terms, with Lean's functions for substitution on them, and Lean's reader of compiled files.
# Its command line is that of leanchecker. It is fetched at a fixed commit, which was made for
# Lean v4.33.0-rc2, and built here with the archive's toolchain.
#
# Usage, from the working directory of setup.sh:
#   bash independent.sh build                             fetch and build lean4lean in ./lean4lean
#   bash independent.sh hostile /path/to/verify/hostile out-dir [modules at a time]
#        each hostile module (built by hostile.sh), in both modes  -> out-dir/independent-hostile.txt
#   bash independent.sh fresh out-dir [module]
#        --fresh on a module of Mathlib, by default the one that declares RiemannHypothesis:
#        every declaration in its import closure is checked           -> out-dir/independent-fresh.txt
#   bash independent.sh sample out-dir [processes]
#        after sample.sh: the same modules of the archive, one process a module, each module's
#        own declarations checked against its imports                 -> out-dir/independent-sample.txt
. "$HOME/.elan/env"
work=$(pwd); bin="$work/lean4lean/.lake/build/bin/lean4lean"
commit=5518bf83860bab48e8d53f1f447cdd6c50c30c3f
TIMEFORMAT='elapsed %R s, processor time %U s user and %S s system'
verdict() { [ "$1" = 0 ] && echo accepts || echo rejects; }
case "$1" in
build)
  rm -rf lean4lean && git clone -q https://github.com/digama0/lean4lean && cd lean4lean || exit 1
  git checkout -q "$commit" || exit 1
  echo "lean4lean commit $(git log -1 --format='%H %cI')"
  echo "made for $(cat lean-toolchain); built here with $(cat "$work/lean/lean-toolchain")"
  cp "$work/lean/lean-toolchain" lean-toolchain
  lake build lean4lean 2>&1 | tail -3
  [ -x "$bin" ] && echo INDEPENDENT-BUILT || { echo INDEPENDENT-FAILED; exit 1; }
  ;;
hostile)
  pkg=$(cd "$2" && pwd); out=$(mkdir -p "$3" && cd "$3" && pwd); par=${4:-1}
  cd "$pkg" || exit 1
  one() {
    m=$1; ec=$4
    verdict() { [ "$1" = 0 ] && echo accepts || echo rejects; }
    lake env "$bin" "Hostile.$m" > "$out/independent-hostile-$m.log" 2>&1 < /dev/null; a=$(verdict $?)
    lake env "$bin" --fresh "Hostile.$m" > "$out/independent-hostile-$m-fresh.log" 2>&1 < /dev/null; b=$(verdict $?)
    echo "Hostile.$m: lean4lean $a, lean4lean --fresh $b (a sound replay: $ec)" > "$out/independent-hostile-$m-report.txt"
  }
  export -f one; export out bin
  grep -v '^$' "$pkg/expected.txt" | xargs -P "$par" -L 1 bash -c 'one "$@"' _
  while read -r m rest; do
    [ -z "$m" ] && continue
    cat "$out/independent-hostile-$m-report.txt"
  done < "$pkg/expected.txt" | tee "$out/independent-hostile.txt"
  ;;
fresh)
  out=$(mkdir -p "$2" && cd "$2" && pwd); root=${3:-Mathlib.NumberTheory.LSeries.RiemannZeta}
  ulimit -s unlimited 2>/dev/null
  cd lean || exit 1
  { time lake env "$bin" --fresh "$root" > "$out/independent-fresh-$root.log" 2>&1 < /dev/null; } 2> "$out/independent-time.tmp"; code=$?
  echo "lean4lean --fresh $root: exit $code; $(cat "$out/independent-time.tmp"); $(grep -a -m1 -i 'checked' "$out/independent-fresh-$root.log")" | tee -a "$out/independent-fresh.txt"
  rm -f "$out/independent-time.tmp"
  ;;
sample)
  out=$(cd "$2" && pwd); par=${3:-8}
  cd lean || exit 1
  xargs -P "$par" -I{} sh -c 's=$(date +%s); lake env "$0" "$1" > /dev/null 2>&1 < /dev/null; echo "$1 $? $(( $(date +%s) - s ))"' "$bin" {} \
    < "$out/sample-modules.txt" > "$out/independent-sample.txt"
  {
    echo "modules checked $(wc -l < "$out/independent-sample.txt")"
    echo "accepted $(awk '$2 == 0' "$out/independent-sample.txt" | wc -l)"
    echo "not accepted $(awk '$2 != 0' "$out/independent-sample.txt" | wc -l)"
    echo "Main $(awk '$1 == "Main" {print ($2 == 0) ? "accepted" : "not accepted"}' "$out/independent-sample.txt")"
    echo "seconds, summed over the modules $(awk '{s += $3} END {print s}' "$out/independent-sample.txt")"
  } > "$out/independent-sample-summary.txt"
  cat "$out/independent-sample-summary.txt"
  ;;
*)
  echo "usage: independent.sh build | hostile DIR OUT | fresh OUT [module] | sample OUT [processes]"; exit 2 ;;
esac
