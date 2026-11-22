#!/usr/bin/env bash
# Tests the checkers on small modules that are built to be wrong (hostile/Hostile/*.lean, and
# the compiled files that hostile/Craft.lean writes directly). Every module with a source
# compiles. Each but the controls has, in its import closure, a compiled file holding something
# that the kernel never saw or would not accept. Lean's own checker (leanchecker, in both of its
# modes) and our replay program are run on every module.
#
# hostile/expected.txt gives, for each module: what leanchecker, leanchecker --fresh and the
# replay are expected to do (accepts, rejects, or any: no expectation, what is observed is
# reported), and the names under which the replay must record its failures (- for none). The
# replay's verdict must be the expected one and its failures must be exactly those names.
# leanchecker without --fresh checks the named module against its imports, which it trusts.
#
# The script stops if the package does not build, if a module has no compiled file (a module
# that did not compile would otherwise count as rejected), or if a line of expected.txt is not
# of the form above. Each module's outputs are removed before it is run, so that nothing read
# afterwards is left from an earlier run.
# Usage:   bash hostile.sh /path/to/this/verify/hostile /path/to/this/verify/replay out-dir [modules at a time]
. "$HOME/.elan/env"
pkg=$(cd "$1" && pwd); prog=$(cd "$2" && pwd); out=$(mkdir -p "$3" && cd "$3" && pwd); par=${4:-1}
(cd "$prog" && lake build replay >/dev/null 2>&1) || { echo "HOSTILE-FAILED the replay program does not build"; exit 1; }
echo "replay program sha256 $(sha256sum "$prog/ReplayMain.lean" | cut -d' ' -f1)"
cd "$pkg" || exit 1
[ -z "$(tail -c 1 expected.txt)" ] || { echo "HOSTILE-FAILED expected.txt does not end with a newline"; exit 1; }
if grep -v -E '^[A-Za-z0-9]+ (accepts|rejects|any) (accepts|rejects|any) (accepts|rejects) [^[:space:]]+$' expected.txt | grep -q .; then
  echo "HOSTILE-FAILED a line of expected.txt is not of the expected form"; exit 1
fi
mapfile -t modules < <(cut -d' ' -f1 expected.txt)
[ "${#modules[@]}" -gt 0 ] || { echo "HOSTILE-FAILED expected.txt names no module"; exit 1; }
[ -z "$(printf '%s\n' "${modules[@]}" | sort | uniq -d)" ] || { echo "HOSTILE-FAILED expected.txt names a module twice"; exit 1; }
lake build > "$out/hostile-build.txt" 2>&1 || { echo "HOSTILE-FAILED the hostile package does not build"; tail -5 "$out/hostile-build.txt"; exit 1; }
lake exe craft >> "$out/hostile-build.txt" 2>&1 || { echo "HOSTILE-FAILED the crafted files were not written"; exit 1; }
echo "the hostile package builds and the crafted files are written"
for m in "${modules[@]}"; do
  [ -f ".lake/build/lib/lean/Hostile/$m.olean" ] || { echo "HOSTILE-FAILED Hostile.$m has no compiled file"; exit 1; }
  rm -rf "$out/hostile-$m-replay" "$out/hostile-$m-report.txt" "$out/hostile-$m-leanchecker.txt" "$out/hostile-$m-leanchecker-fresh.txt"
done
grep -E "depends on axioms|does not depend on any axioms" "$out/hostile-build.txt" | sed 's/^info: /  /'

# one module: the three checkers, then a report in $out/hostile-<module>-report.txt whose
# last line is OK or UNEXPECTED
one() {
  m=$1; ea=$2; eb=$3; ec=$4; names=$5
  verdict() { [ "$1" = 0 ] && echo accepts || echo rejects; }
  lake env leanchecker "Hostile.$m" > "$out/hostile-$m-leanchecker.txt" 2>&1 < /dev/null; a=$(verdict $?)
  lake env leanchecker --fresh "Hostile.$m" > "$out/hostile-$m-leanchecker-fresh.txt" 2>&1 < /dev/null; b=$(verdict $?)
  mkdir -p "$out/hostile-$m-replay"
  LEAN_ABORT_ON_PANIC=1 lake env "$prog/.lake/build/bin/replay" "$out/hostile-$m-replay" "Hostile.$m" > "$out/hostile-$m-replay/log.txt" 2>&1 < /dev/null; c=$(verdict $?)
  ok=yes
  for pair in "$ea:$a" "$eb:$b" "$ec:$c"; do
    e=${pair%%:*}; v=${pair##*:}
    [ "$e" = any ] || [ "$e" = "$v" ] || ok=NO
  done
  # the program writes its files at its end: without its summary the run did not finish
  [ -f "$out/hostile-$m-replay/replay-summary.txt" ] || ok=NO
  got=$(cut -f1 "$out/hostile-$m-replay/replay-failures.txt" 2>/dev/null | grep -v '^$' | LC_ALL=C sort -u | paste -sd, -)
  want=$(echo "$names" | tr ',' '\n' | grep -v '^-$' | LC_ALL=C sort -u | paste -sd, -)
  [ "$got" = "$want" ] || ok=NO
  {
    echo "Hostile.$m: leanchecker $a (expected $ea), leanchecker --fresh $b (expected $eb), replay $c (expected $ec); as expected: $ok"
    [ -f "$out/hostile-$m-replay/replay-summary.txt" ] || echo "    the replay did not finish: $(tail -n 1 "$out/hostile-$m-replay/log.txt" | cut -c1-200)"
    [ "$got" = "$want" ] || echo "    the replay's failures are under [$got], expected [$want]"
    if [ -s "$out/hostile-$m-replay/replay-failures.txt" ]; then sed 's/^/    replay: /' "$out/hostile-$m-replay/replay-failures.txt" | cut -c1-260; fi
    [ "$b" = rejects ] && grep -v '^$' "$out/hostile-$m-leanchecker-fresh.txt" | grep -v -E '^\s|backtrace|\.so' | head -2 | sed 's/^/    leanchecker --fresh: /' | cut -c1-260
    [ $ok = yes ] && echo OK || echo UNEXPECTED
  } > "$out/hostile-$m-report.txt"
}
export -f one; export out prog
xargs -P "$par" -L 1 bash -c 'one "$@"' _ < expected.txt
bad=0
for m in "${modules[@]}"; do
  [ -f "$out/hostile-$m-report.txt" ] || { echo "Hostile.$m: no report was written"; bad=1; continue; }
  sed '$d' "$out/hostile-$m-report.txt"
  [ "$(tail -n 1 "$out/hostile-$m-report.txt")" = OK ] || bad=1
done
# the one axiom that Hostile.Axiom declares must be in the replay's list of axioms
ax=$(grep -c '^Hostile\.' "$out/hostile-Axiom-replay/replay-axioms.txt" 2>/dev/null)
echo "axioms named Hostile.* that the replay lists for Hostile.Axiom: $ax (expected 1)"
[ "$ax" = 1 ] || bad=1

# The report on named theorems. Hostile.conclusion is a theorem that the kernel accepts and that
# depends on Hostile.falseProved, which it rejects; Hostile.Honest.size_pos depends on nothing
# that fails.
rm -rf "$out/hostile-targets"; mkdir -p "$out/hostile-targets"
LEAN_ABORT_ON_PANIC=1 lake env "$prog/.lake/build/bin/replay" "$out/hostile-targets" Hostile.FalseTheorem Hostile.conclusion > "$out/hostile-targets/log.txt" 2>&1 < /dev/null
t1=$(grep -c '^Hostile.conclusion: FAILED' "$out/hostile-targets/replay-targets.txt" 2>/dev/null)
rm -rf "$out/hostile-targets-honest"; mkdir -p "$out/hostile-targets-honest"
LEAN_ABORT_ON_PANIC=1 lake env "$prog/.lake/build/bin/replay" "$out/hostile-targets-honest" Hostile.Honest Hostile.Honest.size_pos > "$out/hostile-targets-honest/log.txt" 2>&1 < /dev/null; c2=$?
t2=$(grep -c '^Hostile.Honest.size_pos: a theorem, checked by the kernel' "$out/hostile-targets-honest/replay-targets.txt" 2>/dev/null)
if [ "$t1" = 1 ] && [ "$t2" = 1 ] && [ "$c2" = 0 ]; then
  echo "named theorems: Hostile.conclusion reported FAILED, Hostile.Honest.size_pos reported checked; as expected: yes"
else
  echo "named theorems: as expected: NO"; bad=1
fi
[ $bad = 0 ] && echo HOSTILE-OK || echo HOSTILE-UNEXPECTED
