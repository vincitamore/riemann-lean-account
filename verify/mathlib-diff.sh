#!/usr/bin/env bash
# How does Mathlib compiled from source differ from the community's cached build of the same
# commit?
#
# The first build of the archive took Mathlib's compiled files from the community's cache; the
# second compiled Mathlib from source. This script fetches the cache into a second copy of the
# Mathlib package and lists every constant of the import closure of Mathlib in each of the two
# builds: kind, safety mark, declaring module, name, and the hash of its type and of its
# value. It writes
#   - the constants (kind, module, name) that one build has and the other lacks;
#   - among the constants both have, those whose types have different hashes, which are
#     statements that differ, and those whose values have different hashes, which are proofs
#     or definitions that were elaborated differently;
#   - for each constant whose statement differs, the statement as each build has it, and, if
#     its name ends in .eq_N, the kind of the constant whose equation it would be.
# The hash is the one that each compiled file stores with each term. It has 32 bits and does
# not see the names of bound variables, their annotations, or metadata. Nothing here recomputes
# it. Equal hashes are evidence that two terms are equal, not a proof.
#
# Usage, from the working directory of setup.sh, after Mathlib has been compiled from source
# (the script stops unless mathlib-build.log records that build; it does not detect a cache
# fetched into lean/ afterwards):
#   bash mathlib-diff.sh out-dir
# Output in out-dir: mathlib-diff.txt. Needs about 10 GB of disk for the cached files and the
# network to fetch them.
set -o pipefail
. "$HOME/.elan/env"
self=$(cd "$(dirname "$0")" && pwd)/$(basename "$0")
out=$(mkdir -p "$1" && cd "$1" && pwd); work=$(pwd)
grep -q '^MATHLIB-EXIT 0' "$work/mathlib-build.log" 2>/dev/null \
  || { echo "mathlib-diff.sh: mathlib-build.log does not record a build of Mathlib from source"; exit 1; }
tmp=$work/mathlib-diff-work; mkdir -p "$tmp"
cat > "$tmp/ListNames.lean" <<'EOL'
import Lean
open Lean
/-- Prints every constant of the import closure of the named module: its kind, whether Lean
marks it unsafe or partial, the module that declares it, its name, and the hashes of its type
and of its value (0 where the kind has no value). -/
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := args.head!.toName }] {} (trustLevel := 1024)
  let mods := env.header.moduleNames
  let stdout ← IO.getStdout
  for i in [0:mods.size] do
    let md := env.header.moduleData[i]!
    for j in [0:md.constNames.size] do
      let c := md.constants[j]!
      let k := match c with
        | .axiomInfo _ => "A" | .defnInfo _ => "D" | .thmInfo _ => "T" | .opaqueInfo _ => "O"
        | .quotInfo _ => "Q" | .inductInfo _ => "I" | .ctorInfo _ => "C" | .recInfo _ => "R"
      let v : UInt64 := match c with
        | .defnInfo d => d.value.hash | .thmInfo d => d.value.hash | .opaqueInfo d => d.value.hash
        | _ => 0
      stdout.putStrLn s!"{k}{if c.isUnsafe then "u" else if c.isPartial then "p" else "-"} {mods[i]!} {c.type.hash} {v} {md.constNames[j]!}"
EOL
# a second copy of the Mathlib package, with no compiled files, and the cache fetched into it
rm -rf "$tmp/mathlib"; mkdir -p "$tmp/mathlib"
tar -C lean/.lake/packages/mathlib --exclude=.lake -cf - . | tar -C "$tmp/mathlib" -xf -
commit=$(git -C "$tmp/mathlib" rev-parse HEAD)
(cd "$tmp/mathlib" && lake exe cache get > "$tmp/cache-get.log" 2>&1) || { echo "the cache could not be fetched"; tail -3 "$tmp/cache-get.log"; exit 1; }
fetched=$(date -u +%Y-%m-%dT%H:%M:%SZ)
(cd "$tmp/mathlib" && lake env lean --run "$tmp/ListNames.lean" Mathlib 2> "$tmp/list-cache.err" > "$tmp/all-cache.txt") || { echo "listing the cached build failed"; exit 1; }
(cd lean && lake env lean --run "$tmp/ListNames.lean" Mathlib 2> "$tmp/list-source.err" > "$tmp/all-source.txt") || { echo "listing the build from source failed"; exit 1; }
# the lists without the hashes: kind, module, name (a name may contain spaces, so it is last)
cut -d' ' -f1,2,5- "$tmp/all-cache.txt" | LC_ALL=C sort > "$tmp/names-cache.txt"
cut -d' ' -f1,2,5- "$tmp/all-source.txt" | LC_ALL=C sort > "$tmp/names-source.txt"
# the constants both builds have: N their number, T one whose types differ in hash, V one whose
# values differ in hash
awk 'function key(   i, k) { k = $1 " " $2; for (i = 5; i <= NF; i++) k = k " " $i; return k }
     NR == FNR { t[key()] = $3; v[key()] = $4; next }
     { k = key(); if (k in t) { n++; if (t[k] != $3) print "T " k; if (v[k] != $4) print "V " k } }
     END { print "N " n }' "$tmp/all-cache.txt" "$tmp/all-source.txt" > "$tmp/common.txt" || exit 1
# the statements that differ, as each build has them
sed -n 's/^T [^ ]* [^ ]* //p' "$tmp/common.txt" > "$tmp/differ-names.txt"
cat > "$tmp/Show.lean" <<'EOL'
import Mathlib
open Lean Meta
def mkName (s : String) : Name :=
  s.splitOn "." |>.foldl (fun n c => if c ≠ "" && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous
#eval show MetaM Unit from do
  let some file ← IO.getEnv "DIFF_NAMES" | throwError "DIFF_NAMES is not set"
  for s in (← IO.FS.lines file) do
    let n := mkName s
    match (← getEnv).find? n with
    | none => IO.println s!"{s}: not found"
    | some ci =>
      IO.println s!"{s} :"
      IO.println ((← ppExpr ci.type).pretty 100)
      if let .str p e := n then
        if e.startsWith "eq_" then
          let k := match (← getEnv).find? p with
            | some (.defnInfo _) => "a definition" | some (.thmInfo _) => "a theorem"
            | some _ => "a constant of another kind" | none => "not a constant"
          IO.println s!"[{p} is {k}]"
EOL
(cd "$tmp/mathlib" && DIFF_NAMES="$tmp/differ-names.txt" lake env lean "$tmp/Show.lean" > "$tmp/show-cache.txt" 2>&1) || { echo "printing the statements of the cached build failed"; tail -3 "$tmp/show-cache.txt"; exit 1; }
(cd lean && DIFF_NAMES="$tmp/differ-names.txt" lake env lean "$tmp/Show.lean" > "$tmp/show-source.txt" 2>&1) || { echo "printing the statements of the build from source failed"; tail -3 "$tmp/show-source.txt"; exit 1; }
{
  echo "script sha256 $(sha256sum "$self" | cut -d' ' -f1)"
  echo "Mathlib commit $commit"
  echo "cache fetched, ended $fetched; the last lines its tool printed:"
  tr -d '\r' < "$tmp/cache-get.log" | grep -v '^$' | tail -n 4 | sed 's/^/    /'
  echo "constants in the import closure of Mathlib, cached build: $(wc -l < "$tmp/names-cache.txt")"
  echo "constants in the import closure of Mathlib, built from source: $(wc -l < "$tmp/names-source.txt")"
  echo "sha256 of the list of names, cached build: $(sha256sum "$tmp/names-cache.txt" | cut -d' ' -f1)"
  echo "sha256 of the list of names, built from source: $(sha256sum "$tmp/names-source.txt" | cut -d' ' -f1)"
  echo "ONLY IN THE BUILD FROM SOURCE $(LC_ALL=C comm -13 "$tmp/names-cache.txt" "$tmp/names-source.txt" | wc -l)"
  LC_ALL=C comm -13 "$tmp/names-cache.txt" "$tmp/names-source.txt" | sed 's/^/  /'
  echo "ONLY IN THE CACHED BUILD $(LC_ALL=C comm -23 "$tmp/names-cache.txt" "$tmp/names-source.txt" | wc -l)"
  LC_ALL=C comm -23 "$tmp/names-cache.txt" "$tmp/names-source.txt" | sed 's/^/  /'
  echo "IN BOTH $(sed -n 's/^N //p' "$tmp/common.txt")"
  echo "IN BOTH, TYPES WITH DIFFERENT HASHES $(grep -c '^T ' "$tmp/common.txt")"
  sed -n 's/^T /  /p' "$tmp/common.txt"
  echo "IN BOTH, VALUES WITH DIFFERENT HASHES $(grep -c '^V ' "$tmp/common.txt")"
  sed -n 's/^V /  /p' "$tmp/common.txt"
  echo "THE STATEMENTS THAT DIFFER, AS THE CACHED BUILD HAS THEM"
  sed 's/^/    /' "$tmp/show-cache.txt"
  echo "THE STATEMENTS THAT DIFFER, AS THE BUILD FROM SOURCE HAS THEM"
  sed 's/^/    /' "$tmp/show-source.txt"
} > "$out/mathlib-diff.txt"
cat "$out/mathlib-diff.txt"
