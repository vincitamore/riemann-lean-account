#!/usr/bin/env bash
# Compares the installed Lean toolchain, file by file, with the release archive that the Lean
# project publishes on GitHub. The kernel recognises some constants of Lean's own library by
# name (the natural numbers and their operations, strings, the quotient type) and takes their
# definitions from the toolchain's compiled files, so those files are part of what every check
# trusts. elan installs the toolchain from another host; this fetches the GitHub copy.
# Usage, from the working directory of setup.sh:   bash toolchain.sh out-dir
. "$HOME/.elan/env"
out=$(mkdir -p "$1" && cd "$1" && pwd)
ver=$(sed 's/.*:v//' lean/lean-toolchain)
pre=$(cd lean && lean --print-prefix)
url=https://github.com/leanprover/lean4/releases/download/v$ver/lean-$ver-linux.tar.zst
tmp=$(mktemp -d)
curl -sSfL --retry 5 -o "$tmp/release.tar.zst" "$url" || { echo "TOOLCHAIN-FAILED download"; exit 1; }
{
  echo "release archive $url"
  echo "release archive sha256 $(sha256sum "$tmp/release.tar.zst" | cut -d' ' -f1)"
  mkdir "$tmp/release" && tar --zstd -xf "$tmp/release.tar.zst" -C "$tmp/release" --strip-components=1
  (cd "$tmp/release" && find . -type f | LC_ALL=C sort | xargs -d '\n' sha256sum) > "$tmp/release.sha"
  (cd "$pre" && find . -type f | LC_ALL=C sort | xargs -d '\n' sha256sum) > "$tmp/installed.sha"
  echo "files in the release archive $(wc -l < "$tmp/release.sha")"
  echo "files in the installed toolchain $(wc -l < "$tmp/installed.sha")"
  diff "$tmp/release.sha" "$tmp/installed.sha" > "$tmp/diff.txt"
  echo "files that differ, or are in one and not the other: $(grep -c '^[<>]' "$tmp/diff.txt")"
  head -20 "$tmp/diff.txt"
  echo "sha256 of the compiled Init/Prelude: $(grep ' ./lib/lean/Init/Prelude.olean$' "$tmp/installed.sha" | cut -d' ' -f1)"
  echo "sha256 of the list of the installed files and their hashes: $(sha256sum "$tmp/installed.sha" | cut -d' ' -f1)"
} > "$out/toolchain.txt"
cat "$out/toolchain.txt"
rm -rf "$tmp"
grep -q '^files that differ, or are in one and not the other: 0$' "$out/toolchain.txt" && echo TOOLCHAIN-OK || echo TOOLCHAIN-DIFFERS
