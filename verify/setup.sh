#!/usr/bin/env bash
# Fetches the archive from its author's site, checks its hash, unpacks it, installs the pinned
# toolchain and provides Mathlib at the pinned commit: compiled from source, or, with
# MATHLIB=cache, from the community's prebuilt cache (faster by about an hour on 32 threads).
# Run in an empty working directory with about 150 GB free:   bash setup.sh
# The source build writes its log to mathlib-build.log in that directory.
set -uo pipefail
for t in git curl zstd tar sha256sum; do command -v $t >/dev/null || { echo "SETUP-FAILED missing $t"; exit 1; }; done
command -v elan >/dev/null || curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
. "$HOME/.elan/env"
for i in $(seq -w 1 14); do
  curl -sSfL --retry 5 -o lean.tar.gz.part$i https://alpo.ge/lean.tar.gz.part$i || { echo "SETUP-FAILED part$i"; exit 1; }
done
cat lean.tar.gz.part?? > lean.tar.gz && rm lean.tar.gz.part??
echo "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc  lean.tar.gz" | sha256sum -c - || { echo "SETUP-FAILED hash"; exit 1; }
tar xzf lean.tar.gz && cd lean || { echo "SETUP-FAILED untar"; exit 1; }
echo "lean files: $(find src -name '*.lean' | wc -l)"
work=$(cd .. && pwd)
if [ "${MATHLIB:-source}" = cache ]; then
  lake exe cache get 2>&1 | tail -3
else
  echo "compiled files before the Mathlib build: $(find .lake -name '*.olean' 2>/dev/null | wc -l)"
  printf 'MATHLIB-START %(%s)T\n' -1 > "$work/mathlib-build.log"
  LEAN_NUM_THREADS=$(nproc) lake build Mathlib 2>&1 | while IFS= read -r l; do printf '%(%s)T %s\n' -1 "$l"; done >> "$work/mathlib-build.log"
  printf 'MATHLIB-EXIT %s\n' "${PIPESTATUS[0]}" >> "$work/mathlib-build.log"
  printf 'MATHLIB-END %(%s)T\n' -1 >> "$work/mathlib-build.log"
  tail -4 "$work/mathlib-build.log"
  grep -q '^MATHLIB-EXIT 0' "$work/mathlib-build.log" || { echo "SETUP-FAILED mathlib"; exit 1; }
fi
lean --version
lake build Statements 2>&1 | tail -5
[ -f .lake/build/lib/lean/Statements.olean ] && echo SETUP-DONE || echo "SETUP-FAILED statements"
