#!/usr/bin/env bash
# Run beside the build. Lake writes a `.setup.json` for every module, listing the module's whole
# import closure: about 5 MB for a module that imports all of Mathlib, so for the 175,187
# modules of this archive several hundred gigabytes. A module's file is read once, when its
# compile starts, and lake accepts a built module without it, so each is deleted as soon as the
# module's .olean exists. Each line of the output gives the time, the number of files removed
# in that pass with their total size in bytes, and the disk in use. Stop it when the build has
# ended.
cd lean/.lake/build || exit 1
while true; do
  n=0; b=0
  while read -r size f; do
    m=${f#ir/}; m=${m%.setup.json}
    [ -f "lib/lean/$m.olean" ] && rm -f "$f" && n=$((n + 1)) && b=$((b + size))
  done < <(find ir -name '*.setup.json' -printf '%s %p\n')
  printf '%(%s)T removed %s bytes %s, disk %s\n' -1 "$n" "$b" "$(df -h . | awk 'END {print $3 " used of " $2}')"
  sleep 60
done
