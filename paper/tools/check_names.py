"""Check every Lean name the paper cites against the dependency cone of the main theorem.

Usage: python tools/check_names.py ../verify/results [--list]

Reads every \\lean{...} of the hand-written sections and of one-page.tex. By default a cited
name must be the whole of, or the last components of, at least one name of the archive, and
every name of the archive that ends so must be in the cone (cut-in.txt.xz). tools/names.txt
gives the other cases, one per line, as `<class> <cited name> [<full name>]`:

  pick     several declarations end with the cited name and not all are in the cone: the full
           name of the one meant is given, and it must be in the cone
  off      the paper says the declaration is outside the cone: every name of the archive that
           ends so must be outside it (or the full name given must be)
  five     in the cone of the five theorems of Main.lean and not in that of riemannHypothesis
           (cut-five-extra.txt)
  mathlib  declared in Mathlib or in Lean's library, not in the archive
  word     a keyword, command, file, directory, module or other text that is not a declaration

The script stops with an error if a cited name fails its class, or if names.txt lists a name
the paper does not cite. With --list it prints each name with its class.
"""
import lzma
import pathlib
import re
import sys


def load(path: pathlib.Path) -> tuple[set, dict]:
    """Full names, and for every dotted suffix the number of full names that end with it."""
    full: set = set()
    suffixes: dict = {}
    with lzma.open(path, "rt", encoding="utf-8") as fh:
        for line in fh:
            _, _, name = line.rstrip("\n").partition(" ")
            if name and name not in full:
                full.add(name)
                parts = name.split(".")
                for i in range(len(parts)):
                    s = ".".join(parts[i:])
                    suffixes[s] = suffixes.get(s, 0) + 1
    return full, suffixes


def main() -> None:
    res = pathlib.Path(sys.argv[1])
    here = pathlib.Path(__file__).resolve().parent.parent
    classes: dict[str, tuple] = {}
    for line in (here / "tools" / "names.txt").read_text(encoding="utf-8").splitlines():
        if line.strip() and not line.startswith("#"):
            cls, rest = line.strip().split(None, 1)
            if cls == "pick" or (cls == "off" and len(rest.split()) == 2 and "." in rest.split()[1]):
                name, full = rest.rsplit(None, 1)
            else:
                name, full = rest, ""
            classes[name.strip()] = (cls, full.strip())
    cited: dict[str, list] = {}
    files = [p for p in sorted((here / "sections").glob("*.tex"))
             if p.name not in ("appendix-rows.tex", "appendix-audit.tex")] + [here / "one-page.tex", here / "version.tex"]
    for p in files:
        text = p.read_text(encoding="utf-8")
        text = text.split("\\begin{document}", 1)[-1]
        for m in re.finditer(r"\\lean\{((?:[^{}]|\{[^{}]*\})*)\}(\\textsubscript\{\\ttfamily 2\})?", text):
            name = m.group(1).replace("\\_", "_").replace("\\#", "#").replace("\\allowbreak", "").replace("{}", "").strip()
            if m.group(2):
                name += "\u2082"
            cited.setdefault(name, []).append(p.name)
    in_full, in_suffix = load(res / "cut-in.txt.xz")
    out_full, out_suffix = load(res / "cut-out.txt.xz")
    five = {l.strip() for l in (res / "cut-five-extra.txt").read_text(encoding="utf-8").splitlines() if l.strip()}
    bad = []
    counts: dict[str, int] = {}
    for name in sorted(cited):
        cls, full = classes.get(name, ("cone", ""))
        counts[cls] = counts.get(cls, 0) + 1
        n_in, n_out = in_suffix.get(name, 0), out_suffix.get(name, 0)
        if cls == "cone":
            ok = n_in > 0 and n_out == 0
        elif cls == "pick":
            ok = full in in_full and (full == name or full.endswith("." + name)) and n_out > 0
        elif cls == "off":
            ok = (full in out_full and full not in in_full and full.endswith(name)) if full else (n_out > 0 and n_in == 0)
        elif cls == "five":
            ok = name in five and n_in == 0
        else:
            ok = cls in ("mathlib", "word")  # not names of the archive: nothing to look up
        if not ok:
            bad.append((name, cls, n_in, n_out, sorted(set(cited[name]))))
        if "--list" in sys.argv:
            print(f"{cls:8} {'ok ' if ok else 'BAD'} {name}  ({n_in} in the cone, {n_out} outside)")
    unused = sorted(n for n in classes if n not in cited)
    for name, cls, n_in, n_out, where in bad:
        print(f"NOT AS CLASSED: {name} (class {cls}; names of the archive ending so: {n_in} in the cone, "
              f"{n_out} outside) in {', '.join(where)}")
    for n in unused:
        print(f"names.txt lists a name the paper does not cite: {n}")
    print(f"{len(cited)} names cited: " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())))
    if bad or unused:
        sys.exit(1)


if __name__ == "__main__":
    main()
