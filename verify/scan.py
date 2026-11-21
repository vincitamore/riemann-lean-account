#!/usr/bin/env python3
"""Static inspection of the archive, before any build.

Usage:  python3 scan.py lean.tar.gz > scan.txt

Streams the tarball without unpacking it and prints:
  * its size and SHA-256, the number of Lean files and of lines, the other files;
  * every occurrence, anywhere in the Lean text (comments included), of the words by which a
    Lean development can state something without proving it, bypass the kernel, or run code
    while a file is compiled; a word counts wherever it stands as a whole word, also after a dot;
  * `axiom` declarations, `partial def` declarations, declarations of syntax or elaborators by
    their keywords, the options that files set, and the files that begin with `module`;
  * whether every import names a file of the archive or a module of a known outside package,
    whether the import graph is acyclic, and how many files are in the import closure of Main.
    (That the outside modules exist is shown by the build, not here.)

A text scan can fail to find a defect; it cannot confirm a proof. The build, the axiom check
and the kernel replay are what certify the theorem.
"""
import collections
import hashlib
import re
import sys
import tarfile

# Words by which something can be stated without proof or put past the kernel.
WORDS = ["sorry", "admit", "native_decide", "implemented_by", "extern", "unsafe", "opaque", "csimp",
         "skipKernelTC", "addDeclWithoutChecking", "ofReduceBool", "ofReduceNat", "trustCompiler", "lcProof",
         "sorryAx", "doCheck", "ofKernelEnv", "reduceBool", "reduceNat"]
# Words of code that adds declarations by program or runs while a file is compiled. These are
# reported; what such code adds goes through the kernel unless it uses one of the words above.
REPORTED = ["addDeclCore", "addDecl", "addAndCompile", "setEnv", "modifyEnv", "evalConst", "evalDecl", "#eval",
            "command_elab", "term_elab", "builtin_command_elab", "builtin_term_elab", "simproc", "dsimproc"]
# a whole word; a dot before it is allowed, so that `Lean.trustCompiler` and `debug.skipKernelTC` count
WORD_RX = {w: re.compile(r"(?<![\w])" + re.escape(w) + r"(?![\w])") for w in WORDS + REPORTED}
OPTION_RX = re.compile(r"\bset_option\s+([\w.]+)")
MODULE_RX = re.compile(r"^module\s*$", re.M)
AXIOM_RX = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*axiom\s", re.M)
PARTIAL_RX = re.compile(r"^\s*(?:private\s+|protected\s+|@\[[^\]]*\]\s*)*partial\s+def\s+(\S+)", re.M)
ELAB_RX = re.compile(r"^\s*(?:scoped\s+|local\s+)?(elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat|"
                     r"initialize|builtin_initialize|run_cmd|run_meta|run_elab)\b", re.M)
IMPORT_RX = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?(\S+)", re.M)
# Roots that are not part of the archive: Lean's own library and Mathlib with its dependencies.
EXTERNAL = {"Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible",
            "LeanSearchClient", "ImportGraph", "Lake", "Cli"}


def main() -> None:
    path = sys.argv[1]
    h = hashlib.sha256()
    size = 0
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 22), b""):
            h.update(block)
            size += len(block)
    print(f"archive bytes {size}")
    print(f"archive sha256 {h.hexdigest()}")

    lean_files = 0
    lines = 0
    other = []
    hits = {w: [] for w in WORDS + REPORTED}
    axioms, partials, elabs = [], [], collections.Counter()
    elab_files = collections.defaultdict(set)
    options = collections.Counter()
    module_files = []
    imports = {}
    main_lines = None
    with tarfile.open(path, "r|gz") as tar:
        for m in tar:
            if not m.isfile():
                continue
            name = m.name
            if not name.endswith(".lean"):
                other.append(name)
                continue
            data = tar.extractfile(m).read()
            lean_files += 1
            lines += data.count(b"\n")
            text = data.decode("utf-8")
            i = name.find("src/")
            mod = name[i + 4:-5].replace("/", ".") if i >= 0 else name[:-5].replace("/", ".")
            if mod == "Main":
                main_lines = text.count("\n")
            imports[mod] = IMPORT_RX.findall(text)
            for w, rx in WORD_RX.items():
                if w in text:
                    for mm in rx.finditer(text):
                        hits[w].append(f"{name}:{text.count(chr(10), 0, mm.start()) + 1}")
            if "axiom" in text:
                for mm in AXIOM_RX.finditer(text):
                    axioms.append(f"{name}:{text.count(chr(10), 0, mm.start()) + 1}")
            if "partial" in text:
                for mm in PARTIAL_RX.finditer(text):
                    partials.append(f"{name}:{text.count(chr(10), 0, mm.start()) + 1} {mm.group(1)}")
            for mm in ELAB_RX.finditer(text):
                elabs[mm.group(1)] += 1
                elab_files[mm.group(1)].add(name)
            if "set_option" in text:
                for mm in OPTION_RX.finditer(text):
                    options[mm.group(1)] += 1
            if MODULE_RX.search(text):
                module_files.append(name)

    print(f"lean files {lean_files}")
    print(f"lines in lean files {lines}")
    print(f"other files {len(other)}: {' '.join(sorted(other))}")
    print(f"lines in Main.lean {main_lines}")
    print()
    print("OCCURRENCES OF WORDS (whole words, also after a dot, anywhere in the text, comments included)")
    for w in WORDS:
        print(f"  {w} {len(hits[w])}")
        for loc in hits[w][:40]:
            print(f"    {loc}")
    print("OTHER WORDS REPORTED (the same matching; code that adds declarations or runs at compile time)")
    for w in REPORTED:
        print(f"  {w} {len(hits[w])} in {len({loc.rsplit(':', 1)[0] for loc in hits[w]})} files")
        for loc in hits[w][:40]:
            print(f"    {loc}")
    print(f"axiom declarations {len(axioms)}")
    for loc in axioms[:40]:
        print(f"    {loc}")
    print(f"partial def declarations {len(partials)}")
    for loc in partials:
        print(f"    {loc}")
    print("SYNTAX, ELABORATORS AND CODE RUN AT ELABORATION (declarations by keyword, with their files)")
    for k in sorted(elabs):
        print(f"  {k} {elabs[k]}")
        for fn in sorted(elab_files[k]):
            print(f"    {fn}")
    print("OPTIONS SET (set_option, by option, with the number of occurrences)")
    for k in sorted(options):
        print(f"  {k} {options[k]}")
    print(f"files with a line that is the word module {len(module_files)}")
    for fn in module_files[:40]:
        print(f"    {fn}")
    print()

    # imports
    mods = set(imports)
    ext = collections.Counter()
    dangling = []
    edges = 0
    for mod, deps in imports.items():
        for d in deps:
            edges += 1
            if d in mods:
                continue
            root = d.split(".")[0]
            if root in EXTERNAL:
                ext[root] += 1
            else:
                dangling.append(f"{mod} imports {d}")
    print(f"import lines {edges}")
    print("imports of modules outside the archive, by root: " + ", ".join(f"{r} {n}" for r, n in sorted(ext.items())))
    print(f"files importing all of Mathlib {sum(1 for d in imports.values() if 'Mathlib' in d)}")
    print(f"imports that resolve to nothing {len(dangling)}")
    for d in dangling[:40]:
        print(f"    {d}")

    # acyclicity (Kahn) and depth
    indeg = {m: 0 for m in mods}
    users = collections.defaultdict(list)
    for mod, deps in imports.items():
        for d in set(deps):
            if d in mods:
                indeg[mod] += 1
                users[d].append(mod)
    queue = collections.deque(m for m, k in indeg.items() if k == 0)
    depth = {m: 1 for m in queue}
    done = 0
    while queue:
        m = queue.popleft()
        done += 1
        for u in users[m]:
            depth[u] = max(depth.get(u, 1), depth[m] + 1)
            indeg[u] -= 1
            if indeg[u] == 0:
                queue.append(u)
    print(f"import graph acyclic {done == len(mods)} (ordered {done} of {len(mods)}); longest chain {max(depth.values())}")

    # closure of Main
    seen = {"Main"}
    stack = ["Main"]
    while stack:
        m = stack.pop()
        for d in imports.get(m, ()):
            if d in mods and d not in seen:
                seen.add(d)
                stack.append(d)
    print(f"files in the import closure of Main {len(seen)} of {len(mods)}")
    missing = sorted(mods - seen)
    for m in missing[:40]:
        print(f"    not imported: {m}")


if __name__ == "__main__":
    main()
