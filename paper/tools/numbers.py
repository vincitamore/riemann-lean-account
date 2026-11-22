"""Write numbers.tex: every measured number of the paper, read from the results files.

Usage: python tools/numbers.py ../verify/results numbers.tex

Nothing in the paper types a measured number by hand. This script reads the output of the
verification programs (scan.txt, build-summary.txt, cut-result.txt, cut-five-extra.txt,
replay-summary.txt) and the counts of the literature table (refs/rows-counts.json), computes the
derived figures (differences, shares) and writes one LaTeX macro per number. It stops with an
error if a number it needs is missing or if two sources disagree.
"""
import json
import pathlib
import re
import sys


def grab(text: str, pattern: str, what: str) -> str:
    m = re.search(pattern, text, re.M)
    if not m:
        sys.exit(f"numbers.py: cannot find {what} ({pattern!r})")
    return m.group(1)


def fmt(n: int) -> str:
    return f"{n:,}".replace(",", "{,}")


def pct(a: int, b: int) -> str:
    return f"{round(100 * a / b)}\\%"


def main() -> None:
    res = pathlib.Path(sys.argv[1])
    dst = pathlib.Path(sys.argv[2])
    here = pathlib.Path(__file__).resolve().parent.parent
    scan = (res / "scan.txt").read_text(encoding="utf-8")
    build = (res / "build-summary.txt").read_text(encoding="utf-8")
    cut = (res / "cut-result.txt").read_text(encoding="utf-8")
    five = [l for l in (res / "cut-five-extra.txt").read_text(encoding="utf-8").splitlines() if l.strip()]
    rep = (res / "replay-summary.txt").read_text(encoding="utf-8")
    rows = json.loads((here / "refs" / "rows-counts.json").read_text(encoding="utf-8"))

    out: list[tuple[str, str, str]] = []  # (macro, value, comment)

    def put(name: str, value: str, comment: str) -> None:
        out.append((name, value, comment))

    # the archive (scan.txt)
    files = int(grab(scan, r"^lean files (\d+)", "the number of Lean files"))
    put("filecount", fmt(files), "scan.txt: lean files")
    put("linecount", fmt(int(grab(scan, r"^lines in lean files (\d+)", "the line count"))), "scan.txt")
    put("linemillions", str(round(int(grab(scan, r"^lines in lean files (\d+)", "the line count")) / 1e6)), "computed")
    put("archivebytes", fmt(int(grab(scan, r"^archive bytes (\d+)", "the archive size"))), "scan.txt")
    sha = grab(scan, r"^archive sha256 ([0-9a-f]{64})", "the archive hash")
    put("archivesha", sha, "scan.txt")
    put("archiveshaA", sha[:32], "first half, for display")
    put("archiveshaB", sha[32:], "second half, for display")
    put("otherfiles", grab(scan, r"^other files (\d+)", "the count of build files"), "scan.txt")
    put("mainlines", grab(scan, r"^lines in Main\.lean (\d+)", "the length of Main.lean"), "scan.txt")
    put("scanmacros", grab(scan, r"^\s+macro (\d+)", "the count of macros"), "scan.txt")
    put("scanelabs", grab(scan, r"^\s+elab (\d+)", "the count of elaborators"), "scan.txt")
    put("scanruncmd", grab(scan, r"^\s+run_cmd (\d+)", "the count of run_cmd"), "scan.txt")

    def files_under(keyword: str) -> int:
        block = re.search(rf"^  {keyword} \d+\n((?:    \S.*\n)*)", scan, re.M)
        return len(block.group(1).splitlines()) if block else 0
    put("scanelabfiles", str(files_under("elab")), "scan.txt: files listed under elab")
    put("scanruncmdfiles", str(files_under("run_cmd")), "scan.txt: files listed under run_cmd")
    put("scanpartial", grab(scan, r"^partial def declarations (\d+)", "the count of partial defs"), "scan.txt")
    put("scandepth", grab(scan, r"longest chain (\d+)", "the depth of the import graph"), "scan.txt")
    put("scanimports", fmt(int(grab(scan, r"^import lines (\d+)", "the count of import lines"))), "scan.txt")
    put("scanallmathlib", fmt(int(grab(scan, r"^files importing all of Mathlib (\d+)", "files importing Mathlib"))), "scan.txt")
    words = re.findall(r"^  (\w+) (\d+)$", scan.split("OCCURRENCES OF WORDS", 1)[1].split("OTHER WORDS REPORTED", 1)[0], re.M)
    for needed in ("sorry", "admit", "native_decide", "implemented_by", "extern", "unsafe", "opaque", "csimp",
                   "skipKernelTC", "addDeclWithoutChecking", "doCheck", "ofReduceBool"):
        if needed not in [w[0] for w in words]:
            sys.exit(f"numbers.py: the scan did not look for the word {needed}")
    for word in words:
        if word[1] != "0":
            sys.exit(f"numbers.py: the scan found the word {word[0]}")
    if "also after a dot" not in scan:
        sys.exit("numbers.py: scan.txt is from the scan that could not match a word after a dot")
    if grab(scan, r"^files with a line that is the word module (\d+)", "the files that begin with module") != "0":
        sys.exit("numbers.py: a file of the archive uses the module system; the text says none does")
    if grab(scan, r"^  #eval (\d+) in", "the count of #eval") != "0":
        sys.exit("numbers.py: the scan found #eval; the text says no file contains it")
    if grab(scan, r"^  addDecl \d+ in (\d+) files", "the files that call addDecl") != "1":
        sys.exit("numbers.py: addDecl is not called in exactly one file; the text says one")
    for other in ("addDeclCore", "addAndCompile", "setEnv", "evalConst", "evalDecl"):
        if grab(scan, rf"^  {other} (\d+) in", f"the count of {other}") != "0":
            sys.exit(f"numbers.py: the scan found {other}; the text says the copying command is the one place that adds a declaration")
    if sorted(re.findall(r"^imports of modules outside the archive, by root: (.*)$", scan, re.M)[0].replace(",", "").split()[0::2]) != ["Batteries", "Lean", "Mathlib"]:
        sys.exit("numbers.py: the outside imports are not those the text names")
    if grab(scan, r"^axiom declarations (\d+)", "the count of axiom declarations") != "0":
        sys.exit("numbers.py: the scan found an axiom declaration")
    if grab(scan, r"^imports that resolve to nothing (\d+)", "unresolved imports") != "0":
        sys.exit("numbers.py: the scan found an import that resolves to nothing")
    if not re.search(rf"^files in the import closure of Main {files} of {files}$", scan, re.M):
        sys.exit("numbers.py: not every file is in the import closure of Main")

    # the build (build-summary.txt, written by summary.sh)
    def build_facts(text: str, prefix: str, where: str) -> None:
        start = int(grab(text, r"^START (\d+)", "the build start"))
        end = int(grab(text, r"^END (\d+)", "the build end"))
        if grab(text, r"^LAKE-EXIT (\d+)", "lake's exit code") != "0":
            sys.exit(f"numbers.py: {where} records a failed build")
        put(prefix + "hours", f"{(end - start) / 3600:.1f}", f"{where}: END minus START")
        put(prefix + "jobs", fmt(int(grab(text, r"Build completed successfully \((\d+) jobs\)", "the job count"))), where)
        put(prefix + "threads", grab(text, r"^START \d+ threads=(\d+)", "the thread count"), where)
        if int(grab(text, r"^oleans (\d+)", "the count of compiled modules")) != files:
            sys.exit(f"numbers.py: {where}: compiled modules and Lean files differ in number")
        put(prefix + "cpu", grab(text, r"^model name\s*:\s*(.+)$", "the processor").strip(), where)
    # A second run exists when the first run's files have been moved to results/run1/. Until
    # then the files in results/ are the first run's, in the earlier output format, and the
    # numbers that only the second run gives are left out (\ifsecondrun in the text).
    second = (res / "run1").is_dir()
    build_facts(build, "build", "build-summary.txt")
    put("leanversion", grab(build, r"leanprover/lean4:v([0-9.]+)", "the Lean version"), "build-summary.txt")
    # the revision of the manifest entry named mathlib: in lake-manifest.json, and so in the
    # lines summary.sh prints, an entry's "inputRev" is the line after its "name"
    mrev = re.search(r'"name": "mathlib",?\s*\n\s*"inputRev": "([0-9a-f]{40})"', build)
    if not mrev and len(re.findall(r'"inputRev": "[0-9a-f]{40}"', build)) == 1:
        mrev = re.search(r'"inputRev": "([0-9a-f]{40})"', build)
    if not mrev:
        sys.exit("numbers.py: cannot find the Mathlib revision in build-summary.txt")
    put("mathlibrev", mrev.group(1), "build-summary.txt")
    if second:
        ms = int(grab(build, r"^MATHLIB-START (\d+)", "the start of the Mathlib build"))
        me = int(grab(build, r"^MATHLIB-END (\d+)", "the end of the Mathlib build"))
        if grab(build, r"^MATHLIB-EXIT (\d+)", "the exit code of the Mathlib build") != "0":
            sys.exit("numbers.py: the Mathlib build failed")
        put("mathlibminutes", str(round((me - ms) / 60)), "build-summary.txt: MATHLIB-END minus MATHLIB-START")
        put("mathlibjobs", fmt(int(grab(build, r"^mathlib-jobs (\d+)", "the Mathlib job count"))), "build-summary.txt")
        put("mathlibmodules", fmt(int(grab(build, r"^mathlib-modules-built (\d+)", "the Mathlib modules built"))), "build-summary.txt")
        put("diskpeak", grab(build, r"^disk-peak-GB (\d+)", "the peak of the disk"), "build-summary.txt")
        sf = re.search(r"^setup-files-measured (\d+) files (\d+) bytes", build, re.M)
        if not sf or int(sf.group(1)) == 0:
            sys.exit("numbers.py: build-summary.txt has no measurement of the setup files")
        put("setupfilemb", f"{int(sf.group(2)) / int(sf.group(1)) / 1e6:.1f}", "build-summary.txt: bytes over files")
        put("setupallgb", str(round(int(sf.group(2)) / int(sf.group(1)) * files / 1e9)), "computed: that size for every module")
        put("memorylimit", grab(build, r"^memory-limit (\d+) GB", "the container's memory limit"), "build-summary.txt")
        put("compiledgb", str(round(int(grab(build, r"^compiled-bytes (\d+)", "the size of the compiled files")) / 1e9)), "build-summary.txt: compiled-bytes")
        first = res / "run1" / "build-summary.txt"
        build_facts(first.read_text(encoding="utf-8"), "firstbuild", "run1/build-summary.txt")

    # the lists of names (cut-in.txt.xz, cut-out.txt.xz): one line "<kind> <name>" for each module
    # that declares the name. Counted here by distinct name.
    import lzma
    kinds_in: dict[str, set] = {}
    kinds_out: dict[str, set] = {}
    lines_t = 0
    for path, table in ((res / "cut-in.txt.xz", kinds_in), (res / "cut-out.txt.xz", kinds_out)):
        with lzma.open(path, "rt", encoding="utf-8") as fh:
            for line in fh:
                kind, _, nm = line.rstrip("\n").partition(" ")
                if nm:
                    table.setdefault(kind, set()).add(nm)
                    lines_t += kind == "T"

    def n_in(k: str) -> int:
        return len(kinds_in.get(k, ()))

    def n_out(k: str) -> int:
        return len(kinds_out.get(k, ()))
    extra = (set(kinds_in) | set(kinds_out)) - set("TDICRO")
    if extra:
        sys.exit(f"numbers.py: the lists contain a kind of declaration not expected: {sorted(extra)}")
    both = set().union(*kinds_in.values()) & set().union(*kinds_out.values())
    if both:
        sys.exit(f"numbers.py: {len(both)} names are in both lists")
    names_in = sum(len(s) for s in kinds_in.values())
    names = names_in + sum(len(s) for s in kinds_out.values())
    t, tin = n_in("T") + n_out("T"), n_in("T")
    d, din = n_in("D") + n_out("D"), n_in("D")
    drec = sum(1 for s in (kinds_in.get("D", set()), kinds_out.get("D", set())) for nm in s if nm.endswith("._unsafe_rec"))
    if any(nm.endswith("._unsafe_rec") for nm in kinds_in.get("D", ())):
        sys.exit("numbers.py: a compiled form of a recursive definition is in the cone")

    # the cone (cut-result.txt)
    cone = int(grab(cut, r"^CONE-SIZE (\d+)", "the cone size"))
    cone5 = int(grab(cut, r"^CONE-SIZE-FIVE-THEOREMS (\d+)", "the five-theorem cone size"))
    if cone5 - cone != len(five):
        sys.exit(f"numbers.py: the cones differ by {cone5 - cone} but cut-five-extra.txt has {len(five)} lines")
    put("conesize", fmt(cone), "cut-result.txt")
    put("conefive", fmt(cone5), "cut-result.txt")
    put("conefiveextra", str(cone5 - cone), "difference of the two")
    put("conearchive", fmt(names_in), "the lists: names of the archive in the cone")
    put("conerest", fmt(cone - names_in), "CONE-SIZE minus the archive's names in the cone")
    by_decl_t = int(grab(cut, r"^PROJECT-THEOREMS total (\d+)", "the theorem declarations"))
    if by_decl_t != lines_t:
        sys.exit("numbers.py: cut-result.txt and the lists disagree on the number of theorem declarations")
    if (int(grab(cut, r"^PROJECT-DEFINITIONS total (\d+)", "the definitions")), int(grab(cut, r"^PROJECT-DEFINITIONS total \d+ in-cone (\d+)", "the definitions in the cone"))) != (d, din):
        sys.exit("numbers.py: cut-result.txt and the lists disagree on the definitions")
    m = re.search(r"^CONE-NAMES archive (\d+) mathlib (\d+) other (\d+)", cut, re.M)
    if m:  # the later output format prints the by-name counts itself: they must agree with the lists
        ca, cm, co = map(int, m.groups())
        if ca + cm + co != cone or ca != names_in:
            sys.exit("numbers.py: CONE-NAMES does not agree with CONE-SIZE and the lists")
        put("conemathlib", fmt(cm), "cut-result.txt")
        put("coneother", fmt(co), "cut-result.txt")
        if tuple(map(int, re.search(r"PROJECT-NAMES total (\d+) in-cone (\d+)", cut).groups())) != (names, names_in):
            sys.exit("numbers.py: the lists of names and cut-result.txt disagree on the number of names")
        if tuple(map(int, re.search(r"PROJECT-THEOREM-NAMES total (\d+) in-cone (\d+)", cut).groups())) != (t, tin):
            sys.exit("numbers.py: the lists of names and cut-result.txt disagree on the theorems")
        if int(re.search(r"compiled-recursion-forms (\d+)", cut).group(1)) != drec:
            sys.exit("numbers.py: the lists of names and cut-result.txt disagree on the compiled forms")
    put("projnames", fmt(names), "the lists, by name")
    put("projnamesout", fmt(names - names_in), "the lists, by name")
    put("projtheorems", fmt(t), "the lists, by name")
    put("coneprojtheorems", fmt(tin), "the lists, by name")
    put("unusedtheorems", fmt(t - tin), "difference")
    put("repeatedtheorems", fmt(by_decl_t - t), "theorem declarations minus theorem names")
    put("theoremshare", pct(tin, t), "computed")
    put("projdefs", fmt(d), "the lists, by name")
    put("coneprojdefs", fmt(din), "the lists, by name")
    put("defshare", pct(din, d), "computed")
    put("projunsaferec", fmt(drec), "the lists: definitions whose name ends in _unsafe_rec")
    m = re.search(r"PROJECT-MODULES with-constants (\d+) touching-cone (\d+)", cut)
    mods, mods_in = map(int, m.groups())
    put("projmodules", fmt(mods), "cut-result.txt")
    put("coneprojmodules", fmt(mods_in), "cut-result.txt")
    put("moduleshare", pct(mods_in, mods), "computed")
    put("unusedmodules", fmt(files - mods_in), "Lean files that declare nothing of the cone")
    put("emptymodules", fmt(files - mods), "Lean files that declare nothing")
    if "MODULES-BY-ROOT" in cut:
        block = cut.split("MODULES-BY-ROOT", 1)[1].split("SHORT-NAME-PROBES", 1)[0]
        total_files = 0
        named = ("Development", "Formalism", "GroundTheory", "ReciprocityTheory", "CompanionTheory", "PositivityTheory")
        other_unused, other_roots, named_unused = 0, 0, 0
        for line in block.splitlines()[1:]:
            p = line.split()
            if len(p) == 4:
                root, allm, decl, touch = p[0], int(p[1]), int(p[2]), int(p[3])
                total_files += allm
                put("mods" + root + "All", fmt(allm), "cut-result.txt MODULES-BY-ROOT")
                put("mods" + root + "Unused", fmt(allm - touch), "modules of the directory minus those touching the cone")
                if root in named:
                    named_unused += allm - touch
                elif allm - touch:
                    other_unused += allm - touch
                    other_roots += 1
        if total_files != files:
            sys.exit(f"numbers.py: MODULES-BY-ROOT adds up to {total_files}, not {files}")
        if named_unused + other_unused != files - mods_in:
            sys.exit("numbers.py: the unused modules by directory do not add up to the total")
        put("modsOtherUnused", str(other_unused), "cut-result.txt MODULES-BY-ROOT: unused modules outside the six directories named")
        put("modsOtherRoots", ["no", "one", "two", "three", "four", "five", "six", "seven"][other_roots], "the directories they are in")
    elif second:
        sys.exit("numbers.py: the second run's cut-result.txt has no MODULES-BY-ROOT table")
    hub = re.search(r"LITERATURE-HUB theorems (\d+) not-in-cone (\d+)", cut)
    if hub.group(2) != "0":
        sys.exit("numbers.py: a theorem of the literature file is outside the cone")
    put("hubtheorems", hub.group(1), "cut-result.txt")
    put("projopaque", str(n_in("O") + n_out("O")), "the lists: opaque constants of the archive")
    put("coneprojopaque", str(n_in("O")), "the lists: of them in the cone")
    put("projinductives", fmt(n_in("I") + n_out("I")), "the lists: inductive types of the archive")


    # the replay (replay-summary.txt)
    def r(key: str) -> int:
        return int(grab(rep, rf"^{key} (\d+)", key))
    replayed = r("replayed")
    kinds = {k: r(k) for k in ("theorems", "definitions", "opaque", "axioms", "constructors-compared", "recursors-compared")}
    ind = re.search(r"^inductive-types (\d+) in (\d+) blocks", rep, re.M)
    # the first run's program printed no line for the constants of the quotient type
    quot = r("quotient-constants") if second else replayed - sum(kinds.values()) - int(ind.group(1))
    total = sum(kinds.values()) + int(ind.group(1)) + quot
    if total != replayed or quot != 4:
        sys.exit(f"numbers.py: the kinds of the replay add up to {total} with {quot} quotient constants, against {replayed} replayed")
    kinds["quotient-constants"] = quot
    if r("failed") != 0:
        sys.exit("numbers.py: the replay reports failures")
    if "selftest accepts-true true rejects-false true" not in rep:
        sys.exit("numbers.py: the replay's self-test did not pass")
    put("replaymodules", fmt(r("modules")), "replay-summary.txt")
    put("replayconstants", fmt(r("constants")), "replay-summary.txt")
    put("replaydecls", fmt(replayed), "replay-summary.txt")
    put("replayskipped", fmt(r("unsafe-or-partial-not-replayed")), "replay-summary.txt")
    if r("constants") - replayed != r("unsafe-or-partial-not-replayed"):
        sys.exit("numbers.py: constants minus replayed is not the number skipped")
    put("replaytheorems", fmt(kinds["theorems"]), "replay-summary.txt")
    put("replaydefs", fmt(kinds["definitions"]), "replay-summary.txt")
    put("replayopaque", fmt(kinds["opaque"]), "replay-summary.txt")
    put("replayaxioms", str(kinds["axioms"]), "replay-summary.txt")
    put("replayquot", str(quot), "replay-summary.txt: quotient-constants (in the first run's format, the constants replayed less those of the other kinds); checked to be 4")
    put("replayinductives", fmt(int(ind.group(1))), "replay-summary.txt")
    put("replayblocks", fmt(int(ind.group(2))), "replay-summary.txt")
    put("replayctors", fmt(kinds["constructors-compared"]), "replay-summary.txt")
    put("replayrecs", fmt(kinds["recursors-compared"]), "replay-summary.txt")
    put("replayminutes", str(round(r("seconds") / 60)), "replay-summary.txt: seconds / 60")
    if second:
        put("replaythreads", grab(rep, r"^threads (\d+)", "the thread count"), "replay-summary.txt")
        if "(equals replayed: true)" not in rep:
            sys.exit("numbers.py: the replay's kinds do not add up to the number replayed")
        if int(grab(rep, r"^compared-with-the-kernel's-constants (\d+)", "the comparison")) != replayed:
            sys.exit("numbers.py: not every replayed constant was compared with the kernel's")
        dup = re.search(r"^names-declared-more-than-once (\d+), further versions (\d+), of which checked (\d+) and axioms (\d+)", rep, re.M)
        if not dup or int(dup.group(3)) + int(dup.group(4)) != int(dup.group(2)):
            sys.exit("numbers.py: not every further version of a repeated name was checked")
        put("replayrepeatednames", fmt(int(dup.group(1))), "replay-summary.txt")
        put("replayrepeated", fmt(int(dup.group(2))), "replay-summary.txt")
        put("replayrepeatedaxioms", dup.group(4), "replay-summary.txt")
        if dup.group(4) != "0":
            sys.exit("numbers.py: a further version of a repeated name is an axiom; the text says every version was checked")
        ex = re.search(r"^exported-parts-compared (\d+) modules, (\d+) constants", rep, re.M)
        put("replayexportedmodules", fmt(int(ex.group(1))), "replay-summary.txt")
        if int(ex.group(1)) != r("modules") - files:
            sys.exit("numbers.py: the modules whose exported parts were compared are not exactly the modules outside the archive")
        put("replayexported", fmt(int(ex.group(2))), "replay-summary.txt")
        for label in ("CONE-AXIOMS", "CONE-AXIOMS-FIVE-THEOREMS"):
            if grab(cut, rf"^{label} (\[.*\])$", "the axioms of the cone") != "[Classical.choice, Quot.sound, propext]":
                sys.exit(f"numbers.py: {label} is not the three standard axioms")
        prov = (res / "replay-provenance.txt").read_text(encoding="utf-8")
        if "exit code 0" not in prov:
            sys.exit("numbers.py: the replay did not exit with code 0")
        cpu = re.search(r"processor time ([0-9.]+) s user and ([0-9.]+) s system", prov)
        replay_cpu_s = float(cpu.group(1)) + float(cpu.group(2))
        put("replaycpuhours", str(round(replay_cpu_s / 3600)), "replay-provenance.txt")
        replay_sha = grab(prov, r"^program sha256 ([0-9a-f]{64})", "the program hash")
        put("replayprogramsha", replay_sha[:16], "replay-provenance.txt")
        targets = [l for l in (res / "replay-targets.txt").read_text(encoding="utf-8").splitlines() if l.strip()]
        want = ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
                "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"]
        if [l.split(":")[0] for l in targets] != want:
            sys.exit("numbers.py: replay-targets.txt does not report on the five theorems")
        for l in targets:
            if "a theorem, checked by the kernel" not in l or not l.rstrip().endswith("axioms: [Classical.choice, Quot.sound, propext]"):
                sys.exit(f"numbers.py: unexpected report on a theorem: {l}")
        put("replayconeconstants", fmt(int(grab(targets[0], r"depends on (\d+) constants", "the dependencies"))), "replay-targets.txt")
        put("replayconeagrees", "true" if int(grab(targets[0], r"depends on (\d+) constants", "the dependencies")) == cone else "false", "compared with CONE-SIZE")
        # The two runs compared. The first took Mathlib from the cache, the second compiled it;
        # the text says that they agree on the archive and differ by some theorems of Mathlib.
        rep1 = (res / "run1" / "replay-summary.txt").read_text(encoding="utf-8")
        cut1 = (res / "run1" / "cut-result.txt").read_text(encoding="utf-8")

        def by_root(text: str) -> dict:
            rows = {}
            for l in text.split("BY-ROOT", 1)[1].splitlines()[1:]:
                mm = re.match(r"^  (\S+) (\d+) (\d+)$", l)
                if not mm:
                    break
                rows[mm.group(1)] = (int(mm.group(2)), int(mm.group(3)))
            return rows
        r1, r2 = by_root(cut1), by_root(cut)
        if set(r1) != set(r2) or any(r1[k] != r2[k] for k in r1 if k != "Mathlib"):
            sys.exit("numbers.py: the two runs differ outside Mathlib; the text says they do not")
        extra = r2["Mathlib"][0] - r1["Mathlib"][0]
        extra_cone = r2["Mathlib"][1] - r1["Mathlib"][1]
        if extra < 0 or extra_cone < 0:
            sys.exit("numbers.py: Mathlib from source declares fewer constants than the cached build")
        put("mathlibextra", str(extra), "cut-result.txt and run1/cut-result.txt: constants of Mathlib")
        put("mathlibextracone", str(extra_cone), "the same, in the cone")
        cone_diff = cone - int(grab(cut1, r"^CONE-SIZE (\d+)", "the first cone"))
        if cone_diff != extra_cone or cone_diff < 0:
            sys.exit("numbers.py: the two cones differ by other than Mathlib's extra constants in the cone")
        put("mathlibextraconewords", "one constant" if cone_diff == 1 else f"{cone_diff} constants",
            "cut-result.txt and run1/cut-result.txt: CONE-SIZE")
        # how the two builds of Mathlib differ (mathlib-diff.txt, the output of mathlib-diff.sh)
        md = (res / "mathlib-diff.txt").read_text(encoding="utf-8")
        aux = re.compile(r"^_private\.(.+)\.0\.(.+)\._(simp|abel)_\d+_\d+$")

        def section(head: str) -> list:
            # the indented lines that follow the line "<head> <count>", checked against the count
            mm = re.search(rf"^{re.escape(head)} (\d+)\n((?:  .*\n)*)", md, re.M)
            if not mm:
                sys.exit(f"numbers.py: mathlib-diff.txt has no section {head}")
            rows_ = [l[2:].split(" ", 2) for l in mm.group(2).splitlines()]
            if any(len(r_) != 3 for r_ in rows_):
                sys.exit(f"numbers.py: mathlib-diff.txt, section {head}: a line is not kind, module, name")
            if len(rows_) != int(mm.group(1)):
                sys.exit(f"numbers.py: mathlib-diff.txt, section {head}: the count and the lines disagree")
            return rows_, int(mm.group(1))
        only_src, src_n = section("ONLY IN THE BUILD FROM SOURCE")
        only_cache, cache_n = section("ONLY IN THE CACHED BUILD")
        if src_n - cache_n != extra:
            sys.exit("numbers.py: mathlib-diff.txt does not account for the difference between the two builds")
        proofs = set()
        for kind, module, name in only_src + only_cache:
            mm = aux.match(name)
            if kind != "T-" or not module.startswith("Mathlib.") or not mm:
                sys.exit(f"numbers.py: {name} is not a private auxiliary theorem of simp or abel in Mathlib; the text says all are")
            proofs.add(mm.group(2))
        put("mathlibonlysource", str(src_n), "mathlib-diff.txt")
        put("mathlibonlycache", str(cache_n), "mathlib-diff.txt")
        put("mathlibdiffproofs", str(len(proofs)), "mathlib-diff.txt: the declarations whose proofs these lemmas belong to")
        # among the constants both builds have: statements and values by Lean's hash
        common = int(grab(md, r"^IN BOTH (\d+)$", "the constants in both builds"))
        tot_cache = int(grab(md, r"^constants in the import closure of Mathlib, cached build: (\d+)", "the cached build's constants"))
        tot_src = int(grab(md, r"^constants in the import closure of Mathlib, built from source: (\d+)", "the source build's constants"))
        if common != tot_cache - cache_n or common != tot_src - src_n:
            sys.exit("numbers.py: mathlib-diff.txt: the constants in both builds are not the totals less those in one only")
        tdiff, tdiff_n = section("IN BOTH, TYPES WITH DIFFERENT HASHES")
        vdiff, vdiff_n = section("IN BOTH, VALUES WITH DIFFERENT HASHES")
        # What may differ, and is described in the text: an auxiliary lemma of simp or abel (the
        # same name can hold another lemma when the numbering shifted); an equation that Lean
        # generates for a definition (name.eq_N); a theorem in whose proof the auxiliary lemmas
        # occur; an auxiliary definition under such a theorem's name, which holds its proof.
        # Anything else stops this script.
        eqn = re.compile(r"^[^_].*\.eq_\d+$")
        t_aux = [n_ for k_, _, n_ in tdiff if k_ == "T-" and aux.match(n_)]
        t_eqn = [n_ for k_, _, n_ in tdiff if k_ == "T-" and eqn.match(n_)]
        if len(t_aux) + len(t_eqn) != tdiff_n:
            sys.exit(f"numbers.py: a statement differs between the two builds of Mathlib that is neither an auxiliary lemma nor a generated equation: {tdiff}")
        # a name ending in .eq_N is an equation of a definition only if the constant before .eq_N
        # is a definition; mathlib-diff.sh prints that for each build, with the two statements
        shown = md.split("THE STATEMENTS THAT DIFFER, AS THE CACHED BUILD HAS THEM", 1)
        if len(shown) != 2 or "THE STATEMENTS THAT DIFFER, AS THE BUILD FROM SOURCE HAS THEM" not in shown[1]:
            sys.exit("numbers.py: mathlib-diff.txt does not print the statements that differ")
        shown_cache, shown_src = shown[1].split("THE STATEMENTS THAT DIFFER, AS THE BUILD FROM SOURCE HAS THEM", 1)
        for n_ in t_aux + t_eqn:
            if f"    {n_} :" not in shown_cache or f"    {n_} :" not in shown_src:
                sys.exit(f"numbers.py: mathlib-diff.txt does not print the statement of {n_} in both builds")
        for n_ in t_eqn:
            if any(f"    [{n_.rsplit('.eq_', 1)[0]} is a definition]" not in part for part in (shown_cache, shown_src)):
                sys.exit(f"numbers.py: {n_} is not an equation of a definition; the text says it is")
        t_names = set(n_ for _, _, n_ in tdiff)
        v_same_as_t = [n_ for _, _, n_ in vdiff if n_ in t_names]
        v_parent_thm = [n_ for k_, _, n_ in vdiff if n_ not in t_names and k_ == "T-" and n_ in proofs]
        v_parent_def = [n_ for k_, _, n_ in vdiff if n_ not in t_names and k_ == "D-"
                        and any(n_.startswith(p_ + "._") for p_ in proofs)]
        if len(v_same_as_t) + len(v_parent_thm) + len(v_parent_def) != vdiff_n or len(v_same_as_t) != tdiff_n:
            sys.exit(f"numbers.py: values differ between the two builds of Mathlib beyond what the text describes: {vdiff}")
        if set(v_parent_thm) | set(n_.rsplit("._", 1)[0] for n_ in v_parent_def) != proofs:
            sys.exit("numbers.py: the proofs that differ are not exactly those in which the auxiliary lemmas occur")
        put("mathlibcommon", fmt(common), "mathlib-diff.txt: IN BOTH")
        put("mathlibtypesdiffer", str(tdiff_n), "mathlib-diff.txt: statements with different hashes")
        put("mathlibvaluesdiffer", str(vdiff_n), "mathlib-diff.txt: values with different hashes")
        small = ["no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten"]
        t_parts, t_short = [], []
        if t_aux:
            t_parts.append(("a further auxiliary lemma, to whose generated name the two builds gave different lemmas" if len(t_aux) == 1
                            else f"{small[len(t_aux)]} further auxiliary lemmas, to whose generated names the two builds gave different lemmas"))
            t_short.append("one further auxiliary lemma" if len(t_aux) == 1 else f"{small[len(t_aux)]} further auxiliary lemmas")
        if t_eqn:
            if len(t_eqn) != 1:
                sys.exit("numbers.py: more than one generated equation differs; the text is written for one")
            t_parts.append(f"\\texttt{{{t_eqn[0].replace('_', chr(92) + '_')}}}, one of the equations that Lean itself generates "
                           "for a definition, which the two builds state in different forms; both forms are printed in the results")
            t_short.append(f"one equation that Lean generates for a definition (`{t_eqn[0]}`), which the two builds state in different forms")
        if tdiff_n == 0:
            t_sentence = "the hash of the statement is the same in both for every one"
            t_short_s = "no statement differs"
        else:
            t_sentence = f"the hash of the statement is the same in both for all but {small[tdiff_n]}: " + ", and ".join(t_parts)
            t_short_s = "statements differ only in " + " and ".join(t_short)
        ordinal = ["", "first", "second", "third", "fourth", "fifth", "sixth"]
        if vdiff_n == 0:
            v_sentence, v_short_s = "The hash of every value is the same.", "and no proof"
        else:
            if len(v_parent_def) == 1 and len(v_parent_thm) + 1 == len(proofs) < len(ordinal):
                holders = (f"{small[len(v_parent_thm)]} of the {small[len(proofs)]} theorems in whose proofs the auxiliary lemmas "
                           f"occur, and an auxiliary definition under the name of the {ordinal[len(proofs)]}")
            elif not v_parent_def and len(v_parent_thm) == len(proofs):
                holders = f"the {small[len(proofs)]} theorems in whose proofs the auxiliary lemmas occur"
            else:
                sys.exit("numbers.py: the values that differ do not have the shape the text is written for")
            v_sentence = (f"The hash of the value differs for {small[vdiff_n]}: "
                          + ("these " + small[tdiff_n] + ", " if tdiff_n else "") + holders + ".")
            v_short_s = "and proofs only in those and in the proofs in which the auxiliary lemmas occur"
        put("mathlibhashnote", f"Among the {fmt(common)} constants that both builds have, {t_sentence}. {v_sentence} "
            "The hash is the 32-bit one that each compiled file stores with each term; it does not see the names of "
            "bound variables, their annotations, or metadata, and nothing here recomputes it. Equal hashes are "
            "evidence that two terms are equal, not a proof of it.", "mathlib-diff.txt, in words")
        put("mathlibhashshort", f"Among the {fmt(common)} constants both have, by Lean's 32-bit hash, {t_short_s}, {v_short_s}",
            "the same, for the README")
        # the lists of the archive's declarations and modules are the same in the two builds
        for name in ("cut-in.txt.xz", "cut-out.txt.xz", "cut-modules.txt.xz"):
            if lzma.open(res / name).read() != lzma.open(res / "run1" / name).read():
                sys.exit(f"numbers.py: {name} differs between the two builds; the text says the lists are identical")
        for k in ("modules", "definitions", "opaque", "axioms", "constructors-compared", "recursors-compared",
                  "unsafe-or-partial-not-replayed", "failed", "inductive-types"):
            if grab(rep1, rf"^{k} (\d+)", k) != grab(rep, rf"^{k} (\d+)", k):
                sys.exit(f"numbers.py: the two replays differ in {k}; the text says they agree there")
        ind1 = re.search(r"^inductive-types (\d+) in (\d+) blocks", rep1, re.M)
        if not ind1 or ind1.groups() != ind.groups():
            sys.exit("numbers.py: the two replays differ in inductive types or blocks")
        r1 = lambda k: int(grab(rep1, rf"^{k} (\d+)", k))
        if r1("replayed") - sum(r1(k) for k in ("theorems", "definitions", "opaque", "axioms", "constructors-compared",
                                                 "recursors-compared")) - int(ind1.group(1)) != quot:
            sys.exit("numbers.py: the first replay's kinds do not leave the four constants of the quotient type")
        for k in ("constants", "replayed", "theorems"):
            if int(grab(rep, rf"^{k} (\d+)", k)) - int(grab(rep1, rf"^{k} (\d+)", k)) != extra:
                sys.exit(f"numbers.py: the two replays differ in {k} by other than Mathlib's extra theorems")
        put("replayrunsagree", "true", "the counts of the two replays compared: equal but for Mathlib's extra theorems")
        put("firstconesize", fmt(int(grab(cut1, r"^CONE-SIZE (\d+)", "the first cone"))), "run1/cut-result.txt")
        for name in ("replay-skipped.txt", "replay-axioms.txt", "cut-five-extra.txt"):
            a = sorted((res / "run1" / name).read_text(encoding="utf-8").split())
            b = sorted((res / name).read_text(encoding="utf-8").split())
            if a != b:
                sys.exit(f"numbers.py: {name} differs between the two runs")
        put("firstreplayminutes", str(round(int(grab(rep1, r"^seconds (\d+)", "seconds")) / 60)), "run1/replay-summary.txt")
        # The duration of the cone step. cut.sh records no time; file-times.txt holds the time at
        # which the machine last wrote each results file. The step ran from the end of the step
        # before it (corollaries.sh, whose last file is targets.txt) to its own last file.
        times = dict((l.split()[0], int(l.split()[1])) for l in
                     (res / "file-times.txt").read_text(encoding="utf-8").splitlines() if l.strip())
        cut_end = max(times[n] for n in ("cut-result.txt", "cut-hub.txt", "cut-modules.txt", "cut-in.txt", "cut-out.txt"))
        cut_secs = cut_end - times["targets.txt"]
        if not 0 < cut_secs < 86400 or times["targets.txt"] < times["corollaries.txt"]:
            sys.exit("numbers.py: file-times.txt does not give a usable duration for the cone step")
        put("cuthours", f"{cut_secs / 3600:.1f}", "file-times.txt: from targets.txt to the last cut file")
        # The second machine's cost up to the last step reported: the provider's hourly price,
        # 1.12 US dollars, times the hours from the machine's start, 2026-11-21 15:09 UTC
        # (1795273740), to the last time in file-times.txt. The price and the start are typed
        # here: no results file holds them. Computed, not billed.
        run_hours = (max(times.values()) - 1795273740) / 3600
        if not 0 < run_hours < 200:
            sys.exit("numbers.py: file-times.txt gives no usable end for the second machine's run")
        put("secondruncost", str(round(run_hours * 1.12)), "computed: 1.12 dollars an hour from the machine's start to the last time in file-times.txt")
    else:
        dup = re.search(r"^names-declared-more-than-once (\d+), other versions also checked (\d+), of which with a different type (\d+)", rep, re.M)
        if dup.group(1) != dup.group(2) or dup.group(3) != "0":
            sys.exit("numbers.py: repeated names were not all checked, or two versions differ")
        put("replayrepeated", fmt(int(dup.group(1))), "replay-summary.txt")
    skipped = [l for l in (res / "replay-skipped.txt").read_text(encoding="utf-8").splitlines() if l.strip()]
    if len(skipped) != r("unsafe-or-partial-not-replayed"):
        sys.exit("numbers.py: replay-skipped.txt does not have the number of lines the summary gives")
    put("replayskippedrec", fmt(sum(1 for l in skipped if l.endswith("._unsafe_rec"))), "replay-skipped.txt")
    put("replaymillions", f"{replayed / 1e6:.1f}", "computed")
    program = (res.parent / "replay" / "ReplayMain.lean").read_text(encoding="utf-8")
    put("replayprogramlines", str(len(program.splitlines())), "verify/replay/ReplayMain.lean: lines, comments included")
    if not second:
        first_form = (res / "replay-program-first-form.lean").read_text(encoding="utf-8")
        put("firstprogramlines", str(len(first_form.splitlines())), "results/replay-program-first-form.lean: lines")

    # the checker's tests: the hostile modules (hostile.txt, the output of hostile.sh)
    host = (res / "hostile.txt").read_text(encoding="utf-8")
    if "HOSTILE-OK" not in host:
        sys.exit("numbers.py: the hostile modules did not behave as expected")
    hsha = grab(host, r"^replay program sha256 ([0-9a-f]{64})$", "the hash of the program the tests used")
    import hashlib
    if hashlib.sha256((res.parent / "replay" / "ReplayMain.lean").read_bytes()).hexdigest() != hsha:
        sys.exit("numbers.py: the hostile tests were not made with the replay program published here")
    put("hostileprogramsha", hsha[:16], "hostile.txt: first sixteen digits")
    desc = {}
    for line in (here / "tools" / "hostile-rows.txt").read_text(encoding="utf-8").splitlines():
        if line.strip() and not line.startswith("#"):
            name, _, text = line.partition(" ")
            desc[name] = text.strip()
    hrows = re.findall(r"^Hostile\.(\w+): leanchecker (\w+) \(expected \w+\), leanchecker --fresh (\w+) \(expected \w+\), replay (\w+) \(expected (\w+)\); as expected: yes$", host, re.M)
    if sorted(h[0] for h in hrows) != sorted(desc):
        sys.exit("numbers.py: hostile.txt and tools/hostile-rows.txt do not name the same modules")
    bad_rows = [h for h in hrows if h[4] == "rejects"]
    if any(h[3] != h[4] for h in hrows):
        sys.exit("numbers.py: the replay did not give the expected verdict on a hostile module")
    put("hostilemodules", str(len(hrows)), "hostile.txt")
    put("hostilebad", str(len(bad_rows)), "hostile.txt: modules a replay must reject")
    put("hostilecontrols", str(len(hrows) - len(bad_rows)), "hostile.txt")
    put("hostilecrafted", str(sum(1 for h in hrows if not (res.parent / "hostile" / "Hostile" / (h[0] + ".lean")).exists())),
        "hostile/: modules with no source file")
    if "named theorems: Hostile.conclusion reported FAILED, Hostile.Honest.size_pos reported checked; as expected: yes" not in host:
        sys.exit("numbers.py: the report on named theorems was not as expected")
    if second and replay_sha != hsha:
        sys.exit("numbers.py: the replay and the hostile tests were not made with the same program")
    put("hostilefreshrejects", str(sum(1 for h in bad_rows if h[2] == "rejects")), "hostile.txt")
    put("hostiledefaultrejects", str(sum(1 for h in bad_rows if h[1] == "rejects")), "hostile.txt")
    order = [l.split(" ", 1)[0] for l in (here / "tools" / "hostile-rows.txt").read_text(encoding="utf-8").splitlines()
             if l.strip() and not l.startswith("#")]
    by_name = {h[0]: h for h in hrows}
    # lean4lean on the same modules (independent-hostile.txt)
    ind_host = (res / "independent-hostile.txt").read_text(encoding="utf-8")
    irows = {m[0]: m for m in re.findall(r"^Hostile\.(\w+): lean4lean (\w+), lean4lean --fresh (\w+) \(a sound replay: (\w+)\)$", ind_host, re.M)}
    if sorted(irows) != sorted(desc):
        sys.exit("numbers.py: independent-hostile.txt does not cover the hostile modules")
    if any(irows[h[0]][1] != "accepts" or irows[h[0]][2] != "accepts" for h in hrows if h[4] == "accepts"):
        sys.exit("numbers.py: lean4lean rejects a control")
    put("independentfreshrejects", str(sum(1 for h in bad_rows if irows[h[0]][2] == "rejects")), "independent-hostile.txt")
    put("independentdefaultrejects", str(sum(1 for h in bad_rows if irows[h[0]][1] == "rejects")), "independent-hostile.txt")
    with open(dst.parent / "hostile-table.tex", "w", encoding="utf-8", newline="\n") as f:
        f.write("% Generated by tools/numbers.py from verify/results/hostile.txt and independent-hostile.txt. Do not edit by hand.\n")
        f.write("\\begin{table}[tp]\n\\centering\\small\n\\begin{tabular}{@{}p{0.5\\textwidth}cccc@{}}\n\\toprule\n")
        f.write("The compiled file holds & \\multicolumn{2}{c}{\\lean{leanchecker}} & \\lean{lean4lean} & ours\\\\\n")
        f.write(" & ordinary & \\lean{--fresh} & \\lean{--fresh} & \\\\\n\\midrule\n")
        mark = {"accepts": "accepts", "rejects": "\\textbf{rejects}"}
        for name in order:
            h = by_name[name]
            f.write(f"{desc[name]} & {mark[h[1]]} & {mark[h[2]]} & {mark[irows[name][2]]} & {mark[h[3]]}\\\\\n")
        f.write("\\bottomrule\n\\end{tabular}\n")
        f.write("\\caption{The modules built to test the checkers, and what each checker does with each. "
                "The first \\hostilecontrols{} are controls, which a checker should accept; a sound "
                "replay rejects the others. The ordinary mode of \\texttt{leanchecker} examines the "
                "named module and trusts its imports; \\texttt{lean4lean} is the second implementation "
                "of the kernel of \\cref{sec:checker}.}\\label{tab:hostile}\n\\end{table}\n")
    ifresh = (res / "independent-fresh.txt").read_text(encoding="utf-8")
    for root in ["Mathlib.NumberTheory.LSeries.RiemannZeta"] + (["Mathlib.NumberTheory.LSeries.DirichletContinuation"] if second else []):
        ms = re.findall(rf"^lean4lean --fresh {re.escape(root)}: exit (\d+); elapsed ([0-9.]+) s", ifresh, re.M)
        if len(ms) != 1 or ms[0][0] != "0":
            sys.exit(f"numbers.py: lean4lean --fresh on {root}: not exactly one line, or not accepted")
        m = ms[0]
        if root.endswith("RiemannZeta"):
            put("independentfreshminutes", str(round(float(m[1]) / 60)), "independent-fresh.txt")
    if second:
        chk = (res / "check.txt").read_text(encoding="utf-8")
        for name, module in (("RiemannHypothesis", "Mathlib.NumberTheory.LSeries.RiemannZeta"),
                             ("riemannZeta", "Mathlib.NumberTheory.LSeries.RiemannZeta"),
                             ("DirichletCharacter.LFunction", "Mathlib.NumberTheory.LSeries.DirichletContinuation")):
            if f"{name} is declared in (some {module})" not in chk and f"{name} is declared in some {module}" not in chk:
                sys.exit(f"numbers.py: check.txt does not say that {name} is declared in {module}")
        # the statements written out in check.sh elaborate against the theorems (a failure makes
        # lean exit with an error), the definitions of Statements.lean are printed in full, and
        # both checkers accept the module Statements
        if not re.search(r"^CHECK-EXIT 0$", chk, re.M):
            sys.exit("numbers.py: check.sh did not end with exit code 0")
        for name in ("RiemannZetaZerosOnLine", "DirichletLNonvanishingRightOfHalf", "DirichletLZerosOnLine", "PrimitiveDirichletLZerosOnLine"):
            if f"def {name} : Prop :=" not in chk:
                sys.exit(f"numbers.py: check.txt does not print the definition {name}")
        for line in ("leanchecker Statements: exit 0", "lean4lean Statements: exit 0"):
            if line not in chk:
                sys.exit(f"numbers.py: check.txt does not have the line '{line}'")
    # The two samples (sample.sh, independent.sh sample) and sample-exact.sh. Each checker, in
    # its ordinary mode, takes a name as a prefix: it checks the module of that name and every
    # module whose name extends it, importing the closure once for each, all at once. On a name
    # with many modules under it the system killed the process at the container's memory limit
    # (exit code 137), which is no verdict. sample-exact.sh lists the modules under every name
    # (sample-prefixes.txt) and, for a name whose process was killed, calls the checker's
    # function for one module on the module of that name and on each module under it
    # (sample-exact.txt). Any other exit code, or a module not accepted there, stops this script.
    def sample_outcome(listfile: str, checker: str, prefix: str) -> None:
        rows = [l.split() for l in (res / listfile).read_text(encoding="utf-8").splitlines() if l.strip()]
        if any(len(r) != 3 for r in rows) or len(set(r[0] for r in rows)) != len(rows):
            sys.exit(f"numbers.py: {listfile} is not one line a name")
        drawn = [l.strip() for l in (res / "sample-modules.txt").read_text(encoding="utf-8").splitlines() if l.strip()]
        if sorted(drawn) != sorted(r[0] for r in rows):
            sys.exit(f"numbers.py: {listfile} does not cover the names drawn")
        cone_modules = set(lzma.open(res / "cut-modules.txt.xz", "rt", encoding="utf-8").read().split())
        if drawn.count("Main") != 1 or not set(drawn) - {"Main"} <= cone_modules:
            sys.exit("numbers.py: the sample is not Main and modules of the cone; the text says it is")
        summary = (res / listfile.replace(".txt", "-summary.txt")).read_text(encoding="utf-8")
        if grab(summary, r"^logs that mention a panic (\d+)", "the count of panics") != "0":
            sys.exit(f"numbers.py: {checker} panicked on a module of the sample")
        if int(grab(summary, r"^modules checked (\d+)", "the sample size")) != len(rows):
            sys.exit(f"numbers.py: {listfile} and its summary disagree on the number of names")
        oom = re.search(r"^processes killed for memory in the container during the step (\d+) -> (\d+)", summary, re.M)
        under: dict[str, set] = {}
        for l in (res / "sample-prefixes.txt").read_text(encoding="utf-8").splitlines():
            if not l.strip():
                continue
            name, mod = l.split()
            if name not in drawn or not mod.startswith(name + "."):
                sys.exit(f"numbers.py: sample-prefixes.txt: {mod} is not a module under a name of the sample")
            under.setdefault(name, set()).add(mod)
        # every module of the cone whose name extends a drawn name must be listed there
        drawn_set = set(drawn)
        for mod in cone_modules:
            parts = mod.split(".")
            for i in range(1, len(parts)):
                name = ".".join(parts[:i])
                if name in drawn_set and mod not in under.get(name, set()):
                    sys.exit(f"numbers.py: sample-prefixes.txt does not list {mod} under {name}")
        exact_text = (res / "sample-exact.txt").read_text(encoding="utf-8")
        for mod, ok in (("Hostile.Honest", True), ("Hostile.FalseTheorem", False)):
            mm = re.search(rf"^route-test {checker} {re.escape(mod)} exit (\d+) ", exact_text, re.M)
            if not mm or (mm.group(1) == "0") != ok:
                sys.exit(f"numbers.py: sample-exact.txt does not show that the route for {checker} gives the right verdict on {mod}")
        exact: dict[str, dict] = {}
        exact_secs = []
        for l in exact_text.splitlines():
            p = l.split()
            if len(p) >= 5 and p[0] == checker and p[1] in drawn_set and p[3].isdigit() and p[4].isdigit():
                if p[2] in exact.setdefault(p[1], {}):
                    sys.exit(f"numbers.py: sample-exact.txt has two lines for {checker} on {p[2]}")
                exact[p[1]][p[2]] = p[3]
                exact_secs.append(int(p[4]))
        not_ok = [(r[0], r[1]) for r in rows if r[1] != "0"]
        for m, code in not_ok:
            if code != "137":
                sys.exit(f"numbers.py: {checker} ended with code {code} on {m}: not a kill; the text does not cover it")
            want = {m} | under.get(m, set())
            if len(want) < 2:
                sys.exit(f"numbers.py: {checker} was killed on {m}, which has no module under it; the text explains the kill by those modules")
            if set(exact.get(m, {})) != want:
                sys.exit(f"numbers.py: {checker}: {m} and the modules under it were not all checked one by one")
            if any(c != "0" for c in exact[m].values()):
                sys.exit(f"numbers.py: {checker} did not accept every module under {m} when they were checked one by one")
        if set(exact) != set(m for m, _ in not_ok):
            sys.exit(f"numbers.py: sample-exact.txt and {listfile} disagree on the names checked one module at a time")
        k = len(not_ok)
        if k > 1:
            sys.exit(f"numbers.py: {k} names of {checker} were killed; the text is written for one")
        if k and (not oom or int(oom.group(2)) - int(oom.group(1)) != k):
            sys.exit(f"numbers.py: a process of {checker} ended with code 137, but the container's counter of kills for memory did not rise by one; the text says memory")
        # the same name alone on the machine (sample-alone.txt): killed again, and how much memory
        # the container held when it was
        alone_gb = None
        if k:
            am = re.search(rf"^DONE-STEP probe {checker} {re.escape(not_ok[0][0])} exit (\d+) seconds (\d+) max-anon-bytes (\d+) oom_kill (\d+)$",
                           (res / "sample-alone.txt").read_text(encoding="utf-8"), re.M)
            if not am or am.group(1) != "137":
                sys.exit(f"numbers.py: sample-alone.txt does not record {checker} killed alone on the name")
            alone_gb = f"{int(am.group(3)) / 1e9:.1f}"
            put(prefix + "alonegb", alone_gb, "sample-alone.txt: the container's anonymous memory at its highest, in units of 10^9 bytes")
            put(prefix + "aloneseconds", am.group(2), "sample-alone.txt")
            put(prefix + "exactmin", str(min(exact_secs)), "sample-exact.txt: the fewest seconds a module took")
            put(prefix + "exactmax", str(max(exact_secs)), "sample-exact.txt: the most seconds a module took")
        covered = set(drawn).union(*under.values()) if under else set(drawn)
        put(prefix + "sample", fmt(len(rows)), listfile)
        put(prefix + "sampledrawn", fmt(len(rows) - 1), listfile)
        put(prefix + "sampleaccepted", fmt(len(rows) - k), f"{listfile}: exit code 0")
        put(prefix + "samplekilled", str(k), f"{listfile}: exit code 137")
        put(prefix + "sampleatatime", grab(summary, r"^processes at a time (\d+)", "the processes at a time"), "the sample's summary")
        put(prefix + "prefixnames", fmt(sum(1 for n in drawn if under.get(n))), "sample-prefixes.txt: names of the sample with modules under them")
        put(prefix + "prefixmodules", fmt(len(covered) - len(drawn)), "sample-prefixes.txt: the modules under those names that are not themselves names of the sample")
        put(prefix + "covered", fmt(len(covered)), "the names of the sample and the modules under them")
        names_with = sum(1 for n in drawn if under.get(n))
        if names_with == 0:
            pnote = "None of the names has a module under it."
        elif names_with == 1:
            pnote = (f"One of the names has modules under it, {fmt(len(covered) - len(drawn))} of them, so that the names "
                     f"cover {fmt(len(covered))} modules.")
        else:
            pnote = (f"{fmt(names_with)} of the names have modules under them, so that the names cover "
                     f"{fmt(len(covered))} modules.")
        put(prefix + "prefixnote", pnote, "sample-prefixes.txt, in words")
        if k == 0:
            note, short = "It accepted all of them.", ""
        else:
            m = not_ok[0][0]
            n_under = len(under[m])
            put(prefix + "killedimports", str(n_under + 1), "the modules that the name on which the process was killed covers")
            first = (f"It accepted the {fmt(len(rows) - 1)} names that are single modules. On the remaining name " if names_with == 1
                     else f"It accepted {fmt(len(rows) - 1)} of the names. On the remaining name, which has {n_under} modules under it, ")
            how = (" Lean's interpreter ran the function." if checker == "lean4lean" else "")
            secs = (f"in {min(exact_secs)} to {max(exact_secs)} seconds each" if min(exact_secs) != max(exact_secs)
                    else f"in {min(exact_secs)} seconds each")
            note = (first + "the system killed the process at the container's memory limit (exit code~137), "
                    f"which is no verdict of the checker; the command imports the closure {n_under + 1} times at once there. "
                    f"Run by itself, it was killed in the same way; the container's anonymous memory, read once a second, "
                    f"had reached {alone_gb}\\,GB of its limit of \\memorylimit\\,GB. We then called the function that the checker applies to "
                    f"one module, \\texttt{{replayFromImports}}, on that module and on each of the {n_under} under it, "
                    f"one at a time; it accepted all {n_under + 1}, {secs}.{how} Called in that way it also rejects a test "
                    f"module of \\cref{{tab:hostile}} that it must reject and accepts one that it must accept.")
            short = (f". For one name, with {n_under} modules under it, the command imports the closure {n_under + 1} times "
                     f"at once and the system killed it at the container's memory limit, also when it ran by itself; the "
                     f"checker's function for one module was then called on each of the {n_under + 1} in turn and accepted all")
        put(prefix + "samplenote", note, f"{listfile}, sample-prefixes.txt and sample-exact.txt, in words")
        put(prefix + "sampleshort", short, "the same, for the README")
    if second:
        sample_outcome("independent-sample.txt", "lean4lean", "independent")

    # Lean's own checker (stock.txt, sample-summary.txt, sample.txt) and the toolchain
    stock = (res / "stock.txt").read_text(encoding="utf-8")
    stock_sha = grab(stock, r"^replay program sha256 ([0-9a-f]{64})$", "the hash of the program run on Mathlib")
    if stock_sha != hsha:
        sys.exit("numbers.py: the runs on Mathlib and the hostile tests were not made with the same program")
    for root, key in (("Mathlib.NumberTheory.LSeries.RiemannZeta", "rz"), ("Mathlib", "mathlib")):
        m = re.search(rf"^leanchecker --fresh {re.escape(root)}: exit (\d+); elapsed ([0-9.]+) s, processor time ([0-9.]+) s user and ([0-9.]+) s system", stock, re.M)
        m2 = re.search(rf"^replay {re.escape(root)}: exit (\d+); elapsed ([0-9.]+) s, processor time ([0-9.]+) s user and ([0-9.]+) s system.*?constants (\d+) replayed (\d+) failed (\d+)", stock, re.M)
        if not m or not m2 or m.group(1) != "0" or m2.group(1) != "0" or m2.group(7) != "0":
            sys.exit(f"numbers.py: Lean's checker and the replay do not both accept {root}")
        put("stockfresh" + key + "minutes", str(round(float(m.group(2)) / 60)), "stock.txt")
        put("stockfresh" + key + "cpuminutes", str(round((float(m.group(3)) + float(m.group(4))) / 60)), "stock.txt: processor time")
        put("stockreplay" + key + "decls", fmt(int(m2.group(6))), "stock.txt")
        put("stockreplay" + key + "minutes", str(max(1, round(float(m2.group(2)) / 60))), "stock.txt")
        put("stockreplay" + key + "cpuminutes", str(round((float(m2.group(3)) + float(m2.group(4))) / 60)), "stock.txt: processor time")
        cpu_ratio = (float(m.group(3)) + float(m.group(4))) / (float(m2.group(3)) + float(m2.group(4)))
        if key == "rz":
            fresh_rz_cpu = float(m.group(3)) + float(m.group(4))
    if second:
        put("freshratio", f"{cpu_ratio:.2f}", "stock.txt: leanchecker --fresh's processor time on Mathlib over the replay's")
        put("freshestimatehours", str(round(replay_cpu_s * cpu_ratio / 3600)),
            "computed: the replay's processor time times the ratio of the two programs' processor times on Mathlib")
        l4 = re.search(r"^lean4lean --fresh Mathlib\.NumberTheory\.LSeries\.RiemannZeta: exit 0; elapsed [0-9.]+ s, processor time ([0-9.]+) s user and ([0-9.]+) s system",
                       ifresh, re.M)
        l4_ratio = (float(l4.group(1)) + float(l4.group(2))) / fresh_rz_cpu
        put("independentratio", f"{l4_ratio:.1f}", "independent-fresh.txt and stock.txt: lean4lean's processor time on the closure of the statement's module over leanchecker --fresh's")
        put("independentestimatehours", str(round(replay_cpu_s * cpu_ratio * l4_ratio / 3600, -1)).split(".")[0],
            "computed: the estimate for leanchecker --fresh times that ratio, to the nearest ten hours")
    msum = (res / "replay-Mathlib" / "replay-summary.txt").read_text(encoding="utf-8")
    ex = re.search(r"^exported-parts-compared (\d+) modules, (\d+) constants", msum, re.M)
    if ex.group(1) != grab(msum, r"^modules (\d+)", "the modules of Mathlib's closure"):
        sys.exit("numbers.py: not every module of Mathlib's closure uses the module system; the text says every one does")
    put("stockexportedmodules", fmt(int(ex.group(1))), "replay-Mathlib/replay-summary.txt")
    put("stockexported", fmt(int(ex.group(2))), "replay-Mathlib/replay-summary.txt")
    put("stockpartialunmarked", fmt(int(grab(msum, r"^exported-axioms-of-partial-definitions-not-marked-unsafe (\d+)", "the unmarked axioms"))),
        "replay-Mathlib/replay-summary.txt")
    if grab(msum, r"^failed (\d+)", "the Mathlib replay's failures") != "0":
        sys.exit("numbers.py: the replay of Mathlib has failures")
    if grab(msum, r"^code-files-read (\d+)", "the code files read") != ex.group(1):
        sys.exit("numbers.py: the files of compiled code were not read for every module of Mathlib's closure")
    if second:
        samp = (res / "sample-summary.txt").read_text(encoding="utf-8")
        checked = int(grab(samp, r"^modules checked (\d+)", "the sample size"))
        sample_outcome("sample.txt", "leanchecker", "stock")
        if checked != sum(1 for l in (res / "sample.txt").read_text(encoding="utf-8").splitlines() if l.strip()):
            sys.exit("numbers.py: sample-summary.txt and sample.txt disagree on the number of modules")
        elapsed = int(grab(samp, r"^elapsed seconds (\d+)", "the elapsed time of the sample"))
        put("stocksampleminutes", str(round(elapsed / 60)), "sample-summary.txt: elapsed seconds / 60")
        put("stockfulldays", fmt(round(elapsed / checked * files / 86400)), "computed: the sample's elapsed time a module, at its number of processes at a time, over every module, in days")
        # the earlier run of the sample step (sample-earlier.txt, ten at a time, output not kept)
        # is kept for the record; nothing in the text is taken from it
    tool = (res / "toolchain.txt").read_text(encoding="utf-8")
    if grab(tool, r"^files that differ, or are in one and not the other: (\d+)", "the toolchain comparison") != "0":
        sys.exit("numbers.py: the toolchain differs from the release")
    put("toolchainfiles", fmt(int(grab(tool, r"^files in the installed toolchain (\d+)", "the toolchain's files"))), "toolchain.txt")

    # the literature table (refs/rows-counts.json)
    published = rows["general"] + rows["restricted"] + rows["differs"]
    if published + rows["internal"] + rows["empty"] + rows["conclusion"] != rows["distinct"]:
        sys.exit("numbers.py: the labels of the literature table do not add up")
    put("literaturerows", str(rows["rows"]), "refs/rows-counts.json")
    put("rowsdistinct", str(rows["distinct"]), "refs/rows-counts.json")
    put("rowsrepeated", str(rows["rows"] - rows["distinct"]), "computed")
    put("rowspublished", str(published), "computed")
    put("rowsgeneral", str(rows["general"]), "refs/rows-counts.json")
    put("rowsspecial", str(rows["restricted"]), "refs/rows-counts.json")
    put("rowsother", str(rows["differs"]), "refs/rows-counts.json")
    put("rowsinternal", str(rows["internal"]), "refs/rows-counts.json")

    with open(dst, "w", encoding="utf-8", newline="\n") as f:
        f.write("% Generated by tools/numbers.py from verify/results/ and refs/rows-counts.json.\n")
        f.write("% Do not edit by hand.\n")
        f.write("\\newif\\ifsecondrun\n" + ("\\secondruntrue\n" if second else "\\secondrunfalse\n"))
        for name, value, comment in out:
            f.write(f"\\newcommand{{\\{name}}}{{{value}}}% {comment}\n")
    print(f"{len(out)} numbers written to {dst}")


if __name__ == "__main__":
    main()
