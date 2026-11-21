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
    # the revision of the manifest entry named mathlib (summary.sh prints every entry)
    mrev = re.search(r'"inputRev": "([0-9a-f]{40})"[^{}]*"name": "mathlib"|"name": "mathlib"[^{}]*"inputRev": "([0-9a-f]{40})"', build)
    if not mrev and len(re.findall(r'"inputRev": "[0-9a-f]{40}"', build)) == 1:
        mrev = re.search(r'"inputRev": "([0-9a-f]{40})"()', build)
    if not mrev:
        sys.exit("numbers.py: cannot find the Mathlib revision in build-summary.txt")
    put("mathlibrev", mrev.group(1) or mrev.group(2), "build-summary.txt")
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
        for line in block.splitlines()[1:]:
            p = line.split()
            if len(p) == 4:
                root, allm, decl, touch = p[0], int(p[1]), int(p[2]), int(p[3])
                total_files += allm
                put("mods" + root + "All", fmt(allm), "cut-result.txt MODULES-BY-ROOT")
                put("mods" + root + "Unused", fmt(allm - touch), "modules of the directory minus those touching the cone")
        if total_files != files:
            sys.exit(f"numbers.py: MODULES-BY-ROOT adds up to {total_files}, not {files}")
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
    put("replayquot", str(quot), "computed: the constants replayed less those of the other kinds; checked to be 4")
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
        # the first run's replay, of the tree built with Mathlib from the cache
        rep1 = (res / "run1" / "replay-summary.txt").read_text(encoding="utf-8")
        same = all(grab(rep1, rf"^{k} (\d+)", k) == grab(rep, rf"^{k} (\d+)", k)
                   for k in ("modules", "constants", "replayed", "theorems", "definitions", "opaque", "axioms",
                             "constructors-compared", "recursors-compared", "unsafe-or-partial-not-replayed", "failed"))
        put("replayrunsagree", "true" if same else "false", "the counts of the two replays compared")
        if not same:
            sys.exit("numbers.py: the two replays' counts differ; the text says they agree")
        put("firstreplayminutes", str(round(int(grab(rep1, r"^seconds (\d+)", "seconds")) / 60)), "run1/replay-summary.txt")
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
    # the independent kernel on the same modules (independent-hostile.txt)
    ind_host = (res / "independent-hostile.txt").read_text(encoding="utf-8")
    irows = {m[0]: m for m in re.findall(r"^Hostile\.(\w+): lean4lean (\w+), lean4lean --fresh (\w+) \(a sound replay: (\w+)\)$", ind_host, re.M)}
    if sorted(irows) != sorted(desc):
        sys.exit("numbers.py: independent-hostile.txt does not cover the hostile modules")
    if any(irows[h[0]][1] != "accepts" or irows[h[0]][2] != "accepts" for h in hrows if h[4] == "accepts"):
        sys.exit("numbers.py: the independent kernel rejects a control")
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
                "named module and trusts its imports; \\texttt{lean4lean} is the independent kernel "
                "of \\cref{sec:checker}.}\\label{tab:hostile}\n\\end{table}\n")
    ifresh = (res / "independent-fresh.txt").read_text(encoding="utf-8")
    m = re.search(r"^lean4lean --fresh Mathlib\.NumberTheory\.LSeries\.RiemannZeta: exit (\d+); elapsed ([0-9.]+) s", ifresh, re.M)
    if not m or m.group(1) != "0":
        sys.exit("numbers.py: the independent kernel did not accept the closure of the statement")
    put("independentfreshminutes", str(round(float(m.group(2)) / 60)), "independent-fresh.txt")
    if second:
        isamp = (res / "independent-sample-summary.txt").read_text(encoding="utf-8")
        ichecked = int(grab(isamp, r"^modules checked (\d+)", "the independent sample size"))
        iaccepted = int(grab(isamp, r"^accepted (\d+)", "the number the independent kernel accepted"))
        put("independentsampleok", "all of them" if iaccepted == ichecked else fmt(iaccepted), "independent-sample-summary.txt")
        put("independentsampleaccepted", fmt(iaccepted), "independent-sample-summary.txt")
        put("independentsample", fmt(ichecked), "independent-sample-summary.txt")

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
    if second:
        put("freshestimatehours", str(round(replay_cpu_s * cpu_ratio / 3600)),
            "computed: the replay's processor time times the ratio of the two programs' processor times on Mathlib")
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
        accepted = int(grab(samp, r"^accepted (\d+)", "the number accepted"))
        if "Main accepted" not in samp:
            sys.exit("numbers.py: Lean's checker did not accept Main")
        put("stocksample", fmt(checked), "sample-summary.txt")
        put("stocksampledrawn", fmt(checked - 1), "sample-summary.txt")
        put("stocksampleok", "all of them" if accepted == checked else fmt(accepted), "sample-summary.txt")
        put("stocksampleaccepted", fmt(accepted), "sample-summary.txt")
        secs = int(grab(samp, r"^seconds, summed over the modules (\d+)", "the time of the sample"))
        put("stockpermodule", str(round(secs / checked)), "sample-summary.txt: seconds a module")
        put("stockfulldays", fmt(round(secs / checked * files / 86400)), "computed: that rate over every module, in processor-days")
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
