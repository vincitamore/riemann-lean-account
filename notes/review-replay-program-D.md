# Review D of the kernel replay program

**What was reviewed.** The changes made to the replay program after review C, the test modules
and the script that changed with them, the lines added to the cone program, and the
subsections "Kernel replay" and "The checker" of the paper, in both branches of
`\ifsecondrun`. The versions, by SHA-256 (computed with `sha256sum`); line numbers below are
of these versions.

| File | SHA-256 |
|---|---|
| `verify/replay/ReplayMain.lean`, 542 lines: the version reviewed (as in commit `4099fbf3a`) | `3cb54c97bb2e006174e17214dbabafb1a432d64761cf33d3aa598ece8859f5c3` |
| `verify/replay/ReplayMain.lean`, 451 lines, as in commit `5b338c81a`: the version review C read, called "the previous version" below | `65396ce3f33656fdb6259e63e55b023c0b779b20c45b85bdba4ffac195cf8011` |
| `verify/hostile/Craft.lean` | `238e7391a18fa1e3469f01eac953db59f6f6260f41e04614d024a154e95d035c` |
| `verify/hostile/expected.txt` | `c871cb645541393ec82825c0ec72300e54a8558b37275e9442ddd5e30f8d8479` |
| `verify/hostile/lakefile.toml` | `1c067176f1a4a917cb539181eb8a88d7b1d64419ed1e6ba2f9939eae9f5bb876` |
| `verify/hostile/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `verify/hostile/Hostile/*.lean`, 20 files | listed in Appendix B |
| `publish/public/verify/hostile.sh` | `40c04eb67802ecd175a8f3ce6762ee313027c28525fd0e76b3f231d5b683bc68` |
| `verify/cut/CutMain.lean` | `181d4383db8b4211f9f10f4678486613253c4bd60a45cd2b6e330bf309b54fe9` |
| `paper/sections/verification.tex` | `8d882aab1cd8a56d616f3dbadab441ebc9235df584f576137e4f6e127d8473ac` |
| `paper/version.tex` (for `\replaystatus`) | `bf64c0d964b5e047ef2a4cac20cd34728bab105e91399d422331be247cb90867` |
| `paper/tools/numbers.py` (for what the paper's numbers count) | `434926d8290fa7009cb8e8413b70ae2d1bf20a98f3470229f844c3e8d5d0b54d` |
| `paper/numbers.tex`, `paper/hostile-table.tex` (generated; for the values of the macros) | `c5e5cd8fa47eda709e23262445b2175337946308d38bc262fd9b593577a3689b`, `b83a5dae72332b718376f835be55e9b44bee5eead36a3b712de6f8ee0de20833` |
| `verify/results/hostile.txt` (the recorded run of the suite) | `e1597132fa3288c70d17f32917b78a629ff35760f70e718c4ddb8b069e2e0a76` |

Lean is cited at release 4.33.1 (`lean --version`: commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`): Lean files by their path under `src/lean/` in the
release archive, the C++ runtime, which the archive does not contain, by its path under `src/`
at tag `v4.33.1`. Each claim below says whether it was read in source (with file and line) or
measured (with what was run); "Method and limits" at the end lists both.

## Verdict

Yes, in two narrow ways of the kind review C reported as its finding 1, and neither reaches the
five theorems. The program now compares the constants of the `.olean` and `.olean.server` parts
of each module-system file with the part it replays, by Lean's own rule, and on the whole of
Lean's library (the closures of `Lean`, `Std` and `Lake`) that comparison objects to nothing
(measured). But a module inside the module
system also receives material from a compiled file by two routes the program does not read.
First, it follows the import list of the exported part, which is not compared: a hand-written
file whose three parts hold the same honest theorem, and whose `.olean` and `.olean.server`
parts list one import more than its private part, a plain compiled file holding
`theorem Exp.badFalse : False := True.intro`, is replayed with `failed 0` and exit code 0,
and a file that begins with `module` and says `public import` of it compiles
`theorem Exp.fromMore : False := Exp.badFalse`, for which `#print axioms` reports no axioms
(finding 1, measured). Second, a module that a `module` file reaches only through a
`meta import` is loaded for its compiled code, and its constants are then taken from its `.ir`
file, which the program never reads: a module whose `.olean` parts are honest and whose `.ir`
file holds `theorem Exp.irFalse : False := True.intro` is replayed with exit code 0, and a
`module` file that reaches it that way compiles a proof of `False` with no axioms reported
(finding 2, measured). A use of either constant inside the replayed closure is rejected
(measured: `unknown constant` both times), and the five theorems are checked, by the program and
by `check.sh`, in the environment built from the private parts, so they are not affected. What
the two cases refute is the sentence of the paper that the program requires the other parts
"to hold what Lean derives from the part replayed". Apart from them I found no input on which
the program reports success wrongly; what was searched is listed at the end of section 3 (a).
The changes cannot make the program accept anything the previous version rejected: they only
add failures, and on the 22 test modules the two versions give the same verdicts and the same
failure names except that the previous version accepts the three new `Exported*` modules
(measured). They make it reject one input the previous version accepted and Lean's import
accepts, a stray `.olean.server` file beside a plain `.olean` (finding 3, measured). The suite
gives the expected verdict and exactly the expected failure names on all 22 modules, on Windows
as in the recorded Linux run. The exported-parts block, the restriction of the allowance to the
toolchain's files and the gate on the first part's flag are each needed by at least one module;
five conditions of the new rule whose loss would let an exported part hold a constant other than
the one Lean derives, and the new rule of the targets report, are needed by none (finding 7,
measured).

## 1. The findings of review C

| Finding of review C | Severity there | In the reviewed version | Lines |
|---|---|---|---|
| 1. A module-system compiled file is compared only in part | gap | Partly closed. For every module whose first part has `isModule`, the `.olean` and `.olean.server` parts are read again and each of their constants must be the replayed constant of its name or that constant exported as an axiom by Lean's rule. Measured: `ExportedOnly`, `ExportedFlag` and `ExportedPartial` are rejected; the previous version accepts all three. Open: the import lists of those parts (finding 1) and the `.ir` part (finding 2). | 310-330, 380-414 |
| 2. Data stored inside names and terms is trusted | note | Stated in the header; unchanged in substance. Not stated in the paper (section 8). Open by choice. | 66-68 |
| 3. Two checks needed by no test module | fragile | Closed. `Hostile.MissingRecursor` and `Hostile.TamperedInductive` hold review C's code with a longer header. Measured: a copy without the "nothing else" direction now fails on `MissingRecursor` and nowhere else, and a copy that never compares inductive records fails on `TamperedInductive` and nowhere else (section 5). | 57, 469-473 |
| 4. `hostile.sh` counts a module that did not compile as rejected | fragile | Closed. The script stops if the program, the package or the crafted files are not built (`hostile.sh` 19, 22, 23), or if a module of `expected.txt` has no `.olean` (25-28), and it compares the names under which failures were recorded (45-47). A new weakness: the outputs of an earlier run can stand in for those of the current one (finding 6). | `hostile.sh` 19-28, 45-47 |
| 5. `balanced` cannot be false | note | Open and unchanged. The argument of review C still holds: the exported-parts block adds nothing to `order`, `emitted` or the kind counters. | 519-520, 524, 540 |
| 6. The targets report can call a theorem checked when a dependency failed | note | Closed: a target is FAILED when any name its traversal reaches has a failure. Measured in section 4. | 476-509 |
| 7. `#print axioms` reads a list recorded in a compiled file | note (paper) | Closed in the paper (subsection "Axioms", and the second-run branch of "Kernel replay"), and the cone program now lists the axioms among the constants of the cone (`verify/cut/CutMain.lean` 252-259). Section 7 compares the two relations. | |
| 8. Comments that say more than the code | note | The four cases are corrected (header 4-11, 51-56, 62-64; docstring 298-301). The new text says more than the code in other places (finding 11). | |

The three attacks that review C proposed for the suite (its section 3) are all added: (a) and
(b) as `MissingRecursor` and `TamperedInductive`, (c) as `ExportedOnly`, together with
`ExportedFlag` and `ExportedPartial`, which `verify/hostile/Craft.lean` writes. Review C's
remarks on the paper (its section 4) are taken up again in section 8.

## 2. Findings

Severities: *false success* (the program reports success on an input that its own header says
it rejects; I found none), *gap* (what the program checks is less than what the paper or the header says it
checks), *fragile* (correct today, but resting on something unchecked, or able to fail on
honest input), *note*.

**1. The import list of an exported part is not compared.** Severity: gap.
- Lines: 380-414 compare constants only; header 21-31.
- What can go wrong. A file that begins with `module` is compiled with its imports at level
  exported (`Lean/Elab/Import.lean:147-153`). `importModulesCore` then follows, for each
  imported module that is not imported with `all`, the import list of its main data
  (`Lean/Environment.lean:2199-2201`), and the main data is the first part, `.olean`
  (`mainModule?`, 2029-2031; `importAll` is true only at level private or under `import all`,
  2182). An import outside the module system, the program's included, follows the private
  part's list. Lean writes the same list into all three parts (`mkModuleData` copies the
  environment's header, 1858-1883), but nothing at import compares the lists, and the program
  compares only `constants` and `constNames`. So an exported part can bring in a module that the
  replay never loads.
- Scenario (measured). Appendix A writes, with `saveModuleDataParts`, a plain file `Exp.Bad`
  holding `theorem Exp.badFalse : False := True.intro`, and a three-part file
  `Exp.ImportsMore` whose parts all hold `theorem Exp.ok : True := True.intro` and whose
  `.olean` and `.olean.server` parts import `Init` and `Exp.Bad` while its private part imports
  `Init` only. The program on root `Exp.ImportsMore`: `failed 0`, exit 0 (the previous version
  too). The file `Exp/UseMore.lean` of Appendix A, which begins with `module`, says
  `public import Exp.ImportsMore` and proves `theorem Exp.fromMore : False := Exp.badFalse`,
  compiles, and `#print axioms` prints `'Exp.fromMore' does not depend on any axioms`.
- Bound (measured). The program on root `Exp.UseMore` fails with
  `Exp.fromMore (kernel) unknown constant 'Exp.badFalse'`; on root `Exp.Bad` it fails with a
  declaration type mismatch. A use inside the replayed closure is always checked against the
  private parts' closure, and `check.sh` imports `Main` from a file without `module`
  (`publish/public/verify/check.sh`, the file it writes begins `import Main`).
- Fix. Require each other part's `imports` and `isModule` to equal the private part's, which is
  what Lean writes.

**2. The `.ir` file is not read.** Severity: gap.
- Lines: 380-414; header 21 ("up to three parts").
- What can go wrong. A module-system file is written with two more files, `.ir.sig` and `.ir`
  (`writeModule`, `Lean/Environment.lean:1901-1915`), and the import loads them whenever a
  module's compiled code is needed (2190, `readIRPartsOfMod` 2093-2105). If a module is reached
  only through a private import of a module that a `module` file imports with `meta`, its data
  is not needed (2180) and `hasData` is false; then `mainModule?` is the `.ir` part
  (2032-2033), and the constants of the `.ir` part go into the importer's constant map
  (2313-2316, 2332-2344). Lean writes no constants there (`mkIRData`, 1891-1899:
  `constants := default`), but a hand-written `.ir` can hold any.
- Scenario (measured). Appendix A writes `Exp.IrCarrier`, three honest parts holding
  `theorem Exp.ok2 : True`, and an `.ir.sig` and `.ir` pair whose `.ir` holds
  `theorem Exp.irFalse : False := True.intro`. `Exp/Mid.lean` is `module` with
  `import Exp.IrCarrier`; `Exp/UseIr.lean` is `module` with `meta import Exp.Mid` and
  `theorem Exp.fromIr : False := Exp.irFalse`. Both compile, and `#print axioms` prints
  `'_private.Exp.UseIr.0.Exp.fromIr' does not depend on any axioms`. The program: on root
  `Exp.IrCarrier`, exit 0; on root `Exp.Mid`, exit 0; on root `Exp.UseIr`, exit 1 with
  `unknown constant 'Exp.irFalse'`. The previous version gives the same three results.
- Fix. Read the `.ir.sig` and `.ir` files when they exist and require them to hold no constants,
  or state the limit.

**3. A stray `.olean.server` file beside a plain `.olean` stops the program.** Severity: fragile
(a false failure).
- Lines: 388-392. The server file is read before the flag of the first part is tested.
- What can go wrong. Lean's import reads the other files only when the first part has
  `isModule` (`readModuleDataPartsOfMod`, `Lean/Environment.lean:2078-2091`). The program reads
  the `.olean.server` file whenever it exists, as the continuation of the `.olean` file. If it is
  not (a file left from another build, or copied), the region reader finds a pointer that lies in
  neither region (`fix_object_ptr`, `src/runtime/compact.cpp:518-539`; the message does not say
  which of the reader's unreachable cases was hit, and this is the one such a file reaches),
  `lean_unreachable` throws (`src/runtime/debug.h:22`), and the exception ends the program.
- Scenario (measured). `Exp.PlainStale` of Appendix A: an honest plain `.olean`, and beside it a
  copy of another module's `.olean.server`. The previous version: exit 0, `failed 0`. The
  reviewed version: exit 1, `uncaught exception: failed to read '….olean.server': 'unreachable'
  code was reached`. Lake deletes the `.olean.server`, `.olean.private` and `.ir` files when it
  rebuilds a module that has stopped beginning with `module` (measured), so this needs a file
  that Lake did not leave.
- Fix. Read the first part alone, test its flag, then read the server part against it, as
  `readModuleDataPartsOfMod` does.

**4. Two counts of the summary count every constant twice.** Severity: note (it reaches the
paper's numbers).
- Lines: 398-414, 526-527.
- Why. The loop at 398 runs over both the `.olean` and the `.olean.server` parts, and Lean
  writes the same constants into both (both come from the exported view of the environment,
  `mkModuleData` 1862-1877). Measured on the closure of `Lean`: in all 2,322 modules the two
  parts hold the same constants, 152,607 in each; the program's `exported-parts-compared` line
  gives 305,214 constants; of the 3,001 partial definitions, 685 are exported as axioms not
  marked unsafe, and `exported-axioms-of-partial-definitions-not-marked-unsafe` gives 1,370.
  On the closure of `Init` the line gives 198 for 99 axioms.
- Consequence. `paper/tools/numbers.py` fills `\replayexported`, `\stockexported` and
  `\stockpartialunmarked` from these two lines (267-269, 386-391), so each is twice the number
  of constants it names, if the two parts of Mathlib's files agree as those of Lean's library do
  [INFERENCE: Mathlib's files not examined; the factor two is measured on Lean's closure]. The
  generated `paper/numbers.tex` gives 1,288,568 and 1,062 for the last two, which would be
  644,284 constants and 531 axioms.
- Fix. Count the `.olean` part only, or say "entries in the two parts".

**5. The second reading of the exported parts costs memory that is not returned.** Severity:
note (fragile at the archive's scale).
- Lines: 388-392.
- Why (read in source). `lean_compacted_region_read` (`src/library/module.cpp:454-621`) maps a
  file at the address recorded in it (`MapViewOfFileEx`, 516; on Linux `mmap` with
  `MAP_FIXED_NOREPLACE`, 530-541) and, when that address is taken, reads the whole file into
  `malloc`ed memory (559-575) and rewrites every pointer in it (`region_reader::read`, slow
  path, `src/runtime/compact.cpp:659-685`). Here the address is always taken, because the
  import has mapped the same `.olean` and `.olean.server` files there and keeps them mapped
  (they are in `env.header.regions`, `Lean/Environment.lean:2368-2372`). The copies are never
  freed: nothing calls `CompactedRegion.free`, and freeing them would not be safe as written,
  since names taken from them are kept in `early`.
- It is safe. A pointer of the server part into the first part is translated into the new copy
  of the first part (`fix_object_ptr`, `src/runtime/compact.cpp:518-539`); the import's
  regions stay mapped for the life of the process; objects in a region carry no reference
  count, so nothing frees them.
- Cost (measured). On the closure of `Lean` the `.olean` files of module-system modules total
  335.4 MB and their `.olean.server` files 30.3 MB, together 348.7 MiB. On `Hostile.Plant`,
  whose closure is that of `Lean`, three runs of each version, alternating, with the peak
  counters of Windows read every 20 ms: the peak of private bytes was 2,623, 2,627 and 2,571 MiB with the previous version
  and 2,967, 2,921 and 2,995 MiB with the reviewed one (means 2,607 and 2,961, a difference of
  354 MiB); the peak working set rose by 357 MiB on average; and a run took 14.6 s instead of
  12.1 s (means). All six runs reported `failed 0`. For Mathlib's closure, which is where
  the archive's replay spends its memory (`publish/public/verify/replay.sh` says "up to about
  30 GB beyond the page cache"), the cost is the total size of those two parts of every
  module-system file in it; I did not measure it.

**6. `hostile.sh` can report on the outputs of an earlier run.** Severity: fragile.
- Lines: `hostile.sh` 38 (`mkdir -p`, nothing removed), 45 (the names are read from
  `replay-failures.txt`), 54 and 59-63 (the verdicts are written to and read from the report
  files).
- What can go wrong. The program writes its output files only at its end (ReplayMain 531-537).
  If a run stops earlier, by an uncaught exception as in finding 3, or by a panic under
  `LEAN_ABORT_ON_PANIC=1`, the module's directory keeps the `replay-failures.txt` of the last
  run that finished, the script reads those names, and the non-zero exit code counts as the
  expected rejection.
- Scenario (measured). I built a copy of the program that stops at its first failure
  without writing anything (one line added after line 200:
  `throw (IO.userError "stopped at the first failure")`), and ran `hostile.sh`, unchanged,
  with it. In a fresh output directory the script printed `HOSTILE-UNEXPECTED` (the four
  controls as expected, the eighteen others not, since no names were recorded). In the output
  directory of an earlier run of the reviewed program it printed `HOSTILE-OK`, with all 22
  modules "as expected". The script prints the hash of the program it ran, and
  `paper/tools/numbers.py` refuses a hash other than that of the published file (313-316), so
  this copy could not reach the paper; but the published program itself stops in this way on
  some inputs (finding 3), and on such a module the names checked would be an earlier run's.
- Two weaker points, both measured with GNU xargs 4.9.0 and bash on a two-line input:
  `xargs -L 1` (57) joins a line that ends in a blank with the next one, so the second module
  would not be run, and its report, if one is left from an earlier run, would be read; and the
  two `while read` loops (25-28, 59-63) skip a last line without a newline, which the `xargs`
  pipeline still runs, so that module's report would never be consulted. `expected.txt` has
  neither defect today (checked).
- Fix. Remove each module's outputs and report before running it; have the program write a
  marker of the run (or check that `replay-summary.txt` is newer than the start of the script);
  read `expected.txt` once, into an array, and fail on a malformed line.

**7. The suite needs only part of the new rule, and none of the new targets rule.** Severity:
fragile.
- Lines: 319-330, 404-405, 493.
- Measured (section 5). Of fourteen one-line copies of the program, those that remove the
  exported-parts block, make the allowance unconditional, gate on the replayed part's own flag,
  or accept an exported constant whose name the private part lacks each give a wrong verdict on
  at least one module. The copies that stop comparing the axiom's statement (322), its universe
  parameters (322), the key of an exported constant (404), or the mark of the axiom of an unsafe
  definition (326) or of an opaque constant (328), give the expected verdict and failures on
  all 22 modules. Each of these five would let an exported part hold a constant with another
  statement or name, or a safe axiom where Lean writes an unsafe one. The copies that drop the
  mark of the axiom of a theorem or of a safe definition (323, 325) pass too; they would only
  admit an exported axiom that is harder to use. `hostile.sh` names no targets, so the rule at 493 is not tested
  at all; the previous rule passes the suite (section 4 shows the difference).
- Fix. Add exported parts that hold: an axiom whose statement differs from the private theorem's;
  one whose universe parameters differ; a constant stored under another name; the axiom of an
  unsafe definition (and of an unsafe opaque constant) not marked unsafe. Run one module of the
  suite with targets, for instance `Hostile.FalseTheorem` with `Hostile.conclusion`, and expect
  `FAILED`.

**8. The allowance depends on how the toolchain's directory is spelled.** Severity: fragile (a
false failure); note.
- Lines: 338-340, 393.
- Why (read in source). `core` is `mFile.toString.startsWith coreLib`. `coreLib` is built from
  `findSysroot`, which returns `LEAN_SYSROOT` or the output of `lean --print-prefix`
  (`Lean/Util/Path.lean:180-187`); `mFile` comes from the search path, whose `LEAN_PATH`
  entries come before the toolchain's own directory (98-110, 117-120). The two strings agree
  only if both name the directory in the same spelling. The test has no separator after `lean`,
  so a directory beside the library whose name begins with it would also count.
- Measured. Under `lake env`, `LEAN_SYSROOT` and the `LEAN_PATH` entry are the same string, and
  the control `Hostile.Honest` passes with 198 entries allowed. With `LEAN_PATH` naming the same
  directory with forward slashes, the same run reports `failed 198`, all of them exported axioms
  of partial definitions in `Init`, and exits 1.
- Fix. Compare canonical paths (`IO.FS.realPath`), with a separator, or decide by the module's
  name (`Init`, `Std`, `Lean`, `Lake`) together with the location.

**9. Inside the module system, the toolchain's library offers the statements of partial
definitions as axioms a theorem may use.** Severity: note (Lean's behaviour, admitted by the
allowance; it concerns the paper).
- Measured. On the closure of `Lean`, all 3,001 partial definitions are named `…._unsafe_rec`;
  the `.olean` part holds 685 of them as axioms not marked unsafe, 1,111 as the definition
  itself and 1,205 not at all (private names), and none as an axiom marked unsafe; on the closure
  of `Lean`, `Std` and `Lake` together, 706 unmarked and none marked. A module compiled by the release marks both of its
  exported axioms of this kind unsafe (`Probe.Rec`, Appendix A). A file that begins with `module` and proves
  `theorem usesUnsafeRec : ∃ f : (Nat → Bool) → Array Nat → Array Nat, True :=
  ⟨@Array.popWhile._unsafe_rec Nat, trivial⟩` compiles, and `#print axioms` reports no axioms;
  the same text without `module` is refused (`(kernel) invalid declaration, safe declaration
  must not contain partial declaration 'Array.popWhile._unsafe_rec'`). The program rejects that
  theorem in its closure (`unknown constant 'Array.popWhile._unsafe_rec'`).
- So the allowance admits exactly what Lean ships, and the header states it correctly. It does
  mean that "which no theorem may use" in the paper holds only outside the module system
  (section 8).

**10. The server part's constants reach no kernel environment.** Severity: note.
- Read in source. `serverData?` (`Lean/Environment.lean:2036-2040`) is used only to build the
  extension state the language server reads (`serverBaseExts`, 2378, 2387); the constants of the
  kernel environment come from `mainModule?` at every level, the language server's included
  (2029-2031, 2313-2316). Comparing the server part's constants does no harm and protects
  nothing that Lean 4.33.1 uses; it doubles the counts (finding 4) and the memory (finding 5).

**11. What the new text says more than the code.** Severity: note.
- Header 21-23: "has up to three parts … The other parts are what a module inside the system
  sees." It has two more files, `.ir.sig` and `.ir`. A module inside the system sees the
  constants of the first part, of the modules its import list names (finding 1), of the private
  part under `import all`, and of the `.ir` part for a module loaded for its code only
  (finding 2); it sees no constant of the server part (finding 10).
- Header 24-26 and 47-49 ("fails unless every constant in them is …", "the exported parts to
  agree with the part replayed"): exact for constants; the other fields of those parts
  (imports, flags, extension entries) are not compared.
- Comment 385-387: "When the flag is not set, every importer receives the first part and the
  other files are never read." True of Lean; the program reads the server file whenever it
  exists (finding 3).
- Header 13-16: "every constant read that is neither unsafe nor partial must equal … the
  constant of that name in the environment the kernel built". The comparison (463-468) is of the
  version Lean keeps of each name; the further versions and the exported parts' constants are
  also read, and are checked or compared otherwise.
- Docstring 310-318: "or, for a theorem, a definition or an opaque constant that the module does
  not expose". Lean exports every theorem as an axiom unless the caller forces it
  (`Lean/AddDecl.lean:113-117`), exposed or not; the code (319-330) accepts both forms for all
  three kinds, which is right.

**12. `balanced` (review C, finding 5).** Severity: note. Unchanged (519-520, 524, 540), and
still unable to be false.

## 3. The exported-parts check

### (a) Is the gate right?

Read in source, at 4.33.1.

- *The flag.* Lean decides whether a file uses the module system by the flag of its first part:
  `readModuleDataPartsOfMod` reads the server and private parts only when the first part has
  `isModule` and throws if either file is missing (`Lean/Environment.lean:2078-2091`), and
  `getData?` selects a level only when the first part has the flag (2023-2026). The flags of the
  other two parts are never read. The program tests the same flag (392), after the import has
  succeeded, so a missing server or private part has already stopped the run. The gate is
  right. Measured: `Hostile.ExportedFlag` (private part marked as outside the module system) is
  rejected, and the copy that tests the replayed part's own flag instead accepts it (section 5).
- *`md`.* The program imports at level private (343, the default of `importModules`, 2438-2440).
  At that level `importAll` is true for every module (2182), so `mainModule?` is the private
  part when the first part has the flag and the first part otherwise (2025-2031), and
  `finalizeImport` puts exactly these into `header.moduleData` (2313-2316, 2368-2369). A file
  without `module` is compiled at the same level (`Lean/Elab/Import.lean:147-153`), and a
  `module` file that says `import all` receives the same part (2182, 2031). So `md` is what a
  non-module importer receives.
- *What a module inside the system receives.* For a module imported without `all`: the
  constants of the first part, in its private and, if the import is public, its public scope
  (2313-2344, 2349-2358), and the modules named by the first part's import list (2199-2201),
  which is finding 1. For a module that is loaded only for its compiled code: the constants of
  its `.ir` part (2032-2033), finding 2. In the language server the constants still come from
  `mainModule?`; the server part feeds only extension state (2036-2040, 2378, 2387), finding 10.
- *Missing and extra files.* With the flag set, a missing `.olean.server` or `.olean.private`
  stops the import before the program's check. Without it, Lean never opens them, and the
  program opens `.olean.server` if it exists (finding 3). An `.olean.private` file beside a
  plain `.olean` is ignored by both.
- *`.ir.sig` and `.ir`.* Only the `.ir` part's constants can reach a kernel environment, and only
  as in finding 2; the `.ir.sig` part is the main data of nothing outside `leanir`
  (`irData?`, 2045-2053).
- *`extraConstNames`.* They go only into `const2ModIdx`, and only from the IR data (2345-2347),
  never into a constant map. They decide to which module a name is attributed, which is how
  `#print axioms` chooses the recorded list it reads (`Lean/Util/CollectAxioms.lean:101-111`),
  but not what any kernel holds. The program does not compare them; for its claim that is
  harmless.
- *Extension entries* of the other parts (attributes, instances, simplification sets, data for
  the compiler) are not compared either. They reach the elaborator and the compiler of a module
  inside the system, not its kernel.

What was searched for a false success, beyond the two findings: every file that the 4.33.1
import reads for a module (2078-2105, 2231-2244), every field of `ModuleData` that reaches a
kernel environment (2312-2372), every level at which a file is compiled
(`Lean/Elab/Import.lean:147-153`), the export rule (below), the allowance and its gate (finding
8), the second reading of the files (finding 5), the new targets rule (section 4), and the exit
condition (540), which is unchanged. The new block only appends to `early` (399-413), every entry
of which becomes a failure (431); it can stop the run with an exception, never make it succeed.

### (b) Is `exportedForm` Lean's rule? The allowance

Read in source. `Lean/AddDecl.lean` (`addDeclCore`, 101-160) writes into the exported view:
for a theorem, an axiom with the theorem's name, universe parameters and type and
`isUnsafe := false`, unless the caller forces exposure (113-117); for a definition, or a mutual
block of one, outside an exported context, an axiom with `isUnsafe := defn.safety != .safe`
(118-122); for an opaque constant there, an axiom with the opaque constant's own `isUnsafe`
(123-127); an axiom as it is (128); for every other declaration (inductive types, the quotient,
mutual blocks of several definitions) the kernel's constants as they are, through
`Environment.addDeclCore`, which puts the same constant into both views
(`Lean/Environment.lean:701-731`); and nothing for a declaration whose names are all private
(`Lean/AddDecl.lean:138-144`) unless `backward.privateInPublic` is set, in which case the
constant as it is. `mkModuleData` writes, at the exported and server levels, the constants of
the exported view, taking the kernel's own constant for the old code generator's auxiliary names
(`Lean/Environment.lean:1866-1877`).

`exportedForm` (319-330) accepts `p` itself, or, when `p` is a theorem, definition or opaque
constant, an axiom with `p`'s name, universe parameters and type marked unsafe exactly as above.
That is Lean's rule for the marks. It is looser in two harmless ways: it accepts either form for
every theorem, definition and opaque constant, whether or not Lean would have exposed it (the
exposed form is `p`, which is replayed; the axiom states the type of a constant that is replayed
or skipped), and it compares terms up to binder names and annotations (the derived `BEq` of
line 57, `Expr.eqv`). It accepts a missing constant, as Lean omits private ones. Measured on the
closure of `Lean` with the rule copied unchanged: 305,214 entries, no mismatch; without the
allowance, exactly the 1,370 entries of finding 4 fail.

The allowance (327, 393). The header (26-31) and the docstring (314-318) say that the toolchain's
library leaves the axiom of a partial definition unmarked and that files compiled by 4.33.1 mark
it. Measured: on the closure of `Init` 99 such axioms, of `Std` 146, of `Lean` 685, of `Lean`,
`Std` and `Lake` together 706, every one unmarked and every partial definition named
`…._unsafe_rec`; a module that I compiled with the release (`Probe.Rec`, Appendix A) has four
recursive definitions: the `_unsafe_rec` forms of the two that are public and not exposed, one by
well-founded recursion and one declared `partial`, are exported as axioms marked unsafe; that of
the exposed one is exported as the definition itself, and that of the private one not at all.
The statement in the header is right, and so is its last sentence: the program never passes the partial definition to the
kernel, so the unmarked axiom states a type the program has not checked. Finding 9 shows what
Lean does with such an axiom; finding 8 shows how the allowance depends on the environment.

### (c) False failures, and the second reading of the files

On honest files compiled by Lean the rule found nothing on the closure of `Lean` (above), and
the suite's controls pass. The program can still fail on input that Lean's import accepts: a
stray `.olean.server` beside a plain `.olean` (finding 3, measured), a toolchain directory
spelled differently in `LEAN_SYSROOT` and `LEAN_PATH` (finding 8, measured), and memory: the
second reading is safe but keeps a full copy of every `.olean` and `.olean.server` of a
module-system file until the end (finding 5). I did not run the program on Mathlib, so whether
Mathlib's files raise anything I cannot say from my own runs; `paper/tools/numbers.py` stops
unless the recorded run on Mathlib reports `failed 0`.

## 4. The targets report

Read in source (476-509). The traversal visits every name reachable through `refsOf` in the
environment the kernel built and records a name as bad when it has a failure, before looking it
up (493), so a failed name with no constant is caught too. Can a target be called checked when
something it depends on failed or was skipped? A constant is in the kernel's environment because
the kernel accepted it, because the main thread added it while its check failed (then it has a
failure), or because the kernel generated it (then the comparison gives it a failure if it
differs, or if no file holds it, 463-473). A constant that is unsafe or partial is never added
(417-420, 434), and the kernel looks up every constant of a term it checks and throws
`unknown constant` for an absent one (`src/kernel/type_checker.cpp:101-122`,
`src/kernel/environment.cpp:78-84`), so a replayed constant that refers to a skipped one fails
its own check. Hence every path from a target to a failed or skipped constant passes through a
name with a failure, and the target is reported FAILED. Two residues, both notes: a failure
recorded under a module's name (357, 399) is reached by no traversal, although the run fails;
and a target that failed its own check is reported as "1 of the constants it depends on failed,
the first being" the target itself.

Measured, with the reviewed version, the previous one, and a copy of the reviewed one with the
previous rule (copy 14 of section 5). `Tgt.AfterUnsafe` is a scratch module (Appendix A) that
imports `Hostile.UsesUnsafe` and proves `theorem Hostile.afterUnsafe : True :=
Hostile.fromUnsafe`. Every run below that has a failure exits with code 1, in all three versions.

| Root, and the target asked about | What it depends on | Previous version, and copy 14 | Reviewed version |
|---|---|---|---|
| `Hostile.FalseTheorem`, `Hostile.conclusion` | `Hostile.falseProved`, which fails its check | "a theorem, checked by the kernel; it depends on 5 constants; axioms: []" | FAILED, first `Hostile.falseProved` |
| `Hostile.MissingRecursor`, `Hostile.usesRec` | `Hostile.Bit.rec`, which the kernel made and no file holds | checked, 10 constants, axioms: [] | FAILED, first `Hostile.Bit.rec` |
| `Tgt.AfterUnsafe`, `Hostile.afterUnsafe` | `Hostile.fromUnsafe`, whose proof uses the unsafe `Hostile.unsafeNumber`, which is not replayed | checked, 8 constants, axioms: [] | FAILED, first `Hostile.fromUnsafe` |
| `Hostile.KeyMismatch`, `Hostile.phantomNonempty` | `Hostile.Phantom`, which fails | checked, 7 constants, axioms: [] | FAILED, first `Hostile.Phantom` |
| controls: `Hostile.fromAxiom`, `Hostile.bySorry`, `Hostile.Honest.size_pos` | | | checked; axioms `[Hostile.assumed]`, `[sorryAx]`, `[]`; exit 0 |

## 5. Regression, and what the test modules test

**Is there a regression?** Read in source: the diff from the previous version adds the
exported-parts block (380-414), whose only effects are entries in `early`, each a failure (431),
counters, and the possibility of an exception, which ends the run with a non-zero code; it
replaces the targets rule by a stricter one (476-509); the rest is comments, the docstring at
298-301, the variable `sysroot` (338-340) and two lines of the summary (526-527). Nothing that
decides the exit code (540) is weakened, and no failure can be removed. So no input the previous
version rejected can be accepted now. The one change in the other direction is finding 3.

**The suite** (measured). Both versions were built from byte-identical copies (hashes checked) in
a scratch copy of `verify/hostile`, built with `lake build` and `lake exe craft`. The reviewed
version was run by `hostile.sh` itself, unchanged, with leanchecker in both modes, and printed
`HOSTILE-OK`; its output is identical to the recorded `verify/results/hostile.txt`, which was
made on Linux, except for one line of `leanchecker`'s error output for `MissingConstructor`
(a backtrace there, the exception's message here). The previous version was run on the same 22
modules by a loop that does what `hostile.sh` does for the replay alone.

| Module | Expected of the replay (`expected.txt`) | Previous version | Reviewed version | Failures recorded by the reviewed version, by name | leanchecker | leanchecker `--fresh` |
|---|---|---|---|---|---|---|
| Honest | accepts | accepts | accepts | none | accepts | accepts |
| Plant | accepts | accepts | accepts | none | accepts | accepts |
| Axiom | accepts | accepts | accepts | none | accepts | accepts |
| Sorry | accepts | accepts | accepts | none | accepts | accepts |
| FalseTheorem | rejects | rejects | rejects | `Hostile.falseProved` | rejects | rejects |
| WrongValue | rejects | rejects | rejects | `Hostile.three` | rejects | rejects |
| UsesUnsafe | rejects | rejects | rejects | `Hostile.fromUnsafe` | rejects | rejects |
| TamperedRecursor | rejects | rejects | rejects | `Hostile.Two.rec` | rejects | rejects |
| TamperedConstructor | rejects | rejects | rejects | `Hostile.Box.mk` | rejects | rejects |
| DupBogusLast | rejects | rejects | rejects | `Hostile.Dup.twice` | accepts | rejects |
| DupBogusFirst | rejects | rejects | rejects | `Hostile.Dup.twice` | accepts | accepts |
| MissingConstructor | rejects | rejects | rejects | `Hostile.Coin`, `Hostile.Coin.heads`, `Hostile.onlyHeads` | rejects | rejects |
| KeyMismatch | rejects | rejects | rejects | `Hostile.Phantom`, `Hostile.phantomBody` | rejects | rejects |
| MissingRecursor | rejects | rejects | rejects | `Hostile.Bit.rec` | accepts | accepts |
| TamperedInductive | rejects | rejects | rejects | `Hostile.Chain` | accepts | accepts |
| FakeQuotient | rejects | rejects | rejects | `Hostile.fakeQuot` | accepts | accepts |
| AfterFakeQuotient | rejects | rejects | rejects | `Hostile.fakeQuot`, `Hostile.falseFromQuot` | accepts | rejects |
| FakeInductive | rejects | rejects | rejects | `Hostile.fakeInductive` | accepts | accepts |
| ConstructorIsUnsafe | rejects | rejects | rejects | `Hostile.Claim`, `Hostile.claimed` | accepts | accepts |
| ExportedOnly | rejects | **accepts** | rejects | `Hostile.exportedFalse` | accepts | accepts |
| ExportedFlag | rejects | **accepts** | rejects | `Hostile.exportedFalse` | accepts | accepts |
| ExportedPartial | rejects | **accepts** | rejects | `Hostile.spin` | accepts | accepts |

For every module the names recorded by the reviewed version are exactly those of the fifth
column of `expected.txt`, and on the first nineteen the previous version recorded the same names.
The three `Exported*` modules record their failure twice, once for each of the two parts read
(`hostile.sh` collapses repeated names). leanchecker rejects 7 of the 18 modules that must be
rejected in its ordinary mode and 9 with `--fresh`.

**The copies** (measured). Each copy differs from the reviewed version in one line, given here by
its line number in the reviewed version; each was built and run on all 22 modules as above. "As
expected" means the expected verdict and exactly the expected names.

| Copy | Change | Modules not as expected |
|---|---|---|
| 1 | 390: `if (← sFile.pathExists) then` becomes `if (← sFile.pathExists) && false then` (the exported-parts block removed) | ExportedOnly, ExportedFlag, ExportedPartial (accepted) |
| 2 | 327: `a.isUnsafe \|\| core` becomes `a.isUnsafe \|\| true` (the allowance made unconditional) | ExportedPartial (accepted) |
| 3 | 392: `parts[0]?.any (·.1.isModule)` becomes `md.isModule` (the gate on the replayed part's own flag) | ExportedFlag (accepted) |
| 4 | 412-413: an exported constant whose name the private part lacks is accepted | ExportedOnly, ExportedFlag (accepted) |
| 5 | 322: `a.type == p.type` becomes `true` | none |
| 6 | 322: `a.levelParams == p.levelParams` becomes `true` | none |
| 7 | 404: `if e.name != n then` becomes `if false then` | none |
| 8 | 326: `.unsafe => a.isUnsafe` becomes `.unsafe => true` | none |
| 9 | 328: `.opaqueInfo o => a.isUnsafe == o.isUnsafe` becomes `.opaqueInfo o => true` | none |
| 10 | 323: `.thmInfo _ => !a.isUnsafe` becomes `.thmInfo _ => true` | none |
| 11 | 325: `.safe => !a.isUnsafe` becomes `.safe => true` | none |
| 12 | review C's copy N: 472, `for n in extra do` becomes `for n in extra.filter (fun _ => false) do` | MissingRecursor (accepted) |
| 13 | review C's copy I: line 57 replaced by `instance : BEq InductiveVal := ⟨fun _ _ => true⟩` and `deriving instance BEq for QuotKind, QuotVal, ConstantInfo` | TamperedInductive (accepted) |
| 14 | 493: `if failed.contains x then` becomes `if failed.contains x && x == t then` (the previous targets rule) | none |

So the suite depends on the exported-parts block, on the restriction of the allowance to the
toolchain's files and on the gate on the first part's flag (copies 1-3), on the two checks
review C found untested (copies 12-13), and on the absent-name branch (copy 4), but not on
copies 5-9, which would admit an exported constant other than the one Lean derives, nor on
copies 10-11 (harmless directions) or 14 (finding 7).

## 6. `hostile.sh`, read as a hostile reader would

Can it print `HOSTILE-OK` without having tested a module? Read in source, line numbers of
`publish/public/verify/hostile.sh`:

- *A module that did not compile.* No longer counted as rejected: the script stops if the
  program does not build (19), if the package does not build (22), if the crafted files are not
  written (23), or if a module of `expected.txt` has no `.olean` (25-28). It checks the main
  `.olean` only; a three-part file missing its private part makes the replay fail at import,
  which is then judged by its names, as below. A module whose source was deleted keeps its old
  `.olean` in `.lake`, and would be tested on that.
- *The names.* For each module the names under which the replay recorded failures must equal the
  fifth column of `expected.txt` as sets (45-47). The messages are not compared, so a module that
  fails for another reason under the same name passes, and a name recorded twice counts once.
- *Outputs of an earlier run.* This is the weakness of finding 6: neither the module's replay
  directory (38) nor its report file (54) is cleared before the module is run, and the program
  writes its outputs only when it reaches its end. Measured as described there.
- *Parallel `xargs` and the exported function.* `one` is exported with `export -f` and called
  through `bash -c` (56-57), with `out` and `prog` exported; `verdict` is defined inside `one`;
  every file `one` writes has the module's name in it, so parallel calls do not share files;
  the working directory is the package's, inherited from the script. I found nothing wrong
  there. `xargs -L 1` joins a line ending in a blank with the next (finding 6), and `xargs`
  interprets quotes and backslashes in its input, which `expected.txt` does not contain.
- *The final loop* (59-63) decides `HOSTILE-OK` from the last line of each report file. A
  missing report file gives an empty last line and `HOSTILE-UNEXPECTED`; a report file left
  from an earlier run gives that run's verdict. A last line of `expected.txt` without a newline
  is skipped by this loop and by the check of compiled files (finding 6).
- *Provenance.* Line 20 prints the hash of the source file, not of the binary; `lake build
  replay` at 19 rebuilds the binary from that source when it has changed, so the two agree
  unless the source changes between 19 and 20.

## 7. `CONE-AXIOMS` and `collectAxioms`

Read in source. `CONE-AXIOMS` (`verify/cut/CutMain.lean` 252-259) lists the axioms (by
`env.find?`, so in the version Lean's import keeps) among the names of the cone, and the cone
(61-92) follows, from each constant reached: the constants of its type, those of its value for a
definition, theorem or opaque constant, the constructors of an inductive type, the inductive type
of a constructor, and the structure named by every projection (`usedConstsImpl`, 32-56; the projection at 52).
`collectAxioms` (`Lean/Util/CollectAxioms.lean`) records a constant if it is an axiom and
follows: the type of an axiom, of a constructor and of a recursor; the type and value of a
definition, theorem or opaque constant; the type and the constructors of an inductive type;
nothing for a quotient constant (56-67). Its `getUsedConstants` does not enter the structure of
a projection (`Lean/Util/FoldConsts.lean:35`). Neither follows the rules of a recursor.
So the relation of the cone contains that of `collectAxioms`, with three more edges: from a
constructor to its inductive type (which its type already mentions), from a projection to its
structure, and from a quotient constant to its type. On the same terms `CONE-AXIOMS` can
therefore contain more than the walk of `collectAxioms`, never less.

Two differences are not in the relation but in the terms walked. For a constant of an imported
module, `collectAxioms` does not walk at all: it takes the list recorded in the compiled file of
the module that the import attributes the name to (41-44, 101-111), which is the first module
in import order that declares it (`Lean/Environment.lean:2344`) or lists it in the
`extraConstNames` of its IR data (2345-2347); it walks only when that file records no list for
the name. The cone walks the terms of the version Lean keeps, which for a name declared by
several modules is in general another module's version (2338-2343). The replay's targets report
follows yet more edges (the rules and blocks of recursors, the constants that literals unfold
to, 142-155 with 93-96) in the environment the kernel built.

## 8. The paper

Read in `paper/sections/verification.tex` and, for `\replaystatus`, `paper/version.tex`, at the
hashes given at the top; line numbers are of those versions. Each item is a sentence that says
more than the program or the scripts do, with a correction. Where a sentence depends on a number,
I took its value from the generated `paper/numbers.tex` (hash at the top) where it is defined
there, and otherwise judged the macro by what `paper/tools/numbers.py` puts in it; the macros of
the second run (`\replayexported` and the others) are not yet defined.

*Kernel replay, both branches.*

- 125-127: "\replaydecls{} are neither unsafe nor partial, and they are what a replay examines,
  together with the further declarations of names that more than one module declares." Holds;
  the program now also compares the constants of the exported parts, which the sentence need not
  mention.

*Kernel replay, second run.*

- 140-142: "So, apart from the unsafe and partial declarations, the compiled files hold, as a
  file outside Lean's module system reads them, exactly what the kernel produces from the
  declarations in them." Two qualifications. "Exactly" holds for the version Lean's import keeps
  of each name; the further versions were each accepted by the kernel, not compared field by
  field (`versionsAgree`, 302-308, compares kind, statement, universe parameters and safety).
  And "as … reads them" means through Lean's reader, which trusts the hashes and flags stored in
  names and terms (review C, finding 2; the program's header says so at 66-68, the paper does
  not). Correction: "…, for the version of each name that Lean's import keeps, exactly what the
  kernel produces from the declarations in them, as Lean's reader of compiled files presents
  them; every further version of a repeated name was accepted by the kernel."
- 142-146: "Mathlib and Lean's library use the module system, in which a compiled file has
  further parts that only a module inside the system reads; Lean derives them from the same
  declarations, each unchanged or reduced to an axiom with the same statement, and the program
  fails unless the \replayexported{} constants in those parts are exactly that." Three things.
  (i) A module inside the system receives more than the constants of those parts: the modules
  named by the exported part's import list, and, for a module loaded for its compiled code only,
  the constants of its `.ir` file; the program compares neither (findings 1 and 2, measured). The
  server part's constants reach no kernel environment (finding 10). (ii) Lean also omits private
  declarations from those parts. (iii) `\replayexported` counts each constant once per part,
  that is twice (finding 4). Correction: "…; Lean writes into them the same declarations, each
  unchanged, reduced to an axiom with the same statement, or left out, and the program fails
  unless each of the constants they hold (\replayexported{} entries in the two parts, each
  constant appearing in both) is exactly that. It does not compare the import lists of those
  parts, or the `.ir` file, through which a module inside the system can also receive
  constants."
- `\replaystatus` (`paper/version.tex` 29-30): "Lean's own replay does not check them either, and
  the kernel accepts no theorem or safe definition that refers to one." Inside the module system
  this is not so for the toolchain's library: there the statement of a partial definition is a
  safe axiom of the same name, which a theorem in a `module` file may use; the kernel accepts it
  and `#print axioms` does not report it (finding 9, measured). The replay rejects such a theorem
  when it is in the closure (measured). Correction: add "outside the module system; inside it,
  Lean's distributed library presents N of them as axioms not marked unsafe, which a theorem may
  use and `#print axioms` does not list", with N counted once (finding 4).
- 154-156: "This matters because \lean{#print axioms}, for a theorem of an imported module,
  prints a list that was recorded in the compiled file when it was written; it does not walk the
  terms again." Correct in substance (`Lean/Util/CollectAxioms.lean:41-44, 101-111, 120-146`). Two
  precisions, if wanted: the file is that of the first module in import order that declares the
  name, which for a repeated name need not be the version Lean keeps (section 7); and if that
  file records no list for the name, the terms are walked.
- 156-159: "\lean{riemannHypothesis} depends in the kernel's environment on
  \replayconeconstants{} constants, counted through types, values, constructors, recursors and
  their rules; the cone of \cref{sec:cone}, which follows types, values and the link between an
  inductive type and its constructors, has \conesize{}." Both relations also follow the structure
  named by a projection (ReplayMain 108, CutMain 52), and the replay's also the constants into
  which the kernel unfolds literals (ReplayMain 93-96). Correction: add "projections" to both
  lists and "literals" to the first.

*Kernel replay, first run.* The sentences describe the first form of the program, which I did not
review. Of those about the current program: "after the last declaration it now compares the
environment the kernel built with what it read from the compiled files, constant by constant and
in both directions, and it refuses an inductive type whose listed constructors are not all there"
(181-183) holds (463-473 and 254-287 of the reviewed version). That the corrected program was run on
the test modules holds for the reviewed version (the recorded `hostile.txt` carries its hash);
that it was run on Mathlib, and which version runs on the archive, I could not check.

*The checker.*

- 189-193: "It imports once, orders the declarations, and runs the kernel checks …". The program
  also reads the `.olean` and `.olean.server` parts of every module-system file a second time
  and keeps the copies (finding 5); that changes the memory it needs, which
  `publish/public/verify/replay.sh` states.
- 200-202 (second run): "our replay of the archive used \replaycpuhours{} hours of processor
  time, so Lean's checker would need about that long." An inference, as review C said; it holds
  only if the two times on Mathlib, in the sentence before, are close, and the program now does
  work on module-system files that `leanchecker` does not. Correction: scale by the ratio
  measured on Mathlib.
- 226-227: "The program now reads the other parts and requires them to hold what Lean derives
  from the part replayed". It requires their constants to; not their import lists, and it does
  not read the `.ir` file (findings 1, 2). Correction: "requires every constant they hold to be
  what Lean derives from the part replayed".
- 229-233: "The tests below were made with the program whose SHA-256 begins
  {\small\ttfamily \hostileprogramsha}. So was the replay reported here. The first run … had
  given the same counts …". `numbers.py` checks the first statement (it compares the hash in
  `hostile.txt` with the published file, numbers.py 313-316), but not the second: it reads the
  replay's hash into `\replayprogramsha` (278) and uses it nowhere, and compares it with nothing.
  Nor the third: it computes `\replayrunsagree` (289-294), the text does not use it, and the
  script does not stop when it is false. Correction: make `numbers.py` stop unless the replay's
  hash equals the tests' and the counts agree, or print both hashes.
- 238-244: "\hostilebad{} of them have, in their import closure, a compiled file that holds
  something the kernel never accepted … A successful build and a clean list of axioms do not,
  then, by themselves show that a theorem holds; they show it for code that does not write into
  the environment behind the kernel's back." The second sentence needs the imported files too:
  `Exp.UseMore` and `Exp.UseIr` write nothing behind the kernel's back, compile, have a clean
  list of axioms and prove `False`, because a file they import was written directly (findings 1
  and 2, measured). Correction: "… for code that does not write into the environment behind the
  kernel's back, and for compiled files that Lean itself wrote".
- 245-249: "Our program rejects all \hostilebad{}, each with exactly the failures its design
  predicts, and accepts the \hostilecontrols{} controls. Lean's checker with --fresh rejects
  \hostilefreshrejects{} of the \hostilebad{}, and in its ordinary mode …
  \hostiledefaultrejects{}." Holds. The first sentence is measured by names (section 5); the
  generated values, 18, 4, 9 and 7, and the two `leanchecker` columns of the generated table agree
  with the recorded `hostile.txt` and with my run, row by row. The `lean4lean` column and
  `\independentfreshrejects` I did not check.
- 257-264: "the \stockexported{} constants in their exported parts are what Lean derives from the
  parts replayed, with one qualification. For a recursive definition that is compiled to code,
  Lean stores a second constant, marked partial, which no theorem may use and which a replay
  does not examine. Lean \leanversion{} exports the statement of such a constant as an axiom
  marked unsafe; in the files of Lean's own library as distributed, \stockpartialunmarked{} such
  axioms are not marked." The two counts, 1,288,568 and 1,062, are of entries in two parts, that
  is, if Mathlib's parts agree as Lean's do, 644,284 constants and 531 axioms (finding 4);
  "which no theorem may use" holds outside the module system only (finding 9, measured); and "what Lean derives" is about
  their constants (findings 1, 2). The claim about marking is right (measured, section 3 (b)).
  Correction: halve the counts or call them entries; "which no theorem outside the module system
  may use; inside it, the unmarked axiom may be used, and `#print axioms` does not list it".
- 264: "The program allows that in those files and nowhere else, and counts them." Holds,
  by the location of the file (finding 8).
- 273-276, `lean4lean`: "It uses Lean's representation of terms, with Lean's own substitution on
  them, and Lean's reader of compiled files; type inference, definitional equality and the
  treatment of inductive types are its own." I did not examine `lean4lean`, and say nothing
  about this sentence or about what its `--fresh` mode reads. If it reads the parts that an
  import outside the module system reads, as `leanchecker` does, it shares the
  limits of findings 1 and 2 [INFERENCE: not checked].

## Method and limits

**Read.** The reviewed file in full, and its difference from the previous version; review C (`notes/review-replay-program-C.md`); everything in
`verify/hostile/`; `publish/public/verify/hostile.sh`, and the parts of `check.sh` and
`replay.sh` cited; the difference in `verify/cut/CutMain.lean` and the rest of that file as
cited; the two subsections of `paper/sections/verification.tex`, `\replaystatus` in
`paper/version.tex`, and the parts of `paper/tools/numbers.py` that fill the macros used there.
Lean 4.33.1, from the `src/lean/` directory of the release archive: `Lean/Environment.lean`
(`mkModuleData`, `writeModule`, `readModuleDataParts`, `saveModuleDataParts`, `ImportedModule`
and its `publicModule?`, `getData?`, `mainModule?`, `serverData?`, `irData?`,
`readModuleDataPartsOfMod`, `readIRPartsOfMod`, `importModulesCore`, `subsumesInfo`,
`finalizeImport`, `importModules`, `Environment.addDeclCore`, `find?`), `Lean/AddDecl.lean`,
`Lean/Util/CollectAxioms.lean`, `Lean/Util/FoldConsts.lean`, `Lean/Util/Path.lean`,
`Lean/Elab/Import.lean`, `Lean/Setup.lean` (`Import`, `ImportArtifacts`),
`Lean/CompactedRegion.lean`. From tag `v4.33.1` of the Lean repository:
`src/library/module.cpp`, `src/runtime/compact.cpp`, `src/runtime/debug.h`,
`src/kernel/type_checker.cpp` (`infer_constant`), `src/kernel/environment.cpp` (`get`).

**Ran.** On a Windows x64 computer with 32 logical processors, using the release archive
`lean-4.33.1-windows.zip` from the Lean project's releases (SHA-256
`c39360867edfff6b090f20c16e18581c969ce839b71e813d76022ec04ec73e4d`; `lean --version`: commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), in a scratch directory outside the repository,
deleted afterwards:
- built byte-identical copies of the reviewed and the previous `ReplayMain.lean` (hashes checked)
  and the fourteen copies of section 5, each with `lake build replay`;
- built a copy of `verify/hostile` with `lake build` and `lake exe craft`, ran `hostile.sh`
  itself, unchanged, with `HOME` pointing at a directory whose `.elan/env` puts the release first
  on `PATH`, and four modules at a time; and ran the previous version and the copies on the same
  22 modules with a loop that does what `hostile.sh` does for the replay, three or four modules at
  a time, with `LEAN_ABORT_ON_PANIC=1`;
- wrote the scratch files of Appendix A, compiled the `module` files there with `lean -o`, and ran
  both versions on them;
- read the parts of every module in the closures of `Init`, `Std`, `Lean` and `Lake` of the
  release, with the rule of `exportedForm` copied unchanged, to obtain the counts of findings 4
  and 9 and section 3 (b); compiled a module with four recursive definitions to see how 4.33.1
  marks their exported axioms; compiled the two files of finding 9;
- changed a module from `module` to a plain file and rebuilt it with Lake (finding 3);
- ran the targets report of section 4, the run of finding 8 with `LEAN_PATH` spelled with
  forward slashes, the runs of finding 6, and the measurement of finding 5.

**Not done, and not checked.**
- I did not run anything on the archive, on Mathlib or on the published results, and did not
  run `replay.sh`, `stock.sh`, `sample.sh` or `independent.sh`. So I cannot say whether Mathlib's
  files raise anything under the new rule, what its second reading costs there, or whether the
  counts that the paper takes from the run on Mathlib are twice the numbers of constants, as they
  are on Lean's closure.
- I did not repeat the Linux run; the recorded `hostile.txt` was made there and agrees with mine.
- I did not examine `lean4lean`, nor what its `--fresh` mode reads.
- I did not examine the first form of the program, which the first-run branch of the paper
  describes.
- I did not test the false failure of finding 8 under a symbolic link, only under another
  spelling; nor finding 3 with a stale file left by any tool other than a copy.
- I did not look for elaboration-level effects of the exported parts' extension entries, which do
  not reach the kernel.
- I did not try the `ImportArtifacts` route by which Lake can give the compiler other copies of
  a module's parts than those on `LEAN_PATH` (`Lean/Setup.lean:69-93`,
  `Lean/Environment.lean:2231-2244`); the program and `check.sh` read the files on `LEAN_PATH`.
- Apart from this report nothing in the repository was written.

## Appendix A: the scratch files

A Lake package with an executable `craft` whose root is the file below, run from the package's
directory after `lake build`. The files `Exp/UseMore.lean`, `Exp/Mid.lean` and `Exp/UseIr.lean`
were compiled afterwards with `lean -o .lake/build/lib/lean/Exp/<name>.olean Exp/<name>.lean`
(`Exp.Mid` before `Exp.UseIr`), with `LEAN_PATH` set to the package's `.lake/build/lib/lean`.
`Tgt/AfterUnsafe.lean` was compiled the same way against a built copy of `verify/hostile`.

```lean
import Lean
open Lean

/-
Scratch files for the fourth review of the replay program (not part of the repository).

(A) `Exp.ImportsMore`: a module-system file whose `.olean` and `.olean.server` parts list one more
    import than its private part: `Exp.Bad`, a plain file holding `theorem Exp.badFalse : False`
    with the proof `True.intro`. Every constant of the three parts is the same honest theorem.
(B) `Exp.IrCarrier`: an honest module-system file whose `.ir` part holds
    `theorem Exp.irFalse : False := True.intro`.
(C) `Exp.Plain`: an honest plain file; `Exp.PlainStale` the same with, beside it, an
    `.olean.server` file copied from another module (a stale part).
-/

def lib : System.FilePath := ".lake/build/lib/lean"

def md (imports : Array Import) (cs : Array ConstantInfo) (isModule := false) : ModuleData :=
  { isModule, imports, constNames := cs.map (·.name), constants := cs, extraConstNames := #[],
    entries := #[] }

def thm (n : Name) (type value : Expr) : ConstantInfo :=
  .thmInfo { name := n, levelParams := [], type, value, all := [n] }

def initImp : Import := { module := `Init }

def main : IO Unit := do
  let dir := lib / "Exp"
  IO.FS.createDirAll dir
  -- (A)
  saveModuleData (modToFilePath lib `Exp.Bad "olean") `Exp.Bad
    (md #[initImp] #[thm `Exp.badFalse (mkConst ``False) (mkConst ``True.intro)])
  let p := modToFilePath lib `Exp.ImportsMore "olean"
  let ok := thm `Exp.ok (mkConst ``True) (mkConst ``True.intro)
  let more : Array Import := #[initImp, { module := `Exp.Bad, isExported := true }]
  saveModuleDataParts `Exp.ImportsMore #[
    (p, md more #[ok] (isModule := true)),
    (p.addExtension "server", md more #[ok] (isModule := true)),
    (p.addExtension "private", md #[initImp] #[ok] (isModule := true))]
  -- (B)
  let q := modToFilePath lib `Exp.IrCarrier "olean"
  let ok2 := thm `Exp.ok2 (mkConst ``True) (mkConst ``True.intro)
  saveModuleDataParts `Exp.IrCarrier #[
    (q, md #[initImp] #[ok2] (isModule := true)),
    (q.addExtension "server", md #[initImp] #[ok2] (isModule := true)),
    (q.addExtension "private", md #[initImp] #[ok2] (isModule := true))]
  saveModuleDataParts (`Exp.IrCarrier ++ `ir) #[
    (q.withExtension "ir.sig", default),
    (q.withExtension "ir",
      md #[initImp] #[thm `Exp.irFalse (mkConst ``False) (mkConst ``True.intro)] (isModule := true))]
  -- (C)
  let ok3 := thm `Exp.ok3 (mkConst ``True) (mkConst ``True.intro)
  saveModuleData (modToFilePath lib `Exp.Plain "olean") `Exp.Plain (md #[initImp] #[ok3])
  let ok4 := thm `Exp.ok4 (mkConst ``True) (mkConst ``True.intro)
  let s := modToFilePath lib `Exp.PlainStale "olean"
  saveModuleData s `Exp.PlainStale (md #[initImp] #[ok4])
  IO.FS.writeBinFile (s.addExtension "server") (← IO.FS.readBinFile (q.addExtension "server"))
  IO.println "written"
```

`Exp/UseMore.lean`:

```lean
module

public import Exp.ImportsMore

public theorem Exp.fromMore : False := Exp.badFalse

#print axioms Exp.fromMore
```

`Exp/Mid.lean`:

```lean
module

import Exp.IrCarrier
```

`Exp/UseIr.lean`:

```lean
module

meta import Exp.Mid

theorem Exp.fromIr : False := Exp.irFalse

#print axioms Exp.fromIr
```

`Tgt/AfterUnsafe.lean`:

```lean
import Hostile.UsesUnsafe

/-- proved from `Hostile.fromUnsafe`, whose own proof uses an unsafe definition -/
theorem Hostile.afterUnsafe : True := Hostile.fromUnsafe
```

The file of finding 9, compiled with `lean` alone; without its first two lines (`module` and an
empty line) it is the file that the kernel refuses:

```lean
module

theorem usesUnsafeRec : ∃ f : (Nat → Bool) → Array Nat → Array Nat, True :=
  ⟨@Array.popWhile._unsafe_rec Nat, trivial⟩

#print axioms usesUnsafeRec
```

`Probe/Rec.lean`, the module of section 3 (b) and finding 9, built with Lake:

```lean
module

/-- well-founded recursion, body not exposed -/
public def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m+1, 0 => ack m 1
  | m+1, n+1 => ack m (ack (m+1) n)
termination_by m n => (m, n)

/-- the same, exposed -/
@[expose] public def ack2 : Nat → Nat → Nat
  | 0, n => n + 1
  | m+1, 0 => ack2 m 1
  | m+1, n+1 => ack2 m (ack2 (m+1) n)
termination_by m n => (m, n)

public partial def spinUp (n : Nat) : Nat := spinUp (n + 1)

def privAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m+1, 0 => privAck m 1
  | m+1, n+1 => privAck m (privAck (m+1) n)
termination_by m n => (m, n)
```

## Appendix B: the test module sources

| File under `verify/hostile/Hostile/` | SHA-256 |
|---|---|
| `AfterFakeQuotient.lean` | `4ebe781085234db6ffc1b24552b6dde553ba365219e1f46008436e8e05f0b6bd` |
| `Axiom.lean` | `8baf777e18b77b1f01e2deaa8126f2e77e970b4536d75ac6cddf9963bc73f0da` |
| `ConstructorIsUnsafe.lean` | `59a2e4cdf35ce8cf32ecd8b904641ea5a29ceae002fb64b2c42dcadc7fcc15b2` |
| `Dup/Bogus.lean` | `e2a3cb94afc77ccbb22b09e79160653529f3266e86c0b5c52f8b6f75da4b2973` |
| `Dup/Good.lean` | `9047adf4369eeb5631a8857783829ad9514d7d62cc695939ce2c661a3b7f66c2` |
| `DupBogusFirst.lean` | `123e6a2f6f9dfe9869bd6b6c4ad192907c76c5c8bea777f2fc896de0446b2901` |
| `DupBogusLast.lean` | `cea8c1cebf776a931c65873d5af3c99362b0636f2d5624ad1d37d104b8742dfb` |
| `FakeInductive.lean` | `5dcb4dd2682b73eb7b166617968e1f746157c65a967d3440e86f45d82a99ec4f` |
| `FakeQuotient.lean` | `55cd535c4d9785709861fd9e00a328470259b91c830ac80db17ab2a07ba115c3` |
| `FalseTheorem.lean` | `0a192f5fa4d3caddc5f1f983f6ca973f42954c4616b69988ddbc24bf52ce2b17` |
| `Honest.lean` | `180c9a7e1ea6ca69375391e9e992ca16cf5d45d0ced7a7adccbfdda6329afebb` |
| `MissingConstructor.lean` | `0cff7fbf63e00afa6dbd4cd631d1867b63433215ca4e7a23a8d272247d4b33ae` |
| `MissingRecursor.lean` | `bdc7aee2693a2167998d75ad51d46e1dd6651c48861c0955b38c6ee45e05b928` |
| `Plant.lean` | `1cb4ba9b42f94f91e76f157bb0c654976e8fc793b4097874a70bddc57c1e4557` |
| `Sorry.lean` | `72379cc17d69670a60183b60e9d53b99051a122919a08ef98e35316859f0b6f2` |
| `TamperedConstructor.lean` | `fbae20df77d0d6ac6fab0cd7b9c47dcfb170b6c413d6e88dacc2eb59b03816e7` |
| `TamperedInductive.lean` | `a8f66f316d9d4adc79dc32273a3f310a86e86ff99ef29304937c28f4e75359be` |
| `TamperedRecursor.lean` | `0099922ea1cce33b9aee05b96a8ed0d04276b5cb16d6b9525ac2b6e62ba4a8ae` |
| `UsesUnsafe.lean` | `a5edd618b9be4c672121adab079c1abca3b04de7f14f04349faabb9fb17a0c40` |
| `WrongValue.lean` | `ce3b199b8a4621f83ad42dba01e5a8dab87584c885c57af0987a61d8beeaeca8` |

## Appendix C: the program that counted the exported parts

Built as an executable of a Lake package with `supportInterpreter = true`, and run under
`lake env` with the roots `Init`, `Std`, `Lean`, `Lean+Std` and `Lean+Std+Lake` (and
`Probe.Rec`, which printed the lines about that module). Its `exportedForm` is the program's,
copied unchanged.

```lean
import Lean
open Lean

deriving instance BEq for InductiveVal, QuotKind, QuotVal, ConstantInfo

/-
For each root, walks the import closure as an import outside the module system does (the private
part's imports), reads each module's parts once, and, for every module whose first part has
`isModule`, compares the `.olean` and `.olean.server` parts with the private part by the rule of
ReplayMain.lean (`exportedForm`), counting as that program counts, and classifies each partial
definition of the private part by what the `.olean` part holds under its name.
-/

def isUnsafeRec (n : Name) : Bool := match n with
  | .str _ s => s == "_unsafe_rec"
  | _ => false

def exportedForm (core : Bool) (p e : ConstantInfo) : Bool :=
  e == p || match e with
    | .axiomInfo a =>
      a.name == p.name && a.levelParams == p.levelParams && a.type == p.type && (match p with
        | .thmInfo _ => !a.isUnsafe
        | .defnInfo d => (match d.safety with
          | .safe => !a.isUnsafe
          | .unsafe => a.isUnsafe
          | .partial => a.isUnsafe || core)
        | .opaqueInfo o => a.isUnsafe == o.isUnsafe
        | _ => false)
    | _ => false

unsafe def main (args : List String) : IO Unit := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let coreLib := (sysroot / "lib" / "lean").toString
  for root in args do
    let mut seen : Std.HashSet Name := {}
    let mut stack : Array Name := root.splitOn "+" |>.map String.toName |>.toArray
    let mut modules := 0
    let mut modModules := 0
    let mut coreModModules := 0
    let mut nExported := 0          -- as the program counts: entries of both parts
    let mut nPartialUnmarked := 0   -- as the program counts: entries of both parts
    let mut failCore := 0           -- mismatches with the allowance where the program allows it
    let mut failNoAllowance := 0    -- mismatches if the allowance were removed
    let mut partialDefs := 0
    let mut partialUnsafeRec := 0
    let mut expAbsent := 0
    let mut expSame := 0
    let mut expAxMarked := 0
    let mut expAxUnmarked := 0
    let mut expAxUnmarkedUnsafeRec := 0
    let mut expAxUnmarkedCore := 0
    let mut expOther := 0
    let mut oleanBytes := 0
    let mut serverBytes := 0
    let mut privateBytes := 0
    let mut examples : Array String := #[]
    let mut oleanEntries := 0
    let mut serverEntries := 0
    let mut partsDiffer := 0
    while !stack.isEmpty do
      let m := stack.back!
      stack := stack.pop
      if seen.contains m then continue
      seen := seen.insert m
      modules := modules + 1
      let mFile ← findOLean m
      let main ← unsafe CompactedRegion.read (α := ModuleData) mFile #[]
      let core := mFile.toString.startsWith coreLib
      if main.1.isModule then
        let sFile := OLeanLevel.server.adjustFileName mFile
        let pFile := OLeanLevel.private.adjustFileName mFile
        -- the other parts, read as Lean's import reads them (`readModuleDataPartsOfMod`)
        let server ← unsafe CompactedRegion.read (α := ModuleData) sFile #[main.2]
        let priv ← unsafe CompactedRegion.read (α := ModuleData) pFile #[main.2, server.2]
        modModules := modModules + 1
        if core then coreModModules := coreModModules + 1
        oleanBytes := oleanBytes + (← mFile.metadata).byteSize.toNat
        serverBytes := serverBytes + (← sFile.metadata).byteSize.toNat
        privateBytes := privateBytes + (← pFile.metadata).byteSize.toNat
        let priv := priv.1
        let exp := main.1
        let mut own : Std.HashMap Name ConstantInfo := {}
        for n in priv.constNames, ci in priv.constants do own := own.insert n ci
        for pd in [main.1, server.1] do
          for n in pd.constNames, e in pd.constants do
            nExported := nExported + 1
            match own[n]? with
            | some p =>
              if exportedForm core p e then
                if p.isPartial && !e.isUnsafe && !(e == p) then nPartialUnmarked := nPartialUnmarked + 1
              else
                failCore := failCore + 1
                if examples.size < 10 then examples := examples.push s!"{m} {n}"
              unless exportedForm false p e do failNoAllowance := failNoAllowance + 1
            | none =>
              failCore := failCore + 1
              failNoAllowance := failNoAllowance + 1
              if examples.size < 10 then examples := examples.push s!"{m} {n} (absent from the private part)"
        let mut expMap : Std.HashMap Name ConstantInfo := {}
        for n in exp.constNames, ci in exp.constants do expMap := expMap.insert n ci
        oleanEntries := oleanEntries + exp.constants.size
        serverEntries := serverEntries + server.1.constants.size
        let mut same := exp.constants.size == server.1.constants.size
        for n in server.1.constNames, e in server.1.constants do
          match expMap[n]? with
          | some e' => unless e == e' do same := false
          | none => same := false
        unless same do partsDiffer := partsDiffer + 1
        for n in priv.constNames, p in priv.constants do
          if p.isPartial then
            partialDefs := partialDefs + 1
            if isUnsafeRec n then partialUnsafeRec := partialUnsafeRec + 1
            unless core do
              IO.println s!"  {m}: partial {n}; .olean part: {match expMap[n]? with | none => "absent" | some (.axiomInfo a) => s!"axiom, unsafe {a.isUnsafe}" | some e => if e == p then "the definition itself" else "other"}"
            match expMap[n]? with
            | none => expAbsent := expAbsent + 1
            | some (.axiomInfo a) =>
              if a.isUnsafe then expAxMarked := expAxMarked + 1
              else
                expAxUnmarked := expAxUnmarked + 1
                if isUnsafeRec n then expAxUnmarkedUnsafeRec := expAxUnmarkedUnsafeRec + 1
                if core then expAxUnmarkedCore := expAxUnmarkedCore + 1
            | some e => if e == p then expSame := expSame + 1 else expOther := expOther + 1
        for imp in priv.imports do stack := stack.push imp.module
      else
        for imp in main.1.imports do stack := stack.push imp.module
    IO.println s!"ROOT {root}: modules {modules}, module-system {modModules} (in the toolchain's library {coreModModules})"
    IO.println s!"  as the program counts (both parts): exported entries {nExported}, unmarked partial axioms {nPartialUnmarked}, mismatches {failCore}, mismatches without the allowance {failNoAllowance}"
    IO.println s!"  partial definitions in private parts {partialDefs}, of them named _unsafe_rec {partialUnsafeRec}"
    IO.println s!"  in the .olean part: absent {expAbsent}, the definition itself {expSame}, axiom marked unsafe {expAxMarked}, axiom not marked {expAxUnmarked} (named _unsafe_rec {expAxUnmarkedUnsafeRec}; in the toolchain's library {expAxUnmarkedCore}), other {expOther}"
    IO.println s!"  entries: .olean parts {oleanEntries}, .olean.server parts {serverEntries}; modules whose two parts differ {partsDiffer}"
    IO.println s!"  bytes of module-system files: .olean {oleanBytes}, .olean.server {serverBytes}, .olean.private {privateBytes}"
    for e in examples do IO.println s!"  mismatch: {e}"
```
