# Review C of the kernel replay program

**Reviewed file.** `verify/replay/ReplayMain.lean`, 451 lines, SHA-256
`65396ce3f33656fdb6259e63e55b023c0b779b20c45b85bdba4ffac195cf8011` (computed with `sha256sum`; it is
also the hash that the addendum of review B gives for the working copy whose diff it read). Line
numbers are of this file. Lean is cited at tag `v4.33.1`, by path under `src/` and line. What was
read and what was run is listed under "Method and limits" at the end; in short, the source was
read in full, and the program, two altered copies of it and the hostile modules were also built
and run, on Windows, with the official release of Lean 4.33.1. While this report was being
finished, the file was changed again (its hash no longer matched the one above, and its header
had been rewritten in answer to some of the findings below); those changes are not reviewed here.

## Verdict

Yes, in one narrow way that does not reach any judgment of the kernel's. A compiled file of a
module that uses Lean's module system has three parts, and the program reads only the part that
an import outside the module system loads (`.olean.private`), never the `.olean` part that a
`module` file loads when it imports the module. A hand-written module whose `.olean` part holds
`theorem Exp.exportedFalse : False := True.intro`, a declaration the kernel rejects, and whose
private part holds an honest theorem, is replayed with `failed 0` and exit code 0, and a `module`
file that imports it compiles a proof of `False` from it, for which `#print axioms` reports no
axioms (measured, finding 1). Any use of such a constant inside the replayed closure is rejected,
and the environment in which the five theorems are checked, by the program and by `check.sh`, is
built from the private parts, so the five theorems are not affected; what the case refutes is the
claim, in the program's header and in the paper, that the comparison covers "the compiled files".
Apart from it I found no input on which the program reports success wrongly. For the parts it
reads, the two-way comparison (lines 375-388) makes every constant that is neither unsafe nor
partial, in the version Lean's import keeps, equal, up to binder names and binder annotations, to
a constant that a kernel call produced, and leaves nothing else in the kernel's environment; every
other version of a repeated name is either checked by the kernel or is an axiom with the kept
version's statement; no recorded failure can be lost; and exit code 0 requires an empty list of
failures. All of this rests, as `leanchecker` does, on the kernel and on Lean's reader of compiled
files, which trusts the hashes and flags stored inside names and terms (finding 2). Every finding
of reviews A and B that could produce a false success is closed by the reviewed file. None of the
seventeen hostile modules needs two of its checks: altered copies of the program without either
check give the expected verdict, with the same failures, on all seventeen, while two new modules
given in item 3 need them (measured, finding 3). The verdicts of the
recorded Linux run are those the source predicts, and my run reproduced all seventeen.

## 1. The findings of reviews A and B

| Finding | Severity there | In the reviewed file | Lines |
|---|---|---|---|
| A1. Quotient constants counted and never compared | unsound | Closed. Every name of `order`, quotient constants included, is compared with the kernel's constant through the `BEq` derived at line 57; a quotient constant under a name the kernel never makes fails with "the kernel produced no constant of this name". Measured on `Hostile.FakeQuotient`. | 57, 269-274, 375-383 |
| A2(a). A member that is not in the block it names is never examined | unsound | Closed. Measured on `Hostile.FakeInductive`. | 236-238 |
| A2(b). Listed constructor names resolved to constants of any kind | unsound | Closed: a listed name must be a safe constructor of that very type (247-251); any other kind (252-254) or a missing name (255-257) fails and the block is not sent. Measured on `Hostile.ConstructorIsUnsafe`. | 242-265 |
| A2(c). The kernel's records of inductive types never compared | unsound | Closed: `BEq InductiveVal` is derived (57) and used (382). Measured on `Hostile.TamperedInductive` (item 3). | 57, 382 |
| A2(d). Constants the kernel generates but the files lack are not reported | unsound | Closed. Measured on `Hostile.MissingRecursor` (item 3). | 384-388 |
| A2(e). The key of a constant is not compared with its stored name | unsound | Closed. Measured on `Hostile.KeyMismatch`. | 311-312 |
| A3(i). A listed constructor that no module declares is dropped | gap | Closed. Measured on `Hostile.MissingConstructor`. | 255-257, 263-265 |
| A3(ii). Early return whenever the name is bound | gap | Closed: the return now consults the set of blocks already attempted (160, 235, 262). An inductive type named like a generated constant reaches the kernel, which refuses the name (`kernel/inductive.cpp:259-260`); the comparison catches anything left. | 160, 235, 262 |
| A4. The parallel scheme | note: sound | Still sound, same structure. The other versions of a repeated name are spawned against the snapshot taken before the kept version is added (217). Two runs with `REPLAY_WINDOW=1` and two threads gave the same summary, failures and axioms as the default schedule (measured, "Method"). | 180-196, 210-218, 373 |
| A5. A wrong order gives only false failures | note | Still true. `depsOf` now covers every member of a block and every listed constructor; `depsFor` adds the dependencies of the other versions. | 99-117, 340-372 |
| A6. `usedConstsImpl` and addresses | note: sound | Unchanged and sound. | 61-88 |
| A7. Safety classification and repeated names rest on `finalizeImport` | fragile | Closed. The kept version is the one Lean keeps, a theorem over an axiom and otherwise the later one (318-326), which is the rule of `Lean/Environment.lean:2334-2343` with `subsumesInfo` (2268-2283); safety is decided on the kept version (330-335); versions that differ in kind, statement, universe parameters or safety fail (279-285, 316-317). Residue: `versionsAgree` also admits two definitions or two opaque constants (282), a case the import refuses before the program runs. | 279-339 |
| A8. The self-test | fragile | Partly closed. The in-process self-test is unchanged: it waits on its own tasks, never passes through `drain`, `emit` or the comparison, and `rejects-false` accepts any error. The hostile suite now exercises those paths, but from outside, not as a condition of the main run's exit code, and it misses two checks (finding 3). | 421-427 |
| A9. Exit code and summary | fragile | Closed in substance. A mismatch in the comparison is a failure; the summary separates names declared more than once from further versions (438). `balanced` is now part of the exit condition but can never be false (finding 5). I found no reachable panic: every `!` access is in range by construction, and the scripts set `LEAN_ABORT_ON_PANIC=1` besides. | 430-451 |
| A10. Differences from `Lean.Environment.replay` | note | The program now checks everything Lean's replay checks, and in addition inductive records, quotient constants, missing and non-constructor names, keys, and every proved version of a repeated name. Measured: both modes of `leanchecker` accept `FakeQuotient`, `FakeInductive`, `ConstructorIsUnsafe`, `DupBogusFirst` and the two modules of item 3, all of which the program rejects. The trust shared with it (names the kernel treats specially, a fresh environment without compiled code) is unchanged. | whole file |
| A11. Header and provenance | note | The claim about `getUsedConstants` is gone. `publish/public/verify/replay.sh` records the program's hash, the toolchain, the root, the thread count, the number of compiled files and the hash of `Main.olean`; there is no fingerprint of the other files read. | 1-53; `replay.sh` |
| A12. What "accepted" covers | note | Closed: each named target must be a theorem in the files and in the kernel's environment, with no failure under its name, and its axioms are computed in the kernel's environment. Measured: `[Hostile.assumed]` for `Hostile.fromAxiom`, `[sorryAx]` for `Hostile.bySorry`. A wording problem remains (finding 6). | 390-420 |
| B1. A constructor absent from the closure is dropped (T12) | unsound | Closed, as A3(i). | 255-257 |
| B2. A key different from the stored name hides an inductive type (T9) | unsound | Closed, as A2(e) and A3(ii). | 235, 311-312 |
| B3. Compared only at constructors and recursors | gap | Closed: (a) a rogue quotient constant fails at 380; (b) a missing recursor fails at 384-388; (c) altered fields of an inductive record fail at 382. | 375-388 |
| B4. A repeated name keeps the last version | fragile | Closed for the kept version and for the listing of axiom versions (336-339, 444). Open and harmless: an axiom is put in `replay-axioms.txt` before its check (230), so a rejected axiom is listed; the run then exits 1. | 230, 318-339, 444 |
| B5. `constNames` and `constants` indexed separately | fragile | Closed: unequal lengths fail, and the loop stops at the shorter. | 306-308 |
| B6. The self-test covers one path | note | As A8. | 421-427 |
| B7. Statements in the header and the paper | note | (a) Gone from the header. (b) The paper now describes blocks and the quotient; item 4 lists what remains. (c) Unchanged and documented: `replay-axioms.txt` lists declared axioms, not used ones. | 1-53 |
| B8. Trust shared with the stock tools | note | Unchanged by nature. `publish/public/verify/toolchain.sh` now compares the installed toolchain with the release. | none |

## 2. Findings

### 2.1 The points named in the assignment

**The final comparison.** `k == all[n]!` (382) uses the `BEq ConstantInfo` derived at line 57. It
compares the constructor tags and then the two values with the value type's `BEq`. At this tag
`ConstantVal`, `AxiomVal`, `DefinitionVal`, `TheoremVal`, `OpaqueVal`, `ConstructorVal`,
`RecursorRule` and `RecursorVal` derive `BEq` (`Lean/Declaration.lean:95-99, 101-103, 120-132,
142-148, 156-163, 328-338, 348-355, 357-382`); `InductiveVal`, `QuotKind`, `QuotVal` and
`ConstantInfo` do not (261-302, 411-420, 430-439) and get it from line 57. Every field is
therefore compared:

| Kind | Fields compared |
|---|---|
| axiom | name, universe parameters, type, `isUnsafe` |
| definition | name, universe parameters, type, value, hints, safety, `all` |
| theorem | name, universe parameters, type, value, `all` |
| opaque constant | name, universe parameters, type, value, `isUnsafe`, `all` |
| quotient constant | name, universe parameters, type, kind |
| inductive type | name, universe parameters, type, `numParams`, `numIndices`, `all`, `ctors`, `numNested`, `isRec`, `isUnsafe`, `isReflexive` |
| constructor | name, universe parameters, type, `induct`, `cidx`, `numParams`, `numFields`, `isUnsafe` |
| recursor | name, universe parameters, type, `all`, `numParams`, `numIndices`, `numMotives`, `numMinors`, each rule's constructor, field count and right-hand side, `k`, `isUnsafe` |

Names compare with `lean_name_eq` (`Init/Prelude.lean:4813-4818`, `runtime/object.cpp:2769-2799`).
Terms compare with `BEq Expr`, which is `Expr.eqv` (`Lean/Expr.lean:804-812`), implemented by
`expr_eq_fn<false>` (`kernel/expr_eq_fn.cpp:23-131`): a pointer test, a test of the stored hashes,
then structural recursion that compares literals, universe levels (structurally), constant names
and their levels, metadata, projection names and indices, and the non-dependency flag of `let`,
but not the binder names and binder annotations of λ, ∀ and `let` (lines 98-110). The equality is
structural up to binder names and annotations, which the kernel never consults. For definitions,
theorems, opaque constants and axioms it holds by construction, because the kernel's constant is
built from the very value the program read (`kernel/environment.cpp:152-223`); it does real work
for inductive types, constructors, recursors and quotient constants.

**"The kernel produced nothing else."** Line 386 folds over `kenv.constants`. The fresh
environment's map starts in its second stage (`SMap.empty.switch`, `Lean/Environment.lean:1538`),
so every addition goes to the persistent half, `Kernel.Environment.find?` looks in the empty
first half and then in that one (282-285), the C++ kernel finds constants through the same
function (`kernel/environment.cpp:74-85`), and `SMap.fold` visits both halves
(`Lean/Data/SMap.lean:52-54, 78-80, 107-108`). The fold therefore
sees every constant the kernel can see. With lines 378-383 the two sets of names are equal.
Measured: it is the only check that rejects `Hostile.MissingRecursor` (item 3).

**Names that several modules declare.** The version kept is the one Lean's import keeps (318-326).
Checked: the kept version, of whatever kind, and every other version that is a theorem, a
definition or an opaque constant, against the same snapshot (210-218). Not checked: the other
versions that are axioms; `versionsAgree` has required them to have the kept version's statement
(up to binder names and annotations), universe parameters and safety, and the kept statement is
checked. `versionsAgree` admits a theorem with a theorem or an axiom, two axioms, two definitions
and two opaque constants with equal statement, universe parameters, `isUnsafe` and `isPartial`
(279-285); the last two pairs never reach it, because `finalizeImport` throws for any pair that
`subsumesInfo` accepts in neither direction (`Lean/Environment.lean:2268-2283, 2338-2343`). It
does not compare the `all` lists of two theorems, or test that two axioms state a proposition,
both of which the import enforces. Lean's own library has repeated names among the private parts:
measured, 91 names with 130 further versions in the closure of `Init` and 123 with 185 in that of
`Lean`, all theorems, all checked.

**Unsafe and partial constants.** Classified on the kept version (330-335), never added, and marked
done before the traversal (349), so a declaration that refers to one fails as an unknown constant
(measured, `Hostile.UsesUnsafe`), as the kernel would reject it against the stored environment
too (`kernel/type_checker.cpp:103-122`). The kernel cannot make a constant under a skipped name
without lines 384-388 reporting it, and an unsafe member or constructor of a block fails at 248 or
surfaces there. The unsafe and partial constants themselves are never examined: an ill-typed
unsafe definition in a compiled file passes, as in Lean's replay (`Lean/Replay.lean:176-182`). An
unsafe axiom is listed in `replay-skipped.txt`, not in `replay-axioms.txt`.

**Inductive blocks.** A block is sent once, from the first member reached, with that member's
universe parameters and parameter count (235, 262-265); the other members' records are compared
afterwards (382), so a disagreement in `all`, universe parameters or parameter count surfaces
there. A member that is missing or of another kind (259-261), a constructor that is missing, of
another kind, of another type or unsafe (247-257), and a block that does not contain the member
reached (236-238) are failures, and the block is then not sent. `blockSent` also records a block
that was not sent, which is right, since a failure was recorded for it. A name listed twice, in
one block or in two, reaches the kernel's own name checks (`kernel/inductive.cpp:259-260, 371,
514`).

**The quotient.** Sent once, when the first quotient constant is reached, after `Eq` (115,
269-274). The kernel refuses to overwrite any of the four names (`kernel/quot.cpp:47-56`), the four
constants it makes are compared field by field, and a quotient constant under any other name fails
at 380.

**Checks and additions in `checkedLater`.** The check is spawned on the snapshot before the
addition (190-194), so it never sees its own declaration, and the declaration is added whatever the
check will say. Later checks may run against a declaration whose own check fails; that failure is
recorded and the run exits 1. An unchecked addition overwrites a binding only when the paired
check, or the kernel's own check of a generated name, reports "already declared"
(`kernel/environment.cpp:102-105`; measured on `Hostile.KeyMismatch`).

**Can a failure be recorded and lost?** No. Failures accumulate in `St.failures` (176-178); every
task enters `pending` when it is spawned (192, 218); `drain` takes the list before waiting and
records every rejection (180-186); the last `drain` (373) runs before the comparison; the state is
returned by `.run` (389). Every kernel exception becomes `.error`
(`kernel/kernel_exception.h:161-217`), and an IO exception ends `main` with a non-zero code.
Measured: every rejected hostile module lists the failures the source predicts (item 5).

**The exit code.** It is 0 exactly when there is no failure, both self-test results are right,
`balanced` holds and every named target is a theorem with no failure (449-451). `balanced` cannot
be false (finding 5); the self-test is weak (A8).

**The targets report.** `refsOf` (120-132) follows every edge that `#print axioms` follows
(`Lean/Util/CollectAxioms.lean:56-66`): the type and value of definitions, theorems and opaque
constants, the type of every other kind, the constructors of an inductive type. It also follows
the inductive type of a constructor, the block and rule right-hand sides of a recursor, the type of
a quotient constant, the structure of every projection, and the constants into which the kernel
expands literals (71-74, 86). Every constant the kernel consults while checking a term is in the
term or reached through one of those edges (unfolding, recursor reduction, eta for structures,
literal expansion). I found no way for it to report fewer axioms than the target depends on in the
environment it walks, which after a successful run is the compiled files' own. A wording problem is
finding 6.

### 2.2 New findings

**1. A module-system compiled file is compared only in part.** Severity: gap.
- Lines: 296-298, 304-310; header 11-17.
- What can go wrong. `importModules` at its default, private level reads the three parts of a
  module that uses the module system and puts the private one in `env.header.moduleData`
  (`Lean/Environment.lean:2023-2033`, with `importAll` forced at 2182 and the parts read at
  2078-2091). The `.olean` part is what a `module` file gets when it imports the module without
  `all` (2025-2031; `Lean/Elab/Import.lean:147-157`). The program reads `moduleData` only, so the
  constants of the `.olean` and `.olean.server` parts are compared with nothing. Lean writes those
  parts from the same environment, with theorems, unexposed definitions and opaque constants turned
  into axioms with the same statement and private names left out (`Lean/AddDecl.lean:113-144`;
  `Lean/Environment.lean:1858-1885`), but a hand-written file can hold anything there, and
  `saveModuleDataParts` is public (1772). Both modes of `leanchecker` read the most private part
  too (`LeanChecker.lean:12-38`) and share the gap.
- Scenario (measured). `Exp.ExportedOnly`, written with `saveModuleDataParts` (appendix): its
  `.olean` and `.olean.server` parts hold `theorem Exp.exportedFalse : False := True.intro`, its
  `.olean.private` part holds `theorem Exp.honest : True := True.intro`. The program on root
  `Exp.ExportedOnly`: `failed 0`, exit 0; `leanchecker` and `leanchecker --fresh`: exit 0. The file

  ```lean
  module

  import Exp.ExportedOnly

  theorem Exp.fromExported : False := Exp.exportedFalse

  #print axioms Exp.fromExported
  ```

  compiles and prints `'_private.Exp.UseExported.0.Exp.fromExported' does not depend on any axioms`.
- Bound (measured). The program on root `Exp.UseExported` fails with
  `(kernel) unknown constant 'Exp.exportedFalse'`, and so do both modes of `leanchecker`: a use
  inside the replayed closure is always checked against the private parts. `check.sh` imports
  `Main` from a file without `module`, hence at the private level (`Lean/Elab/Import.lean:147-152`),
  like the program, so the five theorems are judged in the environment the program checked. Lean's
  own library is built with the module system (its files begin with `module`, for instance
  `Lean/Declaration.lean:6`), and its files are covered by `toolchain.sh`'s comparison with the
  release. Whether the archive and Mathlib at the pinned commit use the module system I did not
  check.
- Fix. For every module whose main part has `isModule`, also read its `.olean` and `.olean.server`
  parts (`readModuleDataParts`, `Lean/Environment.lean:1782`) and require each constant there to
  be the private part's constant of that name or that constant exported as an axiom with the same
  name, universe parameters and type (`Lean/AddDecl.lean:113-126`); fail otherwise. Or restrict
  the claim, in the header (11-17) and in the paper, to the part of each file that an import
  outside the module system reads.

**2. Data stored inside names and terms is trusted.** Severity: note.
- Lines: every comparison of names and terms (311, 313, 379, 382, 385-386) and every kernel call.
- What can go wrong. A name stores its hash, and a term its hash, its range of loose bound
  variables and its flags (`Lean/Expr.lean:471-472`). Name equality compares the stored hashes
  before the structure (`runtime/object.cpp:2769-2773`), hash maps bucket by them, term equality
  starts with them (`kernel/expr_eq_fn.cpp:45-46`), and the kernel's tests for free variables and
  metavariables read the flags (`kernel/environment.cpp:87-100`). Nothing recomputes them when a
  compiled file is read. A wrong value in a comparison gives a false mismatch, which is a reported
  failure, so it cannot produce success. But two constants whose names print the same and whose
  stored hashes differ are two constants to Lean's import, to the kernel's name check
  (`kernel/environment.cpp:102-105`) and to this program; both are checked, both pass the
  comparison, and a statement may then refer to a constant other than the one its printed name
  designates. Success is right about what the kernel accepted and wrong about what was meant.
- Scenario [INFERENCE: not built]. A hand-written module stores a second `RiemannHypothesis`
  whose name carries another hash and whose value is `True`, and a theorem `riemannHypothesis`
  whose statement refers to that one. The replay accepts; `check.sh`'s
  `#check (riemannHypothesis : RiemannHypothesis)` elaborates the name afresh and would not. I did
  not try whether altered flags of a term can make the kernel accept an ill-typed term.
- Fix. Recompute the stored hashes and flags on load (one pass over every name and term, compared
  with a fresh computation), or state this trust beside the kernel's in the paper. It applies
  equally to `leanchecker` and to any checker that uses Lean's reader, `lean4lean` included.

**3. The hostile suite exercises two checks only together with others.** Severity: fragile.
- Lines: 382 for inductive types; 384-388.
- What can go wrong. Each of the thirteen modules that must be rejected is rejected by an earlier
  check, or by the comparison of a constructor, of a recursor, or of a constant the kernel never
  made (item 5 lists the failures). None depends on the comparison of an inductive record or on the
  "nothing else" direction, so a change that broke either would leave the suite green. Measured:
  copy N (lines 384-388 deleted) and copy I (line 57 replaced by a `BEq InductiveVal` that always
  answers true, the other three instances still derived) give, on all seventeen modules, the same
  exit code and the same number of failures as the reviewed program.
- Scenario (measured). `Hostile.MissingRecursor` (item 3): an inductive type and its two
  constructors without a recursor, and
  `usesRec : Hostile.Bit.rec (fun _ => Nat) 0 1 Hostile.Bit.one = 1 := Eq.refl 1`. In the stored
  environment the kernel rejects the theorem: re-adding it with `addDecl` in a file that imports
  the module fails with `(kernel) unknown constant 'Hostile.Bit.rec'`. The reviewed program rejects
  the module with one failure, `Hostile.Bit.rec was produced by the kernel and is not a constant of
  the compiled files that is neither unsafe nor partial`; copy N accepts it with exit 0; both modes
  of `leanchecker` accept it. `Hostile.TamperedInductive` (item 3): a recursive type whose stored
  record says `isRec := false`. The program reports one failure, `Hostile.Chain is an inductive
  type in the compiled files and differs from the constant the kernel produced`; copy I accepts;
  both modes of `leanchecker` accept.
- Fix. Add the two modules of item 3, each with the expectation `accepts accepts rejects`.

**4. `hostile.sh` counts a module that did not compile as rejected.** Severity: fragile.
- Lines: `publish/public/verify/hostile.sh:15-18` (exit codes of `lake build` and `lake exe craft`
  printed, not enforced), 20 and 24-33 (a verdict is an exit code).
- What can go wrong. A module that fails to compile has no compiled file, and every checker then
  exits 1 (measured: the program with "object file ... does not exist", both modes of
  `leanchecker` with "Could not find any oleans"). `verdict` turns that into "rejects", which is
  what `expected.txt` asks of thirteen of the seventeen modules; `paper/tools/numbers.py` needs only
  `HOSTILE-OK` and "as expected: yes". The program's failure messages are compared with nothing.
- Scenario. A later toolchain breaks `Hostile.plant`, which reaches the private function
  `Lean.Kernel.Environment.add` by its internal name through `evalConst`
  (`verify/hostile/Hostile/Plant.lean`). The seven modules that plant fail to compile, the run
  prints `HOSTILE-OK`, and the paper's table reports seven rejections that tested nothing.
- Fix. Stop unless `lake build` and `lake exe craft` exit 0 and every module of `expected.txt` has
  its `.olean`. Record in `expected.txt`, for each module to be rejected, the names that must
  appear in `replay-failures.txt` (item 5 lists them), and compare.

**5. `balanced` cannot be false.** Severity: note.
- Lines: 206, 219-274, 349-369, 430-431, 449.
- Why. The traversal pushes only names with status 0 that are keys of `all` (360-364); every key is
  in `order` or in `skipped`, and the skipped ones are marked done before it starts (349); each name
  is pushed at most once and emitted once, when it is popped (366-369); every call of `emit` on a
  key adds one to `emitted` and one to exactly one kind counter. So the sum of the kinds, `emitted`
  and `order.size` are always equal. It is harmless as a print of the program's own consistency, but
  it should not be described as a check.

**6. The targets report can call a theorem checked when a dependency failed.** Severity: note.
- Lines: 397-417.
- Measured. On `Hostile.FalseTheorem` with the targets `Hostile.conclusion Hostile.falseProved`,
  `replay-targets.txt` says `Hostile.conclusion: a theorem, checked by the kernel; it depends on 5
  constants; axioms: []` and `Hostile.falseProved: FAILED`. The run reports `failed 1` and exits 1,
  so nothing is reported as a success, but the first line read alone is wrong: `conclusion` was
  checked only against an unchecked `falseProved`.
- Fix. Mark a target FAILED when any name in its set `seen` is in `failed`.

**7. `#print axioms` on an imported theorem reads a list stored in its compiled file.** Severity:
note; it concerns `check.sh` and the paper rather than the program.
- At this tag `collectAxioms`, for a constant of an imported module, returns the list that module
  stored when its compiled file was written, and walks terms only for constants of the current file
  (`Lean/Util/CollectAxioms.lean:41-46, 116-117`; `#print axioms` calls it,
  `Lean/Elab/Print.lean:240-245`). So the axioms `check.sh` prints for the five theorems are what the
  archive's compiled files recorded, and a hand-written file can record anything. The program's
  targets report is the only computation of these lists from the terms. Where both lists were
  produced here, in the modules that declare the theorems (where `#print axioms` does walk the
  terms), they agreed: `[Hostile.assumed]`, `[sorryAx]`.
- Fix. Say in the paper which of the two lists is computed (item 4).

**8. Comments that say more than the code.** Severity: note.
- Header 4-8: "takes every constant ... and passes each declaration to the Lean kernel"; the unsafe
  and partial constants are not passed.
- Header 30-33: "checks every version of a name that more than one module declares"; the versions
  that are axioms are not checked (207-215). Lines 36-37 say it correctly.
- Header 44-46: "The modules of `../hostile` test the whole program, each with a compiled file that
  must be rejected"; four of them must be accepted, and two checks are not tested on their own
  (finding 3).
- Docstring 276-278: `versionsAgree` also admits two definitions or two opaque constants (282).

## 3. The hostile modules

All sixteen modules with a source compiled at v4.33.1 (measured), and `Craft.lean` wrote
`Hostile.KeyMismatch`. Each contains what its header says, with the two qualifications in the second
column. The failures in the fourth column are those the source predicts and that my run recorded.

| Module | Header | Expected | Why the program decides as it does |
|---|---|---|---|
| Honest | holds | accepts | control |
| Plant | holds: `mkPrivateNameCore` (`Lean/PrivateName.lean:29-30`) gives the name of the private `Kernel.Environment.add` (`Lean/Environment.lean:310-312`) | accepts | control |
| Axiom | holds; `#print axioms` names `Hostile.assumed` | accepts | `replay-axioms.txt` lists `Hostile.assumed` |
| Sorry | holds | accepts | the targets report gives `[sorryAx]` |
| FalseTheorem | holds; `#print axioms Hostile.conclusion` reports no axioms | rejects | `Hostile.falseProved` fails its check (180-186) |
| WrongValue | holds | rejects | `Hostile.three` fails its check |
| UsesUnsafe | holds | rejects | `Hostile.fromUnsafe` refers to the skipped `Hostile.unsafeNumber` (335, 349) |
| TamperedRecursor | holds in the sense that the order of the two rules is exchanged; each rule keeps its constructor and right-hand side, and the kernel picks a rule by constructor name (`kernel/inductive.cpp:114-118`, used at `kernel/inductive.h:100`), so the stored recursor computes exactly as the original | rejects | the recursor differs (382) |
| TamperedConstructor | holds | rejects | the constructor differs (382) |
| DupBogusLast | holds; Lean keeps the later, bogus version | rejects | the kept version fails its check |
| DupBogusFirst | holds; Lean keeps the proved version | rejects | the other version fails its check (217) |
| MissingConstructor | holds | rejects | 255-257, then an unknown constant, then 380 twice |
| KeyMismatch | holds; it has no source | rejects | 311-312, then "already declared", 380 and 383 |
| FakeQuotient | holds | rejects | 380 |
| AfterFakeQuotient | holds; `#print axioms` reports no axioms | rejects | an unknown constant, then 380 |
| FakeInductive | holds, except "which a replay does not send to the kernel": Lean's replay does send `Hostile.Hidden`, as a safe type, when it reaches `Hostile.fakeInductive` (`Lean/Replay.lean:102-120`) | rejects | 236-238, then 380 |
| ConstructorIsUnsafe | holds | rejects | 252-254, then an unknown constant, then 380 |

**Attacks the suite does not cover.** Three, each measured.

(a) A missing recursor. The stored environment lacks a constant that a theorem uses, and only lines
384-388 see it (finding 3). Expected `accepts accepts rejects`.

```lean
/-
A module whose compiled file holds an inductive type and its constructors but no recursor, and a
theorem proved with the recursor. In the compiled files `Hostile.Bit.rec` does not exist, so the
kernel rejects the theorem there; a replay that rebuilds `Hostile.Bit` has the kernel generate the
recursor, and then the theorem is in order. All four constants are written into the table
directly. A replay must reject this module.
-/
import Hostile.Plant
open Lean Elab Command

run_cmd do
  let bit := mkConst `Hostile.Bit
  let nat := mkConst ``Nat
  Hostile.plant (.inductInfo
    { name := `Hostile.Bit, levelParams := [], type := mkSort Level.one, numParams := 0,
      numIndices := 0, all := [`Hostile.Bit], ctors := [`Hostile.Bit.zero, `Hostile.Bit.one],
      numNested := 0, isRec := false, isUnsafe := false, isReflexive := false })
  Hostile.plant (.ctorInfo
    { name := `Hostile.Bit.zero, levelParams := [], type := bit, induct := `Hostile.Bit,
      cidx := 0, numParams := 0, numFields := 0, isUnsafe := false })
  Hostile.plant (.ctorInfo
    { name := `Hostile.Bit.one, levelParams := [], type := bit, induct := `Hostile.Bit,
      cidx := 1, numParams := 0, numFields := 0, isUnsafe := false })
  -- `Hostile.Bit.rec (motive := fun _ => Nat) 0 1 Hostile.Bit.one = 1`, by `Eq.refl 1`
  let lhs := mkApp4 (mkConst `Hostile.Bit.rec [Level.one]) (.lam `b bit nat .default)
    (mkRawNatLit 0) (mkRawNatLit 1) (mkConst `Hostile.Bit.one)
  Hostile.plant (.thmInfo
    { name := `Hostile.usesRec, levelParams := [],
      type := mkApp3 (mkConst ``Eq [Level.one]) nat lhs (mkRawNatLit 1),
      value := mkApp2 (mkConst ``Eq.refl [Level.one]) nat (mkRawNatLit 1),
      all := [`Hostile.usesRec] })
```

(b) An altered inductive record. Only line 382, applied to an inductive type, sees it (finding 3).
Expected `accepts accepts rejects`.

```lean
/-
A module whose compiled file holds an inductive type whose record is not the one the kernel
makes. `Hostile.Chain` is declared in the ordinary way and is recursive; its record is then
replaced, in the table of constants, by a copy that says it is not. A replay must reject this
module.
-/
import Hostile.Plant
open Lean Elab Command

inductive Hostile.Chain where
  | stop : Hostile.Chain
  | link : Hostile.Chain → Hostile.Chain

run_cmd do
  let some (.inductInfo v) := (← getEnv).find? ``Hostile.Chain | throwError "no inductive type"
  Hostile.plant (.inductInfo { v with isRec := false })
```

(c) An exported part that differs from the private one (finding 1). It needs a file with three
parts, so it belongs in `Craft.lean`, which would write `Hostile.ExportedOnly` as the appendix
writes `Exp.ExportedOnly`; the `module` file that uses it must be compiled after `lake exe craft`.
Today all three checkers accept `Hostile.ExportedOnly` (expected `accepts accepts accepts`, which
documents the gap) and reject the module that uses it.

A fourth case would make `TamperedRecursor` an exploit rather than a difference: exchange the
right-hand sides of the two rules, not their order, and add a theorem that holds only under the
exchanged rules, as review B's T6 does. The program rejects both the recursor (382) and the
theorem, which is then checked against the kernel's rules.

## 4. The paper

Read in `paper/sections/verification.tex` (SHA-256
`1b91cf186a34b972b1a5817581fe010646f40e340c79c32c2cac52294b5fd13e` when read) and, for
`\replaystatus`, `paper/version.tex` (SHA-256
`2999973ce138d033f383fe49e2dc58013042535cdba34fd6ffe4c3d10121dd86` when read). Line numbers are of
those versions; both files changed afterwards, and the changes are not reviewed here. Each item
is a sentence that says more than the program does, or says it inexactly.

*Kernel replay.*
- 95: "A build checks each declaration once, in the process that elaborated it." Not for code that
  adds declarations without the kernel, as several hostile modules do; "normally" is needed.
- 99: "... modules with \replayconstants{} declarations." The number is that of distinct names
  (`all.size`, 299-329). The further versions of repeated names are declarations too and are not
  in it (40,595 in the earlier run).
- 99-100: "Of these, \replaydecls{} are neither unsafe nor partial, and they are what a replay
  examines." It also examines the further versions that are theorems, definitions or opaque
  constants (210-218).
- 108-111: "compared with the compiled files in both directions: each of the \replaydecls{}
  constants must equal, field by field, the constant of the same name". Two qualifications: terms
  are equal up to binder names and binder annotations (`Lean/Expr.lean:804-812`); and for a module
  that uses the module system "the compiled files" are one part of three (finding 1).
- 111-112: "The replay is therefore a statement about the compiled files: they hold exactly what
  the kernel produces from the declarations in them." This says more than the program does: the
  unsafe and partial declarations (5,840 in the earlier run) are not examined; the further versions
  that are axioms are not produced by any kernel call, only required to share the kept version's
  statement; an exported part can hold a declaration the kernel rejects (finding 1, measured); and
  the result rests on the data stored in the objects (finding 2). A version that holds: "apart from
  the unsafe and partial declarations and the further versions of repeated names, they hold, as an
  import outside the module system reads them, exactly what the kernel produces".
- `version.tex` 14-15: "The \replayaxioms{} axioms are all declared in Lean's core library; the
  archive declares none". `replay-axioms.txt` lists safe axioms only (230, 336-339, 444); an unsafe
  axiom would appear in `replay-skipped.txt`. The claim needs that file as well, or the source scan.
- `version.tex` 16-17: "which Lean's import accepts when the statements agree". The import accepts
  only two theorems with equal statement, universe parameters and `all`, a theorem and a safe axiom,
  or two axioms of equal safety that state propositions (`Lean/Environment.lean:2268-2283`); two
  definitions with the same statement are refused.
- `version.tex` 17: "every version was checked". True only if the run's count of further versions
  that are axioms is 0 (`... and axioms N`, line 438); those are not passed to the kernel (207-215).
  `numbers.py` checks that checked plus axioms equals the further versions, not that the axioms are
  0.
- 118-120: "\lean{riemannHypothesis} depends there on \replayconeconstants{} constants; the cone
  ... has \conesize{}." The first number counts every name `refsOf` reaches (409), along more edges
  than a cone through types and values (constructors' inductive types, recursors' blocks and rules,
  literal expansions); the two numbers measure different relations, which the sentence should say
  if they differ.

*The checker.*
- 124-125: "runs the kernel checks in parallel, each against a snapshot". The inductive blocks and
  the quotient are checked on the main thread, against the environment as it is (198-201, 265,
  274).
- 129-132: "our replay used \replaycpuhours{} hours of processor time, and that is roughly what it
  would need." An estimate, not a measurement; `leanchecker --fresh` checks one version per name
  and has no tasks. On the closure of `Hostile.Plant` (203,124 constants) my run gave 76 s for
  `leanchecker --fresh` and 64 s for the program with `LEAN_NUM_THREADS=1` (one worker thread
  besides the main one), so "roughly" holds at that size. `stock.sh` measures both on the closure
  of Mathlib, which would give a ratio to quote instead of an assumption.
- 134-136: "Three reviews ... each without sight of the others' conclusions". Not so for this one:
  this review was asked to read reviews A and B first, and did. Reviews A and B were made without
  sight of each other's conclusions, review B saying so; the addendum of review B saw the diff of
  the corrected program.
- 143-145: "The program was corrected as the reviews proposed, the third review was made of the
  corrected program, and the replay reported here was made with it." This review was made of the
  file whose SHA-256 is given at the top. That the reported replay used it can be shown only by
  `replay-provenance.txt`; the paper should print the hash, and its first sixteen digits should be
  `65396ce3f33656fd`. "As the reviews proposed" is not exact either: review B's "record an axiom
  only after its check" and review A's in-process fixture were not adopted (table, B4 and A8).
- 145-146: "The first run ... had given the same counts for every kind of declaration."
  `numbers.py` compares modules, constants, replayed, theorems, definitions, opaque constants,
  axioms, constructors, recursors, skipped and failures, not inductive types or blocks, and the
  earlier summary has no line for quotient constants.
- 148-149: "We wrote \hostilemodules{} small modules. Every one compiles." `Hostile.KeyMismatch` has
  no source; `Craft.lean` writes its compiled file. And `hostile.sh` does not check that the others
  compile (finding 4); in my run all sixteen did.
- 149-151: "\hostilebad{} of them have a compiled file that holds something the kernel never
  accepted". The compiled files of `DupBogusLast`, `DupBogusFirst` and `AfterFakeQuotient` hold
  nothing of the kind; the wrong constant is in a file they import (`Hostile.Dup.Bogus`,
  `Hostile.FakeQuotient`). "In their import closure" is exact.
- 153-155: "A successful build and a clean list of axioms ... show it for code that does not write
  into the environment behind the kernel's back, and a replay is what covers the rest." At this tag
  the list of axioms of an imported theorem is read from its compiled file (finding 7), so a clean
  list is also only as good as that file; and a replay covers the parts of files it reads and the
  declarations that are neither unsafe nor partial (findings 1 and 2), not "the rest" without
  qualification.
- 168: "drawn at random". By a fixed shuffle (`shuf --random-source=<(yes)`,
  `publish/public/verify/sample.sh:16`), which makes the draw repeatable; "by a fixed pseudo-random
  shuffle" is exact.
- 171-181, `lean4lean`. This is not about the program, and I did not examine `lean4lean`. Two points
  can be checked against Lean's source. "It uses Lean's representation of terms and Lean's reader
  of compiled files": then it shares the trust of finding 2. "None of it is the code of the first":
  Lean's own operations of substitution, abstraction and equality on terms are `@[extern]`
  functions implemented in the first kernel's directory (`Lean/Expr.lean:808, 1428-1497`;
  `kernel/instantiate.cpp:44-150`, `kernel/abstract.cpp:68-75`, `kernel/expr_eq_fn.cpp:130-132`). If
  `lean4lean` calls them, the sentence says more than is true; whether it does I did not check.
  Whether its `--fresh` driver compares inductive records and quotient constants decides how far
  "every definition on which the meaning of the statement depends has passed a second kernel"
  reaches beyond definitions; the table's column for it will show this on the hostile modules.

## 5. The recorded Linux verdicts

They are what the source predicts, and my run on Windows gave the same exit codes and, for each
rejected module, exactly these failures (their order of printing follows the traversal):

- Honest, Axiom, Sorry, Plant: exit 0, `failed 0` (closures of `Init` and of `Lean`; for `Plant`
  203,124 constants replayed).
- FalseTheorem: `Hostile.falseProved` (kernel) declaration type mismatch, has type `True` but is
  expected to have type `False`.
- WrongValue: `Hostile.three` (kernel) declaration type mismatch, has type `String` but is expected
  to have type `Nat`.
- UsesUnsafe: `Hostile.fromUnsafe` (kernel) unknown constant `Hostile.unsafeNumber`.
- TamperedRecursor: `Hostile.Two.rec` is a recursor in the compiled files and differs from the
  constant the kernel produced.
- TamperedConstructor: `Hostile.Box.mk` is a constructor in the compiled files and differs from
  the constant the kernel produced.
- DupBogusLast: `Hostile.Dup.twice` (kernel) declaration type mismatch, has type `Nat` but is
  expected to have type `True` (the kept version).
- DupBogusFirst: the same failure, from the version set aside.
- MissingConstructor: `Hostile.Coin` (`Hostile.Coin.tails` ... is not in the compiled files);
  `Hostile.onlyHeads` (kernel) unknown constant `Hostile.Coin`; `Hostile.Coin.heads` and
  `Hostile.Coin`: the kernel produced no constant of this name.
- KeyMismatch: `Hostile.phantomBody` (the compiled file stores under this name a constant named
  `Hostile.Phantom`); `Hostile.Phantom` (kernel) constant has already been declared;
  `Hostile.phantomBody`: the kernel produced no constant of this name; `Hostile.Phantom` is an
  inductive type in the compiled files and differs from the constant the kernel produced (a
  definition).
- FakeQuotient: `Hostile.fakeQuot`: the kernel produced no constant of this name.
- AfterFakeQuotient: `Hostile.falseFromQuot` (kernel) unknown constant `Hostile.fakeQuot`;
  `Hostile.fakeQuot`: the kernel produced no constant of this name.
- FakeInductive: `Hostile.fakeInductive` is not a member of the mutual block it names; then the
  kernel produced no constant of this name.
- ConstructorIsUnsafe: `Hostile.Claim` (`Hostile.Claim.witness`, listed as a constructor of
  `Hostile.Claim`, is a definition); `Hostile.claimed` (kernel) unknown constant `Hostile.Claim`;
  `Hostile.Claim`: the kernel produced no constant of this name.

## Method and limits

**Read.** The reviewed file; reviews A and B (`notes/review-replay-program-A.md`, `notes/review-replay-program-B.md`); `verify/hostile/` (every module, `Craft.lean`,
`expected.txt`, `lakefile.toml`); `publish/public/verify/hostile.sh`, `replay.sh`, `stock.sh`,
`sample.sh`; `paper/sections/verification.tex` and `paper/version.tex`; the parts of
`paper/tools/numbers.py` that decide what the paper prints. Lean at tag `v4.33.1`, from
`https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/`: `Lean/Replay.lean`,
`LeanChecker.lean`, `Lean/Environment.lean`, `Lean/Declaration.lean`, `Lean/Expr.lean`,
`Lean/AddDecl.lean`, `Lean/Setup.lean`, `Lean/PrivateName.lean`, `Lean/Elab/Import.lean`,
`Lean/Elab/Print.lean`, `Lean/Util/CollectAxioms.lean`, `Lean/Data/SMap.lean`, `Init/Prelude.lean`,
`kernel/environment.cpp`, `kernel/inductive.cpp`, `kernel/inductive.h`, `kernel/quot.cpp`,
`kernel/type_checker.cpp`, `kernel/expr_eq_fn.cpp`, `kernel/instantiate.cpp`,
`kernel/abstract.cpp`, `kernel/kernel_exception.h`, `runtime/object.cpp`.

**Ran.** On a Windows x64 computer, with the release archive `lean-4.33.1-windows.zip` from the Lean
project's GitHub releases (`lean --version`: commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), in a
temporary directory outside the repository, deleted afterwards:
- built a byte-identical copy of the reviewed file (its SHA-256 checked) and two altered copies:
  N, without lines 384-388, and I, with line 57 replaced by
  `instance : BEq InductiveVal := ⟨fun _ _ => true⟩` followed by
  `deriving instance BEq for QuotKind, QuotVal, ConstantInfo`;
- built an unchanged copy of `verify/hostile` with `lake build` and `lake exe craft`, ran the three
  programs on its seventeen modules with `LEAN_ABORT_ON_PANIC=1` as `hostile.sh` does, then added
  the two modules of item 3 and ran the three programs and both modes of `leanchecker` on them,
  and both modes of `leanchecker` on `FakeQuotient`, `FakeInductive`, `ConstructorIsUnsafe` and
  `DupBogusFirst`;
- wrote `Exp.ExportedOnly` and compiled `Exp.UseExported` (appendix), and ran the program and both
  modes of `leanchecker` on both;
- ran the program with named targets on `Hostile.Axiom`, `Hostile.Sorry` and
  `Hostile.FalseTheorem`, and with `REPLAY_WINDOW=1` and `LEAN_NUM_THREADS=2` on `Hostile.Plant` and
  `Hostile.KeyMismatch` (same summary apart from time and threads, same failures, same axioms as
  the default schedule);
- timed the program with `LEAN_NUM_THREADS=1` (64 s) and `leanchecker --fresh` (76 s) on
  `Hostile.Plant`;
- extracted the Lean code of item 3 and of the appendix from this report: the two modules of item 3
  are byte-identical to the ones compiled, and the appendix was built and run again exactly as
  printed, with the results given in finding 1.

Unless stated otherwise `LEAN_NUM_THREADS` was unset. A replay of the closure of `Init` took about
4 s and one of the closure of `Lean` about 11 s.

**Not done.** I did not repeat the Linux run, did not run anything on the archive, Mathlib or the
published results, did not run `replay.sh`, `stock.sh`, `sample.sh` or `hostile.sh` themselves, and
did not examine `lean4lean`. I did not build the twin-name file of finding 2 or try to make the
kernel accept a term through altered stored flags. Apart from this report, nothing in the
repository was written.

## Appendix: the test files of finding 1

`Craft.lean` of a scratch Lake package (an executable `craft` with root `Craft`), run from that
package's directory; `Exp/UseExported.lean` compiled afterwards with
`lean -o .lake/build/lib/lean/Exp/UseExported.olean Exp/UseExported.lean`, with `LEAN_PATH` set
to the package's `.lake/build/lib/lean`.

```lean
import Lean
open Lean

def lib : System.FilePath := ".lake/build/lib/lean"

def data (imports : Array Name) (cs : Array ConstantInfo) (isModule := false) : ModuleData :=
  { isModule, imports := imports.map fun m => ({ module := m } : Import),
    constNames := cs.map (·.name), constants := cs, extraConstNames := #[], entries := #[] }

/-- A module-system file whose exported part holds a theorem `False` with the proof `True.intro`,
which its private part does not hold. -/
def main : IO Unit := do
  let mod := `Exp.ExportedOnly
  let path := modToFilePath lib mod "olean"
  if let some dir := path.parent then IO.FS.createDirAll dir
  let fake : ConstantInfo := .thmInfo
    { name := `Exp.exportedFalse, levelParams := [], type := mkConst ``False,
      value := mkConst ``True.intro, all := [`Exp.exportedFalse] }
  let honest : ConstantInfo := .thmInfo
    { name := `Exp.honest, levelParams := [], type := mkConst ``True,
      value := mkConst ``True.intro, all := [`Exp.honest] }
  saveModuleDataParts mod #[
    (path, data #[`Init] #[fake] (isModule := true)),
    (path.addExtension "server", data #[`Init] #[fake] (isModule := true)),
    (path.addExtension "private", data #[`Init] #[honest] (isModule := true))]
```

`Exp/UseExported.lean` is the file shown in finding 1.
