# Results

Output of our own runs of the programs in `verify/`. Times are Unix seconds.

There are two groups of files. The first is the build of the whole archive and what was run on
it: one build, on one machine, on 20 and 21 November 2026. The second is the static scan and
the tests of the checkers, which need no build of the archive; they were run on 21 November
2026 on the machine that is making the second build, with the scripts and the programs as
they are published here, on that machine's own build of Mathlib from source and while it was
building the archive (so the times in them were measured under load).

## The build of the archive and what was run on it

| File | Produced by | What it is |
|---|---|---|
| `scan.txt` | `scan.py` on the downloaded `lean.tar.gz`, run on the second machine | size and SHA-256 of the archive, counts of files and lines, the static inspection. The scan published with versions 1.0 and 1.1 matched no word that follows a dot and looked for fewer words; this is the corrected scan, on the same file (the same SHA-256) |
| `build-summary.txt` | assembled by hand after the build ended | the first and last lines of the build log (`START` to `END`); then a count of compiled files under `.lake/build`, a count of failure marks and of warnings in the log, the toolchain file, `lean --version`, the revisions in `lake-manifest.json`, the number of processors and the processor model |
| `check.txt` | `check.sh` | where `RiemannHypothesis` and `riemannZeta` are declared, the statement, and the axioms of the five theorems |
| `axioms.txt` | the first axiom check, made when the build ended | the same axioms, from the first run |
| `corollaries.txt` | `lean/Corollaries.lean` compiled against the built archive | the axioms of the three corollaries |
| `targets.txt` | `lean/Targets.lean` compiled against the built archive | it compiles, with no output |
| `cut-result.txt` | `cut/CutMain.lean` as published with version 1.1 | the size of the cone of `riemannHypothesis` and of the cone of all five theorems, counts by kind and by the top-level directory of the declaring module, the probes by name |
| `cut-hub.txt` | the same | every theorem of the file that collects the published results, with whether it is in the cone |
| `cut-in.txt.xz`, `cut-out.txt.xz` | the same | every declaration of the archive inside and outside the cone of `riemannHypothesis`, one per line: kind (`T` theorem, `D` definition, `I` inductive type, `C` constructor, `R` recursor, `O` opaque) and full name. Declarations of Mathlib and of Lean's library are not listed |
| `cut-modules.txt.xz` | the same | the names of the 147,489 modules of the archive that declare at least one declaration of the cone |
| `cut-five-extra.txt` | the same | the 24 declarations in the cone of all five theorems that are not in the cone of `riemannHypothesis` |
| `replay-summary.txt` | `replay-program-first-form.lean` | the counts of the kernel replay |
| `replay-log.txt` | the wrapper described below | the program's progress log |
| `replay-failures.txt` | `replay-program-first-form.lean` | declarations the kernel rejected: empty |
| `replay-axioms.txt` | `replay-program-first-form.lean` | every axiom not marked unsafe that is declared anywhere in the import closure of `Main` (the unsafe ones are in `replay-skipped.txt`) |
| `replay-skipped.txt` | `replay-program-first-form.lean` | the declarations marked unsafe or partial, which a replay does not check |
| `replay-program-first-form.lean` | | the replay program as it was when those files were written (the file `verify/replay/ReplayMain.lean` of version 1.1). It is not the program now in `verify/replay/`. See below for what it did not check |

## The tests of the checkers

| File | Produced by | What it is |
|---|---|---|
| `hostile.txt` | `hostile.sh` | the first line is the SHA-256 of the replay program used, which is the one in `verify/replay/`; then, for each module of `verify/hostile/`, what Lean's checker did in each of its modes, what our replay did, and the failures the replay recorded; then the test of the report on named theorems |
| `independent-hostile.txt` | `independent.sh hostile` | what `lean4lean` did on the same modules, in each of its modes |
| `stock.txt` | `stock.sh` | the first line is the SHA-256 of the replay program used; then Lean's checker with `--fresh`, and our replay, on the import closure of the Mathlib module that declares `RiemannHypothesis` and on Mathlib as a whole: exit codes, times, counts |
| `replay-Mathlib/replay-summary.txt`, `replay-Mathlib.NumberTheory.LSeries.RiemannZeta/replay-summary.txt` | `stock.sh` | the replay program's own summaries of those two runs |
| `independent-fresh.txt` | `independent.sh fresh` | `lean4lean --fresh` on the import closure of the Mathlib module that declares `RiemannHypothesis` |
| `toolchain.txt` | `toolchain.sh` | the installed Lean toolchain compared, file by file, with the release archive from GitHub. Made on the machine of the second build; the first build used the same release, installed in the same way, and was not compared |

## What the first form of the replay program did not check

`replay-summary.txt` and the other `replay-` files of the first group were written by the first
form of the program. It passed every theorem, definition, opaque constant and axiom to the
kernel, and every inductive type with the constructors that the compiled files hold for it, and
it compared the constructors and recursors in the files with the ones the kernel generated. It
did not compare the inductive types or the quotient constants in the files with the kernel's;
it did not check that the kernel's environment holds nothing but the constants of the files;
where a file listed a constructor that no file contains, it would have built the type
without it; and of each compiled file of Mathlib and of Lean's library it read only the part
that a file outside Lean's module system reads. The paper's Section 2 says what that replay
therefore establishes and what it leaves open. The program now in `verify/replay/` makes those
comparisons; its run over the archive is not among these files.

## How to read the counts

**Names and declarations.** `cut-in.txt.xz` and `cut-out.txt.xz` have one line for each
declaration in each module that declares it. Lean lets an auxiliary theorem be declared again in
every module that needs it, so a name can occur on several lines: the two lists have 1,283,850
and 661,669 lines and 1,265,256 and 640,666 distinct names. All repeats are theorems: 1,093,609
lines and 1,075,015 names inside the cone, 494,644 lines and 473,641 names outside. The paper
counts names. The `BY-ROOT` table of `cut-result.txt` counts lines, which is why its in-cone
column adds up to more than `CONE-SIZE`, which counts names.

**Modules.** The archive has 175,187 Lean files; 175,014 of them declare something
and 147,489 declare something in the cone.

**The replay.** The import closure of `Main` declares 2,701,132 names. 5,840 are unsafe
or partial and are not replayed; the other 2,695,292 were. The categories of
`replay-summary.txt` add up to four fewer than that: the four constants of the quotient type
(`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`) are added in one step and counted in no category.

## What is not in a file

- `replay-log.txt` was written by a wrapper that ran the compiled replay program with
  `LEAN_NUM_THREADS=28`, printing `PAR-START` before it and `PAR-EXIT` with the exit code after
  it, and then the container's cumulative count of processes killed for memory (`oom_kill 2`).
  That counter already read 2 when it was read 28 minutes into the run, and the run exited 0,
  so neither kill was of this run.
- The failed attempt with the toolchain's `leanchecker` in its ordinary mode (2,012 modules on
  20 threads, killed at the container's 128 GB limit with exit code 137) left no output that we
  kept.
- The label `CONE-SIZE-FIVE-THEOREMS` in `cut-result.txt` is the cone of all five theorems of
  `Main.lean`; `CONE-SIZE` is that of `riemannHypothesis` alone, and every other figure in that
  file refers to the latter.
- The per-module logs of the tests (each checker's output on each module of `verify/hostile/`)
  are not kept here; `hostile.sh` writes them again.
