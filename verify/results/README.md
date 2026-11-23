# Results

Output of our own runs of the programs in `verify/`.

The files here are those of the second run, on 21 and 22 November 2026: Mathlib compiled from
source, the archive built, and the steps listed below. Each was made by the script named for it
in the table, as published here, except where the list or the table says otherwise. The files
of the first run, of 20 and 21 November, are in `run1/`; the last section says what made them.

The second machine was a container with 32 threads and a memory limit of
64 GB (the summary's "memory" line is the host's). The order of the steps, with
times in UTC:

1. 21 November. `setup.sh`, with Mathlib compiled from source; the scan, made again during the
   build with the corrected `scan.py`.
2. The build, to 07:31 on 22 November. Beside it, one after another: `toolchain.sh`,
   `hostile.sh`, `independent.sh build` and `hostile`, `stock.sh`, `independent.sh fresh` on
   the module that declares `RiemannHypothesis`; then `hostile.sh` and `stock.sh` once more,
   after the last change to the replay program's comments and to `hostile.sh`, which is why
   `hostile.txt` and `stock.txt` carry the present program's hash. Their times were measured
   under the build's load, and the build's under theirs.
3. After the build: `check.sh`, `corollaries.sh`, `summary.sh`, `cut.sh`, `replay.sh`.
4. 12:55 to 13:58. `sample.sh` ten at a time, with the script as it then was, which kept no
   output of the checker; the process on one name was killed (`sample-earlier.txt`). 13:58 to
   15:00, `independent.sh sample`, which lost its process on the same name.
5. 15:01 to 15:02. Each checker's command on that name, by itself (`sample-alone.txt`): killed
   both times.
6. 15:02 to 16:03. `sample.sh` again, eight at a time, with the script as published; the
   process on that name was killed again. Beside it, to 15:30, `independent.sh fresh` on the
   module that declares the Dirichlet L-function, and, from 15:02 on, step 9.
7. 16:03 to 16:05. A first form of the script that became `sample-exact.sh` ran each command
   on that name by itself once more; both were killed again. Its output is not kept.
8. From 16:12, and again from 16:50 with the scripts as published, whose output is what is
   kept: `check.sh` once more (it now prints more and runs both checkers on `Statements`),
   `sample-exact.sh`, `mathlib-diff.sh`.
9. 15:02 to 23:03. `FRESH_ROOTS=Main stock.sh`: Lean's own checker with `--fresh` on the whole
   import closure of `Main`, on one thread, beside steps 6 to 8 for its first two hours; then,
   to 00:02 on 23 November, the same script ran our replay on `Main` once more, with the
   machine otherwise idle and the number of threads left to Lean's default (`fresh-main/`).
   Its summary differs from `replay-summary.txt` only in the threads line and the seconds.

**The kills for memory.** The container's counter of processes killed for memory read 7 at
the end. All seven were processes of one checker or the other on the name
`Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients`, which has 29 modules under it:
one in each of the three sample runs (steps 4 and 6), two in step 5 and two in step 7. The
summaries of the two later sample runs give the counter before and after; the first sample
run's summary has no counter, and the reading of 1 at the start of the run after it is what
dates its kill. `lean4lean` ends with code 134 on the test module it must reject: with a panic
made fatal it aborts while printing its error, and the line kept from its output is part of
the abort's trace.

**Which script made which file.** `replay.sh`, `hostile.sh`, `stock.sh`, `sample-exact.sh` and
`mathlib-diff.sh` write a hash of the program or script into their output. The other scripts
do not. `sample.sh`, `independent.sh`, `check.sh`, `sample-exact.sh` and `mathlib-diff.sh` were
changed on the machine during 22 November and committed afterwards; the published `sample.sh`
and `independent.sh` differ from the files that ran only in their comments. The cone program
that ran is not identified by a hash in its output.

**A correction to the replay program's comment.** Its header says that the copies kept in
memory come to about 650 MB on the closure of Lean's own library; the fourth review measured
652 MiB, which is 684 MB. The comment is left as it is because every result is stamped with
the program's hash.

## The second run

| File | Produced by | What it is |
|---|---|---|
| `scan.txt` | `scan.py` on the downloaded `lean.tar.gz` | size and SHA-256 of the archive, counts of files and lines, the static inspection. The scan published with versions 1.0 and 1.1 matched no word that follows a dot and looked for fewer words; this is the corrected scan |
| `toolchain.txt` | `toolchain.sh` | the installed Lean toolchain compared, file by file, with the release archive from GitHub |
| `build-summary.txt` | `summary.sh` | the machine; the start, end and exit code of `lake build Main` (Unix seconds); counts of compiled files, failure marks and warnings; the size of the archive's compiled files and the container's memory limit, in units of 10^9 bytes; the peak of the disk as `df -h` read it once a minute, in units of 2^30 bytes; the size of the setup files that `janitor.sh` removed; the toolchain and the revisions of the packages; the build of Mathlib from source, whose time includes the download of the toolchain |
| `check.txt` | `check.sh` | where `RiemannHypothesis`, `riemannZeta` and `DirichletCharacter.LFunction` are declared; the statements of the five theorems, with the definitions of the archive's `Statements.lean` printed in full; the axioms of the five theorems as `#print axioms` reports them; the exit code of the file, in which the three main statements are written out and elaborated afresh against the theorems; and the exit codes of `leanchecker` and `lean4lean` on the module `Statements` |
| `corollaries.txt`, `targets.txt` | `corollaries.sh` | the axioms of the three corollaries of `lean/Corollaries.lean`; `lean/Targets.lean` compiles |
| `cut-result.txt` | `cut.sh` | the size of the cone of `riemannHypothesis` and of the cone of all five theorems, the axioms among the constants of each cone, counts by kind and by the top-level directory of the declaring module, the probes by name |
| `cut-hub.txt` | `cut.sh` | every theorem of the file that collects the published results, with whether it is in the cone |
| `cut-in.txt.xz`, `cut-out.txt.xz` | `cut.sh`, then `xz -9` | every declaration of the archive inside and outside the cone of `riemannHypothesis`, one per line: kind (`T` theorem, `D` definition, `I` inductive type, `C` constructor, `R` recursor, `O` opaque) and full name. Declarations of Mathlib and of Lean's library are not listed |
| `cut-modules.txt.xz` | `cut.sh`, then `xz -9` | the names of the 147,489 modules of the archive that declare at least one declaration of the cone |
| `cut-five-extra.txt` | `cut.sh` | the 24 declarations in the cone of all five theorems that are not in the cone of `riemannHypothesis` |
| `replay-summary.txt` | `replay.sh` | the counts of the kernel replay and of the comparisons |
| `replay-provenance.txt` | `replay.sh` | the SHA-256 of the replay program, the toolchain, the root, the threads, the hash of the compiled `Main`, the times and the exit code |
| `replay-targets.txt` | `replay.sh` | for each of the five theorems: that it was checked as a theorem, the number of names the program reaches from it in the environment the kernel built, and its axioms computed from the terms |
| `replay-failures.txt` | `replay.sh` | the failures: empty |
| `replay-axioms.txt` | `replay.sh` | every axiom not marked unsafe that is declared anywhere in the import closure of `Main` |
| `replay-skipped.txt` | `replay.sh` | the declarations marked unsafe or partial, which a replay does not check |
| `hostile.txt` | `hostile.sh` | the first line is the SHA-256 of the replay program used; then, for each module of `verify/hostile/`, what Lean's checker did in each of its modes, what our replay did, and the failures the replay recorded; then the test of the report on named theorems |
| `fresh-main/stock.txt`, `fresh-main/stock-fresh-Main.log.txt` | `FRESH_ROOTS=Main stock.sh` | the SHA-256 of the replay program; Lean's checker with `--fresh` on the whole import closure of `Main`: exit code and times; then our replay on the same closure, run again: exit code, times, counts. The second file is a copy of the checker's log, `stock-fresh-Main.log`: it is empty, since the checker prints nothing when it accepts. The script does not make a panic fatal, so the empty log is what shows there was none. The log's time in `file-times.txt` is when the run began |
| `fresh-main/replay-Main/replay-summary.txt` | the same | the replay program's own summary of that second run over `Main` |
| `independent-build.txt` | `independent.sh build`, in step 2 | the commit of `lean4lean`, the toolchain it was made for and the one it was built with. The file is the log of that step, copied into the results at 14:03 on 22 November. `sample-exact.txt` gives the SHA-256 of the binary and the time it was last written |
| `independent-hostile.txt` | `independent.sh hostile` | what `lean4lean` did on the same modules, in each of its modes |
| `stock.txt` | `stock.sh` | the first line is the SHA-256 of the replay program used; then Lean's checker with `--fresh`, and our replay, on the import closure of the Mathlib module that declares `RiemannHypothesis` and on Mathlib as a whole: exit codes, times, counts |
| `replay-Mathlib/replay-summary.txt`, `replay-Mathlib.NumberTheory.LSeries.RiemannZeta/replay-summary.txt` | `stock.sh` | the replay program's own summaries of those two runs |
| `independent-fresh.txt` | `independent.sh fresh`, twice | `lean4lean --fresh` on the import closure of the Mathlib module that declares `RiemannHypothesis`, and on that of the module that declares the Dirichlet L-function: one line each |
| `sample-modules.txt`, `sample.txt`, `sample-summary.txt` | `sample.sh` | the names drawn, `Main` and 500 modules of the archive; Lean's checker in its ordinary mode on each name, which covers the module of that name and every module whose name extends it: for each name the exit code and the elapsed seconds of its process; the summary, with the container's count of processes killed for memory before and after, and the number of outputs that mention a panic |
| `independent-sample.txt`, `independent-sample-summary.txt` | `independent.sh sample` | `lean4lean` on the same names, in the same form |
| `sample-prefixes.txt` | `sample-exact.sh` | for each name of the sample, the modules whose names extend it: one line, the name and the module, for each |
| `sample-alone.txt` | step 5 above, by a command typed on the machine and not by a published script | for each checker: its command on the one name by itself, the exit code, the seconds, the highest reading of the container's anonymous memory during the run in bytes (`anon` in `memory.stat`, read once a second), and the counter of kills for memory after it. The command was: start `lake env <checker> <name>` in the background, read `anon` each second while it runs, then print the line |
| `sample-exact.txt` | `sample-exact.sh` | the SHA-256 of the script and of the `lean4lean` binary; which sample files it read and how many lines of each had a code other than 0; the test of each way of calling a checker's function on a module of `verify/hostile/` that must be accepted and on one that must be rejected; then, for the name whose process was killed, each module the name covers, checked one at a time by the checker's own function for one module: the checker, the name, the module, the exit code, the seconds, and the last line the checker printed (for `lean4lean`, the number of declarations checked); then the container's count of kills for memory before and after |
| `sample-earlier.txt`, `sample-earlier-summary.txt` | `sample.sh` as it was before its output was kept, ten at a time | step 4 above: the process on the same name ended with code 137. The container's count of kills for memory read 1 at the start of the step that followed (`independent-sample-summary.txt`) |
| `mathlib-diff.txt` | `mathlib-diff.sh` | Mathlib compiled from source against the community's cached build of the same commit, fetched again on this machine: the last lines the fetch printed; the constants one has and the other lacks; among those both have, the ones whose statements or values differ by the hash stored in the compiled files; and, for each whose statement differs, the statement as each build has it |
| `file-times.txt` | `stat -c '%n %Y'` on the files of the results directory on the machine | the time each was last written (Unix seconds), from which the paper takes the duration of the cone step: from `targets.txt`, the last file of the step before it, to the cone's last file. `cut.sh` records no time itself |

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

**The replay.** The import closure of `Main` declares 2,701,138 names.
5,840 are unsafe or partial and are not replayed; the other 2,695,298 were, and
each was then compared with the constant of the same name in the environment the kernel built.
The line `exported-parts-compared` counts the modules of the closure outside the archive, which
are those of Mathlib, of its dependencies and of Lean's library and all use the module system,
and the constants of their first parts; the paper's Section 2 says what that comparison is.
The line `names-declared-more-than-once` gives the number of such names and then the number of
their further versions; the first run's summary printed only the second number.

**The cones.** `CONE-SIZE` in `cut-result.txt` follows types, values, the link between an
inductive type and its constructors, and the structure of a projection. The number in
`replay-targets.txt` is counted by the replay program in the kernel's environment; it also
follows the blocks and rules of the recursors reached and the names into which numerals and
strings unfold, and it is larger by two for `riemannHypothesis`. `CONE-SIZE-FIVE-THEOREMS` is
the cone of all five theorems of `Main.lean`, and every other figure of `cut-result.txt` refers
to the cone of `riemannHypothesis` alone.

## The two runs compared

`paper/tools/numbers.py` stops unless all of the following hold, and they do. The three lists
`cut-in.txt.xz`, `cut-out.txt.xz` and `cut-modules.txt.xz` decompress to the same bytes in the
two runs. `cut-five-extra.txt`, `replay-axioms.txt` and `replay-skipped.txt` hold the same names.
The `BY-ROOT` tables agree for every root but Mathlib. The replays' counts of modules,
definitions, opaque constants, axioms, inductive types and their blocks, constructors,
recursors, quotient constants and skipped declarations agree; the counts of names, of
declarations replayed and of theorems are larger in the second run by the same number, which is
the number by which Mathlib from source has more constants than the first build's Mathlib had.
`mathlib-diff.txt` accounts for that number: the names only in the build from source less the
names only in the cached build. That the cache fetched for that comparison is the Mathlib of the
first build, whose compiled files were not kept, rests on this equality of counts and on the
commit.

## The first run, in `run1/`

One build, with Mathlib's compiled files from the community's cache, on a machine limited to
128 GB. Not all of its files were written by the scripts in their present form.

| File | Produced by | Note |
|---|---|---|
| `build-summary.txt` | assembled by hand from the build log, which was not kept | shorter than `summary.sh` now writes |
| `check.txt` | `check.sh` as it then was | |
| `axioms.txt` | the first axiom check, made when the build ended | the same axioms |
| `corollaries.txt`, `targets.txt` | the two Lean files compiled against the built archive | |
| `cut-*.txt`, `cut-*.txt.xz` | `cut/CutMain.lean` as published with version 1.1 | the same traversal as the present program, which prints more |
| `replay-summary.txt`, `replay-failures.txt`, `replay-axioms.txt`, `replay-skipped.txt` | `replay-program-first-form.lean` | see below |
| `replay-log.txt` | a wrapper that ran that program with `LEAN_NUM_THREADS=28` | it prints `PAR-START` before and `PAR-EXIT` with the exit code after, then the container's cumulative count of processes killed for memory (`oom_kill 2`). That counter already read 2 when it was read 28 minutes into the run, and the run exited 0, so neither kill was of this run |
| `replay-program-first-form.lean` | | the replay program as it was then (the file `verify/replay/ReplayMain.lean` of version 1.1) |

The first form of the replay program passed every theorem, definition, opaque constant and axiom
to the kernel, and every inductive type with the constructors that the compiled files hold for
it, and it compared the constructors and recursors in the files with the ones the kernel
generated. It did not compare the inductive types or the quotient constants in the files with
the kernel's; it did not check that the kernel's environment holds nothing but the constants of
the files; where a file listed a constructor that no file contains, it would have built the type
without it; and of each compiled file of Mathlib and of Lean's library it read only the part
that a file outside Lean's module system reads. The categories of its summary add up to four
fewer than the declarations replayed: the four constants of the quotient type are added in one
step and counted in no category.

An attempt of that run with the toolchain's `leanchecker` in its ordinary mode (2,012 modules
on 20 threads, killed at the container's 128 GB limit with exit code 137) left no output that we
kept.

## What is not in a file

- The per-module outputs of the checkers (on each module of `verify/hostile/`, and on each
  module of the samples) are not kept here; the scripts write them again. The sample summaries
  count the outputs that mention a panic.
- The build logs are not kept here; `build-summary.txt` is what `summary.sh` took from them.
- The lists of all constants of the two builds of Mathlib (about 772,000 lines each) are not
  kept; `mathlib-diff.txt` gives their sizes, the hashes of the lists of names, and their
  differences.
