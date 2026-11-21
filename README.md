# The argument of Alpöge's formal proof of the Riemann Hypothesis

On 20 November 2026 Levent Alpöge released a Lean 4 formalisation, 17 million lines long, of a
proof of the Riemann Hypothesis and of its analogue for every Dirichlet L-function. His note
says that no human-readable proof has been written.

This repository contains two things:

1. **A verification.** We built the archive, checked which axioms the theorems depend on,
   replayed its declarations through the Lean kernel from an empty environment, and computed
   which declarations the final theorem actually uses. The replay program was then reviewed,
   found to check less than we had said, corrected and tested; its second run over the archive
   is under way (see "Status" below).
2. **An account of the argument**, read from the Lean source: the paper
   [`paper/main.pdf`](paper/main.pdf), and a statement of its skeleton on one page,
   [`paper/one-page.pdf`](paper/one-page.pdf).

The archive itself is not redistributed here. Its author serves it in fourteen parts,
`https://alpo.ge/lean.tar.gz.part01` to `part14`; `verify/setup.sh` fetches them and checks the
hash.

## What the machine says

Rows marked (2) were made on the machine of the second build, on its own build of Mathlib from
source, while it was building the archive; the others are from the first build.

| Check | Result |
|---|---|
| Archive | `lean.tar.gz`, 239,275,554 bytes, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`; 175,187 Lean files, 17,374,215 lines |
| Toolchain (2) | Lean 4.33.1; the installed toolchain is identical file by file (17,493 files) to the release on GitHub. The first build used the same release, installed in the same way; its toolchain was not compared. Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` |
| Build | `lake build Main` exited 0 after 183,893 jobs and 13.4 hours on 32 threads; all 175,187 modules built |
| Statement | `riemannHypothesis : RiemannHypothesis`, where `RiemannHypothesis` and `riemannZeta` are Mathlib's own (declared in `Mathlib.NumberTheory.LSeries.RiemannZeta`) |
| Axioms | `#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` and nothing else for each of the five top theorems. For a theorem of an imported module that command prints a list recorded in the compiled file; the run under way computes the axioms from the terms as well |
| Kernel replay | the import closure of `Main` (the archive, Mathlib, Lean's library) declares 2,701,132 names; the 2,695,292 that are not marked unsafe or partial were replayed through the kernel from an empty environment: 2,084,256 theorems, 556,318 definitions, 15,769 inductive types; 0 failures; 57 minutes. This was the first form of our program, which compared only constructors and recursors with the kernel's output and read only one part of each compiled file of Mathlib: see the correction under version 1.2 below |
| The checker, tested (2) | 29 small modules. 25 of them have, in their import closure, a compiled file that holds something the kernel never accepted or whose parts disagree in a way Lean never writes (one proves `False`, compiles, and has no axioms reported). The corrected replay rejects all 25; Lean's `leanchecker --fresh` rejects 9 of them |
| Lean's own checker (2) | `leanchecker --fresh` accepts the import closure of the module that declares the statement, and all of Mathlib; so does the corrected replay. It has not been run on the archive |
| A second kernel (2) | `lean4lean` accepts the import closure of the module that declares the statement, and rejects 9 of the 25 test modules. It has not been run on the archive |
| Dependency cone | `riemannHypothesis` depends on 1,478,219 declarations. Of the archive's 1,548,656 theorems (counted by name), 1,075,015 are among them, in 147,489 of the 175,014 modules that declare anything. The archive declares no axiom anywhere |
| Literature | the archive proves 179 named results of the literature; the proof of the final theorem refers to all of them |

The five theorems of the archive's `Main.lean`, with the definitions of its `Statements.lean`
unfolded:

```lean
theorem riemannHypothesis : RiemannHypothesis
theorem riemannZeta_eq_zero_re :
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2
theorem LFunction_ne_zero_of_half_lt_re :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
theorem LFunction_eq_zero_re :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
theorem LFunction_eq_zero_re_of_isPrimitive :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

This certifies that the theorems hold in Lean with Mathlib, as far as the checks above reach:
the axioms are those of the lists recorded in the compiled files, and the replay establishes
what the paper's Section 2 says. It does not certify any description
of the proof, including ours. Four limits. The replay of the whole archive reported here was
made with the first form of our program and establishes less than a full comparison would; the
corrected program's run is under way. Everything here uses one kernel, the one inside Lean
4.33.1: the build, our replay and Lean's checker share it, so their agreement is one
witness and not several. An independent implementation of the kernel has been run on the test
modules and on the closure of the statement, but not on the archive. The replay program is
ours; it has been reviewed four times and tested as described, by the model that wrote it and
by no person. And the build is ours: we know of no other.

## Status

A second build of the archive is running, with Mathlib compiled from source, to be followed by
the corrected replay, the dependency cone, Lean's own checker on a sample of the archive's
modules and the second kernel on the same sample; we then intend to run Lean's own checker
over the whole archive. Version 1.3 will report it. Until then the
numbers for the archive in the paper are those of the first build. `verify/results/README.md`
says what wrote each results file.

## What the argument is

The paper says it at length. In one paragraph: a windowed form of Landau's theorem reduces
the statement, for each character, to a one-sided bound for a smoothed sum over prime powers on long
windows of scales. An exact identity for an auxiliary CM field turns that bound into an upper
bound for a weighted count of prime powers whose Frobenius lies outside a CM type. The upper
bound has the shape x/m + m, and the exponent 1/2 comes from balancing the two at m near the
square root of x; m is the length of a chain of theta lifts between definite unitary groups.
The bound is proved by squeezing the slope of a lattice of periods between two estimates. From
below: periods are highly divisible at inert primes, because a CM elliptic curve has a formal
group of height two there, and a slope inequality for nearly tight frames of maps transfers
that divisibility to the lattice of periods. From above: the slope of that lattice is computed,
and through the Chowla-Selberg formula it is exactly the main term of the count.

## Layout

| Path | Contents |
|---|---|
| `paper/` | the paper `main.pdf` and the one-page statement `one-page.pdf`, their LaTeX source, the bibliography with the record behind every entry (`refs/`), the table of where each statement was read (`basis.md`), and the scripts that read every measured number from the results (`tools/numbers.py`) and check every cited Lean name against the cone (`tools/check_names.py`) |
| `verify/` | the scripts, the two Lean programs (dependency cone, kernel replay), the modules built to test the checkers (`hostile/`), and the output of our runs in `verify/results/` |
| `notes/` | the reading notes the paper was written from, the reports on bounded parts of the source, and the four reviews of the replay program |
| `lean/` | three corollaries proved against the archive, and statements of consequences worth formalising |
| `ROADMAP.md` | what could be done next |

## Reproducing the verification

On a Linux machine with 32 threads, 128 GB of memory and 150 GB of free disk, with this
repository's `verify/` and `lean/` copied beside an empty working directory:

```sh
mkdir work && cd work
V=/path/to/verify
bash $V/setup.sh                                   # fetch, check the hash, unpack, toolchain, Mathlib from source
python3 $V/scan.py lean.tar.gz > scan.txt          # static inspection, before any build
bash $V/toolchain.sh out                           # the toolchain against the GitHub release
bash $V/janitor.sh > janitor.log 2>&1 &            # keeps the disk from filling; see the script
bash $V/build.sh > build.log 2>&1                  # the long step
kill %1                                            # stop the janitor once the build has ended
bash $V/summary.sh build.log mathlib-build.log janitor.log > out/build-summary.txt
bash $V/check.sh                                   # statement and axioms
bash $V/cut.sh $V/cut out                          # dependency cone
bash $V/replay.sh $V/replay out                    # kernel replay and comparison
bash $V/hostile.sh $V/hostile $V/replay out/hostile-files > out/hostile.txt   # the checkers on modules built to be wrong
bash $V/stock.sh $V/replay out                     # Lean's checker and ours on Mathlib
bash $V/sample.sh out 500 16                       # Lean's checker on a sample of the archive
bash $V/independent.sh build                       # an independent kernel: see the script for its three uses
```

Compare with `verify/results/`, whose `README.md` says what wrote each file. In this version
the results for the archive are those of the first build, some of them made before these
scripts had their present form; the second build runs exactly the commands above.

## Authors and licence

Qui Vincit and Fable. Fable is a language model (Claude, Anthropic); the paper's Section 12 says
who did what. The mathematics is Levent Alpöge's and that of the model he worked with; this is
an exposition of it.

Text and data are under CC BY 4.0, code under the MIT licence; see `LICENSE`. Corrections are
welcome as issues or pull requests.

## Versions

- **1.2**, 21 November 2026.
  - *A correction to what versions 1.0 and 1.1 claimed for the kernel replay.* Two reviews of
    the replay program found, among other things, that it compared only constructors and
    recursors with the kernel's output, so that an inductive type or a quotient constant
    written directly into a compiled file would have been counted and never examined, and
    that it dropped a listed constructor it could not find. Neither review found a way for
    this to affect the five theorems, but the replay established less than those versions
    said, and the paper now says what it did establish and what it left open. A statement in
    the program's comments about Lean's own traversal of terms was false and is removed.
  - The program was rewritten: it now compares the environment the kernel builds with the
    compiled files in both directions. A third review of the rewritten program found one more
    gap (the files that only Lean's module system reads were not compared) and that two checks
    were untested. A fourth review, of the corrections, found two more routes of the same
    kind and a weakness of the test script. The routes were closed, each with a test module,
    and the script was corrected; the fourth reviewer then checked the corrections and found
    no input on which the corrected program reports success wrongly (appended to its report,
    with the points it leaves open). None of these gaps touches the five theorems: the archive
    does not use the module system. All four reviews are in `notes/`.
  - The static scan matched no word that follows a dot, so it could not have found several of
    the names it was looking for. It is corrected and was run again; it finds none of them.
  - The checker is tested on modules built to be wrong (`verify/hostile/`), against Lean's own
    checker and against an independent implementation of the kernel, and on Mathlib against
    Lean's own checker.
  - The run of the corrected program over the whole archive is not in this version; it is
    under way on a second build.
  - Every number in the paper is now read from the results files by a script
    (`paper/tools/numbers.py`), and every Lean name the paper cites is checked against the
    dependency cone (`paper/tools/check_names.py`).
  - The comparison of each formal statement of the literature with its published theorem is
    now the authors' own, with a reason printed for each row (90 as published,
    86 restricted, 3 that differ; version 1.1 printed 99, 75 and 5
    from delegated reports).
  - The gain is stated exactly (Section 5.3); the notation is made consistent, with a table
    (Section 3); a one-page statement of the skeleton is added.
- **1.1**, 21 November 2026. Corrections after two referee reads of version 1.0 made by further
  instances of the model, each finding checked against the Lean source or the results files
  before the text was changed.
  - Counts of the archive's declarations are now by distinct name. Version 1.0 counted a
    theorem once for each module that declares it (1,093,609 of 1,588,253 in the cone); by name
    the figures are 1,075,015 of 1,548,656. The share, 69%, is unchanged.
  - The static inspection is now a published script with its output (`verify/scan.py`,
    `verify/results/scan.txt`).
  - The kernel replay is described exactly: 2,695,292 of the 2,701,132 imported declarations,
    the rest being unsafe or partial ones that no replay checks. A limit is added: the replay
    program is ours and unreviewed.
  - The statement about Vandiver's conjecture in Section 8.1 was wrong for the field of
    $\ell$-th roots of unity and is corrected.
  - The error term left by the period side is the first cost of Section 4.4, not the third;
    the size conditions that make the three costs come out are now stated; the lattices $N_u$
    are rescalings of sublattices, not lattices containing $M_u$; the clauses that close the
    chain of Section 5.6 are named.
  - In Appendix C the comparison of each formal statement with its published theorem is
    attributed to the reports it came from, and one row is relabelled (99 general, 75 special
    cases).
  - Smaller corrections of notation, attribution and cross-reference.
- **1.0**, 21 November 2026. First version.
