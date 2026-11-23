# The argument of Alpöge's formal proof of the Riemann Hypothesis

On 20 November 2026 Levent Alpöge released a Lean 4 formalisation, 17 million lines long, of a
proof of the Riemann Hypothesis and of its analogue for every Dirichlet L-function. His note
says that no human-readable proof has been written.

This repository contains two things:

1. **A verification.** We built the archive twice, the second time with Mathlib compiled from
   source, checked which axioms the theorems depend on, replayed its declarations through the
   Lean kernel from an empty environment, with Lean's own checker and with a program of ours,
   compared what the kernel built with the compiled files, and computed which declarations
   the final theorem actually uses.
2. **An account of the argument**, read from the Lean source: the paper
   [`paper/main.pdf`](paper/main.pdf), and a statement of its skeleton on one page,
   [`paper/one-page.pdf`](paper/one-page.pdf).

The archive itself is not redistributed here. Its author serves it in fourteen parts,
`https://alpo.ge/lean.tar.gz.part01` to `part14`; `verify/setup.sh` fetches them and checks the
hash.

## What the machine says

The numbers are those of the second build. The first build, with Mathlib from the community's
cache, gave the same lists of the archive's declarations and the same replay counts but for
Mathlib's; its replay was made with the earliest form of our program. Its files are in
`verify/results/run1/`.

| Check | Result |
|---|---|
| Archive | `lean.tar.gz`, 239,275,554 bytes, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`; 175,187 Lean files, 17,374,215 lines |
| Toolchain | Lean 4.33.1; on the second machine the installed toolchain is identical file by file (17,493 files) to the release on GitHub. Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` |
| Build | twice. The second time Mathlib was compiled from source first (8,312 modules, 19 minutes), then `lake build Main` exited 0 after 183,893 jobs and 16.0 hours on 32 threads. All 175,187 modules built in both |
| The two builds | the lists of the archive's declarations inside and outside the dependency cone are identical byte for byte. The first build's Mathlib was not kept; the community's cache, fetched again on the second machine, was compared with Mathlib from source. From source it has 8 private auxiliary lemmas of `simp` and `abel` that the cached build lacks, and lacks 2 that it has; no other name differs. Among the 772,124 constants both have, by Lean's 32-bit hash, statements differ only in one further auxiliary lemma and one equation that Lean generates for a definition (`SimpleGraph.Walk.take.eq_2`), which the two builds state in different forms, and proofs only in those and in the proofs in which the auxiliary lemmas occur. `mathlib-diff.txt` names sixteen constants in all, and two of them are in the cone of `riemannHypothesis` as the second build has it: the theorem `MvPolynomial.coeff_killCompl`, whose proof differs, and the one auxiliary lemma of that proof which only the build from source has. No statement that differs is in the cone |
| Statement | `riemannHypothesis : RiemannHypothesis`, where `RiemannHypothesis` and `riemannZeta` are Mathlib's own (declared in `Mathlib.NumberTheory.LSeries.RiemannZeta`). `verify/check.sh` writes out the three main statements and elaborates each afresh against its theorem |
| Axioms | each of the five top theorems depends on `propext`, `Classical.choice`, `Quot.sound` and nothing else: by `#print axioms`, which for an imported theorem prints a recorded list, and again computed from the terms by the replay, in the environment the kernel built. The cone program finds no other axiom among the constants of the cone of the five |
| Kernel replay | the import closure of `Main` (the archive, Mathlib and its dependencies, Lean's library) declares 2,701,138 names; the 2,695,298 that are not marked unsafe or partial were replayed through the kernel from an empty environment, among them 2,084,262 theorems, 556,318 definitions and 15,769 inductive types; 0 failures. The environment the kernel built was then compared with the compiled files, constant by constant, in both directions: no difference. 116 minutes on 32 threads |
| The checker, tested | 29 small modules. 25 of them have, in their import closure, a compiled file that holds something the kernel never accepted or whose parts disagree in a way Lean never writes (one proves `False`, compiles, and has no axioms reported). Our replay rejects all 25; Lean's `leanchecker --fresh` rejects 9 of them |
| Lean's own checker | `leanchecker --fresh` accepts the whole import closure of `Main`: exit code 0 after 8.0 hours on one thread. So the kernel has accepted each of the 2,695,298 constants that are not marked unsafe or partial, in the version Lean's import keeps of its name, twice: once driven by Lean's checker and once by our program. It also accepts all of Mathlib and the closure of the module that declares the statement, as our replay does. In its ordinary mode it takes a name as a prefix and checks every module under the name against its imports. It was run on 501 names, `Main` among them, which cover 530 modules, and every module is accepted: 500 names by the command. For one name, with 29 modules under it, the command imports the closure 30 times at once and the system killed it at the container's memory limit, also when it ran by itself; the checker's function for one module was then called on each of the 30 in turn and accepted all. It also accepts the module `Statements` |
| A second implementation of the kernel | `lean4lean`, which its authors describe as derived from the kernel's C++ code. It accepts the import closures of the two Mathlib modules that declare `RiemannHypothesis`, `riemannZeta` and the Dirichlet L-function, and the archive's module `Statements`; with `--fresh` it rejects 9 of the 25 test modules; and on the same 501 names every module is accepted: 500 names by the command. For one name, with 29 modules under it, the command imports the closure 30 times at once and the system killed it at the container's memory limit, also when it ran by itself; the checker's function for one module was then called on each of the 30 in turn and accepted all |
| Dependency cone | `riemannHypothesis` depends on 1,478,220 declarations. Of the archive's 1,548,656 theorems (counted by name), 1,075,015 are among them; 147,489 of the 175,014 modules that declare anything declare something in the cone. The archive declares no axiom anywhere |
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

This certifies that the theorems hold in Lean with Mathlib. It does not certify any description
of the proof, including ours. Three limits. The full replay uses one kernel, the one inside Lean
4.33.1: the build, our replay and Lean's checker share it, with the code that reads
compiled files, so their agreement is one witness and not several. That code trusts the hashes
and flags that names and terms carry in a compiled file, and the kernel trusts the definitions
of a few constants it knows by name. A second implementation of the kernel has been run on the
test modules, on the closures of the Mathlib definitions the statements are about, on the
archive's module of statements and on a sample of the archive, but not on the whole archive;
that is the check most worth adding. The replay program is ours; it has been reviewed four
times and tested as described, by the model that wrote it and by no person. That the kernel
accepts each of the 2,695,298 constants replayed no longer rests on it, since Lean's own checker finds the
same; the comparisons it adds, and its check of the further versions of repeated names, do.
And both builds are ours: we know of no other.

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

On a Linux machine with 32 threads and 150 GB of free disk, with this repository's `verify/`
and `lean/` copied beside an empty working directory. Give it 128 GB of memory if you can. The
second build ran in a container limited to 64 GB. That sufficed for the build, the
cone and the replay. It did not suffice for the checkers' ordinary mode on a name that covers
30 modules, which imports the closure that many times at once;
`sample-exact.sh` handles that case.

```sh
mkdir work && cd work && mkdir out
V=/path/to/verify
bash $V/setup.sh                                   # fetch, check the hash, unpack, toolchain, Mathlib from source
python3 $V/scan.py lean.tar.gz > out/scan.txt      # static inspection, before any build
bash $V/toolchain.sh out                           # the toolchain against the GitHub release
bash $V/janitor.sh > janitor.log 2>&1 &            # keeps the disk from filling; see the script
bash $V/build.sh > build.log 2>&1                  # the long step
kill %1                                            # stop the janitor once the build has ended
bash $V/summary.sh build.log mathlib-build.log janitor.log > out/build-summary.txt
bash $V/check.sh > out/check.txt                   # statements, where Mathlib declares them, axioms; run again after independent.sh build
bash $V/corollaries.sh /path/to/lean out           # the corollaries and the targets, against the built archive
bash $V/cut.sh $V/cut out                          # dependency cone
bash $V/replay.sh $V/replay out                    # kernel replay and comparison
bash $V/hostile.sh $V/hostile $V/replay out/hostile-files > out/hostile.txt   # the checkers on modules built to be wrong
bash $V/stock.sh $V/replay out                     # Lean's checker and ours on Mathlib
FRESH_ROOTS=Main bash $V/stock.sh $V/replay out/fresh-main   # Lean's checker over the whole archive, 8.0 hours here, then our replay again
bash $V/independent.sh build > out/independent-build.txt   # a second implementation of the kernel, lean4lean
bash $V/independent.sh hostile $V/hostile out/hostile-files # on the same test modules; writes out/hostile-files/independent-hostile.txt
bash $V/independent.sh fresh out                   # on the closure of the module that declares RiemannHypothesis
bash $V/independent.sh fresh out Mathlib.NumberTheory.LSeries.DirichletContinuation   # and of the L-function
bash $V/sample.sh out 500 8                        # Lean's checker on a sample of the archive
bash $V/independent.sh sample out 10               # lean4lean on the same sample
bash $V/sample-exact.sh out $V/hostile             # what each name covers; a name whose process was killed, module by module
bash $V/mathlib-diff.sh out                        # Mathlib from source against the community's cached build
bash $V/cone-probe.sh $V/cut out                   # which of the constants that differ are in the cone
```

The tests on Mathlib and on the test modules (`hostile.sh`, `stock.sh`, the first three uses of
`independent.sh`) need only Mathlib and may run beside the build, as ours did.

Compare with `verify/results/`, whose `README.md` says what wrote each file and in what order
the second run made them; the files of the first run are in `verify/results/run1/`.

## Authors and licence

Qui Vincit and Fable. Fable is a language model (Claude, Anthropic); the paper's Section 12 says
who did what. The mathematics is Levent Alpöge's and that of the model he worked with; this is
an exposition of it.

Text and data are under CC BY 4.0, code under the MIT licence; see `LICENSE`. Corrections are
welcome as issues or pull requests.

## Versions

- **1.5**, 23 November 2026. The constants of Mathlib that differ between the two builds, located
  against the cone.
  - A new program and script (`verify/cut/ConeProbe.lean`, `verify/cone-probe.sh`) ask of each
    such constant whether it is in the cone of `riemannHypothesis`
    (`verify/results/cone-probe.txt`). One theorem whose proof differs and one auxiliary lemma
    are; no constant whose statement differs is. Version 1.4 had left this undetermined.
- **1.4**, 23 November 2026. Lean's own checker over the whole archive.
  - `leanchecker --fresh Main` ended with exit code 0 after 8.0 hours
    (`verify/results/fresh-main/stock.txt`). The paper's Section 2.8 and its limits now say
    what no longer rests on our replay program and what still does.
- **1.3**, 22 November 2026. The second build, and the corrected replay over the whole archive.
  - The archive was built a second time, on another machine, with Mathlib compiled from
    source. The corrected replay program ran over the whole import closure: no failure, and
    the environment the kernel built equals the compiled files constant by constant. The
    axioms of the five theorems are now also computed from the terms.
  - The two builds give the same lists for the archive, byte for byte. Mathlib from source
    differs from the cached build in the names of 8 and
    2 private auxiliary lemmas that tactics generate, in the statements of
    2 constants that both have and in the values of
    6 (`verify/results/mathlib-diff.txt`).
  - After the fourth reviewer's check, only the comment at the head of the replay program was
    changed, to correct sentences the reviewer had named and to add a paragraph on memory. The
    test script refuses an empty or repeated list of modules and tests the program's list of
    axioms.
  - `lean4lean` is now described as its authors describe it, a second implementation derived
    from the kernel's C++ code, and no longer as an independent kernel. It was also run on
    the closure of the module that declares the Dirichlet L-function and on the archive's
    module `Statements`.
  - The sample steps write each checker's output to a log on the machine, make a panic fatal
    and record the container's count of processes killed for memory. The checkers take a name
    as a prefix, which the text now says; `verify/sample-exact.sh` lists what each name covers
    and checks module by module the one name on which the command, importing the closure
    30 times at once, was killed at the container's memory limit.
  - `verify/check.sh` prints the archive's definitions of the statements in full and
    elaborates the three main statements afresh against the theorems.
  - `verify/summary.sh` printed a capped number for the total size of the build's setup files
    and the host's memory in place of the container's; both are corrected.
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
