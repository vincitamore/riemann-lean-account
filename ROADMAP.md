# What could be done next

Open work that this repository makes possible. Each item says what exists here to start from.
None of it has been done by us unless it says so.

## 1. The corrected replay over the whole archive, an independent kernel, and an independent build

The replay of the whole archive reported in version 1.2 was made with the first form of our
program, which compared less with the kernel's output than the corrected program does (see
the paper, Section 2). The corrected program's run over the archive is under way, on a second
build, and version 1.3 will report it.

Everything we ran uses the kernel inside Lean 4.33.1. The check most worth adding is a
run of an independent implementation of the kernel over the whole import closure of `Main`:
lean4lean with `--fresh`, or an export of the environment checked by an external checker. We
ran lean4lean on the modules of `verify/hostile/` and on the closure of the Mathlib module that
declares the statement (`verify/independent.sh`); on the archive it is a matter of processor
time that we did not have.

Lean's own `leanchecker --fresh Main` would make the full replay independent of our program.
It has not been run on the archive. It runs on one thread. On Mathlib it used
36 minutes of processor time and our program
31; the first replay of the archive took 57
minutes on 28 threads, so this is a matter of a day or more of one
processor, with the memory to hold the whole environment. We intend to make that run on the
second build.

The replay program (`verify/replay/ReplayMain.lean`, 582 lines) has been
reviewed four times by the model that wrote it (`notes/review-replay-program-A.md` to `-D.md`)
and by no person. A person's review is wanted.

The build is ours. `verify/` contains everything needed for another; ours took 13.4
hours on 32 threads. Compare your results with `verify/results/`.

## 2. A proof a person can read

The paper describes the proof; it does not make it short. Two statements look like the right
core of a human proof:

- the slope inequality for nearly tight frames (Statement 5.1 of the paper; `TheoremF` in the
  archive), which is about Hermitian lattices alone;
- the identity that turns the period side into the analytic main term (`key_identity5`), with
  the Chowla-Selberg formula behind it.

A proof organised around these two, with divisibility at inert primes as its one arithmetic
input and everything else quoted from the literature, is the next thing to write. The reading
notes in `notes/` give the path through the source for each step.

## 3. Weakening the inputs to what is used

`verify/results/cut-in.txt.xz` lists every declaration of the archive that is in the dependency
cone of the final theorem, and `cut-out.txt.xz` the 640,666 declared names that are
not. Several inputs are used far below their
strength. The cohomological bound, for example, is proved with a square root that the consumer
discards at once (Section 8.2 of the paper). Replacing each input by the weakest statement that
still closes the proof would shorten it and show which of the deep theorems are essential.

The start of the cut is one line of the program (`verify/cut/CutMain.lean`), so the same
question can be asked of any intermediate theorem.

## 4. Auditing the formalised literature, one statement at a time

The archive proves 179 named statements of published theorems. Appendix C of the
paper says what each Lean statement asserts and gives our comparison with the theorem its name
refers to: the published theorem in the generality of a source (90), a restricted
form (86), or a statement that differs (3), with the reason for each
verdict. The records behind that table are in `paper/refs/` (`rows-A.jsonl`, `rows-B.jsonl`,
`rows-C.jsonl`, with the Lean path of every statement; `rows-author.json`, what each asserts;
`rows-scope-author.json`, the comparison).

We made the comparison from the Lean statements and from the theorems as we know them, without
opening the papers. Each row can be checked independently by one person who knows the theorem:
read the Lean statement, read the paper it is named after, and say whether they agree. That
column is the part of this repository most in need of a second reader.

## 5. Extracting the library

If those statements are what the table says, the archive contains formal proofs of global class
field theory, Tate duality, the theory of Bernstein and Zelevinsky, discrete series for U(p,q),
the Siegel-Weil formula for unitary groups, Galois representations attached to automorphic
representations of unitary groups, arithmetic intersection theory, toroidal compactifications
and resolution of singularities in characteristic zero. None is in a form others can use: the
names are generated, the files import each other almost completely, and the statements are
specialised. Extracting any one of them into a clean development would be a contribution in its
own right.

## 6. Consequences, stated formally

`lean/Corollaries.lean` proves three immediate corollaries against the compiled archive, with
the same three axioms (output in `verify/results/corollaries.txt`):

- zeta has no zero with real part greater than 1/2;
- a Dirichlet L-function of a non-trivial character has no real zero in (1/2, 1];
- zeros of a Dirichlet L-function in the open critical strip lie on the critical line.

`lean/Targets.lean` states, and does not prove, the consequences that seem most worth
formalising next. Each follows from GRH for Dirichlet L-functions by a known argument:

- Miller's deterministic primality test with Bach's bound: an odd n is prime if and only if it
  is a strong probable prime to every base up to 2 (log n)^2;
- for a non-principal Dirichlet character modulo N, some positive a < 2 (log N)^2 has
  chi(a) different from 1 (the bound Miller's test needs);
- the prime number theorem with error term of order sqrt(x) log x;
- a prime in every interval (x, x + C sqrt(x) log x] for large x;
- a prime p congruent to a modulo q with p at most C (phi(q) log q)^2.

The constants in that file are those of the cited papers and must be checked against the
papers before a formalisation relies on them.

## 7. The two programs as general tools

`verify/cut/CutMain.lean` and `verify/replay/ReplayMain.lean` were written because the
toolchain's `leanchecker` re-imports the whole import closure for every module, which does not
finish on a tree of this size. Both programs are short and do not depend on this
archive:

- the cut computes the declaration-level dependency cone of any theorem, with a traversal that
  is linear in the size of each proof term;
- the replay re-checks the declarations of an import closure in the kernel (all but the unsafe
  and partial ones), from an empty environment, in one process, with the checks running in
  parallel.

Either could be turned into a small standalone tool for other large formalisations.

## 8. Other L-functions

The author's note says that Dedekind zeta functions are expected to yield to the same method.
Nothing in this repository bears on that.
