# Lean files

The archive corollaries and target statements are in these two files.

- `Corollaries.lean` proves three immediate corollaries from the archive's `Main` and Mathlib
  alone, and prints their axioms. It needs a built copy of the archive: from the archive's root,
  `lake env lean /path/to/Corollaries.lean`. Our output is in
  `../verify/results/corollaries.txt`: each depends on `propext`, `Classical.choice` and
  `Quot.sound` only.
- `Targets.lean` states, and does not prove, consequences of GRH for Dirichlet L-functions that
  are worth formalising next. It needs Mathlib only. Each `def` is a proposition that Lean
  checks for being well formed; the constants are those of the cited papers and must be checked
  against the papers before a formalisation relies on them.

## Two conditional results

[`MillerFromSmallNonresidue.lean`](MillerFromSmallNonresidue.lean) proves
`SmallNonresidue → MillerTestIsCorrect`. For an odd composite modulus the passing bases lie in
a proper subgroup of the unit group. A nonprincipal character that is trivial on that subgroup
turns the assumed small nonresidue into a failing base. When the bound reaches the modulus,
its least prime factor already supplies a failing base.

[`PrimeCountingFromPsi.lean`](PrimeCountingFromPsi.lean) assumes
$|\psi(x)-x|\le C\sqrt{x}\log^2 x$ for $x\ge2$ and proves `PrimeCountingError`.
Mathlib's bound on $\psi-\theta$ gives the corresponding bound for $\theta$. Abel summation
and integration by parts leave an integral bounded by a constant times $\int_2^x t^{-1/2}\,dt$.

Both results use Mathlib alone. The verified pins are Lean 4.36.0 and Mathlib
[`fc4f59e5`](https://github.com/leanprover-community/mathlib4/commit/fc4f59e577feb1a4956671bc04ac18aaaf8cd842).
The Miller proof uses Korselt's squarefreeness condition from `Mathlib.NumberTheory.CarmichaelNumber`,
which is available in v4.36.0. The axiom reports for both theorems and the module replay
results are recorded in [conditional-targets.txt](../verify/results/conditional-targets.txt).

From a checkout of the pinned Mathlib, with elan available, run the following in a POSIX shell.
Set `src` to the absolute path to this directory. The loop compiles the six modules in dependency
order and replays each against its imports.

```sh
set -eu
src=/path/to/riemann-lean-account/lean
lake exe cache get
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out:$(lake env printenv LEAN_PATH)"
for m in Targets MillerPrime MillerSubgroup MillerCharacter MillerFromSmallNonresidue PrimeCountingFromPsi; do
  lean -R "$src" -o "$out/$m.olean" "$src/$m.lean"
  leanchecker -v "$m"
done
```

See [ROADMAP.md](../ROADMAP.md#6-consequences-stated-formally).
