#!/usr/bin/env bash
# After the build: prints the modules in which Mathlib's statement, zeta function and Dirichlet
# L-function are declared; the statements of the five theorems, with the definitions of the
# archive's Statements.lean printed in full; and the axioms each of the five depends on. The
# statements of the three main theorems are also written out here and elaborated afresh against
# the theorems, so that a name in a compiled file that pointed elsewhere would fail. Then
# Lean's checker, and lean4lean if it has been built, are run on the module Statements, which
# holds the archive's own definitions of the statements and is in no sample.
cd lean && . "$HOME/.elan/env"
cat > Check.lean <<'EOL'
import Main
open Lean in
#eval show CoreM Unit from do
  for n in [``RiemannHypothesis, ``riemannZeta, ``DirichletCharacter.LFunction] do
    let env ← getEnv
    let m := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)
    IO.println s!"{n} is declared in {m}"
#check (riemannHypothesis : RiemannHypothesis)
#check (riemannHypothesis :
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2)
#check (LFunction_ne_zero_of_half_lt_re :
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0)
#check (LFunction_eq_zero_re :
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2)
#check @riemannZeta_eq_zero_re
#check @LFunction_ne_zero_of_half_lt_re
#check @LFunction_eq_zero_re
#check @LFunction_eq_zero_re_of_isPrimitive
#print RiemannHypothesis
#print RiemannZetaZerosOnLine
#print DirichletLNonvanishingRightOfHalf
#print DirichletLZerosOnLine
#print PrimitiveDirichletLZerosOnLine
#print axioms riemannHypothesis
#print axioms riemannZeta_eq_zero_re
#print axioms LFunction_ne_zero_of_half_lt_re
#print axioms LFunction_eq_zero_re
#print axioms LFunction_eq_zero_re_of_isPrimitive
EOL
lake env lean Check.lean
echo "CHECK-EXIT $?"
lake env leanchecker Statements > /dev/null 2>&1; echo "leanchecker Statements: exit $?"
l4l=../lean4lean/.lake/build/bin/lean4lean
if [ -x "$l4l" ]; then lake env "$l4l" Statements > /dev/null 2>&1; echo "lean4lean Statements: exit $?"; fi
