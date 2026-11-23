# Landau on windows, and the supply of hosts

Read 2026-11-20 from source text only (build unfinished). Paths are relative to `src/` in the archive: `LT/` = `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/`, `MSB/` = `Development/AutomorphicArithmetic/MeanSquareBounds/`, `CB/` = `Development/AutomorphicArithmetic/CharacterBoxes/`, `TGC/` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`, `JCS/` = `Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/`. Tags: **[read]** transcribed from a definition, statement or proof body; **[proved-by]** a theorem with that statement exists and its proof term was seen; *[inferred]* my interpretation. A tag covers the sentence it opens. A grep for `sorry|admit|axiom` over these directories, `Formalism/LandauZeroFreeBounds` and `Formalism/ZeroFreeRegion` found nothing.

## Direct answers

1. **[read]** `formB` proves Landau on windows for every level and every λ > 1; non-negativity of the coefficients is neither assumed nor used.
2. **[read]** It bounds high Taylor coefficients of the Laplace transform of Gm(e^u) at a real point; their kernel sits in the window, and a pole nearer than σ − θ would make them grow too fast.
3. **[read]** A one-sided bound suffices because |g| + g = 2·max(g, 0); positive weights make every zero a pole with non-zero residue, positive at real zeros; no zero-free region or zero density enters.
4. *[inferred]* So one zero of one L(s, ψ_j) right of θ makes the y^{−θ}-weighted log-average of Gm⁺ exceed Y^η on every late window, not just along a sequence.
5. **[read]** λ > 1 is needed because the a priori bound |Gm| ≤ C y² must be beaten off the window; any λ > 1 works, and 3/2 is chosen by the supply.
6. **[read]** The auxiliary twists are bounded as a family: most primes q ≈ exp(Y^{ε/5}), then most d, are good, by an in-tree mean square and an in-tree zero-density count near Re s = 1 − 1/400; half suffices.
7. *[inferred]* Their huge conductors are irrelevant: what must cancel is a sum of length Y^{400K}, and its tail needs only a zero-free box near Re s = 1.
8. **[read]** Each ψ is handled alone, assuming only the cohomological bound `VWinAt ψ 401`: nothing about zeros, and no induction on conductor, order or scale.
9. **[read]** Windows come from VWin, valid only on [W, W²]; 3/2 absorbs a constant factor k (k³ ≤ W); nothing degenerate was found, two harmless hypotheses are dropped, several definitions are dead.

## A. Landau on windows

### A.1 Statement

**[read]** The function of a level (TGC/ExplicitFormulaErrorOfHostConditions.lean:36–38, 105–121):
```
wt ψ        := if Λ.psK = some ψ then 1 else (3 * Λ.o + 1)⁻¹
Gm y        := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re   -- Nt = KEPT minus the trivial character
Level.cyc ψ := Level.ofSub (Subgroup.zpowers ψ.χ)  -- KEPT = primitive versions of ψ^j, psK := none, o := |⟨ψ⟩|
```
**[read]** Gz y = Σ_{n≤y} Λ(n)(y/n − 1) − y log y + (1+γ)y (`Formalism/StatementOC.lean:13`, with `Gz_eq`), and for χ ≠ 1, gChi χ y = Σ_{n≤y} Λ(n)χ(n)(y/n − 1) + y·L′/L(1, χ) (TGC/Analytic.lean:23).
**[read]** So Gm = G + (3o+1)⁻¹ Σ_{j=1}^{o−1} Re G_{ψ_j}, ψ_j primitive inducing ψ^j, with ramp weight (y/n − 1)⁺ and Mellin transform −(L′/L(s) − s·L′/L(1))/(s(s−1)) (`mellin_Gchi_of_ne_one`, LT/mellinGchiOfNeOne.lean:116).
*[inferred]* For n prime to the conductor the coefficient of Λ(n)(y/n − 1)⁺ is 3o/(3o+1) or 4o/(3o+1), o times the share `lam` (same file, :135) the tops give the coset of Frob_n: positive, but unused (A.4).

**[read]** The statement (TGC/Window.lean:8, 30):
```
HasWindows S la := ∀ y, ∃ Y, y ≤ Y ∧ ∀ x, Y ≤ x → x ≤ Y ^ la → x ∈ S
FormBAt la      := ∀ θ, 0 < θ → θ < 1 → HasWindows {x | Λ.Gm x ≤ x ^ θ} la → Λ.ZeroFreeAbove θ
```
**[proved-by]** `formB : ∀ Λ : Level, Λ.FormB`, i.e. FormBAt for every la > 1.
**[read]** It builds a `CharFamily` with the same Gm, weight 1 on the trivial character and wt > 0 elsewhere (`level_family`), and applies, with δ := la − 1 and C := 1,
```
zeroFree_of_rpow_window F (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
  (h : ∀ Y₀, ∃ Y, Y₀ ≤ Y ∧ ∀ y ∈ Icc Y (Y^(1+δ)), Gm F y ≤ C * y^θ) : ZeroFree F θ
```
**[read]** `CharFamily` (`Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean:24`) has only `a i > 0` and `N i = 1 ∨ χ i ≠ 1`: no coefficient positivity.

### A.2 Proof sketch

1. **[read]** `windowHyp_of_rpow` turns the bound into `WindowHyp` (CharFamily.lean:41): for every η > 0 and Y₀ there are Y ≥ Y₀ and R ≥ max(Gm, 0) on [Y, Y^{1+δ}] with ∫ R(y) y^{−θ−1} dy ≤ Y^η (R = |C|y^θ gives |C|δ log Y); then u = log y.
2. **[read]** `poleData`: Φ(s) = Σ_i (a_i/2)(Φ_{χ_i} + Φ_{χ_i⁻¹}) equals ∫_0^∞ Gm(e^u) e^{−su} du for Re s > 2 (`Gchi_growth`: |Gchi(y)| ≤ C y²), is holomorphic on Re s > 0 off the zero set Z, and at ρ ∈ Z has a simple pole of residue S·(−1/(ρ(ρ−1))), S = Σ_i (a_i/2)(ord_ρ L(χ_i) + ord_ρ L(χ_i⁻¹)) > 0, real and positive if ρ is real (0 < ρ < 1 by non-vanishing on Re s ≥ 1).
3. **[read]** Key inequality (`landau_window_key`), with T_k(s) = (−1)^k Φ^{(k)}(s)/k! = ∫ g(u) u^k e^{−su}/k! du (`landau_coeff`, `iteratedDeriv_laplace`):
   ```
   ∃ σ > 2, ∃ C, ∀ η > 0, ∀ U₀, ∃ U ≥ U₀, ∃ k : ℕ, U ≤ k ∧ ∀ γ : ℝ,
     ‖T_k(σ + γ i)‖ + Re T_k(σ) ≤ C * exp(η U) / (σ − θ)^k
   ```
   **[read]** By `landau_window_ineq` the left side is at most 2∫ max(g, 0)·u^k e^{−σu}/k!; on the window this is ≤ 2(σ−θ)^{−k}∫ R e^{−θu} (`landau_kernel_max`: u^k e^{−au}/k! ≤ a^{−k}); off it |g| ≤ C₀e^{2u}, and `landau_tails` bounds that mass by C/σ^k by exponential tilting, with l = 2 + 6/δ, σ = l(1+δ)(2+l), k = ⌈(1 + δ/2)σU⌉ (for λ = 3/2: σ = 336, k = ⌈420U⌉).
4. **[read]** `landau_dichotomy`: given ρ₀ ∈ Z with Re ρ₀ > θ, either (a) B(σ, D), D ≤ σ − θ, is pole-free while some pole has σ − Re ρ₁ < D, or (b) the nearest pole to σ is a real β > θ, alone in B(σ, r), σ − β < r ≤ σ − θ.
5. **[read]** In (b), `landau_pole_asym` (Cauchy estimate on Φ minus its principal part) gives Re T_k(σ) ≥ c/(σ−β)^{k+1} − M/e^k, c > 0, e = (σ − β + r)/2.
6. **[read]** In (a), `landau_nearest` picks γ near Im ρ₁, off finitely many equidistance values, so z = σ + iγ has a unique nearest pole at distance d < r ≤ D; then ‖T_k(z)‖ ≥ |c|/d^{k+1} − M/e^k, while ‖T_k(σ)‖ ≤ M′/e^k by `landau_cauchy`, e = (d + r)/2 < D.
7. **[read]** Either way c/d^{k+1} ≤ M″/e^k + C e^{ηU}/(σ−θ)^k with d < e ≤ σ − θ and k ≥ U; `landau_growth_contra` takes η = log(e/d)/2 and contradicts this; `lemmaL` covers Re s ≥ 1 by Mathlib.

*[inferred]* This joins Post–Widder (high derivatives of a Laplace transform at a real point see the function near u = k/σ) to Cauchy–Hadamard (Taylor coefficients grow at the rate of the nearest singularity). The dichotomy exposes a complex zero: Re T_k(σ) may be negative, so it is made positive by a real pole's residue or made negligible by moving to σ + iγ, nearer ρ than any pole is to σ.

### A.3 What windows and λ > 1 are for

*[inferred]* Only T_k with k → ∞ are used, each seeing g through a kernel centred near u ≈ (1 + δ/2)U, so one window per k, beyond every point, suffices. The off-window mass must fall below σ^{−k} although |g| may reach C₀e^{2u}; tilting achieves this only if the window's log-length δU is proportional to U, and then σ ≈ 36/δ², which blows up as δ → 0. Windows [Y, CY] would fail; any fixed λ > 1 works.

### A.4 Positivity and inputs

**[read]** The positivity used is a_i > 0 and −1/(ρ(ρ−1)) > 0 for 0 < ρ < 1 (last block of `poleData`); the coefficient positivity of A.1 is never invoked.
*[inferred]* One zero with Re ρ > θ therefore falsifies `WindowHyp` for some η > 0; with R = max(Gm, 0), ∫_Y^{Y^λ} Gm⁺(y) y^{−θ−1} dy > Y^η for all Y ≥ Y₀.
**[read]** The pointwise form of this, `LandauWinAt` (TGC/Window.lean:24), is defined and never used.
**[read]** Inputs: continuation of L, L(s, χ) ≠ 0 on Re s ≥ 1, L(1, χ) ≠ 0, ζ's residue and constant at 1 (Mathlib), conjugation symmetry (`LFunction_conj`, LT/LFunctionConj.lean:88), isolated zeros; no zero-free region, zero density or explicit formula.

Crossley gives a signed example of Alpöge’s criterion. Write $g(u)=G_F(e^u)$ for $u>0$ and extend it by zero. The difference $-g(u)+3g(u-\log 2)-2g(u-2\log 2)$ multiplies the Laplace transform by $(1-2^{-s})(2^{1-s}-1)$. This factor is nonzero in the open critical strip and positive on $(0,1)$, so a one-sided window bound on the difference still gives `ZeroFree F θ`. [Lean declaration](https://github.com/leecrossley/dirichlet-window-transfer/blob/fa94718cf9d65ee5b143ded4c91dc3873222cfdf/DelayedPole.lean#L176) and [archived proof](https://doi.org/10.5281/zenodo.24410863).

## B. The supply of hosts

### B.1 Wiring

**[read]** `zeroFreeAll_of_topG` calls `zeroFreeOn_of_tiedWin_cyc`, which needs, for Λ = Level.cyc ψ: `ChebyshevInequalityOnWindows Λ` (`level_gm_le_on_family_scales`, all levels), `Λ.FormB`, and `ChebyshevInequalityAtWindowScale (3/2) Λ` = `TopG la (GChi ψ) _ (supplyChi ψ (hV ψ)) (hypV_of_cls ψ la)`, with TopG from `Green` and `HypsAlt`.
**[read]** `GChi ψ` (CB/Supply.lean:42) asks at each host point for `EAtH (Level.cyc ψ) H TT x ε 4`, which includes |gChi χ x| ≤ x^{1/2+ε} and |L′/L(1, χ)| ≤ 4 log x for every bounded χ, and for `VVle H.E t (√b)`, the cohomological bound.
**[read]** `supplyChi : ∀ ψ, VWinAt ψ 401 → HostExW (3/2) (GChi ψ).req` is `supplyOfAdmOf hostOfField`, which builds `EAtH` directly from `fieldChi`, the shares and `boundedTw`.

### B.2 The auxiliary characters

**[read]** `boundedTw`: every bounded character is ξ·(·/q)^i·(·/d)^j with (i, j) ≠ (0, 0) and ξ mod ψ.N, bounded at x by `PairGood.bounds` at y = x.
**[read]** `PairGood M ε Y X q d` (CB/PairGood.lean:18): for all ξ mod M, (i, j) ≠ (0, 0), primitive χ inducing the twist and y ∈ [Y, X], ‖gChi χ y‖ ≤ y^{1/2+ε/2} and ‖L′/L(1, χ)‖ ≤ 4 log y; plus zero-free boxes for twists of real characters of conductor dividing 8M.
**[proved-by]** `QH.pairEx`: for all M, ε < 1/52, A ≥ 1 there is Y₁ such that every Y ≥ Y₁ has a pair with `PairGood M ε Y (Y^A) q d`.

**What is averaged.**
- **[read]** q runs over primes q ≤ e^z, q ≡ 3 (8), q > e^{z/2}, z = Y^{ε/5}, with twists ξ(·/q), ξ mod 8M (`stage1`); for a good q, d runs over primes in (e^{z′/2}, e^{z′}], d ≡ 7 (16), q·∏_{3≤p≤z} p | d + 1, z′ = Y^{ε/5} log² Y, with twists ξ(·/q)^a(·/d), a ∈ {0, 1} (`stage2`).
- **[read]** Good means `Box` (MSB/PrimeSetTwoBounds.lean:35): conductor ≤ Q, no zero with Re s > 1 − 1/400 and |Im s| ≤ Q (Q = 8M·e^z, resp. 8M·e^{z+z′}), |L′/L(1)| ≤ C log Y, and |G(y)| ≤ y^{1/2+τ} on all of [Y, Y^K].
- **[read]** Both stages are `stage`: for primes q ≤ U in a class mod m₀, q > √U, log U ∈ [Y^{ε/6}, Y^{ε/5} log² Y], and a fixed set Ξ of primitive characters of conductor ≤ F ≤ √U, at most η·|PPset| moduli have some ξ(·/q) outside the Box.
- **[read]** In its body the bad q lie in B₁ ∪ ⋃_ξ B₂(ξ): B₁ (a zero in the box) has ≤ C(FU)^{1/4} ≤ C·U^{3/8} elements (`count_bad`, from `ZeroDensityBox`) against |PPset| ≥ U^{9/10} (`count_a`); B₂(ξ) (|S| > y^{1/2+τ}/2 for some y) has ≤ η/(2(R+1))·|PPset| (`bad_share` from `meanSqK`); outside both, `box_of_S` gives the Box.
- **[read]** `pair_exists` runs `pair_share` with η = 1/2, so at least half the q are good and, for each, half its d; it takes any good q, then any good d.

**Why length, not conductor, matters.** **[read]** For z ≥ y, gChi χ y = −Σ_{n≤z} Λ(n)χ(n) min(1, y/n) − y·tail(z), tail(z) = −L′/L(1, χ) − Σ_{n≤z} Λ(n)χ(n)/n (`finite_splitting_of_group`, used in `box_of_S` with z = Y^{400K}).
**[read]** `tailK`: if χ has no zero in the box with Y^{ε/6} ≤ log Q ≤ Y^{ε/4}, then |Y^K·tail(Y^{400K})| ≤ Y^ε (via `BoxTail.tail_contour`); `kappaC` and `kappa4` bound |L′/L(1)| likewise.

**The mean square.** **[proved-by]** `meanSqK`: Σ_{q∈PPset} |S(Z, y, q, κ)|² ≤ C·y log y·|PPset| for y ∈ [Y, Y^K], |κ| ≤ 1, with S = Σ_{n≤Z} Λ(n) min(1, y/n) κ(n)(n/q) (MSB/PrimeSetTwoBounds.lean:13, 26).
**[read]** `meanSq_abs` expands the square; for q > Z² in a class mod m₀, |Σ_q (n/q)(n′/q)| = |Σ_q (q/s)|, s the odd squarefree part of nn′ prime to m₀ (`abs_pair_sum_eq`, statement only; *[inferred]* reciprocity). **[read]** s = 1 is the diagonal ≈ y log y; s = n*, one exceptional modulus, costs 2B² + 2B·RR with B ≈ C log y, since the weights live on prime powers; any other s ≤ Z² has |Σ_q (q/s)| ≤ Y^{−(K+1)}|PPset| by `twistK`.
**[read]** `twistK` uses `PNTAPRelW` (JCS/MeanSquareHypWIff.lean:38: PNT mod M with relative error and at most one exceptional real character, for log U ≥ C₀ log M log log M), proved from parts named `smoothed_explicit_formula`, `log_density_bound`, `deuring_heilbronn_lossy`; Landau–Page across moduli (`page_across`); and Siegel's bound (`excBound` ← `siegelLower`).
*[inferred]* This is not a large sieve but orthogonality of quadratic characters over prime moduli, available because the sums are short (Z² = Y^{800K}) and the progression moduli small against U.
**[read]** Uniformity in y (`bad_share`): on each dyadic block [W, 2W], |S(y)|² ≤ 2|S(W)|² + 2W∫|∂S|², Markov bounds the block's bad q by 32C/τ·W^{−τ}|P|, and the blocks sum geometrically.

**The zero density.** **[read]** `ZeroDensityBox` (JCS/CountSt.lean:7): at most C·Q^{1/4} primitive characters of conductor ≤ Q have a zero with Re s > 1 − 1/400 and |Im s| ≤ Q.
**[proved-by]** In the tree (`zero_density_box`), from a mollifier identity M(s)L(s) = 1 + Σ_{n>Y} c_n χ(n) n^{−s}, a duality inequality Σ_i |Σ_n b_n v_i(n)|² ≤ (Σ|b_n|²)·max_i Σ_j |⟨v_i, v_j⟩|, and |Σ_{n<M} χχ̄′(n)| ≤ NN′ for distinct primitive characters (JCS/CountZDefs.lean:24–78; statements read).
*[inferred]* That is Halász–Montgomery with crude constants; Q^{1/4} suffices against ≈ U/log U moduli.

### B.3 Windows, and why 3/2

**[read]** `VWinAt ψ Ct` (CB/ExistsPageN.lean:44): for each ε and each e(x) with x^{2+8ε} ≤ 2^{e(x)} ≤ 2x^{2+8ε} there are J ≥ 1 and X₀ such that, for X ≥ X₀ and every (q, d) with `WinPair ε (X^{1/J}) q d`, some W with X^{1/J} ≤ W, W² ≤ X has `VVle E ⌊x^Ct⌋ √(exp x^ε)` for all fields `IsChiField ψ (e x) q d E` and all x ∈ [W, W²].
**[read]** `winPairs` orders the choices: J from VWinAt; Y₁ from PairEx with A = J; X large and (q, d) from PairEx at Y = X^{1/J}, so the twist bounds hold on [X^{1/J}, X]; then W from VWinAt.
**[read]** It returns [kW, (kW)^{3/2}] with k = c^{1/(2+8ε)}, where `fieldChi` gives ord = c·2^e: for x = k·x′, x′ ∈ [W, W²], the field at level e(x′) has ord ∈ [x^{2+8ε}, 2x^{2+8ε}]; (kW)^{3/2} ≤ W² once k³ ≤ W; and ⌊x^{400}⌋ ≤ ⌊x′^{401}⌋ once k^{400} ≤ x′, hence 401 in VWin.
*[inferred]* So the windows are those of the cohomology bound (the Iwasawa step; third reading §7), and 3/2 is any exponent between 1 and 2 leaving room for k; the twist bounds cover [X^{1/J}, X] ⊇ [W, W²] and impose no window.

### B.4 Logical order

- **[read]** Assumed about ψ: only `VWinAt ψ 401`; `Green` and `HypsAlt` do not mention ψ.
- **[read]** Proved about ψ: L(s, ψ_j) ≠ 0 for Re s > 1/2 for every primitive ψ_j inducing a power of ψ (`level_of_tiedWin`, θ = 1/2 + min(Re s − 1/2, 1/2)/2).
- **[read]** Proved about the auxiliary characters of the chosen pair: no zero in a box near Re s = 1, |L′/L(1)| ≤ 4 log y, |G(y)| ≤ y^{1/2+ε/2} on [Y, Y^J]; nothing about their zeros near Re s = 1/2 is assumed or used.
- **[read]** The other inputs are unconditional in-tree theorems: `ZFRDirichlet`, `ExcBound`, `PNTAPRelW`, `ZeroDensityBox`, and `GzPNT` (through `psiChiBound`).
- **[read]** For y ≥ exp(x^{ε/3})/3 every character of the host, the ψ_j included, is bounded by `thinH` via `psi_thin` (an explicit formula with a zero-free region); real characters divisible by q or d are kept from Siegel zeros by the boxes, the rest (conductor dividing 8 times the odd part of QS) by `small_zeros`, where L(1, χ) ≠ 0 and continuity give an ineffective c₀.
- **[read]** No induction: `zeroFreeOn_of_tiedWin_cyc` is one statement for all ψ; the inductions present are technical (a minimum over moduli ≤ N₀ in `small_zeros`, subgroup closure in `KerChiAny`/`TwistAny`, derivative order in `IteratedDerivLaplace`).
- *[inferred]* An auxiliary character's own half-plane would follow by taking it as ψ, but nothing uses that, so there is no circle.

### B.5 Items the slice left open

- **[read]** `HostConditions` (TGC/Analytic.lean:163) feeds only `PreHostAn` (:170), `EAtH.explicit_formula_error_of_host_conditions` (TGC/ExplicitFormulaErrorOfHostConditions.lean:155) and `PreRows.eAtH` (`Development/AutomorphicArithmetic/CoprimeRanks/OfPInjective.lean:129`); a whole-tree grep finds no use of those three, so all are off the route.
- **[read]** `PrimePairOfBoxAndMeanSquareHypotheses` (`Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:183`) occurs only in the conjunction `zero_free_region_gl2_prime_choice_results` (`Formalism/GL3MeanSquares/ZeroFreeRegionGl2PrimeChoiceResults.lean:10`), which nothing references; `box_of_S` imports that file but names only `finite_splitting_of_group`.
- **[read]** `GzPNT` (`Formalism/ZeroFreeRegion/Statement.lean:16`: |Gz y| ≤ K·y·e^{−c√log y}) is on the route: `pnt_progressions_relative_weak_holds` → `psi_relative_near_range` → `psiChiBound` → `gzPNT`.
- **[read]** `trivStab` proves `TrivStab` (`Formalism/BehrendSets/StatementE.lean:89`): a finite g-subgroup of GL_k(E) is trivial when [E : ℚ]·k < g − 1; it serves torsion-freeness at the level prime (`CongruenceSubgroupTorsionFree.lean:298`), not the supply, despite its Behrend directory.

### B.6 Vacuous, discarded, degenerate

- **[read]** `supplyChi` discards φ.o = o and `KerChi ψ H0` (`fun s φ H0 hs hx hlo hhi _ _`); harmless, since `admissibleClassesTwistedChar` holds for every frame.
- **[read]** Dead near the path: `LandauWinAt`, `LandauWin` (TGC/Window.lean:24, 28); `famD`, `GmLevel`, `LandauZeroFreeCriterion` (`DedekindLFunctions/LandauZeroFreeCriterion.lean:33–61`); the classical all-large-x `zero_free_of_Chebyshev_growth` (TGC/Landau.lean:538), reached only from `zeroFreeOn_of_tiedAll`, which nothing uses.
- **[read]** `ChBalance`, `ChCore`, `ChTop` sit in `LT/` but belong to the count identity; the window proof does not import them.
- **[read]** The G-function is defined three times (`Deduction.Gchi`, `An.gChi`, `ZeroFreeRegionGL2.Gchi`), bridged by `gChi_eq` and `pairEx_g`.
- **[read]** Siegel–Walfisz, ineffective, enters only qualitatively: `psi0_bound` (MSB/GIntegral.lean:66) gives integrability of ψ₀(u)/u² for `g_integral`.
- *[inferred]* No degenerate instance: weights positive, windows non-empty, each PPset of size ≥ U^{9/10}, and η = 1/2 leaves a good pair.

## Chains

- **[read]** Landau: `formB` (`Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean:8`) → `level_family` (PrimitiveCosets/LevelFamily.lean:41) → `zeroFree_of_rpow_window` (LT/ZeroFreeOfRpowWindow.lean:11) → `windowHyp_of_rpow` (LT/WindowHypOfRpow.lean:27), `lemmaL` (LT/lemmaL.lean:13) → `poleData` (LT/poleData.lean:248), `windowHypU_of_windowHyp` (LT/WindowHypUOfWindowHyp.lean:29), `landau_window` (LT/landauWindow.lean:83) → `landau_window_key` (:40) → `landau_tails` (LT/landauTails.lean:80), `landau_window_ineq` (LT/landauWindowIneq.lean:27); `landau_dichotomy` (LT/LandauDichotomy.lean:24), `landau_nearest` (LT/LandauNearest.lean:36), `landau_pole_asym` (LT/LandauPoleAsym.lean:19), `landau_cauchy` (LT/LandauCauchy.lean:9), `landau_growth_contra` (LT/LandauGrowthContra.lean:9).
- **[read]** Top: `zero_free_all_of_green_v_win` (…/ThirdPlaceSeries/TopPlug.lean:12) → `zeroFreeAll_of_topG` (CB/ZeroFreeAllOfTopG.lean:26) → `zeroFreeOn_of_tiedWin_cyc` (TGC/TopWin.lean:90) → `level_of_tiedWin` (TGC/TopWin.lean:68).
- **[read]** Supply: `supplyChi` (CB/SupplyChi.lean:8) → `supplyOfAdm` (CB/HostOfField.lean:17) → `supplyOfAdmOf` (ShortNorms/supplyOfAdmOf.lean:13) → `fieldChi` (CB/FieldChi.lean:20), `winPairs` (CB/WinPairs.lean:5), `hostOfField` (CB/HostOfField.lean:8) → `hostOfFieldOf` (ShortNorms/hostOfFieldOf.lean:159) → `thinH` (MSB/GaussSumFunctionEq.lean:55) → `thin` (MSB/Thin.lean:10), `small_zeros` (MSB/SmallZeros.lean:32); `boundedTw` (CB/BoundedTw.lean:45); `admissibleClassesTwistedChar` (CoprimeRanks/AdmChi.lean:13).
- **[read]** Pairs: `pairEx` (MSB/pairEx.lean:112) → `pair_exists` (MSB/PairExists.lean:9) → `pair_share` (MSB/PairShare.lean:26) → `stage1` (MSB/Stage1Succ.lean:36), `stage2` (MSB/CharOf.lean:61) → `stage` (MSB/StagePow.lean:41) → `box_of_S` (MSB/BoxOfS.lean:28) [`tailK` MSB/TailKExp.lean:92, `kappaC` MSB/kappaC.lean:9]; `meanSqK` (MSB/meanSqK.lean:51) → `meanSq_abs` (MSB/MeanSqAbs.lean:8), `twistK` (MSB/twistK.lean:148) → `pnt_progressions_relative_weak_holds` (JCS/PNTFinal.lean:22) → `psi_relative_near_range` (JCS/PNTRangeA.lean:161) → `psiChiBound` (`Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:23`) → `gzPNT` (`Formalism/ZeroFreeRegion/LogDerivRegion.lean:20`); `page_across` (JCS/MSqPage.lean:37); `excBound` (SiegelWalfiszAPOfSiegelLower.lean:32) → `siegelLower` (`Formalism/LandauZeroFreeBounds/FinalSiegel.lean:17`); `bad_share` (MSB/BadShare.lean:251); `count_bad` (MSB/CountBad.lean:9) → `zero_density_box` (JCS/CountZAll.lean:13); `count_a` (JCS/MSqCount.lean:346).

## Not read

- **[read]** Bodies not read: `LFunction_conj`, `Gchi_growth`, the Mellin computations, `iteratedDeriv_laplace`; `tail_contour`, `kappa4`, `count_a`, `abs_pair_sum_eq`, `meansq_split`, `pairs_one`, `pairs_r`, `twist_one`; the parts of `zero_density_box`; the proofs of `PNTAPRelW`, `page_across`, `siegelLower`, `zFRDirichlet`, `gzPNT`, `psi_thin`; `realBox`, `topsChoiceH`, `thickFrame2`, `levelData`, `qdBig`, `pairRows`, `isChiField`, `exists_ranks_rankVal_frame`, most of `hostOfFieldOf`; `FamilyClassConnected` (inferred from use); the proofs of `TopG`, `level_gm_le_on_family_scales` and `VWin`.
