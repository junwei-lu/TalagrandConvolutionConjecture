# Task: close every `sorry` in Analysis/Cutoff.lean and Analysis/PiecewiseFTC.lean

Touch-set: TalagrandConvConjecture/Analysis/Cutoff.lean,
TalagrandConvConjecture/Analysis/PiecewiseFTC.lean. Do not change statements.
Read CLAUDE.md.

## Cutoff.lean hints

* `smoothstep v = v²(3-2v)`: on `[0,1]` it is in `[0,1]`, `s(0)=0, s(1)=1`,
  `s'(v) = 6v - 6v² = 6v(1-v)`, `s'(0) = s'(1) = 0`, `|s'| ≤ 3/2` on `[0,1]`.
* `hasDerivAt_cutoff`: piecewise; at interior points of each piece use
  `HasDerivAt.congr_of_eventuallyEq` with a neighborhood where `cutoff`
  agrees with the polynomial piece; at the four knots `-1, 0, 1, 2` the
  one-sided derivatives agree (both `0` at `-1, 2`; at `0` and `1`:
  `s'(1) = 0` matches the plateau), so use
  `HasDerivAt` via left/right filter decomposition
  (`hasDerivAt_of_hasDerivAt_left_right`-style; if no such lemma, prove via
  `HasDerivAt` unfolded to `HasDerivWithinAt (Iic) ∧ HasDerivWithinAt (Ici)`
  — `hasDerivAt_iff_hasDerivWithinAt_Iic_Ici`? search; fallback:
  `HasDerivAt.congr` on each side + `HasDerivWithinAt.union`
  with `Iic ∪ Ici = univ`).
* `abs_cutoff'_le`: case analysis + `nlinarith` on each polynomial branch.
* `sqrtTest_sq_diff_le`: WLOG `a ≤ b` (else swap; both sides symmetric).
  `ψ(b) - ψ(a) = ∫_a^b ψ'` (FTC-2, `intervalIntegral.integral_deriv_eq_sub'`
  or `integral_eq_sub_of_hasDerivAt` with `hasDerivAt_sqrtTest`).
  `|ψ'(v)| ≤ 2·e^{v/2}·1_{(ℓ-1,ℓ+2)}(v)` (since `χ/2 + χ'` is `≤ 2` in
  absolute value and vanishes off `(ℓ-1, ℓ+2)`). Then Cauchy–Schwarz for
  interval integrals:
  `(∫ 1_J·e^{v/2})² ≤ (∫ 1_J)·(∫_a^b e^v)` — use
  `MeasureTheory.integral_mul_le_Lp_mul_Lq` on the restricted measure with
  `p = q = 2`, or `inner_mul_le_norm_mul_norm` in `L²(volume.restrict (a,b))`,
  or the elementary route: `∫ 1_J e^{v/2} ≤ √(∫1_J)·√(∫e^v)` via
  `MeasureTheory.integral_mul_le_L2_norm...`; pick whatever exists in
  Mathlib. Note `∫_a^b e^v dv = e^b - e^a = |e^b - e^a|`.
  Constant slack is generous (`16 ≥ 4·2²`... check: `(2)² · (∫1_J)(e^b-e^a)`
  needs `≤ 16·|J∩[a,b]|·|e^b-e^a|`: 4 ≤ 16 fine).

## PiecewiseFTC.lean hints

* `sub_eq_integral_of_finite_exceptions`: induct on the finite exceptional
  set `Z` (or: sort `Z ∩ (a,b)` and split `[a,b]` at those points using
  `intervalIntegral.integral_add_adjacent_intervals`); on each subinterval
  apply `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`
  (continuity on closed + derivative on open + integrability).
* The `≤`-versions: same splitting; on each clean piece use
  `sub_le_integral` style: from FTC on auxiliary
  `t ↦ ∫_a^t w - u t` (monotone via nonneg derivative,
  `monotoneOn_of_hasDerivWithinAt_nonneg`-flavor lemmas in
  `Mathlib.Analysis.Calculus.MeanValue`, e.g.
  `StrictMonoOn`/`monotoneOn_of_deriv_nonneg`); mind that `w - v ≥ 0` only
  as an existential — extract with choice into a function first if needed.
  For `antitone_of_deriv_nonpos_finite_exceptions` no integrability is
  needed: use the mean-value monotonicity on each piece + continuity at the
  finitely many junctions.
* `finite_setOf_poly_exp_eq`: `{t | p.eval (exp (-t)) = 0}` is the preimage
  of `p.roots`-set under the injective map `t ↦ exp (-t)`
  (`Real.exp_injective... ` compose with neg; injectivity:
  `Real.exp_lt_exp` strict mono). A nonzero polynomial has finitely many
  roots: `p.setOf_isRoot_finite` (or via `p.roots.toFinset.finite_toSet` and
  `Polynomial.mem_roots`). Then `Set.Finite.preimage` with `Set.injOn_of_injective`.
* `finite_setOf_expPoly_family_eq`: finite union over `j` of sets of the
  previous form with `p_j := (∑ c j k·X^k) - C (v j)`; `p_j ≠ 0` because its
  constant coefficient is `c j 0 - v j ≠ 0` (`Polynomial.coeff_zero`... via
  `p.coeff 0 ≠ 0 → p ≠ 0`). Note `Real.exp (-t) ^ k = (e^{-t})^k` matches
  `Polynomial.eval` of `X^k`.

Gate: `lake build TalagrandConvConjecture.Analysis.Cutoff TalagrandConvConjecture.Analysis.PiecewiseFTC`,
zero sorry. Commit when green.
