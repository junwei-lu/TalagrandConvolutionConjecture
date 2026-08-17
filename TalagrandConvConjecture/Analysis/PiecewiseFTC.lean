import Mathlib

/-!
# Calculus across finitely many exceptional times; root finiteness

Two pieces of glue used throughout the de-probabilized proof:

1. **FTC with a finite exceptional set**: if `u` is continuous on `[a,b]` and
   differentiable with derivative `v` off a finite set, with `v` interval
   integrable, then `u b - u a = ∫_a^b v`; plus inequality versions. These
   turn the cell-wise ODE identities of the glued flows into endpoint
   identities/estimates.

2. **Finiteness of crossing times**: `t ↦ P_{s(t)} f(x)` is a polynomial in
   `e^{-t}`; hence for `c ≠` its constant term, `{t | value = c}` is finite.
   This makes the barrier `{F_t(x) ≥ ℓ+1}` piecewise constant in `t`
   ([LGF §3], stopping time `τ`), and similarly the level sets in
   [C Lemma 4]'s derivative computation.
-/

namespace Talagrand

open MeasureTheory intervalIntegral

/-- **FTC-2 with finitely many exceptional points**: `u` continuous on
`[a,b]`, `HasDerivAt u (v t) t` for `t ∈ (a,b) \ Z` with `Z` finite, and `v`
interval integrable, imply `u b - u a = ∫_a^b v`. -/
theorem sub_eq_integral_of_finite_exceptions {u v : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (Z : Finset ℝ) (hu : ContinuousOn u (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ Z → HasDerivAt u (v t) t)
    (hv : IntervalIntegrable v volume a b) :
    u b - u a = ∫ t in a..b, v t := by
  sorry

/-- Monotonicity with finitely many exceptional points: continuous on `[a,b]`,
derivative `≤ 0` off a finite set ⟹ `u b ≤ u a`. -/
theorem antitone_of_deriv_nonpos_finite_exceptions {u : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (Z : Finset ℝ) (hu : ContinuousOn u (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ Z →
      ∃ v ≤ (0 : ℝ), HasDerivAt u v t) :
    u b ≤ u a := by
  sorry

/-- Inequality FTC: continuous `u`, derivative bounded by `w` off a finite
set, `w` interval integrable ⟹ `u b - u a ≤ ∫ w`. -/
theorem sub_le_integral_of_finite_exceptions {u w : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (Z : Finset ℝ) (hu : ContinuousOn u (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ Z → ∃ v ≤ w t, HasDerivAt u v t)
    (hw : IntervalIntegrable w volume a b) :
    u b - u a ≤ ∫ t in a..b, w t := by
  sorry

/-- Roots of a nonzero polynomial evaluated along `t ↦ e^{-t}` form a finite
set. -/
theorem finite_setOf_poly_exp_eq {p : Polynomial ℝ} (hp : p ≠ 0) :
    {t : ℝ | p.eval (Real.exp (-t)) = 0}.Finite := by
  sorry

/-- A finite family of exponential-polynomial level conditions has finitely
many crossing times on `ℝ`: if each `g j t = ∑_k c j k · (e^{-t})^k` is a
polynomial in `e^{-t}` whose value `v j` differs from its limit
`c j 0 = g j (+∞)`, then `{t | ∃ j, g j t = v j}` is finite. Convenience
wrapper around `finite_setOf_poly_exp_eq`. -/
theorem finite_setOf_expPoly_family_eq {J : Type*} [Fintype J] {N : ℕ}
    (c : J → ℕ → ℝ) (v : J → ℝ) (hv : ∀ j, v j ≠ c j 0) :
    {t : ℝ | ∃ j, ∑ k ∈ Finset.range N, c j k * Real.exp (-t) ^ k = v j}.Finite := by
  sorry

end Talagrand
