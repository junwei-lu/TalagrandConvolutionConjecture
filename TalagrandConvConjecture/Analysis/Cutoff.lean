import Mathlib

/-!
# A C¹ cutoff function and the coarea Cauchy–Schwarz bound

[C, proof of Lemma 4] uses a `C¹` cutoff `χ : ℝ → [0,1]` with `χ = 1` on
`[0,1]`, `supp χ ⊆ (-1,2)`, `|χ'| ≤ c'`. We build it from the cubic
smoothstep `s v = v²(3-2v)` and prove the FTC/Cauchy–Schwarz estimate for
`ψ(v) = e^{v/2} χ(v - ℓ)`:
`|ψ(b) - ψ(a)|² ≤ 4(½+c')² · |[a,b] ∩ (ℓ-1, ℓ+2)| · |e^b - e^a|`.
-/

namespace Talagrand

open MeasureTheory

/-- Cubic smoothstep on `[0,1]`. -/
def smoothstep (v : ℝ) : ℝ := v ^ 2 * (3 - 2 * v)

/-- The `C¹` cutoff: `0` on `(-∞,-1]`, rises to `1` on `[-1,0]`, `1` on
`[0,1]`, falls on `[1,2]`, `0` on `[2,∞)`. -/
noncomputable def cutoff (v : ℝ) : ℝ :=
  if v ≤ -1 then 0
  else if v ≤ 0 then smoothstep (v + 1)
  else if v ≤ 1 then 1
  else if v ≤ 2 then smoothstep (2 - v)
  else 0

/-- Derivative of the cutoff (defined piecewise; `0` at the outer plateaus). -/
noncomputable def cutoff' (v : ℝ) : ℝ :=
  if v ≤ -1 then 0
  else if v ≤ 0 then 6 * (v + 1) - 6 * (v + 1) ^ 2
  else if v ≤ 1 then 0
  else if v ≤ 2 then -(6 * (2 - v) - 6 * (2 - v) ^ 2)
  else 0

lemma cutoff_mem_Icc (v : ℝ) : cutoff v ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

lemma cutoff_eq_one {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : cutoff v = 1 := by
  sorry

lemma cutoff_eq_zero {v : ℝ} (h : v ≤ -1 ∨ 2 ≤ v) : cutoff v = 0 := by
  sorry

lemma hasDerivAt_cutoff (v : ℝ) : HasDerivAt cutoff (cutoff' v) v := by
  sorry

lemma abs_cutoff'_le (v : ℝ) : |cutoff' v| ≤ 3 / 2 := by
  sorry

lemma cutoff'_eq_zero_of_notMem {v : ℝ} (h : v ∉ Set.Ioo (-1 : ℝ) 2) :
    cutoff' v = 0 := by
  sorry

lemma continuous_cutoff : Continuous cutoff := by
  sorry

/-- The localized square-root test `ψ_ℓ(v) = e^{v/2}·χ(v-ℓ)`; note
`ψ_ℓ(log h) = √h·χ(log h - ℓ)`. -/
noncomputable def sqrtTest (ℓ v : ℝ) : ℝ := Real.exp (v / 2) * cutoff (v - ℓ)

lemma hasDerivAt_sqrtTest (ℓ v : ℝ) :
    HasDerivAt (sqrtTest ℓ)
      (Real.exp (v / 2) * (cutoff (v - ℓ) / 2 + cutoff' (v - ℓ))) v := by
  sorry

/-- **Coarea Cauchy–Schwarz bound** [C, proof of the claim in Lemma 4]:
for all `a b : ℝ`,
`(ψ_ℓ(b) - ψ_ℓ(a))² ≤ 16·(volume of [a,b]_* ∩ (ℓ-1,ℓ+2))·|e^b - e^a|`,
where `[a,b]_*` is the unordered interval. (Constant `16 ≥ 4(½+3/2)²`.) -/
theorem sqrtTest_sq_diff_le (ℓ a b : ℝ) :
    (sqrtTest ℓ b - sqrtTest ℓ a) ^ 2
      ≤ 16 * (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal
          * |Real.exp b - Real.exp a| := by
  sorry

end Talagrand
