import TalagrandConvConjecture.Cube.Entropy

/-!
# A log-Sobolev inequality on the Boolean hypercube

Goal: `Ent_λ(h) ≤ 𝔼_λ ∑_i (√(h(σ_i x)) - √(h x))²` for `h ≥ 0`, i.e.
`Ent(h) ≤ 4·𝔈(√h, √h)` with the Dirichlet form
`𝔈(g,g) = ¼ 𝔼 ∑_i (Δ_i g)²`.

[C, proof of Lemma 4] uses the optimal constant `2` (Gross); any universal
constant suffices for [LGF], and constant `4` admits the following elementary
proof, which is the deviation we take:
* two-point inequality: for `α, β ≥ 0`,
  `½(α² log α² + β² log β²) - m log m ≤ (α-β)²` with `m = (α²+β²)/2`;
  proved via the normalized 1-D inequality
  `(1+u)log(1+u) + (1-u)log(1-u) ≤ 2u²` on `[0,1]` and `1-√(1-u²) ≥ u²/2`;
* tensorization (`entUnif_le_sum_pairEnt` from `Cube/Entropy.lean`).
-/

namespace Talagrand

/-- 1-D inequality: `(1+u)·log(1+u) + (1-u)·log(1-u) ≤ 2u²` for `u ∈ [0,1]`
(at `u = 1` with the convention `0·log 0 = 0`). Convexity on `[0,1/√2]` with
double root at `0`, then concavity + endpoint checks. -/
lemma one_add_mul_log_add_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u) ≤ 2 * u ^ 2 := by
  sorry

/-- `1 - √(1-v) ≥ v/2` for `v ∈ [0,1]`. -/
lemma half_le_one_sub_sqrt_one_sub {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    v / 2 ≤ 1 - Real.sqrt (1 - v) := by
  sorry

/-- **Two-point log-Sobolev inequality** (with constant `1` in this
normalization): for `α, β ≥ 0`,
`(α²·log α² + β²·log β²)/2 - (α²+β²)/2 · log((α²+β²)/2) ≤ (α - β)²`. -/
theorem two_point_LSI {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (α ^ 2 * Real.log (α ^ 2) + β ^ 2 * Real.log (β ^ 2)) / 2
        - (α ^ 2 + β ^ 2) / 2 * Real.log ((α ^ 2 + β ^ 2) / 2)
      ≤ (α - β) ^ 2 := by
  sorry

variable {n : ℕ}

/-- **Log-Sobolev inequality on the cube** (constant 4 vs Gross's 2; the
constant is irrelevant for [LGF]): for `h ≥ 0`,
`Ent_λ(h) ≤ 𝔼_λ ∑_i (√(h(σ_i x)) - √(h x))²  (= 4·𝔈(√h,√h))`.
Used in [C, proof of Lemma 4] via `Ent(h_s) ≲ 𝔈(√h_s, √h_s)`. -/
theorem cube_LSI {h : Cube n → ℝ} (hh : ∀ x, 0 ≤ h x) :
    entUnif h
      ≤ unifE (fun x => ∑ i,
          (Real.sqrt (h (flipCoord i x)) - Real.sqrt (h x)) ^ 2) := by
  sorry

end Talagrand
