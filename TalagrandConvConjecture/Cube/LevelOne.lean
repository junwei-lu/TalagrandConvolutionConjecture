import TalagrandConvConjecture.Cube.Multilinear

/-!
# The biased level-one (Parseval/Bessel) inequality

[C Lemma 7] (= [LGF eq (4.15)], O'Donnell Ch. 8): for `φ : Cube n → {0,1}` and
`z ∈ [-1,1]^n`,
`∑_i (1 - z_i²)·(∂_i φ(z))² ≤ φ(z) - φ(z)² ≤ 1/4`,
where `φ(z)` denotes the multilinear extension `mext φ z` and
`∂_i φ = dmext φ i`.

Proof route (no inner-product-space typeclasses; direct Bessel): under the
product measure `π_z` with coordinate means `z`, the functions
`χ_i(y) = y_i - z_i` are orthogonal with `𝔼 χ_i² = 1 - z_i²` and
`𝔼[φ χ_i] = (1-z_i²)·∂_iφ(z)`; expanding
`𝔼[(φ - 𝔼φ - ∑_{i ∈ s} c_i χ_i)²] ≥ 0` with the optimal `c_i` over the set `s`
of coordinates with `|z_i| < 1` yields the claim (coordinates with `|z_i| = 1`
contribute `0` on the left).
-/

namespace Talagrand

variable {n : ℕ}

/-- Biased expectation of the product of a function with the centered `i`-th
coordinate: `𝔼_{π_z}[g(y)(y_i - z_i)] = (1-z_i²)·∂_i g(z)`. -/
lemma sum_cubeKernel_mul_centered (g : Cube n → ℝ) (z : Fin n → ℝ) (i : Fin n) :
    ∑ y, cubeKernel z y * (g y * (toR (y i) - z i))
      = (1 - z i ^ 2) * dmext g i z := by
  sorry

/-- Orthogonality of centered coordinates under the biased product measure:
for `i ≠ j`, `𝔼_{π_z}[(y_i - z_i)(y_j - z_j)] = 0`. -/
lemma sum_cubeKernel_centered_mul_centered {i j : Fin n} (z : Fin n → ℝ)
    (hij : i ≠ j) :
    ∑ y, cubeKernel z y * ((toR (y i) - z i) * (toR (y j) - z j)) = 0 := by
  sorry

/-- Second moment of a centered coordinate: `𝔼_{π_z}[(y_i - z_i)²] = 1 - z_i²`. -/
lemma sum_cubeKernel_centered_sq (z : Fin n → ℝ) (i : Fin n) :
    ∑ y, cubeKernel z y * (toR (y i) - z i) ^ 2 = 1 - z i ^ 2 := by
  sorry

/-- **Level-one inequality** [C Lemma 7]: for a `{0,1}`-valued `φ` and
`z ∈ [-1,1]^n`,
`∑_i (1-z_i²)(∂_iφ(z))² ≤ mext φ z - (mext φ z)²`. -/
theorem level_one {φ : Cube n → ℝ} (hφ : ∀ x, φ x = 0 ∨ φ x = 1)
    {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1) :
    ∑ i, (1 - z i ^ 2) * dmext φ i z ^ 2 ≤ mext φ z - mext φ z ^ 2 := by
  sorry

/-- The elementary bound `t - t² ≤ 1/4`. -/
lemma self_sub_sq_le_quarter (t : ℝ) : t - t ^ 2 ≤ 1 / 4 := by
  nlinarith [sq_nonneg (t - 1 / 2)]

end Talagrand
