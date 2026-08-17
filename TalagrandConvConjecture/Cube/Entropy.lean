import TalagrandConvConjecture.Cube.Basic

/-!
# Entropy on finite probability spaces and tensorization on the cube

`ent w g = ∑ w i·g i·log(g i) - (∑ w i·g i)·log(∑ w i·g i)` for nonnegative
`g` and probability weights `w` on a finite index type (with the convention
`0·log 0 = 0`, which is automatic since `Real.log 0 = 0`).

Contents (needed for [C Lemma 4], the time-smoothed profile bound):
* the variational lower bound `∑ w g φ ≤ ent w g` whenever `∑ w e^φ ≤ 1`
  [C eq (entropy variational form)];
* the exact chain identity `ent_{μ⊗ν} h = 𝔼_μ[ent_ν h] + ent_μ(𝔼_ν h)`;
* "entropy of an average ≤ average of entropies" (from the variational sup
  representation);
* subadditivity/tensorization over the cube:
  `entUnif h ≤ ∑_i 𝔼_λ[pairEnt i h]` where `pairEnt i h x` is the entropy of
  `h` restricted to the two-point pair `{x, σ_i x}` with uniform weights.
-/

namespace Talagrand

variable {ι : Type*} [Fintype ι]

/-- Entropy functional `Ent_w(g)` on a finite space with weights `w`. -/
noncomputable def ent (w g : ι → ℝ) : ℝ :=
  ∑ i, w i * (g i * Real.log (g i)) -
    (∑ i, w i * g i) * Real.log (∑ i, w i * g i)

/-- Pointwise Young inequality `g·φ ≤ g·log g - g + e^φ` for `g ≥ 0`. -/
lemma mul_le_mul_log_sub_add_exp {g φ : ℝ} (hg : 0 ≤ g) :
    g * φ ≤ g * Real.log g - g + Real.exp φ := by
  sorry

/-- **Variational lower bound for entropy**: if `w` are probability weights,
`g ≥ 0`, and `∑ w e^φ ≤ 1`, then `∑ w·g·φ ≤ Ent_w(g)`. [C, proof of Lemma 4,
step (entropy_vs_anti_concentration_profile).] -/
theorem sum_mul_le_ent (w g φ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hg : ∀ i, 0 ≤ g i) (hφ : ∑ i, w i * Real.exp (φ i) ≤ 1) :
    ∑ i, w i * (g i * φ i) ≤ ent w g := by
  sorry

/-- Entropy is nonnegative for probability weights and nonnegative `g`. -/
lemma ent_nonneg (w g : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hg : ∀ i, 0 ≤ g i) : 0 ≤ ent w g := by
  sorry

/-- Entropy of an average is at most the average of entropies: for probability
weights `p` on `κ` and `w` on `ι`, and `h : κ → ι → ℝ` nonnegative,
`Ent_w(∑_k p k • h k) ≤ ∑_k p k · Ent_w(h k)`. (From the sup representation:
`Ent_w` is a supremum of linear functionals.) -/
theorem ent_average_le {κ : Type*} [Fintype κ] (p : κ → ℝ) (w : ι → ℝ)
    (h : κ → ι → ℝ) (hp : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hh : ∀ k i, 0 ≤ h k i) :
    ent w (fun i => ∑ k, p k * h k i) ≤ ∑ k, p k * ent w (h k) := by
  sorry

variable {n : ℕ}

/-- Entropy of `h` under the uniform measure on the cube. -/
noncomputable def entUnif (h : Cube n → ℝ) : ℝ :=
  unifE (fun x => h x * Real.log (h x)) - unifE h * Real.log (unifE h)

/-- Two-point entropy of `h` along the `i`-th edge at `x`: entropy of the pair
`(h x, h (σ_i x))` under uniform weights `(1/2, 1/2)`. Symmetric in
`x ↔ σ_i x`. -/
noncomputable def pairEnt (i : Fin n) (h : Cube n → ℝ) (x : Cube n) : ℝ :=
  (h x * Real.log (h x) + h (flipCoord i x) * Real.log (h (flipCoord i x))) / 2
    - (h x + h (flipCoord i x)) / 2 * Real.log ((h x + h (flipCoord i x)) / 2)

/-- **Tensorization (subadditivity) of entropy over the cube**:
`Ent_λ(h) ≤ ∑_i 𝔼_λ[pairEnt i h]`. Standard chain-rule induction on `n` using
`ent_average_le`. -/
theorem entUnif_le_sum_pairEnt {h : Cube n → ℝ} (hh : ∀ x, 0 ≤ h x) :
    entUnif h ≤ ∑ i, unifE (fun x => pairEnt i h x) := by
  sorry

end Talagrand
