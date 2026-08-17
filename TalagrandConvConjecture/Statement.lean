import TalagrandConvConjecture.Cube.Heat

/-!
# Talagrand's convolution conjecture: the statement

[LGF Theorem 1.1] (= Talagrand 1989, Problem 2; Talagrand 2016, Conjecture 6).
Let `G = {-1,1}^n` with uniform probability measure `λ`, and let
`μ_a = ((1+a)δ_1/2 + (1-a)δ_{-1}/2)^{⊗n}` for `0 < a < 1`. For
`T_{μ_a} f(x) = ∑_y μ_a({y}) f(x⊙y)` and
`ψ_{μ_a}(u) = sup { u·λ(T_{μ_a} f ≥ u) : f ≥ 0, ‖f‖_{L¹(λ)} = 1 }`,
there is a universal constant `C` with, for every `0 < a < 1`, `u > 1`, `n`:

`ψ_{μ_a}(u) ≤ C · κ_a² (log κ_a/(κ_a-1))^{1/2} / √(log u)`, `κ_a = (1+a)/(1-a)`.

Everything in this file is elementary and self-contained (finite sums over the
cube), so the faithfulness of the headline statement can be audited from this
file plus `Cube/Basic.lean` and the definition `biasedWeight` alone.

The paper states the bound for `n ≥ 1`; we quantify over all `n : ℕ` (the case
`n = 0` is trivially true), which is formally stronger.
-/

namespace Talagrand

variable {n : ℕ}

/-- `κ_a = (1+a)/(1-a)` [LGF Theorem 1.1]. -/
noncomputable def kappa (a : ℝ) : ℝ := (1 + a) / (1 - a)

/-- The constant `K_a = κ_a² (log κ_a/(κ_a-1))^{1/2}` of [LGF Theorem 1.1]. -/
noncomputable def Ka (a : ℝ) : ℝ :=
  kappa a ^ 2 * Real.sqrt (Real.log (kappa a) / (kappa a - 1))

/-- Convolution by the biased product measure:
`T_{μ_a} f(x) = ∑_y μ_a({y}) f(x⊙y)` [LGF §1]. -/
noncomputable def biasedConv (a : ℝ) (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, biasedWeight a y * f (x * y)

/-- Talagrand's weak-`L¹` functional
`ψ_{μ_a}(u) = sup{ u·λ(T_{μ_a}f ≥ u) : f ≥ 0, 𝔼_λ f = 1 }` [LGF §1]. -/
noncomputable def psi (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ⨆ f : {f : Cube n → ℝ // (∀ x, 0 ≤ f x) ∧ unifE f = 1},
    u * unifMeas {x | u ≤ biasedConv a f.1 x}

/-! The headline theorems `talagrand_convolution_conjecture` (pointwise form)
and `talagrand_convolution_conjecture_psi` (`ψ`-form) are stated and proved
in `Main.lean`, using only the definitions of this file in their statements.

### Basic facts making the statement well-posed -/

lemma one_lt_kappa {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 1 < kappa a := by
  rw [kappa, lt_div_iff₀ (by linarith)]
  linarith

lemma Ka_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < Ka a := by
  have hκ : 1 < kappa a := one_lt_kappa ha0 ha1
  have hlog : 0 < Real.log (kappa a) := Real.log_pos hκ
  have hden : 0 < kappa a - 1 := by linarith
  have hs : 0 < Real.sqrt (Real.log (kappa a) / (kappa a - 1)) :=
    Real.sqrt_pos.mpr (div_pos hlog hden)
  have hk : 0 < kappa a := by linarith
  simpa only [Ka] using mul_pos (pow_pos hk 2) hs

/-- `K_a ≥ 1` (from `(κ-1)/κ ≤ log κ ≤ κ-1`); [LGF, proof of Prop 3.2]. -/
lemma one_le_Ka {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 1 ≤ Ka a := by
  have hκ : 1 < kappa a := one_lt_kappa ha0 ha1
  have hk0 : (0 : ℝ) < kappa a := by linarith
  have hden : (0 : ℝ) < kappa a - 1 := by linarith
  -- `log κ ≥ 1 - κ⁻¹`, hence `log κ/(κ-1) ≥ κ⁻¹`
  have hlb : 1 - (kappa a)⁻¹ ≤ Real.log (kappa a) :=
    Real.one_sub_inv_le_log_of_pos hk0
  have hkk : (kappa a)⁻¹ * kappa a = 1 := inv_mul_cancel₀ (ne_of_gt hk0)
  have hq : (kappa a)⁻¹ ≤ Real.log (kappa a) / (kappa a - 1) := by
    rw [le_div_iff₀ hden]
    nlinarith [hlb, hkk, inv_pos.mpr hk0]
  have hqnn : 0 ≤ Real.log (kappa a) / (kappa a - 1) :=
    le_trans (le_of_lt (inv_pos.mpr hk0)) hq
  have hs2 : Real.sqrt (Real.log (kappa a) / (kappa a - 1)) ^ 2
      = Real.log (kappa a) / (kappa a - 1) := Real.sq_sqrt hqnn
  have hs0 : 0 ≤ Real.sqrt (Real.log (kappa a) / (kappa a - 1)) := Real.sqrt_nonneg _
  have hKa0 : 0 ≤ Ka a := le_of_lt (Ka_pos ha0 ha1)
  have hKa2 : 1 ≤ Ka a ^ 2 := by
    have hexp : Ka a ^ 2
        = kappa a ^ 4 * Real.sqrt (Real.log (kappa a) / (kappa a - 1)) ^ 2 := by
      simp only [Ka]; ring
    rw [hexp, hs2]
    have hlow : kappa a ^ 4 * (kappa a)⁻¹ ≤ kappa a ^ 4 *
        (Real.log (kappa a) / (kappa a - 1)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    have hcube : kappa a ^ 4 * (kappa a)⁻¹ = kappa a ^ 3 := by
      field_simp
    have h3 : (1 : ℝ) ≤ kappa a ^ 3 := by nlinarith [hκ, sq_nonneg (kappa a - 1)]
    have hlow' : kappa a ^ 3
        ≤ kappa a ^ 4 * (Real.log (kappa a) / (kappa a - 1)) := by
      rw [← hcube]; exact hlow
    linarith [h3, hlow']
  nlinarith [hKa2, hKa0]

/-- The supremum defining `ψ` is over a bounded family: Markov's inequality
gives `u·λ(T_{μ_a}f ≥ u) ≤ 1` for admissible `f`. -/
lemma bddAbove_psi_family {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {u : ℝ}
    (hu : 0 < u) :
    ∀ f : {f : Cube n → ℝ // (∀ x, 0 ≤ f x) ∧ unifE f = 1},
      u * unifMeas {x | u ≤ biasedConv a f.1 x} ≤ 1 := by
  intro f
  obtain ⟨hf0, hf1⟩ := f.2
  have ha : |a| ≤ 1 := by rw [abs_of_pos ha0]; linarith
  have hconv : biasedConv a f.1 = smooth a f.1 := by
    funext x
    rw [smooth_eq_conv]
    rfl
  have hnn : ∀ x, 0 ≤ biasedConv a f.1 x := by
    intro x
    rw [hconv]
    exact smooth_nonneg ha hf0 x
  have hE : unifE (biasedConv a f.1) = 1 := by
    rw [hconv, unifE_smooth, hf1]
  calc u * unifMeas {x | u ≤ biasedConv a f.1 x} ≤ unifE (biasedConv a f.1) :=
        mul_unifMeas_le_unifE hnn hu
    _ = 1 := hE

end Talagrand
