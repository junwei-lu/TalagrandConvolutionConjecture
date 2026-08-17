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

/-- **Talagrand's convolution conjecture** [LGF Theorem 1.1], pointwise-in-`f`
form: there is a universal constant `C` such that for every dimension `n`,
bias `0 < a < 1`, level `u > 1`, and probability density `f` on the cube
(`f ≥ 0`, `𝔼_λ f = 1`),
`u·λ({T_{μ_a} f ≥ u}) ≤ C·K_a/√(log u)`. -/
theorem talagrand_convolution_conjecture :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (a u : ℝ) (f : Cube n → ℝ),
        0 < a → a < 1 → 1 < u → (∀ x, 0 ≤ f x) → unifE f = 1 →
        u * unifMeas {x | u ≤ biasedConv a f x}
          ≤ C * Ka a / Real.sqrt (Real.log u) := by
  sorry

/-- **Talagrand's convolution conjecture**, `ψ`-form [LGF eq (1.1)]:
`ψ_{μ_a}(u) ≤ C·K_a/√(log u)` for all `0 < a < 1`, `u > 1`, `n`. -/
theorem talagrand_convolution_conjecture_psi :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (a u : ℝ), 0 < a → a < 1 → 1 < u →
        psi a n u ≤ C * Ka a / Real.sqrt (Real.log u) := by
  sorry

/-! ### Basic facts making the statement well-posed -/

lemma one_lt_kappa {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 1 < kappa a := by
  rw [kappa, lt_div_iff₀ (by linarith)]
  linarith

lemma Ka_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < Ka a := by
  sorry

/-- `K_a ≥ 1` (from `(κ-1)/κ ≤ log κ ≤ κ-1`); [LGF, proof of Prop 3.2]. -/
lemma one_le_Ka {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 1 ≤ Ka a := by
  sorry

/-- The supremum defining `ψ` is over a bounded family: Markov's inequality
gives `u·λ(T_{μ_a}f ≥ u) ≤ 1` for admissible `f`. -/
lemma bddAbove_psi_family {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {u : ℝ}
    (hu : 0 < u) :
    ∀ f : {f : Cube n → ℝ // (∀ x, 0 ≤ f x) ∧ unifE f = 1},
      u * unifMeas {x | u ≤ biasedConv a f.1 x} ≤ 1 := by
  sorry

end Talagrand
