import TalagrandConvConjecture.FixedBand

/-!
# Talagrand's convolution conjecture [LGF Theorem 1.1]

From the fixed-band estimate [LGF Prop 3.2] to the weak-type bound: for
strictly positive `f`, the layer-cake/geometric-series argument of
[LGF, proof of Thm 1.1]; general `f ≥ 0` by the strictly positive
approximation `(f+ε)/(1+ε)`.
-/

namespace Talagrand

variable {n : ℕ}

/-- `T_{μ_a} = P_{t_a}`: the biased convolution is the heat flow at time
`t_a = -log a` [LGF §2.1]. -/
lemma biasedConv_eq_heatAt {a : ℝ} (ha : 0 < a) (f : Cube n → ℝ) :
    biasedConv a f = heatAt f (-Real.log a) := by
  sorry

/-- The strictly positive case of [LGF Theorem 1.1]: for `D : Dat n` and
`u > 1`, `u·λ(P_{t_a}f ≥ u) ≤ C·K_a/√(log u)`. -/
theorem main_of_pos :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (D : Dat n) (u : ℝ), 1 < u →
      u * unifMeas {x | u ≤ biasedConv D.a D.f x}
        ≤ C * Ka D.a / Real.sqrt (Real.log u) := by
  sorry

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

end Talagrand
