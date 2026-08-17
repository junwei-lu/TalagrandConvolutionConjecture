import TalagrandConvConjecture.Lemmas.Quantities

/-!
# Stopped score energy [LGF Lemma 3.5]

Per starting point: `𝔼_{x₀}[∫_θ^τ ∑_i S_i² dt] ≤ (κ-1)/log κ·(R_θ+1+log κ)`;
consequently, for `A ⊆ ℰ_θ`,
`𝒮_A ≤ 25·∑_{x₀∈A} ν_{T-θ}(x₀)·(κ/(Λ(R+1)) + (κ-1)/(R+1)²)`
[LGF eq (3.4)-(3.5), with the explicit constant `α² = 25`].

De-probabilized proof (replacing the optional-stopping argument of
[LGF §4.4]): pair the flow against the sector test `G_t(x,y,alive) = F_t(x)`,
`G_t(·,·,dead) = ℓ+1+log κ`. Along cells,
`d/dt⟨π_t, G_t⟩ ≥ ⟨π_t^{alive}, ½∑_i(Y_i log Y_i + 1 - Y_i)⟩`
(the killed flux lands at `F`-values `≤ ℓ+1+log κ` by the edge bound, and
node transfers only increase the pairing); integrating and using the score
convexity `½(Y log Y - Y + 1) ≥ (log κ/(κ-1))·S²` [C eq (40)] gives the
bound.
-/

namespace Talagrand

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- **Per-start stopped score energy bound** [LGF Lemma 3.5, first part]:
for `θ ∈ [T_o - 1, T_o]` and any coupling flow from `x₀`,
`scoreEnergy ≤ (κ-1)/log κ·(R_θ(x₀)+1+log κ)`. -/
theorem scoreEnergy_le {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : obsT - 1 ≤ θ)
    (hθ : θ ≤ obsT) {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) :
    D.scoreEnergy c
      ≤ (kappa D.a - 1) / Real.log (kappa D.a)
        * (D.Rgap ℓ θ x₀ + 1 + Real.log (kappa D.a)) := by
  sorry

/-- **Stopped score energy, localized form** [LGF eq (3.5)] with explicit
constant `α² = 25`: for `A ⊆ ℰ_θ`,
`𝒮_A ≤ 25·∑_{x₀∈A} ν_{T-θ}(x₀)(κ_a/(Λ_a(R_θ+1)) + (κ_a-1)/(R_θ+1)²)`. -/
theorem SA_le {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : obsT - 1 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) {A : Finset (Cube n)} (hA : A ⊆ D.activeF ℓ θ) :
    D.SA Φ A
      ≤ 25 * ∑ x₀ ∈ A, D.startW θ x₀ *
          (kappa D.a / (Lam D.a * (D.Rgap ℓ θ x₀ + 1))
            + (kappa D.a - 1) / (D.Rgap ℓ θ x₀ + 1) ^ 2) := by
  sorry

/-- Nonnegativity of the score energy. -/
lemma scoreEnergy_nonneg {ℓ θ : ℝ} (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) : 0 ≤ D.scoreEnergy c := by
  sorry

lemma SA_nonneg {ℓ θ : ℝ} (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) : 0 ≤ D.SA Φ A := by
  sorry

end Dat

end Talagrand
