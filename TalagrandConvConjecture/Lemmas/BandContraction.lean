import TalagrandConvConjecture.Lemmas.Supermartingale

/-!
# Band contraction [LGF Lemma 3.4]

With `c₀ = e^{1-α} = e^{-4}` and `A_θ(r) = ℙ(ℰ_θ, F_{T_o}(V_{T_o}) ∈ (r,r+1])`:

`(1-c₀)·A_θ(ℓ) ≤ c₀·∑_{j≥1} e^{-j}·A_θ(ℓ+j) + 2·D_{ℰ_θ}`.

Proof [LGF §4.3]: the weighted crossing estimate
`ℙ(ℰ, W ∈ band(ℓ+j), F(V) ≤ ℓ+1) ≤ c₀e^{-j}A_θ(ℓ+j)` (from the terminal
weighted comparison and `N_{T_o} ≥ e^{α+j-1}` on the crossing event), the
zeroth-band bookkeeping through `B_θ(ℓ)`, and two applications of the
`D_{ℰ_θ}` test bound.
-/

namespace Talagrand

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- Weighted band-crossing estimate [LGF eq (4.16)]: for every `j : ℕ`,
`ℙ(ℰ_θ, F_{T_o}(W) ∈ (ℓ+j, ℓ+j+1], F_{T_o}(V) ≤ ℓ+1)
  ≤ e^{1-α}·e^{-j}·A_θ(ℓ+j)`. -/
theorem band_crossing_le {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (j : ℕ) :
    ∑ x₀ ∈ D.activeF ℓ θ, D.startW θ x₀ *
        ∑ s : JSt n, (Φ x₀).term s *
          (if D.F obsT s.2.1 ∈ Set.Ioc (ℓ + j) (ℓ + j + 1)
              ∧ D.F obsT s.1 ≤ ℓ + 1 then (1 : ℝ) else 0)
      ≤ Real.exp (1 - alphaC) * Real.exp (-(j : ℝ))
          * D.Aband Φ (D.activeF ℓ θ) (ℓ + j) := by
  sorry

/-- **Band contraction** [LGF Lemma 3.4]: with `c₀ = e^{1-α}`,
`(1-c₀)·A_θ(ℓ) ≤ c₀·∑_{j≥1} e^{-j}A_θ(ℓ+j) + 2·D_{ℰ_θ}`. The series is
summable since `A_θ ≤ 1` (see `Aband_summable`). -/
theorem band_contraction {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) :
    (1 - Real.exp (1 - alphaC)) * D.Aband Φ (D.activeF ℓ θ) ℓ
      ≤ Real.exp (1 - alphaC) *
          (∑' j : ℕ, Real.exp (-((j : ℝ) + 1))
            * D.Aband Φ (D.activeF ℓ θ) (ℓ + j + 1))
        + 2 * D.DA Φ (D.activeF ℓ θ) := by
  sorry

/-- Summability input for the band series (bands are bounded by `1` and the
weights are geometric). -/
theorem Aband_summable {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) :
    Summable (fun j : ℕ => Real.exp (-((j : ℝ) + 1))
      * D.Aband Φ A (ℓ + j + 1)) := by
  sorry

end Dat

end Talagrand
