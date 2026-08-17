import TalagrandConvConjecture.Lemmas.ScoreEnergy
import TalagrandConvConjecture.Lemmas.Discrepancy
import TalagrandConvConjecture.Lemmas.BandContraction

/-!
# The fixed-band anti-concentration estimate [LGF Proposition 3.2]

`𝔄_{t_a}((ℓ, ℓ+1]) ≲ K_a/√ℓ` for every `ℓ > 0`.

Proof [LGF §3.1], three steps for `ℓ ≥ C·K_a²`:
1. *Active discrepancy*: decompose `ℰ_θ` into gap layers `E_r(θ)`
   (`r ≤ R_θ < r+1`), bound each `D_{E_r}` via [LGF Lemma 3.3] +
   [LGF Lemma 3.5], average over `θ ∈ [T_o-1, T_o]` using the windowed
   profile bound [C Lemma 4]: `∫ D_{ℰ_θ} dθ ≲ K_a/√ℓ` — realized here as a
   pointwise-in-`θ` bound by an explicit measurable majorant with small
   integral.
2. *Inactive starting points*: `Ā_θ(ℓ) = ℙ(ℰ_θᶜ, F_{T_o}(V_{T_o}) ∈ band)`;
   near layers via the profile bound, far layers via the `e^{-F}`-martingale
   Chebyshev estimate `ℙ(F_{T_o}(V_{T_o}) ≤ ℓ+1 | V_θ = x₀) ≤ e^{ℓ+1-F_θ(x₀)}`.
3. *Closing the recurrence*: combine with [LGF Lemma 3.4]; pick a good `θ` by
   the mean-value principle; run the geometric-band bootstrap
   (`ϱ* = c₀/((1-c₀)(e-1)) < 1`) on `𝓜_ℓ = sup_{r≥ℓ} √r·𝔄_{t_a}((r,r+1])`.
For `ℓ < C·K_a²` the trivial bound `𝔄 ≤ 1 ≤ K_a√C/√ℓ` applies.
-/

namespace Talagrand

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- Coupling-flow families exist for every admissible `(ℓ, θ)`. -/
theorem exists_cflowFamily (ℓ : ℝ) (hℓ : 0 < ℓ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) : Nonempty (D.CFlowFamily ℓ θ) := by
  sorry

/-- **Reciprocal-martingale tail bound** [LGF, Step 2 of Prop 3.2]: for any
coupling flow from `x₀`,
`𝔼_{x₀}[1_{F_{T_o}(V_{T_o}) ≤ c}] ≤ e^{c - F_θ(x₀)}` for every `c`. -/
theorem term_V_tail_le {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (cLev : ℝ) :
    ∑ s : JSt n, c.term s * (if D.F obsT s.1 ≤ cLev then (1 : ℝ) else 0)
      ≤ Real.exp (cLev - D.F θ x₀) := by
  sorry

open Classical in
/-- The `V`-terminal band mass over all starting points is the profile:
`∑_{x₀} ν_{T-θ}(x₀)·𝔼_{x₀}[1_{F_{T_o}(V) ∈ I}] = 𝔄_{t_a}(I)`
[LGF eq (3.14), `V_{T_o} ∼ ν_{t_a}`]. -/
theorem sum_term_V_eq_profile {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (I : Set ℝ) :
    ∑ x₀ : Cube n, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
        (if D.F obsT s.1 ∈ I then (1 : ℝ) else 0)
      = profile D.f D.tA I := by
  sorry

/-- Vanishing of high bands: `𝔄_{t_a}((r,r+1]) = 0` once `r` exceeds
`max_x log f_{t_a}(x)`. -/
theorem exists_profile_vanish :
    ∃ B : ℝ, ∀ r : ℝ, B ≤ r → profile D.f D.tA (Set.Ioc r (r + 1)) = 0 := by
  sorry

end Dat

/-- **Fixed-band anti-concentration** [LGF Proposition 3.2]: there is a
universal `C` with `𝔄_{t_a}((ℓ,ℓ+1]) ≤ C·K_a/√ℓ` for all data and `ℓ > 0`. -/
theorem fixed_band :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (D : Dat n) (ℓ : ℝ), 0 < ℓ →
      profile D.f D.tA (Set.Ioc ℓ (ℓ + 1))
        ≤ C * Ka D.a / Real.sqrt ℓ := by
  sorry

end Talagrand
