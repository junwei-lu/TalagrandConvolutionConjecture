import TalagrandConvConjecture.Cube.Heat
import TalagrandConvConjecture.Cube.LogSobolev
import TalagrandConvConjecture.Analysis.Cutoff
import TalagrandConvConjecture.Analysis.PiecewiseFTC

/-!
# The anti-concentration profile and the time-smoothed bound [C Lemma 4]

For a strictly positive density `f` (`𝔼_λ f = 1`) let `f_s = P_s f` and
`𝔄_s(I) = 𝔼_λ[f_s · 1_{log f_s ∈ I}]` (the size-biased logarithmic profile,
[LGF §2.1], [C eq (def_anti_concentration_profile)]).

Main result (`profile_time_integral_le`): there is a universal `C` with
`∫_0^∞ 𝔄_s((ℓ, ℓ+1]) ds ≤ C/ℓ` for every `ℓ > 2` [C Lemma 4].

Proof skeleton [C §3.5]:
* localized test `h_s = f_s·χ(log f_s - ℓ)²`;
* `ℓ·𝔄_s ≤ 2·Ent_λ(h_s)` (entropy variational bound with the explicit
  `φ = ℓ·1_E - log(1+(e^ℓ-1)λ(E))`);
* `Ent_λ(h_s) ≤ 4𝔈(√h_s,√h_s)` (cube LSI, our constant 4);
* discrete coarea: `𝔈(√h_s,√h_s) ≲ ∫_{ℓ-1}^{ℓ+2} levelFlux f s u du`;
* `s ↦ levelExcess f s u` is nonincreasing with derivative `-levelFlux` off
  finitely many crossing times, and `levelExcess ≤ 1`; integrate and Fubini.
-/

namespace Talagrand

open MeasureTheory

variable {n : ℕ}

/-- The size-biased logarithmic profile
`𝔄_s(I) = 𝔼_λ[f_s·1_{log f_s ∈ I}]` [LGF §2.1]. -/
noncomputable def profile (f : Cube n → ℝ) (s : ℝ) (I : Set ℝ) : ℝ :=
  unifE (fun x => I.indicator (fun _ => heatAt f s x) (Real.log (heatAt f s x)))

/-- Excess mass above level `e^u`:
`F_s(u) = 𝔼_λ[(f_s - e^u)⁺]` [C, proof of Lemma 4]. -/
noncomputable def levelExcess (f : Cube n → ℝ) (s u : ℝ) : ℝ :=
  unifE (fun x => max (heatAt f s x - Real.exp u) 0)

open Classical in
/-- Weighted level-boundary flux
`¼·𝔼_λ ∑_i 1_{e^u ∈ (min,max]([f_s(x), f_s(σ_i x)])}·|Δ_i f_s(x)|`
(= `𝔈(1_{f_s > e^u}, f_s)` at non-crossing levels) [C, proof of Lemma 4]. -/
noncomputable def levelFlux (f : Cube n → ℝ) (s u : ℝ) : ℝ :=
  unifE (fun x => ∑ i,
    (if Real.exp u ∈ Set.uIoc (heatAt f s x) (heatAt f s (flipCoord i x))
      then |heatAt f s (flipCoord i x) - heatAt f s x| else 0)) / 4

/-- The localized test function `h_s = f_s·χ(log f_s - ℓ)²`. -/
noncomputable def localizedTest (f : Cube n → ℝ) (s ℓ : ℝ) : Cube n → ℝ :=
  fun x => heatAt f s x * cutoff (Real.log (heatAt f s x) - ℓ) ^ 2

section Positive

variable {f : Cube n → ℝ}

/-- Profiles are nonnegative. -/
lemma profile_nonneg (hf : ∀ x, 0 < f x) (s : ℝ) (I : Set ℝ) :
    0 ≤ profile f s I := by
  sorry

/-- Trivial mass bound: `𝔄_s(I) ≤ 𝔼_λ f_s = 1`. -/
lemma profile_le_one (hf : ∀ x, 0 < f x) (hm : unifE f = 1) (s : ℝ)
    (I : Set ℝ) : profile f s I ≤ 1 := by
  sorry

/-- Entropy lower bound [C eq (entropy_vs_anti_concentration_profile)]:
for `ℓ ≥ 2`, `ℓ·𝔄_s((ℓ,ℓ+1]) ≤ 2·Ent_λ(h_s)`. -/
lemma profile_le_ent (hf : ∀ x, 0 < f x) (hm : unifE f = 1) (s ℓ : ℝ)
    (hℓ : 2 ≤ ℓ) :
    ℓ * profile f s (Set.Ioc ℓ (ℓ + 1)) ≤ 2 * entUnif (localizedTest f s ℓ) := by
  sorry

/-- Coarea comparison [C eq (claim_dirichlet_comparison)] with our constants:
`𝔼_λ ∑_i (Δ_i √h_s)² ≤ 256·∫_{ℓ-1}^{ℓ+2} levelFlux f s u du`. -/
lemma dirichlet_le_flux_integral (hf : ∀ x, 0 < f x) (s ℓ : ℝ) :
    unifE (fun x => ∑ i,
        (Real.sqrt (localizedTest f s ℓ (flipCoord i x))
          - Real.sqrt (localizedTest f s ℓ x)) ^ 2)
      ≤ 256 * ∫ u in ℓ - 1..ℓ + 2, levelFlux f s u := by
  sorry

/-- Level-mass dissipation: for fixed `u > 0`, on any `[s₁,s₂] ⊆ [0,∞)`,
`levelExcess f s₂ u - levelExcess f s₁ u = -∫_{s₁}^{s₂} levelFlux f s u ds`
(FTC with the finitely many crossing times as exceptional set). -/
lemma levelExcess_sub_eq (hf : ∀ x, 0 < f x) (hm : unifE f = 1) (u : ℝ)
    (hu : 0 < u) {s₁ s₂ : ℝ} (h1 : 0 ≤ s₁) (h12 : s₁ ≤ s₂) :
    levelExcess f s₂ u - levelExcess f s₁ u
      = -∫ s in s₁..s₂, levelFlux f s u := by
  sorry

/-- Consequence: the total flux over all time is at most the initial excess:
`∫_{0}^{S} levelFlux f s u ds ≤ 1` for every `S ≥ 0`, `u > 0`. -/
lemma flux_time_integral_le_one (hf : ∀ x, 0 < f x) (hm : unifE f = 1)
    (u : ℝ) (hu : 0 < u) {S : ℝ} (hS : 0 ≤ S) :
    ∫ s in (0 : ℝ)..S, levelFlux f s u ≤ 1 := by
  sorry

/-- **Time-smoothed anti-concentration profile bound** [C Lemma 4]: there is a
universal constant `C` such that for every `n`, strictly positive density `f`,
and `ℓ > 2`, `∫_0^∞ 𝔄_s((ℓ,ℓ+1]) ds ≤ C/ℓ` (as a Lebesgue integral of the
nonnegative integrand). -/
theorem profile_time_integral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (f : Cube n → ℝ), (∀ x, 0 < f x) →
      unifE f = 1 → ∀ ℓ : ℝ, 2 < ℓ →
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (profile f s (Set.Ioc ℓ (ℓ + 1)))
        ≤ ENNReal.ofReal (C / ℓ) := by
  sorry

/-- Windowed corollary of [C Lemma 4], the form consumed by [LGF §3]:
for `0 ≤ s₁ ≤ s₂` and `ℓ > 2`,
`∫_{s₁}^{s₂} 𝔄_s((ℓ,ℓ+1]) ds ≤ C/ℓ` (same universal `C`). -/
theorem profile_window_integral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (f : Cube n → ℝ), (∀ x, 0 < f x) →
      unifE f = 1 → ∀ ℓ : ℝ, 2 < ℓ → ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ s₂ →
      ∫ s in s₁..s₂, profile f s (Set.Ioc ℓ (ℓ + 1)) ≤ C / ℓ := by
  sorry

/-- Measurability in `s` of the profile (finite sum of continuous×indicator). -/
lemma measurable_profile (hf : ∀ x, 0 < f x) (I : Set ℝ) (hI : MeasurableSet I) :
    Measurable fun s => profile f s I := by
  sorry

end Positive

end Talagrand
