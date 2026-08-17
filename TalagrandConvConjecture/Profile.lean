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

/-! ### Elementary facts about the heat flow at nonnegative times

Everything below is used only for `0 ≤ s`; for `s < 0` the operator
`T_ρ = smooth ρ` with `ρ = e^{-s} > 1` is *not* positivity preserving, so
`heatAt f s` may take negative values even for `f > 0`. -/

private lemma abs_exp_neg_le_one {s : ℝ} (hs : 0 ≤ s) : |Real.exp (-s)| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)

/-- For `s ≥ 0` the heat flow of a strictly positive density stays strictly
positive. -/
lemma heatAt_pos (hf : ∀ x, 0 < f x) {s : ℝ} (hs : 0 ≤ s) (x : Cube n) :
    0 < heatAt f s x :=
  smooth_pos (abs_exp_neg_le_one hs) hf x

/-- Mass conservation along the heat flow. -/
lemma unifE_heatAt (f : Cube n → ℝ) (s : ℝ) : unifE (heatAt f s) = unifE f :=
  unifE_smooth _ f

@[simp] lemma heatAt_zero (f : Cube n → ℝ) : heatAt f 0 = f := by
  simp [heatAt]

lemma continuous_heatAt (f : Cube n → ℝ) (x : Cube n) :
    Continuous fun s => heatAt f s x := continuous_smooth_exp f x

/-- Crude pointwise bound: a positive density of mean one is at most `2^n`
pointwise, and the same holds along the heat flow. -/
lemma heatAt_le_pow (hf : ∀ x, 0 < f x) (hm : unifE f = 1) {s : ℝ} (hs : 0 ≤ s)
    (x : Cube n) : heatAt f s x ≤ 2 ^ n := by
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have h1 : unifE (heatAt f s) = 1 := by rw [unifE_heatAt, hm]
  rw [unifE, div_eq_iff h2, one_mul] at h1
  calc heatAt f s x ≤ ∑ y : Cube n, heatAt f s y :=
        Finset.single_le_sum (fun y _ => (heatAt_pos hf hs y).le) (Finset.mem_univ x)
    _ = 2 ^ n := h1

private lemma unifE_sub (g h : Cube n → ℝ) :
    unifE (fun x => g x - h x) = unifE g - unifE h := by
  simp [unifE, Finset.sum_sub_distrib, sub_div]

private lemma sum_inv_mul_eq_unifE (g : Cube n → ℝ) :
    ∑ x : Cube n, ((2 : ℝ) ^ n)⁻¹ * g x = unifE g := by
  rw [← Finset.mul_sum, unifE, div_eq_inv_mul]

-- STATEMENT-ISSUE: `profile_nonneg` is FALSE as stated, because `s` is not
-- restricted to `0 ≤ s` and `heatAt f s = smooth (e^{-s}) f` is not
-- positivity preserving for `s < 0`.  Falsity witness: `n = 1`,
-- `f 1 = 3/2`, `f (-1) = 1/2` (so `f > 0` and `unifE f = 1`); then
-- `heatAt f s x = 1 + (1/2)·e^{-s}·toR (x 0)`, so at `s = -Real.log 4`
-- the two values are `3` and `-1`.  With `I = {0}` we get
-- `Real.log (-1) = Real.log 1 = 0 ∈ I` and `Real.log 3 ∉ I`, hence
-- `profile f s I = (-1 + 0)/2 = -1/2 < 0`.
-- The intended statement (with `0 ≤ s`) is `profile_nonneg'` below; every use
-- in this file and downstream is at nonnegative times.
/-- Profiles are nonnegative. -/
lemma profile_nonneg (hf : ∀ x, 0 < f x) (s : ℝ) (I : Set ℝ) :
    0 ≤ profile f s I := by
  sorry

/-- Profiles are nonnegative (correct form of `profile_nonneg`, with the
missing hypothesis `0 ≤ s`). -/
lemma profile_nonneg' (hf : ∀ x, 0 < f x) {s : ℝ} (hs : 0 ≤ s) (I : Set ℝ) :
    0 ≤ profile f s I :=
  unifE_nonneg fun x =>
    Set.indicator_nonneg (fun _ _ => (heatAt_pos hf hs x).le) _

-- STATEMENT-ISSUE: `profile_le_one` is FALSE as stated, for the same reason as
-- `profile_nonneg` (no hypothesis `0 ≤ s`).  With the same witness
-- (`n = 1`, `f 1 = 3/2`, `f (-1) = 1/2`, `s = -Real.log 4`, values `3` and
-- `-1`) and `I = {Real.log 3}` we get `profile f s I = (3 + 0)/2 = 3/2 > 1`.
-- The intended statement (with `0 ≤ s`) is `profile_le_one'` below.
/-- Trivial mass bound: `𝔄_s(I) ≤ 𝔼_λ f_s = 1`. -/
lemma profile_le_one (hf : ∀ x, 0 < f x) (hm : unifE f = 1) (s : ℝ)
    (I : Set ℝ) : profile f s I ≤ 1 := by
  sorry

/-- Trivial mass bound `𝔄_s(I) ≤ 𝔼_λ f_s = 1` (correct form of
`profile_le_one`, with the missing hypothesis `0 ≤ s`). -/
lemma profile_le_one' (hf : ∀ x, 0 < f x) (hm : unifE f = 1) {s : ℝ}
    (hs : 0 ≤ s) (I : Set ℝ) : profile f s I ≤ 1 := by
  have h1 : profile f s I ≤ unifE (heatAt f s) := by
    refine unifE_mono fun x => ?_
    by_cases hx : Real.log (heatAt f s x) ∈ I
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact (heatAt_pos hf hs x).le
  rwa [unifE_heatAt, hm] at h1

/-- The entropy step of [C eq (entropy_vs_anti_concentration_profile)], stated
for an abstract strictly positive density `F` of mean one (applied below with
`F = f_s`). The test function is `φ = ℓ·1_E - log(1+(e^ℓ-1)λ(E))` with
`E = {log F ∈ (ℓ,ℓ+1]}`, which satisfies `𝔼_λ e^φ = 1`. -/
private lemma abstract_profile_le_ent {F : Cube n → ℝ} (hFpos : ∀ x, 0 < F x)
    (hF1 : unifE F = 1) {ℓ : ℝ} (hℓ : 2 ≤ ℓ) :
    ℓ * unifE (fun x => (Set.Ioc ℓ (ℓ + 1)).indicator (fun _ => F x) (Real.log (F x)))
      ≤ 2 * entUnif (fun x => F x * cutoff (Real.log (F x) - ℓ) ^ 2) := by
  classical
  set g : Cube n → ℝ := fun x => F x * cutoff (Real.log (F x) - ℓ) ^ 2 with hgdef
  set A : ℝ := unifE (fun x =>
    (Set.Ioc ℓ (ℓ + 1)).indicator (fun _ => F x) (Real.log (F x))) with hAdef
  set ind : Cube n → ℝ := fun x =>
    (Set.Ioc ℓ (ℓ + 1)).indicator (fun _ => (1 : ℝ)) (Real.log (F x)) with hinddef
  set p : ℝ := unifE ind with hpdef
  set G : ℝ := unifE g with hGdef
  -- pointwise facts
  have hind1 : ∀ x, Real.log (F x) ∈ Set.Ioc ℓ (ℓ + 1) → ind x = 1 := by
    intro x hx; simp only [hinddef]; exact Set.indicator_of_mem hx _
  have hind0' : ∀ x, Real.log (F x) ∉ Set.Ioc ℓ (ℓ + 1) → ind x = 0 := by
    intro x hx; simp only [hinddef]; exact Set.indicator_of_notMem hx _
  have hgnn : ∀ x, 0 ≤ g x := by
    intro x; simp only [hgdef]; exact mul_nonneg (hFpos x).le (sq_nonneg _)
  have hcut1 : ∀ x, cutoff (Real.log (F x) - ℓ) ^ 2 ≤ 1 := by
    intro x
    have h := cutoff_mem_Icc (Real.log (F x) - ℓ)
    nlinarith [h.1, h.2]
  have hgle : ∀ x, g x ≤ F x := by
    intro x; simp only [hgdef]
    exact mul_le_of_le_one_right (hFpos x).le (hcut1 x)
  have hind0 : ∀ x, 0 ≤ ind x := by
    intro x; simp only [hinddef]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  -- `g·1_E` is the profile integrand (χ = 1 on the band)
  have hgind : ∀ x, g x * ind x
      = (Set.Ioc ℓ (ℓ + 1)).indicator (fun _ => F x) (Real.log (F x)) := by
    intro x
    by_cases hx : Real.log (F x) ∈ Set.Ioc ℓ (ℓ + 1)
    · rw [hind1 x hx, mul_one, Set.indicator_of_mem hx]
      simp only [hgdef]
      rw [cutoff_eq_one (by linarith [hx.1]) (by linarith [hx.2]), one_pow, mul_one]
    · rw [hind0' x hx, mul_zero, Set.indicator_of_notMem hx]
  -- the four scalar bounds
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact unifE_nonneg fun x => Set.indicator_nonneg (fun _ _ => (hFpos x).le) _
  have hp0 : 0 ≤ p := by rw [hpdef]; exact unifE_nonneg hind0
  have hG0 : 0 ≤ G := by rw [hGdef]; exact unifE_nonneg hgnn
  have hG1 : G ≤ 1 := by
    rw [hGdef, ← hF1]; exact unifE_mono hgle
  have he1 : (1 : ℝ) ≤ Real.exp ℓ := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hpA : p ≤ Real.exp (-ℓ) * A := by
    rw [hpdef, hAdef, ← unifE_smul]
    refine unifE_mono fun x => ?_
    by_cases hx : Real.log (F x) ∈ Set.Ioc ℓ (ℓ + 1)
    · rw [hind1 x hx, Set.indicator_of_mem hx]
      have hFx : Real.exp ℓ < F x := by
        have h := Real.exp_lt_exp.mpr hx.1
        rwa [Real.exp_log (hFpos x)] at h
      rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos ℓ), one_mul]
      linarith
    · rw [hind0' x hx, Set.indicator_of_notMem hx, mul_zero]
  have hee : Real.exp ℓ * Real.exp (-ℓ) = 1 := by
    rw [← Real.exp_add]; simp
  have hpA' : (Real.exp ℓ - 1) * p ≤ A := by
    have h2 : Real.exp ℓ * p ≤ Real.exp ℓ * (Real.exp (-ℓ) * A) :=
      mul_le_mul_of_nonneg_left hpA (Real.exp_pos ℓ).le
    have h3 : Real.exp ℓ * (Real.exp (-ℓ) * A) = A := by rw [← mul_assoc, hee, one_mul]
    nlinarith [hp0]
  -- the normalizing constant
  set Q : ℝ := 1 + (Real.exp ℓ - 1) * p with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQdef]; nlinarith [hp0]
  have hQ : (0 : ℝ) < Q := by linarith
  set c : ℝ := Real.log Q with hcdef
  have hc0 : 0 ≤ c := Real.log_nonneg hQ1
  have hcA : c ≤ A := le_trans (by
      have := Real.log_le_sub_one_of_pos hQ
      rw [hQdef] at this; linarith [this]) hpA'
  -- the variational bound
  have hw0 : ∀ _ : Cube n, (0:ℝ) ≤ ((2:ℝ) ^ n)⁻¹ := fun _ => by positivity
  have hw1 : ∑ _x : Cube n, ((2:ℝ) ^ n)⁻¹ = 1 := by
    have h := sum_inv_mul_eq_unifE (fun _ : Cube n => (1:ℝ))
    simpa using h
  have hexpind : ∀ x, Real.exp (ℓ * ind x) = 1 + (Real.exp ℓ - 1) * ind x := by
    intro x
    by_cases hx : Real.log (F x) ∈ Set.Ioc ℓ (ℓ + 1)
    · rw [hind1 x hx, mul_one, mul_one]; ring
    · rw [hind0' x hx, mul_zero, mul_zero, Real.exp_zero, add_zero]
  have hcQ : Real.exp c = Q := Real.exp_log hQ
  have hφ : ∑ x : Cube n, ((2:ℝ) ^ n)⁻¹ * Real.exp (ℓ * ind x - c) ≤ 1 := by
    have hstep : ∀ x : Cube n, ((2:ℝ) ^ n)⁻¹ * Real.exp (ℓ * ind x - c)
        = ((2:ℝ) ^ n)⁻¹ * ((1 + (Real.exp ℓ - 1) * ind x) / Q) := by
      intro x; rw [Real.exp_sub, hexpind x, hcQ]
    rw [Finset.sum_congr rfl fun x _ => hstep x]
    have hdiv : ∀ x : Cube n, ((2:ℝ) ^ n)⁻¹ * ((1 + (Real.exp ℓ - 1) * ind x) / Q)
        = (((2:ℝ) ^ n)⁻¹ * (1 + (Real.exp ℓ - 1) * ind x)) / Q := by
      intro x; ring
    rw [Finset.sum_congr rfl fun x _ => hdiv x, ← Finset.sum_div,
      sum_inv_mul_eq_unifE]
    have hu : unifE (fun x => 1 + (Real.exp ℓ - 1) * ind x) = Q := by
      have h1 := unifE_add (fun _ : Cube n => (1:ℝ)) (fun x => (Real.exp ℓ - 1) * ind x)
      rw [h1, unifE_const, unifE_smul, hQdef, hpdef]
    rw [hu, div_self (ne_of_gt hQ)]
  have hvar := sum_mul_le_ent (fun _ : Cube n => ((2:ℝ) ^ n)⁻¹) g
    (fun x => ℓ * ind x - c) hw0 hw1 hgnn hφ
  have hent : ent (fun _ : Cube n => ((2:ℝ) ^ n)⁻¹) g = entUnif g := by
    rw [ent, entUnif, sum_inv_mul_eq_unifE, sum_inv_mul_eq_unifE]
  have hlhs : ∑ x : Cube n, ((2:ℝ) ^ n)⁻¹ * (g x * (ℓ * ind x - c)) = ℓ * A - c * G := by
    rw [sum_inv_mul_eq_unifE]
    have hre : (fun x => g x * (ℓ * ind x - c))
        = fun x => ℓ * (g x * ind x) - c * g x := by funext x; ring
    rw [hre, unifE_sub, unifE_smul, unifE_smul, ← hGdef, hAdef]
    exact congrArg (fun z => ℓ * z - c * G) (congrArg unifE (funext hgind))
  rw [hlhs, hent] at hvar
  have hcG : c * G ≤ A := le_trans (mul_le_of_le_one_right hc0 hG1) hcA
  nlinarith [hvar, hcG, mul_nonneg (sub_nonneg.mpr hℓ) hA0]

-- STATEMENT-ISSUE: `profile_le_ent` is FALSE as stated (no hypothesis
-- `0 ≤ s`; for `s < 0` the flow `heatAt f s` takes negative values and the
-- entropy of the sign-changing `h_s` can be negative while the profile is
-- `0`).  Falsity witness: `n = 1`, `f 1 = 1.9`, `f (-1) = 0.1`, so
-- `heatAt f s x = 1 + 0.9·e^{-s}·toR (x 0)`; at `e^{-s} = 37.9` the values are
-- `F₊ ≈ 35.1` and `F₋ ≈ -33.1`.  With `ℓ = 2` neither `Real.log 35.1 ≈ 3.56`
-- nor `Real.log 33.1 ≈ 3.50` lies in `(2,3]`, so the profile is `0` and the
-- left side is `0`; but `h_s = (35.1·χ(1.56)², -33.1·χ(1.50)²)
-- ≈ (6.0, -8.28)` has `entUnif h_s ≈ -3.2 < 0`.
-- The intended statement (with `0 ≤ s`) is `profile_le_ent'` below.
/-- Entropy lower bound [C eq (entropy_vs_anti_concentration_profile)]:
for `ℓ ≥ 2`, `ℓ·𝔄_s((ℓ,ℓ+1]) ≤ 2·Ent_λ(h_s)`. -/
lemma profile_le_ent (hf : ∀ x, 0 < f x) (hm : unifE f = 1) (s ℓ : ℝ)
    (hℓ : 2 ≤ ℓ) :
    ℓ * profile f s (Set.Ioc ℓ (ℓ + 1)) ≤ 2 * entUnif (localizedTest f s ℓ) := by
  sorry

/-- Entropy lower bound [C eq (entropy_vs_anti_concentration_profile)] (correct
form of `profile_le_ent`, with the missing hypothesis `0 ≤ s`): for `ℓ ≥ 2`,
`ℓ·𝔄_s((ℓ,ℓ+1]) ≤ 2·Ent_λ(h_s)`. -/
lemma profile_le_ent' (hf : ∀ x, 0 < f x) (hm : unifE f = 1) {s : ℝ}
    (hs : 0 ≤ s) (ℓ : ℝ) (hℓ : 2 ≤ ℓ) :
    ℓ * profile f s (Set.Ioc ℓ (ℓ + 1)) ≤ 2 * entUnif (localizedTest f s ℓ) :=
  abstract_profile_le_ent (fun x => heatAt_pos hf hs x)
    (by rw [unifE_heatAt, hm]) hℓ

/-! ### The level flux as an indicator sum

`levelFlux` is defined with a classical `if`; the following instance-free
`Set.indicator` form is what all the analytic arguments use. -/

/-- The `(x,i)`-summand of `4·levelFlux f s u`, written as an indicator. -/
private noncomputable def fluxTerm (f : Cube n → ℝ) (s u : ℝ) (x : Cube n)
    (i : Fin n) : ℝ :=
  (Set.uIoc (heatAt f s x) (heatAt f s (flipCoord i x))).indicator
    (fun _ => |heatAt f s (flipCoord i x) - heatAt f s x|) (Real.exp u)

private lemma fluxTerm_nonneg (f : Cube n → ℝ) (s u : ℝ) (x : Cube n) (i : Fin n) :
    0 ≤ fluxTerm f s u x i :=
  Set.indicator_nonneg (fun _ _ => abs_nonneg _) _

private lemma levelFlux_eq_fluxTerm (f : Cube n → ℝ) (s u : ℝ) :
    levelFlux f s u = unifE (fun x => ∑ i, fluxTerm f s u x i) / 4 := by
  rw [levelFlux]
  congr 1

lemma levelFlux_nonneg (f : Cube n → ℝ) (s u : ℝ) : 0 ≤ levelFlux f s u := by
  rw [levelFlux_eq_fluxTerm]
  exact div_nonneg
    (unifE_nonneg fun x => Finset.sum_nonneg fun i _ => fluxTerm_nonneg _ _ _ _ _)
    (by norm_num)

private lemma intervalIntegrable_fluxTerm (f : Cube n → ℝ) (s : ℝ) (x : Cube n)
    (i : Fin n) (a b : ℝ) :
    IntervalIntegrable (fun u => fluxTerm f s u x i) volume a b := by
  have hT : MeasurableSet (Real.exp ⁻¹'
      Set.uIoc (heatAt f s x) (heatAt f s (flipCoord i x))) :=
    Real.measurable_exp measurableSet_uIoc
  have heq : (fun u => fluxTerm f s u x i)
      = (Real.exp ⁻¹' Set.uIoc (heatAt f s x) (heatAt f s (flipCoord i x))).indicator
          (fun _ => |heatAt f s (flipCoord i x) - heatAt f s x|) := by
    funext u
    rw [fluxTerm]
    by_cases h : Real.exp u ∈ Set.uIoc (heatAt f s x) (heatAt f s (flipCoord i x))
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show u ∈ Real.exp ⁻¹'
          Set.uIoc (heatAt f s x) (heatAt f s (flipCoord i x)) from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show u ∉ Real.exp ⁻¹'
          Set.uIoc (heatAt f s x) (heatAt f s (flipCoord i x)) from h)]
  rw [heq, intervalIntegrable_iff]
  exact (intervalIntegrable_iff.1
    ((continuous_const :
      Continuous fun _ : ℝ => |heatAt f s (flipCoord i x) - heatAt f s x|).intervalIntegrable
        a b)).indicator hT

private lemma intervalIntegrable_sum_fluxTerm (f : Cube n → ℝ) (s : ℝ) (x : Cube n)
    (a b : ℝ) : IntervalIntegrable (fun u => ∑ i, fluxTerm f s u x i) volume a b := by
  have h := IntervalIntegrable.sum (Finset.univ : Finset (Fin n))
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      intervalIntegrable_fluxTerm f s x i a b)
  have heq : (∑ i ∈ (Finset.univ : Finset (Fin n)), fun u : ℝ => fluxTerm f s u x i)
      = fun u => ∑ i, fluxTerm f s u x i := by
    funext u; simp
  rwa [heq] at h

private lemma integral_unifE_sum_fluxTerm (f : Cube n → ℝ) (s a b : ℝ) :
    ∫ u in a..b, unifE (fun x => ∑ i, fluxTerm f s u x i)
      = unifE (fun x => ∑ i, ∫ u in a..b, fluxTerm f s u x i) := by
  simp only [unifE]
  rw [intervalIntegral.integral_div]
  congr 1
  have h1 : ∫ u in a..b, ∑ x : Cube n, ∑ i, fluxTerm f s u x i
      = ∑ x : Cube n, ∫ u in a..b, ∑ i, fluxTerm f s u x i :=
    intervalIntegral.integral_finset_sum fun x _ =>
      intervalIntegrable_sum_fluxTerm f s x a b
  rw [h1]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact intervalIntegral.integral_finset_sum fun i _ =>
    intervalIntegrable_fluxTerm f s x i a b

/-! ### The pointwise coarea estimate -/

private lemma exp_mem_uIoc_iff (a b u : ℝ) :
    Real.exp u ∈ Set.uIoc (Real.exp a) (Real.exp b) ↔ u ∈ Set.uIoc a b := by
  simp only [Set.mem_uIoc, Real.exp_lt_exp, Real.exp_le_exp]

private lemma sqrt_localizedTest {f : Cube n → ℝ} {s : ℝ}
    (hFpos : ∀ y, 0 < heatAt f s y) (ℓ : ℝ) (y : Cube n) :
    Real.sqrt (localizedTest f s ℓ y) = sqrtTest ℓ (Real.log (heatAt f s y)) := by
  have hc := cutoff_mem_Icc (Real.log (heatAt f s y) - ℓ)
  have hsq : Real.sqrt (heatAt f s y) = Real.exp (Real.log (heatAt f s y) / 2) := by
    have h : (Real.exp (Real.log (heatAt f s y) / 2)) ^ 2 = heatAt f s y := by
      rw [sq, ← Real.exp_add,
        show Real.log (heatAt f s y) / 2 + Real.log (heatAt f s y) / 2
          = Real.log (heatAt f s y) by ring]
      exact Real.exp_log (hFpos y)
    have h2 : Real.sqrt ((Real.exp (Real.log (heatAt f s y) / 2)) ^ 2)
        = Real.exp (Real.log (heatAt f s y) / 2) := Real.sqrt_sq (Real.exp_nonneg _)
    rwa [h] at h2
  simp only [localizedTest, sqrtTest]
  rw [Real.sqrt_mul (hFpos y).le, Real.sqrt_sq hc.1, hsq]

private lemma sqrtTest_sq_diff_le_integral (ℓ a b : ℝ) :
    (sqrtTest ℓ b - sqrtTest ℓ a) ^ 2
      ≤ 16 * ∫ u in ℓ - 1..ℓ + 2,
          (Set.uIoc (Real.exp a) (Real.exp b)).indicator
            (fun _ => |Real.exp b - Real.exp a|) (Real.exp u) := by
  have hle : ℓ - 1 ≤ ℓ + 2 := by linarith
  have hcongr : ∀ u ∈ Set.uIcc (ℓ - 1) (ℓ + 2),
      (Set.uIoc (Real.exp a) (Real.exp b)).indicator
        (fun _ => |Real.exp b - Real.exp a|) (Real.exp u)
      = (Set.uIoc a b).indicator (fun _ => |Real.exp b - Real.exp a|) u := by
    intro u _
    by_cases h : u ∈ Set.uIoc a b
    · rw [Set.indicator_of_mem ((exp_mem_uIoc_iff a b u).2 h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (fun hh => h ((exp_mem_uIoc_iff a b u).1 hh)),
        Set.indicator_of_notMem h]
  have hval : ∫ u in ℓ - 1..ℓ + 2,
      (Set.uIoc a b).indicator (fun _ => |Real.exp b - Real.exp a|) u
      = (volume (Set.Ioc (ℓ - 1) (ℓ + 2) ∩ Set.uIoc a b)).toReal
          * |Real.exp b - Real.exp a| := by
    rw [intervalIntegral.integral_of_le hle,
      MeasureTheory.setIntegral_indicator measurableSet_uIoc,
      MeasureTheory.setIntegral_const, smul_eq_mul]
    rfl
  have hmono : (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal
      ≤ (volume (Set.Ioc (ℓ - 1) (ℓ + 2) ∩ Set.uIoc a b)).toReal := by
    refine ENNReal.toReal_mono ?_ (measure_mono ?_)
    · exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
        measure_Ioc_lt_top)
    · intro y hy
      exact ⟨Set.Ioo_subset_Ioc_self hy.2, hy.1⟩
  have h0 := sqrtTest_sq_diff_le ℓ a b
  rw [intervalIntegral.integral_congr hcongr, hval]
  nlinarith [abs_nonneg (Real.exp b - Real.exp a), h0, hmono]

/-- Coarea comparison [C eq (claim_dirichlet_comparison)] with our constants
(correct form of `dirichlet_le_flux_integral`, with the missing hypothesis
`0 ≤ s`): `𝔼_λ ∑_i (Δ_i √h_s)² ≤ 256·∫_{ℓ-1}^{ℓ+2} levelFlux f s u du`. -/
lemma dirichlet_le_flux_integral' (hf : ∀ x, 0 < f x) {s : ℝ} (hs : 0 ≤ s) (ℓ : ℝ) :
    unifE (fun x => ∑ i,
        (Real.sqrt (localizedTest f s ℓ (flipCoord i x))
          - Real.sqrt (localizedTest f s ℓ x)) ^ 2)
      ≤ 256 * ∫ u in ℓ - 1..ℓ + 2, levelFlux f s u := by
  have hFpos : ∀ y, 0 < heatAt f s y := fun y => heatAt_pos hf hs y
  have hle : ℓ - 1 ≤ ℓ + 2 := by linarith
  have hpt : ∀ (x : Cube n) (i : Fin n),
      (Real.sqrt (localizedTest f s ℓ (flipCoord i x))
        - Real.sqrt (localizedTest f s ℓ x)) ^ 2
        ≤ 16 * ∫ u in ℓ - 1..ℓ + 2, fluxTerm f s u x i := by
    intro x i
    rw [sqrt_localizedTest hFpos ℓ (flipCoord i x), sqrt_localizedTest hFpos ℓ x]
    have h := sqrtTest_sq_diff_le_integral ℓ (Real.log (heatAt f s x))
      (Real.log (heatAt f s (flipCoord i x)))
    rwa [Real.exp_log (hFpos x), Real.exp_log (hFpos (flipCoord i x))] at h
  set X : ℝ := ∫ u in ℓ - 1..ℓ + 2, unifE (fun x => ∑ i, fluxTerm f s u x i) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    refine intervalIntegral.integral_nonneg hle fun u _ => ?_
    exact unifE_nonneg fun x => Finset.sum_nonneg fun i _ => fluxTerm_nonneg _ _ _ _ _
  have hlf : ∫ u in ℓ - 1..ℓ + 2, levelFlux f s u = X / 4 := by
    rw [hXdef, ← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr fun u _ => levelFlux_eq_fluxTerm f s u
  have hchain : unifE (fun x => ∑ i,
      (Real.sqrt (localizedTest f s ℓ (flipCoord i x))
        - Real.sqrt (localizedTest f s ℓ x)) ^ 2) ≤ 16 * X := by
    calc unifE (fun x => ∑ i,
        (Real.sqrt (localizedTest f s ℓ (flipCoord i x))
          - Real.sqrt (localizedTest f s ℓ x)) ^ 2)
        ≤ unifE (fun x => ∑ i, 16 * ∫ u in ℓ - 1..ℓ + 2, fluxTerm f s u x i) :=
          unifE_mono fun x => Finset.sum_le_sum fun i _ => hpt x i
      _ = 16 * unifE (fun x => ∑ i, ∫ u in ℓ - 1..ℓ + 2, fluxTerm f s u x i) := by
          rw [← unifE_smul]
          exact congrArg unifE (funext fun x => (Finset.mul_sum _ _ _).symm)
      _ = 16 * X := by rw [hXdef, integral_unifE_sum_fluxTerm]
  rw [hlf]
  linarith

-- STATEMENT-ISSUE: `dirichlet_le_flux_integral` lacks the hypothesis
-- `0 ≤ s`.  The coarea argument of [C, proof of Lemma 4] rewrites
-- `√(h_s) = ψ_ℓ(log f_s)`, which requires `f_s > 0`; for `s < 0` the flow
-- `heatAt f s` takes negative values (see the witness recorded above
-- `profile_nonneg`) and `√(h_s)` is no longer of this form, so the proof
-- breaks down.  We have not determined whether the inequality happens to
-- remain true for `s < 0`.  The intended statement (with `0 ≤ s`) is
-- `dirichlet_le_flux_integral'` above, which is proved.
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
  have key : Measurable fun s => ∑ x : Cube n,
      I.indicator (fun _ => heatAt f s x) (Real.log (heatAt f s x)) := by
    refine Finset.measurable_sum _ fun x _ => ?_
    have h1 : Measurable fun s => heatAt f s x := (continuous_heatAt f x).measurable
    have h2 : MeasurableSet {s : ℝ | Real.log (heatAt f s x) ∈ I} :=
      (Real.measurable_log.comp h1) hI
    have heq : (fun s => I.indicator (fun _ => heatAt f s x) (Real.log (heatAt f s x)))
        = {s : ℝ | Real.log (heatAt f s x) ∈ I}.indicator (fun s => heatAt f s x) := by
      funext s
      by_cases hs : Real.log (heatAt f s x) ∈ I
      · rw [Set.indicator_of_mem hs,
          Set.indicator_of_mem (show s ∈ {s : ℝ | Real.log (heatAt f s x) ∈ I} from hs)]
      · rw [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (show s ∉ {s : ℝ | Real.log (heatAt f s x) ∈ I} from hs)]
    rw [heq]
    exact h1.indicator h2
  simp only [profile, unifE]
  exact key.div_const _

end Positive

end Talagrand
