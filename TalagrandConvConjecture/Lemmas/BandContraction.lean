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

open Classical

/-! ### Private plumbing: terminal-slice positivity and the pairing functional -/

/-- The terminal slice `π_{K-1}(T_o)` is a legitimate evaluation point of the
last cell of the glued flow. -/
private lemma term_index {ℓ θ : ℝ} {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) :
    c.K - 1 < c.K ∧ obsT ∈ Set.Icc (c.z (c.K - 1)) (c.z (c.K - 1 + 1)) := by
  have hpos : 0 < c.K := c.is.grid.pos
  have hk : c.K - 1 < c.K := Nat.sub_lt hpos Nat.one_pos
  have hsucc : c.K - 1 + 1 = c.K := Nat.succ_pred_eq_of_pos hpos
  have hlast : c.z (c.K - 1 + 1) = obsT := by rw [hsucc]; exact c.is.grid.last
  refine ⟨hk, Set.mem_Icc.mpr ⟨?_, le_of_eq hlast⟩⟩
  have hmono := c.is.grid.mono _ hk
  rw [← hlast]; exact hmono

private lemma term_nonneg {ℓ θ : ℝ} (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (s : JSt n) : 0 ≤ c.term s := by
  show (0:ℝ) ≤ c.π (c.K - 1) obsT s
  exact D.cflow_nonneg hθ c (D.term_index c).1 (D.term_index c).2 s

private lemma startW_nonneg {θ : ℝ} (hθ : θ ≤ obsT) (x₀ : Cube n) :
    0 ≤ D.startW θ x₀ := by
  have h : (0:ℝ) ≤ D.T - θ := by
    have h1 := D.tA_pos
    have h2 : D.T = D.tA + obsT := rfl
    linarith
  show (0:ℝ) ≤ D.fs (D.T - θ) x₀ / 2 ^ n
  exact div_nonneg (D.fs_pos h x₀).le (by positivity)

private lemma NW_nonneg (ℓ θ : ℝ) (x₀ : Cube n) (t : ℝ) (s : JSt n) :
    0 ≤ D.NW ℓ θ x₀ t s := by
  unfold NW
  split <;> exact (Real.exp_pos _).le

/-- The `A`-localized terminal pairing `∑_{x₀∈A} ν(x₀)·𝔼_{x₀}[g(V,W,sector)]`. -/
private noncomputable def pair {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (g : JSt n → ℝ) : ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s * g s

private lemma pair_mono {ℓ θ : ℝ} (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) {g₁ g₂ : JSt n → ℝ} (h : ∀ s, g₁ s ≤ g₂ s) :
    D.pair Φ A g₁ ≤ D.pair Φ A g₂ := by
  refine Finset.sum_le_sum fun x₀ _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (D.startW_nonneg hθ x₀)
  exact Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (h s) (D.term_nonneg hθ (Φ x₀) s)

private lemma pair_add {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n))
    (g₁ g₂ : JSt n → ℝ) :
    D.pair Φ A (fun s => g₁ s + g₂ s) = D.pair Φ A g₁ + D.pair Φ A g₂ := by
  simp only [pair, mul_add, Finset.sum_add_distrib]

private lemma pair_sub {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n))
    (g₁ g₂ : JSt n → ℝ) :
    D.pair Φ A (fun s => g₁ s - g₂ s) = D.pair Φ A g₁ - D.pair Φ A g₂ := by
  simp only [pair, mul_sub, Finset.sum_sub_distrib]

private lemma pair_sum {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n))
    {ι : Type*} [DecidableEq ι] (t : Finset ι) (g : ι → JSt n → ℝ) :
    D.pair Φ A (fun s => ∑ k ∈ t, g k s) = ∑ k ∈ t, D.pair Φ A (g k) := by
  induction t using Finset.induction_on with
  | empty => simp [pair]
  | @insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      rw [D.pair_add, ih]

/-! ### Private plumbing: the terminal indicators -/

/-- Terminal band indicator `1_{F_{T_o}(w) ∈ (r,r+1]}` as a test function. -/
private noncomputable def bandW (r : ℝ) : Cube n → ℝ :=
  fun w => if D.F obsT w ∈ Set.Ioc r (r + 1) then 1 else 0

private lemma bandW_nonneg (r : ℝ) (w : Cube n) : 0 ≤ D.bandW r w := by
  unfold bandW; split <;> norm_num

private lemma bandW_eq_one {r : ℝ} {w : Cube n}
    (h : D.F obsT w ∈ Set.Ioc r (r + 1)) : D.bandW r w = 1 := by
  unfold bandW; rw [if_pos h]

/-- Crossing indicator `1_{F(W) ∈ (ℓ+j, ℓ+j+1]}·1_{F(V) ≤ ℓ+1}`. -/
private noncomputable def crossInd (ℓ : ℝ) (j : ℕ) : JSt n → ℝ := fun s =>
  if D.F obsT s.2.1 ∈ Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)
      ∧ D.F obsT s.1 ≤ ℓ + 1 then 1 else 0

/-- `1_{F(W) > ℓ+1}·1_{F(V) ≤ ℓ+1}`. -/
private noncomputable def hiWloV (ℓ : ℝ) : JSt n → ℝ := fun s =>
  if ℓ + 1 < D.F obsT s.2.1 ∧ D.F obsT s.1 ≤ ℓ + 1 then 1 else 0

/-- `1_{F(V) > ℓ+1}·1_{F(W) ≤ ℓ+1}`. -/
private noncomputable def hiVloW (ℓ : ℝ) : JSt n → ℝ := fun s =>
  if ℓ + 1 < D.F obsT s.1 ∧ D.F obsT s.2.1 ≤ ℓ + 1 then 1 else 0

private lemma Aband_pair {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (r : ℝ) :
    D.Aband Φ A r = D.pair Φ A (fun s => D.bandW r s.1) := rfl

private lemma Bband_pair {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (r : ℝ) :
    D.Bband Φ A r = D.pair Φ A (fun s => D.bandW r s.2.1) := rfl

private lemma crossInd_pair {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (j : ℕ) :
    ∑ x₀ ∈ A, D.startW θ x₀ *
        ∑ s : JSt n, (Φ x₀).term s *
          (if D.F obsT s.2.1 ∈ Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)
              ∧ D.F obsT s.1 ≤ ℓ + 1 then (1 : ℝ) else 0)
      = D.pair Φ A (D.crossInd ℓ j) := rfl

private lemma Dtest_pair {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A B : Finset (Cube n)) :
    ∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B
      = D.pair Φ A (fun s =>
          (if s.2.1 ∈ B then (1 : ℝ) else 0) - (if s.1 ∈ B then (1 : ℝ) else 0)) :=
  rfl

/-- Test set for the band `(r, r+1]`. -/
private noncomputable def bandFin (r : ℝ) : Finset (Cube n) :=
  Finset.univ.filter fun w => D.F obsT w ∈ Set.Ioc r (r + 1)

/-- Test set for the tail `(r, ∞)`. -/
private noncomputable def hiFin (r : ℝ) : Finset (Cube n) :=
  Finset.univ.filter fun w => r < D.F obsT w

private lemma ind_bandFin (r : ℝ) (w : Cube n) :
    (if w ∈ D.bandFin r then (1 : ℝ) else 0) = D.bandW r w := by
  unfold bandFin bandW
  by_cases h : D.F obsT w ∈ Set.Ioc r (r + 1)
  · rw [if_pos h, if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ w, h⟩)]
  · rw [if_neg h, if_neg fun hm => h (Finset.mem_filter.mp hm).2]

private lemma ind_hiFin (r : ℝ) (w : Cube n) :
    (if w ∈ D.hiFin r then (1 : ℝ) else 0)
      = (if r < D.F obsT w then (1 : ℝ) else 0) := by
  unfold hiFin
  by_cases h : r < D.F obsT w
  · rw [if_pos h, if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ w, h⟩)]
  · rw [if_neg h, if_neg fun hm => h (Finset.mem_filter.mp hm).2]

/-- Add/subtract the both-in-`B` mass: the signed test discrepancy for the
tail `B = {F > r}` equals the difference of the two one-sided crossing
events. -/
private lemma cross_ind_eq (r : ℝ) (s : JSt n) :
    (if r < D.F obsT s.2.1 then (1 : ℝ) else 0)
        - (if r < D.F obsT s.1 then (1 : ℝ) else 0)
      = (if r < D.F obsT s.2.1 ∧ D.F obsT s.1 ≤ r then (1 : ℝ) else 0)
        - (if r < D.F obsT s.1 ∧ D.F obsT s.2.1 ≤ r then (1 : ℝ) else 0) := by
  by_cases h1 : r < D.F obsT s.2.1 <;> by_cases h2 : r < D.F obsT s.1
  · rw [if_pos h1, if_pos h2, if_neg fun h => absurd h2 (not_lt.mpr h.2),
      if_neg fun h => absurd h1 (not_lt.mpr h.2)]
    ring
  · rw [if_pos h1, if_neg h2, if_pos ⟨h1, not_lt.mp h2⟩, if_neg fun h => h2 h.1]
    ring
  · rw [if_neg h1, if_pos h2, if_neg fun h => h1 h.1, if_pos ⟨h2, not_lt.mp h1⟩]
    ring
  · rw [if_neg h1, if_neg h2, if_neg fun h => h1 h.1, if_neg fun h => h2 h.1]
    ring

/-- `W ∈ band ℓ` splits into the `j = 0` crossing event and the event that
`V` has already escaped above `ℓ+1`. -/
private lemma bandW_le (ℓ : ℝ) (s : JSt n) :
    D.bandW ℓ s.2.1 ≤ D.crossInd ℓ 0 s + D.hiVloW ℓ s := by
  unfold bandW crossInd hiVloW
  simp only [Nat.cast_zero, add_zero]
  have hnn : (0 : ℝ) ≤ (if ℓ + 1 < D.F obsT s.1 ∧ D.F obsT s.2.1 ≤ ℓ + 1
      then (1 : ℝ) else 0) := by split <;> norm_num
  have hnn2 : (0 : ℝ) ≤ (if D.F obsT s.2.1 ∈ Set.Ioc ℓ (ℓ + 1)
      ∧ D.F obsT s.1 ≤ ℓ + 1 then (1 : ℝ) else 0) := by split <;> norm_num
  by_cases hw : D.F obsT s.2.1 ∈ Set.Ioc ℓ (ℓ + 1)
  · rw [if_pos hw]
    by_cases hv : D.F obsT s.1 ≤ ℓ + 1
    · rw [if_pos (⟨hw, hv⟩ : _ ∧ _)]
      linarith
    · rw [if_neg fun h => hv h.2, if_pos (⟨not_le.mp hv, hw.2⟩ : _ ∧ _)]
      norm_num
  · rw [if_neg hw]
    linarith

/-- Geometric weights: `e^{-j} = (e^{-1})^j`. -/
private lemma exp_neg_nat (j : ℕ) : Real.exp (-(j : ℝ)) = Real.exp (-1) ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
      push_cast
      rw [show -((k : ℝ) + 1) = -(k : ℝ) + -1 by ring, Real.exp_add, ih, pow_succ]

/-- The bands `(r+k, r+k+1]`, `k < M`, cover `(r, r+M]`. -/
private lemma one_le_band_sum (r v : ℝ) (h1 : r < v) :
    ∀ M : ℕ, v ≤ r + M →
      (1 : ℝ) ≤ ∑ k ∈ Finset.range M,
        (if v ∈ Set.Ioc (r + (k : ℝ)) (r + (k : ℝ) + 1) then (1 : ℝ) else 0) := by
  intro M
  induction M with
  | zero =>
      intro h2
      exfalso
      simp only [Nat.cast_zero, add_zero] at h2
      linarith
  | succ m ih =>
      intro h2
      rw [Finset.sum_range_succ]
      have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range m,
          (if v ∈ Set.Ioc (r + (k : ℝ)) (r + (k : ℝ) + 1) then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun k _ => by split <;> norm_num
      have hnn2 : (0 : ℝ) ≤ (if v ∈ Set.Ioc (r + (m : ℝ)) (r + (m : ℝ) + 1)
          then (1 : ℝ) else 0) := by split <;> norm_num
      by_cases hle : v ≤ r + (m : ℝ)
      · have := ih hle
        linarith
      · have hpos : (if v ∈ Set.Ioc (r + (m : ℝ)) (r + (m : ℝ) + 1)
            then (1 : ℝ) else 0) = 1 := by
          refine if_pos ⟨not_le.mp hle, ?_⟩
          push_cast at h2
          linarith
        rw [hpos]
        linarith

/-! ### The band-crossing estimate -/

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
  have hcmp := D.weighted_comparison_localized hℓ hθ0 hθ Φ (D.activeF ℓ θ)
    (D.bandW (ℓ + (j : ℝ))) (D.bandW_nonneg _)
  have step1 : Real.exp (alphaC + (j : ℝ) - 1) *
      (∑ x₀ ∈ D.activeF ℓ θ, D.startW θ x₀ *
        ∑ s : JSt n, (Φ x₀).term s *
          (if D.F obsT s.2.1 ∈ Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)
              ∧ D.F obsT s.1 ≤ ℓ + 1 then (1 : ℝ) else 0))
      ≤ ∑ x₀ ∈ D.activeF ℓ θ, D.startW θ x₀ *
          ∑ s : JSt n, D.NW ℓ θ x₀ obsT s * (Φ x₀).term s
            * D.bandW (ℓ + (j : ℝ)) s.2.1 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x₀ hx₀ => ?_
    rw [← mul_assoc, mul_comm (Real.exp (alphaC + (j : ℝ) - 1)) (D.startW θ x₀),
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (D.startW_nonneg hθ x₀)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    by_cases hc : D.F obsT s.2.1 ∈ Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)
        ∧ D.F obsT s.1 ≤ ℓ + 1
    · have hNW := D.NW_ge_on_crossing hx₀ (Nat.cast_nonneg j) hc.1.1 hc.2
      rw [if_pos hc, D.bandW_eq_one hc.1, mul_one, mul_one]
      exact mul_le_mul_of_nonneg_right hNW (D.term_nonneg hθ (Φ x₀) s)
    · rw [if_neg hc, mul_zero, mul_zero]
      exact mul_nonneg (mul_nonneg (D.NW_nonneg _ _ _ _ _)
        (D.term_nonneg hθ (Φ x₀) s)) (D.bandW_nonneg _ _)
  have key : Real.exp (alphaC + (j : ℝ) - 1) *
      (∑ x₀ ∈ D.activeF ℓ θ, D.startW θ x₀ *
        ∑ s : JSt n, (Φ x₀).term s *
          (if D.F obsT s.2.1 ∈ Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)
              ∧ D.F obsT s.1 ≤ ℓ + 1 then (1 : ℝ) else 0))
      ≤ D.Aband Φ (D.activeF ℓ θ) (ℓ + (j : ℝ)) := step1.trans hcmp
  have he : Real.exp (1 - alphaC + -(j : ℝ)) * Real.exp (alphaC + (j : ℝ) - 1)
      = 1 := by
    rw [← Real.exp_add,
      show (1 - alphaC + -(j : ℝ)) + (alphaC + (j : ℝ) - 1) = 0 by ring,
      Real.exp_zero]
  rw [← Real.exp_add]
  have hmul := mul_le_mul_of_nonneg_left key
    (Real.exp_pos (1 - alphaC + -(j : ℝ))).le
  rw [← mul_assoc, he, one_mul] at hmul
  exact hmul

/-! ### Summability of the band series -/

/-- Summability input for the band series (bands are bounded by `1` and the
weights are geometric). -/
theorem Aband_summable {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) :
    Summable (fun j : ℕ => Real.exp (-((j : ℝ) + 1))
      * D.Aband Φ A (ℓ + j + 1)) := by
  have hexp1 : Real.exp (-1 : ℝ) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
    simpa using h
  have hexplt : Real.exp (-1 : ℝ) < 1 := by
    have h := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
    simpa using h
  have hgeo : Summable (fun j : ℕ => Real.exp (-1 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hexplt
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hgeo
  · exact mul_nonneg (Real.exp_pos _).le (D.Aband_nonneg hθ0 hθ Φ A _)
  · have h1 : D.Aband Φ A (ℓ + (j : ℝ) + 1) ≤ 1 :=
      (D.Aband_le_profile hθ0 hθ Φ A _).trans (profile_le_one D.hf D.hm _ _)
    have h2 : Real.exp (-((j : ℝ) + 1)) ≤ Real.exp (-1 : ℝ) ^ j := by
      rw [show -((j : ℝ) + 1) = -(j : ℝ) + -1 by ring, Real.exp_add,
        exp_neg_nat j]
      nth_rewrite 2 [← mul_one (Real.exp (-1 : ℝ) ^ j)]
      exact mul_le_mul_of_nonneg_left hexp1 (pow_nonneg (Real.exp_pos _).le j)
    have h3 : Real.exp (-((j : ℝ) + 1)) * D.Aband Φ A (ℓ + (j : ℝ) + 1)
        ≤ Real.exp (-((j : ℝ) + 1)) * 1 :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    rw [mul_one] at h3
    exact h3.trans h2

/-! ### Band contraction -/

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
  -- Step 4 of [LGF §4.3]: `A_θ(ℓ) ≤ B_θ(ℓ) + D_{ℰ_θ}` (test `B = band ℓ`).
  have hAB : D.Aband Φ (D.activeF ℓ θ) ℓ
      ≤ D.Bband Φ (D.activeF ℓ θ) ℓ + D.DA Φ (D.activeF ℓ θ) := by
    have habs := D.abs_Dtest_le_DA hθ Φ (D.activeF ℓ θ) (D.bandFin ℓ)
    have heq : ∑ x₀ ∈ D.activeF ℓ θ, D.startW θ x₀ * D.DtestF (Φ x₀) (D.bandFin ℓ)
        = D.Bband Φ (D.activeF ℓ θ) ℓ - D.Aband Φ (D.activeF ℓ θ) ℓ := by
      rw [D.Dtest_pair, D.Bband_pair, D.Aband_pair, ← D.pair_sub]
      congr 1
      funext s
      rw [D.ind_bandFin, D.ind_bandFin]
    rw [heq] at habs
    have h := (abs_le.mp habs).1
    linarith
  -- Step 1: `B_θ(ℓ) ≤ c₀·A_θ(ℓ) + ℙ(ℰ, F(V) > ℓ+1 ≥ F(W))`.
  have h0 : D.pair Φ (D.activeF ℓ θ) (D.crossInd ℓ 0)
      ≤ Real.exp (1 - alphaC) * D.Aband Φ (D.activeF ℓ θ) ℓ := by
    have hbc := D.band_crossing_le hℓ hθ0 hθ Φ 0
    rw [D.crossInd_pair] at hbc
    simpa using hbc
  have hB : D.Bband Φ (D.activeF ℓ θ) ℓ
      ≤ Real.exp (1 - alphaC) * D.Aband Φ (D.activeF ℓ θ) ℓ
        + D.pair Φ (D.activeF ℓ θ) (D.hiVloW ℓ) := by
    have hm : D.Bband Φ (D.activeF ℓ θ) ℓ
        ≤ D.pair Φ (D.activeF ℓ θ) (D.crossInd ℓ 0)
          + D.pair Φ (D.activeF ℓ θ) (D.hiVloW ℓ) := by
      rw [D.Bband_pair, ← D.pair_add]
      exact D.pair_mono hθ Φ _ fun s => D.bandW_le ℓ s
    linarith
  -- Step 2: swap the roles of `V` and `W` at the cost of `D_{ℰ_θ}`.
  have hQ : D.pair Φ (D.activeF ℓ θ) (D.hiVloW ℓ)
      ≤ D.pair Φ (D.activeF ℓ θ) (D.hiWloV ℓ) + D.DA Φ (D.activeF ℓ θ) := by
    have habs := D.abs_Dtest_le_DA hθ Φ (D.activeF ℓ θ) (D.hiFin (ℓ + 1))
    have heq : ∑ x₀ ∈ D.activeF ℓ θ,
          D.startW θ x₀ * D.DtestF (Φ x₀) (D.hiFin (ℓ + 1))
        = D.pair Φ (D.activeF ℓ θ) (D.hiWloV ℓ)
          - D.pair Φ (D.activeF ℓ θ) (D.hiVloW ℓ) := by
      rw [D.Dtest_pair, ← D.pair_sub]
      congr 1
      funext s
      rw [D.ind_hiFin, D.ind_hiFin]
      exact D.cross_ind_eq (ℓ + 1) s
    rw [heq] at habs
    have h := (abs_le.mp habs).1
    linarith
  -- Step 3: partition `(ℓ+1, ∞)` into the bands `(ℓ+j, ℓ+j+1]`, `j ≥ 1`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ w : Cube n, D.F obsT w ≤ C := by
    obtain ⟨C, hC⟩ := Finset.exists_le
      ((Finset.univ : Finset (Cube n)).image fun w => D.F obsT w)
    exact ⟨C, fun w => hC _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))⟩
  obtain ⟨M, hFbd⟩ : ∃ M : ℕ, ∀ w : Cube n, D.F obsT w ≤ (ℓ + 1) + (M : ℝ) := by
    refine ⟨⌈C - (ℓ + 1)⌉₊, fun w => ?_⟩
    have h1 : C - (ℓ + 1) ≤ ((⌈C - (ℓ + 1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith [hC w]
  have hpt : ∀ s : JSt n,
      D.hiWloV ℓ s ≤ ∑ k ∈ Finset.range M, D.crossInd ℓ (k + 1) s := by
    intro s
    unfold hiWloV crossInd
    by_cases hc : ℓ + 1 < D.F obsT s.2.1 ∧ D.F obsT s.1 ≤ ℓ + 1
    · rw [if_pos hc]
      have hrw : ∀ k ∈ Finset.range M,
          (if D.F obsT s.2.1 ∈ Set.Ioc (ℓ + ((k + 1 : ℕ) : ℝ))
              (ℓ + ((k + 1 : ℕ) : ℝ) + 1) ∧ D.F obsT s.1 ≤ ℓ + 1
            then (1 : ℝ) else 0)
            = (if D.F obsT s.2.1 ∈ Set.Ioc ((ℓ + 1) + (k : ℝ))
                ((ℓ + 1) + (k : ℝ) + 1) then (1 : ℝ) else 0) := by
        intro k _
        have he : ℓ + ((k + 1 : ℕ) : ℝ) = (ℓ + 1) + (k : ℝ) := by push_cast; ring
        rw [he]
        by_cases hb : D.F obsT s.2.1 ∈ Set.Ioc ((ℓ + 1) + (k : ℝ))
            ((ℓ + 1) + (k : ℝ) + 1)
        · rw [if_pos (⟨hb, hc.2⟩ : _ ∧ _), if_pos hb]
        · rw [if_neg fun h => hb h.1, if_neg hb]
      rw [Finset.sum_congr rfl hrw]
      exact one_le_band_sum (ℓ + 1) _ hc.1 M (hFbd s.2.1)
    · rw [if_neg hc]
      exact Finset.sum_nonneg fun k _ => by split <;> norm_num
  have hQ'1 : D.pair Φ (D.activeF ℓ θ) (D.hiWloV ℓ)
      ≤ ∑ k ∈ Finset.range M, D.pair Φ (D.activeF ℓ θ) (D.crossInd ℓ (k + 1)) := by
    rw [← D.pair_sum]
    exact D.pair_mono hθ Φ _ hpt
  have hQ'2 : ∀ k ∈ Finset.range M,
      D.pair Φ (D.activeF ℓ θ) (D.crossInd ℓ (k + 1))
        ≤ Real.exp (1 - alphaC) * (Real.exp (-((k : ℝ) + 1))
            * D.Aband Φ (D.activeF ℓ θ) (ℓ + (k : ℝ) + 1)) := by
    intro k _
    have hbc := D.band_crossing_le hℓ hθ0 hθ Φ (k + 1)
    rw [D.crossInd_pair] at hbc
    rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring] at hbc
    rw [show ℓ + ((k : ℝ) + 1) = ℓ + (k : ℝ) + 1 by ring] at hbc
    rw [mul_assoc] at hbc
    exact hbc
  have hQ'3 : ∑ k ∈ Finset.range M, (Real.exp (-((k : ℝ) + 1))
        * D.Aband Φ (D.activeF ℓ θ) (ℓ + (k : ℝ) + 1))
      ≤ ∑' j : ℕ, Real.exp (-((j : ℝ) + 1))
          * D.Aband Φ (D.activeF ℓ θ) (ℓ + (j : ℝ) + 1) :=
    Summable.sum_le_tsum _
      (fun i _ => mul_nonneg (Real.exp_pos _).le (D.Aband_nonneg hθ0 hθ Φ _ _))
      (D.Aband_summable hℓ hθ0 hθ Φ (D.activeF ℓ θ))
  have hQ' : D.pair Φ (D.activeF ℓ θ) (D.hiWloV ℓ)
      ≤ Real.exp (1 - alphaC) * (∑' j : ℕ, Real.exp (-((j : ℝ) + 1))
          * D.Aband Φ (D.activeF ℓ θ) (ℓ + (j : ℝ) + 1)) := by
    calc D.pair Φ (D.activeF ℓ θ) (D.hiWloV ℓ)
        ≤ ∑ k ∈ Finset.range M,
            D.pair Φ (D.activeF ℓ θ) (D.crossInd ℓ (k + 1)) := hQ'1
      _ ≤ ∑ k ∈ Finset.range M, Real.exp (1 - alphaC) *
            (Real.exp (-((k : ℝ) + 1))
              * D.Aband Φ (D.activeF ℓ θ) (ℓ + (k : ℝ) + 1)) :=
          Finset.sum_le_sum hQ'2
      _ = Real.exp (1 - alphaC) * ∑ k ∈ Finset.range M,
            (Real.exp (-((k : ℝ) + 1))
              * D.Aband Φ (D.activeF ℓ θ) (ℓ + (k : ℝ) + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ'3 (Real.exp_pos _).le
  linarith

end Dat

end Talagrand
