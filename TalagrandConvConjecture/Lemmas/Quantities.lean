import TalagrandConvConjecture.Flow.Coupling
import TalagrandConvConjecture.Profile

/-!
# The localized quantities of [LGF §3]

Given data `D`, level `ℓ`, start time `θ`, and a family `Φ` of coupling
flows (one per starting point), this file defines, for `A` a set of starting
points (all events of [LGF §3] are `V_θ`-measurable, i.e. sets of starting
points; `𝔼[1_A ·] = ∑_{x₀∈A} ν_{T-θ}(x₀)·𝔼_{x₀}[·]`):

* `startW D θ x₀ = ν_{T-θ}({x₀})` — the law of `V_θ`;
* `probA` = `ℙ(A)`;
* `scoreEnergy c` — `𝔼_{x₀}∫_θ^τ ∑_i S_i(t,V_t)² dt` for one flow `c`;
* `SA` — the stopped score energy `𝒮_A` [LGF eq (3.3)];
* `DtestF c B` — `𝔼_{x₀}[1_B(W_{T_o}) - 1_B(V_{T_o})]`;
* `DA` — the localized total variation `D_A` [LGF eq (3.3)], defined as the
  half-`L¹` distance (equal to the sup over test sets, see `abs_Dtest_le_DA`);
* `Aband`/`Bband` — the terminal band masses `A_θ(r)`, `B_θ(r)`
  [LGF Lemma 3.4];
* the active set `activeF = ℰ_θ` as a `Finset`.
-/

namespace Talagrand

namespace Dat

variable {n : ℕ} (D : Dat n)

open Classical

/-- Law of `V_θ`: `startW θ x₀ = ν_{T-θ}({x₀}) = f_{T-θ}(x₀)/2^n`. -/
noncomputable def startW (θ : ℝ) (x₀ : Cube n) : ℝ := D.revDensity θ x₀

/-- `ℙ(V_θ ∈ A)`. -/
noncomputable def probA (θ : ℝ) (A : Finset (Cube n)) : ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀

/-- The active event `ℰ_θ = {R_θ ≥ 2α}` as a `Finset` [LGF eq (3.2)]. -/
noncomputable def activeF (ℓ θ : ℝ) : Finset (Cube n) :=
  Finset.univ.filter fun x₀ => 2 * alphaC ≤ D.Rgap ℓ θ x₀

/-- Alive-sector score energy of one coupling flow:
`𝔼_{x₀}[∫_θ^τ ∑_i S_i(t,V_{t-})² dt]` [LGF eq (3.3), inner integral]. -/
noncomputable def scoreEnergy {ℓ θ : ℝ} {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) :
    ℝ :=
  ∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
    ∑ s : JSt n, (if s.2.2 then c.π k t s * ∑ i, D.Sc t i s.1 ^ 2 else 0)

/-- The stopped score energy `𝒮_A = 𝔼[1_A δ̄² ∫_θ^τ ∑_i S_i² dt]`
[LGF eq (3.3)]. -/
noncomputable def SA {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) :
    ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀ * D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀)

/-- Signed terminal test discrepancy for one flow:
`𝔼_{x₀}[1_B(W_{T_o})] - 𝔼_{x₀}[1_B(V_{T_o})]`. -/
noncomputable def DtestF {ℓ θ : ℝ} {x₀ : Cube n} (c : D.CFlow ℓ θ x₀)
    (B : Finset (Cube n)) : ℝ :=
  ∑ s : JSt n, c.term s *
    ((if s.2.1 ∈ B then (1 : ℝ) else 0) - (if s.1 ∈ B then (1 : ℝ) else 0))

/-- The localized total variation distance `D_A` [LGF eq (3.3)], as the
half-`L¹` distance between the `A`-localized terminal laws of `W` and `V`. -/
noncomputable def DA {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) :
    ℝ :=
  (∑ w : Cube n, |∑ x₀ ∈ A, D.startW θ x₀ *
    (∑ s : JSt n, (Φ x₀).term s *
      ((if s.2.1 = w then (1 : ℝ) else 0) - (if s.1 = w then (1 : ℝ) else 0)))|)
    / 2

/-! ## Private toolbox: half-`L¹` distance as a sup over test sets -/

section HalfL1

variable {α : Type*} [Fintype α]

private lemma abs_eq_pos_add_neg (r : ℝ) : |r| = max r 0 + max (-r) 0 := by
  rcases le_total 0 r with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : -r ≤ 0)]
    ring
  · rw [abs_of_nonpos h, max_eq_right h,
      max_eq_left (by linarith : (0 : ℝ) ≤ -r)]
    ring

private lemma max_sub_max_neg (r : ℝ) : max r 0 - max (-r) 0 = r := by
  rcases le_total 0 r with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -r ≤ 0)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -r)]; ring

/-- With total sum zero, the positive part carries exactly half the `L¹`
mass. -/
private lemma sum_pos_part_eq (g : α → ℝ) (h0 : ∑ w, g w = 0) :
    ∑ w, max (g w) 0 = (∑ w, |g w|) / 2 := by
  have h1 : ∑ w, |g w| = (∑ w, max (g w) 0) + ∑ w, max (-(g w)) 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => abs_eq_pos_add_neg (g w)
  have h2 : ∑ w, (max (g w) 0 - max (-(g w)) 0) = 0 := by
    have hpt : ∀ w, max (g w) 0 - max (-(g w)) 0 = g w := fun w =>
      max_sub_max_neg (g w)
    simp only [hpt]
    exact h0
  rw [Finset.sum_sub_distrib] at h2
  linarith

private lemma sum_le_sum_pos_part (g : α → ℝ) (B : Finset α) :
    ∑ w ∈ B, g w ≤ ∑ w, max (g w) 0 :=
  le_trans (Finset.sum_le_sum fun w _ => le_max_left (g w) 0)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      fun w _ _ => le_max_right _ _)

/-- Classical half-`L¹` bound: for a mean-zero signed weight, every test set
picks up at most half the total variation. -/
private lemma abs_sum_le_half_sum_abs (g : α → ℝ) (h0 : ∑ w, g w = 0)
    (B : Finset α) : |∑ w ∈ B, g w| ≤ (∑ w, |g w|) / 2 := by
  have hneg : ∑ w, (-(g w)) = 0 := by simp [h0]
  have hP := sum_pos_part_eq g h0
  have hN := sum_pos_part_eq (fun w => -(g w)) hneg
  simp only [abs_neg] at hN
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 := sum_le_sum_pos_part (fun w => -(g w)) B
    rw [hN] at h1
    have hs : ∑ w ∈ B, (-(g w)) = -∑ w ∈ B, g w := by simp
    rw [hs] at h1
    linarith
  · have h1 := sum_le_sum_pos_part g B
    rw [hP] at h1
    linarith

/-- The half-`L¹` bound is attained at `B = {g > 0}`. -/
private lemma exists_abs_sum_eq_half (g : α → ℝ) (h0 : ∑ w, g w = 0) :
    ∃ B : Finset α, (∑ w, |g w|) / 2 = |∑ w ∈ B, g w| := by
  classical
  refine ⟨Finset.univ.filter fun w => 0 < g w, ?_⟩
  have hsum : ∑ w ∈ Finset.univ.filter (fun w => 0 < g w), g w
      = ∑ w, max (g w) 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : 0 < g w
    · rw [if_pos h, max_eq_left h.le]
    · rw [if_neg h, max_eq_right (not_lt.mp h)]
  rw [hsum, abs_of_nonneg (Finset.sum_nonneg fun w _ => le_max_right (g w) 0),
    sum_pos_part_eq g h0]

end HalfL1

/-! ## Private toolbox: the signed terminal discrepancy density -/

/-- Signed terminal `W`-minus-`V` discrepancy density localized on `A`; `DA`
is half its `L¹` norm. -/
private noncomputable def dmass {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (w : Cube n) : ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀ *
    (∑ s : JSt n, (Φ x₀).term s *
      ((if s.2.1 = w then (1 : ℝ) else 0) - (if s.1 = w then (1 : ℝ) else 0)))

private lemma DA_eq_half {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) :
    D.DA Φ A = (∑ w : Cube n, |D.dmass Φ A w|) / 2 := rfl

private lemma sum_dmass_eq_zero {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) : ∑ w : Cube n, D.dmass Φ A w = 0 := by
  simp only [dmass]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x₀ _ => ?_
  rw [← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  rw [Finset.sum_sub_distrib]
  simp

private lemma dtest_eq_sum_dmass {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A B : Finset (Cube n)) :
    ∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B
      = ∑ w ∈ B, D.dmass Φ A w := by
  have key : ∀ x₀ : Cube n, D.startW θ x₀ * D.DtestF (Φ x₀) B
      = ∑ w ∈ B, D.startW θ x₀ *
        (∑ s : JSt n, (Φ x₀).term s *
          ((if s.2.1 = w then (1 : ℝ) else 0)
            - (if s.1 = w then (1 : ℝ) else 0))) := by
    intro x₀
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [DtestF]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp
  calc ∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B
      = ∑ x₀ ∈ A, ∑ w ∈ B, D.startW θ x₀ *
          (∑ s : JSt n, (Φ x₀).term s *
            ((if s.2.1 = w then (1 : ℝ) else 0)
              - (if s.1 = w then (1 : ℝ) else 0))) :=
        Finset.sum_congr rfl fun x₀ _ => key x₀
    _ = ∑ w ∈ B, D.dmass Φ A w := Finset.sum_comm

/-- Every test set is dominated by `D_A`:
`|ℙ(A, W_{T_o} ∈ B) - ℙ(A, V_{T_o} ∈ B)| ≤ D_A` [LGF eq (3.3)]. -/
theorem abs_Dtest_le_DA {ℓ θ : ℝ} (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ)
    (A B : Finset (Cube n)) :
    |∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B| ≤ D.DA Φ A := by
  rw [D.dtest_eq_sum_dmass Φ A B, D.DA_eq_half Φ A]
  exact abs_sum_le_half_sum_abs _ (D.sum_dmass_eq_zero Φ A) B

/-- `D_A` is attained by some test set (finite optimal test
`B* = {w : ν w < μ w}`). -/
theorem exists_DA_eq {ℓ θ : ℝ} (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) :
    ∃ B : Finset (Cube n),
      D.DA Φ A = |∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B| := by
  obtain ⟨B, hB⟩ := exists_abs_sum_eq_half _ (D.sum_dmass_eq_zero Φ A)
  refine ⟨B, ?_⟩
  rw [D.DA_eq_half Φ A, D.dtest_eq_sum_dmass Φ A B]
  exact hB

/-- Subadditivity of `D` over a disjoint decomposition of `A`
[LGF, proof of Prop 3.2, Step 1]. -/
theorem DA_biUnion_le {ℓ θ : ℝ} (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (E : ι → Finset (Cube n))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (E i) (E j)) :
    D.DA Φ (I.biUnion E) ≤ ∑ i ∈ I, D.DA Φ (E i) := by
  have hpair : (I : Set ι).PairwiseDisjoint E := fun i hi j hj hij =>
    hdisj i hi j hj hij
  have hsplit : ∀ w : Cube n,
      D.dmass Φ (I.biUnion E) w = ∑ i ∈ I, D.dmass Φ (E i) w := by
    intro w
    simp only [dmass]
    exact Finset.sum_biUnion hpair
  have hle : ∑ w : Cube n, |D.dmass Φ (I.biUnion E) w|
      ≤ ∑ w : Cube n, ∑ i ∈ I, |D.dmass Φ (E i) w| := by
    refine Finset.sum_le_sum fun w _ => ?_
    rw [hsplit w]
    exact Finset.abs_sum_le_sum_abs _ _
  have hswap : ∑ i ∈ I, D.DA Φ (E i)
      = (∑ w : Cube n, ∑ i ∈ I, |D.dmass Φ (E i) w|) / 2 := by
    rw [Finset.sum_comm]
    simp only [D.DA_eq_half]
    rw [← Finset.sum_div]
  rw [D.DA_eq_half Φ (I.biUnion E), hswap]
  linarith

/-! ## Private toolbox: transport of the reverse generator -/

/-- Matrix of the reverse generator, `matVec (revMat t) g = revGen t g`. -/
private noncomputable def revMat (t : ℝ) (x x' : Cube n) : ℝ :=
  (∑ i, if x' = flipCoord i x then D.Y t i x / 2 else 0)
    - (if x' = x then ∑ i, D.Y t i x / 2 else 0)

private lemma matVec_revMat (t : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    matVec (D.revMat t) g x = D.revGen t g x := by
  have h1 : ∀ x' : Cube n, D.revMat t x x' * g x'
      = (∑ i, if x' = flipCoord i x then D.Y t i x / 2 * g x' else 0)
        - (if x' = x then (∑ i, D.Y t i x / 2) * g x' else 0) := by
    intro x'
    simp only [revMat, sub_mul, Finset.sum_mul, ite_mul, zero_mul]
  simp only [matVec, h1]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [revGen]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma revFwdMat_eq_revMat (t : ℝ) (x x' : Cube n) :
    D.revFwdMat t x x' = D.revMat t x' x := by
  by_cases h : x = x'
  · subst h; rfl
  · simp only [revFwdMat, revMat, if_neg h]

/-- Transposition of the forward matrix against the generator. -/
private lemma pairing_transpose (t : ℝ) (v g : Cube n → ℝ) :
    ∑ x : Cube n, (∑ x', D.revFwdMat t x x' * v x') * g x
      = ∑ x : Cube n, v x * D.revGen t g x := by
  have hmul : ∀ x : Cube n, (∑ x', D.revFwdMat t x x' * v x') * g x
      = ∑ x', D.revFwdMat t x x' * v x' * g x := fun x => Finset.sum_mul _ _ _
  simp only [hmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [← D.matVec_revMat t g x']
  simp only [matVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [D.revFwdMat_eq_revMat]
  ring

private lemma continuousOn_ite_const {α : Type*} [TopologicalSpace α]
    {c : Prop} [Decidable c] {F : α → ℝ} {s : Set α} (hF : ContinuousOn F s) :
    ContinuousOn (fun t => if c then F t else 0) s := by
  by_cases h : c
  · simpa [h] using hF
  · simpa [h] using (continuousOn_const : ContinuousOn (fun _ : α => (0 : ℝ)) s)

private lemma continuousOn_revMat (x x' : Cube n) :
    ContinuousOn (fun t => D.revMat t x x') (Set.Iic D.T) := by
  refine ContinuousOn.sub ?_ ?_
  · refine continuousOn_finset_sum _ fun i _ => ?_
    exact continuousOn_ite_const ((D.continuousOn_Y i x).div_const 2)
  · refine continuousOn_ite_const ?_
    exact continuousOn_finset_sum _ fun i _ => (D.continuousOn_Y i x).div_const 2

/-- A real function with vanishing derivative within a compact interval is
constant there. -/
private lemma const_of_hasDerivWithinAt_zero {a b : ℝ} {P : ℝ → ℝ}
    (h : ∀ t ∈ Set.Icc a b, HasDerivWithinAt P 0 (Set.Icc a b) t)
    {t₁ t₂ : ℝ} (h1 : t₁ ∈ Set.Icc a b) (h2 : t₂ ∈ Set.Icc a b) :
    P t₁ = P t₂ := by
  have hb := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun _ : ℝ => (0 : ℝ)) (C := 0) (fun t ht => h t ht)
    (fun t _ => by simp) h1 h2
  have h0 : |P t₂ - P t₁| ≤ 0 := by simpa using hb
  have := abs_nonpos_iff.mp h0
  linarith

/-! ## Private toolbox: the terminal `V`-law is the profile -/

private lemma startW_nonneg (θ : ℝ) (hθ : θ ≤ obsT) (x₀ : Cube n) :
    0 ≤ D.startW θ x₀ := by
  have hT : 0 ≤ D.T - θ := by have := D.obsT_lt_T; linarith
  have hpos := D.fs_pos hT x₀
  simp only [startW, revDensity]
  exact div_nonneg hpos.le (by positivity)

private lemma term_nonneg {ℓ θ : ℝ} {x₀ : Cube n} (hθ : θ ≤ obsT)
    (c : D.CFlow ℓ θ x₀) (s : JSt n) : 0 ≤ c.term s := by
  have hK : 0 < c.K := c.is.grid.pos
  have hk : c.K - 1 < c.K := Nat.sub_lt hK Nat.one_pos
  have hsucc : c.K - 1 + 1 = c.K := Nat.succ_pred_eq_of_pos hK
  have hmono : c.z (c.K - 1) ≤ c.z (c.K - 1 + 1) := c.is.grid.mono _ hk
  have hlast : c.z c.K = obsT := c.is.grid.last
  refine D.cflow_nonneg hθ c hk (t := obsT) ?_ s
  rw [hsucc, hlast]
  refine ⟨?_, le_refl _⟩
  rw [hsucc, hlast] at hmono
  exact hmono

/-- The `V`-terminal law of the whole family is the profile of the start-time
layer: private copy of `sum_term_V_eq_profile` (stated with `Set.indicator` so
that no decidability instance has to be matched at the use sites). -/
private theorem sum_term_V_eq_profile' {ℓ θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ) (I : Set ℝ) :
    ∑ x₀ : Cube n, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
        I.indicator (fun _ => (1 : ℝ)) (D.F obsT s.1)
      = profile D.f D.tA I := by
  have hTθ : θ ≤ D.T := le_trans hθ (le_of_lt D.obsT_lt_T)
  -- (1) the backward harmonic extension of the terminal indicator
  obtain ⟨w, hw, hw0⟩ := exists_linFlow (S := Cube n)
    (fun r => D.revMat (θ + obsT - r)) hθ
    (fun x x' => by
      refine ContinuousOn.comp (D.continuousOn_revMat x x')
        (Continuous.continuousOn (by continuity)) ?_
      intro r hr
      have : θ + obsT - r ≤ obsT := by
        have := hr.1; linarith
      exact le_trans this (le_of_lt D.obsT_lt_T))
    (fun x => I.indicator (fun _ => (1 : ℝ)) (D.F obsT x))
  set g : ℝ → Cube n → ℝ := fun t x => w (θ + obsT - t) x with hgdef
  have hmaps : Set.MapsTo (fun t : ℝ => θ + obsT - t) (Set.Icc θ obsT)
      (Set.Icc θ obsT) := by
    intro t ht
    exact ⟨by have := ht.2; linarith, by have := ht.1; linarith⟩
  have hgcont : ∀ x, ContinuousOn (fun t => g t x) (Set.Icc θ obsT) := by
    intro x
    exact ContinuousOn.comp (hw.cont x)
      (Continuous.continuousOn (by continuity)) hmaps
  have hgderiv : ∀ x, ∀ t ∈ Set.Icc θ obsT,
      HasDerivWithinAt (fun t => g t x) (-(D.revGen t (g t) x))
        (Set.Icc θ obsT) t := by
    intro x t ht
    have h1 := hw.deriv x (θ + obsT - t) (hmaps ht)
    have harg : θ + obsT - (θ + obsT - t) = t := by ring
    rw [harg] at h1
    have h2 : HasDerivWithinAt (fun t : ℝ => θ + obsT - t) (-1)
        (Set.Icc θ obsT) t :=
      (hasDerivWithinAt_id t (Set.Icc θ obsT)).const_sub (θ + obsT)
    have h3 := HasDerivWithinAt.comp t h1 h2 hmaps
    have h4 : matVec (D.revMat t) (w (θ + obsT - t)) x
        = D.revGen t (g t) x := D.matVec_revMat t (g t) x
    rw [h4] at h3
    simpa [Function.comp, hgdef, mul_comm] using h3
  -- (2) the marginal identity, per starting point
  have hmarg : ∀ x₀ : Cube n,
      ∑ s : JSt n, (Φ x₀).term s * g obsT s.1 = g θ x₀ :=
    fun x₀ => D.cflow_V_marginal hθ0 hθ (Φ x₀) g hgcont hgderiv
  have hgobs : ∀ x : Cube n, g obsT x = I.indicator (fun _ => (1 : ℝ))
      (D.F obsT x) := by
    intro x
    have : θ + obsT - obsT = θ := by ring
    simp only [hgdef, this]
    rw [hw0]
  -- (3) the pairing with the explicit forward density is constant
  have hPderiv : ∀ t ∈ Set.Icc θ obsT,
      HasDerivWithinAt (fun t => ∑ x : Cube n, D.revDensity t x * g t x) 0
        (Set.Icc θ obsT) t := by
    intro t ht
    have hT : t ≤ D.T := le_trans ht.2 (le_of_lt D.obsT_lt_T)
    have hterm : ∀ x : Cube n,
        HasDerivWithinAt (fun t => D.revDensity t x * g t x)
          ((∑ x', D.revFwdMat t x x' * D.revDensity t x') * g t x
            + D.revDensity t x * -(D.revGen t (g t) x))
          (Set.Icc θ obsT) t := fun x =>
      ((D.hasDerivAt_revDensity hT x).hasDerivWithinAt).mul (hgderiv x t ht)
    have hsum := HasDerivWithinAt.sum (u := (Finset.univ : Finset (Cube n)))
      (fun x _ => hterm x)
    have hzero : ∑ x : Cube n,
        ((∑ x', D.revFwdMat t x x' * D.revDensity t x') * g t x
          + D.revDensity t x * -(D.revGen t (g t) x)) = 0 := by
      have hneg : ∑ x : Cube n, D.revDensity t x * -(D.revGen t (g t) x)
          = -∑ x : Cube n, D.revDensity t x * D.revGen t (g t) x := by
        simp [mul_neg]
      rw [Finset.sum_add_distrib, D.pairing_transpose t (D.revDensity t) (g t),
        hneg]
      ring
    have hfun : (∑ i : Cube n, fun t => D.revDensity t i * g t i)
        = fun t => ∑ x : Cube n, D.revDensity t x * g t x := by
      funext t; simp
    rw [← hzero, ← hfun]
    exact hsum
  have hconst := const_of_hasDerivWithinAt_zero hPderiv
    (Set.left_mem_Icc.mpr hθ) (Set.right_mem_Icc.mpr hθ)
  -- (4) assemble
  have hstart : ∑ x₀ : Cube n, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
      I.indicator (fun _ => (1 : ℝ)) (D.F obsT s.1)
      = ∑ x : Cube n, D.revDensity θ x * g θ x := by
    refine Finset.sum_congr rfl fun x₀ _ => ?_
    have : ∑ s : JSt n, (Φ x₀).term s *
        I.indicator (fun _ => (1 : ℝ)) (D.F obsT s.1) = g θ x₀ := by
      rw [← hmarg x₀]
      exact Finset.sum_congr rfl fun s _ => by rw [hgobs s.1]
    rw [this]
    rfl
  rw [hstart, hconst]
  -- (5) the terminal pairing is the profile
  have htA : D.T - obsT = D.tA := by simp [Dat.T]
  have hfin : ∀ x : Cube n, D.revDensity obsT x * g obsT x
      = I.indicator (fun _ => heatAt D.f D.tA x)
          (Real.log (heatAt D.f D.tA x)) / 2 ^ n := by
    intro x
    rw [hgobs x]
    have hd : D.revDensity obsT x = heatAt D.f D.tA x / 2 ^ n := by
      simp only [revDensity, htA, fs]
    have hF : D.F obsT x = Real.log (heatAt D.f D.tA x) := by
      simp only [F, htA, fs]
    rw [hd, hF]
    by_cases h : Real.log (heatAt D.f D.tA x) ∈ I
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      ring
  simp only [hfin]
  rw [← Finset.sum_div]
  rfl

/-- Terminal `V`-band mass
`A_θ^{[A]}(r) = ℙ(V_θ ∈ A, F_{T_o}(V_{T_o}) ∈ (r, r+1])` [LGF Lemma 3.4]. -/
noncomputable def Aband {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (r : ℝ) : ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
    (if D.F obsT s.1 ∈ Set.Ioc r (r + 1) then (1 : ℝ) else 0)

/-- Terminal `W`-band mass
`B_θ^{[A]}(r) = ℙ(V_θ ∈ A, F_{T_o}(W_{T_o}) ∈ (r, r+1])` [LGF §4.3]. -/
noncomputable def Bband {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (r : ℝ) : ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
    (if D.F obsT s.2.1 ∈ Set.Ioc r (r + 1) then (1 : ℝ) else 0)

/-- `Aband` in `Set.indicator` form, matching `sum_term_V_eq_profile'`. -/
private lemma Aband_eq_indicator {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (r : ℝ) :
    D.Aband Φ A r = ∑ x₀ ∈ A, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
      (Set.Ioc r (r + 1)).indicator (fun _ => (1 : ℝ)) (D.F obsT s.1) := by
  simp only [Aband]
  refine Finset.sum_congr rfl fun x₀ _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : D.F obsT s.1 ∈ Set.Ioc r (r + 1)
  · rw [Set.indicator_of_mem h, if_pos h]
  · rw [Set.indicator_of_notMem h, if_neg h]

/-- Nonnegativity of band masses. -/
lemma Aband_nonneg {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) (r : ℝ) :
    0 ≤ D.Aband Φ A r := by
  refine Finset.sum_nonneg fun x₀ _ => mul_nonneg (D.startW_nonneg θ hθ x₀) ?_
  refine Finset.sum_nonneg fun s _ => mul_nonneg (D.term_nonneg hθ (Φ x₀) s) ?_
  split_ifs <;> norm_num

/-- Band masses are dominated by full-space profile mass:
`A_θ^{[A]}(r) ≤ 𝔄_{t_a}((r,r+1])` [LGF eq (3.14)]. -/
theorem Aband_le_profile {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) (r : ℝ) :
    D.Aband Φ A r ≤ profile D.f D.tA (Set.Ioc r (r + 1)) := by
  rw [D.Aband_eq_indicator Φ A r,
    ← D.sum_term_V_eq_profile' hθ0 hθ Φ (Set.Ioc r (r + 1))]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) ?_
  intro x₀ _ _
  refine mul_nonneg (D.startW_nonneg θ hθ x₀) ?_
  refine Finset.sum_nonneg fun s _ => mul_nonneg (D.term_nonneg hθ (Φ x₀) s) ?_
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- Splitting over the active partition:
`𝔄_{t_a}((ℓ,ℓ+1]) = A_θ^{[ℰ]}(ℓ) + A_θ^{[ℰᶜ]}(ℓ)` [LGF eq (3.14)]. -/
theorem profile_eq_Aband_add {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ) :
    profile D.f D.tA (Set.Ioc ℓ (ℓ + 1))
      = D.Aband Φ (D.activeF ℓ θ) ℓ + D.Aband Φ (D.activeF ℓ θ)ᶜ ℓ := by
  rw [D.Aband_eq_indicator Φ (D.activeF ℓ θ) ℓ,
    D.Aband_eq_indicator Φ (D.activeF ℓ θ)ᶜ ℓ,
    Finset.sum_add_sum_compl]
  exact (D.sum_term_V_eq_profile' hθ0 hθ Φ (Set.Ioc ℓ (ℓ + 1))).symm

/-- The start-weight sums are exactly profile masses of the start-time layer:
`∑_{x₀ : F_θ(x₀) ∈ I} ν_{T-θ}(x₀) = 𝔄_{T-θ}(I)` [LGF, Step 1 of Prop 3.2]. -/
theorem sum_startW_eq_profile (θ : ℝ) (I : Set ℝ) :
    ∑ x₀ ∈ Finset.univ.filter (fun x₀ => D.F θ x₀ ∈ I), D.startW θ x₀
      = profile D.f (D.T - θ) I := by
  rw [Finset.sum_filter]
  have hpt : ∀ x : Cube n, (if D.F θ x ∈ I then D.startW θ x else 0)
      = I.indicator (fun _ => heatAt D.f (D.T - θ) x)
          (Real.log (heatAt D.f (D.T - θ) x)) / 2 ^ n := by
    intro x
    have hd : D.startW θ x = heatAt D.f (D.T - θ) x / 2 ^ n := by
      simp only [startW, revDensity, fs]
    have hF : D.F θ x = Real.log (heatAt D.f (D.T - θ) x) := by
      simp only [F, fs]
    rw [hd, hF]
    by_cases h : Real.log (heatAt D.f (D.T - θ) x) ∈ I
    · rw [Set.indicator_of_mem h, if_pos h]
    · rw [Set.indicator_of_notMem h, if_neg h]
      simp
  simp only [hpt]
  rw [← Finset.sum_div]
  rfl

end Dat

end Talagrand
