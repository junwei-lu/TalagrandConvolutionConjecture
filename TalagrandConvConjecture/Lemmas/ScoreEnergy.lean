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

open Classical

/-! ## Private toolbox -/

private lemma startW_nonneg' (θ : ℝ) (hθ : θ ≤ obsT) (x₀ : Cube n) :
    0 ≤ D.startW θ x₀ := by
  have hT : 0 ≤ D.T - θ := by have := D.obsT_lt_T; linarith
  have hpos := D.fs_pos hT x₀
  simp only [startW, revDensity]
  exact div_nonneg hpos.le (by positivity)

/-- Grid nodes are monotone in the weak sense used throughout. -/
private lemma grid_le {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) :
    ∀ m j, j ≤ m → m ≤ K → z j ≤ z m := by
  intro m
  induction m with
  | zero => intro j hj _; rw [Nat.le_zero.mp hj]
  | succ p ih =>
    intro j hj hpK
    rcases Nat.eq_or_lt_of_le hj with h | h
    · rw [h]
    · have hjp : j ≤ p := Nat.lt_succ_iff.mp h
      exact le_trans (ih j hjp (Nat.le_of_succ_le hpK))
        (hg.mono p (Nat.lt_of_succ_le hpK))

private lemma grid_le_obsT {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) : ∀ j, j ≤ K → z j ≤ obsT := by
  intro j hj
  rw [← hg.last]
  exact D.grid_le hg K j hj le_rfl

/-- A continuous function with no interior zero keeps the (weak) sign it has at
the midpoint. -/
private lemma nonneg_of_mid_nonneg {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hne : ∀ t ∈ Set.Ioo a b, φ t ≠ 0)
    (hmid : 0 ≤ φ ((a + b) / 2)) : ∀ t ∈ Set.Icc a b, 0 ≤ φ t := by
  rcases eq_or_lt_of_le hab with hab' | hab'
  · intro t ht
    have h1 := ht.1
    have h2 := ht.2
    have htv : t = (a + b) / 2 := by linarith
    rw [htv]; exact hmid
  · intro t ht
    by_contra hneg
    push_neg at hneg
    have hmidmem : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    have hmidpos : 0 < φ ((a + b) / 2) :=
      lt_of_le_of_ne hmid (Ne.symm (hne _ hmidmem))
    have hsub : Set.uIcc t ((a + b) / 2) ⊆ Set.Icc a b :=
      Set.uIcc_subset_Icc ht ⟨le_of_lt hmidmem.1, le_of_lt hmidmem.2⟩
    obtain ⟨t₀, ht₀mem, ht₀⟩ := intermediate_value_uIcc (hcont.mono hsub)
      (Set.mem_uIcc.mpr (Or.inl ⟨hneg.le, hmidpos.le⟩))
    have hne1 : t₀ ≠ t := fun h => by rw [h] at ht₀; linarith
    have hne2 : t₀ ≠ (a + b) / 2 := fun h => by rw [h] at ht₀; linarith
    have hIoo : t₀ ∈ Set.Ioo a b := by
      rcases Set.mem_uIcc.mp ht₀mem with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact ⟨lt_of_le_of_lt ht.1 (lt_of_le_of_ne hl (Ne.symm hne1)),
          lt_of_lt_of_le (lt_of_le_of_ne hr hne2) (le_of_lt hmidmem.2)⟩
      · exact ⟨lt_trans hmidmem.1 (lt_of_le_of_ne hl (Ne.symm hne2)),
          lt_of_lt_of_le (lt_of_le_of_ne hr hne1) ht.2⟩
    exact hne t₀ hIoo ht₀

/-- Inside a cell of an admissible grid the barrier is "closed": a point of the
cell barrier stays above the level throughout the closed cell. -/
private lemma cell_F_ge {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k < K) (hzT : z (k + 1) ≤ D.T)
    {x : Cube n} (hx : x ∈ D.barrier ℓ ((z k + z (k + 1)) / 2))
    {t : ℝ} (ht : t ∈ Set.Icc (z k) (z (k + 1))) : ℓ + 1 ≤ D.F t x := by
  simp only [barrier, Set.mem_setOf_eq] at hx
  have hsub : Set.Icc (z k) (z (k + 1)) ⊆ Set.Iic D.T := fun s hs =>
    le_trans hs.2 hzT
  have hφ := nonneg_of_mid_nonneg (φ := fun t => D.F t x - (ℓ + 1))
    (hg.mono k hk) (((D.continuousOn_F x).mono hsub).sub continuousOn_const)
    (fun s hs h => hg.nocross k hk s hs x (by linarith))
    (by linarith) t ht
  linarith

/-- Complementary form: off the cell barrier, `F` stays below the level
throughout the closed cell. -/
private lemma cell_F_le {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k < K) (hzT : z (k + 1) ≤ D.T)
    {x : Cube n} (hx : x ∉ D.barrier ℓ ((z k + z (k + 1)) / 2))
    {t : ℝ} (ht : t ∈ Set.Icc (z k) (z (k + 1))) : D.F t x ≤ ℓ + 1 := by
  simp only [barrier, Set.mem_setOf_eq, not_le] at hx
  have hsub : Set.Icc (z k) (z (k + 1)) ⊆ Set.Iic D.T := fun s hs =>
    le_trans hs.2 hzT
  have hφ := nonneg_of_mid_nonneg (φ := fun t => (ℓ + 1) - D.F t x)
    (hg.mono k hk) (continuousOn_const.sub ((D.continuousOn_F x).mono hsub))
    (fun s hs h => hg.nocross k hk s hs x (by linarith))
    (by linarith) t ht
  linarith

/-- All jump rates of the stopped power coupling are nonnegative. -/
private lemma jrate_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (Bset : Set (Cube n)) {t : ℝ} (ht : t ≤ D.T) (s s' : JSt n) :
    0 ≤ D.jrate d Bset t s s' := by
  obtain ⟨x, y, b⟩ := s
  obtain ⟨x', y', b'⟩ := s'
  simp only [jrate]
  refine Finset.sum_nonneg fun i _ => ?_
  have hY : 0 < D.Y t i x := D.Y_pos ht i x
  have h1 : (0 : ℝ) ≤ D.Y t i x / 2 := by linarith
  have h2 : (0 : ℝ) ≤ D.Y t i x ^ (1 - d) / 2 := by
    have := Real.rpow_pos_of_pos hY (1 - d)
    linarith
  have h3 : D.Y t i x < 1 → (0 : ℝ) ≤ (1 - D.Y t i x ^ d) / 2 := by
    intro hlt
    have := Real.rpow_le_one hY.le hlt.le hd0
    linarith
  have h4 : ¬(D.Y t i x < 1) → (0 : ℝ) ≤ (D.Y t i x - D.Y t i x ^ (1 - d)) / 2 := by
    intro hge
    have h1Y : (1 : ℝ) ≤ D.Y t i x := not_lt.mp hge
    have hle : D.Y t i x ^ (1 - d) ≤ D.Y t i x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1Y (by linarith)
    rw [Real.rpow_one] at hle
    linarith
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · split_ifs <;> first | exact h1 | exact h2 | exact le_rfl
  · split_ifs with hc
    · exact h3 hc.2.2.2.2
    · exact le_rfl
  · split_ifs with hc
    · exact h4 hc.2.2.2.1
    · exact le_rfl

/-- No jump can bring mass into an *alive* state sitting on the cell barrier,
except from an alive state already on the cell barrier (a `W`-only flip). -/
private lemma jrate_eq_zero_of_influx {d : ℝ} (Bset : Set (Cube n)) (t : ℝ)
    (x y : Cube n) (b : Bool) (x' y' : Cube n) (hx' : x' ∈ Bset)
    (hs : ¬(b = true ∧ x ∈ Bset)) :
    D.jrate d Bset t (x, y, b) (x', y', true) = 0 := by
  have hdec : decide (x' ∉ Bset) = false := decide_eq_false (not_not_intro hx')
  by_cases hxx : x' = x
  · have hb : b = false := by
      cases b with
      | false => rfl
      | true => exact absurd (hxx ▸ hx') (fun hmem => hs ⟨rfl, hmem⟩)
    subst hb
    simp only [jrate]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp
  · simp only [jrate]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hdec, hxx]

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
  have hκ : 1 < kappa D.a := one_lt_kappa D.ha0 D.ha1
  have hL : 0 < Real.log (kappa D.a) := Real.log_pos hκ
  have hL0 : Real.log (kappa D.a) ≠ 0 := ne_of_gt hL
  have hκ0 : kappa D.a ≠ 0 := by positivity
  have hκ1 : kappa D.a - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; simp [h] at hκ
  simp only [SA]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x₀ hx₀ => ?_
  have hact : 2 * alphaC ≤ D.Rgap ℓ θ x₀ := by
    have hmem := hA hx₀
    simp only [activeF, Finset.mem_filter] at hmem
    exact hmem.2
  have hRnn := D.Rgap_nonneg ℓ θ x₀
  have hR : (0 : ℝ) < D.Rgap ℓ θ x₀ + 1 := by linarith
  have hR0 : D.Rgap ℓ θ x₀ + 1 ≠ 0 := ne_of_gt hR
  have hdb : D.dbar ℓ θ x₀ = alphaC / (D.Rgap ℓ θ x₀ + 1) := by
    simp only [dbar]
    rw [if_pos hact]
  have hw := D.startW_nonneg' θ hθ x₀
  have hstep : D.startW θ x₀ * D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀)
      ≤ D.startW θ x₀ * D.dbar ℓ θ x₀ ^ 2 *
        ((kappa D.a - 1) / Real.log (kappa D.a)
          * (D.Rgap ℓ θ x₀ + 1 + Real.log (kappa D.a))) :=
    mul_le_mul_of_nonneg_left (D.scoreEnergy_le hℓ hθ0 hθ (Φ x₀))
      (mul_nonneg hw (sq_nonneg _))
  refine le_trans hstep ?_
  rw [hdb]
  simp only [alphaC, Lam]
  field_simp
  nlinarith [hw, hκ, sq_nonneg (kappa D.a)]

/-- Nonnegativity of the score energy. -/
lemma scoreEnergy_nonneg {ℓ θ : ℝ} (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) : 0 ≤ D.scoreEnergy c := by
  refine Finset.sum_nonneg fun k hk => ?_
  have hk' : k < c.K := Finset.mem_range.mp hk
  refine intervalIntegral.integral_nonneg (c.is.grid.mono k hk') ?_
  intro t ht
  refine Finset.sum_nonneg fun s _ => ?_
  by_cases hb : s.2.2
  · rw [if_pos hb]
    exact mul_nonneg (D.cflow_nonneg hθ c hk' ht s)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · rw [if_neg hb]

lemma SA_nonneg {ℓ θ : ℝ} (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) : 0 ≤ D.SA Φ A := by
  refine Finset.sum_nonneg fun x₀ _ => ?_
  exact mul_nonneg (mul_nonneg (D.startW_nonneg' θ hθ x₀) (sq_nonneg _))
    (D.scoreEnergy_nonneg hθ (Φ x₀))

end Dat

end Talagrand
