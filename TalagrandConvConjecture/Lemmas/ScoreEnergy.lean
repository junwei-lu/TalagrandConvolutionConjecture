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

/-- **In-cell alive support**: on a cell whose rate table uses the barrier
`B`, alive mass never sits on `B`. The alive-and-barred sector receives no
in-flux (`jrate_eq_zero_of_influx`), so its total mass has nonpositive
derivative; starting at `0` and staying `≥ 0`, it is identically `0`. -/
private lemma cell_alive_zero' {d : ℝ} {B : Set (Cube n)} {a b : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hbT : b ≤ D.T) {π : ℝ → JSt n → ℝ}
    (hflow : IsLinFlow (fun t => fwdOf (D.jrate d B t)) a b π)
    (hnn : ∀ t ∈ Set.Icc a b, ∀ s : JSt n, 0 ≤ π t s)
    (h0 : ∀ s : JSt n, s.2.2 = true → s.1 ∈ B → π a s = 0) :
    ∀ t ∈ Set.Icc a b, ∀ s : JSt n, s.2.2 = true → s.1 ∈ B → π t s = 0 := by
  classical
  have hσnn : ∀ τ ∈ Set.Icc a b, ∀ s : JSt n,
      0 ≤ (if s.2.2 = true ∧ s.1 ∈ B then π τ s else 0) := by
    intro τ hτ s
    split_ifs with h
    · exact hnn τ hτ s
    · exact le_rfl
  have hcont : ContinuousOn (fun τ => ∑ s : JSt n,
      (if s.2.2 = true ∧ s.1 ∈ B then π τ s else 0)) (Set.Icc a b) := by
    refine continuousOn_finset_sum _ fun s _ => ?_
    by_cases hbs : s.2.2 = true ∧ s.1 ∈ B
    · simpa only [if_pos hbs] using hflow.cont s
    · simpa only [if_neg hbs] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc a b))
  have hderiv : ∀ τ ∈ Set.Icc a b,
      HasDerivWithinAt (fun τ => ∑ s : JSt n,
          (if s.2.2 = true ∧ s.1 ∈ B then π τ s else 0))
        (∑ s : JSt n, (if s.2.2 = true ∧ s.1 ∈ B then
          matVec (fwdOf (D.jrate d B τ)) (π τ) s else 0)) (Set.Icc a b) τ := by
    intro τ hτ
    refine hasDerivWithinAt_fintypeSum fun s => ?_
    by_cases hbs : s.2.2 = true ∧ s.1 ∈ B
    · simpa only [if_pos hbs] using hflow.deriv s τ hτ
    · simpa only [if_neg hbs] using hasDerivWithinAt_const τ (Set.Icc a b) (0 : ℝ)
  have hnonpos : ∀ τ ∈ Set.Icc a b,
      ∑ s : JSt n, (if s.2.2 = true ∧ s.1 ∈ B then
        matVec (fwdOf (D.jrate d B τ)) (π τ) s else 0) ≤ 0 := by
    intro τ hτ
    have hτT : τ ≤ D.T := le_trans hτ.2 hbT
    have hq0 : ∀ u v : JSt n, 0 ≤ D.jrate d B τ u v :=
      fun u v => D.jrate_nonneg hd0 hd1 B hτT u v
    have hw0 : ∀ u : JSt n, 0 ≤ π τ u := hnn τ hτ
    -- no in-flux into the alive-and-barred sector
    have hinflux : ∀ u s : JSt n, ¬(u.2.2 = true ∧ u.1 ∈ B) →
        (s.2.2 = true ∧ s.1 ∈ B) → D.jrate d B τ u s = 0 := by
      intro u s hu hs
      obtain ⟨x, y, bb⟩ := u
      obtain ⟨x', y', b'⟩ := s
      simp only at hs hu
      obtain ⟨hb', hx'⟩ := hs
      subst hb'
      exact D.jrate_eq_zero_of_influx B τ x y bb x' y' hx' hu
    -- indicator form
    have hind : ∀ (s : JSt n) (X : ℝ), (if s.2.2 = true ∧ s.1 ∈ B then X else 0)
        = (if s.2.2 = true ∧ s.1 ∈ B then (1 : ℝ) else 0) * X := by
      intro s X; split_ifs <;> ring
    have hmv : ∀ s : JSt n, matVec (fwdOf (D.jrate d B τ)) (π τ) s
        = (∑ u : JSt n, D.jrate d B τ u s * π τ u)
          - (∑ u : JSt n, D.jrate d B τ s u) * π τ s := by
      intro s
      simp only [matVec, fwdOf, sub_mul, ite_mul, zero_mul]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
      simp
    have hL : ∑ s : JSt n, (if s.2.2 = true ∧ s.1 ∈ B then
          matVec (fwdOf (D.jrate d B τ)) (π τ) s else 0)
        = (∑ u : JSt n, π τ u * ∑ s : JSt n,
            (if s.2.2 = true ∧ s.1 ∈ B then (1 : ℝ) else 0) * D.jrate d B τ u s)
          - ∑ u : JSt n, π τ u *
            ((if u.2.2 = true ∧ u.1 ∈ B then (1 : ℝ) else 0)
              * ∑ v : JSt n, D.jrate d B τ u v) := by
      have e1 : ∀ s : JSt n, (if s.2.2 = true ∧ s.1 ∈ B then
            matVec (fwdOf (D.jrate d B τ)) (π τ) s else 0)
          = (∑ u : JSt n, (if s.2.2 = true ∧ s.1 ∈ B then (1 : ℝ) else 0)
                * D.jrate d B τ u s * π τ u)
            - (if s.2.2 = true ∧ s.1 ∈ B then (1 : ℝ) else 0)
              * ((∑ u : JSt n, D.jrate d B τ s u) * π τ s) := by
        intro s
        rw [hind s, hmv s, mul_sub, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [Finset.sum_congr rfl fun s _ => e1 s, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      · exact Finset.sum_congr rfl fun u _ => by ring
    rw [hL, sub_nonpos]
    refine Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (hw0 u)
    by_cases hbu : u.2.2 = true ∧ u.1 ∈ B
    · rw [if_pos hbu, one_mul]
      refine Finset.sum_le_sum fun s _ => ?_
      by_cases hbs : s.2.2 = true ∧ s.1 ∈ B
      · rw [if_pos hbs, one_mul]
      · rw [if_neg hbs, zero_mul]; exact hq0 u s
    · rw [if_neg hbu, zero_mul]
      refine le_of_eq (Finset.sum_eq_zero fun s _ => ?_)
      by_cases hbs : s.2.2 = true ∧ s.1 ∈ B
      · rw [if_pos hbs, one_mul, hinflux u s hbu hbs]
      · rw [if_neg hbs, zero_mul]
  intro t ht s hs1 hs2
  have hmono : (∑ s : JSt n, (if s.2.2 = true ∧ s.1 ∈ B then π t s else 0))
      ≤ ∑ s : JSt n, (if s.2.2 = true ∧ s.1 ∈ B then π a s else 0) := by
    refine le_of_hasDerivWithinAt_nonpos ht.1
      (hcont.mono (Set.Icc_subset_Icc le_rfl ht.2)) fun τ hτ => ?_
    have hτ' : τ ∈ Set.Icc a b := ⟨hτ.1, le_trans hτ.2 ht.2⟩
    exact ⟨_, hnonpos τ hτ', (hderiv τ hτ').mono (Set.Icc_subset_Icc le_rfl ht.2)⟩
  have hzero : (∑ s : JSt n, (if s.2.2 = true ∧ s.1 ∈ B then π a s else 0)) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    split_ifs with h
    · exact h0 u h.1 h.2
    · rfl
  rw [hzero] at hmono
  have hsum0 : (∑ s : JSt n, (if s.2.2 = true ∧ s.1 ∈ B then π t s else 0)) = 0 :=
    le_antisymm hmono (Finset.sum_nonneg fun u _ => hσnn t ht u)
  have hthis := (Finset.sum_eq_zero_iff_of_nonneg
    (fun u (_ : u ∈ Finset.univ) => hσnn t ht u)).mp hsum0 s (Finset.mem_univ s)
  rwa [if_pos ⟨hs1, hs2⟩] at hthis

/-- One-target jump sums: `P1` has a unique target, `P2` contributes nothing
to the test, `P3` has a unique target under the side condition `Q3` (local
copy of the coupling's bookkeeping lemma). -/
private lemma sum_three_jumps' (P1 P2 P3 : JSt n → Prop)
    [DecidablePred P1] [DecidablePred P2] [DecidablePred P3]
    (Q3 : Prop) [Decidable Q3] (s1 s3 : JSt n) (r1 r2 r3 : ℝ) (f : JSt n → ℝ)
    (h1 : ∀ s, P1 s ↔ s = s1) (h2 : ∀ s, P2 s → f s = 0)
    (h3 : ∀ s, P3 s ↔ (Q3 ∧ s = s3)) :
    ∑ s : JSt n, ((if P1 s then r1 else 0) + (if P2 s then r2 else 0)
        + (if P3 s then r3 else 0)) * f s
      = r1 * f s1 + (if Q3 then r3 * f s3 else 0) := by
  classical
  have key : ∀ s : JSt n, ((if P1 s then r1 else 0) + (if P2 s then r2 else 0)
      + (if P3 s then r3 else 0)) * f s
      = (if s = s1 then r1 * f s1 else 0)
        + (if Q3 ∧ s = s3 then r3 * f s3 else 0) := by
    intro s
    have e2 : (if P2 s then r2 else 0) * f s = 0 := by
      by_cases hp : P2 s
      · rw [h2 s hp, mul_zero]
      · rw [if_neg hp, zero_mul]
    have e1 : (if P1 s then r1 else 0) * f s = if s = s1 then r1 * f s1 else 0 := by
      by_cases hp : P1 s
      · have hs := (h1 s).mp hp
        rw [if_pos hp, if_pos hs, hs]
      · rw [if_neg hp, if_neg (fun hEq => hp ((h1 s).mpr hEq)), zero_mul]
    have e3 : (if P3 s then r3 else 0) * f s
        = if Q3 ∧ s = s3 then r3 * f s3 else 0 := by
      by_cases hp : P3 s
      · have hs := (h3 s).mp hp
        rw [if_pos hp, if_pos hs, hs.2]
      · rw [if_neg hp, if_neg (fun hEq => hp ((h3 s).mpr hEq)), zero_mul]
    rw [add_mul, add_mul, e1, e2, e3, add_zero]
  rw [Finset.sum_congr rfl fun s _ => key s, Finset.sum_add_distrib]
  congr 1
  · simp
  · by_cases hq : Q3
    · simp only [hq, true_and, if_true]
      simp
    · simp only [hq, false_and, if_false, Finset.sum_const_zero]

open Classical in
/-- Coordinate-wise expansion of a jump sum of the stopped power coupling
against an arbitrary test `f` which is blind to `W`-only moves. -/
private lemma jrate_expand {d : ℝ} (B : Set (Cube n)) (t : ℝ) (x y : Cube n)
    (bb : Bool) (f : JSt n → ℝ)
    (hf2 : bb = true → ∀ y' : Cube n, f (x, y', true) = 0) :
    ∑ s' : JSt n, D.jrate d B t (x, y, bb) s' * f s'
      = ∑ i : Fin n,
        ((if bb then (if D.Y t i x < 1 then D.Y t i x / 2
              else D.Y t i x ^ (1 - d) / 2)
            else D.Y t i x / 2)
          * f (flipCoord i x, flipCoord i y, (bb && decide (flipCoord i x ∉ B)))
        + (if bb = true ∧ ¬(D.Y t i x < 1) then
            (D.Y t i x - D.Y t i x ^ (1 - d)) / 2
              * f (flipCoord i x, y, decide (flipCoord i x ∉ B))
          else 0)) := by
  classical
  simp only [jrate]
  rw [Finset.sum_congr rfl fun s' _ => Finset.sum_mul _ _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans (sum_three_jumps' _ _ _ (bb = true ∧ ¬(D.Y t i x < 1))
    ((flipCoord i x, flipCoord i y, (bb && decide (flipCoord i x ∉ B))) : JSt n)
    ((flipCoord i x, y, decide (flipCoord i x ∉ B)) : JSt n) _ _ _ f ?_ ?_ ?_) ?_
  · intro s'
    constructor
    · refine fun hc => Prod.ext_iff.mpr ⟨hc.1, Prod.ext_iff.mpr ⟨hc.2.1, ?_⟩⟩
      rw [hc.2.2, hc.1]
    · intro hEq
      subst hEq
      exact ⟨rfl, rfl, rfl⟩
  · intro s' hs'
    have hx' : s'.1 = x := hs'.2.2.1
    have hb' : s'.2.2 = true := hs'.2.1
    have hEq : s' = ((x, s'.2.1, true) : JSt n) :=
      Prod.ext_iff.mpr ⟨hx', Prod.ext_iff.mpr ⟨rfl, hb'⟩⟩
    have hzz := hf2 hs'.1 s'.2.1
    rwa [← hEq] at hzz
  · intro s'
    constructor
    · refine fun hc => ⟨⟨hc.1, hc.2.2.2.1⟩,
        Prod.ext_iff.mpr ⟨hc.2.2.1, Prod.ext_iff.mpr ⟨hc.2.1, ?_⟩⟩⟩
      rw [hc.2.2.2.2, hc.2.2.1]
    · intro hc
      obtain ⟨⟨hb, hY⟩, hEq⟩ := hc
      subst hEq
      exact ⟨hb, rfl, rfl, hY, rfl⟩
  · rfl

/-- Dead-sector jumps leave the sector test unchanged. -/
private lemma jump_dead {d : ℝ} (B : Set (Cube n)) (t : ℝ) (x y : Cube n)
    (Gf : JSt n → ℝ) (cst : ℝ) (hGd : ∀ x' y' : Cube n, Gf (x', y', false) = cst) :
    ∑ s' : JSt n, D.jrate d B t (x, y, false) s' * (Gf s' - Gf (x, y, false)) = 0 := by
  classical
  rw [D.jrate_expand B t x y false _ (by simp)]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [hGd]

/-- Alive-sector jump balance: the `V`-moving jumps carry total rate `Y_i/2`
and land at a value at least `F_t(σ_i x)`, so the jump part of the drift
dominates `½∑_i Y_i log Y_i`. -/
private lemma jump_alive {d ℓ : ℝ} (B : Set (Cube n)) {t : ℝ} (ht : t ≤ obsT)
    (x y : Cube n) (Gf : JSt n → ℝ)
    (hGa : ∀ x' y' : Cube n, Gf (x', y', true) = D.F t x')
    (hGd : ∀ x' y' : Cube n, Gf (x', y', false) = ℓ + 1 + Real.log (kappa D.a))
    (hFx : D.F t x ≤ ℓ + 1) :
    ∑ i : Fin n, D.Y t i x * Real.log (D.Y t i x) / 2
      ≤ ∑ s' : JSt n, D.jrate d B t (x, y, true) s' * (Gf s' - Gf (x, y, true)) := by
  classical
  have hT : t ≤ D.T := D.le_T_of_le_obsT ht
  have hflip : ∀ i : Fin n, D.F t (flipCoord i x) - D.F t x = Real.log (D.Y t i x) :=
    fun i => D.F_flipCoord_sub_of_le hT i x
  have hΔ : ∀ i : Fin n, Real.log (D.Y t i x)
      ≤ Gf (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))
          - Gf (x, y, true) := by
    intro i
    rw [hGa x y]
    by_cases hb : flipCoord i x ∈ B
    · rw [show (decide (flipCoord i x ∉ B)) = false by simp [hb], hGd]
      have h2 : Real.log (D.Y t i x) ≤ Real.log (kappa D.a) :=
        Real.log_le_log (D.Y_pos hT i x) (D.Y_le_kappa ht i x)
      linarith [hflip i]
    · rw [show (decide (flipCoord i x ∉ B)) = true by simp [hb], hGa]
      linarith [hflip i]
  have hΔ' : ∀ i : Fin n,
      Gf (flipCoord i x, y, decide (flipCoord i x ∉ B)) - Gf (x, y, true)
        = Gf (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))
            - Gf (x, y, true) := by
    intro i
    by_cases hb : flipCoord i x ∈ B
    · rw [show (decide (flipCoord i x ∉ B)) = false by simp [hb]]
      simp only [hGd]
    · rw [show (decide (flipCoord i x ∉ B)) = true by simp [hb]]
      simp only [hGa]
  rw [D.jrate_expand B t x y true _ (by intro _ y'; rw [hGa, hGa, sub_self])]
  refine Finset.sum_le_sum fun i _ => ?_
  have hY : 0 < D.Y t i x := D.Y_pos hT i x
  have hD := hΔ i
  rw [if_pos (rfl : (true : Bool) = true), Bool.true_and, hΔ' i]
  set Δ : ℝ := Gf (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))
    - Gf (x, y, true) with hΔdef
  have hmul : D.Y t i x / 2 * Real.log (D.Y t i x) ≤ D.Y t i x / 2 * Δ :=
    mul_le_mul_of_nonneg_left hD (by linarith)
  by_cases h1 : D.Y t i x < 1
  · rw [if_pos h1, if_neg (fun hc : (true = true ∧ ¬(D.Y t i x < 1)) => hc.2 h1)]
    nlinarith [hmul]
  · rw [if_neg h1, if_pos (⟨rfl, h1⟩ : (true = true ∧ ¬(D.Y t i x < 1)))]
    nlinarith [hmul]

/-- The node transfer clears alive mass on the barrier at the node time. -/
private lemma killTr_kills' {ℓ t : ℝ} (v : JSt n → ℝ) {s : JSt n}
    (hs1 : s.2.2 = true) (hs2 : s.1 ∈ D.barrier ℓ t) :
    matVec (D.killTr ℓ t) v s = 0 := by
  classical
  obtain ⟨x, y, b⟩ := s
  simp only at hs1 hs2
  subst hs1
  refine Finset.sum_eq_zero fun s' _ => ?_
  obtain ⟨x', y', b'⟩ := s'
  have hdec : decide (x ∉ D.barrier ℓ t) = false := by simp [hs2]
  have hz : D.killTr ℓ t (x, y, true) (x', y', b') = 0 := by
    simp only [killTr]
    refine if_neg ?_
    rintro ⟨hxx, -, h3⟩
    rw [← hxx, hdec, Bool.and_false] at h3
    exact Bool.noConfusion h3
  rw [hz, zero_mul]

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
