import Mathlib

/-!
# Finite-dimensional linear ODE flows

Existence, uniqueness, positivity, and mass bounds for
`y'(t) = A(t)·y(t)` on a compact interval `[a,b]`, with `A : ℝ → S → S → ℝ`
continuous in `t` on a finite state space `S`.

This is the "master equation" backbone of the de-probabilized formalization
of [LGF]: the reverse heat process, the coupled process, and their killed and
weighted variants ([LGF §2.2, §4]) are all instances (cell-wise, between the
finitely many barrier-crossing times).

Conventions: `y t : S → ℝ` is a column of masses;
`(matVecA A t y) s = ∑ s', A t s s' * y s'`. Positivity requires the Metzler
condition (off-diagonal entries `≥ 0`), mass bounds require column-sum
conditions (`∑_s A t s s' = 0` for conservation, `≤ 0` for sub-conservation).
-/

namespace Talagrand

open scoped NNReal

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Action of the time-dependent matrix. -/
def matVec (A : S → S → ℝ) (y : S → ℝ) : S → ℝ := fun s => ∑ s', A s s' * y s'

/-- `IsLinFlow A a b y` : `y` solves `y' = A(t) y` on `[a,b]`
(continuity on `[a,b]`, derivative within `[a,b]` at every point). -/
structure IsLinFlow (A : ℝ → S → S → ℝ) (a b : ℝ) (y : ℝ → S → ℝ) : Prop where
  cont : ∀ s, ContinuousOn (fun t => y t s) (Set.Icc a b)
  deriv : ∀ s, ∀ t ∈ Set.Icc a b,
    HasDerivWithinAt (fun t => y t s) (matVec (A t) (y t) s) (Set.Icc a b) t

/-! ### Elementary calculus glue -/

section Glue

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restrict a two-sided derivative on `[a,b]` to a right derivative at an
interior-on-the-left point. -/
theorem hasDerivWithinAt_Ici_of_Icc {f : ℝ → F} {v : F} {a b x : ℝ}
    (hx : x ∈ Set.Ico a b) (h : HasDerivWithinAt f v (Set.Icc a b) x) :
    HasDerivWithinAt f v (Set.Ici x) x := by
  refine h.mono_of_mem_nhdsWithin (Filter.mem_of_superset
    (Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx.2))) ?_)
  rintro y ⟨hy1, hy2⟩
  exact ⟨le_trans hx.1 hy1, le_of_lt hy2⟩

/-- Restrict a two-sided derivative on `[a,b]` to a right derivative at an
interior point. -/
theorem hasDerivWithinAt_Ioi_of_Icc {f : ℝ → F} {v : F} {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b) (h : HasDerivWithinAt f v (Set.Icc a b) x) :
    HasDerivWithinAt f v (Set.Ioi x) x := by
  refine h.mono_of_mem_nhdsWithin (Filter.mem_of_superset
    (Filter.inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx.2))) ?_)
  rintro y ⟨hy1, hy2⟩
  exact ⟨le_of_lt (lt_trans hx.1 hy1), le_of_lt hy2⟩

end Glue

/-- A function which is `≥` its value at the right endpoint `c` throughout
`[a,c)` has nonpositive derivative at `c`. -/
theorem nonpos_of_hasDerivWithinAt_left {f : ℝ → ℝ} {a c v : ℝ} (hac : a < c)
    (hd : HasDerivWithinAt f v (Set.Icc a c) c)
    (hf : ∀ t ∈ Set.Ico a c, f c ≤ f t) : v ≤ 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Icc_diff_right] at hd
  haveI : (nhdsWithin c (Set.Ico a c)).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hac]; infer_instance
  refine le_of_tendsto hd (Filter.eventually_of_mem self_mem_nhdsWithin ?_)
  intro t ht
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hf t ht)) (by linarith [ht.2])

/-- FTC-style comparison: continuity on `[a,b]` plus a pointwise derivative
bound by an integrable `φ` gives `F b - F a ≤ ∫ φ`. -/
theorem sub_le_integral_of_hasDerivWithinAt_le {F φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hd : ∀ x ∈ Set.Icc a b, ∃ v ≤ φ x, HasDerivWithinAt F v (Set.Icc a b) x)
    (hφ : IntervalIntegrable φ MeasureTheory.volume a b) :
    F b - F a ≤ ∫ t in a..b, φ t := by
  choose! v hv1 hv2 using hd
  refine intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hcont
    (fun x hx => hasDerivWithinAt_Ioi_of_Icc hx (hv2 x ⟨hx.1.le, hx.2.le⟩)) ?_
    (fun x hx => hv1 x ⟨hx.1.le, hx.2.le⟩)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hφ

/-- Monotone-decrease from a pointwise nonpositive derivative bound. -/
theorem le_of_hasDerivWithinAt_nonpos {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hd : ∀ x ∈ Set.Icc a b, ∃ v ≤ (0 : ℝ), HasDerivWithinAt F v (Set.Icc a b) x) :
    F b ≤ F a := by
  have := sub_le_integral_of_hasDerivWithinAt_le (φ := fun _ => (0 : ℝ)) hab hcont hd
    intervalIntegrable_const
  simpa using this

/-- Derivative of a finite sum, in `fun t => ∑ i, f i t` form. -/
theorem hasDerivWithinAt_fintypeSum {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ}
    {f' : ι → ℝ} {u : Set ℝ} {x : ℝ}
    (h : ∀ i, HasDerivWithinAt (f i) (f' i) u x) :
    HasDerivWithinAt (fun t => ∑ i, f i t) (∑ i, f' i) u x := by
  have hfun : (∑ i : ι, f i) = fun t => ∑ i : ι, f i t := by
    funext t; simp
  have h2 := HasDerivWithinAt.sum (u := (Finset.univ : Finset ι)) fun i _ => h i
  rwa [hfun] at h2

/-! ### Bounds on the generator -/

/-- Row-sum bound for a matrix acting on the sup norm. -/
theorem norm_matVec_le {A : S → S → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (h : ∀ s, ∑ s', |A s s'| ≤ M) (y : S → ℝ) : ‖matVec A y‖ ≤ M * ‖y‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hM0 (norm_nonneg y))]
  intro s
  simp only [matVec, Real.norm_eq_abs]
  calc |∑ s', A s s' * y s'| ≤ ∑ s', |A s s' * y s'| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s', |A s s'| * |y s'| := by simp [abs_mul]
    _ ≤ ∑ s', |A s s'| * ‖y‖ := Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm y s') (abs_nonneg _)
    _ = (∑ s', |A s s'|) * ‖y‖ := by rw [← Finset.sum_mul]
    _ ≤ M * ‖y‖ := mul_le_mul_of_nonneg_right (h s) (norm_nonneg y)

theorem matVec_sub (A : S → S → ℝ) (y z : S → ℝ) :
    matVec A y - matVec A z = matVec A (y - z) := by
  funext s
  simp only [matVec, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s' _ => by ring

theorem lipschitzWith_matVec {A : S → S → ℝ} {M : ℝ≥0}
    (h : ∀ s, ∑ s', |A s s'| ≤ (M : ℝ)) : LipschitzWith M (matVec A) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm, dist_eq_norm, matVec_sub]
  exact norm_matVec_le M.coe_nonneg h _

/-- A uniform row-sum bound for a continuous matrix family on a compact
interval. -/
theorem exists_rowSum_bound {A : ℝ → S → S → ℝ} {a b : ℝ}
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ∀ s, ∑ s', |A t s s'| ≤ M := by
  choose c hc using fun s s' =>
    (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn (hA s s')
  refine ⟨∑ p : S, ∑ q : S, |c p q|,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro t ht s
  calc ∑ s', |A t s s'| ≤ ∑ s', |c s s'| :=
        Finset.sum_le_sum fun s' _ =>
          le_trans (by simpa [Real.norm_eq_abs] using hc s s' t ht) (le_abs_self _)
    _ ≤ ∑ p : S, ∑ q : S, |c p q| :=
        Finset.single_le_sum (f := fun p => ∑ q : S, |c p q|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ s)

/-! ### Building flows -/

/-- A family of derivatives suffices: continuity is automatic. -/
theorem isLinFlow_of_deriv {A : ℝ → S → S → ℝ} {a b : ℝ} {y : ℝ → S → ℝ}
    (h : ∀ s, ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun t => y t s) (matVec (A t) (y t) s) (Set.Icc a b) t) :
    IsLinFlow A a b y :=
  ⟨fun s t ht => (h s t ht).continuousWithinAt, h⟩

/-- Gluing two flows sharing an endpoint value. -/
theorem isLinFlow_glue {A : ℝ → S → S → ℝ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    {y₁ y₂ : ℝ → S → ℝ} (h1 : IsLinFlow A a c y₁) (h2 : IsLinFlow A c b y₂)
    (hm : y₁ c = y₂ c) :
    IsLinFlow A a b (fun t => if t ≤ c then y₁ t else y₂ t) := by
  set Y : ℝ → S → ℝ := fun t => if t ≤ c then y₁ t else y₂ t with hY
  refine isLinFlow_of_deriv fun s t ht => ?_
  rcases lt_trichotomy t c with htc | htc | htc
  · -- left of the node: `Y` agrees with `y₁` on a neighbourhood
    have hmem : Set.Icc a c ∈ nhdsWithin t (Set.Icc a b) :=
      Filter.mem_of_superset
        (Filter.inter_mem self_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htc)))
        (fun y hy => ⟨hy.1.1, le_of_lt hy.2⟩)
    have hd := (h1.deriv s t ⟨ht.1, htc.le⟩).mono_of_mem_nhdsWithin hmem
    have hYt : Y t = y₁ t := by simp [hY, htc.le]
    rw [hYt]
    refine hd.congr_of_eventuallyEq ?_ (congrFun hYt s)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htc)] with x hx
    simp only [Set.mem_Iio] at hx
    simp [hY, le_of_lt hx]
  · -- at the node: union of the two one-sided derivatives
    subst htc
    have hYt : Y t = y₁ t := by simp [hY]
    have e1 : HasDerivWithinAt (fun τ => Y τ s) (matVec (A t) (Y t) s) (Set.Icc a t) t := by
      rw [hYt]
      refine (h1.deriv s t (Set.right_mem_Icc.2 hac)).congr (fun x hx => ?_) (by simp [hY])
      simp [hY, hx.2]
    have e2 : HasDerivWithinAt (fun τ => Y τ s) (matVec (A t) (Y t) s) (Set.Icc t b) t := by
      rw [hYt, hm]
      refine (h2.deriv s t (Set.left_mem_Icc.2 hcb)).congr (fun x hx => ?_) (by simp [hY, hm])
      rcases eq_or_lt_of_le hx.1 with h | h
      · simp [hY, ← h, hm]
      · simp [hY, not_le.2 h]
    have := e1.union e2
    rwa [Set.Icc_union_Icc_eq_Icc hac hcb] at this
  · -- right of the node
    have hmem : Set.Icc c b ∈ nhdsWithin t (Set.Icc a b) :=
      Filter.mem_of_superset
        (Filter.inter_mem self_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds htc)))
        (fun y hy => ⟨le_of_lt hy.2, hy.1.2⟩)
    have hd := (h2.deriv s t ⟨htc.le, ht.2⟩).mono_of_mem_nhdsWithin hmem
    have hYt : Y t = y₂ t := by simp [hY, not_le.2 htc]
    rw [hYt]
    refine hd.congr_of_eventuallyEq ?_ (congrFun hYt s)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds htc)] with x hx
    simp only [Set.mem_Ioi] at hx
    simp [hY, not_le.2 hx]

/-- Existence on a short interval, from Picard–Lindelöf. -/
theorem exists_linFlow_small {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ t ∈ Set.Icc a b, ∀ s, ∑ s', |A t s s'| ≤ M)
    (hsmall : M * (b - a) ≤ 1 / 2) (y₀ : S → ℝ) :
    ∃ y : ℝ → S → ℝ, IsLinFlow A a b y ∧ y a = y₀ := by
  set f : ℝ → (S → ℝ) → (S → ℝ) := fun t w => matVec (A t) w with hf
  set K : ℝ≥0 := ⟨M, hM0⟩ with hK
  set rad : ℝ≥0 := ⟨‖y₀‖ + 1, by positivity⟩ with hrad
  set L : ℝ≥0 := ⟨M * (2 * ‖y₀‖ + 1), by positivity⟩ with hL
  have hpl : IsPicardLindelof f (⟨a, Set.left_mem_Icc.2 hab⟩ : Set.Icc a b) y₀ rad 0 L K := by
    constructor
    · intro t ht
      exact (lipschitzWith_matVec (M := K) (hM t ht)).lipschitzOnWith
    · intro x _
      refine continuousOn_pi.2 fun s => ?_
      exact continuousOn_finset_sum _ fun s' _ => (hA s s').mul continuousOn_const
    · intro t ht x hx
      have hx' : ‖x‖ ≤ ‖y₀‖ + rad := by
        have := mem_closedBall_iff_norm.1 hx
        calc ‖x‖ = ‖x - y₀ + y₀‖ := by ring_nf
          _ ≤ ‖x - y₀‖ + ‖y₀‖ := norm_add_le _ _
          _ ≤ rad + ‖y₀‖ := by linarith
          _ = ‖y₀‖ + rad := by ring
      have h1 : ‖f t x‖ ≤ M * ‖x‖ := norm_matVec_le hM0 (hM t ht) x
      have h2 : M * ‖x‖ ≤ M * (‖y₀‖ + rad) := mul_le_mul_of_nonneg_left hx' hM0
      have h3 : ((rad : ℝ)) = ‖y₀‖ + 1 := rfl
      have : ((L : ℝ)) = M * (2 * ‖y₀‖ + 1) := rfl
      rw [this]
      calc ‖f t x‖ ≤ M * (‖y₀‖ + rad) := le_trans h1 h2
        _ = M * (2 * ‖y₀‖ + 1) := by rw [h3]; ring
    · have hrad' : ((rad : ℝ)) = ‖y₀‖ + 1 := rfl
      have hL' : ((L : ℝ)) = M * (2 * ‖y₀‖ + 1) := rfl
      have hmax : max (b - a) (a - a) = b - a := by
        rw [sub_self]; exact max_eq_left (by linarith)
      simp only [NNReal.coe_zero, sub_zero, hrad', hL', hmax]
      have h0 : (0 : ℝ) ≤ ‖y₀‖ := norm_nonneg _
      nlinarith [hsmall, h0, mul_nonneg hM0 (sub_nonneg.2 hab)]
  obtain ⟨α, hα0, hαd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨α, isLinFlow_of_deriv fun s t ht => ?_, hα0⟩
  exact (hasDerivWithinAt_pi.1 (hαd t ht)) s

/-- Existence on an interval of length at most `n * δ`, by induction on `n`. -/
theorem exists_linFlow_aux (A : ℝ → S → S → ℝ) {M δ : ℝ} (hM0 : 0 ≤ M) (hδ : 0 < δ)
    (hMδ : M * δ ≤ 1 / 2) :
    ∀ (n : ℕ) (a b : ℝ), a ≤ b → b - a ≤ n * δ →
      (∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b)) →
      (∀ t ∈ Set.Icc a b, ∀ s, ∑ s', |A t s s'| ≤ M) →
      ∀ y₀ : S → ℝ, ∃ y : ℝ → S → ℝ, IsLinFlow A a b y ∧ y a = y₀ := by
  intro n
  induction n with
  | zero =>
    intro a b hab hlen hA hM y₀
    refine exists_linFlow_small hab hA hM0 hM ?_ y₀
    simp only [Nat.cast_zero, zero_mul] at hlen
    nlinarith
  | succ n ih =>
    intro a b hab hlen hA hM y₀
    by_cases hle : b - a ≤ δ
    · exact exists_linFlow_small hab hA hM0 hM (by nlinarith) y₀
    · push_neg at hle
      have hac : a ≤ a + δ := by linarith
      have hcb : a + δ ≤ b := by linarith
      have hA1 : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a (a + δ)) :=
        fun s s' => (hA s s').mono (Set.Icc_subset_Icc le_rfl hcb)
      have hM1 : ∀ t ∈ Set.Icc a (a + δ), ∀ s, ∑ s', |A t s s'| ≤ M :=
        fun t ht => hM t ⟨ht.1, le_trans ht.2 hcb⟩
      obtain ⟨y₁, hy₁, hy₁0⟩ :=
        exists_linFlow_small hac hA1 hM0 hM1 (by nlinarith) y₀
      have hA2 : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc (a + δ) b) :=
        fun s s' => (hA s s').mono (Set.Icc_subset_Icc hac le_rfl)
      have hM2 : ∀ t ∈ Set.Icc (a + δ) b, ∀ s, ∑ s', |A t s s'| ≤ M :=
        fun t ht => hM t ⟨le_trans hac ht.1, ht.2⟩
      have hlen2 : b - (a + δ) ≤ n * δ := by push_cast at hlen ⊢; nlinarith
      obtain ⟨y₂, hy₂, hy₂0⟩ := ih (a + δ) b hcb hlen2 hA2 hM2 (y₁ (a + δ))
      refine ⟨fun t => if t ≤ a + δ then y₁ t else y₂ t,
        isLinFlow_glue hac hcb hy₁ hy₂ hy₂0.symm, ?_⟩
      simp [hac, hy₁0]

/-- **Existence** of the linear flow with prescribed initial value. -/
theorem exists_linFlow (A : ℝ → S → S → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    (y₀ : S → ℝ) :
    ∃ y : ℝ → S → ℝ, IsLinFlow A a b y ∧ y a = y₀ := by
  obtain ⟨M, hM0, hM⟩ := exists_rowSum_bound hA
  set δ : ℝ := 1 / (2 * (M + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hMδ : M * δ ≤ 1 / 2 := by
    have hkey : (M + 1) * δ = 1 / 2 := by
      rw [hδdef]; field_simp
    calc M * δ ≤ (M + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = 1 / 2 := hkey
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / δ)
  exact exists_linFlow_aux A hM0 hδ hMδ n a b hab ((div_le_iff₀ hδ).1 hn) hA hM y₀

/-- **Uniqueness**: two flows with the same initial value agree on `[a,b]`. -/
theorem linFlow_unique {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    {y z : ℝ → S → ℝ} (hy : IsLinFlow A a b y) (hz : IsLinFlow A a b z)
    (h0 : y a = z a) : ∀ t ∈ Set.Icc a b, y t = z t := by
  obtain ⟨M, hM0, hM⟩ := exists_rowSum_bound hA
  set K : ℝ≥0 := ⟨M, hM0⟩ with hK
  intro t ht
  refine ODE_solution_unique_of_mem_Icc_right (K := K)
    (v := fun t w => matVec (A t) w) (s := fun _ => Set.univ)
    (fun τ hτ => (lipschitzWith_matVec (M := K) (hM τ ⟨hτ.1, hτ.2.le⟩)).lipschitzOnWith)
    (continuousOn_pi.2 hy.cont)
    (fun τ hτ => hasDerivWithinAt_pi.2 fun s =>
      hasDerivWithinAt_Ici_of_Icc hτ (hy.deriv s τ ⟨hτ.1, hτ.2.le⟩))
    (fun _ _ => Set.mem_univ _)
    (continuousOn_pi.2 hz.cont)
    (fun τ hτ => hasDerivWithinAt_pi.2 fun s =>
      hasDerivWithinAt_Ici_of_Icc hτ (hz.deriv s τ ⟨hτ.1, hτ.2.le⟩))
    (fun _ _ => Set.mem_univ _) h0 ht

/-! ### Positivity -/

/-- Core positivity argument: a nonnegative-at-`a` solution of a Metzler
differential *inequality* `d' = A d + r` with `r ≥ 0` stays nonnegative.
Both `linFlow_nonneg` and `linFlow_le_of_source` are instances. -/
theorem nonneg_of_flow_ineq {A : ℝ → S → S → ℝ} {a b : ℝ}
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    (hMetzler : ∀ t ∈ Set.Icc a b, ∀ s s', s ≠ s' → 0 ≤ A t s s')
    {d : ℝ → S → ℝ} (hdc : ∀ s, ContinuousOn (fun t => d t s) (Set.Icc a b))
    (hd : ∀ s, ∀ t ∈ Set.Icc a b, ∃ r ≥ (0 : ℝ),
      HasDerivWithinAt (fun t => d t s) (matVec (A t) (d t) s + r) (Set.Icc a b) t)
    (h0 : ∀ s, 0 ≤ d a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ d t s := by
  obtain ⟨M, hM0, hM⟩ := exists_rowSum_bound hA
  set C : ℝ := M + 1 with hC
  -- Step 1: for every `ε > 0`, the shifted family stays strictly positive.
  have key : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Icc a b, ∀ s,
      0 < d t s + ε * Real.exp (C * t) := by
    intro ε hε
    set W : ℝ → S → ℝ := fun t s => d t s + ε * Real.exp (C * t) with hW
    have hWc : ∀ s, ContinuousOn (fun t => W t s) (Set.Icc a b) := by
      intro s
      exact (hdc s).add (Continuous.continuousOn (by fun_prop))
    by_contra hcon
    push_neg at hcon
    obtain ⟨t₁, ht₁, s₁, hs₁⟩ := hcon
    set Z : Set ℝ := ⋃ s : S, Set.Icc a b ∩ (fun t => W t s) ⁻¹' Set.Iic 0 with hZ
    have hZcl : IsClosed Z :=
      isClosed_iUnion_of_finite fun s =>
        (hWc s).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hZsub : Z ⊆ Set.Icc a b := by
      intro x hx
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hx
      exact hs.1
    have hZne : Z.Nonempty := ⟨t₁, Set.mem_iUnion.2 ⟨s₁, ht₁, hs₁⟩⟩
    have hZbdd : BddBelow Z := ⟨a, fun x hx => (hZsub hx).1⟩
    set c : ℝ := sInf Z with hc
    have hcZ : c ∈ Z := hZcl.csInf_mem hZne hZbdd
    have hcab : c ∈ Set.Icc a b := hZsub hcZ
    obtain ⟨j, hj1, hj2⟩ := Set.mem_iUnion.1 hcZ
    have hac : a ≤ c := le_csInf hZne fun x hx => (hZsub hx).1
    have hane : a ≠ c := by
      intro h
      have : W a j ≤ 0 := by rw [h]; exact hj2
      have hpos : 0 < W a j := by
        have := h0 j
        have : 0 < ε * Real.exp (C * a) := by positivity
        simp only [hW]
        linarith [h0 j]
      linarith
    have hacs : a < c := lt_of_le_of_ne hac hane
    -- `W` is strictly positive to the left of `c`
    have hlow : ∀ t ∈ Set.Ico a c, ∀ s, 0 < W t s := by
      intro t ht s
      by_contra hneg
      push_neg at hneg
      have htab : t ∈ Set.Icc a b := ⟨ht.1, le_trans ht.2.le hcab.2⟩
      have : c ≤ t := csInf_le hZbdd (Set.mem_iUnion.2 ⟨s, htab, hneg⟩)
      linarith [ht.2]
    -- hence nonnegative at `c` by continuity
    have hge : ∀ s, 0 ≤ W c s := by
      set G : Set ℝ := ⋂ s : S, Set.Icc a b ∩ (fun t => W t s) ⁻¹' Set.Ici 0 with hG
      have hGcl : IsClosed G :=
        isClosed_iInter fun s =>
          (hWc s).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have hsub : Set.Ico a c ⊆ G := by
        intro t ht
        refine Set.mem_iInter.2 fun s => ⟨⟨ht.1, le_trans ht.2.le hcab.2⟩, ?_⟩
        exact le_of_lt (hlow t ht s)
      have : c ∈ G := by
        apply hGcl.closure_subset_iff.2 hsub
        rw [closure_Ico (ne_of_lt hacs)]
        exact Set.right_mem_Icc.2 hacs.le
      intro s
      exact (Set.mem_iInter.1 this s).2
    have hcj : W c j = 0 := le_antisymm hj2 (hge j)
    -- the derivative of `W (·) j` at `c` is strictly positive
    obtain ⟨r, hr0, hrd⟩ := hd j c hcab
    have hexp : HasDerivAt (fun t : ℝ => ε * Real.exp (C * t))
        (ε * (Real.exp (C * c) * C)) c := by
      have h1 : HasDerivAt (fun t : ℝ => C * t) C c := by
        simpa using (hasDerivAt_id c).const_mul C
      exact (h1.exp).const_mul ε
    have hWd : HasDerivWithinAt (fun t => W t j)
        (matVec (A c) (d c) j + r + ε * (Real.exp (C * c) * C)) (Set.Icc a b) c :=
      hrd.add hexp.hasDerivWithinAt
    have hE : (0 : ℝ) < Real.exp (C * c) := Real.exp_pos _
    have hP : 0 ≤ ∑ s', A c j s' * W c s' := by
      refine Finset.sum_nonneg fun s' _ => ?_
      by_cases h : j = s'
      · rw [← h, hcj]; simp
      · exact mul_nonneg (hMetzler c hcab j s' h) (hge s')
    have hQ : ∑ s', A c j s' ≤ M := by
      refine le_trans (Finset.sum_le_sum fun s' _ => le_abs_self _) ?_
      exact hM c hcab j
    have hrw : matVec (A c) (d c) j
        = (∑ s', A c j s' * W c s') - ε * Real.exp (C * c) * (∑ s', A c j s') := by
      simp only [matVec, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s' _ => ?_
      simp only [hW]
      ring
    have hvpos : 0 < matVec (A c) (d c) j + r + ε * (Real.exp (C * c) * C) := by
      rw [hrw, hC]
      have hmul : ε * Real.exp (C * c) * (∑ s', A c j s') ≤ ε * Real.exp (C * c) * M :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
      nlinarith [hP, hr0, mul_pos hε hE]
    -- contradiction with the left-derivative sign
    have hle0 : matVec (A c) (d c) j + r + ε * (Real.exp (C * c) * C) ≤ 0 := by
      refine nonpos_of_hasDerivWithinAt_left hacs
        (hWd.mono (Set.Icc_subset_Icc le_rfl hcab.2)) fun t ht => ?_
      rw [hcj]
      exact le_of_lt (hlow t ht j)
    linarith
  -- Step 2: let `ε ↓ 0`.
  intro t ht s
  by_contra hneg
  push_neg at hneg
  have hE : (0 : ℝ) < Real.exp (C * t) := Real.exp_pos _
  have := key (-(d t s) / Real.exp (C * t)) (div_pos (neg_pos.2 hneg) hE) t ht s
  rw [div_mul_cancel₀ _ (ne_of_gt hE)] at this
  linarith

/-- **Positivity** (Metzler): if all off-diagonal entries of `A t` are `≥ 0`
on `[a,b]` and `y a ≥ 0`, then `y t ≥ 0` on `[a,b]`. -/
theorem linFlow_nonneg {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    (hMetzler : ∀ t ∈ Set.Icc a b, ∀ s s', s ≠ s' → 0 ≤ A t s s')
    {y : ℝ → S → ℝ} (hy : IsLinFlow A a b y) (h0 : ∀ s, 0 ≤ y a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ y t s :=
  nonneg_of_flow_ineq hA hMetzler hy.cont
    (fun s t ht => ⟨0, le_rfl, by simpa using hy.deriv s t ht⟩) h0

/-- **Mass conservation**: if all column sums of `A t` vanish
(`∑_s A t s s' = 0`), the total mass `∑_s y t s` is constant. -/
theorem linFlow_mass_eq {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcol : ∀ t ∈ Set.Icc a b, ∀ s', ∑ s, A t s s' = 0)
    {y : ℝ → S → ℝ} (hy : IsLinFlow A a b y) :
    ∀ t ∈ Set.Icc a b, ∑ s, y t s = ∑ s, y a s := by
  have key : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun t => ∑ s, y t s) 0 (Set.Icc a b) t := by
    intro t ht
    have h := hasDerivWithinAt_fintypeSum (f := fun s τ => y τ s)
      (f' := fun s => matVec (A t) (y t) s) (u := Set.Icc a b) (x := t)
      fun s => hy.deriv s t ht
    have hzero : ∑ s, matVec (A t) (y t) s = 0 := by
      simp only [matVec]
      rw [Finset.sum_comm]
      simp [← Finset.sum_mul, hcol t ht]
    rwa [hzero] at h
  refine constant_of_has_deriv_right_zero
    (continuousOn_finset_sum _ fun s _ => hy.cont s) fun x hx => ?_
  exact hasDerivWithinAt_Ici_of_Icc hx (key x ⟨hx.1, hx.2.le⟩)

/-- **Mass sub-conservation**: if column sums are `≤ 0` and `y ≥ 0` along the
flow, the total mass is nonincreasing. -/
theorem linFlow_mass_le {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcol : ∀ t ∈ Set.Icc a b, ∀ s', ∑ s, A t s s' ≤ 0)
    {y : ℝ → S → ℝ} (hy : IsLinFlow A a b y)
    (hpos : ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ y t s) :
    ∀ t ∈ Set.Icc a b, ∑ s, y t s ≤ ∑ s, y a s := by
  intro t ht
  have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl ht.2
  refine le_of_hasDerivWithinAt_nonpos ht.1
    ((continuousOn_finset_sum _ fun s _ => hy.cont s).mono hsub) fun x hx => ?_
  refine ⟨∑ s, matVec (A x) (y x) s, ?_, ?_⟩
  · have : ∑ s, matVec (A x) (y x) s = ∑ s', (∑ s, A x s s') * y x s' := by
      simp only [matVec]
      rw [Finset.sum_comm]
      simp [← Finset.sum_mul]
    rw [this]
    exact Finset.sum_nonpos fun s' _ =>
      mul_nonpos_of_nonpos_of_nonneg (hcol x (hsub hx) s') (hpos x (hsub hx) s')
  · exact (hasDerivWithinAt_fintypeSum (f := fun s τ => y τ s)
      (f' := fun s => matVec (A x) (y x) s)
      (fun s => hy.deriv s x (hsub hx))).mono hsub

/-- Derivative of a pairing `t ↦ ∑_s y t s · g t s` along the flow:
`d/dt ⟨y_t, g_t⟩ = ⟨A(t)y_t, g_t⟩ + ⟨y_t, ∂_t g_t⟩`. The workhorse for all
martingale-type arguments ([LGF §4]: Duhamel, supermartingale, score
energy). -/
theorem hasDerivWithinAt_pairing {A : ℝ → S → S → ℝ} {a b : ℝ}
    {y : ℝ → S → ℝ} (hy : IsLinFlow A a b y) {g : ℝ → S → ℝ} {g' : S → ℝ}
    {t : ℝ} (ht : t ∈ Set.Icc a b)
    (hg : ∀ s, HasDerivWithinAt (fun t => g t s) (g' s) (Set.Icc a b) t) :
    HasDerivWithinAt (fun t => ∑ s, y t s * g t s)
      (∑ s, (matVec (A t) (y t) s * g t s + y t s * g' s)) (Set.Icc a b) t :=
  hasDerivWithinAt_fintypeSum fun s => (hy.deriv s t ht).mul (hg s)

/-- **Comparison/domination**: if `z` solves the same Metzler ODE with an
extra nonnegative source against a nonnegative flow (`z' = A z + r`,
`r ≥ 0` pointwise), and `z a ≥ y a ≥ 0`, then `z ≥ y` on `[a,b]`.
(Used to compare weighted flows against tilted lower-bound flows.) -/
theorem linFlow_le_of_source {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    (hMetzler : ∀ t ∈ Set.Icc a b, ∀ s s', s ≠ s' → 0 ≤ A t s s')
    {y z : ℝ → S → ℝ} (hy : IsLinFlow A a b y)
    (hzc : ∀ s, ContinuousOn (fun t => z t s) (Set.Icc a b))
    (hz : ∀ s, ∀ t ∈ Set.Icc a b, ∃ r ≥ 0,
      HasDerivWithinAt (fun t => z t s) (matVec (A t) (z t) s + r)
        (Set.Icc a b) t)
    (h0 : ∀ s, y a s ≤ z a s) (hy0 : ∀ s, 0 ≤ y a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, y t s ≤ z t s := by
  have hmain : ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ z t s - y t s := by
    refine nonneg_of_flow_ineq hA hMetzler (d := fun t s => z t s - y t s)
      (fun s => (hzc s).sub (hy.cont s)) (fun s t ht => ?_) (fun s => by
        simpa using sub_nonneg.2 (h0 s))
    obtain ⟨r, hr0, hrd⟩ := hz s t ht
    refine ⟨r, hr0, ?_⟩
    have hdiff := hrd.sub (hy.deriv s t ht)
    have hcalc : matVec (A t) (z t) s + r - matVec (A t) (y t) s
        = matVec (A t) (fun s => z t s - y t s) s + r := by
      simp only [matVec, ← Finset.sum_sub_distrib]
      rw [← sub_add_eq_add_sub]
      congr 1
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s' _ => by ring
    rwa [hcalc] at hdiff
  intro t ht s
  linarith [hmain t ht s]

end Talagrand
