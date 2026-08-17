import Mathlib

/-!
# A C¹ cutoff function and the coarea Cauchy–Schwarz bound

[C, proof of Lemma 4] uses a `C¹` cutoff `χ : ℝ → [0,1]` with `χ = 1` on
`[0,1]`, `supp χ ⊆ (-1,2)`, `|χ'| ≤ c'`. We build it from the cubic
smoothstep `s v = v²(3-2v)` and prove the FTC/Cauchy–Schwarz estimate for
`ψ(v) = e^{v/2} χ(v - ℓ)`:
`|ψ(b) - ψ(a)|² ≤ 4(½+c')² · |[a,b] ∩ (ℓ-1, ℓ+2)| · |e^b - e^a|`.
-/

namespace Talagrand

open MeasureTheory

/-- Cubic smoothstep on `[0,1]`. -/
def smoothstep (v : ℝ) : ℝ := v ^ 2 * (3 - 2 * v)

/-- The `C¹` cutoff: `0` on `(-∞,-1]`, rises to `1` on `[-1,0]`, `1` on
`[0,1]`, falls on `[1,2]`, `0` on `[2,∞)`. -/
noncomputable def cutoff (v : ℝ) : ℝ :=
  if v ≤ -1 then 0
  else if v ≤ 0 then smoothstep (v + 1)
  else if v ≤ 1 then 1
  else if v ≤ 2 then smoothstep (2 - v)
  else 0

/-- Derivative of the cutoff (defined piecewise; `0` at the outer plateaus). -/
noncomputable def cutoff' (v : ℝ) : ℝ :=
  if v ≤ -1 then 0
  else if v ≤ 0 then 6 * (v + 1) - 6 * (v + 1) ^ 2
  else if v ≤ 1 then 0
  else if v ≤ 2 then -(6 * (2 - v) - 6 * (2 - v) ^ 2)
  else 0

/-! ### Values of the individual pieces -/

private lemma cutoff_of_mem_1 {v : ℝ} (h1 : -1 < v) (h2 : v ≤ 0) :
    cutoff v = smoothstep (v + 1) := by
  unfold cutoff
  rw [if_neg (not_le.mpr h1), if_pos h2]

private lemma cutoff_of_mem_3 {v : ℝ} (h1 : 1 < v) (h2 : v ≤ 2) :
    cutoff v = smoothstep (2 - v) := by
  unfold cutoff
  rw [if_neg (not_le.mpr (by linarith : (-1 : ℝ) < v)),
    if_neg (not_le.mpr (by linarith : (0 : ℝ) < v)),
    if_neg (not_le.mpr h1), if_pos h2]

private lemma cutoff'_eq_zero_left {v : ℝ} (h : v ≤ -1) : cutoff' v = 0 := by
  unfold cutoff'; rw [if_pos h]

private lemma cutoff'_eq_piece1 {v : ℝ} (h1 : -1 < v) (h2 : v ≤ 0) :
    cutoff' v = 6 * (v + 1) - 6 * (v + 1) ^ 2 := by
  unfold cutoff'
  rw [if_neg (not_le.mpr h1), if_pos h2]

private lemma cutoff'_eq_zero_mid {v : ℝ} (h1 : 0 < v) (h2 : v ≤ 1) : cutoff' v = 0 := by
  unfold cutoff'
  rw [if_neg (not_le.mpr (by linarith : (-1 : ℝ) < v)), if_neg (not_le.mpr h1), if_pos h2]

private lemma cutoff'_eq_piece3 {v : ℝ} (h1 : 1 < v) (h2 : v ≤ 2) :
    cutoff' v = -(6 * (2 - v) - 6 * (2 - v) ^ 2) := by
  unfold cutoff'
  rw [if_neg (not_le.mpr (by linarith : (-1 : ℝ) < v)),
    if_neg (not_le.mpr (by linarith : (0 : ℝ) < v)),
    if_neg (not_le.mpr h1), if_pos h2]

private lemma cutoff'_eq_zero_right {v : ℝ} (h : 2 < v) : cutoff' v = 0 := by
  unfold cutoff'
  rw [if_neg (not_le.mpr (by linarith : (-1 : ℝ) < v)),
    if_neg (not_le.mpr (by linarith : (0 : ℝ) < v)),
    if_neg (not_le.mpr (by linarith : (1 : ℝ) < v)),
    if_neg (not_le.mpr h)]

lemma cutoff_mem_Icc (v : ℝ) : cutoff v ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [cutoff, smoothstep, Set.mem_Icc]
  split_ifs with h1 h2 h3 h4 <;> constructor <;>
    nlinarith [sq_nonneg (v + 1), sq_nonneg v, sq_nonneg (v - 1), sq_nonneg (v - 2)]

lemma cutoff_eq_one {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : cutoff v = 1 := by
  unfold cutoff
  split_ifs with a b
  · exfalso; linarith
  · rw [show v = 0 from le_antisymm b h0]
    norm_num [smoothstep]
  · rfl

lemma cutoff_eq_zero {v : ℝ} (h : v ≤ -1 ∨ 2 ≤ v) : cutoff v = 0 := by
  unfold cutoff
  rcases h with h | h
  · rw [if_pos h]
  · rw [if_neg (not_le.mpr (by linarith : (-1 : ℝ) < v)),
      if_neg (not_le.mpr (by linarith : (0 : ℝ) < v)),
      if_neg (not_le.mpr (by linarith : (1 : ℝ) < v))]
    split_ifs with h4
    · rw [show v = 2 from le_antisymm h4 h]
      norm_num [smoothstep]
    · rfl

/-! ### Differentiability -/

private lemma hasDerivAt_piece1 (v : ℝ) :
    HasDerivAt (fun w : ℝ => smoothstep (w + 1)) (6 * (v + 1) - 6 * (v + 1) ^ 2) v := by
  have h3 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * v ^ 2) v := by
    simpa using hasDerivAt_pow 3 v
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * v) v := by
    simpa using hasDerivAt_pow 2 v
  have H := ((h3.const_mul (-2 : ℝ)).add (h2.const_mul (-3 : ℝ))).add_const (1 : ℝ)
  have hf : (fun w : ℝ => smoothstep (w + 1))
      = fun w : ℝ => -2 * w ^ 3 + -3 * w ^ 2 + 1 := by
    funext w; unfold smoothstep; ring
  rw [hf, show 6 * (v + 1) - 6 * (v + 1) ^ 2 = -2 * (3 * v ^ 2) + -3 * (2 * v) by ring]
  exact H

private lemma hasDerivAt_piece3 (v : ℝ) :
    HasDerivAt (fun w : ℝ => smoothstep (2 - w)) (-(6 * (2 - v) - 6 * (2 - v) ^ 2)) v := by
  have h3 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * v ^ 2) v := by
    simpa using hasDerivAt_pow 3 v
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * v) v := by
    simpa using hasDerivAt_pow 2 v
  have h1 : HasDerivAt (fun w : ℝ => w) 1 v := hasDerivAt_id v
  have H := (((h3.const_mul (2 : ℝ)).add (h2.const_mul (-9 : ℝ))).add
    (h1.const_mul (12 : ℝ))).add_const (-4 : ℝ)
  have hf : (fun w : ℝ => smoothstep (2 - w))
      = fun w : ℝ => 2 * w ^ 3 + -9 * w ^ 2 + 12 * w + -4 := by
    funext w; unfold smoothstep; ring
  rw [hf, show -(6 * (2 - v) - 6 * (2 - v) ^ 2)
    = 2 * (3 * v ^ 2) + -9 * (2 * v) + 12 * 1 by ring]
  exact H

private lemma hasDerivAt_local {f g : ℝ → ℝ} {c x : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (heq : ∀ y ∈ s, f y = g y) (hg : HasDerivAt g c x) :
    HasDerivAt f c x :=
  hg.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hs.mem_nhds hx) heq)

private lemma hasDerivAt_of_left_right {f : ℝ → ℝ} {c x : ℝ}
    (hl : HasDerivWithinAt f c (Set.Iic x) x) (hr : HasDerivWithinAt f c (Set.Ici x) x) :
    HasDerivAt f c x := by
  rw [← hasDerivWithinAt_univ, ← Set.Iic_union_Ici (a := x)]
  exact hl.union hr

private lemma hasDerivAt_glue {f g h : ℝ → ℝ} {c x l r : ℝ}
    (hlx : l < x) (hxr : x < r)
    (hg : HasDerivAt g c x) (hh : HasDerivAt h c x)
    (hlt : ∀ y ∈ Set.Ioo l r, y ≤ x → f y = g y)
    (hgt : ∀ y ∈ Set.Ioo l r, x ≤ y → f y = h y) :
    HasDerivAt f c x := by
  have hmem : Set.Ioo l r ∈ nhds x := Ioo_mem_nhds hlx hxr
  have hxmem : x ∈ Set.Ioo l r := ⟨hlx, hxr⟩
  refine hasDerivAt_of_left_right ?_ ?_
  · refine (hg.hasDerivWithinAt (s := Set.Iic x)).congr_of_eventuallyEq ?_ (hlt x hxmem le_rfl)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with y hy1 hy2
    exact hlt y hy2 hy1
  · refine (hh.hasDerivWithinAt (s := Set.Ici x)).congr_of_eventuallyEq ?_ (hgt x hxmem le_rfl)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with y hy1 hy2
    exact hgt y hy2 hy1

lemma hasDerivAt_cutoff (v : ℝ) : HasDerivAt cutoff (cutoff' v) v := by
  rcases lt_trichotomy v (-1) with h | h | h
  · -- `v < -1`: locally zero
    rw [cutoff'_eq_zero_left h.le]
    refine hasDerivAt_local isOpen_Iio (show v ∈ Set.Iio (-1 : ℝ) from h) ?_
      (hasDerivAt_const v (0 : ℝ))
    intro y hy
    exact cutoff_eq_zero (Or.inl (le_of_lt hy))
  · -- `v = -1`: glue the zero plateau with the rising cubic
    subst h
    rw [cutoff'_eq_zero_left le_rfl]
    have hh : HasDerivAt (fun w : ℝ => smoothstep (w + 1)) 0 (-1) := by
      have h1 : 6 * ((-1 : ℝ) + 1) - 6 * ((-1 : ℝ) + 1) ^ 2 = 0 := by norm_num
      have H := hasDerivAt_piece1 (-1 : ℝ)
      rwa [h1] at H
    refine hasDerivAt_glue (l := -2) (r := 0) (by norm_num) (by norm_num)
      (hasDerivAt_const _ (0 : ℝ)) hh ?_ ?_
    · intro y _ hy1
      exact cutoff_eq_zero (Or.inl hy1)
    · intro y hy hy1
      rcases eq_or_lt_of_le hy1 with rfl | hlt
      · norm_num [cutoff, smoothstep]
      · exact cutoff_of_mem_1 hlt (le_of_lt hy.2)
  · rcases lt_trichotomy v 0 with h0 | h0 | h0
    · -- `-1 < v < 0`
      rw [cutoff'_eq_piece1 h h0.le]
      refine hasDerivAt_local isOpen_Ioo (show v ∈ Set.Ioo (-1 : ℝ) 0 from ⟨h, h0⟩) ?_
        (hasDerivAt_piece1 v)
      intro y hy
      exact cutoff_of_mem_1 hy.1 hy.2.le
    · -- `v = 0`
      subst h0
      have hz : cutoff' (0 : ℝ) = 0 := by
        rw [cutoff'_eq_piece1 (by norm_num) le_rfl]; norm_num
      rw [hz]
      have hg : HasDerivAt (fun w : ℝ => smoothstep (w + 1)) 0 0 := by
        have h1 : 6 * ((0 : ℝ) + 1) - 6 * ((0 : ℝ) + 1) ^ 2 = 0 := by norm_num
        have H := hasDerivAt_piece1 (0 : ℝ)
        rwa [h1] at H
      refine hasDerivAt_glue (l := -1) (r := 1) (by norm_num) (by norm_num) hg
        (hasDerivAt_const _ (1 : ℝ)) ?_ ?_
      · intro y hy hy1
        exact cutoff_of_mem_1 hy.1 hy1
      · intro y hy hy1
        exact cutoff_eq_one hy1 hy.2.le
    · rcases lt_trichotomy v 1 with h1 | h1 | h1
      · -- `0 < v < 1`
        rw [cutoff'_eq_zero_mid h0 h1.le]
        refine hasDerivAt_local isOpen_Ioo (show v ∈ Set.Ioo (0 : ℝ) 1 from ⟨h0, h1⟩) ?_
          (hasDerivAt_const v (1 : ℝ))
        intro y hy
        exact cutoff_eq_one hy.1.le hy.2.le
      · -- `v = 1`
        subst h1
        have hz : cutoff' (1 : ℝ) = 0 := cutoff'_eq_zero_mid (by norm_num) le_rfl
        rw [hz]
        have hh : HasDerivAt (fun w : ℝ => smoothstep (2 - w)) 0 1 := by
          have h2 : -(6 * (2 - (1 : ℝ)) - 6 * (2 - (1 : ℝ)) ^ 2) = 0 := by norm_num
          have H := hasDerivAt_piece3 (1 : ℝ)
          rwa [h2] at H
        refine hasDerivAt_glue (l := 0) (r := 2) (by norm_num) (by norm_num)
          (hasDerivAt_const _ (1 : ℝ)) hh ?_ ?_
        · intro y hy hy1
          exact cutoff_eq_one hy.1.le hy1
        · intro y hy hy1
          rcases eq_or_lt_of_le hy1 with rfl | hlt
          · norm_num [cutoff, smoothstep]
          · exact cutoff_of_mem_3 hlt hy.2.le
      · rcases lt_trichotomy v 2 with h2 | h2 | h2
        · -- `1 < v < 2`
          rw [cutoff'_eq_piece3 h1 h2.le]
          refine hasDerivAt_local isOpen_Ioo (show v ∈ Set.Ioo (1 : ℝ) 2 from ⟨h1, h2⟩) ?_
            (hasDerivAt_piece3 v)
          intro y hy
          exact cutoff_of_mem_3 hy.1 hy.2.le
        · -- `v = 2`
          subst h2
          have hz : cutoff' (2 : ℝ) = 0 := by
            rw [cutoff'_eq_piece3 (by norm_num) le_rfl]; norm_num
          rw [hz]
          have hg : HasDerivAt (fun w : ℝ => smoothstep (2 - w)) 0 2 := by
            have h3 : -(6 * (2 - (2 : ℝ)) - 6 * (2 - (2 : ℝ)) ^ 2) = 0 := by norm_num
            have H := hasDerivAt_piece3 (2 : ℝ)
            rwa [h3] at H
          refine hasDerivAt_glue (l := 1) (r := 3) (by norm_num) (by norm_num) hg
            (hasDerivAt_const _ (0 : ℝ)) ?_ ?_
          · intro y hy hy1
            exact cutoff_of_mem_3 hy.1 hy1
          · intro y _ hy1
            exact cutoff_eq_zero (Or.inr hy1)
        · -- `2 < v`
          rw [cutoff'_eq_zero_right h2]
          refine hasDerivAt_local isOpen_Ioi (show v ∈ Set.Ioi (2 : ℝ) from h2) ?_
            (hasDerivAt_const v (0 : ℝ))
          intro y hy
          exact cutoff_eq_zero (Or.inr (le_of_lt hy))

lemma abs_cutoff'_le (v : ℝ) : |cutoff' v| ≤ 3 / 2 := by
  rw [abs_le]
  unfold cutoff'
  split_ifs with h1 h2 h3 h4 <;> constructor <;>
    nlinarith [sq_nonneg (2 * v + 1), sq_nonneg (2 * v - 3)]

lemma cutoff'_eq_zero_of_notMem {v : ℝ} (h : v ∉ Set.Ioo (-1 : ℝ) 2) :
    cutoff' v = 0 := by
  simp only [Set.mem_Ioo, not_and_or, not_lt] at h
  rcases h with h | h
  · exact cutoff'_eq_zero_left h
  · rcases eq_or_lt_of_le h with h' | h'
    · rw [cutoff'_eq_piece3 (by linarith) (by linarith)]
      rw [show v = 2 from h'.symm]
      norm_num
    · exact cutoff'_eq_zero_right h'

lemma continuous_cutoff : Continuous cutoff :=
  continuous_iff_continuousAt.mpr fun v => (hasDerivAt_cutoff v).continuousAt

/-- The localized square-root test `ψ_ℓ(v) = e^{v/2}·χ(v-ℓ)`; note
`ψ_ℓ(log h) = √h·χ(log h - ℓ)`. -/
noncomputable def sqrtTest (ℓ v : ℝ) : ℝ := Real.exp (v / 2) * cutoff (v - ℓ)

lemma hasDerivAt_sqrtTest (ℓ v : ℝ) :
    HasDerivAt (sqrtTest ℓ)
      (Real.exp (v / 2) * (cutoff (v - ℓ) / 2 + cutoff' (v - ℓ))) v := by
  have h1 : HasDerivAt (fun w : ℝ => w / 2) (1 / 2 : ℝ) v := by
    simpa using (hasDerivAt_id v).div_const 2
  have he : HasDerivAt (fun w : ℝ => Real.exp (w / 2)) (Real.exp (v / 2) * (1 / 2)) v := h1.exp
  have h2 : HasDerivAt (fun w : ℝ => w - ℓ) 1 v := (hasDerivAt_id v).sub_const ℓ
  have hc : HasDerivAt (fun w : ℝ => cutoff (w - ℓ)) (cutoff' (v - ℓ)) v := by
    simpa [Function.comp_def] using (hasDerivAt_cutoff (v - ℓ)).comp v h2
  have H := he.mul hc
  unfold sqrtTest
  convert H using 1
  ring

private lemma continuous_sqrtTest (ℓ : ℝ) : Continuous (sqrtTest ℓ) := by
  unfold sqrtTest
  have h1 : Continuous fun v : ℝ => Real.exp (v / 2) :=
    Real.continuous_exp.comp' (continuous_id.div_const 2)
  have h2 : Continuous fun v : ℝ => cutoff (v - ℓ) :=
    continuous_cutoff.comp' (continuous_id.sub continuous_const)
  exact h1.mul h2

/-- Pointwise bound on `ψ'` by the AM–GM majorant `t + e^v/t`. -/
private lemma abs_deriv_sqrtTest_le (ℓ v : ℝ) {t : ℝ} (ht : 0 < t) :
    |Real.exp (v / 2) * (cutoff (v - ℓ) / 2 + cutoff' (v - ℓ))| ≤ t + Real.exp v / t := by
  have hE : Real.exp v = Real.exp (v / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hEpos : 0 < Real.exp (v / 2) := Real.exp_pos _
  have hfac : |cutoff (v - ℓ) / 2 + cutoff' (v - ℓ)| ≤ 2 := by
    have h1 := cutoff_mem_Icc (v - ℓ)
    have h2 := abs_cutoff'_le (v - ℓ)
    rw [Set.mem_Icc] at h1
    rw [abs_le] at h2 ⊢
    constructor <;> linarith [h1.1, h1.2]
  have hstep : |Real.exp (v / 2) * (cutoff (v - ℓ) / 2 + cutoff' (v - ℓ))|
      ≤ 2 * Real.exp (v / 2) := by
    calc |Real.exp (v / 2) * (cutoff (v - ℓ) / 2 + cutoff' (v - ℓ))|
        = Real.exp (v / 2) * |cutoff (v - ℓ) / 2 + cutoff' (v - ℓ)| := by
          rw [abs_mul, abs_of_pos hEpos]
      _ ≤ Real.exp (v / 2) * 2 := by
          exact mul_le_mul_of_nonneg_left hfac hEpos.le
      _ = 2 * Real.exp (v / 2) := by ring
  have hamgm : 2 * Real.exp (v / 2) ≤ t + Real.exp v / t := by
    have hkey : t + Real.exp v / t - 2 * Real.exp (v / 2)
        = (t - Real.exp (v / 2)) ^ 2 / t := by
      rw [hE]
      field_simp
      ring
    have : 0 ≤ (t - Real.exp (v / 2)) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    linarith
  linarith

/-- The pointwise-in-`t` AM–GM/FTC estimate on an ordered pair of endpoints. -/
private lemma abs_sqrtTest_sub_le (ℓ x y : ℝ) (hxy : x ≤ y) {t : ℝ} (ht : 0 < t) :
    |sqrtTest ℓ y - sqrtTest ℓ x| ≤ t * (y - x) + (Real.exp y - Real.exp x) / t := by
  have hcont : ContinuousOn (sqrtTest ℓ) (Set.Icc x y) := (continuous_sqrtTest ℓ).continuousOn
  have hφcont : Continuous fun v : ℝ => t + Real.exp v / t :=
    continuous_const.add (Real.continuous_exp.div_const t)
  have hφint : IntegrableOn (fun v : ℝ => t + Real.exp v / t) (Set.Icc x y) volume :=
    hφcont.integrableOn_Icc
  have hint : (∫ v in x..y, (t + Real.exp v / t))
      = t * (y - x) + (Real.exp y - Real.exp x) / t := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((Real.continuous_exp.div_const t).intervalIntegrable x y),
      intervalIntegral.integral_const, intervalIntegral.integral_div, integral_exp]
    simp [smul_eq_mul]
    ring
  have hub : sqrtTest ℓ y - sqrtTest ℓ x ≤ ∫ v in x..y, (t + Real.exp v / t) :=
    intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hxy hcont
      (fun v _ => (hasDerivAt_sqrtTest ℓ v).hasDerivWithinAt) hφint
      (fun v _ => (le_abs_self _).trans (abs_deriv_sqrtTest_le ℓ v ht))
  have hlb : -sqrtTest ℓ y - -sqrtTest ℓ x ≤ ∫ v in x..y, (t + Real.exp v / t) :=
    intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hxy hcont.neg
      (fun v _ => ((hasDerivAt_sqrtTest ℓ v).neg).hasDerivWithinAt) hφint
      (fun v _ => (neg_le_abs _).trans (abs_deriv_sqrtTest_le ℓ v ht))
  rw [hint] at hub hlb
  rw [abs_le]
  constructor <;> linarith

/-- Elementary optimization: `X ≤ t·m + D/t` for every `t > 0` forces
`X² ≤ 4mD`. -/
private lemma sq_le_of_forall_pos {X m D : ℝ} (hX : 0 ≤ X) (hm : 0 ≤ m) (hD : 0 ≤ D)
    (h : ∀ t : ℝ, 0 < t → X ≤ t * m + D / t) : X ^ 2 ≤ 4 * m * D := by
  rcases eq_or_lt_of_le hm with rfl | hm0
  · have hX0 : X ≤ 0 := by
      by_contra hc
      push_neg at hc
      have ht : (0 : ℝ) < (D + 1) / X := by positivity
      have htne : (D + 1) / X ≠ 0 := ne_of_gt ht
      have hkey := h _ ht
      rw [mul_zero, zero_add] at hkey
      have hmul := mul_le_mul_of_nonneg_right hkey ht.le
      have hcancel : D / ((D + 1) / X) * ((D + 1) / X) = D := by field_simp
      rw [hcancel] at hmul
      have hprod : (D + 1) / X * X = D + 1 := by field_simp
      nlinarith [hmul, hprod]
    nlinarith
  · rcases eq_or_lt_of_le hD with rfl | hD0
    · have hX0 : X ≤ 0 := by
        by_contra hc
        push_neg at hc
        have ht : (0 : ℝ) < X / (2 * m) := by positivity
        have hkey := h _ ht
        rw [zero_div, add_zero] at hkey
        have hcancel : X / (2 * m) * m = X / 2 := by
          field_simp
        rw [hcancel] at hkey
        linarith
      nlinarith
    · obtain ⟨s, hs0, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 * m = D :=
        ⟨Real.sqrt (D / m), Real.sqrt_pos.mpr (by positivity), by
          rw [Real.sq_sqrt (by positivity)]; field_simp⟩
      have hsne : s ≠ 0 := ne_of_gt hs0
      have hDs : D / s = s * m := by
        rw [← hs2]; field_simp
      have hkey := h s hs0
      rw [hDs] at hkey
      have hX2 : X ≤ 2 * (s * m) := by linarith
      have h4 : 4 * (s * m) * (s * m) = 4 * m * D := by rw [← hs2]; ring
      nlinarith [mul_self_le_mul_self hX hX2]

private lemma sqrtTest_sq_diff_le_of_le (ℓ a b : ℝ) (hab : a ≤ b) :
    (sqrtTest ℓ b - sqrtTest ℓ a) ^ 2
      ≤ 16 * (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal
          * |Real.exp b - Real.exp a| := by
  have hmnn : 0 ≤ (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal :=
    ENNReal.toReal_nonneg
  have hDnn : 0 ≤ |Real.exp b - Real.exp a| := abs_nonneg _
  by_cases hdeg : b ≤ ℓ - 1 ∨ ℓ + 2 ≤ a
  · have h0 : sqrtTest ℓ b - sqrtTest ℓ a = 0 := by
      unfold sqrtTest
      rcases hdeg with hd | hd
      · rw [cutoff_eq_zero (Or.inl (by linarith : b - ℓ ≤ -1)),
          cutoff_eq_zero (Or.inl (by linarith : a - ℓ ≤ -1))]
        ring
      · rw [cutoff_eq_zero (Or.inr (by linarith : (2 : ℝ) ≤ b - ℓ)),
          cutoff_eq_zero (Or.inr (by linarith : (2 : ℝ) ≤ a - ℓ))]
        ring
    rw [h0]
    have : (0 : ℝ) ≤ 16 * (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal
        * |Real.exp b - Real.exp a| :=
      mul_nonneg (mul_nonneg (by norm_num) hmnn) hDnn
    simpa using this
  push_neg at hdeg
  obtain ⟨hb1, ha2⟩ := hdeg
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = max a (ℓ - 1) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = min b (ℓ + 2) := ⟨_, rfl⟩
  have hap : a ≤ p := hp ▸ le_max_left _ _
  have hlp : ℓ - 1 ≤ p := hp ▸ le_max_right _ _
  have hqb : q ≤ b := hq ▸ min_le_left _ _
  have hql : q ≤ ℓ + 2 := hq ▸ min_le_right _ _
  have hpq : p ≤ q := by
    rw [hp, hq]
    exact max_le (le_min hab ha2.le) (le_min hb1.le (by linarith))
  -- the endpoints may be moved to `p`, `q` without changing `ψ`
  have hψa : sqrtTest ℓ a = sqrtTest ℓ p := by
    rcases le_total (ℓ - 1) a with hcase | hcase
    · rw [hp, max_eq_left hcase]
    · have hpv : p = ℓ - 1 := by rw [hp, max_eq_right hcase]
      rw [hpv]
      unfold sqrtTest
      rw [cutoff_eq_zero (Or.inl (by linarith : a - ℓ ≤ -1)),
        cutoff_eq_zero (Or.inl (by linarith : ℓ - 1 - ℓ ≤ -1))]
      ring
  have hψb : sqrtTest ℓ b = sqrtTest ℓ q := by
    rcases le_total b (ℓ + 2) with hcase | hcase
    · rw [hq, min_eq_left hcase]
    · have hqv : q = ℓ + 2 := by rw [hq, min_eq_right hcase]
      rw [hqv]
      unfold sqrtTest
      rw [cutoff_eq_zero (Or.inr (by linarith : (2 : ℝ) ≤ b - ℓ)),
        cutoff_eq_zero (Or.inr (by linarith : (2 : ℝ) ≤ ℓ + 2 - ℓ))]
      ring
  -- the length of `(p,q)` is at most the measure appearing on the right
  have hsub : Set.Ioo p q ⊆ Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2) := by
    intro x hx
    rw [Set.uIoc_of_le hab]
    exact ⟨⟨lt_of_le_of_lt hap hx.1, hx.2.le.trans hqb⟩,
      ⟨lt_of_le_of_lt hlp hx.1, lt_of_lt_of_le hx.2 hql⟩⟩
  have hfin : volume (Set.Ioo (ℓ - 1) (ℓ + 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hmle : q - p ≤ (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal := by
    have h1 : (volume (Set.Ioo p q)).toReal
        ≤ (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal :=
      ENNReal.toReal_mono (ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_right))
        (measure_mono hsub)
    rwa [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)] at h1
  have hDle : Real.exp q - Real.exp p ≤ |Real.exp b - Real.exp a| := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hab))]
    have e1 : Real.exp a ≤ Real.exp p := Real.exp_le_exp.mpr hap
    have e2 : Real.exp q ≤ Real.exp b := Real.exp_le_exp.mpr hqb
    linarith
  -- optimize the AM–GM bound over `t`
  have hkey : ∀ t : ℝ, 0 < t → |sqrtTest ℓ b - sqrtTest ℓ a|
      ≤ t * (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal
        + |Real.exp b - Real.exp a| / t := by
    intro t ht
    rw [hψa, hψb]
    have h2 := abs_sqrtTest_sub_le ℓ p q hpq ht
    have h3 : t * (q - p)
        ≤ t * (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal :=
      mul_le_mul_of_nonneg_left hmle ht.le
    have h4 : (Real.exp q - Real.exp p) / t ≤ |Real.exp b - Real.exp a| / t := by
      gcongr
    linarith
  have hfinal := sq_le_of_forall_pos (abs_nonneg (sqrtTest ℓ b - sqrtTest ℓ a)) hmnn hDnn hkey
  rw [sq_abs] at hfinal
  nlinarith [mul_nonneg hmnn hDnn]

/-- **Coarea Cauchy–Schwarz bound** [C, proof of the claim in Lemma 4]:
for all `a b : ℝ`,
`(ψ_ℓ(b) - ψ_ℓ(a))² ≤ 16·(volume of [a,b]_* ∩ (ℓ-1,ℓ+2))·|e^b - e^a|`,
where `[a,b]_*` is the unordered interval. (Constant `16 ≥ 4(½+3/2)²`.) -/
theorem sqrtTest_sq_diff_le (ℓ a b : ℝ) :
    (sqrtTest ℓ b - sqrtTest ℓ a) ^ 2
      ≤ 16 * (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal
          * |Real.exp b - Real.exp a| := by
  rcases le_total a b with hab | hab
  · exact sqrtTest_sq_diff_le_of_le ℓ a b hab
  · have H := sqrtTest_sq_diff_le_of_le ℓ b a hab
    rw [Set.uIoc_comm b a] at H
    calc (sqrtTest ℓ b - sqrtTest ℓ a) ^ 2 = (sqrtTest ℓ a - sqrtTest ℓ b) ^ 2 := by ring
      _ ≤ 16 * (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal
            * |Real.exp a - Real.exp b| := H
      _ = 16 * (volume (Set.uIoc a b ∩ Set.Ioo (ℓ - 1) (ℓ + 2))).toReal
            * |Real.exp b - Real.exp a| := by rw [abs_sub_comm]

end Talagrand
