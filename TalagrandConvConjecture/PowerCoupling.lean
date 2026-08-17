import TalagrandConvConjecture.Reverse.Setup

/-!
# The power splitting and its pointwise estimates [LGF §4]

The power coupling of [LGF §4] splits each reverse edge ratio `Y` into two
geometric powers, governed by a frozen exponent `δ̄ ∈ [0,1)`:

* `powerRatio d Y = (1-Y^d)/(1-Y)` for `Y < 1`, `d` at `Y = 1`,
  `(Y-Y^{1-d})/(Y-1)` for `Y > 1` — this is `δ_i` of [LGF §4] with
  `d = δ̄`, `Y = Y_i(t,x)`;
* frozen data at start time `θ`: `Rgap = [ℓ - F_θ(x₀)]₊`, active event
  `ℰ_θ = {Rgap ≥ 2α}`, `δ̄ = α·1_{ℰ}/(Rgap+1)` with `α = 5`
  [LGF eq (3.2)].

Pointwise estimates:
* `0 ≤ powerRatio ≤ Λ_a·d` on `[κ⁻¹, κ]` [LGF Lemma 5.2];
* the conditioned power bound [LGF eq (4.11)];
* the AM–GM drift defect `Y^d ≤ (1-d) + dY` [LGF eq (4.13)];
* the score convexity `2(κ-1)(Y log Y - Y + 1) ≥ log κ·(1-Y)²` on
  `[κ⁻¹,κ]` [C eq (40); LGF §4.4];
* basic facts about `Λ_a = κ log κ/(κ-1)` and `K_a = κ^{3/2}√Λ_a`.
-/

namespace Talagrand

/-- The universal stopping-level constant `α = 5` of [LGF eq (3.2)]. -/
def alphaC : ℝ := 5

/-- `Λ_a = κ_a·log κ_a/(κ_a - 1)` [LGF §3]. -/
noncomputable def Lam (a : ℝ) : ℝ :=
  kappa a * Real.log (kappa a) / (kappa a - 1)

/-- The power-splitting coefficient `δ_i` of [LGF §4] as a function of the
frozen exponent `d = δ̄` and the edge ratio `Y = Y_i(t,x)`:
`powerRatio δ̄ Y = δ_i(t,x)`. -/
noncomputable def powerRatio (d Y : ℝ) : ℝ :=
  if Y < 1 then (1 - Y ^ d) / (1 - Y)
  else if Y = 1 then d
  else (Y - Y ^ (1 - d)) / (Y - 1)

section OneDim

variable {κ d Y : ℝ}

/-! ### Elementary logarithm inequalities

All of `powerRatio_le` and `score_convexity` reduce to three facts about
`Real.log`: the chord bound (concavity), `2y log y ≥ y² - 1` on `(0,1]`, and
`(y+1) log y ≥ 2(y-1)` on `[1,∞)`. -/

/-- Chord bound from concavity of `log`: on `[x,y]` the logarithm lies above
the chord through its endpoints. -/
private lemma log_chord {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hz1 : x ≤ z)
    (hz2 : z ≤ y) :
    (y - z) * Real.log x + (z - x) * Real.log y ≤ (y - x) * Real.log z := by
  have hy : 0 < y := hx.trans hxy
  have hz : 0 < z := lt_of_lt_of_le hx hz1
  have hd : 0 < y - x := by linarith
  have hdne : y - x ≠ 0 := ne_of_gt hd
  have ha : 0 ≤ (y - z) / (y - x) := div_nonneg (by linarith) hd.le
  have hb : 0 ≤ (z - x) / (y - x) := div_nonneg (by linarith) hd.le
  have hab : (y - z) / (y - x) + (z - x) / (y - x) = 1 := by
    rw [← add_div]
    have hnum : y - z + (z - x) = y - x := by ring
    rw [hnum, div_self hdne]
  have hmem : ((y - z) / (y - x)) • x + ((z - x) / (y - x)) • y = z := by
    have hcomb : ((y - z) / (y - x)) * x + ((z - x) / (y - x)) * y
        = ((y - z) * x + (z - x) * y) / (y - x) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    simp only [smul_eq_mul, hcomb]
    rw [div_eq_iff hdne]
    ring
  have hcc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr hy) ha hb hab
  rw [hmem] at hcc
  simp only [smul_eq_mul, div_mul_eq_mul_div, ← add_div] at hcc
  rw [div_le_iff₀ hd] at hcc
  linarith

/-- `2y·log y ≥ y² - 1` for `0 < y ≤ 1`; equivalently
`y log y - y + 1 ≥ (1-y)²/2`. -/
private lemma sq_sub_one_le_two_mul_log {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    y ^ 2 - 1 ≤ 2 * y * Real.log y := by
  have hd : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => 2 * s * Real.log s - s ^ 2 + 1)
        (2 * Real.log t + 2 - 2 * t) t := by
    intro t ht0
    have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt ht0)
    have h3 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h4 := ((h1.mul h2).sub h3).add_const 1
    have heq : 2 * Real.log t + 2 * t * t⁻¹ - 2 * t
        = 2 * Real.log t + 2 - 2 * t := by
      field_simp
    rwa [heq] at h4
  have hanti : AntitoneOn (fun s : ℝ => 2 * s * Real.log s - s ^ 2 + 1)
      (Set.Ioc (0 : ℝ) 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 1)
      (f' := fun t => 2 * Real.log t + 2 - 2 * t) ?_ ?_ ?_
    · intro t ht
      exact (hd t ht.1).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      exact (hd t ht.1).hasDerivWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      have := Real.log_le_sub_one_of_pos ht.1
      linarith
  have h := hanti (Set.mem_Ioc.mpr ⟨hy0, hy1⟩)
    (Set.mem_Ioc.mpr ⟨one_pos, le_rfl⟩) hy1
  norm_num at h
  linarith

/-- `(y+1)·log y ≥ 2(y-1)` for `y ≥ 1`. -/
private lemma two_mul_sub_one_le_add_one_mul_log {y : ℝ} (hy : 1 ≤ y) :
    2 * (y - 1) ≤ (y + 1) * Real.log y := by
  have hd : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => (s + 1) * Real.log s - 2 * (s - 1))
        (Real.log t + t⁻¹ - 1) t := by
    intro t ht0
    have h1 : HasDerivAt (fun s : ℝ => s + 1) 1 t := (hasDerivAt_id t).add_const 1
    have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt ht0)
    have h3 : HasDerivAt (fun s : ℝ => 2 * (s - 1)) 2 t := by
      simpa using ((hasDerivAt_id t).sub_const 1).const_mul (2 : ℝ)
    have h4 := (h1.mul h2).sub h3
    have heq : 1 * Real.log t + (t + 1) * t⁻¹ - 2 = Real.log t + t⁻¹ - 1 := by
      field_simp
      ring
    rwa [heq] at h4
  have hmono : MonotoneOn (fun s : ℝ => (s + 1) * Real.log s - 2 * (s - 1))
      (Set.Ici (1 : ℝ)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (f' := fun t => Real.log t + t⁻¹ - 1) ?_ ?_ ?_
    · intro t ht
      exact (hd t (lt_of_lt_of_le one_pos ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hd t (lt_trans one_pos ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
      have := Real.one_sub_inv_le_log_of_pos ht0
      linarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  norm_num at h
  linarith

/-- `1 ≤ κ·log κ/(κ-1)`. -/
private lemma one_le_lam_of (hκ : 1 < κ) : 1 ≤ κ * Real.log κ / (κ - 1) := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have h : 1 - κ⁻¹ ≤ Real.log κ := Real.one_sub_inv_le_log_of_pos hκ0
  have hkk : κ * (1 - κ⁻¹) = κ - 1 := by field_simp
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < κ - 1)]
  nlinarith [mul_le_mul_of_nonneg_left h hκ0.le, hkk]

/-- `κ·log κ/(κ-1) ≤ κ`. -/
private lemma lam_of_le (hκ : 1 < κ) : κ * Real.log κ / (κ - 1) ≤ κ := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have h := Real.log_le_sub_one_of_pos hκ0
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < κ - 1)]
  nlinarith [h, hκ0]

/-- `1 ≤ Λ_a ≤ κ_a` (from `(κ-1)/κ ≤ log κ ≤ κ-1`) [LGF, proof of
Prop 3.2]. -/
lemma one_le_Lam {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 1 ≤ Lam a :=
  one_le_lam_of (one_lt_kappa ha0 ha1)

lemma Lam_le_kappa {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Lam a ≤ kappa a :=
  lam_of_le (one_lt_kappa ha0 ha1)

/-- `K_a² = κ_a³·Λ_a` [LGF, Step 1 of Prop 3.2]. -/
lemma Ka_sq_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Ka a ^ 2 = kappa a ^ 3 * Lam a := by
  have hκ : 1 < kappa a := one_lt_kappa ha0 ha1
  have hne : kappa a - 1 ≠ 0 := by
    have : (0 : ℝ) < kappa a - 1 := by linarith
    exact ne_of_gt this
  have hnn : 0 ≤ Real.log (kappa a) / (kappa a - 1) :=
    div_nonneg (Real.log_nonneg hκ.le) (by linarith)
  simp only [Ka, Lam, mul_pow, Real.sq_sqrt hnn]
  field_simp

lemma powerRatio_nonneg (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hY : 0 < Y) :
    0 ≤ powerRatio d Y := by
  unfold powerRatio
  split_ifs with h1 h2
  · exact div_nonneg (by linarith [Real.rpow_le_one hY.le h1.le hd0])
      (by linarith)
  · exact hd0
  · have hY1 : 1 < Y := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    have hle : Y ^ (1 - d) ≤ Y ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hY1.le (by linarith)
    rw [Real.rpow_one] at hle
    exact div_nonneg (by linarith) (by linarith)

/-- Chord form of concavity used for the `Y < 1` branch of [LGF Lemma 5.2]:
`-log Y·(κ-1) ≤ κ log κ·(1-Y)` for `Y ∈ [κ⁻¹, 1]`. -/
private lemma log_lower_chord (hκ : 1 < κ) (hY1 : κ⁻¹ ≤ Y) (hY2 : Y ≤ 1) :
    -Real.log Y * (κ - 1) ≤ κ * Real.log κ * (1 - Y) := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hκne : κ ≠ 0 := ne_of_gt hκ0
  have hinv0 : (0 : ℝ) < κ⁻¹ := inv_pos.mpr hκ0
  have hkk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκne
  have hinv1 : κ⁻¹ < 1 := by nlinarith [hkk, hinv0, hκ]
  have hc := log_chord hinv0 hinv1 hY1 hY2
  rw [Real.log_inv, Real.log_one] at hc
  have hmul := mul_le_mul_of_nonneg_left hc hκ0.le
  have hexp : κ * ((1 - κ⁻¹) * Real.log Y) = (κ - 1) * Real.log Y := by
    field_simp
  rw [hexp] at hmul
  nlinarith [hmul]

/-- The `Y < 1` branch of [LGF Lemma 5.2]. -/
private lemma powerRatio_le_of_lt_one (hκ : 1 < κ) (hd0 : 0 ≤ d)
    (hY1 : κ⁻¹ ≤ Y) (hY : Y < 1) :
    powerRatio d Y ≤ κ * Real.log κ / (κ - 1) * d := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hden : (0 : ℝ) < κ - 1 := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (inv_pos.mpr hκ0) hY1
  have hchord := log_lower_chord hκ hY1 hY.le
  have hexp : 1 - Y ^ d ≤ d * (-Real.log Y) := by
    have h := Real.add_one_le_exp (Real.log Y * d)
    rw [← Real.rpow_def_of_pos hYpos d] at h
    linarith
  unfold powerRatio
  rw [if_pos hY, div_le_iff₀ (by linarith : (0 : ℝ) < 1 - Y)]
  have hfrac : κ * Real.log κ / (κ - 1) * d * (1 - Y)
      = d * (κ * Real.log κ * (1 - Y)) / (κ - 1) := by
    field_simp
  rw [hfrac, le_div_iff₀ hden]
  have h2 : (1 - Y ^ d) * (κ - 1) ≤ d * (-Real.log Y) * (κ - 1) :=
    mul_le_mul_of_nonneg_right hexp hden.le
  have h3 : d * (-Real.log Y * (κ - 1)) ≤ d * (κ * Real.log κ * (1 - Y)) :=
    mul_le_mul_of_nonneg_left hchord hd0
  nlinarith [h2, h3]

/-- The power ratio is invariant under `Y ↦ Y⁻¹` (the two geometric branches
of the coupling are exchanged by inverting the edge ratio). -/
private lemma powerRatio_inv (hY : 1 < Y) : powerRatio d Y = powerRatio d Y⁻¹ := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hYne : Y ≠ 0 := ne_of_gt hY0
  have hipos : (0 : ℝ) < Y⁻¹ := inv_pos.mpr hY0
  have hkk : Y * Y⁻¹ = 1 := mul_inv_cancel₀ hYne
  have hinv1 : Y⁻¹ < 1 := by nlinarith [hkk, hipos, hY]
  have hp : (0 : ℝ) < Y ^ d := Real.rpow_pos_of_pos hY0 d
  have hpne : Y ^ d ≠ 0 := ne_of_gt hp
  have hY1ne : Y - 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < Y - 1)
  unfold powerRatio
  rw [if_neg (not_lt.mpr hY.le), if_neg (ne_of_gt hY), if_pos hinv1,
    Real.inv_rpow hY0.le]
  have h1d : Y ^ (1 - d) = Y / Y ^ d := by
    rw [Real.rpow_sub hY0, Real.rpow_one]
  have hne2 : (1 : ℝ) - Y⁻¹ ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - Y⁻¹)
  rw [h1d, div_eq_div_iff hY1ne hne2]
  field_simp

/-- **Size of the power perturbation** [LGF Lemma 5.2]: on `[κ⁻¹, κ]`,
`powerRatio d Y ≤ (κ·log κ/(κ-1))·d`. -/
theorem powerRatio_le (hκ : 1 < κ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hY1 : κ⁻¹ ≤ Y) (hY2 : Y ≤ κ) :
    powerRatio d Y ≤ κ * Real.log κ / (κ - 1) * d := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  rcases lt_trichotomy Y 1 with h | h | h
  · exact powerRatio_le_of_lt_one hκ hd0 hY1 h
  · have hΛ : 1 ≤ κ * Real.log κ / (κ - 1) := one_le_lam_of hκ
    unfold powerRatio
    rw [if_neg (by rw [h]; exact lt_irrefl 1), if_pos h]
    nlinarith [hΛ, hd0]
  · have hY0 : (0 : ℝ) < Y := by linarith
    have hipos : (0 : ℝ) < Y⁻¹ := inv_pos.mpr hY0
    have hkk : Y * Y⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hY0)
    have hinvlt : Y⁻¹ < 1 := by nlinarith [hkk, hipos, h]
    have hinvY1 : κ⁻¹ ≤ Y⁻¹ := by
      have e1 : κ⁻¹ * (Y * κ) = Y := by field_simp
      have e2 : Y⁻¹ * (Y * κ) = κ := by field_simp
      nlinarith [e1, e2, mul_pos hY0 hκ0, hY2]
    rw [powerRatio_inv h]
    exact powerRatio_le_of_lt_one hκ hd0 hinvY1 hinvlt

/-- The two splitting identities: for `Y < 1`,
`(1 - Y^d)/2 = powerRatio d Y·(1-Y)/2`; for `Y > 1`,
`(Y - Y^{1-d})/2 = -powerRatio d Y·(1-Y)/2` [LGF §4, interpretation of the
coupling rates; proof of Lemma 5.1]. -/
lemma one_sub_rpow_eq (hY0 : 0 < Y) (hY : Y < 1) :
    (1 - Y ^ d) / 2 = powerRatio d Y * ((1 - Y) / 2) := by
  have h : (1 : ℝ) - Y ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - Y)
  unfold powerRatio
  rw [if_pos hY]
  field_simp

lemma rpow_sub_eq (hY : 1 < Y) :
    (Y - Y ^ (1 - d)) / 2 = -(powerRatio d Y * ((1 - Y) / 2)) := by
  have h : Y - 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < Y - 1)
  unfold powerRatio
  rw [if_neg (not_lt.mpr hY.le), if_neg (ne_of_gt hY)]
  field_simp
  ring

/-- **AM–GM drift defect** [LGF eq (4.13)]: for `Y > 0`, `d ∈ [0,1]`,
`Y^d ≤ (1-d) + d·Y`; hence the switched power drift is nonpositive. -/
theorem rpow_le_one_sub_add_mul (hY : 0 < Y) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    Y ^ d ≤ (1 - d) + d * Y := by
  have h := Real.geom_mean_le_arith_mean2_weighted (by linarith : (0 : ℝ) ≤ 1 - d)
    hd0 (by norm_num : (0 : ℝ) ≤ 1) hY.le (by ring)
  simpa using h

/-- **Score convexity** [C eq (40)]: for `κ > 1` and `Y ∈ [κ⁻¹, κ]`,
`2(κ-1)(Y·log Y - Y + 1) ≥ log κ·(1-Y)²`; equivalently
`½(Y log Y - Y + 1) ≥ (log κ/(κ-1))·S²` with `S = (1-Y)/2`. -/
theorem score_convexity (hκ : 1 < κ) (hY1 : κ⁻¹ ≤ Y) (hY2 : Y ≤ κ) :
    Real.log κ * (1 - Y) ^ 2 ≤ 2 * (κ - 1) * (Y * Real.log Y - Y + 1) := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (inv_pos.mpr hκ0) hY1
  have hL : Real.log κ ≤ κ - 1 := Real.log_le_sub_one_of_pos hκ0
  rcases le_or_gt Y 1 with hY | hY
  · -- `Y ≤ 1`: use `2(Y log Y - Y + 1) ≥ (1-Y)²` and `log κ ≤ κ-1`.
    have hD : Y ^ 2 - 1 ≤ 2 * Y * Real.log Y := sq_sub_one_le_two_mul_log hYpos hY
    have h1 : 0 ≤ (κ - 1 - Real.log κ) * (1 - Y) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : 0 ≤ (κ - 1) * (2 * Y * Real.log Y - Y ^ 2 + 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2]
  · -- `1 < Y ≤ κ`: chord bound plus `(Y+1) log Y ≥ 2(Y-1)`.
    have hchord := log_chord (x := 1) (y := κ) (z := Y) one_pos hκ hY.le hY2
    rw [Real.log_one] at hchord
    have hA : 2 * (Y - 1) ≤ (Y + 1) * Real.log Y :=
      two_mul_sub_one_le_add_one_mul_log hY.le
    have h1 : 0 ≤ (Y - 1) * ((κ - 1) * Real.log Y - (Y - 1) * Real.log κ) :=
      mul_nonneg (by linarith) (by nlinarith [hchord])
    have h2 : 0 ≤ (κ - 1) * ((Y + 1) * Real.log Y - 2 * (Y - 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2]

/-- The conditioned-coefficient bound, `S ≤ 0` branch [LGF §5.3]: for
`Y ≥ 1` in `[κ⁻¹,κ]` and `λ > 0`,
`λ·(1 - Y^{-d})/(Y-1) ≤ λ·d` — packaged as the statement actually used:
`(λ·powerRatio d Y/Y) ≤ λ·d` for `Y > 1`. -/
lemma lam_mul_powerRatio_div_le (hY : 1 < Y) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    lam * powerRatio d Y / Y ≤ lam * d := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hp : (0 : ℝ) < Y ^ d := Real.rpow_pos_of_pos hY0 d
  have hkey : powerRatio d Y / Y ≤ d := by
    unfold powerRatio
    rw [if_neg (not_lt.mpr hY.le), if_neg (ne_of_gt hY), div_div,
      div_le_iff₀ (mul_pos (by linarith : (0 : ℝ) < Y - 1) hY0)]
    have h1d : Y ^ (1 - d) = Y / Y ^ d := by
      rw [Real.rpow_sub hY0, Real.rpow_one]
    have hexp : 1 - (Y ^ d)⁻¹ ≤ d * Real.log Y := by
      have h := Real.add_one_le_exp (-(Real.log Y * d))
      rw [Real.exp_neg, ← Real.rpow_def_of_pos hY0 d] at h
      linarith
    have hlogle : Real.log Y ≤ Y - 1 := Real.log_le_sub_one_of_pos hY0
    rw [h1d]
    have e1 : Y - Y / Y ^ d = Y * (1 - (Y ^ d)⁻¹) := by
      field_simp
    rw [e1]
    have h2 : Y * (1 - (Y ^ d)⁻¹) ≤ Y * (d * Real.log Y) :=
      mul_le_mul_of_nonneg_left hexp hY0.le
    have h3 : Y * (d * Real.log Y) ≤ Y * (d * (Y - 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogle hd0) hY0.le
    nlinarith [h2, h3]
  calc lam * powerRatio d Y / Y = lam * (powerRatio d Y / Y) := by ring
    _ ≤ lam * d := mul_le_mul_of_nonneg_left hkey hlam

end OneDim

/-! ## Frozen data at the perturbation start [LGF eq (3.2)] -/

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- Remaining gap `R_θ = [ℓ - F_θ(x₀)]₊` at start time `θ`, starting point
`x₀` [LGF eq (3.2)]. -/
noncomputable def Rgap (ℓ θ : ℝ) (x₀ : Cube n) : ℝ := max (ℓ - D.F θ x₀) 0

/-- The active (excess-gap) event `ℰ_θ = {R_θ ≥ 2α}` as a set of starting
points [LGF eq (3.2)]. -/
def activeSet (ℓ θ : ℝ) : Set (Cube n) := {x₀ | 2 * alphaC ≤ D.Rgap ℓ θ x₀}

open Classical in
/-- Frozen perturbation size `δ̄ = α·1_{ℰ_θ}/(R_θ+1)` [LGF eq (3.2)]. -/
noncomputable def dbar (ℓ θ : ℝ) (x₀ : Cube n) : ℝ :=
  if 2 * alphaC ≤ D.Rgap ℓ θ x₀ then alphaC / (D.Rgap ℓ θ x₀ + 1) else 0

lemma Rgap_nonneg (ℓ θ : ℝ) (x₀ : Cube n) : 0 ≤ D.Rgap ℓ θ x₀ :=
  le_max_right _ _

lemma dbar_nonneg (ℓ θ : ℝ) (x₀ : Cube n) : 0 ≤ D.dbar ℓ θ x₀ := by
  have hR := D.Rgap_nonneg ℓ θ x₀
  unfold dbar
  split_ifs with h
  · exact div_nonneg (by norm_num [alphaC]) (by linarith)
  · exact le_rfl

/-- `δ̄ ≤ α/(2α+1) < 1/2` on the active set, `0` off it. -/
lemma dbar_lt_half (ℓ θ : ℝ) (x₀ : Cube n) : D.dbar ℓ θ x₀ < 1 / 2 := by
  have hR := D.Rgap_nonneg ℓ θ x₀
  unfold dbar
  split_ifs with h
  · rw [div_lt_div_iff₀ (by linarith : (0 : ℝ) < D.Rgap ℓ θ x₀ + 1)
      (by norm_num : (0 : ℝ) < 2)]
    simp only [alphaC] at h ⊢
    linarith
  · norm_num

/-- On the active set, `δ̄·(R_θ+1) = α` [LGF, proof of Lemma 3.4]. -/
lemma dbar_mul_Rgap_add_one {ℓ θ : ℝ} {x₀ : Cube n}
    (h : x₀ ∈ D.activeSet ℓ θ) :
    D.dbar ℓ θ x₀ * (D.Rgap ℓ θ x₀ + 1) = alphaC := by
  have h' : 2 * alphaC ≤ D.Rgap ℓ θ x₀ := h
  have hR := D.Rgap_nonneg ℓ θ x₀
  have hne : D.Rgap ℓ θ x₀ + 1 ≠ 0 := ne_of_gt (by linarith)
  unfold dbar
  rw [if_pos h']
  field_simp

/-- Off the active set `δ̄ = 0` (the coupling degenerates to `W = V`). -/
lemma dbar_eq_zero {ℓ θ : ℝ} {x₀ : Cube n} (h : x₀ ∉ D.activeSet ℓ θ) :
    D.dbar ℓ θ x₀ = 0 := by
  have h' : ¬ (2 * alphaC ≤ D.Rgap ℓ θ x₀) := h
  unfold dbar
  rw [if_neg h']

open Classical in
/-- **Conditioned power bound** [LGF eq (4.11)]: for `t ≤ T_o`, on the active
set, writing `d = δ̄`,
`(δ_i·(1_{S_i>0} + r_{t,i}^ζ·1_{S_i≤0}))² ≤ κ_a·Λ_a²·δ̄²·λ_{t,i}^ζ(x)`,
where `δ_i = powerRatio δ̄ Y` and `r_{t,i}^ζ = λ_{t,i}^ζ/Y_i`. -/
theorem conditioned_power_bound {ℓ θ t : ℝ} (ht : t ≤ obsT) {x₀ : Cube n}
    (i : Fin n) (x ζ : Cube n) :
    (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) *
        (if 0 < D.Sc t i x then 1 else D.lam t i x ζ / D.Y t i x)) ^ 2
      ≤ kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ := by
  have hκ : 1 < kappa D.a := one_lt_kappa D.ha0 D.ha1
  have hκ0 : (0 : ℝ) < kappa D.a := by linarith
  have hΛ1 : 1 ≤ Lam D.a := one_le_Lam D.ha0 D.ha1
  have hΛeq : Lam D.a
      = kappa D.a * Real.log (kappa D.a) / (kappa D.a - 1) := rfl
  have hd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
  have hd1 : D.dbar ℓ θ x₀ ≤ 1 := by linarith [D.dbar_lt_half ℓ θ x₀]
  have hY1 : (kappa D.a)⁻¹ ≤ D.Y t i x := D.kappa_inv_le_Y ht i x
  have hY2 : D.Y t i x ≤ kappa D.a := D.Y_le_kappa ht i x
  have hYpos : 0 < D.Y t i x := lt_of_lt_of_le (inv_pos.mpr hκ0) hY1
  have hlam1 : (kappa D.a)⁻¹ ≤ D.lam t i x ζ := D.kappa_inv_le_lam ht i x ζ
  have hlam2 : D.lam t i x ζ ≤ kappa D.a := D.lam_le_kappa ht i x ζ
  have hlampos : 0 < D.lam t i x ζ := D.lam_pos ht i x ζ
  have hpr0 : 0 ≤ powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) :=
    powerRatio_nonneg hd0 hd1 hYpos
  -- `κ·λ ≥ 1` and `λ ≤ κΛ²`, the two uses of the edge bounds
  have hkl : 1 ≤ kappa D.a * D.lam t i x ζ := by
    have h := mul_le_mul_of_nonneg_left hlam1 hκ0.le
    rw [mul_inv_cancel₀ (ne_of_gt hκ0)] at h
    linarith
  have hΛsq : (1 : ℝ) ≤ Lam D.a ^ 2 := by nlinarith [hΛ1]
  have hlamΛ : D.lam t i x ζ ≤ kappa D.a * Lam D.a ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hΛsq hκ0.le
    linarith [h, hlam2]
  by_cases hS : 0 < D.Sc t i x
  · rw [if_pos hS, mul_one]
    have hprle : powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)
        ≤ Lam D.a * D.dbar ℓ θ x₀ := by
      rw [hΛeq]
      exact powerRatio_le hκ hd0 hd1 hY1 hY2
    have hsq : powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) ^ 2
        ≤ (Lam D.a * D.dbar ℓ θ x₀) ^ 2 := by
      nlinarith [mul_self_le_mul_self hpr0 hprle]
    have h0 : 0 ≤ Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 := by positivity
    nlinarith [hsq, mul_nonneg h0 (by linarith :
      (0 : ℝ) ≤ kappa D.a * D.lam t i x ζ - 1)]
  · rw [if_neg hS]
    have hYge : 1 ≤ D.Y t i x := by
      have hSle : D.Sc t i x ≤ 0 := not_lt.mp hS
      simp only [Dat.Sc] at hSle
      linarith
    rcases eq_or_lt_of_le hYge with hYeq | hYgt
    · -- `Y = 1`: the ratio is exactly `δ̄` and the factor is `λ`
      have hpr : powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) = D.dbar ℓ θ x₀ := by
        unfold powerRatio
        rw [if_neg (by rw [← hYeq]; exact lt_irrefl 1), if_pos hYeq.symm]
      rw [hpr, ← hYeq, div_one]
      have hfin : 0 ≤ D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ *
          (kappa D.a * Lam D.a ^ 2 - D.lam t i x ζ) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hlampos.le) (by linarith)
      nlinarith [hfin]
    · -- `Y > 1`: the conditioned ratio is at most `λ·δ̄`
      have hkey : D.lam t i x ζ * powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)
            / D.Y t i x ≤ D.lam t i x ζ * D.dbar ℓ θ x₀ :=
        lam_mul_powerRatio_div_le hYgt hd0 hd1 hlampos.le
      have heq : powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) *
          (D.lam t i x ζ / D.Y t i x)
          = D.lam t i x ζ * powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)
            / D.Y t i x := by ring
      rw [heq]
      have hnn : 0 ≤ D.lam t i x ζ * powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)
          / D.Y t i x :=
        div_nonneg (mul_nonneg hlampos.le hpr0) hYpos.le
      have hsq := mul_self_le_mul_self hnn hkey
      have hfin : 0 ≤ D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ *
          (kappa D.a * Lam D.a ^ 2 - D.lam t i x ζ) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hlampos.le) (by linarith)
      nlinarith [hsq, hfin]

end Dat

end Talagrand
