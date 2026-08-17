import Mathlib

/-!
# Calculus across finitely many exceptional times; root finiteness

Two pieces of glue used throughout the de-probabilized proof:

1. **FTC with a finite exceptional set**: if `u` is continuous on `[a,b]` and
   differentiable with derivative `v` off a finite set, with `v` interval
   integrable, then `u b - u a = ∫_a^b v`; plus inequality versions. These
   turn the cell-wise ODE identities of the glued flows into endpoint
   identities/estimates.

2. **Finiteness of crossing times**: `t ↦ P_{s(t)} f(x)` is a polynomial in
   `e^{-t}`; hence for `c ≠` its constant term, `{t | value = c}` is finite.
   This makes the barrier `{F_t(x) ≥ ℓ+1}` piecewise constant in `t`
   ([LGF §3], stopping time `τ`), and similarly the level sets in
   [C Lemma 4]'s derivative computation.
-/

namespace Talagrand

open MeasureTheory intervalIntegral

/-! ### The exception-free cases -/

private lemma sub_eq_integral_clean {u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt u (v t) t)
    (hv : IntervalIntegrable v volume a b) :
    u b - u a = ∫ t in a..b, v t :=
  (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hu
    (fun t ht => (hd t ht).hasDerivWithinAt) hv).symm

private lemma sub_le_integral_clean {u w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, ∃ v ≤ w t, HasDerivAt u v t)
    (hw : IntervalIntegrable w volume a b) :
    u b - u a ≤ ∫ t in a..b, w t := by
  choose! g hgle hgd using hd
  exact intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hu
    (fun t ht => (hgd t ht).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hw) hgle

/-! ### Induction on the exceptional set -/

private lemma sub_eq_integral_aux (n : ℕ) : ∀ (Z : Finset ℝ) (u v : ℝ → ℝ) (a b : ℝ),
    Z.card = n → a ≤ b → ContinuousOn u (Set.Icc a b) →
    (∀ t ∈ Set.Ioo a b, t ∉ Z → HasDerivAt u (v t) t) →
    IntervalIntegrable v volume a b → u b - u a = ∫ t in a..b, v t := by
  induction n with
  | zero =>
    intro Z u v a b hcard hab hu hd hv
    have hZ : Z = ∅ := Finset.card_eq_zero.mp hcard
    exact sub_eq_integral_clean hab hu (fun t ht => hd t ht (by simp [hZ])) hv
  | succ n ih =>
    intro Z u v a b hcard hab hu hd hv
    by_cases hex : ∃ z ∈ Z, z ∈ Set.Ioo a b
    · obtain ⟨z, hzZ, hz⟩ := hex
      have hcard' : (Z.erase z).card = n := by
        simp [Finset.card_erase_of_mem hzZ, hcard]
      have haz : a ≤ z := hz.1.le
      have hzb : z ≤ b := hz.2.le
      have hsub1 : Set.uIcc a z ⊆ Set.uIcc a b := by
        rw [Set.uIcc_of_le haz, Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc le_rfl hzb
      have hsub2 : Set.uIcc z b ⊆ Set.uIcc a b := by
        rw [Set.uIcc_of_le hzb, Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc haz le_rfl
      have h1 : u z - u a = ∫ t in a..z, v t := by
        refine ih (Z.erase z) u v a z hcard' haz
          (hu.mono (Set.Icc_subset_Icc le_rfl hzb)) ?_ (hv.mono_set hsub1)
        intro t ht htZ
        exact hd t ⟨ht.1, ht.2.trans hz.2⟩
          (fun htZ' => htZ (Finset.mem_erase.mpr ⟨ne_of_lt ht.2, htZ'⟩))
      have h2 : u b - u z = ∫ t in z..b, v t := by
        refine ih (Z.erase z) u v z b hcard' hzb
          (hu.mono (Set.Icc_subset_Icc haz le_rfl)) ?_ (hv.mono_set hsub2)
        intro t ht htZ
        exact hd t ⟨hz.1.trans ht.1, ht.2⟩
          (fun htZ' => htZ (Finset.mem_erase.mpr ⟨(ne_of_lt ht.1).symm, htZ'⟩))
      have h3 : (∫ t in a..z, v t) + (∫ t in z..b, v t) = ∫ t in a..b, v t :=
        intervalIntegral.integral_add_adjacent_intervals (hv.mono_set hsub1) (hv.mono_set hsub2)
      linarith
    · push_neg at hex
      exact sub_eq_integral_clean hab hu (fun t ht => hd t ht (fun htZ => hex t htZ ht)) hv

private lemma sub_le_integral_aux (n : ℕ) : ∀ (Z : Finset ℝ) (u w : ℝ → ℝ) (a b : ℝ),
    Z.card = n → a ≤ b → ContinuousOn u (Set.Icc a b) →
    (∀ t ∈ Set.Ioo a b, t ∉ Z → ∃ v ≤ w t, HasDerivAt u v t) →
    IntervalIntegrable w volume a b → u b - u a ≤ ∫ t in a..b, w t := by
  induction n with
  | zero =>
    intro Z u w a b hcard hab hu hd hw
    have hZ : Z = ∅ := Finset.card_eq_zero.mp hcard
    exact sub_le_integral_clean hab hu (fun t ht => hd t ht (by simp [hZ])) hw
  | succ n ih =>
    intro Z u w a b hcard hab hu hd hw
    by_cases hex : ∃ z ∈ Z, z ∈ Set.Ioo a b
    · obtain ⟨z, hzZ, hz⟩ := hex
      have hcard' : (Z.erase z).card = n := by
        simp [Finset.card_erase_of_mem hzZ, hcard]
      have haz : a ≤ z := hz.1.le
      have hzb : z ≤ b := hz.2.le
      have hsub1 : Set.uIcc a z ⊆ Set.uIcc a b := by
        rw [Set.uIcc_of_le haz, Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc le_rfl hzb
      have hsub2 : Set.uIcc z b ⊆ Set.uIcc a b := by
        rw [Set.uIcc_of_le hzb, Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc haz le_rfl
      have h1 : u z - u a ≤ ∫ t in a..z, w t := by
        refine ih (Z.erase z) u w a z hcard' haz
          (hu.mono (Set.Icc_subset_Icc le_rfl hzb)) ?_ (hw.mono_set hsub1)
        intro t ht htZ
        exact hd t ⟨ht.1, ht.2.trans hz.2⟩
          (fun htZ' => htZ (Finset.mem_erase.mpr ⟨ne_of_lt ht.2, htZ'⟩))
      have h2 : u b - u z ≤ ∫ t in z..b, w t := by
        refine ih (Z.erase z) u w z b hcard' hzb
          (hu.mono (Set.Icc_subset_Icc haz le_rfl)) ?_ (hw.mono_set hsub2)
        intro t ht htZ
        exact hd t ⟨hz.1.trans ht.1, ht.2⟩
          (fun htZ' => htZ (Finset.mem_erase.mpr ⟨(ne_of_lt ht.1).symm, htZ'⟩))
      have h3 : (∫ t in a..z, w t) + (∫ t in z..b, w t) = ∫ t in a..b, w t :=
        intervalIntegral.integral_add_adjacent_intervals (hw.mono_set hsub1) (hw.mono_set hsub2)
      linarith
    · push_neg at hex
      exact sub_le_integral_clean hab hu (fun t ht => hd t ht (fun htZ => hex t htZ ht)) hw

/-- **FTC-2 with finitely many exceptional points**: `u` continuous on
`[a,b]`, `HasDerivAt u (v t) t` for `t ∈ (a,b) \ Z` with `Z` finite, and `v`
interval integrable, imply `u b - u a = ∫_a^b v`. -/
theorem sub_eq_integral_of_finite_exceptions {u v : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (Z : Finset ℝ) (hu : ContinuousOn u (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ Z → HasDerivAt u (v t) t)
    (hv : IntervalIntegrable v volume a b) :
    u b - u a = ∫ t in a..b, v t :=
  sub_eq_integral_aux Z.card Z u v a b rfl hab hu hd hv

/-- Inequality FTC: continuous `u`, derivative bounded by `w` off a finite
set, `w` interval integrable ⟹ `u b - u a ≤ ∫ w`. -/
theorem sub_le_integral_of_finite_exceptions {u w : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (Z : Finset ℝ) (hu : ContinuousOn u (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ Z → ∃ v ≤ w t, HasDerivAt u v t)
    (hw : IntervalIntegrable w volume a b) :
    u b - u a ≤ ∫ t in a..b, w t :=
  sub_le_integral_aux Z.card Z u w a b rfl hab hu hd hw

/-- Monotonicity with finitely many exceptional points: continuous on `[a,b]`,
derivative `≤ 0` off a finite set ⟹ `u b ≤ u a`. -/
theorem antitone_of_deriv_nonpos_finite_exceptions {u : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (Z : Finset ℝ) (hu : ContinuousOn u (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, t ∉ Z →
      ∃ v ≤ (0 : ℝ), HasDerivAt u v t) :
    u b ≤ u a := by
  have h := sub_le_integral_of_finite_exceptions (w := fun _ => (0 : ℝ)) hab Z hu hd
    (intervalIntegral.intervalIntegrable_const)
  have h0 : (∫ _t in a..b, (0 : ℝ)) = 0 := by simp
  rw [h0] at h
  linarith

/-! ### Finiteness of crossing times -/

/-- Roots of a nonzero polynomial evaluated along `t ↦ e^{-t}` form a finite
set. -/
theorem finite_setOf_poly_exp_eq {p : Polynomial ℝ} (hp : p ≠ 0) :
    {t : ℝ | p.eval (Real.exp (-t)) = 0}.Finite := by
  have hinj : Function.Injective fun t : ℝ => Real.exp (-t) := by
    intro x y hxy
    simpa using hxy
  have hroot : {x : ℝ | p.eval x = 0}.Finite := Polynomial.finite_setOf_isRoot hp
  exact hroot.preimage (fun x _ y _ hxy => hinj hxy)

/-- A finite family of exponential-polynomial level conditions has finitely
many crossing times on `ℝ`, assuming the (necessary) hypothesis `0 < N`: if
each `g j t = ∑_{k<N} c j k · (e^{-t})^k` is a polynomial in `e^{-t}` whose
value `v j` differs from its limit `c j 0 = g j (+∞)`, then
`{t | ∃ j, g j t = v j}` is finite. The `0 < N` hypothesis is necessary
(see the repair note below); this is the canonical form. -/
theorem finite_setOf_expPoly_family_eq_of_pos {J : Type*} [Fintype J] {N : ℕ} (hN : 0 < N)
    (c : J → ℕ → ℝ) (v : J → ℝ) (hv : ∀ j, v j ≠ c j 0) :
    {t : ℝ | ∃ j, ∑ k ∈ Finset.range N, c j k * Real.exp (-t) ^ k = v j}.Finite := by
  have hset : {t : ℝ | ∃ j, ∑ k ∈ Finset.range N, c j k * Real.exp (-t) ^ k = v j}
      = ⋃ j : J, {t : ℝ | ∑ k ∈ Finset.range N, c j k * Real.exp (-t) ^ k = v j} := by
    ext t; simp
  rw [hset]
  refine Set.finite_iUnion (fun j => ?_)
  set p : Polynomial ℝ :=
    (∑ k ∈ Finset.range N, Polynomial.C (c j k) * Polynomial.X ^ k) - Polynomial.C (v j)
    with hpdef
  have hev : ∀ x : ℝ, p.eval x = (∑ k ∈ Finset.range N, c j k * x ^ k) - v j := by
    intro x
    simp [hpdef, Polynomial.eval_finset_sum]
  have hp0 : p ≠ 0 := by
    intro hzero
    have h1 : p.eval 0 = 0 := by rw [hzero]; simp
    rw [hev] at h1
    have h2 : ∑ k ∈ Finset.range N, c j k * (0 : ℝ) ^ k = c j 0 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
      simp [Finset.sum_range_succ', pow_succ]
    rw [h2] at h1
    exact hv j (by linarith)
  refine (finite_setOf_poly_exp_eq hp0).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [hev]
  linarith

-- STATEMENT REPAIR (laptop adjudication of the lane's STATEMENT-ISSUE): the
-- original `finite_setOf_expPoly_family_eq`, stated without `0 < N`, is FALSE
-- at `N = 0` — witness `J := Unit`, `N := 0`, `c := fun _ _ => 1`,
-- `v := fun _ => 0`: the empty sum is `0`, so the set is `Set.univ`, infinite,
-- while `hv` (`0 ≠ 1`) holds. The refuted form has been deleted; every
-- intended use has `N ≥ 1`, so consumers must supply `0 < N` and use
-- `finite_setOf_expPoly_family_eq_of_pos` above.

end Talagrand
