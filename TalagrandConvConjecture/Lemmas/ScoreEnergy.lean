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
