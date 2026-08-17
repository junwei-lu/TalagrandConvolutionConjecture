import TalagrandConvConjecture.Lemmas.ScoreEnergy
import TalagrandConvConjecture.Lemmas.Discrepancy
import TalagrandConvConjecture.Lemmas.BandContraction

/-!
# The fixed-band anti-concentration estimate [LGF Proposition 3.2]

`𝔄_{t_a}((ℓ, ℓ+1]) ≲ K_a/√ℓ` for every `ℓ > 0`.

Proof [LGF §3.1], three steps for `ℓ ≥ C·K_a²`:
1. *Active discrepancy*: decompose `ℰ_θ` into gap layers `E_r(θ)`
   (`r ≤ R_θ < r+1`), bound each `D_{E_r}` via [LGF Lemma 3.3] +
   [LGF Lemma 3.5], average over `θ ∈ [T_o-1, T_o]` using the windowed
   profile bound [C Lemma 4]: `∫ D_{ℰ_θ} dθ ≲ K_a/√ℓ` — realized here as a
   pointwise-in-`θ` bound by an explicit measurable majorant with small
   integral.
2. *Inactive starting points*: `Ā_θ(ℓ) = ℙ(ℰ_θᶜ, F_{T_o}(V_{T_o}) ∈ band)`;
   near layers via the profile bound, far layers via the `e^{-F}`-martingale
   Chebyshev estimate `ℙ(F_{T_o}(V_{T_o}) ≤ ℓ+1 | V_θ = x₀) ≤ e^{ℓ+1-F_θ(x₀)}`.
3. *Closing the recurrence*: combine with [LGF Lemma 3.4]; pick a good `θ` by
   the mean-value principle; run the geometric-band bootstrap
   (`ϱ* = c₀/((1-c₀)(e-1)) < 1`) on `𝓜_ℓ = sup_{r≥ℓ} √r·𝔄_{t_a}((r,r+1])`.
For `ℓ < C·K_a²` the trivial bound `𝔄 ≤ 1 ≤ K_a√C/√ℓ` applies.
-/

namespace Talagrand

/-! ### Elementary sum and analytic bounds used in the proof of [LGF Prop 3.2] -/

/-- `∑_{j<m} (j+1)^{-1/2} ≤ 2√m`. -/
private lemma sum_inv_sqrt_le (m : ℕ) :
    ∑ j ∈ Finset.range m, (Real.sqrt ((j : ℝ) + 1))⁻¹ ≤ 2 * Real.sqrt m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk1 : (0 : ℝ) < Real.sqrt ((k : ℝ) + 1) :=
      Real.sqrt_pos.mpr (by positivity)
    have hsq : Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) = (k : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hmul : Real.sqrt (k : ℝ) * Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 / 2 := by
      rw [← Real.sqrt_mul (by positivity)]
      calc Real.sqrt ((k : ℝ) * ((k : ℝ) + 1))
          ≤ Real.sqrt (((k : ℝ) + 1 / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = (k : ℝ) + 1 / 2 := Real.sqrt_sq (by positivity)
    have h2 : 1 ≤ (2 * Real.sqrt ((k : ℝ) + 1) - 2 * Real.sqrt (k : ℝ))
        * Real.sqrt ((k : ℝ) + 1) := by nlinarith
    have key : (Real.sqrt ((k : ℝ) + 1))⁻¹
        ≤ 2 * Real.sqrt ((k : ℝ) + 1) - 2 * Real.sqrt (k : ℝ) := by
      calc (Real.sqrt ((k : ℝ) + 1))⁻¹
          = 1 * (Real.sqrt ((k : ℝ) + 1))⁻¹ := (one_mul _).symm
        _ ≤ ((2 * Real.sqrt ((k : ℝ) + 1) - 2 * Real.sqrt (k : ℝ))
              * Real.sqrt ((k : ℝ) + 1)) * (Real.sqrt ((k : ℝ) + 1))⁻¹ :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = 2 * Real.sqrt ((k : ℝ) + 1) - 2 * Real.sqrt (k : ℝ) := by
            field_simp
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith

/-- Harmonic-sum bound, real form. -/
private lemma sum_inv_le_one_add_log (m : ℕ) :
    ∑ j ∈ Finset.range m, ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log m := by
  have h := harmonic_le_one_add_log m
  rw [harmonic] at h
  push_cast at h
  exact h

private lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith

private lemma log_le_four_mul_sqrt_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have h1 := log_le_two_mul_sqrt (Real.sqrt_pos.mpr hx)
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith

/-- `κ_a·Λ_a ≤ K_a` (from `K² = κ³Λ` and `Λ ≤ κ`). -/
private lemma kappa_mul_Lam_le {κ Λ K : ℝ} (hκ : 1 < κ) (hΛ1 : 1 ≤ Λ)
    (hΛκ : Λ ≤ κ) (hK : K ^ 2 = κ ^ 3 * Λ) (hK0 : 0 ≤ K) : κ * Λ ≤ K := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have h1 : (κ * Λ) ^ 2 ≤ K ^ 2 := by
    rw [hK]
    nlinarith [mul_nonneg (mul_nonneg (mul_pos hκ0 hκ0).le hΛ0.le)
      (sub_nonneg.mpr hΛκ)]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hK0] at h2

/-- The absorption inequality of [LGF eq (3.12)]:
`κ²Λ·(1 + log ℓ) ≤ 5·K·√ℓ` whenever `ℓ ≥ K²` and `ℓ ≥ 1`. -/
private lemma kappa_sq_Lam_log_le {κ Λ K ℓ : ℝ} (hκ : 1 < κ) (hΛ1 : 1 ≤ Λ)
    (hΛκ : Λ ≤ κ) (hK : K ^ 2 = κ ^ 3 * Λ) (hK1 : 1 ≤ K) (hℓ : K ^ 2 ≤ ℓ)
    (hℓ1 : 1 ≤ ℓ) : κ ^ 2 * Λ * (1 + Real.log ℓ) ≤ 5 * K * Real.sqrt ℓ := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hkl : κ * Λ ≤ K := kappa_mul_Lam_le hκ hΛ1 hΛκ hK hK0
  -- `(κ²Λ)² ≤ K³`
  have hcube : (κ ^ 2 * Λ) ^ 2 ≤ K ^ 3 := by
    have h1 : (κ ^ 2 * Λ) ^ 2 = (κ * Λ) * (κ ^ 3 * Λ) := by ring
    have h2 : K ^ 3 = K * (κ ^ 3 * Λ) := by rw [← hK]; ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right hkl (by positivity)
  have hsqrtK : Real.sqrt (K ^ 3) = K * Real.sqrt K := by
    rw [show K ^ 3 = K ^ 2 * K by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hK0]
  have hmain : κ ^ 2 * Λ ≤ K * Real.sqrt K := by
    rw [← hsqrtK]
    calc κ ^ 2 * Λ = Real.sqrt ((κ ^ 2 * Λ) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (K ^ 3) := Real.sqrt_le_sqrt hcube
  -- `1 + log ℓ ≤ 5·ℓ^{1/4}`
  have hq1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt ℓ) := by
    have : (1 : ℝ) ≤ Real.sqrt ℓ := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hℓ1
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by simpa using this)
  have hlog : 1 + Real.log ℓ ≤ 5 * Real.sqrt (Real.sqrt ℓ) := by
    have := log_le_four_mul_sqrt_sqrt hℓ0
    linarith
  -- `√K ≤ ℓ^{1/4}`
  have hKle : K ≤ Real.sqrt ℓ := by
    rw [show K = Real.sqrt (K ^ 2) from (Real.sqrt_sq hK0).symm]
    exact Real.sqrt_le_sqrt hℓ
  have hsK : Real.sqrt K ≤ Real.sqrt (Real.sqrt ℓ) := Real.sqrt_le_sqrt hKle
  have hqq : Real.sqrt (Real.sqrt ℓ) * Real.sqrt (Real.sqrt ℓ) = Real.sqrt ℓ :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hsK0 : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hlog0 : (0 : ℝ) ≤ Real.log ℓ := Real.log_nonneg hℓ1
  calc κ ^ 2 * Λ * (1 + Real.log ℓ)
      ≤ (K * Real.sqrt K) * (5 * Real.sqrt (Real.sqrt ℓ)) := by
        exact mul_le_mul hmain hlog (by linarith) (by positivity)
    _ ≤ (K * Real.sqrt (Real.sqrt ℓ)) * (5 * Real.sqrt (Real.sqrt ℓ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hsK hK0
    _ = 5 * K * (Real.sqrt (Real.sqrt ℓ) * Real.sqrt (Real.sqrt ℓ)) := by ring
    _ = 5 * K * Real.sqrt ℓ := by rw [hqq]

/-- `√x ≤ y` from `x ≤ y²`. -/
private lemma sqrt_le_of_le_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) :
    Real.sqrt x ≤ y := by
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

/-- Subadditivity of the square root. -/
private lemma sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  refine sqrt_le_of_le_sq (by positivity) ?_
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a,
    Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- `∑_{j<m} (j+1)^{-2} ≤ 2`. -/
private lemma sum_inv_sq_le (m : ℕ) :
    ∑ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have key : ∀ k : ℕ, ∑ j ∈ Finset.range k, (((j : ℝ) + 1) ^ 2)⁻¹
      ≤ 2 - 2 / ((k : ℝ) + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ p ih =>
      rw [Finset.sum_range_succ]
      have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
      have hp2 : (0 : ℝ) < (p : ℝ) + 1 + 1 := by positivity
      have hid : 2 / ((p : ℝ) + 1) - 2 / ((p : ℝ) + 1 + 1)
          - (((p : ℝ) + 1) ^ 2)⁻¹
          = (p : ℝ) / ((((p : ℝ) + 1) ^ 2) * ((p : ℝ) + 1 + 1)) := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ (p : ℝ) / ((((p : ℝ) + 1) ^ 2) * ((p : ℝ) + 1 + 1)) := by
        positivity
      have hcast : ((p + 1 : ℕ) : ℝ) + 1 = (p : ℝ) + 1 + 1 := by push_cast; ring
      rw [hcast]
      linarith
  have h1 : (0 : ℝ) ≤ 2 / ((m : ℝ) + 1) := by positivity
  linarith [key m]

/-- Geometric partial sums of `2⁻¹`. -/
private lemma sum_half_pow_le (Q : ℕ) :
    ∑ q ∈ Finset.range Q, (1 / 2 : ℝ) ^ q ≤ 2 := by
  have key : ∀ k : ℕ, ∑ q ∈ Finset.range k, (1 / 2 : ℝ) ^ q
      ≤ 2 - 2 * (1 / 2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ p ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linarith
  have h1 : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ Q := by positivity
  linarith [key Q]

private lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-1)]

private lemma exp_neg_nat_succ (j : ℕ) :
    Real.exp (-((j : ℝ) + 1)) = Real.exp (-1) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hc : -(((k + 1 : ℕ) : ℝ) + 1) = -((k : ℝ) + 1) + -1 := by push_cast; ring
    rw [hc, Real.exp_add, ih, pow_succ]; ring

private lemma exp_neg_succ_le (j : ℕ) :
    Real.exp (-((j : ℝ) + 1)) ≤ 1 / 2 * (1 / 2 : ℝ) ^ j := by
  have h1 : Real.exp (-1) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le_half _
  calc Real.exp (-((j : ℝ) + 1)) = Real.exp (-1) ^ (j + 1) := exp_neg_nat_succ j
    _ ≤ (1 / 2 : ℝ) ^ (j + 1) := h1
    _ = 1 / 2 * (1 / 2 : ℝ) ^ j := by rw [pow_succ]; ring

private lemma summable_exp_neg_succ :
    Summable (fun j : ℕ => Real.exp (-((j : ℝ) + 1))) := by
  refine Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) exp_neg_succ_le ?_
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- `∑_{j≥0} e^{-(j+1)} ≤ 1` (used with `e^{-1} ≤ ½`). -/
private lemma tsum_exp_neg_succ_le_one :
    ∑' j : ℕ, Real.exp (-((j : ℝ) + 1)) ≤ 1 := by
  have hs : Summable (fun j : ℕ => 1 / 2 * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hgeo : ∑' j : ℕ, (1 / 2 : ℝ) ^ j = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  calc ∑' j : ℕ, Real.exp (-((j : ℝ) + 1))
      ≤ ∑' j : ℕ, 1 / 2 * (1 / 2 : ℝ) ^ j :=
        summable_exp_neg_succ.tsum_le_tsum exp_neg_succ_le hs
    _ = 1 / 2 * ∑' j : ℕ, (1 / 2 : ℝ) ^ j := tsum_mul_left
    _ = 1 := by rw [hgeo]; norm_num

private lemma exp_shift_eq (q : ℕ) :
    Real.exp (11 - (q : ℝ)) = Real.exp 11 * Real.exp (-1) ^ q := by
  induction q with
  | zero => simp
  | succ k ih =>
    have hc : (11 : ℝ) - ((k + 1 : ℕ) : ℝ) = (11 - (k : ℝ)) + -1 := by
      push_cast; ring
    rw [hc, Real.exp_add, ih, pow_succ]; ring

/-- The shifted geometric weights of Step 2: `∑_{q<Q} e^{11-q} ≤ 2e^{11}`. -/
private lemma sum_exp_shift_le (Q : ℕ) :
    ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ)) ≤ 2 * Real.exp 11 := by
  have hpt : ∀ q ∈ Finset.range Q,
      Real.exp (11 - (q : ℝ)) ≤ Real.exp 11 * (1 / 2 : ℝ) ^ q := by
    intro q _
    have h1 : Real.exp (-1) ^ q ≤ (1 / 2 : ℝ) ^ q :=
      pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le_half _
    rw [exp_shift_eq q]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos 11).le
  calc ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ))
      ≤ ∑ q ∈ Finset.range Q, Real.exp 11 * (1 / 2 : ℝ) ^ q :=
        Finset.sum_le_sum hpt
    _ = Real.exp 11 * ∑ q ∈ Finset.range Q, (1 / 2 : ℝ) ^ q := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp 11 * 2 :=
        mul_le_mul_of_nonneg_left (sum_half_pow_le Q) (Real.exp_pos 11).le
    _ = 2 * Real.exp 11 := by ring

/-- `c₀ = e^{1-α} = e^{-4} ≤ 1/16` (from `e > 2`). -/
private lemma exp_one_sub_alphaC_le : Real.exp (1 - alphaC) ≤ 1 / 16 := by
  have hval : (1 : ℝ) - alphaC = -4 := by norm_num [alphaC]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he4 : Real.exp 4 = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    have p2 : (2 : ℝ) * 2 ≤ Real.exp 1 * Real.exp 1 :=
      mul_le_mul h2 h2 (by norm_num) (Real.exp_pos 1).le
    have p3 : (2 : ℝ) * 2 * 2 ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 :=
      mul_le_mul p2 h2 (by norm_num) (by positivity)
    have p4 : (2 : ℝ) * 2 * 2 * 2
        ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 :=
      mul_le_mul p3 h2 (by norm_num) (by positivity)
    rw [he4]; linarith
  have hinv : Real.exp (-4) * Real.exp 4 = 1 := by rw [← Real.exp_add]; norm_num
  rw [hval]
  nlinarith [mul_nonneg (sub_nonneg.mpr h16) (Real.exp_pos (-4 : ℝ)).le, hinv]

/-- The per-layer discrepancy bound of [LGF Step 1 of Prop 3.2], as pure
algebra: combine `D_A ≤ C(κΛ√(𝒮·ℙ) + κΛ²𝒮)` [LGF Lemma 3.3] with
`𝒮 ≤ 25(κ/(Λu) + (κ-1)/u²)·ℙ` [LGF Lemma 3.5] and `K² = κ³Λ`, where
`u = R+1 ≥ 1` is the (frozen) gap of the layer. -/
private lemma DA_layer_bound {κ Λ K CD DAv SAv p u : ℝ}
    (hκ : 1 < κ) (hΛ1 : 1 ≤ Λ) (hΛκ : Λ ≤ κ) (hK : K ^ 2 = κ ^ 3 * Λ)
    (hK0 : 0 ≤ K) (hCD : 0 ≤ CD) (hu : 1 ≤ u) (hp : 0 ≤ p)
    (hSA : SAv ≤ 25 * (κ / (Λ * u) + (κ - 1) / u ^ 2) * p)
    (hDA : DAv ≤ CD * (κ * Λ * Real.sqrt (SAv * p) + κ * Λ ^ 2 * SAv)) :
    DAv ≤ CD * (5 * K / Real.sqrt u + 30 * κ ^ 2 * Λ / u
      + 25 * K ^ 2 / u ^ 2) * p := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
  set S : ℝ := 25 * (κ / (Λ * u) + (κ - 1) / u ^ 2) with hS
  have hA0 : (0 : ℝ) ≤ κ / (Λ * u) := by positivity
  have hB0 : (0 : ℝ) ≤ (κ - 1) / u ^ 2 :=
    div_nonneg (by linarith) (by positivity)
  have hS0 : (0 : ℝ) ≤ S := by rw [hS]; linarith
  -- (i) `√(𝒮ℙ) ≤ √S·ℙ`
  have hsq : Real.sqrt (SAv * p) ≤ Real.sqrt S * p := by
    have h1 : SAv * p ≤ S * p ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hSA hp]
    calc Real.sqrt (SAv * p) ≤ Real.sqrt (S * p ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt S * p := by rw [Real.sqrt_mul hS0, Real.sqrt_sq hp]
  -- (ii) split the square root of the two-term majorant
  have hsplit : Real.sqrt S
      ≤ 5 * (Real.sqrt (κ / (Λ * u)) + Real.sqrt (κ - 1) / u) := by
    have h25 : Real.sqrt S
        = 5 * Real.sqrt (κ / (Λ * u) + (κ - 1) / u ^ 2) := by
      rw [hS, show (25 : ℝ) * (κ / (Λ * u) + (κ - 1) / u ^ 2)
        = 5 ^ 2 * (κ / (Λ * u) + (κ - 1) / u ^ 2) by norm_num,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hab : Real.sqrt (κ / (Λ * u) + (κ - 1) / u ^ 2)
        ≤ Real.sqrt (κ / (Λ * u)) + Real.sqrt ((κ - 1) / u ^ 2) :=
      sqrt_add_le hA0 hB0
    have hB : Real.sqrt ((κ - 1) / u ^ 2) = Real.sqrt (κ - 1) / u := by
      rw [Real.sqrt_div (by linarith : (0 : ℝ) ≤ κ - 1), Real.sqrt_sq hu0.le]
    rw [h25, ← hB]
    linarith
  -- (iii) the leading term is exactly `K/√u`
  have hKu : κ * Λ * Real.sqrt (κ / (Λ * u)) = K / Real.sqrt u := by
    have e2 : (κ * Λ) ^ 2 * (κ / (Λ * u)) = K ^ 2 / u := by
      rw [hK]; field_simp
    calc κ * Λ * Real.sqrt (κ / (Λ * u))
        = Real.sqrt ((κ * Λ) ^ 2) * Real.sqrt (κ / (Λ * u)) := by
          rw [Real.sqrt_sq (by positivity)]
      _ = Real.sqrt ((κ * Λ) ^ 2 * (κ / (Λ * u))) :=
          (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt (K ^ 2 / u) := by rw [e2]
      _ = K / Real.sqrt u := by
          rw [Real.sqrt_div (by positivity), Real.sqrt_sq hK0]
  -- (iv) the sub-leading square root is absorbed into `κ²Λ`
  have hsk : Real.sqrt (κ - 1) ≤ κ := sqrt_le_of_le_sq hκ0.le (by nlinarith)
  have h4 : κ * Λ * (Real.sqrt (κ - 1) / u) ≤ κ ^ 2 * Λ / u := by
    have hid : κ ^ 2 * Λ / u - κ * Λ * (Real.sqrt (κ - 1) / u)
        = κ * Λ * (κ - Real.sqrt (κ - 1)) / u := by field_simp
    have hnn : (0 : ℝ) ≤ κ * Λ * (κ - Real.sqrt (κ - 1)) / u :=
      div_nonneg (mul_nonneg (mul_nonneg hκ0.le hΛ0.le) (by linarith)) hu0.le
    linarith
  have hkey : κ * Λ * Real.sqrt S
      ≤ 5 * (K / Real.sqrt u) + 5 * (κ ^ 2 * Λ / u) := by
    have h := mul_le_mul_of_nonneg_left hsplit (by positivity : (0 : ℝ) ≤ κ * Λ)
    have e : κ * Λ * (5 * (Real.sqrt (κ / (Λ * u)) + Real.sqrt (κ - 1) / u))
        = 5 * (κ * Λ * Real.sqrt (κ / (Λ * u)))
          + 5 * (κ * Λ * (Real.sqrt (κ - 1) / u)) := by ring
    rw [e, hKu] at h
    linarith
  -- (v) the second (energy) term
  have hSecond : κ * Λ ^ 2 * S ≤ 25 * κ ^ 2 * Λ / u + 25 * K ^ 2 / u ^ 2 := by
    have hb : κ * Λ ^ 2 * (κ - 1) ≤ K ^ 2 := by
      rw [hK]
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hκ0.le hκ0.le) hΛ0.le)
        (sub_nonneg.mpr hΛκ), mul_pos hκ0 (mul_pos hΛ0 hΛ0)]
    have hid : (25 * κ ^ 2 * Λ / u + 25 * K ^ 2 / u ^ 2) - κ * Λ ^ 2 * S
        = 25 * (K ^ 2 - κ * Λ ^ 2 * (κ - 1)) / u ^ 2 := by
      rw [hS]; field_simp; ring
    have hnn : (0 : ℝ) ≤ 25 * (K ^ 2 - κ * Λ ^ 2 * (κ - 1)) / u ^ 2 :=
      div_nonneg (by linarith) (by positivity)
    linarith
  -- assemble
  have a1 : κ * Λ * Real.sqrt (SAv * p)
      ≤ (5 * (K / Real.sqrt u) + 5 * (κ ^ 2 * Λ / u)) * p := by
    calc κ * Λ * Real.sqrt (SAv * p) ≤ κ * Λ * (Real.sqrt S * p) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (κ * Λ * Real.sqrt S) * p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hkey hp
  have a2 : κ * Λ ^ 2 * SAv
      ≤ (25 * κ ^ 2 * Λ / u + 25 * K ^ 2 / u ^ 2) * p := by
    calc κ * Λ ^ 2 * SAv ≤ κ * Λ ^ 2 * (S * p) :=
          mul_le_mul_of_nonneg_left hSA (by positivity)
      _ = (κ * Λ ^ 2 * S) * p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hSecond hp
  calc DAv ≤ CD * (κ * Λ * Real.sqrt (SAv * p) + κ * Λ ^ 2 * SAv) := hDA
    _ ≤ CD * ((5 * (K / Real.sqrt u) + 5 * (κ ^ 2 * Λ / u)) * p
          + (25 * κ ^ 2 * Λ / u + 25 * K ^ 2 / u ^ 2) * p) :=
        mul_le_mul_of_nonneg_left (by linarith) hCD
    _ = CD * (5 * K / Real.sqrt u + 30 * κ ^ 2 * Λ / u
          + 25 * K ^ 2 / u ^ 2) * p := by ring

/-- The layer sum of [LGF eq (3.11)]. -/
private lemma sum_layer_coeff_le {κ Λ K : ℝ} (hK0 : 0 ≤ K)
    (hκΛ : 0 ≤ κ ^ 2 * Λ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (5 * K / Real.sqrt ((i : ℝ) + 1)
        + 30 * κ ^ 2 * Λ / ((i : ℝ) + 1) + 25 * K ^ 2 / ((i : ℝ) + 1) ^ 2)
      ≤ 10 * K * Real.sqrt m + 30 * κ ^ 2 * Λ * (1 + Real.log m)
        + 50 * K ^ 2 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : ∑ i ∈ Finset.range m, 5 * K / Real.sqrt ((i : ℝ) + 1)
      = 5 * K * ∑ i ∈ Finset.range m, (Real.sqrt ((i : ℝ) + 1))⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
  have e2 : ∑ i ∈ Finset.range m, 30 * κ ^ 2 * Λ / ((i : ℝ) + 1)
      = 30 * κ ^ 2 * Λ * ∑ i ∈ Finset.range m, ((i : ℝ) + 1)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
  have e3 : ∑ i ∈ Finset.range m, 25 * K ^ 2 / ((i : ℝ) + 1) ^ 2
      = 25 * K ^ 2 * ∑ i ∈ Finset.range m, (((i : ℝ) + 1) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
  rw [e1, e2, e3]
  have b1 : 5 * K * ∑ i ∈ Finset.range m, (Real.sqrt ((i : ℝ) + 1))⁻¹
      ≤ 5 * K * (2 * Real.sqrt m) :=
    mul_le_mul_of_nonneg_left (sum_inv_sqrt_le m) (by linarith)
  have b2 : 30 * κ ^ 2 * Λ * ∑ i ∈ Finset.range m, ((i : ℝ) + 1)⁻¹
      ≤ 30 * κ ^ 2 * Λ * (1 + Real.log m) :=
    mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log m) (by linarith)
  have b3 : 25 * K ^ 2 * ∑ i ∈ Finset.range m, (((i : ℝ) + 1) ^ 2)⁻¹
      ≤ 25 * K ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left (sum_inv_sq_le m) (by positivity)
  linarith

/-- The unit bands `(c+q, c+q+1]`, `q < Q`, cover `(c, c+Q]`. -/
private lemma exists_band_index {c v : ℝ} {Q : ℕ} (h1 : c < v) (h2 : v ≤ c + Q) :
    ∃ q ∈ Finset.range Q, v ∈ Set.Ioc (c + (q : ℝ)) (c + (q : ℝ) + 1) := by
  have hd0 : (0 : ℝ) < v - c := by linarith
  have hcQ : v - c ≤ (Q : ℝ) := by linarith
  have hc1 : 1 ≤ ⌈v - c⌉₊ := Nat.ceil_pos.mpr hd0
  have hcQ' : ⌈v - c⌉₊ ≤ Q := Nat.ceil_le.mpr hcQ
  refine ⟨⌈v - c⌉₊ - 1, Finset.mem_range.mpr (by omega), ?_⟩
  have hcast : ((⌈v - c⌉₊ - 1 : ℕ) : ℝ) = (⌈v - c⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hc1]; norm_num
  refine ⟨?_, ?_⟩
  · have h := Nat.ceil_lt_add_one hd0.le
    rw [hcast]; linarith
  · have h := Nat.le_ceil (v - c)
    rw [hcast]; linarith

/-- `Icc a (b+1) = insert (b+1) (Icc a b)` for `a ≤ b+1`. -/
private lemma Icc_eq_insert (a b : ℕ) (hab : a ≤ b + 1) :
    Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
  ext i
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- Interval integrability is preserved by finite sums. -/
private lemma intervalIntegrable_finsum' {ι : Type*} (s : Finset ι)
    (g : ι → ℝ → ℝ) {a b : ℝ}
    (hg : ∀ i, IntervalIntegrable (g i) MeasureTheory.volume a b) :
    IntervalIntegrable (fun t => ∑ i ∈ s, g i t) MeasureTheory.volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have heq : (fun t => ∑ i ∈ insert j s, g i t)
        = fun t => g j t + ∑ i ∈ s, g i t := by
      funext t; rw [Finset.sum_insert hj]
    rw [heq]
    exact (hg j).add ih

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- Coupling-flow families exist for every admissible `(ℓ, θ)`. -/
theorem exists_cflowFamily (ℓ : ℝ) (hℓ : 0 < ℓ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) : Nonempty (D.CFlowFamily ℓ θ) :=
  ⟨fun x₀ => (D.exists_cflow ℓ hℓ hθ0 hθ x₀).some⟩

/-- Terminal sub-law of a coupling flow is nonnegative (the terminal time
`T_o` sits in the last cell of the grid). -/
lemma cflow_term_nonneg {ℓ θ : ℝ} (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (s : JSt n) : 0 ≤ c.term s := by
  have hK : 0 < c.K := c.is.grid.pos
  have hk : c.K - 1 < c.K := Nat.sub_lt hK Nat.one_pos
  have hsucc : c.K - 1 + 1 = c.K := Nat.succ_pred_eq_of_pos hK
  have hmono : c.z (c.K - 1) ≤ c.z (c.K - 1 + 1) := c.is.grid.mono _ hk
  have hlast : c.z (c.K - 1 + 1) = obsT := by rw [hsucc]; exact c.is.grid.last
  have ht : obsT ∈ Set.Icc (c.z (c.K - 1)) (c.z (c.K - 1 + 1)) :=
    ⟨by rw [← hlast]; exact hmono, hlast.ge⟩
  exact D.cflow_nonneg hθ c hk ht s

/-- **Reciprocal-martingale tail bound** [LGF, Step 2 of Prop 3.2]: for any
coupling flow from `x₀`,
`𝔼_{x₀}[1_{F_{T_o}(V_{T_o}) ≤ c}] ≤ e^{c - F_θ(x₀)}` for every `c`. -/
theorem term_V_tail_le {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (cLev : ℝ) :
    ∑ s : JSt n, c.term s * (if D.F obsT s.1 ≤ cLev then (1 : ℝ) else 0)
      ≤ Real.exp (cLev - D.F θ x₀) := by
  classical
  have hsub : Set.Icc θ obsT ⊆ Set.Iic D.T := fun t ht =>
    le_trans ht.2 (le_of_lt D.obsT_lt_T)
  have hmarg : ∑ s : JSt n, c.term s * Real.exp (-(D.F obsT s.1))
      = Real.exp (-(D.F θ x₀)) := by
    refine D.cflow_V_marginal hθ0 hθ c (fun t x => Real.exp (-(D.F t x)))
      (fun x => (((D.continuousOn_F x).mono hsub).neg).rexp) ?_
    intro x t ht
    exact (D.hasDerivAt_exp_neg_F (hsub ht) x).hasDerivWithinAt
  have hterm : ∀ s : JSt n, 0 ≤ c.term s := fun s => D.cflow_term_nonneg hθ c s
  have hle : ∀ s : JSt n, c.term s * (if D.F obsT s.1 ≤ cLev then (1 : ℝ) else 0)
      ≤ Real.exp cLev * (c.term s * Real.exp (-(D.F obsT s.1))) := by
    intro s
    by_cases h : D.F obsT s.1 ≤ cLev
    · rw [if_pos h, mul_one]
      have h1 : (1 : ℝ) ≤ Real.exp cLev * Real.exp (-(D.F obsT s.1)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      calc c.term s = c.term s * 1 := (mul_one _).symm
        _ ≤ c.term s * (Real.exp cLev * Real.exp (-(D.F obsT s.1))) :=
            mul_le_mul_of_nonneg_left h1 (hterm s)
        _ = Real.exp cLev * (c.term s * Real.exp (-(D.F obsT s.1))) := by ring
    · rw [if_neg h, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (hterm s) (Real.exp_pos _).le)
  calc ∑ s : JSt n, c.term s * (if D.F obsT s.1 ≤ cLev then (1 : ℝ) else 0)
      ≤ ∑ s : JSt n, Real.exp cLev * (c.term s * Real.exp (-(D.F obsT s.1))) :=
        Finset.sum_le_sum fun s _ => hle s
    _ = Real.exp cLev * ∑ s : JSt n, c.term s * Real.exp (-(D.F obsT s.1)) := by
        rw [← Finset.mul_sum]
    _ = Real.exp cLev * Real.exp (-(D.F θ x₀)) := by rw [hmarg]
    _ = Real.exp (cLev - D.F θ x₀) := by
        rw [← Real.exp_add, ← sub_eq_add_neg]

/-! ### The backward (terminal-value) extension of a test function

`revFwdMat` is the transpose of the matrix of `revGen`; the terminal-value
problem `∂_t g = -revGen g`, `g_{T_o} = φ` is therefore solved by reversing
time in `exists_linFlow`, and the pairing `⟨ν_{T-t}, g_t⟩` is constant. -/

/-- Summing `revFwdMat` against its *first* index reproduces the reverse
generator: `∑_x revFwdMat_t(x,y)·g(x) = (L̃_t g)(y)`. -/
lemma sum_revFwdMat_mul (t : ℝ) (g : Cube n → ℝ) (y : Cube n) :
    ∑ x : Cube n, D.revFwdMat t x y * g x = D.revGen t g y := by
  classical
  have e1 : ∀ x : Cube n, D.revFwdMat t x y * g x
      = (∑ i, if x = flipCoord i y then D.Y t i y / 2 * g x else 0)
        - (if x = y then (∑ i, D.Y t i x / 2) * g x else 0) := by
    intro x
    rw [revFwdMat, sub_mul, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by
        by_cases h : x = flipCoord i y <;> simp [h]
    · by_cases h : x = y <;> simp [h]
  rw [Finset.sum_congr rfl fun x _ => e1 x, Finset.sum_sub_distrib,
    Finset.sum_comm]
  have e2 : ∀ i : Fin n,
      (∑ x : Cube n, if x = flipCoord i y then D.Y t i y / 2 * g x else 0)
        = D.Y t i y / 2 * g (flipCoord i y) := fun i => by simp
  have e3 : (∑ x : Cube n, if x = y then (∑ i, D.Y t i x / 2) * g x else 0)
      = (∑ i, D.Y t i y / 2) * g y := by simp
  rw [Finset.sum_congr rfl fun i _ => e2 i, e3, revGen, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Continuity in `t` of the forward matrix entries on `(-∞, T]`. -/
lemma continuousOn_revFwdMat (x x' : Cube n) :
    ContinuousOn (fun t => D.revFwdMat t x x') (Set.Iic D.T) := by
  classical
  simp only [revFwdMat]
  refine ContinuousOn.sub (continuousOn_finset_sum _ fun i _ => ?_) ?_
  · by_cases h : x = flipCoord i x'
    · simp only [if_pos h]
      exact (D.continuousOn_Y i x').div_const 2
    · simp only [if_neg h]; exact continuousOn_const
  · by_cases h : x = x'
    · simp only [if_pos h]
      exact continuousOn_finset_sum _ fun i _ => (D.continuousOn_Y i x).div_const 2
    · simp only [if_neg h]; exact continuousOn_const

/-- Backward (terminal-value) extension: for every `φ` there is `g` on
`[θ, T_o]` with `∂_t g_t = -L̃_t g_t` and `g_{T_o} = φ`. -/
lemma exists_backFlow {θ : ℝ} (hθ : θ ≤ obsT) (φ : Cube n → ℝ) :
    ∃ g : ℝ → Cube n → ℝ,
      (∀ x, ContinuousOn (fun t => g t x) (Set.Icc θ obsT)) ∧
      (∀ x, ∀ t ∈ Set.Icc θ obsT,
        HasDerivWithinAt (fun t => g t x) (-(D.revGen t (g t) x))
          (Set.Icc θ obsT) t) ∧
      g obsT = φ := by
  classical
  have hmaps : Set.MapsTo (fun t => θ + obsT - t) (Set.Icc θ obsT)
      (Set.Icc θ obsT) := fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hmapsT : Set.MapsTo (fun t => θ + obsT - t) (Set.Icc θ obsT)
      (Set.Iic D.T) := fun t ht => by
    have := (hmaps ht).2
    have h2 : obsT ≤ D.T := D.obsT_lt_T.le
    exact le_trans this h2
  have hcontσ : ContinuousOn (fun t : ℝ => θ + obsT - t) (Set.Icc θ obsT) := by
    fun_prop
  set A : ℝ → Cube n → Cube n → ℝ :=
    fun t x x' => D.revFwdMat (θ + obsT - t) x' x with hA
  have hAc : ∀ x x', ContinuousOn (fun t => A t x x') (Set.Icc θ obsT) :=
    fun x x' => (D.continuousOn_revFwdMat x' x).comp hcontσ hmapsT
  obtain ⟨w, hw, hw0⟩ := exists_linFlow A hθ hAc φ
  refine ⟨fun t => w (θ + obsT - t), fun x => (hw.cont x).comp hcontσ hmaps,
    ?_, ?_⟩
  · intro x t ht
    have hσ : HasDerivWithinAt (fun t : ℝ => θ + obsT - t) (-1)
        (Set.Icc θ obsT) t := by
      simpa using
        (((hasDerivAt_const t (θ + obsT)).sub (hasDerivAt_id t)).hasDerivWithinAt
          (s := Set.Icc θ obsT))
    have hd := hw.deriv x (θ + obsT - t) (hmaps ht)
    have key : HasDerivWithinAt (fun t => w (θ + obsT - t) x)
        (matVec (A (θ + obsT - t)) (w (θ + obsT - t)) x * (-1))
        (Set.Icc θ obsT) t := hd.comp t hσ hmaps
    have harg : θ + obsT - (θ + obsT - t) = t := by ring
    have hval : matVec (A (θ + obsT - t)) (w (θ + obsT - t)) x
        = D.revGen t (w (θ + obsT - t)) x := by
      simp only [hA, matVec, harg]
      exact D.sum_revFwdMat_mul t (w (θ + obsT - t)) x
    rw [hval, mul_neg_one] at key
    exact key
  · funext x
    show w (θ + obsT - obsT) x = φ x
    rw [show θ + obsT - obsT = θ from by ring]
    exact congrFun hw0 x

open Classical in
/-- The `V`-terminal band mass over all starting points is the profile:
`∑_{x₀} ν_{T-θ}(x₀)·𝔼_{x₀}[1_{F_{T_o}(V) ∈ I}] = 𝔄_{t_a}(I)`
[LGF eq (3.14), `V_{T_o} ∼ ν_{t_a}`]. -/
theorem sum_term_V_eq_profile {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (I : Set ℝ) :
    ∑ x₀ : Cube n, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
        (if D.F obsT s.1 ∈ I then (1 : ℝ) else 0)
      = profile D.f D.tA I := by
  classical
  obtain ⟨g, hgc, hgd, hgT⟩ :=
    D.exists_backFlow hθ (fun x => if D.F obsT x ∈ I then (1 : ℝ) else 0)
  have hgTx : ∀ x : Cube n,
      g obsT x = if D.F obsT x ∈ I then (1 : ℝ) else 0 := fun x => congrFun hgT x
  -- the reverse law is a flow for `revFwdMat`
  have hTle : ∀ t ∈ Set.Icc θ obsT, t ≤ D.T := fun t ht =>
    le_trans ht.2 D.obsT_lt_T.le
  have hν : IsLinFlow D.revFwdMat θ obsT (fun t => D.revDensity t) := by
    refine ⟨fun x t ht => ?_, fun x t ht => ?_⟩
    · exact ((D.hasDerivAt_revDensity (hTle t ht) x).continuousAt).continuousWithinAt
    · exact (D.hasDerivAt_revDensity (hTle t ht) x).hasDerivWithinAt
  -- the pairing has vanishing derivative
  have hpair : ∀ t ∈ Set.Icc θ obsT,
      HasDerivWithinAt (fun t => ∑ x : Cube n, D.revDensity t x * g t x) 0
        (Set.Icc θ obsT) t := by
    intro t ht
    have h := hasDerivWithinAt_pairing hν ht (g := g)
      (g' := fun x => -(D.revGen t (g t) x)) (fun x => hgd x t ht)
    have e1 : ∑ x : Cube n, matVec (D.revFwdMat t) (D.revDensity t) x * g t x
        = ∑ x : Cube n, D.revDensity t x * D.revGen t (g t) x := by
      simp only [matVec, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [← D.sum_revFwdMat_mul t (g t) x', Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    have e2 : ∑ x : Cube n, D.revDensity t x * (-(D.revGen t (g t) x))
        = -∑ x : Cube n, D.revDensity t x * D.revGen t (g t) x := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hzero : ∑ x : Cube n, (matVec (D.revFwdMat t) (D.revDensity t) x * g t x
        + D.revDensity t x * (-(D.revGen t (g t) x))) = 0 := by
      rw [Finset.sum_add_distrib, e1, e2, add_neg_cancel]
    rwa [hzero] at h
  -- hence it is constant
  have hconst : ∑ x : Cube n, D.revDensity obsT x * g obsT x
      = ∑ x : Cube n, D.revDensity θ x * g θ x := by
    rcases eq_or_lt_of_le hθ with heq | hlt
    · rw [heq]
    · refine constant_of_derivWithin_zero
        (fun t ht => (hpair t ht).differentiableWithinAt)
        (fun t ht => (hpair t ⟨ht.1, ht.2.le⟩).derivWithin
          (uniqueDiffOn_Icc hlt t ⟨ht.1, ht.2.le⟩))
        obsT (Set.right_mem_Icc.2 hθ)
  -- the left-hand side is the pairing at time `θ`
  have hmarg : ∀ x₀ : Cube n,
      ∑ s : JSt n, (Φ x₀).term s * (if D.F obsT s.1 ∈ I then (1 : ℝ) else 0)
        = g θ x₀ := by
    intro x₀
    have h := D.cflow_V_marginal hθ0 hθ (Φ x₀) g hgc hgd
    simpa only [hgTx] using h
  have hL : ∑ x₀ : Cube n, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
        (if D.F obsT s.1 ∈ I then (1 : ℝ) else 0)
      = ∑ x₀ : Cube n, D.revDensity θ x₀ * g θ x₀ :=
    Finset.sum_congr rfl fun x₀ _ => by rw [hmarg x₀]; rfl
  -- and the pairing at time `T_o` is the profile
  have hTsub : D.T - obsT = D.tA := by
    show D.tA + obsT - obsT = D.tA
    ring
  have hterm : ∀ x : Cube n, D.revDensity obsT x * g obsT x
      = I.indicator (fun _ => heatAt D.f D.tA x)
          (Real.log (heatAt D.f D.tA x)) / 2 ^ n := by
    intro x
    have hF : D.F obsT x = Real.log (heatAt D.f D.tA x) := by
      show Real.log (D.fs (D.T - obsT) x) = _
      rw [hTsub]; rfl
    have hd : D.revDensity obsT x = heatAt D.f D.tA x / 2 ^ n := by
      show D.fs (D.T - obsT) x / 2 ^ n = _
      rw [hTsub]; rfl
    rw [hgTx, hF, hd]
    by_cases h : Real.log (heatAt D.f D.tA x) ∈ I
    · rw [if_pos h, Set.indicator_of_mem h]; ring
    · rw [if_neg h, Set.indicator_of_notMem h]; ring
  have hR : ∑ x : Cube n, D.revDensity obsT x * g obsT x = profile D.f D.tA I := by
    rw [profile, unifE, Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => hterm x
  rw [hL, ← hconst, hR]

/-- Vanishing of high bands: `𝔄_{t_a}((r,r+1]) = 0` once `r` exceeds
`max_x log f_{t_a}(x)`. -/
theorem exists_profile_vanish :
    ∃ B : ℝ, ∀ r : ℝ, B ≤ r → profile D.f D.tA (Set.Ioc r (r + 1)) = 0 := by
  classical
  refine ⟨1 + ∑ x : Cube n, |Real.log (heatAt D.f D.tA x)|, fun r hr => ?_⟩
  have hnot : ∀ x : Cube n,
      Real.log (heatAt D.f D.tA x) ∉ Set.Ioc r (r + 1) := by
    intro x hx
    have h1 : |Real.log (heatAt D.f D.tA x)|
        ≤ ∑ y : Cube n, |Real.log (heatAt D.f D.tA y)| :=
      Finset.single_le_sum (f := fun y : Cube n => |Real.log (heatAt D.f D.tA y)|)
        (fun y _ => abs_nonneg _) (Finset.mem_univ x)
    have h2 := le_abs_self (Real.log (heatAt D.f D.tA x))
    have h3 := hx.1
    linarith
  have hz : (fun x : Cube n => (Set.Ioc r (r + 1)).indicator
      (fun _ => heatAt D.f D.tA x) (Real.log (heatAt D.f D.tA x)))
      = fun _ : Cube n => (0 : ℝ) := by
    funext x
    exact Set.indicator_of_notMem (hnot x) _
  simp only [profile, hz]
  exact unifE_const 0

/-! ### Layer bookkeeping and the two steps of [LGF Prop 3.2] -/

private lemma startW_nn {θ : ℝ} (hθ : θ ≤ obsT) (x₀ : Cube n) :
    0 ≤ D.startW θ x₀ := by
  have hT : (0 : ℝ) ≤ D.T - θ := by have := D.obsT_lt_T; linarith
  simp only [startW, revDensity]
  exact div_nonneg (D.fs_pos hT x₀).le (by positivity)

private lemma probA_nonneg {θ : ℝ} (hθ : θ ≤ obsT) (A : Finset (Cube n)) :
    0 ≤ D.probA θ A :=
  Finset.sum_nonneg fun x₀ _ => D.startW_nn hθ x₀

private lemma probA_le_one {θ : ℝ} (hθ : θ ≤ obsT) (A : Finset (Cube n)) :
    D.probA θ A ≤ 1 := by
  have h1 : D.probA θ A ≤ ∑ x₀ : Cube n, D.startW θ x₀ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      fun x _ _ => D.startW_nn hθ x
  have h2 : ∑ x₀ : Cube n, D.startW θ x₀ = 1 := by
    have h := D.unifE_fs (D.T - θ)
    rw [unifE] at h
    have e : ∀ x₀ : Cube n, D.startW θ x₀ = D.fs (D.T - θ) x₀ / 2 ^ n :=
      fun _ => rfl
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.sum_div]
    exact h
  linarith

private lemma mem_activeF_iff {ℓ θ : ℝ} (x₀ : Cube n) :
    x₀ ∈ D.activeF ℓ θ ↔ 2 * alphaC ≤ D.Rgap ℓ θ x₀ := by
  rw [activeF, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x₀, h⟩⟩

/-- The frozen gap lies in the `c`-th unit cell iff the log-density lies in the
corresponding start-time band (`c > 0` rules out the `max` truncation). -/
private lemma Rgap_cell_iff {ℓ θ c : ℝ} (hc : 0 < c) (x₀ : Cube n) :
    (c ≤ D.Rgap ℓ θ x₀ ∧ D.Rgap ℓ θ x₀ < c + 1)
      ↔ D.F θ x₀ ∈ Set.Ioc (ℓ - c - 1) (ℓ - c - 1 + 1) := by
  simp only [Rgap, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    have hnn : (0 : ℝ) ≤ ℓ - D.F θ x₀ := by
      by_contra hcon
      rw [max_eq_right (not_le.mp hcon).le] at h1
      linarith
    rw [max_eq_left hnn] at h1 h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ ℓ - D.F θ x₀)]
    exact ⟨by linarith, by linarith⟩

/-- On `ℰ_θᶜ` the frozen log-density is above `ℓ - 2α = ℓ - 10`. -/
private lemma F_gt_of_not_active {ℓ θ : ℝ} {x₀ : Cube n}
    (h : x₀ ∉ D.activeF ℓ θ) : ℓ - 10 < D.F θ x₀ := by
  have h' : ¬ (2 * alphaC ≤ D.Rgap ℓ θ x₀) := fun hc =>
    h ((D.mem_activeF_iff x₀).mpr hc)
  have h2 : D.Rgap ℓ θ x₀ < 10 := by
    have := not_le.mp h'
    simp only [alphaC] at this
    linarith
  have h3 : ℓ - D.F θ x₀ ≤ D.Rgap ℓ θ x₀ := by
    simp only [Rgap]; exact le_max_left _ _
  linarith

/-- `F_θ ≤ n·log 2` (the heat semigroup is an averaging operator). -/
private lemma F_le_dim (θ : ℝ) (hθ : θ ≤ obsT) (x₀ : Cube n) :
    D.F θ x₀ ≤ (n : ℝ) * Real.log 2 := by
  have hT : (0 : ℝ) ≤ D.T - θ := by have := D.obsT_lt_T; linarith
  have hpos : 0 < heatAt D.f (D.T - θ) x₀ := heatAt_pos D.hf hT x₀
  have hle : heatAt D.f (D.T - θ) x₀ ≤ 2 ^ n := heatAt_le_pow D.hf D.hm hT x₀
  have hF : D.F θ x₀ = Real.log (heatAt D.f (D.T - θ) x₀) := rfl
  rw [hF]
  calc Real.log (heatAt D.f (D.T - θ) x₀) ≤ Real.log ((2 : ℝ) ^ n) :=
        Real.log_le_log hpos hle
    _ = (n : ℝ) * Real.log 2 := by rw [Real.log_pow]

open Classical in
/-- Indicator form of `sum_startW_eq_profile`. -/
private lemma sum_startW_ind_eq_profile (θ : ℝ) (I : Set ℝ) :
    ∑ x₀ : Cube n, D.startW θ x₀ * (if D.F θ x₀ ∈ I then (1 : ℝ) else 0)
      = profile D.f (D.T - θ) I := by
  rw [← D.sum_startW_eq_profile θ I, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x₀ _ => ?_
  by_cases h : D.F θ x₀ ∈ I
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

open Classical in
/-- The gap layers of Step 1: `E_i = {i ≤ R_θ < i+1}` for `i < m`, together
with the top layer `E_m = {R_θ ≥ m}` [LGF Step 1 of Prop 3.2]. -/
private noncomputable def layerF (ℓ θ : ℝ) (m i : ℕ) : Finset (Cube n) :=
  Finset.univ.filter fun x₀ =>
    if i = m then (m : ℝ) ≤ D.Rgap ℓ θ x₀
    else (i : ℝ) ≤ D.Rgap ℓ θ x₀ ∧ D.Rgap ℓ θ x₀ < (i : ℝ) + 1

private lemma mem_layerF_iff {ℓ θ : ℝ} {m i : ℕ} (x₀ : Cube n) :
    x₀ ∈ D.layerF ℓ θ m i ↔
      (if i = m then (m : ℝ) ≤ D.Rgap ℓ θ x₀
        else (i : ℝ) ≤ D.Rgap ℓ θ x₀ ∧ D.Rgap ℓ θ x₀ < (i : ℝ) + 1) := by
  rw [layerF, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x₀, h⟩⟩

private lemma layerF_Rgap_ge {ℓ θ : ℝ} {m i : ℕ} {x₀ : Cube n}
    (h : x₀ ∈ D.layerF ℓ θ m i) : (i : ℝ) ≤ D.Rgap ℓ θ x₀ := by
  rw [D.mem_layerF_iff] at h
  by_cases hi : i = m
  · rw [if_pos hi] at h; rw [hi]; exact h
  · rw [if_neg hi] at h; exact h.1

private lemma layerF_subset_activeF {ℓ θ : ℝ} {m i : ℕ} (hi : 10 ≤ i) :
    D.layerF ℓ θ m i ⊆ D.activeF ℓ θ := by
  intro x₀ hx
  rw [D.mem_activeF_iff]
  have h1 := D.layerF_Rgap_ge hx
  have h2 : (10 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  simp only [alphaC]
  linarith

private lemma layerF_disjoint {ℓ θ : ℝ} {m : ℕ} :
    ∀ i ∈ Finset.Icc 10 m, ∀ j ∈ Finset.Icc 10 m, i ≠ j →
      Disjoint (D.layerF ℓ θ m i) (D.layerF ℓ θ m j) := by
  intro i hi j hj hij
  rw [Finset.disjoint_left]
  intro x₀ hxi hxj
  rw [Finset.mem_Icc] at hi hj
  rw [D.mem_layerF_iff] at hxi hxj
  by_cases him : i = m
  · by_cases hjm : j = m
    · exact hij (him.trans hjm.symm)
    · rw [if_pos him] at hxi
      rw [if_neg hjm] at hxj
      have hn : j + 1 ≤ m := by omega
      have hc : ((j : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hn
      linarith [hxi, hxj.2]
  · by_cases hjm : j = m
    · rw [if_neg him] at hxi
      rw [if_pos hjm] at hxj
      have hn : i + 1 ≤ m := by omega
      have hc : ((i : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hn
      linarith [hxj, hxi.2]
    · rw [if_neg him] at hxi
      rw [if_neg hjm] at hxj
      rcases Nat.lt_or_ge i j with h | h
      · have hn : i + 1 ≤ j := by omega
        have hc : ((i : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast hn
        linarith [hxi.2, hxj.1]
      · have hn : j + 1 ≤ i := by omega
        have hc : ((j : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast hn
        linarith [hxj.2, hxi.1]

private lemma activeF_eq_biUnion {ℓ θ : ℝ} {m : ℕ} (hm : 10 ≤ m) :
    D.activeF ℓ θ = (Finset.Icc 10 m).biUnion (D.layerF ℓ θ m) := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro x₀ hx
    rw [D.mem_activeF_iff] at hx
    have hR10 : (10 : ℝ) ≤ D.Rgap ℓ θ x₀ := by
      simp only [alphaC] at hx; linarith
    by_cases hbig : (m : ℝ) ≤ D.Rgap ℓ θ x₀
    · refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm, le_rfl⟩, ?_⟩
      rw [D.mem_layerF_iff, if_pos rfl]
      exact hbig
    · have hRnn : (0 : ℝ) ≤ D.Rgap ℓ θ x₀ := D.Rgap_nonneg ℓ θ x₀
      have hfl : ((⌊D.Rgap ℓ θ x₀⌋₊ : ℕ) : ℝ) ≤ D.Rgap ℓ θ x₀ := Nat.floor_le hRnn
      have hfl2 : D.Rgap ℓ θ x₀ < ((⌊D.Rgap ℓ θ x₀⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hi10 : 10 ≤ ⌊D.Rgap ℓ θ x₀⌋₊ :=
        Nat.le_floor (by exact_mod_cast hR10)
      have him : ⌊D.Rgap ℓ θ x₀⌋₊ < m := by
        by_contra hcon
        have hc : (m : ℝ) ≤ ((⌊D.Rgap ℓ θ x₀⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_of_not_lt hcon
        exact hbig (le_trans hc hfl)
      refine Finset.mem_biUnion.mpr
        ⟨⌊D.Rgap ℓ θ x₀⌋₊, Finset.mem_Icc.mpr ⟨hi10, him.le⟩, ?_⟩
      rw [D.mem_layerF_iff, if_neg (Nat.ne_of_lt him)]
      exact ⟨hfl, hfl2⟩
  · intro x₀ hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact D.layerF_subset_activeF (Finset.mem_Icc.mp hi).1 hxi

private lemma probA_layerF_eq {ℓ θ : ℝ} {m i : ℕ} (hi : 10 ≤ i) (him : i ≠ m) :
    D.probA θ (D.layerF ℓ θ m i)
      = profile D.f (D.T - θ)
          (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1)) := by
  have hi0 : (0 : ℝ) < (i : ℝ) := by
    have h : (10 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    linarith
  simp only [probA]
  rw [← D.sum_startW_eq_profile θ
    (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1))]
  refine Finset.sum_congr (Finset.ext fun x₀ => ?_) fun _ _ => rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, D.mem_layerF_iff,
    if_neg him]
  exact D.Rgap_cell_iff hi0 x₀

/-! ### The explicit majorant of Steps 1–2 -/

/-- The per-layer discrepancy coefficient of Step 1 of [LGF Prop 3.2]. -/
private noncomputable def layerCoeff (CD : ℝ) (i : ℕ) : ℝ :=
  CD * (5 * Ka D.a / Real.sqrt ((i : ℝ) + 1)
    + 30 * kappa D.a ^ 2 * Lam D.a / ((i : ℝ) + 1)
    + 25 * Ka D.a ^ 2 / ((i : ℝ) + 1) ^ 2)

private lemma layerCoeff_nonneg {CD : ℝ} (hCD : 0 ≤ CD) (i : ℕ) :
    0 ≤ D.layerCoeff CD i := by
  refine mul_nonneg hCD ?_
  have hK0 : (0 : ℝ) ≤ Ka D.a := le_trans zero_le_one (one_le_Ka D.ha0 D.ha1)
  have hΛ0 : (0 : ℝ) ≤ Lam D.a := le_trans zero_le_one (one_le_Lam D.ha0 D.ha1)
  have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have t1 : (0 : ℝ) ≤ 5 * Ka D.a / Real.sqrt ((i : ℝ) + 1) :=
    div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have t2 : (0 : ℝ) ≤ 30 * kappa D.a ^ 2 * Lam D.a / ((i : ℝ) + 1) :=
    div_nonneg (mul_nonneg (by positivity) hΛ0) h1.le
  have t3 : (0 : ℝ) ≤ 25 * Ka D.a ^ 2 / ((i : ℝ) + 1) ^ 2 :=
    div_nonneg (by positivity) (by positivity)
  linarith

/-- The explicit measurable majorant produced by Steps 1–2 of
[LGF Prop 3.2], as a function of the start-time heat parameter `t = T - θ`:
a finite combination of start-time band profiles plus one constant. -/
private noncomputable def errMaj (CD ℓ : ℝ) (m' Q : ℕ) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.Icc 10 m', D.layerCoeff CD i
      * profile D.f t (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1)))
    + D.layerCoeff CD (m' + 1)
    + ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ))
        * profile D.f t (Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1))

open Classical in
/-- **Step 2 of [LGF Prop 3.2]**: on `ℰ_θᶜ` the frozen log-density exceeds
`ℓ-10`, and the terminal band mass from `x₀` is at most
`e^{ℓ+1-F_θ(x₀)} ≤ e^{11-q}` on the `q`-th start-time layer. -/
private lemma Aband_compl_le {ℓ : ℝ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ) {Q : ℕ}
    (hQ : (n : ℝ) * Real.log 2 ≤ ℓ - 10 + (Q : ℝ)) :
    D.Aband Φ (D.activeF ℓ θ)ᶜ ℓ
      ≤ ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ))
          * profile D.f (D.T - θ)
              (Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1)) := by
  set W : Cube n → ℝ := fun x₀ => ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ))
    * (if D.F θ x₀ ∈ Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1)
        then (1 : ℝ) else 0) with hW
  have hWnn : ∀ x₀, 0 ≤ W x₀ := fun x₀ =>
    Finset.sum_nonneg fun q _ =>
      mul_nonneg (Real.exp_pos _).le (by split_ifs <;> norm_num)
  have hmain : D.Aband Φ (D.activeF ℓ θ)ᶜ ℓ
      ≤ ∑ x₀ ∈ (D.activeF ℓ θ)ᶜ, D.startW θ x₀ * W x₀ := by
    simp only [Aband]
    refine Finset.sum_le_sum fun x₀ hx₀ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (D.startW_nn hθ x₀)
    have hb : ∑ s : JSt n, (Φ x₀).term s
        * (if D.F obsT s.1 ∈ Set.Ioc ℓ (ℓ + 1) then (1 : ℝ) else 0)
        ≤ Real.exp ((ℓ + 1) - D.F θ x₀) := by
      refine le_trans (Finset.sum_le_sum ?_)
        (D.term_V_tail_le hθ0 hθ (Φ x₀) (ℓ + 1))
      intro s _
      refine mul_le_mul_of_nonneg_left ?_ (D.cflow_term_nonneg hθ (Φ x₀) s)
      by_cases h : D.F obsT s.1 ∈ Set.Ioc ℓ (ℓ + 1)
      · rw [if_pos h, if_pos h.2]
      · rw [if_neg h]; split_ifs <;> norm_num
    have hinact : ℓ - 10 < D.F θ x₀ :=
      D.F_gt_of_not_active (Finset.mem_compl.mp hx₀)
    have hup : D.F θ x₀ ≤ ℓ - 10 + (Q : ℝ) := le_trans (D.F_le_dim θ hθ x₀) hQ
    obtain ⟨q, hqQ, hqmem⟩ := exists_band_index hinact hup
    have hexp : Real.exp ((ℓ + 1) - D.F θ x₀) ≤ Real.exp (11 - (q : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      have := hqmem.1
      linarith
    have hsingle : Real.exp (11 - (q : ℝ)) ≤ W x₀ := by
      have hmem := Finset.single_le_sum
        (f := fun q' : ℕ => Real.exp (11 - (q' : ℝ))
          * (if D.F θ x₀ ∈ Set.Ioc (ℓ - 10 + (q' : ℝ)) (ℓ - 10 + (q' : ℝ) + 1)
              then (1 : ℝ) else 0))
        (fun q' _ => mul_nonneg (Real.exp_pos _).le
          (by split_ifs <;> norm_num)) hqQ
      simp only [if_pos hqmem, mul_one] at hmem
      exact hmem
    linarith
  refine le_trans hmain ?_
  have hfull : ∑ x₀ ∈ (D.activeF ℓ θ)ᶜ, D.startW θ x₀ * W x₀
      ≤ ∑ x₀ : Cube n, D.startW θ x₀ * W x₀ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun x _ _ => mul_nonneg (D.startW_nn hθ x) (hWnn x)
  refine le_trans hfull (le_of_eq ?_)
  have e1 : ∀ x₀ : Cube n, D.startW θ x₀ * W x₀
      = ∑ q ∈ Finset.range Q, D.startW θ x₀ * (Real.exp (11 - (q : ℝ))
        * (if D.F θ x₀ ∈ Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1)
            then (1 : ℝ) else 0)) := fun x₀ => by rw [hW, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x₀ _ => e1 x₀, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← D.sum_startW_ind_eq_profile θ
    (Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun x₀ _ => by ring_nf

/-- **Steps 1–2 of [LGF Prop 3.2]** combined: for every start time `θ` in the
averaging window and every choice of coupling flows, the active discrepancy
plus the inactive terminal band mass is bounded by the explicit majorant. -/
private lemma errMaj_ge {CD ℓ : ℝ} (hCD0 : 0 ≤ CD)
    (hCDb : ∀ (θ : ℝ), obsT - 1 ≤ θ → θ ≤ obsT → ∀ (Φ : D.CFlowFamily ℓ θ)
      (A : Finset (Cube n)), A ⊆ D.activeF ℓ θ →
      D.DA Φ A ≤ CD * (kappa D.a * Lam D.a
          * Real.sqrt (D.SA Φ A * D.probA θ A)
        + kappa D.a * Lam D.a ^ 2 * D.SA Φ A))
    (hℓ : 0 < ℓ) {m' Q : ℕ} (hm' : 10 ≤ m' + 1)
    (hQ : (n : ℝ) * Real.log 2 ≤ ℓ - 10 + (Q : ℝ))
    {θ : ℝ} (hθ0 : obsT - 1 ≤ θ) (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ) :
    D.DA Φ (D.activeF ℓ θ) + D.Aband Φ (D.activeF ℓ θ)ᶜ ℓ
      ≤ D.errMaj CD ℓ m' Q (D.T - θ) := by
  have hθ0' : (0 : ℝ) ≤ θ := by simp only [obsT] at hθ0; linarith
  have hκ : 1 < kappa D.a := one_lt_kappa D.ha0 D.ha1
  have hΛ1 : 1 ≤ Lam D.a := one_le_Lam D.ha0 D.ha1
  have hΛκ : Lam D.a ≤ kappa D.a := Lam_le_kappa D.ha0 D.ha1
  have hKsq : Ka D.a ^ 2 = kappa D.a ^ 3 * Lam D.a := Ka_sq_eq D.ha0 D.ha1
  have hK1 : 1 ≤ Ka D.a := one_le_Ka D.ha0 D.ha1
  -- the per-layer discrepancy bound
  have hlayer : ∀ i ∈ Finset.Icc 10 (m' + 1),
      D.DA Φ (D.layerF ℓ θ (m' + 1) i)
        ≤ D.layerCoeff CD i * D.probA θ (D.layerF ℓ θ (m' + 1) i) := by
    intro i hi
    have hi10 : 10 ≤ i := (Finset.mem_Icc.mp hi).1
    have hsub := D.layerF_subset_activeF (m := m' + 1) (ℓ := ℓ) (θ := θ) hi10
    have hinn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hu : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith
    have hp := D.probA_nonneg hθ (D.layerF ℓ θ (m' + 1) i)
    have hSA : D.SA Φ (D.layerF ℓ θ (m' + 1) i)
        ≤ 25 * (kappa D.a / (Lam D.a * ((i : ℝ) + 1))
            + (kappa D.a - 1) / ((i : ℝ) + 1) ^ 2)
          * D.probA θ (D.layerF ℓ θ (m' + 1) i) := by
      refine le_trans (D.SA_le hℓ hθ0 hθ Φ hsub) ?_
      have hpt : ∀ x₀ ∈ D.layerF ℓ θ (m' + 1) i,
          D.startW θ x₀ * (kappa D.a / (Lam D.a * (D.Rgap ℓ θ x₀ + 1))
              + (kappa D.a - 1) / (D.Rgap ℓ θ x₀ + 1) ^ 2)
            ≤ D.startW θ x₀ * (kappa D.a / (Lam D.a * ((i : ℝ) + 1))
              + (kappa D.a - 1) / ((i : ℝ) + 1) ^ 2) := by
        intro x₀ hx
        refine mul_le_mul_of_nonneg_left ?_ (D.startW_nn hθ x₀)
        have hR : (i : ℝ) ≤ D.Rgap ℓ θ x₀ := D.layerF_Rgap_ge hx
        have t1 : kappa D.a / (Lam D.a * (D.Rgap ℓ θ x₀ + 1))
            ≤ kappa D.a / (Lam D.a * ((i : ℝ) + 1)) :=
          div_le_div_of_nonneg_left (by linarith)
            (mul_pos (by linarith) (by linarith))
            (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
        have t2 : (kappa D.a - 1) / (D.Rgap ℓ θ x₀ + 1) ^ 2
            ≤ (kappa D.a - 1) / ((i : ℝ) + 1) ^ 2 :=
          div_le_div_of_nonneg_left (by linarith) (by positivity)
            (pow_le_pow_left₀ (by linarith) (by linarith) 2)
        linarith
      calc 25 * ∑ x₀ ∈ D.layerF ℓ θ (m' + 1) i, D.startW θ x₀
              * (kappa D.a / (Lam D.a * (D.Rgap ℓ θ x₀ + 1))
                + (kappa D.a - 1) / (D.Rgap ℓ θ x₀ + 1) ^ 2)
          ≤ 25 * ∑ x₀ ∈ D.layerF ℓ θ (m' + 1) i, D.startW θ x₀
              * (kappa D.a / (Lam D.a * ((i : ℝ) + 1))
                + (kappa D.a - 1) / ((i : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by norm_num)
        _ = 25 * (kappa D.a / (Lam D.a * ((i : ℝ) + 1))
              + (kappa D.a - 1) / ((i : ℝ) + 1) ^ 2)
            * D.probA θ (D.layerF ℓ θ (m' + 1) i) := by
            simp only [probA]
            rw [← Finset.sum_mul]
            ring
    have hDAb := hCDb θ hθ0 hθ Φ (D.layerF ℓ θ (m' + 1) i) hsub
    have hres := DA_layer_bound hκ hΛ1 hΛκ hKsq (by linarith) hCD0 hu hp hSA hDAb
    simpa only [layerCoeff] using hres
  -- Step 1
  have hstep1 : D.DA Φ (D.activeF ℓ θ)
      ≤ (∑ i ∈ Finset.Icc 10 m', D.layerCoeff CD i
          * profile D.f (D.T - θ)
            (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1)))
        + D.layerCoeff CD (m' + 1) := by
    rw [D.activeF_eq_biUnion (ℓ := ℓ) (θ := θ) (m := m' + 1) hm']
    refine le_trans (D.DA_biUnion_le hθ Φ (Finset.Icc 10 (m' + 1))
      (D.layerF ℓ θ (m' + 1)) D.layerF_disjoint) ?_
    refine le_trans (Finset.sum_le_sum hlayer) ?_
    have hnotmem : m' + 1 ∉ Finset.Icc 10 m' := by
      intro hc; have := (Finset.mem_Icc.mp hc).2; omega
    rw [Icc_eq_insert 10 m' hm', Finset.sum_insert hnotmem]
    have hA : ∀ i ∈ Finset.Icc 10 m',
        D.layerCoeff CD i * D.probA θ (D.layerF ℓ θ (m' + 1) i)
          = D.layerCoeff CD i * profile D.f (D.T - θ)
              (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1)) := by
      intro i hi
      rw [D.probA_layerF_eq (Finset.mem_Icc.mp hi).1
        (by have := (Finset.mem_Icc.mp hi).2; omega)]
    have hB : D.layerCoeff CD (m' + 1)
        * D.probA θ (D.layerF ℓ θ (m' + 1) (m' + 1))
          ≤ D.layerCoeff CD (m' + 1) := by
      have h1 := D.probA_le_one hθ (D.layerF ℓ θ (m' + 1) (m' + 1))
      have h2 := D.layerCoeff_nonneg hCD0 (m' + 1)
      nlinarith
    rw [Finset.sum_congr rfl hA]
    linarith
  -- Step 2
  have hstep2 := D.Aband_compl_le (ℓ := ℓ) hθ0' hθ Φ hQ
  simp only [errMaj]
  linarith

/-! ### Step 3 of [LGF Prop 3.2]: the `θ`-average of the majorant -/

private lemma intervalIntegrable_profile (c : ℝ) (I : Set ℝ)
    (hI : MeasurableSet I) :
    IntervalIntegrable (fun t => c * profile D.f t I) MeasureTheory.volume
      D.tA (D.tA + 1) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => |c|)
    (MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne)
    ((measurable_profile D.hf I hI).const_mul c).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans D.tA_pos.le ht.1.le
  have h1 : 0 ≤ profile D.f t I := profile_nonneg D.hf ht0 I
  have h2 : profile D.f t I ≤ 1 := profile_le_one D.hf D.hm ht0 I
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
  linarith [mul_nonneg (abs_nonneg c) (by linarith : (0 : ℝ) ≤ 1 - profile D.f t I)]

private lemma intervalIntegrable_errMaj (CD ℓ : ℝ) (m' Q : ℕ) :
    IntervalIntegrable (D.errMaj CD ℓ m' Q) MeasureTheory.volume
      D.tA (D.tA + 1) := by
  have h1 : IntervalIntegrable (fun t => ∑ i ∈ Finset.Icc 10 m',
      D.layerCoeff CD i * profile D.f t
        (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1)))
      MeasureTheory.volume D.tA (D.tA + 1) :=
    intervalIntegrable_finsum' _ _ fun i =>
      D.intervalIntegrable_profile _ _ measurableSet_Ioc
  have h2 : IntervalIntegrable (fun _ : ℝ => D.layerCoeff CD (m' + 1))
      MeasureTheory.volume D.tA (D.tA + 1) := intervalIntegrable_const
  have h3 : IntervalIntegrable (fun t => ∑ q ∈ Finset.range Q,
      Real.exp (11 - (q : ℝ)) * profile D.f t
        (Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1)))
      MeasureTheory.volume D.tA (D.tA + 1) :=
    intervalIntegrable_finsum' _ _ fun q =>
      D.intervalIntegrable_profile _ _ measurableSet_Ioc
  unfold errMaj
  exact (h1.add h2).add h3

/-- **Step 3 of [LGF Prop 3.2]**: the windowed profile bound [C Lemma 4]
applied layer by layer gives `∫ Err ≲ K_a/√ℓ`. -/
private lemma errMaj_integral_le {CD CP ℓ : ℝ} (hCD0 : 0 ≤ CD) (hCP0 : 0 < CP)
    (hCPb : ∀ r : ℝ, 2 < r →
      (∫ t in D.tA..(D.tA + 1), profile D.f t (Set.Ioc r (r + 1))) ≤ CP / r)
    (hℓ64 : 64 ≤ ℓ) (hℓK : Ka D.a ^ 2 ≤ ℓ) {m' Q : ℕ}
    (hmle : (m' : ℝ) + 1 ≤ ℓ / 2) (hmge : ℓ / 2 - 1 ≤ (m' : ℝ) + 1) :
    (∫ t in D.tA..(D.tA + 1), D.errMaj CD ℓ m' Q t)
      ≤ (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP) * Ka D.a
          / Real.sqrt ℓ := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ0
  have hs : (0 : ℝ) < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
  have hsne : Real.sqrt ℓ ≠ 0 := ne_of_gt hs
  have hss : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓ0.le
  have hs8 : (8 : ℝ) ≤ Real.sqrt ℓ := by
    have h := Real.sqrt_le_sqrt (show (64 : ℝ) ≤ ℓ from hℓ64)
    rwa [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hκ : 1 < kappa D.a := one_lt_kappa D.ha0 D.ha1
  have hΛ1 : 1 ≤ Lam D.a := one_le_Lam D.ha0 D.ha1
  have hΛκ : Lam D.a ≤ kappa D.a := Lam_le_kappa D.ha0 D.ha1
  have hKsq : Ka D.a ^ 2 = kappa D.a ^ 3 * Lam D.a := Ka_sq_eq D.ha0 D.ha1
  have hK1 : 1 ≤ Ka D.a := one_le_Ka D.ha0 D.ha1
  have hK0 : (0 : ℝ) ≤ Ka D.a := by linarith
  have hE0 : (0 : ℝ) ≤ kappa D.a ^ 2 * Lam D.a :=
    mul_nonneg (by positivity) (by linarith)
  have habs := kappa_sq_Lam_log_le hκ hΛ1 hΛκ hKsq hK1 hℓK (by linarith)
  have hlog0 : (0 : ℝ) ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  have hE : kappa D.a ^ 2 * Lam D.a ≤ 5 * Ka D.a * Real.sqrt ℓ := by
    linarith [mul_le_mul_of_nonneg_left
      (by linarith : (1 : ℝ) ≤ 1 + Real.log ℓ) hE0, habs]
  have hKs : Ka D.a ≤ Real.sqrt ℓ := by
    rw [show Ka D.a = Real.sqrt (Ka D.a ^ 2) from (Real.sqrt_sq hK0).symm]
    exact Real.sqrt_le_sqrt hℓK
  -- the uniform band-integral bound
  have hband : ∀ r : ℝ, ℓ / 2 ≤ r →
      (∫ t in D.tA..(D.tA + 1), profile D.f t (Set.Ioc r (r + 1)))
        ≤ 2 * CP / ℓ := by
    intro r hr
    refine le_trans (hCPb r (by linarith)) ?_
    have he : CP / (ℓ / 2) = 2 * CP / ℓ := by rw [div_div_eq_mul_div]; ring
    rw [← he]
    exact div_le_div_of_nonneg_left hCP0.le (by linarith) hr
  -- split the integral
  have h1 : IntervalIntegrable (fun t => ∑ i ∈ Finset.Icc 10 m',
      D.layerCoeff CD i * profile D.f t
        (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1)))
      MeasureTheory.volume D.tA (D.tA + 1) :=
    intervalIntegrable_finsum' _ _ fun i =>
      D.intervalIntegrable_profile _ _ measurableSet_Ioc
  have h2 : IntervalIntegrable (fun _ : ℝ => D.layerCoeff CD (m' + 1))
      MeasureTheory.volume D.tA (D.tA + 1) := intervalIntegrable_const
  have h3 : IntervalIntegrable (fun t => ∑ q ∈ Finset.range Q,
      Real.exp (11 - (q : ℝ)) * profile D.f t
        (Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1)))
      MeasureTheory.volume D.tA (D.tA + 1) :=
    intervalIntegrable_finsum' _ _ fun q =>
      D.intervalIntegrable_profile _ _ measurableSet_Ioc
  have hsplitI : (∫ t in D.tA..(D.tA + 1), D.errMaj CD ℓ m' Q t)
      = (∑ i ∈ Finset.Icc 10 m', D.layerCoeff CD i
          * ∫ t in D.tA..(D.tA + 1), profile D.f t
              (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1)))
        + D.layerCoeff CD (m' + 1)
        + ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ))
            * ∫ t in D.tA..(D.tA + 1), profile D.f t
                (Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1)) := by
    unfold errMaj
    rw [intervalIntegral.integral_add (h1.add h2) h3,
      intervalIntegral.integral_add h1 h2]
    congr 1
    · congr 1
      · rw [intervalIntegral.integral_finset_sum
          (fun i _ => D.intervalIntegrable_profile _ _ measurableSet_Ioc)]
        exact Finset.sum_congr rfl fun i _ =>
          intervalIntegral.integral_const_mul _ _
      · rw [intervalIntegral.integral_const,
          show D.tA + 1 - D.tA = 1 by ring, one_smul]
    · rw [intervalIntegral.integral_finset_sum
        (fun q _ => D.intervalIntegrable_profile _ _ measurableSet_Ioc)]
      exact Finset.sum_congr rfl fun q _ =>
        intervalIntegral.integral_const_mul _ _
  rw [hsplitI]
  -- Term A: the layered active discrepancy
  have hTA : (∑ i ∈ Finset.Icc 10 m', D.layerCoeff CD i
        * ∫ t in D.tA..(D.tA + 1), profile D.f t
            (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1)))
      ≤ (∑ i ∈ Finset.range (m' + 1), D.layerCoeff CD i) * (2 * CP / ℓ) := by
    have hstep : ∀ i ∈ Finset.Icc 10 m', D.layerCoeff CD i
        * ∫ t in D.tA..(D.tA + 1), profile D.f t
            (Set.Ioc (ℓ - (i : ℝ) - 1) (ℓ - (i : ℝ) - 1 + 1))
        ≤ D.layerCoeff CD i * (2 * CP / ℓ) := by
      intro i hi
      refine mul_le_mul_of_nonneg_left (hband _ ?_) (D.layerCoeff_nonneg hCD0 i)
      have hic : (i : ℝ) ≤ (m' : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hi).2
      linarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_
      (div_nonneg (by linarith) hℓ0.le)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun i _ _ => D.layerCoeff_nonneg hCD0 i)
    intro i hi
    exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hi).2; omega)
  have hcast : ((m' + 1 : ℕ) : ℝ) = (m' : ℝ) + 1 := by push_cast; ring
  have hsumcoeff : ∑ i ∈ Finset.range (m' + 1), D.layerCoeff CD i
      ≤ CD * (210 * Ka D.a * Real.sqrt ℓ) := by
    have e : ∑ i ∈ Finset.range (m' + 1), D.layerCoeff CD i
        = CD * ∑ i ∈ Finset.range (m' + 1),
            (5 * Ka D.a / Real.sqrt ((i : ℝ) + 1)
              + 30 * kappa D.a ^ 2 * Lam D.a / ((i : ℝ) + 1)
              + 25 * Ka D.a ^ 2 / ((i : ℝ) + 1) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hCD0
    refine le_trans (sum_layer_coeff_le hK0 hE0 (m' + 1)) ?_
    rw [hcast]
    have hMr0 : (0 : ℝ) < (m' : ℝ) + 1 := by positivity
    have hMrℓ : (m' : ℝ) + 1 ≤ ℓ := by linarith
    have hsq1 : Real.sqrt ((m' : ℝ) + 1) ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt hMrℓ
    have hlogle : Real.log ((m' : ℝ) + 1) ≤ Real.log ℓ :=
      Real.log_le_log hMr0 hMrℓ
    have t1 : 10 * Ka D.a * Real.sqrt ((m' : ℝ) + 1)
        ≤ 10 * Ka D.a * Real.sqrt ℓ :=
      mul_le_mul_of_nonneg_left hsq1 (by linarith)
    have t2 : 30 * (kappa D.a ^ 2 * Lam D.a) * (1 + Real.log ((m' : ℝ) + 1))
        ≤ 150 * Ka D.a * Real.sqrt ℓ := by
      linarith [mul_le_mul_of_nonneg_left hlogle hE0, habs]
    have t3 : 50 * Ka D.a ^ 2 ≤ 50 * Ka D.a * Real.sqrt ℓ := by
      linarith [mul_le_mul_of_nonneg_left hKs hK0]
    linarith [t1, t2, t3]
  have hTAfin : (∑ i ∈ Finset.range (m' + 1), D.layerCoeff CD i) * (2 * CP / ℓ)
      ≤ 420 * CP * CD * Ka D.a / Real.sqrt ℓ := by
    have hmono : (∑ i ∈ Finset.range (m' + 1), D.layerCoeff CD i) * (2 * CP / ℓ)
        ≤ (CD * (210 * Ka D.a * Real.sqrt ℓ)) * (2 * CP / ℓ) :=
      mul_le_mul_of_nonneg_right hsumcoeff (div_nonneg (by linarith) hℓ0.le)
    refine le_trans hmono (le_of_eq ?_)
    have hsl : Real.sqrt ℓ / ℓ = 1 / Real.sqrt ℓ := by
      field_simp
      linarith [hss]
    have e1 : (CD * (210 * Ka D.a * Real.sqrt ℓ)) * (2 * CP / ℓ)
        = (420 * CP * CD * Ka D.a) * (Real.sqrt ℓ / ℓ) := by ring
    rw [e1, hsl]
    ring
  -- Term B: the top layer
  have hw : ℓ / 2 ≤ (m' : ℝ) + 2 := by linarith
  have hw0 : (0 : ℝ) < (m' : ℝ) + 2 := by positivity
  have hsw : (0 : ℝ) < Real.sqrt ((m' : ℝ) + 2) := Real.sqrt_pos.mpr hw0
  have hBcoeff : D.layerCoeff CD (m' + 1)
      = CD * (5 * Ka D.a / Real.sqrt ((m' : ℝ) + 2)
        + 30 * (kappa D.a ^ 2 * Lam D.a) / ((m' : ℝ) + 2)
        + 25 * Ka D.a ^ 2 / ((m' : ℝ) + 2) ^ 2) := by
    simp only [layerCoeff]
    rw [show ((m' + 1 : ℕ) : ℝ) + 1 = (m' : ℝ) + 2 by push_cast; ring]
    ring
  have hsws : Real.sqrt ℓ ≤ 2 * Real.sqrt ((m' : ℝ) + 2) := by
    have h := Real.sqrt_le_sqrt (show ℓ ≤ 4 * ((m' : ℝ) + 2) by linarith)
    have e : Real.sqrt (4 * ((m' : ℝ) + 2)) = 2 * Real.sqrt ((m' : ℝ) + 2) := by
      rw [show (4 : ℝ) * ((m' : ℝ) + 2) = 2 ^ 2 * ((m' : ℝ) + 2) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rwa [e] at h
  have hKss : Ka D.a * (Real.sqrt ℓ * Real.sqrt ℓ) = Ka D.a * ℓ := by rw [hss]
  have hB1 : 5 * Ka D.a / Real.sqrt ((m' : ℝ) + 2)
      ≤ 10 * Ka D.a / Real.sqrt ℓ := by
    rw [div_le_div_iff₀ hsw hs]
    linarith [mul_le_mul_of_nonneg_left hsws hK0]
  have hB2 : 30 * (kappa D.a ^ 2 * Lam D.a) / ((m' : ℝ) + 2)
      ≤ 300 * Ka D.a / Real.sqrt ℓ := by
    rw [div_le_div_iff₀ hw0 hs]
    linarith [mul_le_mul_of_nonneg_right hE hs.le, hKss,
      mul_le_mul_of_nonneg_left hw hK0]
  have hB3 : 25 * Ka D.a ^ 2 / ((m' : ℝ) + 2) ^ 2
      ≤ 100 * Ka D.a / Real.sqrt ℓ := by
    rw [div_le_div_iff₀ (by positivity) hs]
    have g1 : Ka D.a * Real.sqrt ℓ * Ka D.a ≤ Ka D.a * Real.sqrt ℓ * Real.sqrt ℓ :=
      mul_le_mul_of_nonneg_left hKs (mul_nonneg hK0 hs.le)
    have g3 : Ka D.a * (ℓ / 2) ^ 2 ≤ Ka D.a * ((m' : ℝ) + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) hw 2) hK0
    have hll : ℓ ≤ ℓ ^ 2 := by
      linarith [mul_nonneg hℓ0.le (by linarith : (0 : ℝ) ≤ ℓ - 1)]
    have g4 : Ka D.a * ℓ ≤ Ka D.a * ℓ ^ 2 :=
      mul_le_mul_of_nonneg_left hll hK0
    linarith [g1, g3, g4, hKss]
  have hTB : D.layerCoeff CD (m' + 1) ≤ 410 * CD * Ka D.a / Real.sqrt ℓ := by
    rw [hBcoeff]
    have hsum : 5 * Ka D.a / Real.sqrt ((m' : ℝ) + 2)
          + 30 * (kappa D.a ^ 2 * Lam D.a) / ((m' : ℝ) + 2)
          + 25 * Ka D.a ^ 2 / ((m' : ℝ) + 2) ^ 2
        ≤ 410 * Ka D.a / Real.sqrt ℓ := by
      have e : (10 : ℝ) * Ka D.a / Real.sqrt ℓ + 300 * Ka D.a / Real.sqrt ℓ
          + 100 * Ka D.a / Real.sqrt ℓ = 410 * Ka D.a / Real.sqrt ℓ := by
        field_simp; ring
      linarith [hB1, hB2, hB3, e.le, e.ge]
    have hmul := mul_le_mul_of_nonneg_left hsum hCD0
    refine le_trans hmul (le_of_eq ?_)
    field_simp
  -- Term C: the inactive layers
  have hTC : (∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ))
        * ∫ t in D.tA..(D.tA + 1), profile D.f t
            (Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1)))
      ≤ 4 * Real.exp 11 * CP * Ka D.a / Real.sqrt ℓ := by
    have hstep : ∀ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ))
        * ∫ t in D.tA..(D.tA + 1), profile D.f t
            (Set.Ioc (ℓ - 10 + (q : ℝ)) (ℓ - 10 + (q : ℝ) + 1))
        ≤ Real.exp (11 - (q : ℝ)) * (2 * CP / ℓ) := by
      intro q _
      refine mul_le_mul_of_nonneg_left (hband _ ?_) (Real.exp_pos _).le
      have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.sum_mul]
    have hgeo : ∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ)) ≤ 2 * Real.exp 11 :=
      sum_exp_shift_le Q
    have hmono : (∑ q ∈ Finset.range Q, Real.exp (11 - (q : ℝ))) * (2 * CP / ℓ)
        ≤ (2 * Real.exp 11) * (2 * CP / ℓ) :=
      mul_le_mul_of_nonneg_right hgeo (div_nonneg (by linarith) hℓ0.le)
    refine le_trans hmono ?_
    have he : (2 * Real.exp 11) * (2 * CP / ℓ) = 4 * Real.exp 11 * CP / ℓ := by
      ring
    rw [he, div_le_div_iff₀ hℓ0 hs]
    have hKl : Real.sqrt ℓ ≤ Ka D.a * ℓ := by
      linarith [mul_nonneg (sub_nonneg.mpr hK1) hℓ0.le, hss,
        mul_nonneg hs.le (by linarith : (0 : ℝ) ≤ Real.sqrt ℓ - 1)]
    have hc0 : (0 : ℝ) ≤ 4 * Real.exp 11 * CP :=
      mul_nonneg (by positivity) hCP0.le
    linarith [mul_le_mul_of_nonneg_left hKl hc0]
  -- combine
  have hfin : 420 * CP * CD * Ka D.a / Real.sqrt ℓ
      + 410 * CD * Ka D.a / Real.sqrt ℓ
      + 4 * Real.exp 11 * CP * Ka D.a / Real.sqrt ℓ
      = (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP) * Ka D.a
          / Real.sqrt ℓ := by
    field_simp
  linarith [le_trans hTA hTAfin, hTB, hTC, hfin.le, hfin.ge]

/-- **The band recurrence** of [LGF Prop 3.2]: one step of the geometric
bootstrap at a level `ℓ ≥ max(64, K_a²)`. Steps 1–2 bound the error term
pointwise in `θ`, Step 3 picks a good `θ` by the mean-value principle on the
window `[T_o-1, T_o]`, and [LGF Lemma 3.4] closes the loop. -/
private lemma band_step {CD CP : ℝ} (hCD0 : 0 < CD) (hCP0 : 0 < CP)
    (hCDb : ∀ (ℓ θ : ℝ), 0 < ℓ → obsT - 1 ≤ θ → θ ≤ obsT →
      ∀ (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)), A ⊆ D.activeF ℓ θ →
      D.DA Φ A ≤ CD * (kappa D.a * Lam D.a
          * Real.sqrt (D.SA Φ A * D.probA θ A)
        + kappa D.a * Lam D.a ^ 2 * D.SA Φ A))
    (hCPb : ∀ r : ℝ, 2 < r →
      (∫ t in D.tA..(D.tA + 1), profile D.f t (Set.Ioc r (r + 1))) ≤ CP / r)
    {ℓ M : ℝ} (hℓ64 : 64 ≤ ℓ) (hℓK : Ka D.a ^ 2 ≤ ℓ) (hM0 : 0 ≤ M)
    (hMbd : ∀ r : ℝ, ℓ ≤ r →
      Real.sqrt r * profile D.f D.tA (Set.Ioc r (r + 1)) ≤ M) :
    Real.sqrt ℓ * profile D.f D.tA (Set.Ioc ℓ (ℓ + 1))
      ≤ 1 / 15 * M
        + 32 / 15 * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)
            * Ka D.a := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hs : (0 : ℝ) < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
  have hsne : Real.sqrt ℓ ≠ 0 := ne_of_gt hs
  -- the layer count `m = ⌊ℓ/2⌋ = m' + 1`
  have hmle : ((⌊ℓ / 2⌋₊ : ℕ) : ℝ) ≤ ℓ / 2 := Nat.floor_le (by linarith)
  have hmge : ℓ / 2 < ((⌊ℓ / 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm32 : 32 ≤ ⌊ℓ / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
  obtain ⟨m', hm'eq⟩ : ∃ m' : ℕ, ⌊ℓ / 2⌋₊ = m' + 1 := ⟨⌊ℓ / 2⌋₊ - 1, by omega⟩
  have hm'10 : 10 ≤ m' + 1 := by omega
  have hcast : ((m' + 1 : ℕ) : ℝ) = (m' : ℝ) + 1 := by push_cast; ring
  have hmle' : (m' : ℝ) + 1 ≤ ℓ / 2 := by rw [← hcast, ← hm'eq]; exact hmle
  have hmge' : ℓ / 2 - 1 ≤ (m' : ℝ) + 1 := by
    rw [← hcast, ← hm'eq]; linarith
  -- the far cutoff `Q`
  have hQb : (n : ℝ) * Real.log 2
      ≤ ℓ - 10 + ((12 + ⌈(n : ℝ) * Real.log 2⌉₊ : ℕ) : ℝ) := by
    have h1 : (n : ℝ) * Real.log 2 ≤ ((⌈(n : ℝ) * Real.log 2⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((12 + ⌈(n : ℝ) * Real.log 2⌉₊ : ℕ) : ℝ)
        = 12 + ((⌈(n : ℝ) * Real.log 2⌉₊ : ℕ) : ℝ) := by push_cast; ring
    rw [h2]; linarith
  -- Step 3: the mean-value choice of the start time
  have hint := D.errMaj_integral_le hCD0.le hCP0 hCPb hℓ64 hℓK hmle' hmge'
    (Q := 12 + ⌈(n : ℝ) * Real.log 2⌉₊)
  have hIvol : MeasureTheory.volume (Set.Ioc D.tA (D.tA + 1)) ≠ 0 := by
    rw [Real.volume_Ioc, show D.tA + 1 - D.tA = 1 by ring]
    simp
  have hIon : MeasureTheory.IntegrableOn
      (D.errMaj CD ℓ m' (12 + ⌈(n : ℝ) * Real.log 2⌉₊))
      (Set.Ioc D.tA (D.tA + 1)) MeasureTheory.volume := by
    have h := D.intervalIntegrable_errMaj CD ℓ m' (12 + ⌈(n : ℝ) * Real.log 2⌉₊)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at h
  obtain ⟨t, ht, hmean⟩ :=
    MeasureTheory.exists_le_setAverage hIvol measure_Ioc_lt_top.ne hIon
  have havg : (⨍ u in Set.Ioc D.tA (D.tA + 1),
        D.errMaj CD ℓ m' (12 + ⌈(n : ℝ) * Real.log 2⌉₊) u)
      = ∫ u in D.tA..(D.tA + 1),
        D.errMaj CD ℓ m' (12 + ⌈(n : ℝ) * Real.log 2⌉₊) u := by
    rw [MeasureTheory.setAverage_eq,
      Real.volume_real_Ioc_of_le (by linarith : D.tA ≤ D.tA + 1),
      show D.tA + 1 - D.tA = 1 by ring, inv_one, one_smul,
      intervalIntegral.integral_of_le (by linarith : D.tA ≤ D.tA + 1)]
  rw [havg] at hmean
  -- the good start time
  have hT : D.T = D.tA + obsT := rfl
  have hθle : D.T - t ≤ obsT := by have := ht.1; rw [hT]; linarith
  have hθge : obsT - 1 ≤ D.T - t := by have := ht.2; rw [hT]; linarith
  have hθ0 : (0 : ℝ) ≤ D.T - t := by simp only [obsT] at hθge; linarith
  obtain ⟨Φ⟩ := D.exists_cflowFamily ℓ hℓ0 hθ0 hθle
  have hTθ : D.T - (D.T - t) = t := by ring
  have herr := D.errMaj_ge hCD0.le
    (fun θ' h1 h2 Φ' A hA => hCDb ℓ θ' hℓ0 h1 h2 Φ' A hA)
    hℓ0 hm'10 hQb hθge hθle Φ
  rw [hTθ] at herr
  -- [LGF Lemma 3.4] and the profile split
  have hprofsplit := D.profile_eq_Aband_add hℓ0 hθ0 hθle Φ
  have hbc := D.band_contraction hℓ0 hθ0 hθle Φ
  have hAnn := D.Aband_nonneg hθ0 hθle Φ (D.activeF ℓ (D.T - t)) ℓ
  have hBnn := D.Aband_nonneg hθ0 hθle Φ (D.activeF ℓ (D.T - t))ᶜ ℓ
  -- the geometric tail
  have htail : (∑' j : ℕ, Real.exp (-((j : ℝ) + 1))
      * D.Aband Φ (D.activeF ℓ (D.T - t)) (ℓ + j + 1)) ≤ M / Real.sqrt ℓ := by
    have hsum1 := D.Aband_summable hℓ0 hθ0 hθle Φ (D.activeF ℓ (D.T - t))
    have hsum2 : Summable
        (fun j : ℕ => Real.exp (-((j : ℝ) + 1)) * (M / Real.sqrt ℓ)) :=
      summable_exp_neg_succ.mul_right _
    have hbdd : ∀ j : ℕ, Real.exp (-((j : ℝ) + 1))
        * D.Aband Φ (D.activeF ℓ (D.T - t)) (ℓ + j + 1)
        ≤ Real.exp (-((j : ℝ) + 1)) * (M / Real.sqrt ℓ) := by
      intro j
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hjn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have h1 := D.Aband_le_profile hθ0 hθle Φ (D.activeF ℓ (D.T - t))
        (ℓ + (j : ℝ) + 1)
      have h2 := hMbd (ℓ + (j : ℝ) + 1) (by linarith)
      have hsj : (0 : ℝ) < Real.sqrt (ℓ + (j : ℝ) + 1) :=
        Real.sqrt_pos.mpr (by linarith)
      have h3 : profile D.f D.tA
          (Set.Ioc (ℓ + (j : ℝ) + 1) (ℓ + (j : ℝ) + 1 + 1))
          ≤ M / Real.sqrt (ℓ + (j : ℝ) + 1) := by
        rw [le_div_iff₀ hsj]; linarith
      have h4 : M / Real.sqrt (ℓ + (j : ℝ) + 1) ≤ M / Real.sqrt ℓ :=
        div_le_div_of_nonneg_left hM0 hs (Real.sqrt_le_sqrt (by linarith))
      linarith
    calc (∑' j : ℕ, Real.exp (-((j : ℝ) + 1))
            * D.Aband Φ (D.activeF ℓ (D.T - t)) (ℓ + j + 1))
        ≤ ∑' j : ℕ, Real.exp (-((j : ℝ) + 1)) * (M / Real.sqrt ℓ) :=
          hsum1.tsum_le_tsum hbdd hsum2
      _ = (∑' j : ℕ, Real.exp (-((j : ℝ) + 1))) * (M / Real.sqrt ℓ) :=
          tsum_mul_right
      _ ≤ 1 * (M / Real.sqrt ℓ) :=
          mul_le_mul_of_nonneg_right tsum_exp_neg_succ_le_one
            (div_nonneg hM0 hs.le)
      _ = M / Real.sqrt ℓ := one_mul _
  -- close the step
  have hc₀ : Real.exp (1 - alphaC) ≤ 1 / 16 := exp_one_sub_alphaC_le
  have hc₀0 : (0 : ℝ) < Real.exp (1 - alphaC) := Real.exp_pos _
  have hDB : D.DA Φ (D.activeF ℓ (D.T - t))
      + D.Aband Φ (D.activeF ℓ (D.T - t))ᶜ ℓ
      ≤ (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP) * Ka D.a
          / Real.sqrt ℓ := le_trans herr (le_trans hmean hint)
  have e1 : (15 / 16 : ℝ) * D.Aband Φ (D.activeF ℓ (D.T - t)) ℓ
      ≤ (1 - Real.exp (1 - alphaC)) * D.Aband Φ (D.activeF ℓ (D.T - t)) ℓ :=
    mul_le_mul_of_nonneg_right (by linarith) hAnn
  have e2 : Real.exp (1 - alphaC) * (M / Real.sqrt ℓ)
      ≤ 1 / 16 * (M / Real.sqrt ℓ) :=
    mul_le_mul_of_nonneg_right hc₀ (div_nonneg hM0 hs.le)
  have e3 : Real.exp (1 - alphaC) *
      (∑' j : ℕ, Real.exp (-((j : ℝ) + 1))
        * D.Aband Φ (D.activeF ℓ (D.T - t)) (ℓ + j + 1))
      ≤ Real.exp (1 - alphaC) * (M / Real.sqrt ℓ) :=
    mul_le_mul_of_nonneg_left htail hc₀0.le
  have hA : D.Aband Φ (D.activeF ℓ (D.T - t)) ℓ
      ≤ 1 / 15 * (M / Real.sqrt ℓ)
        + 32 / 15 * D.DA Φ (D.activeF ℓ (D.T - t)) := by
    linarith [hbc, e1, e2, e3]
  have hP : profile D.f D.tA (Set.Ioc ℓ (ℓ + 1))
      ≤ 1 / 15 * (M / Real.sqrt ℓ)
        + 32 / 15 * ((420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)
            * Ka D.a / Real.sqrt ℓ) := by
    rw [hprofsplit]
    linarith [hA, hDB, hBnn]
  have hmul := mul_le_mul_of_nonneg_left hP hs.le
  have hinv : Real.sqrt ℓ * (Real.sqrt ℓ)⁻¹ = 1 := mul_inv_cancel₀ hsne
  have hsimp : Real.sqrt ℓ * (1 / 15 * (M / Real.sqrt ℓ)
        + 32 / 15 * ((420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)
            * Ka D.a / Real.sqrt ℓ))
      = (1 / 15 * M
          + 32 / 15 * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)
            * Ka D.a) * (Real.sqrt ℓ * (Real.sqrt ℓ)⁻¹) := by ring
  rw [hinv, mul_one] at hsimp
  linarith [hmul, hsimp.le, hsimp.ge]

end Dat

/-- **Fixed-band anti-concentration** [LGF Proposition 3.2]: there is a
universal `C` with `𝔄_{t_a}((ℓ,ℓ+1]) ≤ C·K_a/√ℓ` for all data and `ℓ > 0`. -/
theorem fixed_band :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (D : Dat n) (ℓ : ℝ), 0 < ℓ →
      profile D.f D.tA (Set.Ioc ℓ (ℓ + 1))
        ≤ C * Ka D.a / Real.sqrt ℓ := by
  obtain ⟨CD, hCD0, hCD⟩ := Dat.DA_le
  obtain ⟨CP, hCP0, hCP⟩ := profile_window_integral_le
  have hc₂0 : (0 : ℝ)
      < 420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP := by
    have h1 : (0 : ℝ) < 420 * CP * CD :=
      mul_pos (mul_pos (by norm_num) hCP0) hCD0
    have h2 : (0 : ℝ) < 410 * CD := mul_pos (by norm_num) hCD0
    have h3 : (0 : ℝ) < 4 * Real.exp 11 * CP :=
      mul_pos (by positivity) hCP0
    linarith
  refine ⟨max 9 (16 / 7 * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro n D ℓ hℓ0
  have hK1 : 1 ≤ Ka D.a := one_le_Ka D.ha0 D.ha1
  have hK0 : (0 : ℝ) ≤ Ka D.a := by linarith
  have hs : (0 : ℝ) < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
  have hC9 : (9 : ℝ)
      ≤ max 9 (16 / 7 * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)) :=
    le_max_left _ _
  have hCc : 16 / 7 * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)
      ≤ max 9 (16 / 7 * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)) :=
    le_max_right _ _
  -- specialized inputs
  have hCDb : ∀ (ℓ' θ : ℝ), 0 < ℓ' → obsT - 1 ≤ θ → θ ≤ obsT →
      ∀ (Φ : D.CFlowFamily ℓ' θ) (A : Finset (Cube n)), A ⊆ D.activeF ℓ' θ →
      D.DA Φ A ≤ CD * (kappa D.a * Lam D.a
          * Real.sqrt (D.SA Φ A * D.probA θ A)
        + kappa D.a * Lam D.a ^ 2 * D.SA Φ A) :=
    fun ℓ' θ h1 h2 h3 Φ A hA => hCD D ℓ' θ h1 h2 h3 Φ A hA
  have hCPb : ∀ r : ℝ, 2 < r →
      (∫ t in D.tA..(D.tA + 1), profile D.f t (Set.Ioc r (r + 1))) ≤ CP / r :=
    fun r hr => hCP D.f D.hf D.hm r hr D.tA (D.tA + 1) D.tA_pos.le (by linarith)
  -- the bootstrap functional
  set g : ℝ → ℝ := fun r => Real.sqrt r * profile D.f D.tA (Set.Ioc r (r + 1))
    with hgdef
  have hgnn : ∀ r : ℝ, 0 ≤ g r := fun r => by
    simp only [hgdef]
    exact mul_nonneg (Real.sqrt_nonneg r) (profile_nonneg D.hf D.tA_pos.le _)
  have hL64 : (64 : ℝ) ≤ 64 + Ka D.a ^ 2 := by nlinarith
  have hLK : Ka D.a ^ 2 ≤ 64 + Ka D.a ^ 2 := by linarith
  have hne : (g '' Set.Ici (64 + Ka D.a ^ 2)).Nonempty :=
    ⟨g (64 + Ka D.a ^ 2), ⟨64 + Ka D.a ^ 2, Set.self_mem_Ici, rfl⟩⟩
  obtain ⟨B, hB⟩ := D.exists_profile_vanish
  have hbdd : BddAbove (g '' Set.Ici (64 + Ka D.a ^ 2)) := by
    refine ⟨Real.sqrt B + 1, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    simp only [hgdef]
    by_cases hrB : B ≤ r
    · rw [hB r hrB, mul_zero]
      positivity
    · have h1 : profile D.f D.tA (Set.Ioc r (r + 1)) ≤ 1 :=
        profile_le_one D.hf D.hm D.tA_pos.le _
      have h0 : 0 ≤ profile D.f D.tA (Set.Ioc r (r + 1)) :=
        profile_nonneg D.hf D.tA_pos.le _
      have h2 : Real.sqrt r ≤ Real.sqrt B :=
        Real.sqrt_le_sqrt (le_of_lt (not_le.mp hrB))
      have h3 : (0 : ℝ) ≤ Real.sqrt r := Real.sqrt_nonneg r
      nlinarith
  set M : ℝ := sSup (g '' Set.Ici (64 + Ka D.a ^ 2)) with hMdef
  have hMub : ∀ r : ℝ, 64 + Ka D.a ^ 2 ≤ r → g r ≤ M := fun r hr =>
    le_csSup hbdd ⟨r, hr, rfl⟩
  have hM0 : (0 : ℝ) ≤ M :=
    le_trans (hgnn (64 + Ka D.a ^ 2)) (hMub _ le_rfl)
  have hMstep : ∀ y ∈ g '' Set.Ici (64 + Ka D.a ^ 2),
      y ≤ 1 / 15 * M
        + 32 / 15 * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)
            * Ka D.a := by
    rintro y ⟨r, hr, rfl⟩
    have hrL : 64 + Ka D.a ^ 2 ≤ r := hr
    have hsq0 : (0 : ℝ) ≤ Ka D.a ^ 2 := sq_nonneg _
    simp only [hgdef]
    refine D.band_step hCD0 hCP0 hCDb hCPb (by linarith) (by linarith) hM0 ?_
    intro r' hr'
    have h := hMub r' (le_trans hrL hr')
    simpa only [hgdef] using h
  have hMrec : M ≤ 1 / 15 * M
      + 32 / 15 * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)
          * Ka D.a := csSup_le hne hMstep
  have hMle : M ≤ 16 / 7
      * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP) * Ka D.a := by
    linarith
  by_cases hcase : 64 + Ka D.a ^ 2 ≤ ℓ
  · have h1 := hMub ℓ hcase
    simp only [hgdef] at h1
    have h2 : profile D.f D.tA (Set.Ioc ℓ (ℓ + 1)) ≤ M / Real.sqrt ℓ := by
      rw [le_div_iff₀ hs]; linarith
    have h3 : M ≤ max 9 (16 / 7
        * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP)) * Ka D.a := by
      have := mul_le_mul_of_nonneg_right hCc hK0
      linarith
    have h4 : M / Real.sqrt ℓ ≤ max 9 (16 / 7
        * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP))
        * Ka D.a / Real.sqrt ℓ := by
      rw [div_le_div_iff₀ hs hs]
      exact mul_le_mul_of_nonneg_right h3 hs.le
    linarith
  · have hPle : profile D.f D.tA (Set.Ioc ℓ (ℓ + 1)) ≤ 1 :=
      profile_le_one D.hf D.hm D.tA_pos.le _
    have hsL : Real.sqrt ℓ ≤ 9 * Ka D.a := by
      have h1 : Real.sqrt ℓ ≤ Real.sqrt (64 + Ka D.a ^ 2) :=
        Real.sqrt_le_sqrt (le_of_lt (not_le.mp hcase))
      have h2 : Real.sqrt (64 + Ka D.a ^ 2) ≤ 8 + Ka D.a :=
        sqrt_le_of_le_sq (by linarith) (by nlinarith)
      linarith
    have h3 : (1 : ℝ) ≤ max 9 (16 / 7
        * (420 * CP * CD + 410 * CD + 4 * Real.exp 11 * CP))
        * Ka D.a / Real.sqrt ℓ := by
      rw [le_div_iff₀ hs, one_mul]
      linarith [mul_le_mul_of_nonneg_right hC9 hK0]
    linarith

end Talagrand
