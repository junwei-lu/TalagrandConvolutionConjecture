import TalagrandConvConjecture.Statement
import TalagrandConvConjecture.ODE.LinearFlow

/-!
# The reverse heat process: fixed data and pointwise identities

Fixed data for the whole argument [LGF §2]: a bias `0 < a < 1` and a strictly
positive density `f` on `Cube n` with `𝔼_λ f = 1`. Derived quantities:
`t_a = -log a`, observation time `T_o = 2`, horizon `T = t_a + 2`, and for
`0 ≤ t ≤ T`:

* `F t x = log f_{T-t}(x)` (reverse-time log-density),
* `Y t i x = f_{T-t}(σ_i x)/f_{T-t}(x)` (reverse jump-rate ratio),
* `Sc t i x = (1 - Y t i x)/2` (score) [LGF eq (2.1)].

The reverse process of [LGF §2.2] is represented by its master equation: the
time-dependent generator `revGen` [LGF eq (3.7)] and the explicit forward
density `revDensity t = f_{T-t}/2^n` which solves the forward equation
(`V_t ∼ ν_{T-t}`). The terminal likelihood `H_t^ζ` [LGF §5.2] with its
harmonicity and the ratio identity `r^ζ·Y = λ^ζ` [LGF eq (4.5)] also lives
here.
-/

namespace Talagrand

/-- The observation time `T_o = 2` [LGF §2.2]. -/
def obsT : ℝ := 2

variable {n : ℕ}

/-- The fixed data of [LGF]: bias `a ∈ (0,1)` and strictly positive density
`f` with `𝔼_λ f = 1`. All fields are constitutive for [LGF Theorem 1.1]'s
proof (the reduction from general `f ≥ 0` is done in `Main.lean`). -/
structure Dat (n : ℕ) where
  /-- the bias parameter of `μ_a` -/
  a : ℝ
  /-- `0 < a` (constitutive, [LGF §1]) -/
  ha0 : 0 < a
  /-- `a < 1` (constitutive, [LGF §1]) -/
  ha1 : a < 1
  /-- the density -/
  f : Cube n → ℝ
  /-- strict positivity (standing assumption of [LGF §2.1]) -/
  hf : ∀ x, 0 < f x
  /-- unit mass `‖f‖₁ = 1` -/
  hm : unifE f = 1

namespace Dat

variable (D : Dat n)

/-- `t_a = -log a`, so that `T_{μ_a} = P_{t_a}` [LGF §2.1]. -/
noncomputable def tA : ℝ := -Real.log D.a

/-- Horizon `T = t_a + T_o` [LGF §2.2]. -/
noncomputable def T : ℝ := D.tA + obsT

/-- `f_s = P_s f`. -/
noncomputable def fs (s : ℝ) : Cube n → ℝ := heatAt D.f s

/-- Reverse-time log-density `F_t(x) = log f_{T-t}(x)` [LGF eq (2.1)]. -/
noncomputable def F (t : ℝ) (x : Cube n) : ℝ := Real.log (D.fs (D.T - t) x)

/-- Reverse jump-rate ratio `Y_i(t,x) = f_{T-t}(σ_i x)/f_{T-t}(x)`
[LGF eq (2.1)]. -/
noncomputable def Y (t : ℝ) (i : Fin n) (x : Cube n) : ℝ :=
  D.fs (D.T - t) (flipCoord i x) / D.fs (D.T - t) x

/-- Score `S_i(t,x) = (1 - Y_i(t,x))/2` [LGF eq (2.1)]. -/
noncomputable def Sc (t : ℝ) (i : Fin n) (x : Cube n) : ℝ := (1 - D.Y t i x) / 2

/-- Time-dependent generator of the reverse process
`L̃_t g(x) = ½∑_i Y_i(t,x)(g(σ_i x) - g(x))` [LGF eq (3.7)]. -/
noncomputable def revGen (t : ℝ) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ i, D.Y t i x * (g (flipCoord i x) - g x) / 2

/-- Forward-equation rate matrix of the reverse process (mass flowing into
`x` from `x'`): `revFwdMat t x x' = ½Y_i(t,x') for x = σ_i x'`, diagonal
`-½∑_i Y_i(t,x)`. -/
noncomputable def revFwdMat (t : ℝ) (x x' : Cube n) : ℝ :=
  (∑ i, if x = flipCoord i x' then D.Y t i x' / 2 else 0)
    - (if x = x' then ∑ i, D.Y t i x / 2 else 0)

/-- Explicit law of the reverse process: `V_t ∼ ν_{T-t}`, density
`f_{T-t}·2^{-n}` w.r.t. counting measure [LGF §2.2]. -/
noncomputable def revDensity (t : ℝ) (x : Cube n) : ℝ := D.fs (D.T - t) x / 2 ^ n

/-! ## Basic positivity and ranges -/

lemma tA_pos : 0 < D.tA := by
  have := Real.log_neg D.ha0 D.ha1
  simp only [tA]; linarith

lemma obsT_lt_T : obsT < D.T := by
  have := D.tA_pos; simp only [T]; linarith

/-- `|e^{-s}| ≤ 1` for `s ≥ 0`: the smoothing parameter stays in the solid
cube along the (forward) heat flow. -/
lemma abs_exp_neg_le_one {s : ℝ} (hs : 0 ≤ s) : |Real.exp (-s)| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hs)

lemma fs_pos {s : ℝ} (hs : 0 ≤ s) (x : Cube n) : 0 < D.fs s x := by
  simp only [fs, heatAt]
  exact smooth_pos (abs_exp_neg_le_one hs) D.hf x

lemma fs_ne_zero {s : ℝ} (hs : 0 ≤ s) (x : Cube n) : D.fs s x ≠ 0 :=
  (D.fs_pos hs x).ne'

lemma fs_zero (x : Cube n) : D.fs 0 x = D.f x := by
  simp only [fs, heatAt, neg_zero, Real.exp_zero, smooth_one]

/-- Mass conservation along the heat flow. -/
lemma unifE_fs (s : ℝ) : unifE (D.fs s) = 1 := by
  simp only [fs, heatAt]
  rw [unifE_smooth, D.hm]

/-- `0 ≤ T - t` whenever `t ≤ T`; the heat time along the reverse process. -/
lemma T_sub_nonneg {t : ℝ} (ht : t ≤ D.T) : (0 : ℝ) ≤ D.T - t := by linarith

lemma Y_pos {t : ℝ} (ht : t ≤ D.T) (i : Fin n) (x : Cube n) :
    0 < D.Y t i x := by
  simp only [Y]
  exact div_pos (D.fs_pos (D.T_sub_nonneg ht) _) (D.fs_pos (D.T_sub_nonneg ht) _)

lemma Y_ne_zero {t : ℝ} (ht : t ≤ D.T) (i : Fin n) (x : Cube n) :
    D.Y t i x ≠ 0 := (D.Y_pos ht i x).ne'

lemma kappa_pos : 0 < kappa D.a := lt_trans one_pos (one_lt_kappa D.ha0 D.ha1)

/-- Before the observation time the smoothing parameter is at most the bias:
`e^{-(T-t)} ≤ a` for `t ≤ T_o`. -/
lemma abs_exp_le_a {t : ℝ} (ht : t ≤ obsT) :
    |Real.exp (-(D.T - t))| ≤ D.a := by
  rw [abs_of_pos (Real.exp_pos _)]
  simp only [obsT] at ht
  have hle : D.tA ≤ D.T - t := by simp only [T, obsT]; linarith
  calc Real.exp (-(D.T - t)) ≤ Real.exp (-D.tA) := Real.exp_le_exp.mpr (by linarith)
    _ = D.a := by rw [tA, neg_neg, Real.exp_log D.ha0]

lemma le_T_of_le_obsT {t : ℝ} (ht : t ≤ obsT) : t ≤ D.T := le_trans ht D.obsT_lt_T.le

/-- Involutivity of the edge ratio, in the form needed before `Y_flipCoord`. -/
lemma Y_flipCoord_aux (t : ℝ) (i : Fin n) (x : Cube n) :
    D.Y t i (flipCoord i x) = (D.Y t i x)⁻¹ := by
  simp only [Y, flipCoord_flipCoord, inv_div]

/-- **Edge-ratio bound** [C Lemma 5 / LGF eq (4.4)]: for `t ≤ T_o`,
`κ_a⁻¹ ≤ Y_i(t,x) ≤ κ_a`. -/
lemma Y_le_kappa {t : ℝ} (ht : t ≤ obsT) (i : Fin n) (x : Cube n) :
    D.Y t i x ≤ kappa D.a := by
  have hpos := D.fs_pos (D.T_sub_nonneg (D.le_T_of_le_obsT ht)) x
  simp only [Y]
  rw [div_le_iff₀ hpos, kappa]
  simp only [fs, heatAt]
  exact smooth_flipCoord_le (D.abs_exp_le_a ht) D.ha1 (fun y => (D.hf y).le) i x

lemma kappa_inv_le_Y {t : ℝ} (ht : t ≤ obsT) (i : Fin n) (x : Cube n) :
    (kappa D.a)⁻¹ ≤ D.Y t i x := by
  have hY : 0 < D.Y t i x := D.Y_pos (D.le_T_of_le_obsT ht) i x
  have h := D.Y_le_kappa ht i (flipCoord i x)
  rw [D.Y_flipCoord_aux] at h
  have h1 : 1 ≤ D.Y t i x * kappa D.a := by
    have := mul_le_mul_of_nonneg_left h hY.le
    rwa [mul_inv_cancel₀ hY.ne'] at this
  rw [inv_eq_one_div, div_le_iff₀ D.kappa_pos]
  exact h1

@[simp] lemma Y_flipCoord (t : ℝ) (i : Fin n) (x : Cube n) :
    D.Y t i (flipCoord i x) = (D.Y t i x)⁻¹ := D.Y_flipCoord_aux t i x

/-- `F_t(σ_i x) - F_t(x) = log Y_i(t,x)`, for `t ≤ T` (where `f_{T-t} > 0`).
This is `F_flipCoord_sub` with the (necessary) time restriction; see the
STATEMENT-ISSUE note there. -/
lemma F_flipCoord_sub_of_le {t : ℝ} (ht : t ≤ D.T) (i : Fin n) (x : Cube n) :
    D.F t (flipCoord i x) - D.F t x = Real.log (D.Y t i x) := by
  simp only [F, Y]
  rw [Real.log_div (D.fs_ne_zero (D.T_sub_nonneg ht) _) (D.fs_ne_zero (D.T_sub_nonneg ht) _)]

-- STATEMENT-ISSUE: as stated (for *every* `t : ℝ`) this lemma is false; it
-- needs `t ≤ D.T`, which is exactly `F_flipCoord_sub_of_le` above (proved, and
-- used everywhere in this development).  For `t > D.T` the heat parameter
-- `ρ = e^{-(T-t)}` exceeds `1`, the multilinear extension `f_{T-t}` may vanish,
-- and both sides degenerate differently because `Real.log 0 = 0`.
-- Falsity witness: `n = 1`, `a` arbitrary, `f 1 = 1/2`, `f (-1) = 3/2`
-- (so `f > 0` and `unifE f = 1`).  At `ρ = 2`, i.e. `t = D.T + log 2`, one has
--   `f_{T-t} x = (1+2)/2·(1/2) + (1-2)/2·(3/2) = 0` at `x = (1)`, while
--   `f_{T-t} (σ x) = (1-2)/2·(1/2) + (1+2)/2·(3/2) = 2`.
-- Then LHS `= log 2 - log 0 = log 2 ≠ 0`, whereas
-- `Y = 2 / 0 = 0` so RHS `= log 0 = 0`.
/-- `F_t(σ_i x) - F_t(x) = log Y_i(t,x)`. -/
lemma F_flipCoord_sub (t : ℝ) (i : Fin n) (x : Cube n) :
    D.F t (flipCoord i x) - D.F t x = Real.log (D.Y t i x) := by
  sorry

/-! ## Heat-flow derivative identities -/

/-- Flux identity `Y_i(t,y)·f_{T-t}(y) = f_{T-t}(σ_i y)`; this is what makes
`ν_{T-t}` the exact solution of the reverse forward equation. -/
lemma Y_mul_fs {t : ℝ} (ht : t ≤ D.T) (i : Fin n) (y : Cube n) :
    D.Y t i y * D.fs (D.T - t) y = D.fs (D.T - t) (flipCoord i y) := by
  have hy : D.fs (D.T - t) y ≠ 0 := D.fs_ne_zero (D.T_sub_nonneg ht) y
  simp only [Y]
  field_simp

/-- Reverse-time heat equation: `d/dt f_{T-t}(x) = -L f_{T-t}(x)`. -/
lemma hasDerivAt_fs_sub (t : ℝ) (x : Cube n) :
    HasDerivAt (fun t => D.fs (D.T - t) x) (-(cubeLap (D.fs (D.T - t)) x)) t := by
  have h1 : HasDerivAt (fun s : ℝ => smooth (Real.exp (-s)) D.f x)
      (cubeLap (smooth (Real.exp (-(D.T - t))) D.f) x) (D.T - t) :=
    hasDerivAt_smooth_exp D.f x (D.T - t)
  have h2 : HasDerivAt (fun u : ℝ => D.T - u) (-1) t := by
    simpa using (hasDerivAt_const t D.T).sub (hasDerivAt_id t)
  have h3 := h1.comp t h2
  rw [mul_neg_one] at h3
  simpa only [fs, heatAt, Function.comp_def] using h3

/-- `L f_{T-t}(x) = f_{T-t}(x)·∑_i (Y_i - 1)/2`. -/
lemma cubeLap_fs_eq {t : ℝ} (ht : t ≤ D.T) (x : Cube n) :
    cubeLap (D.fs (D.T - t)) x = D.fs (D.T - t) x * ∑ i, (D.Y t i x - 1) / 2 := by
  have hb : D.fs (D.T - t) x ≠ 0 := D.fs_ne_zero (D.T_sub_nonneg ht) x
  simp only [cubeLap, Y, Finset.mul_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- `∂_t F_t(x) = ∑_i S_i(t,x)` [LGF eq (3.8)]. -/
lemma hasDerivAt_F {t : ℝ} (ht : t ≤ D.T) (x : Cube n) :
    HasDerivAt (fun t => D.F t x) (∑ i, D.Sc t i x) t := by
  have hb : D.fs (D.T - t) x ≠ 0 := D.fs_ne_zero (D.T_sub_nonneg ht) x
  have hsum : ∑ i, D.Sc t i x + ∑ i, (D.Y t i x - 1) / 2 = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [Sc]; ring
  have h2 : ∑ i, D.Sc t i x = -∑ i, (D.Y t i x - 1) / 2 := by linarith
  have hval : -(cubeLap (D.fs (D.T - t)) x) / D.fs (D.T - t) x = ∑ i, D.Sc t i x := by
    rw [D.cubeLap_fs_eq ht x, h2]
    field_simp
  have h := (D.hasDerivAt_fs_sub t x).log hb
  rw [hval] at h
  simpa only [F] using h

/-- Continuity in `t` of `t ↦ f_{T-t}(x)`. -/
lemma continuous_fs_sub (x : Cube n) : Continuous fun t => D.fs (D.T - t) x := by
  simp only [fs, heatAt]
  exact (continuous_smooth_exp D.f x).comp (continuous_const.sub continuous_id)

/-- Continuity of `(t,x) ↦ F_t(x)` in `t` on `(-∞, T]`. -/
lemma continuousOn_F (x : Cube n) :
    ContinuousOn (fun t => D.F t x) (Set.Iic D.T) := by
  simp only [F]
  exact (D.continuous_fs_sub x).continuousOn.log fun t ht =>
    D.fs_ne_zero (D.T_sub_nonneg (Set.mem_Iic.mp ht)) x

/-- The reciprocal `e^{-F_t(V_t)}` is space-time harmonic:
`∂_t e^{-F_t(x)} = -L̃_t(e^{-F_t(·)})(x)` [LGF, Step 2 of Prop 3.2's proof]. -/
lemma hasDerivAt_exp_neg_F {t : ℝ} (ht : t ≤ D.T) (x : Cube n) :
    HasDerivAt (fun t => Real.exp (-(D.F t x)))
      (-(D.revGen t (fun y => Real.exp (-(D.F t y))) x)) t := by
  have hflip : ∀ i : Fin n, Real.exp (-(D.F t (flipCoord i x)))
      = Real.exp (-(D.F t x)) / D.Y t i x := by
    intro i
    have h1 : D.F t (flipCoord i x) = D.F t x + Real.log (D.Y t i x) := by
      have := D.F_flipCoord_sub_of_le ht i x; linarith
    have h3 : Real.exp (-Real.log (D.Y t i x)) = (D.Y t i x)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log (D.Y_pos ht i x)]
    rw [h1, neg_add, Real.exp_add, h3, div_eq_mul_inv]
  have key : D.revGen t (fun y => Real.exp (-(D.F t y))) x
      = Real.exp (-(D.F t x)) * ∑ i, D.Sc t i x := by
    simp only [revGen, hflip, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hY := D.Y_ne_zero ht i x
    simp only [Sc]
    field_simp
  rw [key, ← mul_neg]
  exact ((D.hasDerivAt_F ht x).neg).exp

/-- The reverse forward-equation flux sum, in closed form. -/
lemma sum_revFwdMat_mul_revDensity {t : ℝ} (ht : t ≤ D.T) (x : Cube n) :
    ∑ x', D.revFwdMat t x x' * D.revDensity t x'
      = -(cubeLap (D.fs (D.T - t)) x) / 2 ^ n := by
  have hb : D.fs (D.T - t) x ≠ 0 := D.fs_ne_zero (D.T_sub_nonneg ht) x
  -- split the two contributions
  have hsplit : ∑ x' : Cube n, D.revFwdMat t x x' * D.revDensity t x'
      = (∑ x' : Cube n, ∑ i : Fin n,
          (if x = flipCoord i x' then D.Y t i x' / 2 else 0) * D.revDensity t x')
        - ∑ x' : Cube n,
            (if x = x' then ∑ i, D.Y t i x / 2 else 0) * D.revDensity t x' := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x' _ => ?_
    simp only [revFwdMat, sub_mul, Finset.sum_mul]
  -- the incoming flux from the `i`-th neighbour
  have hA : ∀ i : Fin n, ∑ x' : Cube n,
      (if x = flipCoord i x' then D.Y t i x' / 2 else 0) * D.revDensity t x'
      = D.fs (D.T - t) x / 2 / 2 ^ n := by
    intro i
    have hcond : ∀ x' : Cube n, (x = flipCoord i x') ↔ (x' = flipCoord i x) := by
      intro x'
      constructor
      · rintro rfl; rw [flipCoord_flipCoord]
      · rintro rfl; rw [flipCoord_flipCoord]
    have h2 : D.Y t i (flipCoord i x) * D.fs (D.T - t) (flipCoord i x)
        = D.fs (D.T - t) x := by
      simpa using D.Y_mul_fs ht i (flipCoord i x)
    simp only [hcond, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      revDensity]
    calc D.Y t i (flipCoord i x) / 2 * (D.fs (D.T - t) (flipCoord i x) / 2 ^ n)
        = D.Y t i (flipCoord i x) * D.fs (D.T - t) (flipCoord i x) / 2 / 2 ^ n := by ring
      _ = D.fs (D.T - t) x / 2 / 2 ^ n := by rw [h2]
  rw [hsplit, Finset.sum_comm, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hA i)]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, revDensity]
  -- closed forms for the two sums
  have hYsum : (∑ i, D.Y t i x / 2) * (D.fs (D.T - t) x / 2 ^ n)
      = (∑ i, D.fs (D.T - t) (flipCoord i x)) / 2 / 2 ^ n := by
    have h1 : ∑ i, D.fs (D.T - t) (flipCoord i x)
        = (∑ i, D.Y t i x) * D.fs (D.T - t) x := by
      rw [Finset.sum_mul]
      exact (Finset.sum_congr rfl fun i _ => D.Y_mul_fs ht i x).symm
    rw [h1, ← Finset.sum_div]
    ring
  rw [hYsum]
  simp only [cubeLap]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- The explicit density `revDensity` solves the forward (master) equation of
the reverse process: `∂_t ν_{T-t}(x) = ∑_{x'} revFwdMat t x x' ν_{T-t}(x')`
[LGF §2.2: `V_t ∼ ν_{T-t}`]. -/
lemma hasDerivAt_revDensity {t : ℝ} (ht : t ≤ D.T) (x : Cube n) :
    HasDerivAt (fun t => D.revDensity t x)
      (∑ x', D.revFwdMat t x x' * D.revDensity t x') t := by
  rw [D.sum_revFwdMat_mul_revDensity ht x]
  simp only [revDensity]
  exact (D.hasDerivAt_fs_sub t x).div_const (2 ^ n)

/-- Continuity in `t` of the rate matrix entries on `(-∞, T]`. -/
lemma continuousOn_Y (i : Fin n) (x : Cube n) :
    ContinuousOn (fun t => D.Y t i x) (Set.Iic D.T) := by
  simp only [Y]
  exact (D.continuous_fs_sub _).continuousOn.div (D.continuous_fs_sub x).continuousOn
    fun t ht => D.fs_ne_zero (D.T_sub_nonneg (Set.mem_Iic.mp ht)) x

/-! ## Terminal likelihood `H_t^ζ` [LGF §5.2] -/

/-- Terminal likelihood
`H_t^ζ(x) = f(ζ)·∏_j((1+e^{-(T-t)}x_jζ_j)/2)/f_{T-t}(x)`
(= `ℙ(V_T = ζ | V_t = x)`, Bayes formula [LGF §5.2]). -/
noncomputable def Hlik (t : ℝ) (ζ x : Cube n) : ℝ :=
  (∏ j, (1 + Real.exp (-(D.T - t)) * toR (x j) * toR (ζ j)) / 2) * D.f ζ
    / D.fs (D.T - t) x

/-- Conditioned edge coefficient
`λ_{t,i}^ζ(x) = (1 - ρ_t x_iζ_i)/(1 + ρ_t x_iζ_i)`, `ρ_t = e^{-(T-t)}`
[LGF §4.1]. -/
noncomputable def lam (t : ℝ) (i : Fin n) (x ζ : Cube n) : ℝ :=
  (1 - Real.exp (-(D.T - t)) * toR (x i) * toR (ζ i))
    / (1 + Real.exp (-(D.T - t)) * toR (x i) * toR (ζ i))

lemma Hlik_pos {t : ℝ} (ht : t < D.T) (ζ x : Cube n) : 0 < D.Hlik t ζ x := by
  sorry

lemma Hlik_nonneg {t : ℝ} (ht : t ≤ D.T) (ζ x : Cube n) : 0 ≤ D.Hlik t ζ x := by
  sorry

/-- `∑_ζ H_t^ζ(x) = 1`. -/
lemma sum_Hlik {t : ℝ} (ht : t ≤ D.T) (x : Cube n) :
    ∑ ζ, D.Hlik t ζ x = 1 := by
  sorry

/-- Ratio identity `H_t^ζ(σ_i x)/H_t^ζ(x)·Y_i(t,x) = λ_{t,i}^ζ(x)`
[LGF eq (4.5)]. -/
lemma Hlik_flipCoord_mul_Y {t : ℝ} (ht : t < D.T) (i : Fin n) (ζ x : Cube n) :
    D.Hlik t ζ (flipCoord i x) / D.Hlik t ζ x * D.Y t i x = D.lam t i x ζ := by
  sorry

/-- `κ_a⁻¹ ≤ λ_{t,i}^ζ(x) ≤ κ_a` for `t ≤ T_o` [LGF eq (4.5)]. -/
lemma lam_le_kappa {t : ℝ} (ht : t ≤ obsT) (i : Fin n) (x ζ : Cube n) :
    D.lam t i x ζ ≤ kappa D.a := by
  sorry

lemma kappa_inv_le_lam {t : ℝ} (ht : t ≤ obsT) (i : Fin n) (x ζ : Cube n) :
    (kappa D.a)⁻¹ ≤ D.lam t i x ζ := by
  sorry

lemma lam_pos {t : ℝ} (ht : t ≤ obsT) (i : Fin n) (x ζ : Cube n) :
    0 < D.lam t i x ζ := by
  sorry

/-- Space-time harmonicity of the terminal likelihood:
`∂_t H_t^ζ(x) = -L̃_t(H_t^ζ)(x)` [LGF §4.1 / Lemma 5.1]. -/
lemma hasDerivAt_Hlik {t : ℝ} (ht : t < D.T) (ζ x : Cube n) :
    HasDerivAt (fun t => D.Hlik t ζ x)
      (-(D.revGen t (fun y => D.Hlik t ζ y) x)) t := by
  sorry

end Dat

end Talagrand
