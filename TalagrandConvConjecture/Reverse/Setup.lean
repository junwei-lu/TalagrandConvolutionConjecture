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

lemma fs_pos {s : ℝ} (hs : 0 ≤ s) (x : Cube n) : 0 < D.fs s x := by
  sorry

lemma fs_zero (x : Cube n) : D.fs 0 x = D.f x := by
  sorry

/-- Mass conservation along the heat flow. -/
lemma unifE_fs (s : ℝ) : unifE (D.fs s) = 1 := by
  sorry

lemma Y_pos {t : ℝ} (ht : t ≤ D.T) (i : Fin n) (x : Cube n) :
    0 < D.Y t i x := by
  sorry

/-- **Edge-ratio bound** [C Lemma 5 / LGF eq (4.4)]: for `t ≤ T_o`,
`κ_a⁻¹ ≤ Y_i(t,x) ≤ κ_a`. -/
lemma Y_le_kappa {t : ℝ} (ht : t ≤ obsT) (i : Fin n) (x : Cube n) :
    D.Y t i x ≤ kappa D.a := by
  sorry

lemma kappa_inv_le_Y {t : ℝ} (ht : t ≤ obsT) (i : Fin n) (x : Cube n) :
    (kappa D.a)⁻¹ ≤ D.Y t i x := by
  sorry

@[simp] lemma Y_flipCoord (t : ℝ) (i : Fin n) (x : Cube n) :
    D.Y t i (flipCoord i x) = (D.Y t i x)⁻¹ := by
  sorry

/-- `F_t(σ_i x) - F_t(x) = log Y_i(t,x)`. -/
lemma F_flipCoord_sub (t : ℝ) (i : Fin n) (x : Cube n) :
    D.F t (flipCoord i x) - D.F t x = Real.log (D.Y t i x) := by
  sorry

/-! ## Heat-flow derivative identities -/

/-- `∂_t F_t(x) = ∑_i S_i(t,x)` [LGF eq (3.8)]. -/
lemma hasDerivAt_F {t : ℝ} (ht : t ≤ D.T) (x : Cube n) :
    HasDerivAt (fun t => D.F t x) (∑ i, D.Sc t i x) t := by
  sorry

/-- Continuity of `(t,x) ↦ F_t(x)` in `t` on `(-∞, T]`. -/
lemma continuousOn_F (x : Cube n) :
    ContinuousOn (fun t => D.F t x) (Set.Iic D.T) := by
  sorry

/-- The reciprocal `e^{-F_t(V_t)}` is space-time harmonic:
`∂_t e^{-F_t(x)} = -L̃_t(e^{-F_t(·)})(x)` [LGF, Step 2 of Prop 3.2's proof]. -/
lemma hasDerivAt_exp_neg_F {t : ℝ} (ht : t ≤ D.T) (x : Cube n) :
    HasDerivAt (fun t => Real.exp (-(D.F t x)))
      (-(D.revGen t (fun y => Real.exp (-(D.F t y))) x)) t := by
  sorry

/-- The explicit density `revDensity` solves the forward (master) equation of
the reverse process: `∂_t ν_{T-t}(x) = ∑_{x'} revFwdMat t x x' ν_{T-t}(x')`
[LGF §2.2: `V_t ∼ ν_{T-t}`]. -/
lemma hasDerivAt_revDensity {t : ℝ} (ht : t ≤ D.T) (x : Cube n) :
    HasDerivAt (fun t => D.revDensity t x)
      (∑ x', D.revFwdMat t x x' * D.revDensity t x') t := by
  sorry

/-- Continuity in `t` of the rate matrix entries on `(-∞, T]`. -/
lemma continuousOn_Y (i : Fin n) (x : Cube n) :
    ContinuousOn (fun t => D.Y t i x) (Set.Iic D.T) := by
  sorry

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
