import TalagrandConvConjecture.Cube.Multilinear

/-!
# Heat smoothing on the cube

`smooth ρ f x = mext f (ρ·x)` is convolution of `f` with the biased product
measure `μ_ρ`; `P_t = smooth (e^{-t})` is the Boolean heat semigroup
[LGF §2.1, C §2.3]. This file proves the semigroup law, mass conservation,
positivity, the heat equation (time derivative = discrete Laplacian), and the
edge-ratio bound [C Lemma 5].
-/

namespace Talagrand

variable {n : ℕ}

/-- Smoothing at correlation `ρ`: `T_ρ f(x) = f(ρ x)` via the multilinear
extension; equals convolution by the biased measure `μ_ρ` (see
`smooth_eq_conv`). -/
noncomputable def smooth (ρ : ℝ) (f : Cube n → ℝ) : Cube n → ℝ :=
  fun x => mext f (fun i => ρ * toR (x i))

/-- Weight of the biased product measure `μ_ρ({y}) = ∏ (1+ρ·y_i)/2`
[LGF §1]. -/
noncomputable def biasedWeight (ρ : ℝ) (y : Cube n) : ℝ :=
  ∏ i, (1 + ρ * toR (y i)) / 2

/-- Discrete Laplacian (generator of the heat semigroup):
`L f(x) = ½ ∑_i (f(σ_i x) - f x)` [C eq (heat_semigroup_generator)]. -/
noncomputable def cubeLap (f : Cube n → ℝ) : Cube n → ℝ :=
  fun x => (∑ i, (f (flipCoord i x) - f x)) / 2

/-- `smooth` is convolution by the biased measure:
`T_ρ f(x) = ∑_y μ_ρ({y}) f(x⊙y)` [LGF §1]. -/
lemma smooth_eq_conv (ρ : ℝ) (f : Cube n → ℝ) (x : Cube n) :
    smooth ρ f x = ∑ y, biasedWeight ρ y * f (x * y) := by
  sorry

@[simp] lemma smooth_one (f : Cube n → ℝ) : smooth 1 f = f := by
  sorry

/-- Semigroup / multiplicativity law: `T_ρ T_{ρ'} = T_{ρρ'}`. -/
lemma smooth_smooth (ρ ρ' : ℝ) (f : Cube n → ℝ) :
    smooth ρ (smooth ρ' f) = smooth (ρ * ρ') f := by
  sorry

/-- Mass conservation: `𝔼_λ (T_ρ f) = 𝔼_λ f`. -/
lemma unifE_smooth (ρ : ℝ) (f : Cube n → ℝ) : unifE (smooth ρ f) = unifE f := by
  sorry

lemma smooth_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : Cube n → ℝ}
    (hf : ∀ x, 0 ≤ f x) (x : Cube n) : 0 ≤ smooth ρ f x := by
  refine mext_nonneg (fun i => ?_) hf
  rw [abs_mul, abs_toR, mul_one]
  exact hρ

lemma smooth_pos {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : Cube n → ℝ}
    (hf : ∀ x, 0 < f x) (x : Cube n) : 0 < smooth ρ f x := by
  sorry

/-- Heat equation: `d/dt P_t f(x) = L(P_t f)(x)` at `ρ = e^{-t}`
[C eq (heat_semigroup)]. -/
lemma hasDerivAt_smooth_exp (f : Cube n → ℝ) (x : Cube n) (t : ℝ) :
    HasDerivAt (fun s => smooth (Real.exp (-s)) f x)
      (cubeLap (smooth (Real.exp (-t)) f) x) t := by
  sorry

/-- Continuity of `t ↦ P_t f (x)`. -/
lemma continuous_smooth_exp (f : Cube n → ℝ) (x : Cube n) :
    Continuous fun s => smooth (Real.exp (-s)) f x := by
  sorry

/-- **Edge-ratio bound** [C Lemma 5]: for `f ≥ 0` not identically zero and
`|ρ| ≤ a' < 1`, adjacent values of `T_ρ f` differ by a factor at most
`(1+a')/(1-a')`. Stated for strictly positive `f` (the use case in [LGF]). -/
lemma smooth_flipCoord_le {ρ a' : ℝ} (hρ : |ρ| ≤ a') (ha' : a' < 1)
    {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) (i : Fin n) (x : Cube n) :
    smooth ρ f (flipCoord i x) ≤ (1 + a') / (1 - a') * smooth ρ f x := by
  sorry

/-- The smoothed function is expressible with the kernel centered at `x`:
`T_ρ f(x) = ∑_z ∏_j ((1+ρ x_j z_j)/2) f z`. Convenient form for ratio
estimates and for the terminal likelihood `H_t^ζ` [LGF §5.2]. -/
lemma smooth_eq_kernel_sum (ρ : ℝ) (f : Cube n → ℝ) (x : Cube n) :
    smooth ρ f x = ∑ z, (∏ j, (1 + ρ * toR (x j) * toR (z j)) / 2) * f z := by
  sorry

/-- `f_s = P_s f`, the heat flow at time `s` [LGF §2.1]. -/
noncomputable def heatAt (f : Cube n → ℝ) (s : ℝ) : Cube n → ℝ :=
  smooth (Real.exp (-s)) f

end Talagrand
