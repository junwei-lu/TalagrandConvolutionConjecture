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

/-- The biased weight is the kernel of the constant mean vector `ρ`. -/
lemma biasedWeight_eq_cubeKernel (ρ : ℝ) (y : Cube n) :
    biasedWeight ρ y = cubeKernel (fun _ => ρ) y := rfl

/-- The biased measure is a probability measure: `∑_y μ_ρ({y}) = 1`. -/
lemma sum_biasedWeight (ρ : ℝ) : ∑ y : Cube n, biasedWeight ρ y = 1 := by
  simp only [biasedWeight_eq_cubeKernel]
  exact sum_cubeKernel _

/-- `smooth` is convolution by the biased measure:
`T_ρ f(x) = ∑_y μ_ρ({y}) f(x⊙y)` [LGF §1]. -/
lemma smooth_eq_conv (ρ : ℝ) (f : Cube n → ℝ) (x : Cube n) :
    smooth ρ f x = ∑ y, biasedWeight ρ y * f (x * y) := by
  have key : ∀ y : Cube n,
      cubeKernel (fun i => ρ * toR (x i)) (y * x) * f (y * x)
        = biasedWeight ρ y * f (x * y) := by
    intro y
    rw [mul_comm y x]
    congr 1
    simp only [cubeKernel, biasedWeight]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hxy : toR ((x * y) i) = toR (x i) * toR (y i) := toR_mul (x i) (y i)
    rw [hxy]
    have hr : ρ * toR (x i) * (toR (x i) * toR (y i))
        = ρ * toR (y i) * (toR (x i) * toR (x i)) := by ring
    rw [hr, toR_mul_self, mul_one]
  calc smooth ρ f x
      = ∑ z : Cube n, cubeKernel (fun i => ρ * toR (x i)) z * f z := rfl
    _ = ∑ y : Cube n, cubeKernel (fun i => ρ * toR (x i)) (y * x) * f (y * x) :=
        (sum_comp_mul_right x _).symm
    _ = ∑ y : Cube n, biasedWeight ρ y * f (x * y) :=
        Finset.sum_congr rfl fun y _ => key y

@[simp] lemma smooth_one (f : Cube n → ℝ) : smooth 1 f = f := by
  funext x
  show mext f (fun i => 1 * toR (x i)) = f x
  simp only [one_mul]
  exact mext_toR f x

/-- Semigroup / multiplicativity law: `T_ρ T_{ρ'} = T_{ρρ'}`. -/
lemma smooth_smooth (ρ ρ' : ℝ) (f : Cube n → ℝ) :
    smooth ρ (smooth ρ' f) = smooth (ρ * ρ') f := by
  funext x
  show mext (fun w => mext f (fun i => ρ' * toR (w i))) (fun i => ρ * toR (x i))
      = mext f (fun i => ρ * ρ' * toR (x i))
  rw [mext_smooth_eq f ρ' (fun i => ρ * toR (x i))]
  congr 1
  funext i
  ring

/-- Mass conservation: `𝔼_λ (T_ρ f) = 𝔼_λ f`. -/
lemma unifE_smooth (ρ : ℝ) (f : Cube n → ℝ) : unifE (smooth ρ f) = unifE f := by
  unfold unifE
  congr 1
  calc ∑ x : Cube n, smooth ρ f x
      = ∑ x : Cube n, ∑ y : Cube n, biasedWeight ρ y * f (x * y) :=
        Finset.sum_congr rfl fun x _ => smooth_eq_conv ρ f x
    _ = ∑ y : Cube n, ∑ x : Cube n, biasedWeight ρ y * f (x * y) :=
        Finset.sum_comm
    _ = ∑ y : Cube n, biasedWeight ρ y * ∑ x : Cube n, f x := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.mul_sum, sum_comp_mul_right y f]
    _ = (∑ y : Cube n, biasedWeight ρ y) * ∑ x : Cube n, f x := by
        rw [Finset.sum_mul]
    _ = ∑ x : Cube n, f x := by rw [sum_biasedWeight, one_mul]

lemma smooth_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : Cube n → ℝ}
    (hf : ∀ x, 0 ≤ f x) (x : Cube n) : 0 ≤ smooth ρ f x := by
  refine mext_nonneg (fun i => ?_) hf
  rw [abs_mul, abs_toR, mul_one]
  exact hρ

lemma smooth_pos {ρ : ℝ} (hρ : |ρ| ≤ 1) {f : Cube n → ℝ}
    (hf : ∀ x, 0 < f x) (x : Cube n) : 0 < smooth ρ f x := by
  refine mext_pos (fun i => ?_) hf
  rw [abs_mul, abs_toR, mul_one]
  exact hρ

/-- Flipping a coordinate is a discrete difference of the extension: this is the
identity behind the heat equation. -/
lemma smooth_flipCoord_eq (ρ : ℝ) (f : Cube n → ℝ) (i : Fin n) (x : Cube n) :
    smooth ρ f (flipCoord i x)
      = smooth ρ f x
        - 2 * (ρ * toR (x i)) * dmext f i (fun j => ρ * toR (x j)) := by
  have h : (fun j => ρ * toR (flipCoord i x j))
      = Function.update (fun j => ρ * toR (x j)) i (-(ρ * toR (x i))) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [flipCoord_ne hj, Function.update_of_ne hj]
  show mext f (fun j => ρ * toR (flipCoord i x j)) = _
  rw [h]
  exact mext_update_neg f i (fun j => ρ * toR (x j))

/-- The discrete Laplacian of `T_ρ f` in terms of the partial derivatives of the
multilinear extension. -/
lemma cubeLap_smooth (ρ : ℝ) (f : Cube n → ℝ) (x : Cube n) :
    cubeLap (smooth ρ f) x
      = ∑ i, dmext f i (fun j => ρ * toR (x j)) * -(ρ * toR (x i)) := by
  have hterm : ∀ i : Fin n, smooth ρ f (flipCoord i x) - smooth ρ f x
      = 2 * (dmext f i (fun j => ρ * toR (x j)) * -(ρ * toR (x i))) := by
    intro i
    rw [smooth_flipCoord_eq]
    ring
  simp only [cubeLap, hterm]
  rw [← Finset.mul_sum]
  ring

/-- Heat equation: `d/dt P_t f(x) = L(P_t f)(x)` at `ρ = e^{-t}`
[C eq (heat_semigroup)]. -/
lemma hasDerivAt_smooth_exp (f : Cube n → ℝ) (x : Cube n) (t : ℝ) :
    HasDerivAt (fun s => smooth (Real.exp (-s)) f x)
      (cubeLap (smooth (Real.exp (-t)) f) x) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg' t)
  have hz : ∀ i : Fin n,
      HasDerivAt (fun s => Real.exp (-s) * toR (x i))
        (-(Real.exp (-t) * toR (x i))) t := by
    intro i
    simpa [neg_mul] using hexp.mul_const (toR (x i))
  have hcomp := hasDerivAt_mext_comp f (fun s i => Real.exp (-s) * toR (x i))
    (fun i => -(Real.exp (-t) * toR (x i))) t hz
  rw [cubeLap_smooth]
  exact hcomp

/-- Continuity of `t ↦ P_t f (x)`. -/
lemma continuous_smooth_exp (f : Cube n → ℝ) (x : Cube n) :
    Continuous fun s => smooth (Real.exp (-s)) f x :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_smooth_exp f x t).continuousAt

/-- **Edge-ratio bound** [C Lemma 5]: for `f ≥ 0` not identically zero and
`|ρ| ≤ a' < 1`, adjacent values of `T_ρ f` differ by a factor at most
`(1+a')/(1-a')`. Stated for strictly positive `f` (the use case in [LGF]). -/
lemma smooth_flipCoord_le {ρ a' : ℝ} (hρ : |ρ| ≤ a') (ha' : a' < 1)
    {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) (i : Fin n) (x : Cube n) :
    smooth ρ f (flipCoord i x) ≤ (1 + a') / (1 - a') * smooth ρ f x := by
  have ha0 : 0 ≤ a' := le_trans (abs_nonneg ρ) hρ
  have h1a : (0 : ℝ) < 1 - a' := by linarith
  have hb : ∀ (w z : Cube n) (j : Fin n), |ρ * toR (w j) * toR (z j)| ≤ a' := by
    intro w z j
    rw [abs_mul, abs_mul, abs_toR, abs_toR, mul_one, mul_one]
    exact hρ
  have hfac : ∀ (w z : Cube n) (j : Fin n),
      0 ≤ (1 + ρ * toR (w j) * toR (z j)) / 2 := by
    intro w z j
    have := (abs_le.1 (hb w z j)).1
    linarith
  show (∑ z : Cube n, (∏ j, (1 + ρ * toR (flipCoord i x j) * toR (z j)) / 2) * f z)
      ≤ (1 + a') / (1 - a')
        * ∑ z : Cube n, (∏ j, (1 + ρ * toR (x j) * toR (z j)) / 2) * f z
  refine sum_div_le_of_ratio_le
    (fun z => mul_nonneg (Finset.prod_nonneg fun j _ => hfac x z j) (hf z))
    (fun z => ?_)
  have hsplit : ∀ w : Cube n, (∏ j, (1 + ρ * toR (w j) * toR (z j)) / 2)
      = (1 + ρ * toR (w i) * toR (z i)) / 2
        * ∏ j ∈ Finset.univ.erase i, (1 + ρ * toR (w j) * toR (z j)) / 2 :=
    fun w => (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
  have hP : (∏ j ∈ Finset.univ.erase i,
        (1 + ρ * toR (flipCoord i x j) * toR (z j)) / 2)
      = ∏ j ∈ Finset.univ.erase i, (1 + ρ * toR (x j) * toR (z j)) / 2 :=
    Finset.prod_congr rfl fun j hj => by
      rw [flipCoord_ne (Finset.ne_of_mem_erase hj)]
  have hPnn : 0 ≤ ∏ j ∈ Finset.univ.erase i, (1 + ρ * toR (x j) * toR (z j)) / 2 :=
    Finset.prod_nonneg fun j _ => hfac x z j
  have hPf : 0 ≤ (∏ j ∈ Finset.univ.erase i,
      (1 + ρ * toR (x j) * toR (z j)) / 2) * f z := mul_nonneg hPnn (hf z)
  rw [hsplit (flipCoord i x), hsplit x, hP, flipCoord_self, toR_neg]
  have hlb : -a' ≤ ρ * toR (x i) * toR (z i) := (abs_le.1 (hb x z i)).1
  have hkey : 1 - ρ * toR (x i) * toR (z i)
      ≤ (1 + a') / (1 - a') * (1 + ρ * toR (x i) * toR (z i)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1a]
    nlinarith [hlb]
  have hmul := mul_le_mul_of_nonneg_right hkey hPf
  have hneg : 1 + ρ * -toR (x i) * toR (z i) = 1 - ρ * toR (x i) * toR (z i) := by
    ring
  rw [hneg]
  linarith [hmul]

/-- The smoothed function is expressible with the kernel centered at `x`:
`T_ρ f(x) = ∑_z ∏_j ((1+ρ x_j z_j)/2) f z`. Convenient form for ratio
estimates and for the terminal likelihood `H_t^ζ` [LGF §5.2]. -/
lemma smooth_eq_kernel_sum (ρ : ℝ) (f : Cube n → ℝ) (x : Cube n) :
    smooth ρ f x = ∑ z, (∏ j, (1 + ρ * toR (x j) * toR (z j)) / 2) * f z := rfl

/-- `f_s = P_s f`, the heat flow at time `s` [LGF §2.1]. -/
noncomputable def heatAt (f : Cube n → ℝ) (s : ℝ) : Cube n → ℝ :=
  smooth (Real.exp (-s)) f

end Talagrand
