import TalagrandConvConjecture.Cube.Basic

/-!
# Multilinear (harmonic) extension of functions on the cube

For `f : Cube n → ℝ` the multilinear extension is
`mext f z = ∑_y ∏_i ((1 + z i·y i)/2) · f y`, `z ∈ ℝ^n`; it agrees with `f` on
`{-1,1}^n` and is affine in each coordinate. `dmext f i` is the `i`-th partial
derivative (a constant in `z i`). This is the standard biased-expectation view
of the extension [C §2.1, O'Donnell Ch. 8]; the heat semigroup and the Boolean
bridge of [LGF] are built from it.
-/

namespace Talagrand

variable {n : ℕ}

/-- Product kernel `∏_i (1 + z i · y i)/2`: the density of the biased product
measure with mean vector `z` at the cube point `y`. -/
noncomputable def cubeKernel (z : Fin n → ℝ) (y : Cube n) : ℝ :=
  ∏ i, (1 + z i * toR (y i)) / 2

/-- Multilinear extension of `f` evaluated at `z ∈ ℝ^n`; equivalently the
expectation of `f` under the product measure with coordinate means `z`. -/
noncomputable def mext (f : Cube n → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ y, cubeKernel z y * f y

/-- `i`-th partial derivative of the multilinear extension (does not depend on
`z i`). -/
noncomputable def dmext (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ) : ℝ :=
  ∑ y, (toR (y i) * (∏ j ∈ Finset.univ.erase i, (1 + z j * toR (y j)) / 2) / 2)
    * f y

lemma cubeKernel_nonneg {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1) (y : Cube n) :
    0 ≤ cubeKernel z y := by
  refine Finset.prod_nonneg fun i _ => ?_
  have := one_add_mul_toR_nonneg (hz i) (y i)
  linarith

lemma cubeKernel_pos {z : Fin n → ℝ} (hz : ∀ i, |z i| < 1) (y : Cube n) :
    0 < cubeKernel z y := by
  refine Finset.prod_pos fun i _ => ?_
  have := one_add_mul_toR_pos (hz i) (y i)
  linarith

/-- The kernel is a probability density: `∑_y cubeKernel z y = 1`. -/
lemma sum_cubeKernel (z : Fin n → ℝ) : ∑ y : Cube n, cubeKernel z y = 1 := by
  sorry

/-- Interpolation: the extension agrees with `f` at cube points. -/
@[simp] lemma mext_toR (f : Cube n → ℝ) (x : Cube n) :
    mext f (fun i => toR (x i)) = f x := by
  sorry

/-- `mext f` is affine in the `i`-th coordinate with slope `dmext f i z`. -/
lemma mext_update (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ) (s : ℝ) :
    mext f (Function.update z i s)
      = mext f (Function.update z i 0) + s * dmext f i z := by
  sorry

/-- The slope does not depend on the `i`-th coordinate of the base point. -/
lemma dmext_update (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ) (s : ℝ) :
    dmext f i (Function.update z i s) = dmext f i z := by
  sorry

/-- Negating the `i`-th coordinate: the discrete difference formula
`mext f (z with -z i) = mext f z - 2·z i·dmext f i z`. This is the identity
behind [LGF eq (5.2)-(5.3)] (bridge differences). -/
lemma mext_update_neg (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ) :
    mext f (Function.update z i (-(z i))) = mext f z - 2 * z i * dmext f i z := by
  sorry

/-- Derivative of the extension in one coordinate. -/
lemma hasDerivAt_mext_update (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ)
    (s : ℝ) :
    HasDerivAt (fun t => mext f (Function.update z i t)) (dmext f i z) s := by
  sorry

/-- Chain rule along a differentiable curve `z : ℝ → ℝ^n`:
`d/dt mext f (z t) = ∑_i dmext f i (z t) · (z i)'(t)`. -/
lemma hasDerivAt_mext_comp (f : Cube n → ℝ) (z : ℝ → Fin n → ℝ)
    (z' : Fin n → ℝ) (t : ℝ) (hz : ∀ i, HasDerivAt (fun t => z t i) (z' i) t) :
    HasDerivAt (fun t => mext f (z t)) (∑ i, dmext f i (z t) * z' i) t := by
  sorry

/-- Master composition identity: extending the `ρ`-smoothed function and then
evaluating at `z` is the same as extending `f` at `ρ • z`. Specializes to the
semigroup law of the heat flow and to `P_t f(x) = f(e^{-t}x)`
[C eq (explicit_heat_semigroup)]. -/
lemma mext_smooth_eq (f : Cube n → ℝ) (ρ : ℝ) (z : Fin n → ℝ) :
    mext (fun x => mext f (fun i => ρ * toR (x i))) z
      = mext f (fun i => ρ * z i) := by
  sorry

/-- Monotonicity in `f`. -/
lemma mext_mono {f g : Cube n → ℝ} {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1)
    (h : ∀ x, f x ≤ g x) :
    mext f z ≤ mext g z := by
  sorry

lemma mext_nonneg {f : Cube n → ℝ} {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mext f z := by
  sorry

/-- Strict positivity of the extension of a strictly positive function on the
closed solid cube. -/
lemma mext_pos {f : Cube n → ℝ} {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1)
    (hf : ∀ x, 0 < f x) : 0 < mext f z := by
  sorry

/-- Values of the extension of a `[0,1]`-valued function stay in `[0,1]` on the
solid cube [C Lemma 5, last part]. -/
lemma mext_mem_Icc {f : Cube n → ℝ} {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : mext f z ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- Pointwise kernel-ratio bound ⇒ ratio bound for the extension (mediant
inequality): if `f ≥ 0` and `g ≤ c·h` pointwise with `h, g ≥ 0` then sums obey
the same bound. Used to derive the edge-ratio bound [C Lemma 5]. -/
lemma sum_div_le_of_ratio_le {ι : Type*} [Fintype ι] {g h : ι → ℝ} {c : ℝ}
    (hh : ∀ i, 0 ≤ h i) (hb : ∀ i, g i ≤ c * h i) :
    ∑ i, g i ≤ c * ∑ i, h i := by
  sorry

end Talagrand
