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

/-- A product of per-coordinate sums over `ℤˣ` is a sum over the cube of
products. (Restatement of `Fintype.prod_sum` for `Cube n`.) -/
lemma sum_cube_prod (F : Fin n → ℤˣ → ℝ) :
    ∑ x : Cube n, ∏ i, F i (x i) = ∏ i, ∑ u : ℤˣ, F i u :=
  (Fintype.prod_sum F).symm

/-- The kernel is a probability density: `∑_y cubeKernel z y = 1`. -/
lemma sum_cubeKernel (z : Fin n → ℝ) : ∑ y : Cube n, cubeKernel z y = 1 := by
  have h : ∑ y : Cube n, cubeKernel z y
      = ∏ i, ∑ u : ℤˣ, (1 + z i * toR u) / 2 :=
    sum_cube_prod (fun i u => (1 + z i * toR u) / 2)
  rw [h]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [sum_units_int]
  simp only [toR_one, toR_neg_one]
  ring

/-- Interpolation: the extension agrees with `f` at cube points. -/
@[simp] lemma mext_toR (f : Cube n → ℝ) (x : Cube n) :
    mext f (fun i => toR (x i)) = f x := by
  have hx : cubeKernel (fun i => toR (x i)) x = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    show (1 + toR (x i) * toR (x i)) / 2 = 1
    rw [toR_mul_self]; norm_num
  have hne : ∀ y : Cube n, y ≠ x → cubeKernel (fun i => toR (x i)) y = 0 := by
    intro y hy
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ x j := by
      by_contra hcon
      exact hy (funext fun j => not_not.1 fun hne => hcon ⟨j, hne⟩)
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    show (1 + toR (x j) * toR (y j)) / 2 = 0
    rw [toR_mul_of_ne (Ne.symm hj)]
    norm_num
  rw [mext, Finset.sum_eq_single x (fun y _ hy => by rw [hne y hy, zero_mul])
    (fun h => absurd (Finset.mem_univ x) h), hx, one_mul]

/-- Split the kernel product at the `i`-th coordinate. -/
lemma mext_eq_split (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ) :
    mext f z = ∑ y : Cube n,
      ((1 + z i * toR (y i)) / 2
        * ∏ j ∈ Finset.univ.erase i, (1 + z j * toR (y j)) / 2) * f y := by
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [cubeKernel, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]

/-- `mext f` is affine in the `i`-th coordinate with slope `dmext f i z`. -/
lemma mext_update (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ) (s : ℝ) :
    mext f (Function.update z i s)
      = mext f (Function.update z i 0) + s * dmext f i z := by
  have hQ : ∀ (t : ℝ) (y : Cube n),
      (∏ j ∈ Finset.univ.erase i, (1 + Function.update z i t j * toR (y j)) / 2)
        = ∏ j ∈ Finset.univ.erase i, (1 + z j * toR (y j)) / 2 := fun t y =>
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [mext_eq_split f i (Function.update z i s),
    mext_eq_split f i (Function.update z i 0), dmext, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hQ s y, hQ 0 y, Function.update_self, Function.update_self]
  ring

/-- The slope does not depend on the `i`-th coordinate of the base point. -/
lemma dmext_update (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ) (s : ℝ) :
    dmext f i (Function.update z i s) = dmext f i z := by
  have hQ : ∀ y : Cube n,
      (∏ j ∈ Finset.univ.erase i, (1 + Function.update z i s j * toR (y j)) / 2)
        = ∏ j ∈ Finset.univ.erase i, (1 + z j * toR (y j)) / 2 := fun y =>
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  simp only [dmext, hQ]

/-- Negating the `i`-th coordinate: the discrete difference formula
`mext f (z with -z i) = mext f z - 2·z i·dmext f i z`. This is the identity
behind [LGF eq (5.2)-(5.3)] (bridge differences). -/
lemma mext_update_neg (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ) :
    mext f (Function.update z i (-(z i))) = mext f z - 2 * z i * dmext f i z := by
  have h1 := mext_update f i z (-(z i))
  have h2 := mext_update f i z (z i)
  rw [Function.update_eq_self] at h2
  rw [h1, h2]
  ring

/-- Derivative of the extension in one coordinate. -/
lemma hasDerivAt_mext_update (f : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ)
    (s : ℝ) :
    HasDerivAt (fun t => mext f (Function.update z i t)) (dmext f i z) s := by
  have hfun : (fun t => mext f (Function.update z i t))
      = fun t => mext f (Function.update z i 0) + t * dmext f i z :=
    funext fun t => mext_update f i z t
  rw [hfun]
  simpa using ((hasDerivAt_id s).mul_const (dmext f i z)).const_add
    (mext f (Function.update z i 0))

/-- Chain rule along a differentiable curve `z : ℝ → ℝ^n`:
`d/dt mext f (z t) = ∑_i dmext f i (z t) · (z i)'(t)`. -/
lemma hasDerivAt_mext_comp (f : Cube n → ℝ) (z : ℝ → Fin n → ℝ)
    (z' : Fin n → ℝ) (t : ℝ) (hz : ∀ i, HasDerivAt (fun t => z t i) (z' i) t) :
    HasDerivAt (fun t => mext f (z t)) (∑ i, dmext f i (z t) * z' i) t := by
  set D : Cube n → ℝ := fun y =>
    ∑ i, (∏ j ∈ Finset.univ.erase i, (1 + z t j * toR (y j)) / 2)
      * (z' i * toR (y i) / 2) with hD
  have hy : ∀ y : Cube n,
      HasDerivAt (fun s => cubeKernel (z s) y * f y) (D y * f y) t := by
    intro y
    have h0 : HasDerivAt (fun s => ∏ i, (1 + z s i * toR (y i)) / 2)
        (∑ i, (∏ j ∈ Finset.univ.erase i, (1 + z t j * toR (y j)) / 2)
          • (z' i * toR (y i) / 2)) t :=
      HasDerivAt.fun_finset_prod (u := (Finset.univ : Finset (Fin n)))
        (f := fun i s => (1 + z s i * toR (y i)) / 2)
        (f' := fun i => z' i * toR (y i) / 2) (x := t)
        (fun i _ => (((hz i).mul_const (toR (y i))).const_add 1).div_const 2)
    have h1 : HasDerivAt (fun s => cubeKernel (z s) y) (D y) t := by
      simpa [cubeKernel, hD, smul_eq_mul] using h0
    exact h1.mul_const (f y)
  have hsum : HasDerivAt (fun s => ∑ y : Cube n, cubeKernel (z s) y * f y)
      (∑ y : Cube n, D y * f y) t := HasDerivAt.fun_sum (fun y _ => hy y)
  have hEq : (∑ y : Cube n, D y * f y) = ∑ i, dmext f i (z t) * z' i := by
    calc ∑ y : Cube n, D y * f y
        = ∑ y : Cube n, ∑ i,
            (toR (y i) * (∏ j ∈ Finset.univ.erase i, (1 + z t j * toR (y j)) / 2)
              / 2 * f y) * z' i := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hD, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ y : Cube n,
            (toR (y i) * (∏ j ∈ Finset.univ.erase i, (1 + z t j * toR (y j)) / 2)
              / 2 * f y) * z' i := Finset.sum_comm
      _ = ∑ i, dmext f i (z t) * z' i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_mul]
          rfl
  rw [← hEq]
  exact hsum

/-- Master composition identity: extending the `ρ`-smoothed function and then
evaluating at `z` is the same as extending `f` at `ρ • z`. Specializes to the
semigroup law of the heat flow and to `P_t f(x) = f(e^{-t}x)`
[C eq (explicit_heat_semigroup)]. -/
lemma mext_smooth_eq (f : Cube n → ℝ) (ρ : ℝ) (z : Fin n → ℝ) :
    mext (fun x => mext f (fun i => ρ * toR (x i))) z
      = mext f (fun i => ρ * z i) := by
  have step : ∀ y : Cube n,
      (∑ x : Cube n, cubeKernel z x * cubeKernel (fun i => ρ * toR (x i)) y)
        = cubeKernel (fun i => ρ * z i) y := by
    intro y
    simp only [cubeKernel]
    calc ∑ x : Cube n, (∏ i, (1 + z i * toR (x i)) / 2)
            * ∏ i, (1 + ρ * toR (x i) * toR (y i)) / 2
        = ∑ x : Cube n, ∏ i,
            ((1 + z i * toR (x i)) / 2 * ((1 + ρ * toR (x i) * toR (y i)) / 2)) :=
          Finset.sum_congr rfl fun x _ => (Finset.prod_mul_distrib).symm
      _ = ∏ i, ∑ u : ℤˣ,
            ((1 + z i * toR u) / 2 * ((1 + ρ * toR u * toR (y i)) / 2)) :=
          sum_cube_prod
            (fun i u => (1 + z i * toR u) / 2 * ((1 + ρ * toR u * toR (y i)) / 2))
      _ = ∏ i, (1 + ρ * z i * toR (y i)) / 2 := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [sum_units_int]
          simp only [toR_one, toR_neg_one]
          ring
  simp only [mext]
  calc ∑ x : Cube n, cubeKernel z x
          * ∑ y : Cube n, cubeKernel (fun i => ρ * toR (x i)) y * f y
      = ∑ x : Cube n, ∑ y : Cube n,
          cubeKernel z x * cubeKernel (fun i => ρ * toR (x i)) y * f y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => (mul_assoc _ _ _).symm
    _ = ∑ y : Cube n, ∑ x : Cube n,
          cubeKernel z x * cubeKernel (fun i => ρ * toR (x i)) y * f y :=
        Finset.sum_comm
    _ = ∑ y : Cube n, cubeKernel (fun i => ρ * z i) y * f y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, step y]

/-- Monotonicity in `f`. -/
lemma mext_mono {f g : Cube n → ℝ} {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1)
    (h : ∀ x, f x ≤ g x) :
    mext f z ≤ mext g z :=
  Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (h y) (cubeKernel_nonneg hz y)

lemma mext_nonneg {f : Cube n → ℝ} {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mext f z :=
  Finset.sum_nonneg fun y _ => mul_nonneg (cubeKernel_nonneg hz y) (hf y)

/-- Strict positivity of the extension of a strictly positive function on the
closed solid cube. -/
lemma mext_pos {f : Cube n → ℝ} {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1)
    (hf : ∀ x, 0 < f x) : 0 < mext f z := by
  obtain ⟨y, hy⟩ : ∃ y : Cube n, 0 < cubeKernel z y := by
    by_contra hcon
    have hcon' : ∀ y : Cube n, cubeKernel z y ≤ 0 :=
      fun y => not_lt.1 fun h => hcon ⟨y, h⟩
    have hzero : ∑ y : Cube n, cubeKernel z y = 0 :=
      Finset.sum_eq_zero fun y _ => le_antisymm (hcon' y) (cubeKernel_nonneg hz y)
    rw [sum_cubeKernel] at hzero
    exact one_ne_zero hzero
  rw [mext]
  refine Finset.sum_pos'
    (fun w _ => mul_nonneg (cubeKernel_nonneg hz w) (hf w).le)
    ⟨y, Finset.mem_univ y, mul_pos hy (hf y)⟩

/-- Values of the extension of a `[0,1]`-valued function stay in `[0,1]` on the
solid cube [C Lemma 5, last part]. -/
lemma mext_mem_Icc {f : Cube n → ℝ} {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : mext f z ∈ Set.Icc (0 : ℝ) 1 := by
  have hone : mext (fun _ : Cube n => (1 : ℝ)) z = 1 := by
    simp [mext, sum_cubeKernel]
  refine Set.mem_Icc.2 ⟨mext_nonneg hz fun x => (hf x).1, ?_⟩
  have := mext_mono (f := f) (g := fun _ => (1 : ℝ)) hz fun x => (hf x).2
  rwa [hone] at this

/-- Pointwise kernel-ratio bound ⇒ ratio bound for the extension (mediant
inequality): if `f ≥ 0` and `g ≤ c·h` pointwise with `h, g ≥ 0` then sums obey
the same bound. Used to derive the edge-ratio bound [C Lemma 5]. -/
lemma sum_div_le_of_ratio_le {ι : Type*} [Fintype ι] {g h : ι → ℝ} {c : ℝ}
    (hh : ∀ i, 0 ≤ h i) (hb : ∀ i, g i ≤ c * h i) :
    ∑ i, g i ≤ c * ∑ i, h i := by
  calc ∑ i, g i ≤ ∑ i, c * h i := Finset.sum_le_sum fun i _ => hb i
    _ = c * ∑ i, h i := by rw [Finset.mul_sum]

end Talagrand
