import TalagrandConvConjecture.Cube.Multilinear

/-!
# The biased level-one (Parseval/Bessel) inequality

[C Lemma 7] (= [LGF eq (4.15)], O'Donnell Ch. 8): for `φ : Cube n → {0,1}` and
`z ∈ [-1,1]^n`,
`∑_i (1 - z_i²)·(∂_i φ(z))² ≤ φ(z) - φ(z)² ≤ 1/4`,
where `φ(z)` denotes the multilinear extension `mext φ z` and
`∂_i φ = dmext φ i`.

Proof route (no inner-product-space typeclasses; direct Bessel): under the
product measure `π_z` with coordinate means `z`, the functions
`χ_i(y) = y_i - z_i` are orthogonal with `𝔼 χ_i² = 1 - z_i²` and
`𝔼[φ χ_i] = (1-z_i²)·∂_iφ(z)`; expanding
`𝔼[(φ - 𝔼φ - ∑_{i ∈ s} c_i χ_i)²] ≥ 0` with the optimal `c_i` over the set `s`
of coordinates with `|z_i| < 1` yields the claim (coordinates with `|z_i| = 1`
contribute `0` on the left).
-/

namespace Talagrand

variable {n : ℕ}

/-! ### Single-coordinate (two-point) computations -/

/-- A sum over the two units of `ℤ`. -/
private lemma sum_units_eq (w : ℤˣ → ℝ) : ∑ ε : ℤˣ, w ε = w 1 + w (-1) := by
  have hne : (1 : ℤˣ) ≠ -1 := by
    intro h
    have h' : ((1 : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) := congrArg Units.val h
    norm_num at h'
  have huniv : (Finset.univ : Finset ℤˣ) = {1, -1} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact Int.units_eq_one_or u
  rw [huniv]
  exact Finset.sum_pair hne

/-- The two-point biased weights sum to `1`. -/
private lemma sum_units_kernel (c : ℝ) : ∑ ε : ℤˣ, (1 + c * toR ε) / 2 = 1 := by
  rw [sum_units_eq]
  simp only [toR_one, toR_neg_one]
  ring

/-- The centered coordinate has biased mean `0`. -/
private lemma sum_units_kernel_centered (c : ℝ) :
    ∑ ε : ℤˣ, (1 + c * toR ε) / 2 * (toR ε - c) = 0 := by
  rw [sum_units_eq]
  simp only [toR_one, toR_neg_one]
  ring

/-- The centered coordinate has biased second moment `1 - c²`. -/
private lemma sum_units_kernel_centered_sq (c : ℝ) :
    ∑ ε : ℤˣ, (1 + c * toR ε) / 2 * (toR ε - c) ^ 2 = 1 - c ^ 2 := by
  rw [sum_units_eq]
  simp only [toR_one, toR_neg_one]
  ring

/-! ### Product structure of the biased measure -/

-- (product-of-sums factorization `sum_cube_prod` is provided by
-- `Cube/Multilinear.lean`)

/-- Splitting the product kernel off the `i`-th coordinate. -/
private lemma cubeKernel_erase (z : Fin n → ℝ) (y : Cube n) (i : Fin n) :
    cubeKernel z y
      = (1 + z i * toR (y i)) / 2
        * ∏ k ∈ Finset.univ.erase i, (1 + z k * toR (y k)) / 2 := by
  classical
  simp only [cubeKernel]
  exact (Finset.mul_prod_erase Finset.univ
    (fun k => (1 + z k * toR (y k)) / 2) (Finset.mem_univ i)).symm

/-- Factorization of a biased expectation across the coordinate `i`: everything
outside `i` is a product of single-coordinate factors, and the `i`-th factor is
an arbitrary function `w` of the sign. -/
private lemma sum_cube_split (f : Fin n → ℤˣ → ℝ) (i : Fin n) (w : ℤˣ → ℝ) :
    ∑ y : Cube n, (∏ k ∈ Finset.univ.erase i, f k (y k)) * w (y i)
      = (∏ k ∈ Finset.univ.erase i, ∑ ε : ℤˣ, f k ε) * ∑ ε : ℤˣ, w ε := by
  classical
  have hgi : ∀ ε : ℤˣ, (if i = i then w ε else f i ε) = w ε := by
    intro ε; simp
  have hgk : ∀ k, k ≠ i → ∀ ε : ℤˣ, (if k = i then w ε else f k ε) = f k ε := by
    intro k hk ε; simp [hk]
  have hL : ∀ y : Cube n, (∏ k, (if k = i then w (y k) else f k (y k)))
      = (∏ k ∈ Finset.univ.erase i, f k (y k)) * w (y i) := by
    intro y
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => if k = i then w (y k) else f k (y k)) (Finset.mem_univ i),
      hgi (y i),
      Finset.prod_congr rfl (fun k hk => hgk k (Finset.ne_of_mem_erase hk) (y k))]
    ring
  have hR : (∏ k, ∑ ε : ℤˣ, (if k = i then w ε else f k ε))
      = (∏ k ∈ Finset.univ.erase i, ∑ ε : ℤˣ, f k ε) * ∑ ε : ℤˣ, w ε := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => ∑ ε : ℤˣ, (if k = i then w ε else f k ε)) (Finset.mem_univ i),
      Finset.sum_congr rfl (fun ε (_ : ε ∈ Finset.univ) => hgi ε),
      Finset.prod_congr rfl (fun k hk =>
        Finset.sum_congr rfl (fun ε (_ : ε ∈ Finset.univ) =>
          hgk k (Finset.ne_of_mem_erase hk) ε))]
    ring
  calc ∑ y : Cube n, (∏ k ∈ Finset.univ.erase i, f k (y k)) * w (y i)
      = ∑ y : Cube n, ∏ k, (if k = i then w (y k) else f k (y k)) :=
        Finset.sum_congr rfl (fun y _ => (hL y).symm)
    _ = ∏ k, ∑ ε : ℤˣ, (if k = i then w ε else f k ε) :=
        sum_cube_prod (fun k ε => if k = i then w ε else f k ε)
    _ = _ := hR

/-- The marginal weights of all coordinates but `i` multiply to `1`. -/
private lemma prod_erase_sum_units (z : Fin n → ℝ) (i : Fin n) :
    (∏ k ∈ Finset.univ.erase i, ∑ ε : ℤˣ, (1 + z k * toR ε) / 2) = 1 :=
  Finset.prod_eq_one (fun k _ => sum_units_kernel (z k))

/-- The product kernel is a probability density (proved here directly from the
product structure, independently of `sum_cubeKernel`). -/
private lemma sum_cubeKernel_eq_one (z : Fin n → ℝ) :
    ∑ y : Cube n, cubeKernel z y = 1 := by
  calc ∑ y : Cube n, cubeKernel z y
      = ∑ y : Cube n, ∏ k, (1 + z k * toR (y k)) / 2 := rfl
    _ = ∏ k, ∑ ε : ℤˣ, (1 + z k * toR ε) / 2 :=
        sum_cube_prod (fun k ε => (1 + z k * toR ε) / 2)
    _ = 1 := Finset.prod_eq_one (fun k _ => sum_units_kernel (z k))

/-! ### The three moment identities -/

/-- Biased expectation of the product of a function with the centered `i`-th
coordinate: `𝔼_{π_z}[g(y)(y_i - z_i)] = (1-z_i²)·∂_i g(z)`. -/
lemma sum_cubeKernel_mul_centered (g : Cube n → ℝ) (z : Fin n → ℝ) (i : Fin n) :
    ∑ y, cubeKernel z y * (g y * (toR (y i) - z i))
      = (1 - z i ^ 2) * dmext g i z := by
  classical
  simp only [dmext]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [cubeKernel_erase z y i]
  have ht : toR (y i) ^ 2 = 1 := toR_sq _
  linear_combination
    ((∏ k ∈ Finset.univ.erase i, (1 + z k * toR (y k)) / 2) * g y * z i / 2) * ht

/-- The centered `i`-th coordinate has biased mean zero. -/
private lemma sum_cubeKernel_centered (z : Fin n → ℝ) (i : Fin n) :
    ∑ y : Cube n, cubeKernel z y * (toR (y i) - z i) = 0 := by
  classical
  calc ∑ y : Cube n, cubeKernel z y * (toR (y i) - z i)
      = ∑ y : Cube n, (∏ k ∈ Finset.univ.erase i, (1 + z k * toR (y k)) / 2)
          * ((1 + z i * toR (y i)) / 2 * (toR (y i) - z i)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [cubeKernel_erase z y i]; ring
    _ = (∏ k ∈ Finset.univ.erase i, ∑ ε : ℤˣ, (1 + z k * toR ε) / 2)
          * ∑ ε : ℤˣ, (1 + z i * toR ε) / 2 * (toR ε - z i) :=
        sum_cube_split (fun k ε => (1 + z k * toR ε) / 2) i
          (fun ε => (1 + z i * toR ε) / 2 * (toR ε - z i))
    _ = 0 := by rw [sum_units_kernel_centered, mul_zero]

/-- Orthogonality of centered coordinates under the biased product measure:
for `i ≠ j`, `𝔼_{π_z}[(y_i - z_i)(y_j - z_j)] = 0`. -/
lemma sum_cubeKernel_centered_mul_centered {i j : Fin n} (z : Fin n → ℝ)
    (hij : i ≠ j) :
    ∑ y, cubeKernel z y * ((toR (y i) - z i) * (toR (y j) - z j)) = 0 := by
  classical
  have hjmem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hif : ∀ y : Cube n,
      (∏ k ∈ Finset.univ.erase i, (if k = j then toR (y k) - z j else 1))
        = toR (y j) - z j := by
    intro y
    calc (∏ k ∈ Finset.univ.erase i, (if k = j then toR (y k) - z j else 1))
        = (if j = j then toR (y j) - z j else 1) :=
          Finset.prod_eq_single j (fun b _ hb => by simp [hb])
            (fun h => absurd hjmem h)
      _ = toR (y j) - z j := by simp
  calc ∑ y : Cube n, cubeKernel z y * ((toR (y i) - z i) * (toR (y j) - z j))
      = ∑ y : Cube n, (∏ k ∈ Finset.univ.erase i,
            (1 + z k * toR (y k)) / 2 * (if k = j then toR (y k) - z j else 1))
          * ((1 + z i * toR (y i)) / 2 * (toR (y i) - z i)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [cubeKernel_erase z y i, Finset.prod_mul_distrib, hif y]
        ring
    _ = (∏ k ∈ Finset.univ.erase i, ∑ ε : ℤˣ,
            (1 + z k * toR ε) / 2 * (if k = j then toR ε - z j else 1))
          * ∑ ε : ℤˣ, (1 + z i * toR ε) / 2 * (toR ε - z i) :=
        sum_cube_split
          (fun k ε => (1 + z k * toR ε) / 2 * (if k = j then toR ε - z j else 1))
          i (fun ε => (1 + z i * toR ε) / 2 * (toR ε - z i))
    _ = 0 := by rw [sum_units_kernel_centered, mul_zero]

/-- Second moment of a centered coordinate: `𝔼_{π_z}[(y_i - z_i)²] = 1 - z_i²`. -/
lemma sum_cubeKernel_centered_sq (z : Fin n → ℝ) (i : Fin n) :
    ∑ y, cubeKernel z y * (toR (y i) - z i) ^ 2 = 1 - z i ^ 2 := by
  classical
  calc ∑ y : Cube n, cubeKernel z y * (toR (y i) - z i) ^ 2
      = ∑ y : Cube n, (∏ k ∈ Finset.univ.erase i, (1 + z k * toR (y k)) / 2)
          * ((1 + z i * toR (y i)) / 2 * (toR (y i) - z i) ^ 2) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [cubeKernel_erase z y i]; ring
    _ = (∏ k ∈ Finset.univ.erase i, ∑ ε : ℤˣ, (1 + z k * toR ε) / 2)
          * ∑ ε : ℤˣ, (1 + z i * toR ε) / 2 * (toR ε - z i) ^ 2 :=
        sum_cube_split (fun k ε => (1 + z k * toR ε) / 2) i
          (fun ε => (1 + z i * toR ε) / 2 * (toR ε - z i) ^ 2)
    _ = 1 - z i ^ 2 := by
        rw [prod_erase_sum_units, sum_units_kernel_centered_sq, one_mul]

/-! ### The level-one inequality -/

/-- **Level-one inequality** [C Lemma 7]: for a `{0,1}`-valued `φ` and
`z ∈ [-1,1]^n`,
`∑_i (1-z_i²)(∂_iφ(z))² ≤ mext φ z - (mext φ z)²`. -/
theorem level_one {φ : Cube n → ℝ} (hφ : ∀ x, φ x = 0 ∨ φ x = 1)
    {z : Fin n → ℝ} (hz : ∀ i, |z i| ≤ 1) :
    ∑ i, (1 - z i ^ 2) * dmext φ i z ^ 2 ≤ mext φ z - mext φ z ^ 2 := by
  classical
  have hzsq : ∀ i, z i ^ 2 ≤ 1 := by
    intro i
    nlinarith [sq_abs (z i), abs_nonneg (z i), hz i]
  obtain ⟨s, hmem⟩ : ∃ s : Finset (Fin n), ∀ i, i ∈ s ↔ z i ^ 2 < 1 :=
    ⟨Finset.univ.filter (fun i => z i ^ 2 < 1), fun i => by simp⟩
  have hEsum : ∑ y : Cube n, cubeKernel z y * φ y = mext φ z := rfl
  have hsq : ∀ y : Cube n, φ y ^ 2 = φ y := by
    intro y; rcases hφ y with h | h <;> rw [h] <;> norm_num
  -- Variance term.
  have hA : ∑ y : Cube n, cubeKernel z y * (φ y - mext φ z) ^ 2
      = mext φ z - mext φ z ^ 2 := by
    have h : ∀ y : Cube n, cubeKernel z y * (φ y - mext φ z) ^ 2
        = cubeKernel z y * φ y * (1 - 2 * mext φ z)
          + cubeKernel z y * mext φ z ^ 2 := by
      intro y
      linear_combination cubeKernel z y * hsq y
    calc ∑ y : Cube n, cubeKernel z y * (φ y - mext φ z) ^ 2
        = ∑ y : Cube n, (cubeKernel z y * φ y * (1 - 2 * mext φ z)
            + cubeKernel z y * mext φ z ^ 2) :=
          Finset.sum_congr rfl (fun y _ => h y)
      _ = (∑ y : Cube n, cubeKernel z y * φ y) * (1 - 2 * mext φ z)
            + (∑ y : Cube n, cubeKernel z y) * mext φ z ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
      _ = mext φ z - mext φ z ^ 2 := by
          rw [sum_cubeKernel_eq_one, hEsum]; ring
  -- Cross terms.
  have hB : ∀ i : Fin n,
      (∑ y : Cube n, cubeKernel z y * ((φ y - mext φ z) * (toR (y i) - z i)))
        = (1 - z i ^ 2) * dmext φ i z := by
    intro i
    calc (∑ y : Cube n, cubeKernel z y * ((φ y - mext φ z) * (toR (y i) - z i)))
        = ∑ y : Cube n, (cubeKernel z y * (φ y * (toR (y i) - z i))
            - mext φ z * (cubeKernel z y * (toR (y i) - z i))) :=
          Finset.sum_congr rfl (fun y _ => by ring)
      _ = (∑ y : Cube n, cubeKernel z y * (φ y * (toR (y i) - z i)))
            - mext φ z * ∑ y : Cube n, cubeKernel z y * (toR (y i) - z i) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = (1 - z i ^ 2) * dmext φ i z := by
          rw [sum_cubeKernel_mul_centered, sum_cubeKernel_centered, mul_zero,
            sub_zero]
  -- Expansion of the square.
  have hQeq : ∑ y : Cube n, cubeKernel z y *
        (φ y - mext φ z - ∑ i ∈ s, dmext φ i z * (toR (y i) - z i)) ^ 2
      = ((∑ y : Cube n, cubeKernel z y * (φ y - mext φ z) ^ 2)
          - 2 * ∑ i ∈ s, dmext φ i z *
              (∑ y : Cube n, cubeKernel z y
                * ((φ y - mext φ z) * (toR (y i) - z i))))
        + ∑ i ∈ s, ∑ j ∈ s, dmext φ i z * dmext φ j z *
            (∑ y : Cube n, cubeKernel z y
              * ((toR (y i) - z i) * (toR (y j) - z j))) := by
    have h1 : ∀ y : Cube n, cubeKernel z y *
          (φ y - mext φ z - ∑ i ∈ s, dmext φ i z * (toR (y i) - z i)) ^ 2
        = (cubeKernel z y * (φ y - mext φ z) ^ 2
            - 2 * ∑ i ∈ s, dmext φ i z *
                (cubeKernel z y * ((φ y - mext φ z) * (toR (y i) - z i))))
          + ∑ i ∈ s, ∑ j ∈ s, dmext φ i z * dmext φ j z *
              (cubeKernel z y * ((toR (y i) - z i) * (toR (y j) - z j))) := by
      intro y
      have e1 : (∑ i ∈ s, dmext φ i z * (toR (y i) - z i)) ^ 2
          = ∑ i ∈ s, ∑ j ∈ s, (dmext φ i z * (toR (y i) - z i))
              * (dmext φ j z * (toR (y j) - z j)) := by
        rw [pow_two, Finset.sum_mul_sum]
      have e2 : (∑ i ∈ s, dmext φ i z *
            (cubeKernel z y * ((φ y - mext φ z) * (toR (y i) - z i))))
          = cubeKernel z y * (φ y - mext φ z)
              * ∑ i ∈ s, dmext φ i z * (toR (y i) - z i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have e3 : (∑ i ∈ s, ∑ j ∈ s, dmext φ i z * dmext φ j z *
              (cubeKernel z y * ((toR (y i) - z i) * (toR (y j) - z j))))
          = cubeKernel z y * ∑ i ∈ s, ∑ j ∈ s,
              (dmext φ i z * (toR (y i) - z i))
                * (dmext φ j z * (toR (y j) - z j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e2, e3, ← e1]
      ring
    have hQ2 : (∑ y : Cube n, 2 * ∑ i ∈ s, dmext φ i z *
          (cubeKernel z y * ((φ y - mext φ z) * (toR (y i) - z i))))
        = 2 * ∑ i ∈ s, dmext φ i z *
            (∑ y : Cube n, cubeKernel z y
              * ((φ y - mext φ z) * (toR (y i) - z i))) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      exact congrArg (fun t => 2 * t)
        (Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm)
    have hR2 : (∑ y : Cube n, ∑ i ∈ s, ∑ j ∈ s, dmext φ i z * dmext φ j z *
            (cubeKernel z y * ((toR (y i) - z i) * (toR (y j) - z j))))
        = ∑ i ∈ s, ∑ j ∈ s, dmext φ i z * dmext φ j z *
            (∑ y : Cube n, cubeKernel z y
              * ((toR (y i) - z i) * (toR (y j) - z j))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    calc ∑ y : Cube n, cubeKernel z y *
          (φ y - mext φ z - ∑ i ∈ s, dmext φ i z * (toR (y i) - z i)) ^ 2
        = ∑ y : Cube n, ((cubeKernel z y * (φ y - mext φ z) ^ 2
              - 2 * ∑ i ∈ s, dmext φ i z *
                  (cubeKernel z y * ((φ y - mext φ z) * (toR (y i) - z i))))
            + ∑ i ∈ s, ∑ j ∈ s, dmext φ i z * dmext φ j z *
                (cubeKernel z y * ((toR (y i) - z i) * (toR (y j) - z j)))) :=
          Finset.sum_congr rfl (fun y _ => h1 y)
      _ = ((∑ y : Cube n, cubeKernel z y * (φ y - mext φ z) ^ 2)
            - ∑ y : Cube n, 2 * ∑ i ∈ s, dmext φ i z *
                (cubeKernel z y * ((φ y - mext φ z) * (toR (y i) - z i))))
          + ∑ y : Cube n, ∑ i ∈ s, ∑ j ∈ s, dmext φ i z * dmext φ j z *
              (cubeKernel z y * ((toR (y i) - z i) * (toR (y j) - z j))) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by rw [hQ2, hR2]
  -- Orthogonality collapses the quadratic term.
  have hCC : ∑ i ∈ s, ∑ j ∈ s, dmext φ i z * dmext φ j z *
        (∑ y : Cube n, cubeKernel z y
          * ((toR (y i) - z i) * (toR (y j) - z j)))
      = ∑ i ∈ s, (1 - z i ^ 2) * dmext φ i z ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single_of_mem i hi (fun j _ hji => by
      rw [sum_cubeKernel_centered_mul_centered z (Ne.symm hji), mul_zero])]
    have h2 : (∑ y : Cube n, cubeKernel z y
          * ((toR (y i) - z i) * (toR (y i) - z i))) = 1 - z i ^ 2 := by
      rw [← sum_cubeKernel_centered_sq z i]
      exact Finset.sum_congr rfl fun y _ => by rw [pow_two]
    rw [h2]; ring
  have hmid : ∑ i ∈ s, dmext φ i z *
        (∑ y : Cube n, cubeKernel z y
          * ((φ y - mext φ z) * (toR (y i) - z i)))
      = ∑ i ∈ s, (1 - z i ^ 2) * dmext φ i z ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB i]; ring
  have hnonneg : 0 ≤ ∑ y : Cube n, cubeKernel z y *
      (φ y - mext φ z - ∑ i ∈ s, dmext φ i z * (toR (y i) - z i)) ^ 2 :=
    Finset.sum_nonneg fun y _ =>
      mul_nonneg (cubeKernel_nonneg hz y) (sq_nonneg _)
  rw [hQeq, hA, hmid, hCC] at hnonneg
  have hfull : ∑ i, (1 - z i ^ 2) * dmext φ i z ^ 2
      = ∑ i ∈ s, (1 - z i ^ 2) * dmext φ i z ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hi
    have h1 : ¬ (z i ^ 2 < 1) := fun h => hi ((hmem i).2 h)
    have h2 : z i ^ 2 = 1 := le_antisymm (hzsq i) (not_lt.1 h1)
    rw [h2]; ring
  rw [hfull]
  linarith [hnonneg]

/-- The elementary bound `t - t² ≤ 1/4`. -/
lemma self_sub_sq_le_quarter (t : ℝ) : t - t ^ 2 ≤ 1 / 4 := by
  nlinarith [sq_nonneg (t - 1 / 2)]

end Talagrand
