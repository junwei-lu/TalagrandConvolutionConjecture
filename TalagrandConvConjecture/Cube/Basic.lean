import Mathlib

/-!
# The Boolean hypercube: state space, uniform expectation, coordinate flips

The cube `{-1,1}^n` is encoded as `Cube n := Fin n → ℤˣ` (sign vectors with
pointwise multiplication). `toR` embeds signs into `ℝ`. `unifE` is expectation
under the uniform probability measure `λ` on the cube, and `unifMeas` the
uniform measure of a set. [LGF §1 notation.]
-/

namespace Talagrand

/-- The Boolean hypercube `{-1,1}^n` as sign vectors. Pointwise multiplication
is the group operation `x ⊙ y` of [LGF §1]. -/
abbrev Cube (n : ℕ) := Fin n → ℤˣ

variable {n : ℕ}

/-- The real value of a sign: `±1 : ℤˣ` into `ℝ`. -/
def toR (u : ℤˣ) : ℝ := ((u : ℤ) : ℝ)

@[simp] lemma toR_one : toR 1 = 1 := by simp [toR]

@[simp] lemma toR_neg_one : toR (-1) = -1 := by simp [toR]

lemma toR_eq_one_or (u : ℤˣ) : toR u = 1 ∨ toR u = -1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

@[simp] lemma toR_mul (u v : ℤˣ) : toR (u * v) = toR u * toR v := by
  simp [toR]

@[simp] lemma toR_neg (u : ℤˣ) : toR (-u) = -toR u := by simp [toR]

@[simp] lemma toR_mul_self (u : ℤˣ) : toR u * toR u = 1 := by
  rcases toR_eq_one_or u with h | h <;> rw [h] <;> norm_num

@[simp] lemma toR_sq (u : ℤˣ) : toR u ^ 2 = 1 := by
  rw [sq]; exact toR_mul_self u

@[simp] lemma abs_toR (u : ℤˣ) : |toR u| = 1 := by
  rcases toR_eq_one_or u with h | h <;> rw [h] <;> norm_num

lemma neg_one_le_toR (u : ℤˣ) : -1 ≤ toR u := by
  rcases toR_eq_one_or u with h | h <;> rw [h] <;> norm_num

lemma toR_le_one (u : ℤˣ) : toR u ≤ 1 := by
  rcases toR_eq_one_or u with h | h <;> rw [h] <;> norm_num

lemma toR_ne_zero (u : ℤˣ) : toR u ≠ 0 := by
  rcases toR_eq_one_or u with h | h <;> rw [h] <;> norm_num

/-- `1 + ρ·u` is nonnegative when `|ρ| ≤ 1`; these are (twice) the biased-coin
weights. -/
lemma one_add_mul_toR_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) (u : ℤˣ) :
    0 ≤ 1 + ρ * toR u := by
  rcases toR_eq_one_or u with h | h <;> rw [h] <;>
    [linarith [neg_abs_le ρ]; linarith [le_abs_self ρ]]

/-- `1 + ρ·u` is positive when `|ρ| < 1`. -/
lemma one_add_mul_toR_pos {ρ : ℝ} (hρ : |ρ| < 1) (u : ℤˣ) :
    0 < 1 + ρ * toR u := by
  rcases toR_eq_one_or u with h | h <;> rw [h] <;>
    [linarith [neg_abs_le ρ]; linarith [le_abs_self ρ]]

/-! ## Coordinate flip -/

/-- Flip the `i`-th coordinate: `σ_i x` of [LGF §1]. -/
def flipCoord (i : Fin n) (x : Cube n) : Cube n := Function.update x i (-(x i))

@[simp] lemma flipCoord_self (i : Fin n) (x : Cube n) :
    flipCoord i x i = -(x i) := by simp [flipCoord]

@[simp] lemma flipCoord_ne {i j : Fin n} (h : j ≠ i) (x : Cube n) :
    flipCoord i x j = x j := by simp [flipCoord, h]

@[simp] lemma flipCoord_flipCoord (i : Fin n) (x : Cube n) :
    flipCoord i (flipCoord i x) = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma flipCoord_involutive (i : Fin n) : Function.Involutive (flipCoord i) :=
  fun x => flipCoord_flipCoord i x

lemma flipCoord_bijective (i : Fin n) : Function.Bijective (flipCoord i) :=
  (flipCoord_involutive i).bijective

/-- Reindexing a sum by a coordinate flip. -/
lemma sum_comp_flipCoord (i : Fin n) (g : Cube n → ℝ) :
    ∑ x : Cube n, g (flipCoord i x) = ∑ x : Cube n, g x :=
  Fintype.sum_bijective _ (flipCoord_bijective i) _ _ (fun _ => rfl)

/-- Reindexing a sum by translation (group multiplication). -/
lemma sum_comp_mul_right (y : Cube n) (g : Cube n → ℝ) :
    ∑ x : Cube n, g (x * y) = ∑ x : Cube n, g x :=
  Fintype.sum_bijective (· * y) (Group.mulRight_bijective y) _ _ (fun _ => rfl)

@[simp] lemma card_cube : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

/-! ## Uniform expectation and uniform measure -/

/-- Expectation under the uniform probability measure `λ` on the cube. -/
noncomputable def unifE (g : Cube n → ℝ) : ℝ := (∑ x, g x) / 2 ^ n

/-- Uniform measure of a set, `λ(E)`. -/
noncomputable def unifMeas (E : Set (Cube n)) : ℝ :=
  unifE (E.indicator fun _ => (1 : ℝ))

lemma unifE_nonneg {g : Cube n → ℝ} (hg : ∀ x, 0 ≤ g x) : 0 ≤ unifE g := by
  have : 0 ≤ ∑ x, g x := Finset.sum_nonneg fun x _ => hg x
  positivity

@[simp] lemma unifE_const (c : ℝ) : unifE (fun _ : Cube n => c) = c := by
  have h2 : ((2 : ℝ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [unifE, Finset.sum_const, Finset.card_univ, card_cube,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

lemma unifE_add (g h : Cube n → ℝ) :
    unifE (fun x => g x + h x) = unifE g + unifE h := by
  simp [unifE, Finset.sum_add_distrib, add_div]

lemma unifE_smul (c : ℝ) (g : Cube n → ℝ) :
    unifE (fun x => c * g x) = c * unifE g := by
  simp [unifE, ← Finset.mul_sum, mul_div_assoc]

lemma unifE_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x) :
    unifE g ≤ unifE h := by
  have hsum : ∑ x, g x ≤ ∑ x, h x := Finset.sum_le_sum fun x _ => hgh x
  rw [unifE, unifE, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hsum (by positivity)

/-- Invariance of `λ` under coordinate flips. -/
lemma unifE_comp_flipCoord (i : Fin n) (g : Cube n → ℝ) :
    unifE (fun x => g (flipCoord i x)) = unifE g := by
  simp [unifE, sum_comp_flipCoord]

/-- Invariance of `λ` under translation. -/
lemma unifE_comp_mul_right (y : Cube n) (g : Cube n → ℝ) :
    unifE (fun x => g (x * y)) = unifE g := by
  simp [unifE, sum_comp_mul_right]

lemma unifMeas_nonneg (E : Set (Cube n)) : 0 ≤ unifMeas E :=
  unifE_nonneg fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma unifMeas_le_one (E : Set (Cube n)) : unifMeas E ≤ 1 := by
  have hle : ∀ x, E.indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
    intro x
    by_cases hx : x ∈ E
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  calc unifMeas E ≤ unifE (fun _ => (1 : ℝ)) := unifE_mono hle
    _ = 1 := unifE_const 1

lemma unifMeas_mono {E F : Set (Cube n)} (h : E ⊆ F) :
    unifMeas E ≤ unifMeas F := by
  refine unifE_mono fun x => ?_
  by_cases hx : x ∈ E
  · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (h hx)]
  · simp only [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- Markov's inequality on the cube: for `g ≥ 0` and `u > 0`,
`u·λ(g ≥ u) ≤ 𝔼_λ g`. Gives the trivial bound `ψ_μ(u) ≤ 1` of [LGF §1]. -/
lemma mul_unifMeas_le_unifE {g : Cube n → ℝ} (hg : ∀ x, 0 ≤ g x) {u : ℝ}
    (_hu : 0 < u) : u * unifMeas {x | u ≤ g x} ≤ unifE g := by
  rw [unifMeas, ← unifE_smul]
  refine unifE_mono fun x => ?_
  by_cases hx : x ∈ {x | u ≤ g x}
  · simpa [Set.indicator_of_mem hx] using hx
  · simp [Set.indicator_of_notMem hx, hg x]

end Talagrand
