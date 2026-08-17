import TalagrandConvConjecture.Reverse.Setup
import TalagrandConvConjecture.Cube.LevelOne

/-!
# The Boolean bridge [LGF §4.1, §5.2; C Lemmas 9–11]

For `ζ ∈ G` and `t ≤ T_o` set `γ_t = e^{-(T_o-t)}`,
`a_t = γ_t(1-a²)/(1-a²γ_t²)`, `b_t = a(1-γ_t²)/(1-a²γ_t²)`, and the bridge
mean vector `m_t^{[i]}(x,y,ζ) = a_t y_i + b_t x_i y_i ζ_i`. For a test
`φ : G → {0,1}`, `q_t^ζ(x,y) = φ(m_t(x,y,ζ))` (multilinear extension).

Contents ([LGF Lemma 4.4] and the identities of §5.2):
* difference formulas `Δ_i^y q, Δ_i^y q(σ_i x, ·), Δ_i^{xy} q`;
* the coefficient ODE `ṁ^{[i]} = λ_{t,i}^ζ a_t y_i` and space-time
  harmonicity of `q_t^ζ` under the conditioned synchronized generator;
* the carré-du-champ identity [LGF eq (4.9)];
* the weighted bridge estimate `λ_{t,i}^ζ b_t² ≤ a²/(1-a²)·(1-(m^{[i]})²)`
  [LGF eq (4.8)];
* `|m^{[i]}| ≤ 1` (so the level-one inequality applies at `z = m_t`).
-/

namespace Talagrand

/-- `γ_t = e^{-(T_o - t)}` [LGF §4.1]. -/
noncomputable def gam (t : ℝ) : ℝ := Real.exp (-(obsT - t))

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- `a_t = γ_t(1-a²)/(1-a²γ_t²)` [LGF §4.1]. -/
noncomputable def aB (t : ℝ) : ℝ := gam t * (1 - D.a ^ 2) / (1 - D.a ^ 2 * gam t ^ 2)

/-- `b_t = a(1-γ_t²)/(1-a²γ_t²)` [LGF §4.1]. -/
noncomputable def bB (t : ℝ) : ℝ := D.a * (1 - gam t ^ 2) / (1 - D.a ^ 2 * gam t ^ 2)

/-- Bridge mean vector `m_t(x,y,ζ) ∈ [-1,1]^n`,
`m_t^{[i]} = a_t y_i + b_t x_i y_i ζ_i` [LGF §4.1]. -/
noncomputable def mB (t : ℝ) (x y ζ : Cube n) (i : Fin n) : ℝ :=
  D.aB t * toR (y i) + D.bB t * toR (x i) * toR (y i) * toR (ζ i)

/-- The bridge test `q_t^ζ(x,y) = φ(m_t(x,y,ζ))` for a terminal test `φ`
[LGF §4.1]. -/
noncomputable def qB (φ : Cube n → ℝ) (t : ℝ) (ζ x y : Cube n) : ℝ :=
  mext φ (D.mB t x y ζ)

section ranges

lemma gam_pos (t : ℝ) : 0 < gam t := Real.exp_pos _

lemma gam_le_one {t : ℝ} (ht : t ≤ obsT) : gam t ≤ 1 := by
  have : -(obsT - t) ≤ 0 := by linarith
  simpa [gam] using Real.exp_le_one_iff.mpr this

lemma a_sq_lt_one : D.a ^ 2 < 1 := by
  nlinarith [mul_pos D.ha0 (sub_pos.mpr D.ha1), D.ha1]

/-- The common denominator `1 - a²γ_t²` is strictly positive (for all `t` with
`γ_t ≤ 1`). -/
lemma den_pos {t : ℝ} (ht : t ≤ obsT) : 0 < 1 - D.a ^ 2 * gam t ^ 2 := by
  have hg0 : 0 < gam t := gam_pos t
  have hg1 : gam t ≤ 1 := gam_le_one ht
  have hgs : gam t ^ 2 ≤ 1 := by nlinarith
  nlinarith [D.a_sq_lt_one, sq_nonneg D.a]

lemma aB_nonneg {t : ℝ} (ht : t ≤ obsT) : 0 ≤ D.aB t := by
  have hg0 : 0 < gam t := gam_pos t
  refine div_nonneg (mul_nonneg hg0.le ?_) (le_of_lt (D.den_pos ht))
  linarith [D.a_sq_lt_one]

lemma bB_nonneg {t : ℝ} (ht : t ≤ obsT) : 0 ≤ D.bB t := by
  have hg0 : 0 < gam t := gam_pos t
  have hg1 : gam t ≤ 1 := gam_le_one ht
  refine div_nonneg (mul_nonneg D.ha0.le ?_) (le_of_lt (D.den_pos ht))
  nlinarith

/-- `a_t + b_t = (a+γ_t)/(1+aγ_t) ≤ 1`, hence `|m^{[i]}| ≤ 1`. -/
lemma aB_add_bB_le_one {t : ℝ} (ht : t ≤ obsT) : D.aB t + D.bB t ≤ 1 := by
  have hg0 : 0 < gam t := gam_pos t
  have hg1 : gam t ≤ 1 := gam_le_one ht
  have hd : 0 < 1 - D.a ^ 2 * gam t ^ 2 := D.den_pos ht
  rw [aB, bB, ← add_div, div_le_one hd]
  -- `1 - a²γ² - (γ(1-a²) + a(1-γ²)) = (1-a)(1-γ)(1-aγ) ≥ 0`
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr D.ha1.le) (sub_nonneg.mpr hg1))
    (sub_nonneg.mpr (by nlinarith [D.ha0, D.ha1] : D.a * gam t ≤ 1))]

lemma abs_mB_le_one {t : ℝ} (ht : t ≤ obsT) (x y ζ : Cube n) (i : Fin n) :
    |D.mB t x y ζ i| ≤ 1 := by
  have h1 : |D.aB t * toR (y i)| = D.aB t := by
    rw [abs_mul, abs_toR, mul_one, abs_of_nonneg (D.aB_nonneg ht)]
  have h2 : |D.bB t * toR (x i) * toR (y i) * toR (ζ i)| = D.bB t := by
    rw [abs_mul, abs_mul, abs_mul, abs_toR, abs_toR, abs_toR,
      abs_of_nonneg (D.bB_nonneg ht)]; ring
  calc |D.mB t x y ζ i| ≤ |D.aB t * toR (y i)|
        + |D.bB t * toR (x i) * toR (y i) * toR (ζ i)| := abs_add_le _ _
    _ = D.aB t + D.bB t := by rw [h1, h2]
    _ ≤ 1 := D.aB_add_bB_le_one ht

end ranges

section identities

/-- Affine-difference form of `mext_update`: changing the `i`-th coordinate
from `z i` to `s` changes `mext φ` by `(s - z i)·∂_iφ`. -/
lemma mext_update_sub (φ : Cube n → ℝ) (i : Fin n) (z : Fin n → ℝ) (s : ℝ) :
    mext φ (Function.update z i s) - mext φ z = (s - z i) * dmext φ i z := by
  have h1 := mext_update φ i z s
  have h2 := mext_update φ i z (z i)
  simp only [Function.update_eq_self] at h2
  rw [h1, h2]; ring

/-- Flipping `y_i` negates `m^{[i]}` and leaves other coordinates unchanged:
`m_t(x, σ_i y, ζ) = update (m_t(x,y,ζ)) i (-(m^{[i]}))`. -/
lemma mB_flip_y (t : ℝ) (x y ζ : Cube n) (i : Fin n) :
    D.mB t x (flipCoord i y) ζ
      = Function.update (D.mB t x y ζ) i (-(D.mB t x y ζ i)) := by
  funext j
  by_cases h : j = i
  · subst h; simp only [mB, flipCoord_self, toR_neg, Function.update_self]; ring
  · simp only [mB, flipCoord_ne h, Function.update_of_ne h]

/-- Flipping `x_i` negates the `b_t`-part of `m^{[i]}` only. -/
lemma mB_flip_x (t : ℝ) (x y ζ : Cube n) (i : Fin n) :
    D.mB t (flipCoord i x) y ζ
      = Function.update (D.mB t x y ζ) i
          (D.aB t * toR (y i) - D.bB t * toR (x i) * toR (y i) * toR (ζ i)) := by
  funext j
  by_cases h : j = i
  · subst h; simp only [mB, flipCoord_self, toR_neg, Function.update_self]; ring
  · simp only [mB, flipCoord_ne h, Function.update_of_ne h]

/-- Flipping both `x_i, y_i` shifts `m^{[i]}` by `-2a_t y_i`. -/
lemma mB_flip_xy (t : ℝ) (x y ζ : Cube n) (i : Fin n) :
    D.mB t (flipCoord i x) (flipCoord i y) ζ
      = Function.update (D.mB t x y ζ) i
          (D.mB t x y ζ i - 2 * D.aB t * toR (y i)) := by
  funext j
  by_cases h : j = i
  · subst h; simp only [mB, flipCoord_self, toR_neg, Function.update_self]; ring
  · simp only [mB, flipCoord_ne h, Function.update_of_ne h]

/-- Bridge difference in `y` [LGF eq (4.6)]:
`Δ_i^y q_t^ζ(x,y) = -2(a_t y_i + b_t x_i y_i ζ_i)·∂_iφ(m_t)`. -/
lemma qB_flip_y_sub (φ : Cube n → ℝ) (t : ℝ) (ζ x y : Cube n) (i : Fin n) :
    D.qB φ t ζ x (flipCoord i y) - D.qB φ t ζ x y
      = -2 * D.mB t x y ζ i * dmext φ i (D.mB t x y ζ) := by
  simp only [qB]
  rw [mB_flip_y, mext_update_neg]
  ring

/-- Bridge difference in `y` after flipping `x_i` [LGF eq (4.7)]:
`Δ_i^y q_t^ζ(σ_i x, y) = -2(a_t y_i - b_t x_i y_i ζ_i)·∂_iφ(m_t)`. -/
lemma qB_flip_y_flip_x_sub (φ : Cube n → ℝ) (t : ℝ) (ζ x y : Cube n)
    (i : Fin n) :
    D.qB φ t ζ (flipCoord i x) (flipCoord i y) - D.qB φ t ζ (flipCoord i x) y
      = -2 * (D.aB t * toR (y i)
          - D.bB t * toR (x i) * toR (y i) * toR (ζ i))
        * dmext φ i (D.mB t x y ζ) := by
  simp only [qB]
  rw [mB_flip_y, mext_update_neg, D.mB_flip_x t x y ζ i, Function.update_self,
    dmext_update]
  ring

/-- Synchronized bridge difference:
`Δ_i^{xy} q_t^ζ = -2a_t y_i·∂_iφ(m_t)` [LGF §5.2]. -/
lemma qB_flip_xy_sub (φ : Cube n → ℝ) (t : ℝ) (ζ x y : Cube n) (i : Fin n) :
    D.qB φ t ζ (flipCoord i x) (flipCoord i y) - D.qB φ t ζ x y
      = -2 * D.aB t * toR (y i) * dmext φ i (D.mB t x y ζ) := by
  simp only [qB]
  rw [mB_flip_xy, mext_update_sub]
  ring

/-- `γ_t` solves `γ̇ = γ`. -/
lemma hasDerivAt_gam (t : ℝ) : HasDerivAt (fun s => gam s) (gam t) t := by
  have h : HasDerivAt (fun s : ℝ => -(obsT - s)) 1 t := by
    simpa using hasDerivAt_id t
  simpa [gam] using h.exp

/-- `ρ_t = e^{-(T-t)} = a·γ_t` (uses `e^{-t_a} = a`). -/
lemma exp_neg_T_sub (t : ℝ) : Real.exp (-(D.T - t)) = D.a * gam t := by
  have h : -(D.T - t) = Real.log D.a + -(obsT - t) := by
    simp only [T, tA]; ring
  rw [h, Real.exp_add, Real.exp_log D.ha0, gam]

/-- Normalized form of `λ_{t,i}^ζ` once the sign `ε = x_iζ_i` is known. -/
lemma lam_eq_of (t : ℝ) (i : Fin n) (x ζ : Cube n) {p q : ℝ}
    (hp : 1 - D.a * gam t * toR (x i) * toR (ζ i) = p)
    (hq : 1 + D.a * gam t * toR (x i) * toR (ζ i) = q) :
    D.lam t i x ζ = p / q := by
  simp only [lam, D.exp_neg_T_sub, hp, hq]

/-- Coefficient ODE on the nondegenerate range `1 - a²γ_t² ≠ 0`
(automatic for `t ≤ T_o` by `den_pos`, and in fact for every `t ≠ T`):
`d/dt m_t^{[i]} = λ_{t,i}^ζ(x)·a_t·y_i` [LGF §5.2]. -/
lemma hasDerivAt_mB_of_ne {t : ℝ} (hne : 1 - D.a ^ 2 * gam t ^ 2 ≠ 0)
    (x y ζ : Cube n) (i : Fin n) :
    HasDerivAt (fun t => D.mB t x y ζ i)
      (D.lam t i x ζ * D.aB t * toR (y i)) t := by
  have hfac : (1 - D.a * gam t) * (1 + D.a * gam t) = 1 - D.a ^ 2 * gam t ^ 2 := by
    ring
  have h1 : (1 : ℝ) - D.a * gam t ≠ 0 := by
    intro h; exact hne (by rw [← hfac, h]; ring)
  have h2 : (1 : ℝ) + D.a * gam t ≠ 0 := by
    intro h; exact hne (by rw [← hfac, h]; ring)
  have h1' : (1 : ℝ) - gam t * D.a ≠ 0 := by rw [mul_comm (gam t) D.a]; exact h1
  have h2' : (1 : ℝ) + gam t * D.a ≠ 0 := by rw [mul_comm (gam t) D.a]; exact h2
  have hg : HasDerivAt (fun s => gam s) (gam t) t := hasDerivAt_gam t
  have hden : HasDerivAt (fun s => 1 - D.a ^ 2 * gam s ^ 2)
      (-(D.a ^ 2 * ((2 : ℕ) * gam t ^ (2 - 1) * gam t))) t :=
    ((hg.pow 2).const_mul (D.a ^ 2)).const_sub 1
  have hA := (hg.mul_const (1 - D.a ^ 2)).div hden hne
  have hB := (((hg.pow 2).const_sub 1).const_mul D.a).div hden hne
  have hM := (hA.mul_const (toR (y i))).add
    (((hB.mul_const (toR (x i))).mul_const (toR (y i))).mul_const (toR (ζ i)))
  convert hM using 1
  simp only [Pi.pow_apply]
  -- `λ_{t,i}^ζ = (1 ∓ aγ)/(1 ± aγ)` according to the sign `ε = x_iζ_i`
  have hlam : ∀ p q : ℝ, (1 : ℝ) - D.a * gam t * toR (x i) * toR (ζ i) = p →
      (1 : ℝ) + D.a * gam t * toR (x i) * toR (ζ i) = q →
      D.lam t i x ζ = p / q := by
    intro p q hp hq
    simp only [lam, D.exp_neg_T_sub, hp, hq]
  rcases toR_eq_one_or (x i) with hx | hx <;> rcases toR_eq_one_or (ζ i) with hz | hz
  · rw [hlam (1 - D.a * gam t) (1 + D.a * gam t) (by rw [hx, hz]; ring)
      (by rw [hx, hz]; ring)]
    simp only [aB, hx, hz]; field_simp; ring
  · rw [hlam (1 + D.a * gam t) (1 - D.a * gam t) (by rw [hx, hz]; ring)
      (by rw [hx, hz]; ring)]
    simp only [aB, hx, hz]; field_simp; ring
  · rw [hlam (1 + D.a * gam t) (1 - D.a * gam t) (by rw [hx, hz]; ring)
      (by rw [hx, hz]; ring)]
    simp only [aB, hx, hz]; field_simp; ring
  · rw [hlam (1 - D.a * gam t) (1 + D.a * gam t) (by rw [hx, hz]; ring)
      (by rw [hx, hz]; ring)]
    simp only [aB, hx, hz]; field_simp; ring

/-- The bridge coefficients degenerate exactly at `t = T`: `aγ_T = 1`, i.e.
`1 - a²γ_T² = 0` (so `a_T`, `b_T` are junk `x/0 = 0` there). -/
lemma a_mul_gam_T : D.a * gam D.T = 1 := by
  have h := D.exp_neg_T_sub D.T
  simpa using h.symm

-- STATEMENT-ISSUE: this hypothesis-free form is FALSE at the single time
-- `t = D.T` (where `γ_T = 1/a`, so `1 - a²γ_T² = 0`). There both `a_t` and
-- `b_t` are junk (`x/0 = 0`) while their limits are infinite/nonzero, so
-- `s ↦ m_s^{[i]}` is discontinuous at `T` and no derivative exists, whereas
-- the stated RHS evaluates to `0`. Falsity witness: `n = 1`, `y i = 1`,
-- `x i = ζ i = 1`, `t = D.T`: the LHS function tends to
-- `(a + a⁻¹)/2 ≠ 0 = m_T^{[i]}`. The intended statement carries `t ≤ obsT`
-- (or `t ≠ D.T`); `hasDerivAt_mB_of_ne` above proves exactly that, and every
-- downstream use in this file is inside `t ≤ obsT`. Replacing the hypothesis
-- closes this `sorry` by `exact D.hasDerivAt_mB_of_ne (ne_of_gt (D.den_pos ht)) ..`.
/-- Coefficient ODE: `d/dt m_t^{[i]} = λ_{t,i}^ζ(x)·a_t·y_i` (equivalently
the pair of scalar ODEs for `a_t ± b_t`) [LGF §5.2, harmonicity of the
bridge]. -/
lemma hasDerivAt_mB (t : ℝ) (x y ζ : Cube n) (i : Fin n) :
    HasDerivAt (fun t => D.mB t x y ζ i)
      (D.lam t i x ζ * D.aB t * toR (y i)) t := by
  sorry

/-- **Space-time harmonicity of the bridge** under the conditioned
synchronized generator [LGF Lemma 4.4]:
`∂_t q_t^ζ(x,y) + ½∑_i λ_{t,i}^ζ(x)·Δ_i^{xy}q_t^ζ(x,y) = 0`. -/
theorem hasDerivAt_qB (φ : Cube n → ℝ) (t : ℝ) (ζ x y : Cube n) :
    HasDerivAt (fun t => D.qB φ t ζ x y)
      (-(∑ i, D.lam t i x ζ *
          (D.qB φ t ζ (flipCoord i x) (flipCoord i y) - D.qB φ t ζ x y) / 2))
      t := by
  have h := hasDerivAt_mext_comp φ (fun s => D.mB s x y ζ)
    (fun i => D.lam t i x ζ * D.aB t * toR (y i)) t
    (fun i => D.hasDerivAt_mB t x y ζ i)
  convert h using 1
  have key : ∀ i : Fin n,
      D.lam t i x ζ * (D.qB φ t ζ (flipCoord i x) (flipCoord i y) - D.qB φ t ζ x y) / 2
        = -(dmext φ i (D.mB t x y ζ) * (D.lam t i x ζ * D.aB t * toR (y i))) := by
    intro i; rw [D.qB_flip_xy_sub φ t ζ x y i]; ring
  simp only [key, Finset.sum_neg_distrib, neg_neg]

/-- **Carré du champ** [LGF eq (4.9)]:
`(∂_t + 𝓛^{0,ζ})(q_t^ζ)² = 2a_t²∑_i λ_{t,i}^ζ|∂_iφ(m_t)|²`. -/
theorem hasDerivAt_qB_sq (φ : Cube n → ℝ) (t : ℝ) (ζ x y : Cube n) :
    HasDerivAt (fun t => D.qB φ t ζ x y ^ 2)
      (-(∑ i, D.lam t i x ζ *
            (D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
              - D.qB φ t ζ x y ^ 2) / 2)
        + 2 * D.aB t ^ 2 * ∑ i, D.lam t i x ζ
            * dmext φ i (D.mB t x y ζ) ^ 2) t := by
  have h := (D.hasDerivAt_qB φ t ζ x y).pow 2
  convert h using 1
  have hqF : ∀ i : Fin n, D.qB φ t ζ (flipCoord i x) (flipCoord i y)
      = D.qB φ t ζ x y + (-2 * D.aB t * toR (y i) * dmext φ i (D.mB t x y ζ)) := by
    intro i
    have := D.qB_flip_xy_sub φ t ζ x y i
    linarith
  simp only [hqF, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (-2 * D.aB t ^ 2 * D.lam t i x ζ
    * dmext φ i (D.mB t x y ζ) ^ 2) * toR_sq (y i)

/-- **Weighted bridge estimate** [LGF eq (4.8)]:
`λ_{t,i}^ζ(x)·b_t² ≤ a²/(1-a²)·(1 - (m_t^{[i]})²)` for `t ≤ T_o`. -/
theorem lam_mul_bB_sq_le {t : ℝ} (ht : t ≤ obsT) (x y ζ : Cube n) (i : Fin n) :
    D.lam t i x ζ * D.bB t ^ 2
      ≤ D.a ^ 2 / (1 - D.a ^ 2) * (1 - D.mB t x y ζ i ^ 2) := by
  have hg0 : 0 < gam t := gam_pos t
  have hg1 : gam t ≤ 1 := gam_le_one ht
  have hd : 0 < 1 - D.a ^ 2 * gam t ^ 2 := D.den_pos ht
  have hag : D.a * gam t < 1 := by nlinarith [D.ha0, D.ha1]
  have hp1 : (0 : ℝ) < 1 - D.a * gam t := by linarith
  have hp2 : (0 : ℝ) < 1 + D.a * gam t := by nlinarith [D.ha0]
  have hasq : (0 : ℝ) < 1 - D.a ^ 2 := by linarith [D.a_sq_lt_one]
  have hgsq : (0 : ℝ) ≤ 1 - gam t ^ 2 := by nlinarith
  have hne1 : (1 : ℝ) - D.a * gam t ≠ 0 := ne_of_gt hp1
  have hne2 : (1 : ℝ) + D.a * gam t ≠ 0 := ne_of_gt hp2
  have hnd : (1 : ℝ) - D.a ^ 2 * gam t ^ 2 ≠ 0 := ne_of_gt hd
  have hna : (1 : ℝ) - D.a ^ 2 ≠ 0 := ne_of_gt hasq
  -- the difference `RHS - LHS` equals `a²γ²(1-a²)(1-γ²)/((1±aγ)²(1-a²γ²)) ≥ 0`
  have hquot : ∀ d : ℝ, 0 ≤ d →
      0 ≤ D.a ^ 2 * gam t ^ 2 * (1 - D.a ^ 2) * (1 - gam t ^ 2) / d := fun d hdd =>
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hasq.le) hgsq) hdd
  have hden : ∀ c : ℝ, (0 : ℝ) ≤ c ^ 2 * (1 - D.a ^ 2 * gam t ^ 2) := fun c =>
    mul_nonneg (sq_nonneg _) hd.le
  have hm : D.mB t x y ζ i ^ 2
      = (D.aB t + D.bB t * (toR (x i) * toR (ζ i))) ^ 2 := by
    simp only [mB]
    linear_combination ((D.aB t + D.bB t * (toR (x i) * toR (ζ i))) ^ 2) * toR_sq (y i)
  rw [hm, ← sub_nonneg]
  rcases toR_eq_one_or (x i) with hx | hx <;> rcases toR_eq_one_or (ζ i) with hz | hz
  · rw [show toR (x i) * toR (ζ i) = 1 by rw [hx, hz]; ring,
      D.lam_eq_of t i x ζ (p := 1 - D.a * gam t) (q := 1 + D.a * gam t)
        (by rw [hx, hz]; ring) (by rw [hx, hz]; ring),
      show D.a ^ 2 / (1 - D.a ^ 2) * (1 - (D.aB t + D.bB t * 1) ^ 2)
          - (1 - D.a * gam t) / (1 + D.a * gam t) * D.bB t ^ 2
        = D.a ^ 2 * gam t ^ 2 * (1 - D.a ^ 2) * (1 - gam t ^ 2)
            / ((1 + D.a * gam t) ^ 2 * (1 - D.a ^ 2 * gam t ^ 2)) by
        simp only [aB, bB]; field_simp; ring]
    exact hquot _ (hden _)
  · rw [show toR (x i) * toR (ζ i) = -1 by rw [hx, hz]; ring,
      D.lam_eq_of t i x ζ (p := 1 + D.a * gam t) (q := 1 - D.a * gam t)
        (by rw [hx, hz]; ring) (by rw [hx, hz]; ring),
      show D.a ^ 2 / (1 - D.a ^ 2) * (1 - (D.aB t + D.bB t * -1) ^ 2)
          - (1 + D.a * gam t) / (1 - D.a * gam t) * D.bB t ^ 2
        = D.a ^ 2 * gam t ^ 2 * (1 - D.a ^ 2) * (1 - gam t ^ 2)
            / ((1 - D.a * gam t) ^ 2 * (1 - D.a ^ 2 * gam t ^ 2)) by
        simp only [aB, bB]; field_simp; ring]
    exact hquot _ (hden _)
  · rw [show toR (x i) * toR (ζ i) = -1 by rw [hx, hz]; ring,
      D.lam_eq_of t i x ζ (p := 1 + D.a * gam t) (q := 1 - D.a * gam t)
        (by rw [hx, hz]; ring) (by rw [hx, hz]; ring),
      show D.a ^ 2 / (1 - D.a ^ 2) * (1 - (D.aB t + D.bB t * -1) ^ 2)
          - (1 + D.a * gam t) / (1 - D.a * gam t) * D.bB t ^ 2
        = D.a ^ 2 * gam t ^ 2 * (1 - D.a ^ 2) * (1 - gam t ^ 2)
            / ((1 - D.a * gam t) ^ 2 * (1 - D.a ^ 2 * gam t ^ 2)) by
        simp only [aB, bB]; field_simp; ring]
    exact hquot _ (hden _)
  · rw [show toR (x i) * toR (ζ i) = 1 by rw [hx, hz]; ring,
      D.lam_eq_of t i x ζ (p := 1 - D.a * gam t) (q := 1 + D.a * gam t)
        (by rw [hx, hz]; ring) (by rw [hx, hz]; ring),
      show D.a ^ 2 / (1 - D.a ^ 2) * (1 - (D.aB t + D.bB t * 1) ^ 2)
          - (1 - D.a * gam t) / (1 + D.a * gam t) * D.bB t ^ 2
        = D.a ^ 2 * gam t ^ 2 * (1 - D.a ^ 2) * (1 - gam t ^ 2)
            / ((1 + D.a * gam t) ^ 2 * (1 - D.a ^ 2 * gam t ^ 2)) by
        simp only [aB, bB]; field_simp; ring]
    exact hquot _ (hden _)

end identities

end Dat

end Talagrand
