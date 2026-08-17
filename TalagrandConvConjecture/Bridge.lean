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
  sorry

/-- **Carré du champ** [LGF eq (4.9)]:
`(∂_t + 𝓛^{0,ζ})(q_t^ζ)² = 2a_t²∑_i λ_{t,i}^ζ|∂_iφ(m_t)|²`. -/
theorem hasDerivAt_qB_sq (φ : Cube n → ℝ) (t : ℝ) (ζ x y : Cube n) :
    HasDerivAt (fun t => D.qB φ t ζ x y ^ 2)
      (-(∑ i, D.lam t i x ζ *
            (D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
              - D.qB φ t ζ x y ^ 2) / 2)
        + 2 * D.aB t ^ 2 * ∑ i, D.lam t i x ζ
            * dmext φ i (D.mB t x y ζ) ^ 2) t := by
  sorry

/-- **Weighted bridge estimate** [LGF eq (4.8)]:
`λ_{t,i}^ζ(x)·b_t² ≤ a²/(1-a²)·(1 - (m_t^{[i]})²)` for `t ≤ T_o`. -/
theorem lam_mul_bB_sq_le {t : ℝ} (ht : t ≤ obsT) (x y ζ : Cube n) (i : Fin n) :
    D.lam t i x ζ * D.bB t ^ 2
      ≤ D.a ^ 2 / (1 - D.a ^ 2) * (1 - D.mB t x y ζ i ^ 2) := by
  sorry

end identities

end Dat

end Talagrand
