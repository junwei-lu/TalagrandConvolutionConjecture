import TalagrandConvConjecture.Cube.Entropy

/-!
# A log-Sobolev inequality on the Boolean hypercube

Goal: `Ent_λ(h) ≤ 𝔼_λ ∑_i (√(h(σ_i x)) - √(h x))²` for `h ≥ 0`, i.e.
`Ent(h) ≤ 4·𝔈(√h, √h)` with the Dirichlet form
`𝔈(g,g) = ¼ 𝔼 ∑_i (Δ_i g)²`.

[C, proof of Lemma 4] uses the optimal constant `2` (Gross); any universal
constant suffices for [LGF], and constant `4` admits the following elementary
proof, which is the deviation we take:
* two-point inequality: for `α, β ≥ 0`,
  `½(α² log α² + β² log β²) - m log m ≤ (α-β)²` with `m = (α²+β²)/2`;
  proved via the normalized 1-D inequality
  `(1+u)log(1+u) + (1-u)log(1-u) ≤ 2u²` on `[0,1]` and `1-√(1-u²) ≥ u²/2`;
* tensorization (`entUnif_le_sum_pairEnt` from `Cube/Entropy.lean`).
-/

namespace Talagrand

/-- The 1-D inequality on the full range `[-1,1]`: both summands are bounded
by `Real.log_le_sub_one_of_pos` (`log(1±u) ≤ ±u`) after multiplying by the
nonnegative factors `1 ± u`. -/
private lemma one_add_mul_log_add_le' (u : ℝ) (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u) ≤ 2 * u ^ 2 := by
  have hA : (1 + u) * Real.log (1 + u) ≤ u + u ^ 2 := by
    rcases eq_or_lt_of_le hu0 with h | h
    · subst h; norm_num
    · have hpos : (0:ℝ) < 1 + u := by linarith
      have hlog : Real.log (1 + u) ≤ u := by
        have := Real.log_le_sub_one_of_pos hpos
        linarith
      linarith [mul_le_mul_of_nonneg_left hlog hpos.le]
  have hB : (1 - u) * Real.log (1 - u) ≤ -u + u ^ 2 := by
    rcases eq_or_lt_of_le hu1 with h | h
    · subst h; norm_num
    · have hpos : (0:ℝ) < 1 - u := by linarith
      have hlog : Real.log (1 - u) ≤ -u := by
        have := Real.log_le_sub_one_of_pos hpos
        linarith
      linarith [mul_le_mul_of_nonneg_left hlog hpos.le]
  linarith

/-- 1-D inequality: `(1+u)·log(1+u) + (1-u)·log(1-u) ≤ 2u²` for `u ∈ [0,1]`
(at `u = 1` with the convention `0·log 0 = 0`). Convexity on `[0,1/√2]` with
double root at `0`, then concavity + endpoint checks. -/
lemma one_add_mul_log_add_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u) ≤ 2 * u ^ 2 :=
  one_add_mul_log_add_le' u (by linarith) hu1

/-- `1 - √(1-v) ≥ v/2` for `v ∈ [0,1]`. -/
lemma half_le_one_sub_sqrt_one_sub {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    v / 2 ≤ 1 - Real.sqrt (1 - v) := by
  have h1 : 1 - v ≤ (1 - v / 2) ^ 2 := by nlinarith
  have h2 : Real.sqrt (1 - v) ≤ Real.sqrt ((1 - v / 2) ^ 2) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by linarith)] at h2
  linarith

/-- `m·x·log(m·x) = m·(x·log x) + m·x·log m` for `m > 0`, `x ≥ 0`. -/
private lemma mul_log_mul {m x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) :
    m * x * Real.log (m * x) = m * (x * Real.log x) + m * x * Real.log m := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; simp
  · rw [Real.log_mul (ne_of_gt hm) (ne_of_gt h)]; ring

/-- The two-point entropy in the parametrization `α² = m(1+u)`, `β² = m(1-u)`
is `m/2` times the 1-D expression, hence at most `m·u²`. -/
private lemma two_point_key {m u : ℝ} (hm : 0 < m) (hu0 : -1 ≤ u) (hu1 : u ≤ 1) :
    (m * (1 + u) * Real.log (m * (1 + u))
        + m * (1 - u) * Real.log (m * (1 - u))) / 2 - m * Real.log m
      ≤ m * u ^ 2 := by
  have h1 : (0:ℝ) ≤ 1 + u := by linarith
  have h2 : (0:ℝ) ≤ 1 - u := by linarith
  have key : (m * (1 + u) * Real.log (m * (1 + u))
        + m * (1 - u) * Real.log (m * (1 - u))) / 2 - m * Real.log m
      = m / 2 * ((1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u)) := by
    rw [mul_log_mul hm h1, mul_log_mul hm h2]
    ring
  rw [key]
  have h3 := mul_le_mul_of_nonneg_left (one_add_mul_log_add_le' u hu0 hu1)
    (by linarith : (0:ℝ) ≤ m / 2)
  linarith

/-- **Two-point log-Sobolev inequality** (with constant `1` in this
normalization): for `α, β ≥ 0`,
`(α²·log α² + β²·log β²)/2 - (α²+β²)/2 · log((α²+β²)/2) ≤ (α - β)²`. -/
theorem two_point_LSI {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (α ^ 2 * Real.log (α ^ 2) + β ^ 2 * Real.log (β ^ 2)) / 2
        - (α ^ 2 + β ^ 2) / 2 * Real.log ((α ^ 2 + β ^ 2) / 2)
      ≤ (α - β) ^ 2 := by
  rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ (α ^ 2 + β ^ 2) / 2) with h0 | h0
  · have hs : α ^ 2 = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    have ht : β ^ 2 = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    have ha0 : α = 0 := by
      have := sq_eq_zero_iff.mp hs; simpa using this
    have hb0 : β = 0 := by
      have := sq_eq_zero_iff.mp ht; simpa using this
    subst ha0; subst hb0
    norm_num
  · have hsum : (0:ℝ) < α ^ 2 + β ^ 2 := by linarith
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (α ^ 2 - β ^ 2) / (α ^ 2 + β ^ 2) := ⟨_, rfl⟩
    obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (α ^ 2 + β ^ 2) / 2 := ⟨_, rfl⟩
    have hm : 0 < m := by rw [hmdef]; linarith
    have ha : m * (1 + u) = α ^ 2 := by
      rw [hmdef, hu]; field_simp; ring
    have hb : m * (1 - u) = β ^ 2 := by
      rw [hmdef, hu]; field_simp; ring
    have hu0 : -1 ≤ u := by
      have h2 : (0:ℝ) ≤ (2 * α ^ 2) / (α ^ 2 + β ^ 2) :=
        div_nonneg (by positivity) hsum.le
      have h3 : (α ^ 2 - β ^ 2) / (α ^ 2 + β ^ 2) + 1
          = (2 * α ^ 2) / (α ^ 2 + β ^ 2) := by field_simp; ring
      rw [hu]; linarith
    have hu1 : u ≤ 1 := by
      have h2 : (0:ℝ) ≤ (2 * β ^ 2) / (α ^ 2 + β ^ 2) :=
        div_nonneg (by positivity) hsum.le
      have h3 : 1 - (α ^ 2 - β ^ 2) / (α ^ 2 + β ^ 2)
          = (2 * β ^ 2) / (α ^ 2 + β ^ 2) := by field_simp; ring
      rw [hu]; linarith
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    have habs : α * β = m * Real.sqrt (1 - u ^ 2) := by
      have hsq : (α * β) ^ 2 = (m * Real.sqrt (1 - u ^ 2)) ^ 2 := by
        have hs2 : (m * Real.sqrt (1 - u ^ 2)) ^ 2 = m ^ 2 * (1 - u ^ 2) := by
          rw [mul_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - u ^ 2)]
        rw [hs2]
        calc (α * β) ^ 2 = α ^ 2 * β ^ 2 := by ring
          _ = (m * (1 + u)) * (m * (1 - u)) := by rw [ha, hb]
          _ = m ^ 2 * (1 - u ^ 2) := by ring
      have h1 : α * β = Real.sqrt ((α * β) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      rw [h1, hsq, Real.sqrt_sq (mul_nonneg hm.le (Real.sqrt_nonneg _))]
    have hrhs : (α - β) ^ 2 = 2 * m - 2 * (m * Real.sqrt (1 - u ^ 2)) := by
      have e : (α - β) ^ 2 = α ^ 2 + β ^ 2 - 2 * (α * β) := by ring
      rw [e, habs, ← ha, ← hb]
      ring
    have hgoalL : (α ^ 2 * Real.log (α ^ 2) + β ^ 2 * Real.log (β ^ 2)) / 2
          - (α ^ 2 + β ^ 2) / 2 * Real.log ((α ^ 2 + β ^ 2) / 2)
        = (m * (1 + u) * Real.log (m * (1 + u))
            + m * (1 - u) * Real.log (m * (1 - u))) / 2 - m * Real.log m := by
      rw [← ha, ← hb, show m * (1 + u) + m * (1 - u) = 2 * m from by ring,
        show 2 * m / 2 = m from by ring]
    rw [hrhs, hgoalL]
    have hkey := two_point_key hm hu0 hu1
    have hhalf := half_le_one_sub_sqrt_one_sub (v := u ^ 2) (by positivity) hu2
    have h4 := mul_le_mul_of_nonneg_left hhalf (by linarith : (0:ℝ) ≤ 2 * m)
    linarith

variable {n : ℕ}

/-- Linearity of `unifE` over a finite sum. -/
private lemma unifE_sum {m : ℕ} (F : Fin m → Cube n → ℝ) :
    ∑ i, unifE (fun x => F i x) = unifE (fun x => ∑ i, F i x) := by
  simp only [unifE]
  rw [← Finset.sum_div, Finset.sum_comm]

/-- **Log-Sobolev inequality on the cube** (constant 4 vs Gross's 2; the
constant is irrelevant for [LGF]): for `h ≥ 0`,
`Ent_λ(h) ≤ 𝔼_λ ∑_i (√(h(σ_i x)) - √(h x))²  (= 4·𝔈(√h,√h))`.
Used in [C, proof of Lemma 4] via `Ent(h_s) ≲ 𝔈(√h_s, √h_s)`. -/
theorem cube_LSI {h : Cube n → ℝ} (hh : ∀ x, 0 ≤ h x) :
    entUnif h
      ≤ unifE (fun x => ∑ i,
          (Real.sqrt (h (flipCoord i x)) - Real.sqrt (h x)) ^ 2) := by
  refine (entUnif_le_sum_pairEnt hh).trans ?_
  rw [unifE_sum (fun (i : Fin n) (x : Cube n) => pairEnt i h x)]
  refine unifE_mono fun x => ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have key := two_point_LSI (Real.sqrt_nonneg (h x))
    (Real.sqrt_nonneg (h (flipCoord i x)))
  rw [Real.sq_sqrt (hh x), Real.sq_sqrt (hh (flipCoord i x))] at key
  rw [show (Real.sqrt (h (flipCoord i x)) - Real.sqrt (h x)) ^ 2
        = (Real.sqrt (h x) - Real.sqrt (h (flipCoord i x))) ^ 2 from by ring]
  exact key

end Talagrand
