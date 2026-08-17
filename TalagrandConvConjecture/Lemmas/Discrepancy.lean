import TalagrandConvConjecture.Lemmas.Quantities
import TalagrandConvConjecture.Lemmas.ScoreEnergy

/-!
# Localized total variation distance [LGF Lemma 3.3]

For `A ⊆ ℰ_θ`:
`D_A ≲ κ_a Λ_a √(𝒮_A ℙ(A)) + κ_a Λ_a² 𝒮_A`.

Proof [LGF §4.1] (localized Duhamel–bridge method of [XZ §3]): for an
indicator test `φ`, set `U_t(x,y) = ∑_ζ H_t^ζ(x)·q_t^ζ(x,y)`. Then
`(∂_t + 𝓛̄⁰_t)U = 0` and `U_{T_o}(x,y) = φ(y)`, so the glued Duhamel identity
gives `𝔼[1_A(φ(W_{T_o}) - φ(V_{T_o}))] = 𝔼[1_A ∫_θ^τ 𝓑_t U_t dt]`
[LGF eq (4.10)]. The pointwise bound
`|𝓑_t U_t| ≲ √κ_a Λ_a (δ̄²∑S_i²)^{1/2} Γ_t^{1/2}` [LGF eq (4.17)] with
`Γ_t = ∑_ζ H^ζ ∑_i λ^ζ_i(a_t²+b_t²)|∂_iφ(m_t)|²`, Cauchy–Schwarz, the
level-one inequality + bridge `b`-control for `Ψ_b` [LGF eq (4.19)], and the
`(q^ζ)²`-Dynkin/carré-du-champ argument for `Ψ_a` [LGF eq (4.20)-(4.21)]
close the estimate `Y_A ≲ κ_a ℙ(A) + κ_a Λ_a² 𝒮_A` [LGF eq (4.21)].
-/

namespace Talagrand

/-! ### Elementary discrete Cauchy–Schwarz helpers

These are stated over an arbitrary `Finset` so that they can be reused for the
sums over coordinates `i`, over terminal points `ζ` (with the weights `H^ζ`),
over the state space, and over starting points. -/

/-- Cauchy–Schwarz for finite sums of reals. -/
private lemma cs_sq {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 := by
  have hA : (0 : ℝ) ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have key : ∀ lam : ℝ, 0 ≤ lam ^ 2 * (∑ i ∈ s, f i ^ 2)
      - 2 * lam * (∑ i ∈ s, f i * g i) + ∑ i ∈ s, g i ^ 2 := by
    intro lam
    have hnn : (0 : ℝ) ≤ ∑ i ∈ s, (lam * f i - g i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hpt : ∀ i : ι, (lam * f i - g i) ^ 2
        = lam ^ 2 * f i ^ 2 - 2 * lam * (f i * g i) + g i ^ 2 := by
      intro i; ring
    rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hnn
    exact hnn
  rcases eq_or_lt_of_le hA with h | h
  · have hf : ∀ i ∈ s, f i = 0 := by
      intro i hi
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ s) => sq_nonneg (f j))).mp h.symm i hi
      exact sq_eq_zero_iff.mp h0
    have hC : ∑ i ∈ s, f i * g i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hf i hi, zero_mul]
    rw [hC, ← h]
    simp
  · have hA' : (∑ i ∈ s, f i ^ 2) ≠ 0 := ne_of_gt h
    have hk := key ((∑ i ∈ s, f i * g i) / (∑ i ∈ s, f i ^ 2))
    have hre : ((∑ i ∈ s, f i * g i) / (∑ i ∈ s, f i ^ 2)) ^ 2 * (∑ i ∈ s, f i ^ 2)
        - 2 * ((∑ i ∈ s, f i * g i) / (∑ i ∈ s, f i ^ 2)) * (∑ i ∈ s, f i * g i)
        + ∑ i ∈ s, g i ^ 2
        = (∑ i ∈ s, g i ^ 2) - (∑ i ∈ s, f i * g i) ^ 2 / (∑ i ∈ s, f i ^ 2) := by
      field_simp
      ring
    rw [hre] at hk
    have hdiv : (∑ i ∈ s, f i * g i) ^ 2 / (∑ i ∈ s, f i ^ 2) ≤ ∑ i ∈ s, g i ^ 2 := by
      linarith
    calc (∑ i ∈ s, f i * g i) ^ 2
        = (∑ i ∈ s, f i * g i) ^ 2 / (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, f i ^ 2) := by
          field_simp
      _ ≤ (∑ i ∈ s, g i ^ 2) * (∑ i ∈ s, f i ^ 2) :=
          mul_le_mul_of_nonneg_right hdiv h.le
      _ = (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 := by ring

/-- Cauchy–Schwarz in square-root form, for nonnegative summands. -/
private lemma sum_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, f i * g i
      ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have hA : (0 : ℝ) ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hC : (0 : ℝ) ≤ ∑ i ∈ s, f i * g i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hf i hi) (hg i hi)
  calc ∑ i ∈ s, f i * g i = Real.sqrt ((∑ i ∈ s, f i * g i) ^ 2) :=
        (Real.sqrt_sq hC).symm
    _ ≤ Real.sqrt ((∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2) :=
        Real.sqrt_le_sqrt (cs_sq s f g)
    _ = Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) :=
        Real.sqrt_mul hA _

/-- Jensen/Cauchy–Schwarz against a nonnegative weight:
`(∑ p f)² ≤ (∑ p)(∑ p f²)`. -/
private lemma sq_weighted_le {ι : Type*} (s : Finset ι) (p f : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    (∑ i ∈ s, p i * f i) ^ 2 ≤ (∑ i ∈ s, p i) * ∑ i ∈ s, p i * f i ^ 2 := by
  have h := cs_sq s (fun i => Real.sqrt (p i)) (fun i => Real.sqrt (p i) * f i)
  have e1 : ∀ i ∈ s, Real.sqrt (p i) * (Real.sqrt (p i) * f i) = p i * f i := by
    intro i hi; rw [← mul_assoc, Real.mul_self_sqrt (hp i hi)]
  have e2 : ∀ i ∈ s, Real.sqrt (p i) ^ 2 = p i := fun i hi => Real.sq_sqrt (hp i hi)
  have e3 : ∀ i ∈ s, (Real.sqrt (p i) * f i) ^ 2 = p i * f i ^ 2 := by
    intro i hi; rw [mul_pow, Real.sq_sqrt (hp i hi)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
  exact h

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- The bridge average `U_t(x,y) = ∑_ζ H_t^ζ(x) q_t^ζ(x,y)` [LGF §4.1]. -/
noncomputable def Utest (φ : Cube n → ℝ) (t : ℝ) (x y : Cube n) : ℝ :=
  ∑ ζ, D.Hlik t ζ x * D.qB φ t ζ x y

/-- The bridge energy density
`Γ_t(x,y) = ∑_ζ H_t^ζ(x)∑_i λ_{t,i}^ζ(x)(a_t²+b_t²)|∂_iφ(m_t)|²`
[LGF eq (4.17)]. -/
noncomputable def Gam (φ : Cube n → ℝ) (t : ℝ) (x y : Cube n) : ℝ :=
  ∑ ζ, D.Hlik t ζ x * ∑ i, D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
    * dmext φ i (D.mB t x y ζ) ^ 2

/-! ### Terminal values of the bridge coefficients -/

section terminal

/-- `γ_{T_o} = 1`. -/
private lemma gam_obsT : gam obsT = 1 := by
  simp [gam]

/-- `a_{T_o} = 1`. -/
private lemma aB_obsT : D.aB obsT = 1 := by
  have h0 := D.ha0
  have h1 := D.ha1
  have ha : (1 : ℝ) - D.a ^ 2 ≠ 0 := by nlinarith
  simp only [aB, gam_obsT, one_pow, mul_one, one_mul]
  exact div_self ha

/-- `b_{T_o} = 0`. -/
private lemma bB_obsT : D.bB obsT = 0 := by
  simp [bB, gam_obsT]

/-- `m_{T_o}(x,y,ζ) = y`. -/
private lemma mB_obsT (x y ζ : Cube n) :
    D.mB obsT x y ζ = fun i => toR (y i) := by
  funext i
  simp [mB, D.aB_obsT, D.bB_obsT]

/-- `q_{T_o}^ζ(x,y) = φ(y)`. -/
private lemma qB_obsT (φ : Cube n → ℝ) (ζ x y : Cube n) :
    D.qB φ obsT ζ x y = φ y := by
  rw [qB, D.mB_obsT x y ζ, mext_toR]

end terminal

/-- Terminal value: `U_{T_o}(x,y) = φ(y)`. -/
theorem Utest_obsT (φ : Cube n → ℝ) (x y : Cube n) :
    D.Utest φ obsT x y = φ y := by
  simp only [Utest, D.qB_obsT φ _ x y, ← Finset.sum_mul]
  rw [D.sum_Hlik D.obsT_lt_T.le x, one_mul]

/-- Space-time harmonicity of `U` for the synchronized joint generator
[LGF §4.1]: `∂_t U_t(x,y) = -½∑_i Y_i(t,x)·Δ_i^{xy}U_t(x,y)`. -/
theorem hasDerivAt_Utest (φ : Cube n → ℝ) {t : ℝ} (ht : t < D.T)
    (x y : Cube n) :
    HasDerivAt (fun t => D.Utest φ t x y)
      (-(∑ i, D.Y t i x *
          (D.Utest φ t (flipCoord i x) (flipCoord i y) - D.Utest φ t x y) / 2))
      t := by
  -- `H^ζ(x)·λ_{t,i}^ζ(x) = H^ζ(σ_i x)·Y_i(t,x)` [LGF eq (4.5)]
  have hlam : ∀ (ζ : Cube n) (i : Fin n),
      D.Hlik t ζ x * D.lam t i x ζ = D.Hlik t ζ (flipCoord i x) * D.Y t i x := by
    intro ζ i
    have h0 : D.Hlik t ζ x ≠ 0 := (D.Hlik_pos ht ζ x).ne'
    rw [← D.Hlik_flipCoord_mul_Y ht i ζ x]
    field_simp
  -- per-`ζ` product rule plus the algebraic recombination
  have key : ∀ ζ : Cube n,
      HasDerivAt (fun t => D.Hlik t ζ x * D.qB φ t ζ x y)
        (-(∑ i, D.Y t i x *
            (D.Hlik t ζ (flipCoord i x) * D.qB φ t ζ (flipCoord i x) (flipCoord i y)
              - D.Hlik t ζ x * D.qB φ t ζ x y) / 2)) t := by
    intro ζ
    have hH := D.hasDerivAt_Hlik ht ζ x
    have hq := D.hasDerivAt_qB φ (ne_of_lt ht) ζ x y
    have hstep : ∀ i : Fin n,
        D.Y t i x * (D.Hlik t ζ (flipCoord i x) - D.Hlik t ζ x) / 2 * D.qB φ t ζ x y
          + D.Hlik t ζ x *
            (D.lam t i x ζ *
              (D.qB φ t ζ (flipCoord i x) (flipCoord i y) - D.qB φ t ζ x y) / 2)
        = D.Y t i x *
            (D.Hlik t ζ (flipCoord i x) * D.qB φ t ζ (flipCoord i x) (flipCoord i y)
              - D.Hlik t ζ x * D.qB φ t ζ x y) / 2 := by
      intro i
      linear_combination
        ((D.qB φ t ζ (flipCoord i x) (flipCoord i y) - D.qB φ t ζ x y) / 2) * hlam ζ i
    have hEq :
        -(D.revGen t (fun w => D.Hlik t ζ w) x) * D.qB φ t ζ x y
          + D.Hlik t ζ x *
            -(∑ i, D.lam t i x ζ *
                (D.qB φ t ζ (flipCoord i x) (flipCoord i y) - D.qB φ t ζ x y) / 2)
        = -(∑ i, D.Y t i x *
            (D.Hlik t ζ (flipCoord i x) * D.qB φ t ζ (flipCoord i x) (flipCoord i y)
              - D.Hlik t ζ x * D.qB φ t ζ x y) / 2) := by
      have hre : ∀ S P : ℝ,
          -S * D.qB φ t ζ x y + D.Hlik t ζ x * -P
            = -(S * D.qB φ t ζ x y + D.Hlik t ζ x * P) := by
        intro S P; ring
      rw [revGen, hre, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => hstep i)
    rw [← hEq]
    exact hH.mul hq
  -- reassemble the `ζ`-sum
  have hswap : ∀ i : Fin n,
      D.Y t i x * (D.Utest φ t (flipCoord i x) (flipCoord i y) - D.Utest φ t x y) / 2
        = ∑ ζ : Cube n, D.Y t i x *
            (D.Hlik t ζ (flipCoord i x) * D.qB φ t ζ (flipCoord i x) (flipCoord i y)
              - D.Hlik t ζ x * D.qB φ t ζ x y) / 2 := by
    intro i
    rw [Utest, Utest, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
  have hfin :
      (∑ ζ : Cube n, -(∑ i, D.Y t i x *
          (D.Hlik t ζ (flipCoord i x) * D.qB φ t ζ (flipCoord i x) (flipCoord i y)
            - D.Hlik t ζ x * D.qB φ t ζ x y) / 2))
        = -(∑ i, D.Y t i x *
            (D.Utest φ t (flipCoord i x) (flipCoord i y) - D.Utest φ t x y) / 2) := by
    have hneg : ∀ g : Cube n → ℝ, ∑ ζ : Cube n, -(g ζ) = -∑ ζ : Cube n, g ζ := by
      intro g; simp
    rw [hneg]
    refine congrArg Neg.neg ?_
    rw [Finset.sum_congr rfl fun i _ => hswap i, Finset.sum_comm]
  have hfun : (fun s => D.Utest φ s x y)
      = ∑ ζ : Cube n, (fun s => D.Hlik s ζ x * D.qB φ s ζ x y) := by
    funext s
    simp only [Finset.sum_apply, Utest]
  rw [← hfin, hfun]
  exact HasDerivAt.sum (u := (Finset.univ : Finset (Cube n))) fun ζ _ => key ζ

/-- Diagonal transport: `g(t,x) := U_t(x,x)` is space-time harmonic for the
reverse generator (synchronized flips preserve the diagonal), with
`g(T_o,·) = φ`; hence by the `V`-marginal property,
`𝔼_{x₀}[φ(V_{T_o})] = U_θ(x₀,x₀)` [LGF eq (4.10) via Lemma 5.1]. -/
theorem term_V_eq_Utest_diag {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) (φ : Cube n → ℝ) :
    ∑ s, c.term s * φ s.1 = D.Utest φ θ x₀ x₀ := by
  have hderiv : ∀ (w : Cube n), ∀ s ∈ Set.Icc θ obsT,
      HasDerivAt (fun t => D.Utest φ t w w)
        (-(D.revGen s (fun v => D.Utest φ s v v) w)) s := by
    intro w s hs
    exact D.hasDerivAt_Utest φ (lt_of_le_of_lt hs.2 D.obsT_lt_T) w w
  have hmarg := D.cflow_V_marginal hθ0 hθ c (fun t w => D.Utest φ t w w)
    (fun w => fun s hs => ((hderiv w s hs).continuousAt).continuousWithinAt)
    (fun w => fun s hs => (hderiv w s hs).hasDerivWithinAt)
  simpa only [D.Utest_obsT φ] using hmarg

/-! ### Ingredients of the pointwise perturbation bound [LGF eq (4.17)] -/

/-- The conditioned power weight `1_{S_i>0} + r_{t,i}^ζ·1_{S_i≤0}`
of [LGF eq (4.11)] (`r_{t,i}^ζ = λ_{t,i}^ζ/Y_i`). -/
private noncomputable def pwt (t : ℝ) (i : Fin n) (x ζ : Cube n) : ℝ :=
  if 0 < D.Sc t i x then 1 else D.lam t i x ζ / D.Y t i x

/-- The bridge coefficient hit by the perturbation: `m_t^{[i]}` on the
`W`-only branch (`Y < 1`), `a_t y_i - b_t x_i y_i ζ_i` on the `V`-only
branch [LGF eq (4.6)-(4.7)]. -/
private noncomputable def pcf (t : ℝ) (i : Fin n) (x y ζ : Cube n) : ℝ :=
  if 0 < D.Sc t i x then D.mB t x y ζ i
  else D.aB t * toR (y i) - D.bB t * toR (x i) * toR (y i) * toR (ζ i)

/-- The `ζ`-averaged modulus appearing in [LGF eq (4.17)] after the
`S_i`-factor has been pulled out. -/
private noncomputable def pgm (φ : Cube n → ℝ) (ℓ θ t : ℝ) (x₀ : Cube n)
    (i : Fin n) (x y : Cube n) : ℝ :=
  ∑ ζ, D.Hlik t ζ x *
    (2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
      * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|)

/-- `|a_t y_i ± b_t x_i y_i ζ_i| ≤ a_t + b_t`. -/
private lemma abs_pcf_le {t : ℝ} (ht : t ≤ obsT) (i : Fin n) (x y ζ : Cube n) :
    |D.pcf t i x y ζ| ≤ D.aB t + D.bB t := by
  have haB := D.aB_nonneg ht
  have hbB := D.bB_nonneg ht
  have h1 : |D.aB t * toR (y i)| = D.aB t := by
    rw [abs_mul, abs_toR, mul_one, abs_of_nonneg haB]
  have h2 : |D.bB t * toR (x i) * toR (y i) * toR (ζ i)| = D.bB t := by
    rw [abs_mul, abs_mul, abs_mul, abs_toR, abs_toR, abs_toR, abs_of_nonneg hbB]
    ring
  have hA1 := neg_abs_le (D.aB t * toR (y i))
  have hA2 := le_abs_self (D.aB t * toR (y i))
  have hB1 := neg_abs_le (D.bB t * toR (x i) * toR (y i) * toR (ζ i))
  have hB2 := le_abs_self (D.bB t * toR (x i) * toR (y i) * toR (ζ i))
  rw [h1] at hA1 hA2
  rw [h2] at hB1 hB2
  by_cases hs : 0 < D.Sc t i x
  · simp only [pcf, mB, if_pos hs]
    rw [abs_le]
    constructor <;> linarith
  · simp only [pcf, if_neg hs]
    rw [abs_le]
    constructor <;> linarith

/-- Nonnegativity of `pgm`. -/
private lemma pgm_nonneg {ℓ θ t : ℝ} (ht : t ≤ obsT) (hT : t ≤ D.T)
    (φ : Cube n → ℝ) (x₀ : Cube n) (i : Fin n) (x y : Cube n) :
    0 ≤ D.pgm φ ℓ θ t x₀ i x y := by
  refine Finset.sum_nonneg fun ζ _ => mul_nonneg (D.Hlik_nonneg hT ζ x) ?_
  have haB := D.aB_nonneg ht
  have hbB := D.bB_nonneg ht
  have h1 : (0 : ℝ) ≤ 2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ| := by
    have := abs_nonneg (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ)
    linarith
  have h2 : (0 : ℝ) ≤ 2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
      * (D.aB t + D.bB t) := mul_nonneg h1 (by linarith)
  exact mul_nonneg h2 (abs_nonneg _)

/-- The perturbation applied to `U`, pointwise bound [LGF eq (4.17)]:
for `t ≤ T_o`, `{0,1}`-valued `φ`, and any `x y`,
`|𝓑_t U_t(x,y)| ≤ √8·√κ_a·Λ_a·δ̄·(∑_i S_i(t,x)²)^{1/2}·Γ_t(x,y)^{1/2}`,
where `𝓑_t` is the power perturbation generator [LGF eq (4.3)] with frozen
exponent `δ̄ = dbar ℓ θ x₀`. -/
theorem abs_pert_Utest_le {ℓ θ t : ℝ} (ht0 : θ ≤ t) (ht : t ≤ obsT)
    (hθ : θ ≤ obsT) {x₀ : Cube n} {φ : Cube n → ℝ}
    (hφ : ∀ w, φ w = 0 ∨ φ w = 1) (x y : Cube n) :
    |∑ i, (if D.Y t i x < 1 then
        (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
          (D.Utest φ t x (flipCoord i y) - D.Utest φ t x y)
      else
        -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2) *
          (D.Utest φ t (flipCoord i x) (flipCoord i y)
            - D.Utest φ t (flipCoord i x) y))|
      ≤ Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
        * Real.sqrt (∑ i, D.Sc t i x ^ 2) * Real.sqrt (D.Gam φ t x y) := by
  have htT : t < D.T := lt_of_le_of_lt ht D.obsT_lt_T
  have hk1 : 1 < kappa D.a := one_lt_kappa D.ha0 D.ha1
  have hk0 : (0 : ℝ) ≤ kappa D.a := by linarith
  have hLam0 : (0 : ℝ) ≤ Lam D.a := le_trans zero_le_one (one_le_Lam D.ha0 D.ha1)
  have hd0 : (0 : ℝ) ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
  have haB := D.aB_nonneg ht
  have hbB := D.bB_nonneg ht
  -- (A) rewrite the `i`-th perturbation term
  have hA : ∀ i : Fin n,
      (if D.Y t i x < 1 then
          (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
            (D.Utest φ t x (flipCoord i y) - D.Utest φ t x y)
        else
          -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2) *
            (D.Utest φ t (flipCoord i x) (flipCoord i y)
              - D.Utest φ t (flipCoord i x) y))
        = D.Sc t i x * ∑ ζ : Cube n, D.Hlik t ζ x *
            (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ
              * (-2 * D.pcf t i x y ζ) * dmext φ i (D.mB t x y ζ)) := by
    intro i
    have hYpos : 0 < D.Y t i x := D.Y_pos htT.le i x
    by_cases hY : D.Y t i x < 1
    · have hs : 0 < D.Sc t i x := by simp only [Sc]; linarith
      rw [if_pos hY]
      have hcoef : (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2
          = powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.Sc t i x := by
        simp only [Sc]; exact one_sub_rpow_eq hYpos hY
      have hdiff : D.Utest φ t x (flipCoord i y) - D.Utest φ t x y
          = ∑ ζ : Cube n, D.Hlik t ζ x *
              (-2 * D.mB t x y ζ i * dmext φ i (D.mB t x y ζ)) := by
        rw [Utest, Utest, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun ζ _ => by
          rw [← mul_sub, D.qB_flip_y_sub φ t ζ x y i]
      rw [hcoef, hdiff, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ζ _ => ?_
      simp only [pwt, pcf, if_pos hs]
      ring
    · have hY' : 1 ≤ D.Y t i x := not_lt.mp hY
      have hs : ¬ (0 < D.Sc t i x) := by
        simp only [Sc]; push_neg; linarith
      rw [if_neg hY]
      have hdiff : D.Utest φ t (flipCoord i x) (flipCoord i y)
            - D.Utest φ t (flipCoord i x) y
          = ∑ ζ : Cube n, D.Hlik t ζ (flipCoord i x) *
              (-2 * (D.aB t * toR (y i)
                  - D.bB t * toR (x i) * toR (y i) * toR (ζ i))
                * dmext φ i (D.mB t x y ζ)) := by
        rw [Utest, Utest, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun ζ _ => by
          rw [← mul_sub, D.qB_flip_y_flip_x_sub φ t ζ x y i]
      have hHflip : ∀ ζ : Cube n, D.Hlik t ζ (flipCoord i x)
          = D.Hlik t ζ x * (D.lam t i x ζ / D.Y t i x) := by
        intro ζ
        have hY0 : D.Y t i x ≠ 0 := ne_of_gt hYpos
        have h0 : D.Hlik t ζ x ≠ 0 := (D.Hlik_pos htT ζ x).ne'
        rw [← D.Hlik_flipCoord_mul_Y htT i ζ x]
        field_simp
      rcases eq_or_lt_of_le hY' with hY1 | hY1
      · have hSc : D.Sc t i x = 0 := by simp only [Sc, ← hY1]; ring
        rw [hSc, ← hY1]
        simp
      · have hcoef : -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2)
            = powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.Sc t i x := by
          simp only [Sc]
          rw [rpow_sub_eq hY1]
          ring
        rw [hcoef, hdiff, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ζ _ => ?_
        rw [hHflip ζ]
        simp only [pwt, pcf, if_neg hs]
        ring
  -- (B) pointwise modulus bound
  have hB : ∀ i : Fin n,
      |(if D.Y t i x < 1 then
          (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
            (D.Utest φ t x (flipCoord i y) - D.Utest φ t x y)
        else
          -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2) *
            (D.Utest φ t (flipCoord i x) (flipCoord i y)
              - D.Utest φ t (flipCoord i x) y))|
        ≤ |D.Sc t i x| * D.pgm φ ℓ θ t x₀ i x y := by
    intro i
    rw [hA i, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun ζ _ => ?_
    have hH := D.Hlik_nonneg htT.le ζ x
    have hpc := D.abs_pcf_le ht i x y ζ
    have hn1 : (0 : ℝ) ≤ |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ| :=
      abs_nonneg _
    have hn2 : (0 : ℝ) ≤ |dmext φ i (D.mB t x y ζ)| := abs_nonneg _
    rw [abs_mul, abs_of_nonneg hH]
    refine mul_le_mul_of_nonneg_left ?_ hH
    have hexp : |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ
          * (-2 * D.pcf t i x y ζ) * dmext φ i (D.mB t x y ζ)|
        = |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
          * (2 * |D.pcf t i x y ζ|) * |dmext φ i (D.mB t x y ζ)| := by
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
    rw [hexp]
    calc |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
            * (2 * |D.pcf t i x y ζ|) * |dmext φ i (D.mB t x y ζ)|
        ≤ |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
            * (2 * (D.aB t + D.bB t)) * |dmext φ i (D.mB t x y ζ)| := by
          refine mul_le_mul_of_nonneg_right ?_ hn2
          refine mul_le_mul_of_nonneg_left ?_ hn1
          linarith
      _ = 2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
            * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)| := by ring
  -- (C) the conditioned-power / bridge-coefficient bound on `pgm`
  have hC : ∀ i : Fin n, D.pgm φ ℓ θ t x₀ i x y ^ 2
      ≤ 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
          ∑ ζ : Cube n, D.Hlik t ζ x *
            (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2) := by
    intro i
    have hw := sq_weighted_le (Finset.univ : Finset (Cube n)) (fun ζ => D.Hlik t ζ x)
      (fun ζ => 2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
        * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|)
      (fun ζ _ => D.Hlik_nonneg htT.le ζ x)
    rw [D.sum_Hlik htT.le x, one_mul] at hw
    refine le_trans hw ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ζ _ => ?_
    have hH := D.Hlik_nonneg htT.le ζ x
    have hcpb := D.conditioned_power_bound (ℓ := ℓ) (θ := θ) (x₀ := x₀) ht i x ζ
    have hcpb' : (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
        ≤ kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ := by
      simpa only [pwt] using hcpb
    have hab2 : (D.aB t + D.bB t) ^ 2 ≤ 2 * (D.aB t ^ 2 + D.bB t ^ 2) := by
      nlinarith [sq_nonneg (D.aB t - D.bB t)]
    have hP0 : (0 : ℝ)
        ≤ (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2 := sq_nonneg _
    have hQ0 : (0 : ℝ) ≤ (D.aB t + D.bB t) ^ 2 := sq_nonneg _
    have hR0 : (0 : ℝ) ≤ dmext φ i (D.mB t x y ζ) ^ 2 := sq_nonneg _
    have hP'0 : (0 : ℝ)
        ≤ kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ :=
      le_trans hP0 hcpb'
    have hPQ : (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
          * (D.aB t + D.bB t) ^ 2
        ≤ (kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ)
          * (2 * (D.aB t ^ 2 + D.bB t ^ 2)) :=
      mul_le_mul hcpb' hab2 hQ0 hP'0
    have hsqexp : (2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
          * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|) ^ 2
        = 4 * ((powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
            * (D.aB t + D.bB t) ^ 2) * dmext φ i (D.mB t x y ζ) ^ 2 := by
      have e1 : |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ| ^ 2
          = (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2 := sq_abs _
      have e2 : |dmext φ i (D.mB t x y ζ)| ^ 2
          = dmext φ i (D.mB t x y ζ) ^ 2 := sq_abs _
      calc (2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
              * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|) ^ 2
          = 4 * (|powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ| ^ 2
              * (D.aB t + D.bB t) ^ 2) * |dmext φ i (D.mB t x y ζ)| ^ 2 := by ring
        _ = _ := by rw [e1, e2]
    rw [hsqexp]
    have h4 := mul_le_mul_of_nonneg_left hPQ (by norm_num : (0 : ℝ) ≤ 4)
    have h5 := mul_le_mul_of_nonneg_right h4 hR0
    have hfin : 4 * ((powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
          * (D.aB t + D.bB t) ^ 2) * dmext φ i (D.mB t x y ζ) ^ 2
        ≤ 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
            (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2) := by
      calc 4 * ((powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
              * (D.aB t + D.bB t) ^ 2) * dmext φ i (D.mB t x y ζ) ^ 2
          ≤ 4 * ((kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ)
              * (2 * (D.aB t ^ 2 + D.bB t ^ 2))) * dmext φ i (D.mB t x y ζ) ^ 2 := h5
        _ = _ := by ring
    calc D.Hlik t ζ x * (4 * ((powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)
            * D.pwt t i x ζ) ^ 2 * (D.aB t + D.bB t) ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2)
        ≤ D.Hlik t ζ x * (8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
            (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2)) := mul_le_mul_of_nonneg_left hfin hH
      _ = 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
            (D.Hlik t ζ x * (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2)) := by ring
  -- (D) sum over coordinates: the energy density `Γ` appears
  have hDsum : ∑ i, D.pgm φ ℓ θ t x₀ i x y ^ 2
      ≤ 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.Gam φ t x y := by
    calc ∑ i, D.pgm φ ℓ θ t x₀ i x y ^ 2
        ≤ ∑ i, 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
            ∑ ζ : Cube n, D.Hlik t ζ x *
              (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
                * dmext φ i (D.mB t x y ζ) ^ 2) :=
          Finset.sum_le_sum fun i _ => hC i
      _ = 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
            ∑ i, ∑ ζ : Cube n, D.Hlik t ζ x *
              (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
                * dmext φ i (D.mB t x y ζ) ^ 2) := by rw [Finset.mul_sum]
      _ = 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.Gam φ t x y := by
          refine congrArg _ ?_
          rw [Gam, Finset.sum_comm]
          exact Finset.sum_congr rfl fun ζ _ => by rw [Finset.mul_sum]
  -- (E) assemble
  have h8k : (0 : ℝ) ≤ 8 * kappa D.a := by linarith
  have hA1 : (0 : ℝ) ≤ 8 * kappa D.a * Lam D.a ^ 2 := mul_nonneg h8k (sq_nonneg _)
  have hA2 : (0 : ℝ) ≤ 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 :=
    mul_nonneg hA1 (sq_nonneg _)
  have hsqrt : Real.sqrt (8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2
        * D.Gam φ t x y)
      = Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
        * Real.sqrt (D.Gam φ t x y) := by
    rw [Real.sqrt_mul hA2, Real.sqrt_mul hA1, Real.sqrt_mul h8k,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_sq hLam0, Real.sqrt_sq hd0]
  calc |∑ i, (if D.Y t i x < 1 then
          (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
            (D.Utest φ t x (flipCoord i y) - D.Utest φ t x y)
        else
          -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2) *
            (D.Utest φ t (flipCoord i x) (flipCoord i y)
              - D.Utest φ t (flipCoord i x) y))|
      ≤ ∑ i, |(if D.Y t i x < 1 then
          (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
            (D.Utest φ t x (flipCoord i y) - D.Utest φ t x y)
        else
          -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2) *
            (D.Utest φ t (flipCoord i x) (flipCoord i y)
              - D.Utest φ t (flipCoord i x) y))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |D.Sc t i x| * D.pgm φ ℓ θ t x₀ i x y :=
        Finset.sum_le_sum fun i _ => hB i
    _ ≤ Real.sqrt (∑ i, |D.Sc t i x| ^ 2)
          * Real.sqrt (∑ i, D.pgm φ ℓ θ t x₀ i x y ^ 2) :=
        sum_le_sqrt_mul_sqrt _ _ _ (fun i _ => abs_nonneg _)
          (fun i _ => D.pgm_nonneg ht htT.le φ x₀ i x y)
    _ = Real.sqrt (∑ i, D.Sc t i x ^ 2)
          * Real.sqrt (∑ i, D.pgm φ ℓ θ t x₀ i x y ^ 2) := by
        simp only [sq_abs]
    _ ≤ Real.sqrt (∑ i, D.Sc t i x ^ 2)
          * Real.sqrt (8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2
              * D.Gam φ t x y) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hDsum) (Real.sqrt_nonneg _)
    _ = Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
          * Real.sqrt (∑ i, D.Sc t i x ^ 2) * Real.sqrt (D.Gam φ t x y) := by
        rw [hsqrt]; ring

/-- The `Ψ_b` estimate [LGF eq (4.19)]: the `b_t²` part of the bridge energy
is bounded by `κ_a/4` pointwise after the level-one inequality and the
`b`-control (`T_o - θ ≤ 1` supplies the time factor downstream):
for `t ≤ T_o` and `{0,1}`-valued `φ`,
`∑_ζ H^ζ ∑_i λ^ζ_i b_t² |∂_iφ(m_t)|² ≤ κ_a/(4(1-a²))·(1-a²) = κ_a/4`
(stated with the clean constant). -/
theorem bpart_Gam_le {ℓ θ t : ℝ} (ht0 : θ ≤ t) (ht : t ≤ obsT)
    {φ : Cube n → ℝ} (hφ : ∀ w, φ w = 0 ∨ φ w = 1) {x y : Cube n}
    (hT : t ≤ D.T) :
    ∑ ζ, D.Hlik t ζ x * ∑ i, D.lam t i x ζ * D.bB t ^ 2
        * dmext φ i (D.mB t x y ζ) ^ 2
      ≤ kappa D.a / 4 := by
  have h0 := D.ha0
  have h1 := D.ha1
  have hden : (0 : ℝ) < 1 - D.a ^ 2 := by nlinarith
  have hc0 : (0 : ℝ) ≤ D.a ^ 2 / (1 - D.a ^ 2) := by positivity
  have h1a' : (1 : ℝ) - D.a ≠ 0 := by intro h; linarith [h1]
  have hden' : (1 : ℝ) - D.a ^ 2 ≠ 0 := ne_of_gt hden
  have hka : D.a ^ 2 / (1 - D.a ^ 2) ≤ kappa D.a := by
    have hdiff : kappa D.a - D.a ^ 2 / (1 - D.a ^ 2)
        = (1 + 2 * D.a) / (1 - D.a ^ 2) := by
      rw [kappa]
      field_simp
      ring
    have hpos : (0 : ℝ) ≤ (1 + 2 * D.a) / (1 - D.a ^ 2) :=
      div_nonneg (by linarith) hden.le
    linarith
  have hkey : ∀ ζ : Cube n,
      ∑ i, D.lam t i x ζ * D.bB t ^ 2 * dmext φ i (D.mB t x y ζ) ^ 2
        ≤ kappa D.a / 4 := by
    intro ζ
    have hz : ∀ i, |D.mB t x y ζ i| ≤ 1 := fun i => D.abs_mB_le_one ht x y ζ i
    have hstep :
        ∑ i, D.lam t i x ζ * D.bB t ^ 2 * dmext φ i (D.mB t x y ζ) ^ 2
          ≤ ∑ i, D.a ^ 2 / (1 - D.a ^ 2) *
              ((1 - D.mB t x y ζ i ^ 2) * dmext φ i (D.mB t x y ζ) ^ 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hb := D.lam_mul_bB_sq_le ht x y ζ i
      have hd : (0 : ℝ) ≤ dmext φ i (D.mB t x y ζ) ^ 2 := sq_nonneg _
      nlinarith
    have hsum := level_one hφ hz
    have hq := self_sub_sq_le_quarter (mext φ (D.mB t x y ζ))
    calc ∑ i, D.lam t i x ζ * D.bB t ^ 2 * dmext φ i (D.mB t x y ζ) ^ 2
        ≤ ∑ i, D.a ^ 2 / (1 - D.a ^ 2) *
            ((1 - D.mB t x y ζ i ^ 2) * dmext φ i (D.mB t x y ζ) ^ 2) := hstep
      _ = D.a ^ 2 / (1 - D.a ^ 2) *
            ∑ i, (1 - D.mB t x y ζ i ^ 2) * dmext φ i (D.mB t x y ζ) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ D.a ^ 2 / (1 - D.a ^ 2) * (1 / 4) := by
            refine mul_le_mul_of_nonneg_left ?_ hc0
            linarith
      _ ≤ kappa D.a / 4 := by linarith
  calc ∑ ζ, D.Hlik t ζ x *
        ∑ i, D.lam t i x ζ * D.bB t ^ 2 * dmext φ i (D.mB t x y ζ) ^ 2
      ≤ ∑ ζ : Cube n, D.Hlik t ζ x * (kappa D.a / 4) :=
        Finset.sum_le_sum fun ζ _ =>
          mul_le_mul_of_nonneg_left (hkey ζ) (D.Hlik_nonneg hT ζ x)
    _ = kappa D.a / 4 := by rw [← Finset.sum_mul, D.sum_Hlik hT x, one_mul]

/-! ### Stage A: the localized Duhamel identity [LGF eq (4.10)]

`𝔼_{x₀}[φ(W_{T_o})] - 𝔼_{x₀}[φ(V_{T_o})] = ∑_k ∫_cell ⟨π^{alive}, 𝓑U⟩`:
the pairing of the flow with the sector-blind test
`U_t(V-pos, W-pos)` has cell derivative exactly the alive perturbation
(the synchronized parts cancel against the harmonicity of `U`), and the
node transfers are invisible to a sector-blind test. -/

/-- A rate `if`-term with a uniquely determined target collapses. -/
private lemma sum_state_eq' {P : JSt n → Prop} [DecidablePred P] {τ₀ : JSt n}
    (hP : ∀ τ, P τ ↔ τ = τ₀) (r : ℝ) (f : JSt n → ℝ) :
    ∑ τ : JSt n, (if P τ then r else 0) * f τ = r * f τ₀ := by
  classical
  have key : ∀ τ : JSt n,
      (if P τ then r else 0) * f τ = if τ = τ₀ then r * f τ₀ else 0 := by
    intro τ
    by_cases hτ : τ = τ₀
    · rw [if_pos hτ, if_pos ((hP τ).mpr hτ), hτ]
    · rw [if_neg hτ, if_neg (fun hc => hτ ((hP τ).mp hc)), zero_mul]
  simp [key]

/-- Transposed action of a forward matrix against a test function. -/
private lemma fwdOf_transpose_pair' (q : JSt n → JSt n → ℝ) (g : JSt n → ℝ)
    (σ : JSt n) :
    ∑ s, fwdOf q s σ * g s = ∑ s, q σ s * (g s - g σ) := by
  classical
  have h2 : ∑ s, (if s = σ then ∑ s'', q s s'' else 0) * g s
      = (∑ s'', q σ s'') * g σ := by simp
  simp only [fwdOf, sub_mul, Finset.sum_sub_distrib, h2, mul_sub]
  rw [← Finset.sum_mul]

open Classical in
private lemma jrate_apply' (dd : ℝ) (B : Set (Cube n)) (t : ℝ)
    (x y : Cube n) (b : Bool) (τ : JSt n) :
    D.jrate dd B t (x, y, b) τ
      = ∑ i : Fin n,
        ((if τ.1 = flipCoord i x ∧ τ.2.1 = flipCoord i y ∧
              (τ.2.2 = (b && decide (τ.1 ∉ B))) then
            (if b then
              (if D.Y t i x < 1 then D.Y t i x / 2
               else D.Y t i x ^ (1 - dd) / 2)
             else D.Y t i x / 2)
          else 0)
        + (if b ∧ τ.2.2 = true ∧ τ.1 = x ∧ τ.2.1 = flipCoord i y ∧
              D.Y t i x < 1 then
            (1 - D.Y t i x ^ dd) / 2
          else 0)
        + (if b ∧ τ.2.1 = y ∧ τ.1 = flipCoord i x ∧ ¬(D.Y t i x < 1) ∧
              (τ.2.2 = decide (τ.1 ∉ B)) then
            (D.Y t i x - D.Y t i x ^ (1 - dd)) / 2
          else 0)) := by
  obtain ⟨x', y', b'⟩ := τ; rfl

open Classical in
/-- Alive-sector jump pairing, expanded coordinate by coordinate. -/
private lemma jrate_pair_true' (dd : ℝ) (B : Set (Cube n)) (t : ℝ)
    (x y : Cube n) (f : JSt n → ℝ) :
    ∑ τ : JSt n, D.jrate dd B t (x, y, true) τ * f τ
      = ∑ i : Fin n,
        ((if D.Y t i x < 1 then D.Y t i x / 2 else D.Y t i x ^ (1 - dd) / 2)
            * f (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))
        + (if D.Y t i x < 1 then (1 - D.Y t i x ^ dd) / 2 else 0)
            * f (x, flipCoord i y, true)
        + (if D.Y t i x < 1 then 0 else (D.Y t i x - D.Y t i x ^ (1 - dd)) / 2)
            * f (flipCoord i x, y, decide (flipCoord i x ∉ B))) := by
  simp_rw [D.jrate_apply' dd B t x y true, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine sum_state_eq'
      (P := fun τ : JSt n => τ.1 = flipCoord i x ∧ τ.2.1 = flipCoord i y ∧
        (τ.2.2 = (true && decide (τ.1 ∉ B))))
      (τ₀ := (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))) ?_ _ _
    intro τ
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [h1, Bool.true_and] at h3
      exact Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, h3⟩⟩
    · rintro rfl; exact ⟨rfl, rfl, by simp⟩
  · by_cases hY : D.Y t i x < 1
    · rw [if_pos hY]
      refine sum_state_eq'
        (P := fun τ : JSt n => True ∧ τ.2.2 = true ∧ τ.1 = x ∧
          τ.2.1 = flipCoord i y ∧ D.Y t i x < 1)
        (τ₀ := (x, flipCoord i y, true)) ?_ _ _
      intro τ
      constructor
      · rintro ⟨-, h2, h3, h4, -⟩
        exact Prod.ext_iff.mpr ⟨h3, Prod.ext_iff.mpr ⟨h4, h2⟩⟩
      · rintro rfl; exact ⟨trivial, rfl, rfl, rfl, hY⟩
    · rw [if_neg hY, zero_mul]
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [if_neg (fun hc => hY hc.2.2.2.2), zero_mul]
  · by_cases hY : D.Y t i x < 1
    · rw [if_pos hY, zero_mul]
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [if_neg (fun hc => hc.2.2.2.1 hY), zero_mul]
    · rw [if_neg hY]
      refine sum_state_eq'
        (P := fun τ : JSt n => True ∧ τ.2.1 = y ∧ τ.1 = flipCoord i x ∧
          ¬(D.Y t i x < 1) ∧ (τ.2.2 = decide (τ.1 ∉ B)))
        (τ₀ := (flipCoord i x, y, decide (flipCoord i x ∉ B))) ?_ _ _
      intro τ
      constructor
      · rintro ⟨-, h2, h3, -, h5⟩
        rw [h3] at h5
        exact Prod.ext_iff.mpr ⟨h3, Prod.ext_iff.mpr ⟨h2, h5⟩⟩
      · rintro rfl; exact ⟨trivial, rfl, rfl, hY, rfl⟩

open Classical in
/-- Dead-sector jump pairing: synchronized flips only. -/
private lemma jrate_pair_false' (dd : ℝ) (B : Set (Cube n)) (t : ℝ)
    (x y : Cube n) (f : JSt n → ℝ) :
    ∑ τ : JSt n, D.jrate dd B t (x, y, false) τ * f τ
      = ∑ i : Fin n, D.Y t i x / 2 * f (flipCoord i x, flipCoord i y, false) := by
  simp_rw [D.jrate_apply' dd B t x y false, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h2 : ∑ τ : JSt n,
      (if (false : Bool) ∧ τ.2.2 = true ∧ τ.1 = x ∧ τ.2.1 = flipCoord i y ∧
          D.Y t i x < 1 then (1 - D.Y t i x ^ dd) / 2 else 0) * f τ = 0 := by
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [if_neg (by rintro ⟨h, -⟩; exact Bool.noConfusion h), zero_mul]
  have h3 : ∑ τ : JSt n,
      (if (false : Bool) ∧ τ.2.1 = y ∧ τ.1 = flipCoord i x ∧
          ¬(D.Y t i x < 1) ∧ (τ.2.2 = decide (τ.1 ∉ B)) then
        (D.Y t i x - D.Y t i x ^ (1 - dd)) / 2 else 0) * f τ = 0 := by
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [if_neg (by rintro ⟨h, -⟩; exact Bool.noConfusion h), zero_mul]
  rw [h2, h3, add_zero, add_zero]
  refine sum_state_eq'
    (P := fun τ : JSt n => τ.1 = flipCoord i x ∧ τ.2.1 = flipCoord i y ∧
      (τ.2.2 = ((false : Bool) && decide (τ.1 ∉ B))))
    (τ₀ := (flipCoord i x, flipCoord i y, false)) ?_ _ _
  intro τ
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [Bool.false_and] at h3
    exact Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, h3⟩⟩
  · rintro rfl; exact ⟨rfl, rfl, by simp⟩

/-- The alive-sector power perturbation applied to `U` at one position pair
(the integrand of the localized Duhamel identity, [LGF eq (4.10)]). -/
private noncomputable def pertU (φ : Cube n → ℝ) (ℓ θ : ℝ) (x₀ : Cube n)
    (t : ℝ) (x y : Cube n) : ℝ :=
  ∑ i, (if D.Y t i x < 1 then
      (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
        (D.Utest φ t x (flipCoord i y) - D.Utest φ t x y)
    else
      -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2) *
        (D.Utest φ t (flipCoord i x) (flipCoord i y)
          - D.Utest φ t (flipCoord i x) y))

/-- Restatement of `abs_pert_Utest_le` for `pertU`. -/
private lemma abs_pertU_le {ℓ θ t : ℝ} (ht0 : θ ≤ t) (ht : t ≤ obsT)
    (hθ : θ ≤ obsT) {x₀ : Cube n} {φ : Cube n → ℝ}
    (hφ : ∀ w, φ w = 0 ∨ φ w = 1) (x y : Cube n) :
    |D.pertU φ ℓ θ x₀ t x y|
      ≤ Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
        * Real.sqrt (∑ i, D.Sc t i x ^ 2) * Real.sqrt (D.Gam φ t x y) :=
  D.abs_pert_Utest_le ht0 ht hθ hφ x y

/-- The single-source pairing identity: at an alive source, the jump pairing
of `U` equals the synchronized part plus the power perturbation. -/
private lemma jrate_U_pair_alive (φ : Cube n → ℝ) {ℓ θ : ℝ} (x₀ : Cube n)
    (B : Set (Cube n)) (t : ℝ) (x y : Cube n) :
    ∑ τ : JSt n, D.jrate (D.dbar ℓ θ x₀) B t (x, y, true) τ *
        (D.Utest φ t τ.1 τ.2.1 - D.Utest φ t x y)
      = (∑ i, D.Y t i x *
          (D.Utest φ t (flipCoord i x) (flipCoord i y) - D.Utest φ t x y) / 2)
        + D.pertU φ ℓ θ x₀ t x y := by
  rw [D.jrate_pair_true' (D.dbar ℓ θ x₀) B t x y
    (fun τ => D.Utest φ t τ.1 τ.2.1 - D.Utest φ t x y), pertU,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hY : D.Y t i x < 1
  · simp only [if_pos hY]
    ring
  · simp only [if_neg hY]
    ring

/-- At a dead source the jump pairing of `U` is purely synchronized. -/
private lemma jrate_U_pair_dead (φ : Cube n → ℝ) (dd : ℝ)
    (B : Set (Cube n)) (t : ℝ) (x y : Cube n) :
    ∑ τ : JSt n, D.jrate dd B t (x, y, false) τ *
        (D.Utest φ t τ.1 τ.2.1 - D.Utest φ t x y)
      = ∑ i, D.Y t i x *
          (D.Utest φ t (flipCoord i x) (flipCoord i y) - D.Utest φ t x y) / 2 := by
  rw [D.jrate_pair_false' dd B t x y
    (fun τ => D.Utest φ t τ.1 τ.2.1 - D.Utest φ t x y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Generic pairing of a forward matrix against a test. -/
private lemma matVec_fwdOf_pairing (q : JSt n → JSt n → ℝ) (v w : JSt n → ℝ) :
    ∑ s, matVec (fwdOf q) v s * w s
      = ∑ σ, v σ * (∑ τ, q σ τ * (w τ - w σ)) := by
  classical
  have h1 : ∑ s, matVec (fwdOf q) v s * w s
      = ∑ σ, v σ * (∑ s, fwdOf q s σ * w s) := by
    simp only [matVec, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ =>
      by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [h1]
  exact Finset.sum_congr rfl fun σ _ => by rw [fwdOf_transpose_pair']

/-- The `max`-form of the perturbation coefficients (manifestly continuous
across the `Y = 1` branch switch, where both branches vanish). -/
private lemma pertU_eq_max_form (φ : Cube n → ℝ) (ℓ θ : ℝ) (x₀ : Cube n)
    {t : ℝ} (ht : t ≤ D.T) (x y : Cube n) :
    D.pertU φ ℓ θ x₀ t x y
      = ∑ i, (max (1 - D.Y t i x ^ D.dbar ℓ θ x₀) 0 / 2 *
          (D.Utest φ t x (flipCoord i y) - D.Utest φ t x y)
        - max (D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) 0 / 2 *
          (D.Utest φ t (flipCoord i x) (flipCoord i y)
            - D.Utest φ t (flipCoord i x) y)) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hY0 : 0 < D.Y t i x := D.Y_pos ht i x
  have hd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
  have hd1 : D.dbar ℓ θ x₀ ≤ 1 := by
    have := D.dbar_lt_half ℓ θ x₀; linarith
  by_cases hY : D.Y t i x < 1
  · have h1 : D.Y t i x ^ D.dbar ℓ θ x₀ ≤ 1 :=
      Real.rpow_le_one hY0.le hY.le hd0
    have h2 : D.Y t i x ≤ D.Y t i x ^ (1 - D.dbar ℓ θ x₀) := by
      have := Real.rpow_le_rpow_of_exponent_ge hY0 hY.le
        (show 1 - D.dbar ℓ θ x₀ ≤ 1 by linarith)
      simpa [Real.rpow_one] using this
    rw [if_pos hY, max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · push_neg at hY
    have h1 : 1 ≤ D.Y t i x ^ D.dbar ℓ θ x₀ :=
      Real.one_le_rpow hY hd0
    have h2 : D.Y t i x ^ (1 - D.dbar ℓ θ x₀) ≤ D.Y t i x := by
      have := Real.rpow_le_rpow_of_exponent_le hY
        (show 1 - D.dbar ℓ θ x₀ ≤ 1 by linarith)
      simpa [Real.rpow_one] using this
    rw [if_neg (not_lt.mpr hY), max_eq_right (by linarith),
      max_eq_left (by linarith)]
    ring

/-- Continuity in `t` of `U_t(x,y)` on any interval inside `(-∞, T)`. -/
private lemma continuousOn_Utest (φ : Cube n → ℝ) {a b : ℝ} (hb : b < D.T)
    (x y : Cube n) :
    ContinuousOn (fun t => D.Utest φ t x y) (Set.Icc a b) := fun t ht =>
  ((D.hasDerivAt_Utest φ (lt_of_le_of_lt ht.2 hb) x y).continuousAt).continuousWithinAt

/-- Continuity of the pointwise max (via the abs identity). -/
private lemma contOn_max {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => max (f x) (g x)) s := by
  have hEq : (fun x => max (f x) (g x))
      = fun x => (f x + g x + |f x - g x|) / 2 := by
    funext x
    rcases le_total (f x) (g x) with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
  rw [hEq]
  exact ((hf.add hg).add ((hf.sub hg).abs)).div_const 2

/-- Continuity in `t` of the perturbation on a closed cell below `T`. -/
private lemma continuousOn_pertU (φ : Cube n → ℝ) (ℓ θ : ℝ) (x₀ : Cube n)
    {a b : ℝ} (hb : b < D.T) (x y : Cube n) :
    ContinuousOn (fun t => D.pertU φ ℓ θ x₀ t x y) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Iic D.T := fun t ht => le_of_lt (lt_of_le_of_lt ht.2 hb)
  have hforms : ∀ t ∈ Set.Icc a b, D.pertU φ ℓ θ x₀ t x y
      = ∑ i, (max (1 - D.Y t i x ^ D.dbar ℓ θ x₀) 0 / 2 *
          (D.Utest φ t x (flipCoord i y) - D.Utest φ t x y)
        - max (D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) 0 / 2 *
          (D.Utest φ t (flipCoord i x) (flipCoord i y)
            - D.Utest φ t (flipCoord i x) y)) := fun t ht =>
    D.pertU_eq_max_form φ ℓ θ x₀ (hsub ht) x y
  refine ContinuousOn.congr ?_ hforms
  refine continuousOn_finset_sum _ fun i _ => ?_
  have hYc : ContinuousOn (fun t => D.Y t i x) (Set.Icc a b) :=
    (D.continuousOn_Y i x).mono hsub
  have hYne : ∀ t ∈ Set.Icc a b, D.Y t i x ≠ 0 := fun t ht =>
    (D.Y_pos (hsub ht) i x).ne'
  have hr1 : ContinuousOn (fun t => D.Y t i x ^ D.dbar ℓ θ x₀) (Set.Icc a b) :=
    hYc.rpow_const fun t ht => Or.inl (hYne t ht)
  have hr2 : ContinuousOn (fun t => D.Y t i x ^ (1 - D.dbar ℓ θ x₀))
      (Set.Icc a b) := hYc.rpow_const fun t ht => Or.inl (hYne t ht)
  exact ((ContinuousOn.div_const (contOn_max
        (continuousOn_const.sub hr1) continuousOn_const) 2).mul
      ((D.continuousOn_Utest φ hb x (flipCoord i y)).sub
        (D.continuousOn_Utest φ hb x y))).sub
    ((ContinuousOn.div_const (contOn_max
        (hYc.sub hr2) continuousOn_const) 2).mul
      ((D.continuousOn_Utest φ hb (flipCoord i x) (flipCoord i y)).sub
        (D.continuousOn_Utest φ hb (flipCoord i x) y)))

/-- The `U`-pairing of the flow in cell `k`. -/
private noncomputable def uPair (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ s : JSt n, c.π k t s * D.Utest φ t s.1 s.2.1

/-- The alive-perturbation integrand of the Duhamel identity. -/
private noncomputable def pertPair (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ s : JSt n, (if s.2.2 = true then
    c.π k t s * D.pertU φ ℓ θ x₀ t s.1 s.2.1 else 0)

/-- Grid nodes are monotone. -/
private lemma grid_le'' {ℓ θ : ℝ} {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) :
    ∀ q p, p ≤ q → q ≤ c.K → c.z p ≤ c.z q := by
  intro q
  induction q with
  | zero => intro p hp _; simp [Nat.le_zero.mp hp]
  | succ m ih =>
    intro p hp hm
    rcases Nat.eq_or_lt_of_le hp with h | h
    · rw [h]
    · exact le_trans (ih p (Nat.lt_succ_iff.mp h) (Nat.le_of_succ_le hm))
        (c.is.grid.mono m (Nat.lt_of_succ_le hm))

/-- Right cell endpoints stay below the observation time. -/
private lemma cell_le_obsT {ℓ θ : ℝ} {x₀ : Cube n} (c : D.CFlow ℓ θ x₀)
    {k : ℕ} (hk : k < c.K) : c.z (k + 1) ≤ obsT := by
  have h := D.grid_le'' c c.K (k + 1) (Nat.succ_le_of_lt hk) le_rfl
  rwa [c.is.grid.last] at h

/-- **Cell derivative of the `U`-pairing**: the synchronized parts cancel
against the harmonicity of `U`, leaving the alive perturbation. -/
private lemma uPair_hasDeriv (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) {k : ℕ} (hk : k < c.K) {t : ℝ}
    (ht : t ∈ Set.Icc (c.z k) (c.z (k + 1))) :
    HasDerivWithinAt (D.uPair φ c k) (D.pertPair φ c k t)
      (Set.Icc (c.z k) (c.z (k + 1))) t := by
  classical
  have hzo : c.z (k + 1) ≤ obsT := D.cell_le_obsT c hk
  have htT : t < D.T := lt_of_le_of_lt (le_trans ht.2 hzo) D.obsT_lt_T
  have hg : ∀ s : JSt n,
      HasDerivWithinAt (fun u => D.Utest φ u s.1 s.2.1)
        (-(∑ i, D.Y t i s.1 *
          (D.Utest φ t (flipCoord i s.1) (flipCoord i s.2.1)
            - D.Utest φ t s.1 s.2.1) / 2))
        (Set.Icc (c.z k) (c.z (k + 1))) t :=
    fun s => (D.hasDerivAt_Utest φ htT s.1 s.2.1).hasDerivWithinAt
  have hpair := hasDerivWithinAt_pairing (c.is.glued.flow k hk) ht hg
  have hval : (∑ s : JSt n,
      (matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s
          * D.Utest φ t s.1 s.2.1
        + c.π k t s * -(∑ i, D.Y t i s.1 *
            (D.Utest φ t (flipCoord i s.1) (flipCoord i s.2.1)
              - D.Utest φ t s.1 s.2.1) / 2)))
      = D.pertPair φ c k t := by
    rw [Finset.sum_add_distrib]
    have hA : ∑ s : JSt n,
        matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s
          * D.Utest φ t s.1 s.2.1
        = ∑ σ : JSt n, c.π k t σ *
            (∑ τ : JSt n, D.jrate (D.dbar ℓ θ x₀)
              (D.barrier ℓ ((c.z k + c.z (k + 1)) / 2)) t σ τ *
              (D.Utest φ t τ.1 τ.2.1 - D.Utest φ t σ.1 σ.2.1)) := by
      simp only [cellGen]
      exact matVec_fwdOf_pairing _ _ _
    rw [hA, ← Finset.sum_add_distrib, pertPair]
    refine Finset.sum_congr rfl fun σ _ => ?_
    obtain ⟨x, y, b⟩ := σ
    cases b with
    | true =>
      rw [D.jrate_U_pair_alive φ x₀ _ t x y]
      have hcond : (((x, y, true) : JSt n).2.2 = true) := rfl
      rw [if_pos hcond]
      ring
    | false =>
      rw [D.jrate_U_pair_dead φ _ _ t x y]
      have hif : (if ((x, y, false) : JSt n).2.2 = true then
          c.π k t (x, y, false) * D.pertU φ ℓ θ x₀ t x y else 0) = 0 := by
        simp
      rw [hif]
      ring
  have hfun : (fun u => ∑ s : JSt n, c.π k u s * D.Utest φ u s.1 s.2.1)
      = D.uPair φ c k := rfl
  rw [hfun, hval] at hpair
  exact hpair

open Classical in
/-- The node transfer as a `{0,1}` matrix with one nonzero entry per column. -/
private lemma killTr_eq_single' (ℓ t : ℝ) (s s' : JSt n) :
    D.killTr ℓ t s s'
      = if s = (s'.1, s'.2.1, (s'.2.2 && decide (s'.1 ∉ D.barrier ℓ t))) then 1
        else 0 := by
  obtain ⟨x, y, b⟩ := s
  obtain ⟨x', y', b'⟩ := s'
  simp only [killTr, Prod.mk.injEq]

open Classical in
/-- Node transfers are invisible to a sector-blind test of both positions. -/
private lemma killTr_pair_pos (ℓ t : ℝ) (v : JSt n → ℝ)
    (h : Cube n → Cube n → ℝ) :
    ∑ s : JSt n, matVec (D.killTr ℓ t) v s * h s.1 s.2.1
      = ∑ s : JSt n, v s * h s.1 s.2.1 := by
  simp only [matVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  have key : ∀ s : JSt n, D.killTr ℓ t s s' * v s' * h s.1 s.2.1
      = if s = (s'.1, s'.2.1, (s'.2.2 && decide (s'.1 ∉ D.barrier ℓ t))) then
          v s' * h s'.1 s'.2.1 else 0 := by
    intro s
    rw [D.killTr_eq_single' ℓ t s s']
    by_cases hs : s = ((s'.1, s'.2.1,
        (s'.2.2 && decide (s'.1 ∉ D.barrier ℓ t))) : JSt n)
    · rw [if_pos hs, if_pos hs, hs]
      simp
    · rw [if_neg hs, if_neg hs, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun s _ => key s]
  simp

/-- **The localized Duhamel identity** [LGF eq (4.10)]: for a `{0,1}`-valued
test (indicator of `B`), the signed terminal discrepancy of one coupling flow
is the accumulated alive perturbation. -/
private lemma duhamel {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (B : Finset (Cube n)) :
    D.DtestF c B
      = ∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
          D.pertPair (fun w => if w ∈ B then (1 : ℝ) else 0) c k t := by
  classical
  set φ : Cube n → ℝ := fun w => if w ∈ B then (1 : ℝ) else 0 with hφdef
  have hK : 0 < c.K := c.is.grid.pos
  have hzo : ∀ k, k < c.K → c.z (k + 1) ≤ obsT := fun k hk => D.cell_le_obsT c hk
  have hcellT : ∀ k, k < c.K → c.z (k + 1) < D.T := fun k hk =>
    lt_of_le_of_lt (hzo k hk) D.obsT_lt_T
  -- continuity of the pairing on each cell
  have hucont : ∀ k, k < c.K →
      ContinuousOn (D.uPair φ c k) (Set.Icc (c.z k) (c.z (k + 1))) := by
    intro k hk
    exact fun t ht => (D.uPair_hasDeriv φ c hk ht).continuousWithinAt
  -- integrability of the perturbation integrand on each cell
  have hint : ∀ k, k < c.K →
      IntervalIntegrable (D.pertPair φ c k) MeasureTheory.volume
        (c.z k) (c.z (k + 1)) := by
    intro k hk
    have hcont : ContinuousOn (D.pertPair φ c k)
        (Set.Icc (c.z k) (c.z (k + 1))) := by
      refine continuousOn_finset_sum _ fun s _ => ?_
      by_cases hs : s.2.2 = true
      · simp only [pertPair, if_pos hs]
        exact ((c.is.glued.flow k hk).cont s).mul
          (D.continuousOn_pertU φ ℓ θ x₀ (hcellT k hk) s.1 s.2.1)
      · simp only [pertPair, if_neg hs]
        exact continuousOn_const
    exact ContinuousOn.intervalIntegrable
      (by rwa [Set.uIcc_of_le (c.is.grid.mono k hk)])
  -- node preservation: sector-blind test
  have hnode_eq : ∀ k, k + 1 < c.K →
      D.uPair φ c (k + 1) (c.z (k + 1)) = D.uPair φ c k (c.z (k + 1)) := by
    intro k hk1
    have hnode := c.is.glued.node k hk1
    simp only [uPair, hnode]
    exact D.killTr_pair_pos ℓ (c.z (k + 1)) (c.π k (c.z (k + 1)))
      (fun v w => D.Utest φ (c.z (k + 1)) v w)
  -- exact chaining
  have hchain := chain_eq (u := D.uPair φ c) (φ := D.pertPair φ c) hK
    c.is.grid.mono hucont
    (fun k hk t ht => D.uPair_hasDeriv φ c hk ht) hint hnode_eq
  -- endpoints
  have hlast : c.z c.K = obsT := c.is.grid.last
  have hfirst : c.z 0 = θ := c.is.grid.first
  -- terminal value: `∑ term·φ(W)`
  have hterm : D.uPair φ c (c.K - 1) (c.z c.K)
      = ∑ s : JSt n, c.term s * φ s.2.1 := by
    rw [hlast]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Dat.CFlow.term, D.Utest_obsT φ s.1 s.2.1]
  -- initial value: `∑ term·φ(V)` via the diagonal transport
  have hinit : D.uPair φ c 0 (c.z 0) = ∑ s : JSt n, c.term s * φ s.1 := by
    have h1 : D.uPair φ c 0 (c.z 0) = D.Utest φ (c.z 0) x₀ x₀ := by
      simp only [uPair]
      rw [c.is.glued.init, D.killTr_pair_pos ℓ (c.z 0) (initVec x₀)
        (fun v w => D.Utest φ (c.z 0) v w)]
      have hsel : ∀ s : JSt n, initVec x₀ s * D.Utest φ (c.z 0) s.1 s.2.1
          = if s = ((x₀, x₀, true) : JSt n) then
              D.Utest φ (c.z 0) x₀ x₀ else 0 := by
        intro s
        simp only [initVec]
        by_cases hs : s = ((x₀, x₀, true) : JSt n)
        · rw [if_pos hs, if_pos hs, hs, one_mul]
        · rw [if_neg hs, if_neg hs, zero_mul]
      rw [Finset.sum_congr rfl fun s _ => hsel s]
      simp
    rw [h1, hfirst]
    exact (D.term_V_eq_Utest_diag hθ0 hθ c φ).symm
  -- assemble
  have hD : D.DtestF c B
      = (∑ s : JSt n, c.term s * φ s.2.1) - ∑ s : JSt n, c.term s * φ s.1 := by
    simp only [DtestF, hφdef, mul_sub, Finset.sum_sub_distrib]
  rw [hD, ← hterm, ← hinit, hchain]
  ring

/-! ### Stage B: the Cauchy–Schwarz cascade

`|∑_{x₀∈A} startW·(test discrepancy)| ≤ √8·√κ·Λ·√(𝒮_A)·√(Y_A)` with
`Y_A = ∑_A startW·(accumulated Γ-energy)` [LGF eq (4.18)]. -/

/-- Interval Cauchy–Schwarz in square-root form (via the `ε`-regularized
AM–GM split). -/
private lemma intervalIntegral_sqrt_mul_le {F G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Set.Icc a b))
    (hG : ContinuousOn G (Set.Icc a b))
    (hF0 : ∀ t ∈ Set.Icc a b, 0 ≤ F t) (hG0 : ∀ t ∈ Set.Icc a b, 0 ≤ G t) :
    ∫ t in a..b, Real.sqrt (F t) * Real.sqrt (G t)
      ≤ Real.sqrt (∫ t in a..b, F t) * Real.sqrt (∫ t in a..b, G t) := by
  classical
  set IF := ∫ t in a..b, F t with hIF
  set IG := ∫ t in a..b, G t with hIG
  have hFi : IntervalIntegrable F MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable (by rwa [Set.uIcc_of_le hab])
  have hGi : IntervalIntegrable G MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable (by rwa [Set.uIcc_of_le hab])
  have hIF0 : 0 ≤ IF := intervalIntegral.integral_nonneg hab hF0
  have hIG0 : 0 ≤ IG := intervalIntegral.integral_nonneg hab hG0
  have hkey : ∀ ε : ℝ, 0 < ε →
      (∫ t in a..b, Real.sqrt (F t) * Real.sqrt (G t))
        ≤ Real.sqrt ((IF + ε) * (IG + ε)) := by
    intro ε hε
    have hIFε : 0 < IF + ε := by linarith
    have hIGε : 0 < IG + ε := by linarith
    set lam := Real.sqrt ((IG + ε) / (IF + ε)) with hlam
    have hlam0 : 0 < lam := Real.sqrt_pos.mpr (div_pos hIGε hIFε)
    have hpt : ∀ t ∈ Set.Icc a b,
        Real.sqrt (F t) * Real.sqrt (G t) ≤ (lam * F t + G t / lam) / 2 := by
      intro t ht
      have h1 : 0 ≤ lam * F t := mul_nonneg hlam0.le (hF0 t ht)
      have h2 : 0 ≤ G t / lam := div_nonneg (hG0 t ht) hlam0.le
      have hsq : Real.sqrt (lam * F t) * Real.sqrt (G t / lam)
          = Real.sqrt (F t) * Real.sqrt (G t) := by
        rw [← Real.sqrt_mul h1, ← Real.sqrt_mul (hF0 t ht)]
        congr 1
        field_simp
      nlinarith [sq_nonneg (Real.sqrt (lam * F t) - Real.sqrt (G t / lam)),
        Real.sq_sqrt h1, Real.sq_sqrt h2, hsq,
        Real.sqrt_nonneg (lam * F t), Real.sqrt_nonneg (G t / lam)]
    have hSGi : IntervalIntegrable (fun t => Real.sqrt (F t) * Real.sqrt (G t))
        MeasureTheory.volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]
      exact (hF.sqrt).mul (hG.sqrt)
    have hRHSi : IntervalIntegrable (fun t => (lam * F t + G t / lam) / 2)
        MeasureTheory.volume a b :=
      (((hFi.const_mul lam).add (hGi.div_const lam)).div_const 2)
    have hint := intervalIntegral.integral_mono_on hab hSGi hRHSi hpt
    have hval : (∫ t in a..b, (lam * F t + G t / lam) / 2)
        = (lam * IF + IG / lam) / 2 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add
        (hFi.const_mul lam) (hGi.div_const lam),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
    have hbound : (lam * IF + IG / lam) / 2 ≤ Real.sqrt ((IF + ε) * (IG + ε)) := by
      have hFs : Real.sqrt (IF + ε) ^ 2 = IF + ε := Real.sq_sqrt hIFε.le
      have hGs : Real.sqrt (IG + ε) ^ 2 = IG + ε := Real.sq_sqrt hIGε.le
      have hFpos : 0 < Real.sqrt (IF + ε) := Real.sqrt_pos.mpr hIFε
      have hGpos : 0 < Real.sqrt (IG + ε) := Real.sqrt_pos.mpr hIGε
      have hsm : Real.sqrt ((IF + ε) * (IG + ε))
          = Real.sqrt (IF + ε) * Real.sqrt (IG + ε) := Real.sqrt_mul hIFε.le _
      have hlam2 : lam = Real.sqrt (IG + ε) / Real.sqrt (IF + ε) := by
        rw [hlam, show (IG + ε) / (IF + ε)
            = (Real.sqrt (IG + ε) / Real.sqrt (IF + ε)) ^ 2 by
          rw [div_pow, hFs, hGs]]
        exact Real.sqrt_sq (by positivity)
      have h1 : lam * (IF + ε) = Real.sqrt (IF + ε) * Real.sqrt (IG + ε) := by
        rw [hlam2, div_mul_eq_mul_div, div_eq_iff hFpos.ne']
        linear_combination (-Real.sqrt (IG + ε)) * Real.mul_self_sqrt hIFε.le
      have h2 : (IG + ε) / lam = Real.sqrt (IF + ε) * Real.sqrt (IG + ε) := by
        rw [hlam2, div_div_eq_mul_div, div_eq_iff hGpos.ne']
        linear_combination (-Real.sqrt (IF + ε)) * Real.mul_self_sqrt hIGε.le
      have hle1 : lam * IF ≤ lam * (IF + ε) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam0.le
      have hle2 : IG / lam ≤ (IG + ε) / lam := by
        have h := mul_le_mul_of_nonneg_right (show IG ≤ IG + ε by linarith)
          (le_of_lt (inv_pos.mpr hlam0))
        simpa [div_eq_mul_inv] using h
      calc (lam * IF + IG / lam) / 2
          ≤ (lam * (IF + ε) + (IG + ε) / lam) / 2 := by linarith
        _ = Real.sqrt ((IF + ε) * (IG + ε)) := by rw [h1, h2, hsm]; ring
    calc (∫ t in a..b, Real.sqrt (F t) * Real.sqrt (G t))
        ≤ (lam * IF + IG / lam) / 2 := le_of_le_of_eq hint hval
      _ ≤ Real.sqrt ((IF + ε) * (IG + ε)) := hbound
  have hlim : Filter.Tendsto (fun ε : ℝ => Real.sqrt ((IF + ε) * (IG + ε)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt IF * Real.sqrt IG)) := by
    have hc : Continuous fun ε : ℝ => Real.sqrt ((IF + ε) * (IG + ε)) := by
      fun_prop
    have h0 : Real.sqrt ((IF + 0) * (IG + 0)) = Real.sqrt IF * Real.sqrt IG := by
      rw [add_zero, add_zero, Real.sqrt_mul hIF0]
    have := hc.tendsto 0
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hkey ε hε

/-- Weighted Cauchy–Schwarz: `∑ p·√u·√v ≤ √(∑ p u)·√(∑ p v)`. -/
private lemma weighted_cs {ι : Type*} (s : Finset ι) (p u v : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) :
    ∑ i ∈ s, p i * (Real.sqrt (u i) * Real.sqrt (v i))
      ≤ Real.sqrt (∑ i ∈ s, p i * u i) * Real.sqrt (∑ i ∈ s, p i * v i) := by
  have hall : ∀ i ∈ s, 0 ≤ u i ∧ 0 ≤ v i := fun i hi => ⟨hu i hi, hv i hi⟩
  · have h := sum_le_sqrt_mul_sqrt s
      (fun i => Real.sqrt (p i) * Real.sqrt (u i))
      (fun i => Real.sqrt (p i) * Real.sqrt (v i))
      (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have e1 : ∀ i ∈ s, (Real.sqrt (p i) * Real.sqrt (u i))
        * (Real.sqrt (p i) * Real.sqrt (v i))
        = p i * (Real.sqrt (u i) * Real.sqrt (v i)) := by
      intro i hi
      have : Real.sqrt (p i) * Real.sqrt (p i) = p i :=
        Real.mul_self_sqrt (hp i hi)
      calc (Real.sqrt (p i) * Real.sqrt (u i))
            * (Real.sqrt (p i) * Real.sqrt (v i))
          = (Real.sqrt (p i) * Real.sqrt (p i))
            * (Real.sqrt (u i) * Real.sqrt (v i)) := by ring
        _ = p i * (Real.sqrt (u i) * Real.sqrt (v i)) := by rw [this]
    have e2 : ∀ i ∈ s, (Real.sqrt (p i) * Real.sqrt (u i)) ^ 2 = p i * u i := by
      intro i hi
      rw [mul_pow, Real.sq_sqrt (hp i hi), Real.sq_sqrt (hall i hi).1]
    have e3 : ∀ i ∈ s, (Real.sqrt (p i) * Real.sqrt (v i)) ^ 2 = p i * v i := by
      intro i hi
      rw [mul_pow, Real.sq_sqrt (hp i hi), Real.sq_sqrt (hall i hi).2]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
      Finset.sum_congr rfl e3] at h
    exact h

/-! #### Continuity toolbox (all in `t`, on closed cells below `T_o`) -/

private lemma continuous_gamB' : Continuous gam := by
  have : Continuous fun t : ℝ => -(obsT - t) :=
    (continuous_const.sub continuous_id).neg
  exact Real.continuous_exp.comp this

private lemma continuousOn_aB' {a b : ℝ} (hb : b ≤ obsT) :
    ContinuousOn D.aB (Set.Icc a b) := by
  refine ContinuousOn.div
    ((continuous_gamB'.mul continuous_const).continuousOn)
    ((continuous_const.sub (continuous_const.mul
      (continuous_gamB'.pow 2))).continuousOn) ?_
  intro t ht
  exact ne_of_gt (D.den_pos (le_trans ht.2 hb))

private lemma continuousOn_bB' {a b : ℝ} (hb : b ≤ obsT) :
    ContinuousOn D.bB (Set.Icc a b) := by
  refine ContinuousOn.div
    ((continuous_const.mul (continuous_const.sub
      (continuous_gamB'.pow 2))).continuousOn)
    ((continuous_const.sub (continuous_const.mul
      (continuous_gamB'.pow 2))).continuousOn) ?_
  intro t ht
  exact ne_of_gt (D.den_pos (le_trans ht.2 hb))

private lemma continuousOn_mB' {a b : ℝ} (hb : b ≤ obsT) (x y ζ : Cube n)
    (j : Fin n) : ContinuousOn (fun t => D.mB t x y ζ j) (Set.Icc a b) := by
  simp only [mB]
  exact ((D.continuousOn_aB' hb).mul continuousOn_const).add
    ((((D.continuousOn_bB' hb).mul continuousOn_const).mul
      continuousOn_const).mul continuousOn_const)

private lemma continuousOn_dmext_mB' {a b : ℝ} (hb : b ≤ obsT)
    (φ : Cube n → ℝ) (i : Fin n) (x y ζ : Cube n) :
    ContinuousOn (fun t => dmext φ i (D.mB t x y ζ)) (Set.Icc a b) := by
  simp only [dmext]
  refine continuousOn_finset_sum _ fun w _ => ?_
  refine ContinuousOn.mul (ContinuousOn.div_const ?_ 2) continuousOn_const
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_prod _ fun j _ => ?_
  exact (continuousOn_const.add ((D.continuousOn_mB' hb x y ζ j).mul
    continuousOn_const)).div_const 2

private lemma continuousOn_Hlik' {a b : ℝ} (hbT : b < D.T) (ζ x : Cube n) :
    ContinuousOn (fun t => D.Hlik t ζ x) (Set.Icc a b) := fun t ht =>
  ((D.hasDerivAt_Hlik (lt_of_le_of_lt ht.2 hbT) ζ x).continuousAt).continuousWithinAt

private lemma continuousOn_lam' {a b : ℝ} (hb : b ≤ obsT) (i : Fin n)
    (x ζ : Cube n) : ContinuousOn (fun t => D.lam t i x ζ) (Set.Icc a b) := by
  have hexp : Continuous fun t : ℝ => Real.exp (-(D.T - t)) :=
    Real.continuous_exp.comp ((continuous_const.sub continuous_id).neg)
  simp only [lam]
  refine ContinuousOn.div
    ((continuous_const.sub ((hexp.mul continuous_const).mul
      continuous_const)).continuousOn)
    ((continuous_const.add ((hexp.mul continuous_const).mul
      continuous_const)).continuousOn) ?_
  intro t ht
  have habs := D.abs_exp_le_a (le_trans ht.2 hb)
  rw [abs_of_pos (Real.exp_pos _)] at habs
  have ha1 := D.ha1
  have hb1 : Real.exp (-(D.T - t)) * toR (x i) * toR (ζ i)
      = Real.exp (-(D.T - t)) * (toR (x i) * toR (ζ i)) := by ring
  rcases toR_eq_one_or (x i) with hx | hx <;>
    rcases toR_eq_one_or (ζ i) with hζ | hζ <;>
      rw [hb1, hx, hζ] <;> [skip; skip; skip; skip] <;>
      · intro hzero
        nlinarith [Real.exp_pos (-(D.T - t))]

private lemma Gam_nonneg {t : ℝ} (ht : t ≤ obsT) (φ : Cube n → ℝ)
    (x y : Cube n) : 0 ≤ D.Gam φ t x y := by
  refine Finset.sum_nonneg fun ζ _ => mul_nonneg
    (D.Hlik_nonneg (le_trans ht D.obsT_lt_T.le) ζ x) ?_
  refine Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (mul_nonneg (D.lam_pos ht i x ζ).le
    (add_nonneg (sq_nonneg _) (sq_nonneg _))) (sq_nonneg _)

private lemma continuousOn_Gam' {a b : ℝ} (hb : b ≤ obsT) (hbT : b < D.T)
    (φ : Cube n → ℝ) (x y : Cube n) :
    ContinuousOn (fun t => D.Gam φ t x y) (Set.Icc a b) := by
  simp only [Gam]
  refine continuousOn_finset_sum _ fun ζ _ => ContinuousOn.mul
    (D.continuousOn_Hlik' hbT ζ x) ?_
  refine continuousOn_finset_sum _ fun i _ => ?_
  exact ((D.continuousOn_lam' hb i x ζ).mul
      (((D.continuousOn_aB' hb).pow 2).add
        ((D.continuousOn_bB' hb).pow 2))).mul
    ((D.continuousOn_dmext_mB' hb φ i x y ζ).pow 2)

/-! #### The per-flow energy bound (B1–B5) -/

/-- The accumulated `Γ`-energy of one coupling flow, for a given test. -/
private noncomputable def gamE (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) : ℝ :=
  ∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
    ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1

/-- Alive score integrand of `scoreEnergy`, named for reuse. -/
private noncomputable def scInt {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ s : JSt n, (if s.2.2 then c.π k t s * ∑ i, D.Sc t i s.1 ^ 2 else 0)

private lemma scoreEnergy_eq {ℓ θ : ℝ} {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) :
    D.scoreEnergy c = ∑ k ∈ Finset.range c.K,
      ∫ t in c.z k..c.z (k + 1), D.scInt c k t := rfl

/-- Continuity of the alive score integrand on a closed cell. -/
private lemma continuousOn_scInt {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) {k : ℕ} (hk : k < c.K) :
    ContinuousOn (D.scInt c k) (Set.Icc (c.z k) (c.z (k + 1))) := by
  have hsub : Set.Icc (c.z k) (c.z (k + 1)) ⊆ Set.Iic D.T := fun t ht =>
    le_trans ht.2 (le_trans (D.cell_le_obsT c hk) D.obsT_lt_T.le)
  refine continuousOn_finset_sum _ fun s _ => ?_
  by_cases hs : s.2.2
  · simp only [scInt, if_pos hs]
    refine ((c.is.glued.flow k hk).cont s).mul
      (continuousOn_finset_sum _ fun i _ => ?_)
    have hY : ContinuousOn (fun t => D.Y t i s.1)
        (Set.Icc (c.z k) (c.z (k + 1))) := (D.continuousOn_Y i s.1).mono hsub
    simpa [Sc] using ((continuousOn_const.sub hY).div_const 2).pow 2
  · simp only [scInt, if_neg hs]
    exact continuousOn_const

/-- Continuity of the `Γ`-pairing integrand on a closed cell. -/
private lemma continuousOn_gamInt (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) {k : ℕ} (hk : k < c.K) :
    ContinuousOn (fun t => ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)
      (Set.Icc (c.z k) (c.z (k + 1))) := by
  have hb : c.z (k + 1) ≤ obsT := D.cell_le_obsT c hk
  have hbT : c.z (k + 1) < D.T := lt_of_le_of_lt hb D.obsT_lt_T
  exact continuousOn_finset_sum _ fun s _ =>
    ((c.is.glued.flow k hk).cont s).mul (D.continuousOn_Gam' hb hbT φ s.1 s.2.1)

private lemma scInt_nonneg {ℓ θ : ℝ} (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) {k : ℕ} (hk : k < c.K) {t : ℝ}
    (ht : t ∈ Set.Icc (c.z k) (c.z (k + 1))) : 0 ≤ D.scInt c k t := by
  unfold scInt
  refine Finset.sum_nonneg fun s _ => ?_
  by_cases hs : s.2.2
  · rw [if_pos hs]
    exact mul_nonneg (D.cflow_nonneg hθ c hk ht s)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · rw [if_neg hs]

private lemma gamInt_nonneg (φ : Cube n → ℝ) {ℓ θ : ℝ} (hθ : θ ≤ obsT)
    {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) {k : ℕ} (hk : k < c.K) {t : ℝ}
    (ht : t ∈ Set.Icc (c.z k) (c.z (k + 1))) :
    0 ≤ ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1 := by
  have htB : t ≤ obsT := le_trans ht.2 (D.cell_le_obsT c hk)
  exact Finset.sum_nonneg fun s _ => mul_nonneg (D.cflow_nonneg hθ c hk ht s)
    (D.Gam_nonneg htB φ s.1 s.2.1)

/-- (B1)+(B2): pointwise-in-`t` bound of the perturbation pairing by the
geometric mean of the score and `Γ` integrands. -/
private lemma abs_pertPair_le (B : Finset (Cube n)) {ℓ θ : ℝ}
    (hθ0 : obsT - 1 ≤ θ) (hθ : θ ≤ obsT) {x₀ : Cube n} (c : D.CFlow ℓ θ x₀)
    {k : ℕ} (hk : k < c.K) {t : ℝ}
    (ht : t ∈ Set.Icc (c.z k) (c.z (k + 1))) :
    |D.pertPair (fun w => if w ∈ B then (1 : ℝ) else 0) c k t|
      ≤ Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
        * (Real.sqrt (D.scInt c k t)
          * Real.sqrt (∑ s : JSt n, c.π k t s *
              D.Gam (fun w => if w ∈ B then (1 : ℝ) else 0) t s.1 s.2.1)) := by
  classical
  set φ : Cube n → ℝ := fun w => if w ∈ B then (1 : ℝ) else 0 with hφdef
  have hφ01 : ∀ w, φ w = 0 ∨ φ w = 1 := by
    intro w; by_cases hw : w ∈ B <;> simp [hφdef, hw]
  have htB : t ≤ obsT := le_trans ht.2 (D.cell_le_obsT c hk)
  have htθ : θ ≤ t := by
    have h0 := D.grid_le'' c k 0 (Nat.zero_le k) hk.le
    rw [c.is.grid.first] at h0
    exact le_trans h0 ht.1
  have hθo : θ ≤ obsT := le_trans htθ htB
  have hπ0 : ∀ s : JSt n, 0 ≤ c.π k t s := fun s => D.cflow_nonneg hθ c hk ht s
  set p : JSt n → ℝ := fun s => if s.2.2 then c.π k t s else 0 with hpdef
  have hp0 : ∀ s : JSt n, 0 ≤ p s := by
    intro s
    by_cases hs : s.2.2 <;> simp [hpdef, hs, hπ0 s]
  set Cst := Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a with hCst
  have hCst0 : 0 ≤ Cst := by
    have h1 : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ Real.sqrt (kappa D.a) := Real.sqrt_nonneg _
    have h3 : (0:ℝ) ≤ Lam D.a :=
      le_trans zero_le_one (one_le_Lam D.ha0 D.ha1)
    positivity
  have hd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
  -- step 1+2: triangle + the pointwise perturbation bound
  have hstep12 : |D.pertPair φ c k t|
      ≤ ∑ s : JSt n, p s * (Cst * D.dbar ℓ θ x₀ *
          (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
            * Real.sqrt (D.Gam φ t s.1 s.2.1))) := by
    have h1 : |D.pertPair φ c k t|
        ≤ ∑ s : JSt n, p s * |D.pertU φ ℓ θ x₀ t s.1 s.2.1| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun s _ => ?_
      by_cases hs : s.2.2
      · simp [pertPair, hpdef, hs, abs_mul, abs_of_nonneg (hπ0 s)]
      · simp [pertPair, hpdef, hs]
    refine le_trans h1 (Finset.sum_le_sum fun s _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hp0 s)
    have := D.abs_pertU_le (θ := θ) (ℓ := ℓ) (x₀ := x₀) htθ htB hθo hφ01 s.1 s.2.1
    calc |D.pertU φ ℓ θ x₀ t s.1 s.2.1|
        ≤ Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
          * Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
          * Real.sqrt (D.Gam φ t s.1 s.2.1) := this
      _ = Cst * D.dbar ℓ θ x₀ * (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
          * Real.sqrt (D.Gam φ t s.1 s.2.1)) := by rw [hCst]; ring
  -- step 3: pull the constants out
  have hstep3 : ∑ s : JSt n, p s * (Cst * D.dbar ℓ θ x₀ *
        (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
          * Real.sqrt (D.Gam φ t s.1 s.2.1)))
      = Cst * D.dbar ℓ θ x₀ * ∑ s : JSt n, p s *
          (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
            * Real.sqrt (D.Gam φ t s.1 s.2.1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  -- step 4: weighted Cauchy–Schwarz over the state space
  have hstep4 : ∑ s : JSt n, p s *
        (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
          * Real.sqrt (D.Gam φ t s.1 s.2.1))
      ≤ Real.sqrt (∑ s : JSt n, p s * ∑ i, D.Sc t i s.1 ^ 2)
        * Real.sqrt (∑ s : JSt n, p s * D.Gam φ t s.1 s.2.1) :=
    weighted_cs Finset.univ p _ _ (fun s _ => hp0 s)
      (fun s _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (fun s _ => D.Gam_nonneg htB φ s.1 s.2.1)
  -- step 5: identify/dominate the two factors
  have hfac1 : (∑ s : JSt n, p s * ∑ i, D.Sc t i s.1 ^ 2) = D.scInt c k t := by
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : s.2.2 <;> simp [hpdef, scInt, hs]
  have hfac2 : (∑ s : JSt n, p s * D.Gam φ t s.1 s.2.1)
      ≤ ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1 := by
    refine Finset.sum_le_sum fun s _ => ?_
    by_cases hs : s.2.2
    · simp [hpdef, hs]
    · simp only [hpdef, if_neg hs, zero_mul]
      exact mul_nonneg (hπ0 s) (D.Gam_nonneg htB φ s.1 s.2.1)
  calc |D.pertPair φ c k t|
      ≤ Cst * D.dbar ℓ θ x₀ * ∑ s : JSt n, p s *
          (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
            * Real.sqrt (D.Gam φ t s.1 s.2.1)) := by
        rw [← hstep3]; exact hstep12
    _ ≤ Cst * D.dbar ℓ θ x₀ *
        (Real.sqrt (D.scInt c k t)
          * Real.sqrt (∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCst0 hd0)
        refine le_trans hstep4 ?_
        rw [hfac1]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt hfac2) (Real.sqrt_nonneg _)
    _ = Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
        * (Real.sqrt (D.scInt c k t)
          * Real.sqrt (∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := by
        rw [hCst]

/-- (B3)+(B4)+(B5): the per-flow discrepancy bound
`|𝔼_{x₀}[φ(W)] - 𝔼_{x₀}[φ(V)]| ≤ √8·√κ·Λ·δ̄·√(scoreEnergy)·√(gamE)`. -/
private lemma abs_DtestF_le (B : Finset (Cube n)) {ℓ θ : ℝ}
    (hθ0' : 0 ≤ θ) (hθ1 : obsT - 1 ≤ θ) (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) :
    |D.DtestF c B|
      ≤ Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
        * (Real.sqrt (D.scoreEnergy c)
          * Real.sqrt (D.gamE (fun w => if w ∈ B then (1 : ℝ) else 0) c)) := by
  classical
  set φ : Cube n → ℝ := fun w => if w ∈ B then (1 : ℝ) else 0 with hφdef
  set Cst := Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a with hCst
  have hCst0 : 0 ≤ Cst := by
    have h3 : (0:ℝ) ≤ Lam D.a := le_trans zero_le_one (one_le_Lam D.ha0 D.ha1)
    have h1 : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ Real.sqrt (kappa D.a) := Real.sqrt_nonneg _
    positivity
  have hd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
  have hmono : ∀ k, k < c.K → c.z k ≤ c.z (k + 1) := c.is.grid.mono
  have hφ01 : ∀ w, φ w = 0 ∨ φ w = 1 := by
    intro w; by_cases hw : w ∈ B <;> simp [hφdef, hw]
  -- per-cell: |∫ pertPair| ≤ Cst·δ̄·√(∫ scInt)·√(∫ gamInt)
  have hcell : ∀ k, k < c.K →
      |∫ t in c.z k..c.z (k + 1), D.pertPair φ c k t|
        ≤ Cst * D.dbar ℓ θ x₀ *
          (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)
            * Real.sqrt (∫ t in c.z k..c.z (k + 1),
                ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := by
    intro k hk
    have hb : c.z (k + 1) ≤ obsT := D.cell_le_obsT c hk
    have hbT : c.z (k + 1) < D.T := lt_of_le_of_lt hb D.obsT_lt_T
    have hzk : c.z k ≤ c.z (k + 1) := hmono k hk
    -- continuity of the three integrands
    have hpc : ContinuousOn (D.pertPair φ c k)
        (Set.Icc (c.z k) (c.z (k + 1))) := by
      refine continuousOn_finset_sum _ fun s _ => ?_
      by_cases hs : s.2.2
      · simp only [pertPair, if_pos hs]
        exact ((c.is.glued.flow k hk).cont s).mul
          (D.continuousOn_pertU φ ℓ θ x₀ hbT s.1 s.2.1)
      · simp only [pertPair, if_neg hs]
        exact continuousOn_const
    have hsc : ContinuousOn (D.scInt c k)
        (Set.Icc (c.z k) (c.z (k + 1))) := D.continuousOn_scInt c hk
    have hgc : ContinuousOn (fun t => ∑ s : JSt n, c.π k t s *
        D.Gam φ t s.1 s.2.1) (Set.Icc (c.z k) (c.z (k + 1))) :=
      D.continuousOn_gamInt φ c hk
    -- interval integrabilities
    have hpint : IntervalIntegrable (fun t => |D.pertPair φ c k t|)
        MeasureTheory.volume (c.z k) (c.z (k + 1)) :=
      ContinuousOn.intervalIntegrable
        (by rw [Set.uIcc_of_le hzk]; exact hpc.abs)
    have hbint : IntervalIntegrable (fun t => Cst * D.dbar ℓ θ x₀ *
        (Real.sqrt (D.scInt c k t) * Real.sqrt (∑ s : JSt n, c.π k t s *
          D.Gam φ t s.1 s.2.1)))
        MeasureTheory.volume (c.z k) (c.z (k + 1)) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hzk]
      exact (continuousOn_const.mul (hsc.sqrt.mul hgc.sqrt))
    calc |∫ t in c.z k..c.z (k + 1), D.pertPair φ c k t|
        ≤ ∫ t in c.z k..c.z (k + 1), |D.pertPair φ c k t| :=
          intervalIntegral.abs_integral_le_integral_abs hzk
      _ ≤ ∫ t in c.z k..c.z (k + 1), Cst * D.dbar ℓ θ x₀ *
            (Real.sqrt (D.scInt c k t) * Real.sqrt (∑ s : JSt n, c.π k t s *
              D.Gam φ t s.1 s.2.1)) := by
          refine intervalIntegral.integral_mono_on hzk hpint hbint fun t ht => ?_
          have h := D.abs_pertPair_le B hθ1 hθ c hk ht
          calc |D.pertPair φ c k t| ≤ _ := h
            _ = Cst * D.dbar ℓ θ x₀ * (Real.sqrt (D.scInt c k t)
                * Real.sqrt (∑ s : JSt n, c.π k t s *
                  D.Gam φ t s.1 s.2.1)) := by rw [hCst]
      _ = Cst * D.dbar ℓ θ x₀ * ∫ t in c.z k..c.z (k + 1),
            Real.sqrt (D.scInt c k t) * Real.sqrt (∑ s : JSt n, c.π k t s *
              D.Gam φ t s.1 s.2.1) := by
          rw [← intervalIntegral.integral_const_mul]
      _ ≤ Cst * D.dbar ℓ θ x₀ *
          (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)
            * Real.sqrt (∫ t in c.z k..c.z (k + 1),
                ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCst0 hd0)
          exact intervalIntegral_sqrt_mul_le hzk hsc hgc
            (fun t ht => D.scInt_nonneg hθ c hk ht)
            (fun t ht => D.gamInt_nonneg φ hθ c hk ht)
  -- sum the cells: Duhamel + discrete Cauchy–Schwarz
  have hduh := D.duhamel hθ0' hθ c B
  have habs : |D.DtestF c B|
      ≤ ∑ k ∈ Finset.range c.K, |∫ t in c.z k..c.z (k + 1),
          D.pertPair φ c k t| := by
    rw [hduh]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsplit : ∑ k ∈ Finset.range c.K, |∫ t in c.z k..c.z (k + 1),
        D.pertPair φ c k t|
      ≤ Cst * D.dbar ℓ θ x₀ * ∑ k ∈ Finset.range c.K,
          (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)
            * Real.sqrt (∫ t in c.z k..c.z (k + 1),
                ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    exact hcell k (Finset.mem_range.mp hk)
  have hcs : ∑ k ∈ Finset.range c.K,
        (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)
          * Real.sqrt (∫ t in c.z k..c.z (k + 1),
              ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1))
      ≤ Real.sqrt (D.scoreEnergy c) * Real.sqrt (D.gamE φ c) := by
    have h := sum_le_sqrt_mul_sqrt (Finset.range c.K)
      (fun k => Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t))
      (fun k => Real.sqrt (∫ t in c.z k..c.z (k + 1),
        ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1))
      (fun k _ => Real.sqrt_nonneg _) (fun k _ => Real.sqrt_nonneg _)
    have e1 : ∀ k ∈ Finset.range c.K,
        (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)) ^ 2
          = ∫ t in c.z k..c.z (k + 1), D.scInt c k t := fun k hk =>
      Real.sq_sqrt (intervalIntegral.integral_nonneg
        (hmono k (Finset.mem_range.mp hk))
        (fun t ht => D.scInt_nonneg hθ c (Finset.mem_range.mp hk) ht))
    have e2 : ∀ k ∈ Finset.range c.K,
        (Real.sqrt (∫ t in c.z k..c.z (k + 1),
            ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) ^ 2
          = ∫ t in c.z k..c.z (k + 1),
              ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1 := fun k hk =>
      Real.sq_sqrt (intervalIntegral.integral_nonneg
        (hmono k (Finset.mem_range.mp hk))
        (fun t ht => D.gamInt_nonneg φ hθ c (Finset.mem_range.mp hk) ht))
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at h
    exact h
  calc |D.DtestF c B|
      ≤ ∑ k ∈ Finset.range c.K, |∫ t in c.z k..c.z (k + 1),
          D.pertPair φ c k t| := habs
    _ ≤ Cst * D.dbar ℓ θ x₀ * ∑ k ∈ Finset.range c.K,
          (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)
            * Real.sqrt (∫ t in c.z k..c.z (k + 1),
                ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := hsplit
    _ ≤ Cst * D.dbar ℓ θ x₀ *
        (Real.sqrt (D.scoreEnergy c) * Real.sqrt (D.gamE φ c)) := by
        exact mul_le_mul_of_nonneg_left hcs (mul_nonneg hCst0 hd0)
    _ = Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
        * (Real.sqrt (D.scoreEnergy c) * Real.sqrt (D.gamE φ c)) := by
        rw [hCst]

private lemma startW_nonneg'' {θ : ℝ} (hθ : θ ≤ obsT) (x₀ : Cube n) :
    0 ≤ D.startW θ x₀ := by
  have hT : 0 ≤ D.T - θ := by have := D.obsT_lt_T; linarith
  simp only [startW, revDensity]
  exact div_nonneg (D.fs_pos hT x₀).le (by positivity)

private lemma gamE_nonneg (φ : Cube n → ℝ) {ℓ θ : ℝ} (hθ : θ ≤ obsT)
    {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) : 0 ≤ D.gamE φ c := by
  refine Finset.sum_nonneg fun k hk => ?_
  exact intervalIntegral.integral_nonneg
    (c.is.grid.mono k (Finset.mem_range.mp hk))
    (fun t ht => D.gamInt_nonneg φ hθ c (Finset.mem_range.mp hk) ht)

/-- (B6): the `x₀`-weighted discrepancy bound
`|∑_A startW·Dtest| ≤ √8·√κ·Λ·√(𝒮_A)·√(Y_A)` [LGF eq (4.18)]. -/
private lemma abs_sum_Dtest_le (B : Finset (Cube n)) {ℓ θ : ℝ}
    (hθ0' : 0 ≤ θ) (hθ1 : obsT - 1 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) :
    |∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B|
      ≤ Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a
        * (Real.sqrt (D.SA Φ A)
          * Real.sqrt (∑ x₀ ∈ A, D.startW θ x₀ *
              D.gamE (fun w => if w ∈ B then (1 : ℝ) else 0) (Φ x₀))) := by
  classical
  set φ : Cube n → ℝ := fun w => if w ∈ B then (1 : ℝ) else 0 with hφdef
  set Cst := Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a with hCst
  have hCst0 : 0 ≤ Cst := by
    have h3 : (0:ℝ) ≤ Lam D.a := le_trans zero_le_one (one_le_Lam D.ha0 D.ha1)
    have h1 : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ Real.sqrt (kappa D.a) := Real.sqrt_nonneg _
    positivity
  have hsw0 : ∀ x₀ ∈ A, 0 ≤ D.startW θ x₀ := fun x₀ _ => D.startW_nonneg'' hθ x₀
  -- triangle then the per-flow bound with `δ̄·√ = √(δ̄²·)`
  have hstep1 : |∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B|
      ≤ Cst * ∑ x₀ ∈ A, D.startW θ x₀ *
          (Real.sqrt (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))
            * Real.sqrt (D.gamE φ (Φ x₀))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x₀ hx₀ => ?_
    have hd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
    have hsqrt : D.dbar ℓ θ x₀ * Real.sqrt (D.scoreEnergy (Φ x₀))
        = Real.sqrt (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hd0]
    calc |D.startW θ x₀ * D.DtestF (Φ x₀) B|
        = D.startW θ x₀ * |D.DtestF (Φ x₀) B| := by
          rw [abs_mul, abs_of_nonneg (hsw0 x₀ hx₀)]
      _ ≤ D.startW θ x₀ * (Cst * D.dbar ℓ θ x₀ *
            (Real.sqrt (D.scoreEnergy (Φ x₀)) * Real.sqrt (D.gamE φ (Φ x₀)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (hsw0 x₀ hx₀)
          have h := D.abs_DtestF_le B hθ0' hθ1 hθ (Φ x₀)
          calc |D.DtestF (Φ x₀) B| ≤ _ := h
            _ = Cst * D.dbar ℓ θ x₀ *
                (Real.sqrt (D.scoreEnergy (Φ x₀))
                  * Real.sqrt (D.gamE φ (Φ x₀))) := by rw [hCst]
      _ = Cst * (D.startW θ x₀ *
            (Real.sqrt (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))
              * Real.sqrt (D.gamE φ (Φ x₀)))) := by
          rw [← hsqrt]; ring
  -- weighted Cauchy–Schwarz over the starting points
  have hstep2 : ∑ x₀ ∈ A, D.startW θ x₀ *
        (Real.sqrt (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))
          * Real.sqrt (D.gamE φ (Φ x₀)))
      ≤ Real.sqrt (∑ x₀ ∈ A, D.startW θ x₀ *
            (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀)))
        * Real.sqrt (∑ x₀ ∈ A, D.startW θ x₀ * D.gamE φ (Φ x₀)) :=
    weighted_cs A _ _ _ hsw0
      (fun x₀ _ => mul_nonneg (sq_nonneg _) (D.scoreEnergy_nonneg hθ (Φ x₀)))
      (fun x₀ _ => D.gamE_nonneg φ hθ (Φ x₀))
  have hSA : (∑ x₀ ∈ A, D.startW θ x₀ *
        (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))) = D.SA Φ A := by
    refine Finset.sum_congr rfl fun x₀ _ => ?_
    ring
  calc |∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B|
      ≤ Cst * ∑ x₀ ∈ A, D.startW θ x₀ *
          (Real.sqrt (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))
            * Real.sqrt (D.gamE φ (Φ x₀))) := hstep1
    _ ≤ Cst * (Real.sqrt (D.SA Φ A)
          * Real.sqrt (∑ x₀ ∈ A, D.startW θ x₀ * D.gamE φ (Φ x₀))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCst0
        rw [← hSA]
        exact hstep2
    _ = Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a
        * (Real.sqrt (D.SA Φ A)
          * Real.sqrt (∑ x₀ ∈ A, D.startW θ x₀ * D.gamE φ (Φ x₀))) := by
        rw [hCst]

/-! ### Stage C: closing the `Γ`-energy [LGF eq (4.19)–(4.21)]

The `b_t²`-part of `gamE` is bounded by `κ/4` (level-one + `b`-control);
the `a_t²`-part is closed by chaining the flow against
`Q_t(x,y) = ∑_ζ H_t^ζ(x)·q_t^ζ(x,y)²` (carré du champ). -/

/-- The squared-bridge average `Q_t(x,y) = ∑_ζ H^ζ q_ζ²` [LGF eq (4.20)]. -/
private noncomputable def Qtest (φ : Cube n → ℝ) (t : ℝ) (x y : Cube n) : ℝ :=
  ∑ ζ, D.Hlik t ζ x * D.qB φ t ζ x y ^ 2

/-- The `a_t²`-part of the bridge energy density. -/
private noncomputable def apInt (φ : Cube n → ℝ) (t : ℝ) (x y : Cube n) : ℝ :=
  ∑ ζ, D.Hlik t ζ x * ∑ i, D.lam t i x ζ * D.aB t ^ 2
    * dmext φ i (D.mB t x y ζ) ^ 2

/-- The `b_t²`-part of the bridge energy density. -/
private noncomputable def bpInt (φ : Cube n → ℝ) (t : ℝ) (x y : Cube n) : ℝ :=
  ∑ ζ, D.Hlik t ζ x * ∑ i, D.lam t i x ζ * D.bB t ^ 2
    * dmext φ i (D.mB t x y ζ) ^ 2

private lemma Gam_eq_ap_add_bp (φ : Cube n → ℝ) (t : ℝ) (x y : Cube n) :
    D.Gam φ t x y = D.apInt φ t x y + D.bpInt φ t x y := by
  simp only [Gam, apInt, bpInt]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `q_t^ζ(x,y) ∈ [0,1]` for a `{0,1}`-valued test. -/
private lemma qB_mem01 {φ : Cube n → ℝ} (hφ : ∀ w, φ w = 0 ∨ φ w = 1)
    {t : ℝ} (ht : t ≤ obsT) (ζ x y : Cube n) :
    D.qB φ t ζ x y ∈ Set.Icc (0 : ℝ) 1 := by
  have hz : ∀ i, |D.mB t x y ζ i| ≤ 1 := fun i => D.abs_mB_le_one ht x y ζ i
  have hφ01 : ∀ w, φ w ∈ Set.Icc (0 : ℝ) 1 := by
    intro w
    rcases hφ w with h | h <;> rw [h] <;> constructor <;> norm_num
  exact mext_mem_Icc hz hφ01

/-- `Q_t(x,y) ∈ [0,1]` for a `{0,1}`-valued test and `t ≤ T_o`. -/
private lemma Qtest_mem01 {φ : Cube n → ℝ} (hφ : ∀ w, φ w = 0 ∨ φ w = 1)
    {t : ℝ} (ht : t ≤ obsT) (x y : Cube n) :
    D.Qtest φ t x y ∈ Set.Icc (0 : ℝ) 1 := by
  have hT : t ≤ D.T := le_trans ht D.obsT_lt_T.le
  constructor
  · refine Finset.sum_nonneg fun ζ _ => ?_
    exact mul_nonneg (D.Hlik_nonneg hT ζ x) (sq_nonneg _)
  · calc D.Qtest φ t x y
        ≤ ∑ ζ, D.Hlik t ζ x * 1 := by
          refine Finset.sum_le_sum fun ζ _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (D.Hlik_nonneg hT ζ x)
          have h := D.qB_mem01 hφ ht ζ x y
          nlinarith [h.1, h.2]
      _ = 1 := by
          simp only [mul_one]
          exact D.sum_Hlik hT x

/-- Space-time derivative of `Q`: synchronized transport plus twice the
`a_t²`-energy (carré du champ, [LGF eq (4.20)]). -/
private lemma hasDerivAt_Qtest (φ : Cube n → ℝ) {t : ℝ} (ht : t < D.T)
    (x y : Cube n) :
    HasDerivAt (fun t => D.Qtest φ t x y)
      (-(∑ i, D.Y t i x *
          (D.Qtest φ t (flipCoord i x) (flipCoord i y) - D.Qtest φ t x y) / 2)
        + 2 * D.apInt φ t x y) t := by
  have hlam : ∀ (ζ : Cube n) (i : Fin n),
      D.Hlik t ζ x * D.lam t i x ζ = D.Hlik t ζ (flipCoord i x) * D.Y t i x := by
    intro ζ i
    have h0 : D.Hlik t ζ x ≠ 0 := (D.Hlik_pos ht ζ x).ne'
    rw [← D.Hlik_flipCoord_mul_Y ht i ζ x]
    field_simp
  have key : ∀ ζ : Cube n,
      HasDerivAt (fun t => D.Hlik t ζ x * D.qB φ t ζ x y ^ 2)
        (-(∑ i, D.Y t i x *
            (D.Hlik t ζ (flipCoord i x)
                * D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
              - D.Hlik t ζ x * D.qB φ t ζ x y ^ 2) / 2)
          + D.Hlik t ζ x * (2 * D.aB t ^ 2 * ∑ i, D.lam t i x ζ
              * dmext φ i (D.mB t x y ζ) ^ 2)) t := by
    intro ζ
    have hH := D.hasDerivAt_Hlik ht ζ x
    have hq := D.hasDerivAt_qB_sq φ (ne_of_lt ht) ζ x y
    have hprod := hH.mul hq
    have hEq :
        -(D.revGen t (fun w => D.Hlik t ζ w) x) * D.qB φ t ζ x y ^ 2
          + D.Hlik t ζ x *
            (-(∑ i, D.lam t i x ζ *
                (D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
                  - D.qB φ t ζ x y ^ 2) / 2)
              + 2 * D.aB t ^ 2 * ∑ i, D.lam t i x ζ
                  * dmext φ i (D.mB t x y ζ) ^ 2)
        = -(∑ i, D.Y t i x *
            (D.Hlik t ζ (flipCoord i x)
                * D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
              - D.Hlik t ζ x * D.qB φ t ζ x y ^ 2) / 2)
          + D.Hlik t ζ x * (2 * D.aB t ^ 2 * ∑ i, D.lam t i x ζ
              * dmext φ i (D.mB t x y ζ) ^ 2) := by
      have hstep : ∀ i : Fin n,
          D.Y t i x * (D.Hlik t ζ (flipCoord i x) - D.Hlik t ζ x) / 2
              * D.qB φ t ζ x y ^ 2
            + D.Hlik t ζ x *
              (D.lam t i x ζ *
                (D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
                  - D.qB φ t ζ x y ^ 2) / 2)
          = D.Y t i x *
              (D.Hlik t ζ (flipCoord i x)
                  * D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
                - D.Hlik t ζ x * D.qB φ t ζ x y ^ 2) / 2 := by
        intro i
        linear_combination
          ((D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
            - D.qB φ t ζ x y ^ 2) / 2) * hlam ζ i
      have hre : ∀ S P R : ℝ,
          -S * D.qB φ t ζ x y ^ 2 + D.Hlik t ζ x * (-P + R)
            = -(S * D.qB φ t ζ x y ^ 2 + D.Hlik t ζ x * P)
              + D.Hlik t ζ x * R := by
        intro S P R; ring
      rw [revGen, hre, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1
      exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => hstep i)
    rw [← hEq]
    exact hprod
  have hswap : ∀ i : Fin n,
      D.Y t i x * (D.Qtest φ t (flipCoord i x) (flipCoord i y)
          - D.Qtest φ t x y) / 2
        = ∑ ζ : Cube n, D.Y t i x *
            (D.Hlik t ζ (flipCoord i x)
                * D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
              - D.Hlik t ζ x * D.qB φ t ζ x y ^ 2) / 2 := by
    intro i
    rw [Qtest, Qtest, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
  have hap : D.apInt φ t x y
      = ∑ ζ : Cube n, D.Hlik t ζ x * (D.aB t ^ 2 * ∑ i, D.lam t i x ζ
          * dmext φ i (D.mB t x y ζ) ^ 2) := by
    simp only [apInt]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hfin :
      (∑ ζ : Cube n, (-(∑ i, D.Y t i x *
          (D.Hlik t ζ (flipCoord i x)
              * D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
            - D.Hlik t ζ x * D.qB φ t ζ x y ^ 2) / 2)
        + D.Hlik t ζ x * (2 * D.aB t ^ 2 * ∑ i, D.lam t i x ζ
            * dmext φ i (D.mB t x y ζ) ^ 2)))
      = -(∑ i, D.Y t i x *
          (D.Qtest φ t (flipCoord i x) (flipCoord i y) - D.Qtest φ t x y) / 2)
        + 2 * D.apInt φ t x y := by
    rw [Finset.sum_add_distrib]
    congr 1
    · have hneg : ∀ g : Cube n → ℝ, ∑ ζ : Cube n, -(g ζ) = -∑ ζ : Cube n, g ζ := by
        intro g; simp
      rw [hneg]
      refine congrArg Neg.neg ?_
      rw [Finset.sum_congr rfl fun i _ => hswap i, Finset.sum_comm]
    · rw [hap, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ζ _ => ?_
      ring
  have hfun : (fun s => D.Qtest φ s x y)
      = ∑ ζ : Cube n, (fun s => D.Hlik s ζ x * D.qB φ s ζ x y ^ 2) := by
    funext s
    simp only [Finset.sum_apply, Qtest]
  rw [← hfin, hfun]
  exact HasDerivAt.sum (u := (Finset.univ : Finset (Cube n))) fun ζ _ => key ζ

/-- The conditioned-power/bridge bound on `∑_i pgm²` ([LGF eq (4.17)]'s
engine, extracted for reuse by the `q²`-perturbation). -/
private lemma pgm_sq_sum_le {ℓ θ t : ℝ} (ht : t ≤ obsT)
    (φ : Cube n → ℝ) (x₀ : Cube n) (x y : Cube n) :
    ∑ i, D.pgm φ ℓ θ t x₀ i x y ^ 2
      ≤ 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.Gam φ t x y := by
  have htT : t < D.T := lt_of_le_of_lt ht D.obsT_lt_T
  have hC : ∀ i : Fin n, D.pgm φ ℓ θ t x₀ i x y ^ 2
      ≤ 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
          ∑ ζ : Cube n, D.Hlik t ζ x *
            (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2) := by
    intro i
    have hw := sq_weighted_le (Finset.univ : Finset (Cube n)) (fun ζ => D.Hlik t ζ x)
      (fun ζ => 2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
        * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|)
      (fun ζ _ => D.Hlik_nonneg htT.le ζ x)
    rw [D.sum_Hlik htT.le x, one_mul] at hw
    refine le_trans hw ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ζ _ => ?_
    have hH := D.Hlik_nonneg htT.le ζ x
    have hcpb := D.conditioned_power_bound (ℓ := ℓ) (θ := θ) (x₀ := x₀) ht i x ζ
    have hcpb' : (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
        ≤ kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ := by
      simpa only [pwt] using hcpb
    have hab2 : (D.aB t + D.bB t) ^ 2 ≤ 2 * (D.aB t ^ 2 + D.bB t ^ 2) := by
      nlinarith [sq_nonneg (D.aB t - D.bB t)]
    have hQ0 : (0 : ℝ) ≤ (D.aB t + D.bB t) ^ 2 := sq_nonneg _
    have hR0 : (0 : ℝ) ≤ dmext φ i (D.mB t x y ζ) ^ 2 := sq_nonneg _
    have hP'0 : (0 : ℝ)
        ≤ kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ :=
      le_trans (sq_nonneg _) hcpb'
    have hPQ : (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
          * (D.aB t + D.bB t) ^ 2
        ≤ (kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ)
          * (2 * (D.aB t ^ 2 + D.bB t ^ 2)) :=
      mul_le_mul hcpb' hab2 hQ0 hP'0
    have hsqexp : (2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
          * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|) ^ 2
        = 4 * ((powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
            * (D.aB t + D.bB t) ^ 2) * dmext φ i (D.mB t x y ζ) ^ 2 := by
      have e1 : |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ| ^ 2
          = (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2 := sq_abs _
      have e2 : |dmext φ i (D.mB t x y ζ)| ^ 2
          = dmext φ i (D.mB t x y ζ) ^ 2 := sq_abs _
      calc (2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
              * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|) ^ 2
          = 4 * (|powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ| ^ 2
              * (D.aB t + D.bB t) ^ 2) * |dmext φ i (D.mB t x y ζ)| ^ 2 := by ring
        _ = _ := by rw [e1, e2]
    rw [hsqexp]
    have h4 := mul_le_mul_of_nonneg_left hPQ (by norm_num : (0 : ℝ) ≤ 4)
    have h5 := mul_le_mul_of_nonneg_right h4 hR0
    have hfin : 4 * ((powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
          * (D.aB t + D.bB t) ^ 2) * dmext φ i (D.mB t x y ζ) ^ 2
        ≤ 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
            (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2) := by
      calc 4 * ((powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ) ^ 2
              * (D.aB t + D.bB t) ^ 2) * dmext φ i (D.mB t x y ζ) ^ 2
          ≤ 4 * ((kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ)
              * (2 * (D.aB t ^ 2 + D.bB t ^ 2))) * dmext φ i (D.mB t x y ζ) ^ 2 := h5
        _ = _ := by ring
    calc D.Hlik t ζ x * (4 * ((powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)
            * D.pwt t i x ζ) ^ 2 * (D.aB t + D.bB t) ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2)
        ≤ D.Hlik t ζ x * (8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
            (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2)) := mul_le_mul_of_nonneg_left hfin hH
      _ = 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
            (D.Hlik t ζ x * (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2)) := by ring
  calc ∑ i, D.pgm φ ℓ θ t x₀ i x y ^ 2
      ≤ ∑ i, 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
          ∑ ζ : Cube n, D.Hlik t ζ x *
            (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2) :=
        Finset.sum_le_sum fun i _ => hC i
    _ = 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 *
          ∑ i, ∑ ζ : Cube n, D.Hlik t ζ x *
            (D.lam t i x ζ * (D.aB t ^ 2 + D.bB t ^ 2)
              * dmext φ i (D.mB t x y ζ) ^ 2) := by rw [Finset.mul_sum]
    _ = 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.Gam φ t x y := by
        refine congrArg _ ?_
        rw [Gam, Finset.sum_comm]
        exact Finset.sum_congr rfl fun ζ _ => by rw [Finset.mul_sum]

/-- The `q²`-perturbation at one state (the analogue of `pertU` for the
carré-du-champ chain [LGF eq (4.20)]). -/
private noncomputable def pertQ (φ : Cube n → ℝ) (ℓ θ : ℝ) (x₀ : Cube n)
    (t : ℝ) (x y : Cube n) : ℝ :=
  ∑ i, (if D.Y t i x < 1 then
      (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
        (D.Qtest φ t x (flipCoord i y) - D.Qtest φ t x y)
    else
      -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2) *
        (D.Qtest φ t (flipCoord i x) (flipCoord i y)
          - D.Qtest φ t (flipCoord i x) y))

/-- Pointwise bound on the `q²`-perturbation: twice the `pertU` bound
(`|Δ(q²)| ≤ 2|Δq|` for `q ∈ [0,1]`) [LGF, proof of eq (4.21)]. -/
private lemma abs_pertQ_le {ℓ θ t : ℝ} (ht0 : θ ≤ t) (ht : t ≤ obsT)
    (hθ : θ ≤ obsT) {x₀ : Cube n} {φ : Cube n → ℝ}
    (hφ : ∀ w, φ w = 0 ∨ φ w = 1) (x y : Cube n) :
    |D.pertQ φ ℓ θ x₀ t x y|
      ≤ 2 * (Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
        * Real.sqrt (∑ i, D.Sc t i x ^ 2) * Real.sqrt (D.Gam φ t x y)) := by
  have htT : t < D.T := lt_of_le_of_lt ht D.obsT_lt_T
  have hLam0 : (0 : ℝ) ≤ Lam D.a := le_trans zero_le_one (one_le_Lam D.ha0 D.ha1)
  have hd0 : (0 : ℝ) ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
  have hk1 : 1 < kappa D.a := one_lt_kappa D.ha0 D.ha1
  -- (B') per-coordinate modulus bound with the extra factor 2
  have hB : ∀ i : Fin n,
      |(if D.Y t i x < 1 then
          (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
            (D.Qtest φ t x (flipCoord i y) - D.Qtest φ t x y)
        else
          -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2) *
            (D.Qtest φ t (flipCoord i x) (flipCoord i y)
              - D.Qtest φ t (flipCoord i x) y))|
        ≤ |D.Sc t i x| * (2 * D.pgm φ ℓ θ t x₀ i x y) := by
    intro i
    have hYpos : 0 < D.Y t i x := D.Y_pos htT.le i x
    have hq01 : ∀ ζ v w, D.qB φ t ζ v w ∈ Set.Icc (0:ℝ) 1 :=
      fun ζ v w => D.qB_mem01 hφ ht ζ v w
    by_cases hY : D.Y t i x < 1
    · -- `W`-only branch: `Δ_i^y Q = ∑_ζ H·(q'+q)·Δ_i^y q`
      have hs : 0 < D.Sc t i x := by simp only [Sc]; linarith
      have hcoef : (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2
          = powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.Sc t i x := by
        simp only [Sc]; exact one_sub_rpow_eq hYpos hY
      have hdiff : D.Qtest φ t x (flipCoord i y) - D.Qtest φ t x y
          = ∑ ζ : Cube n, D.Hlik t ζ x *
              ((D.qB φ t ζ x (flipCoord i y) + D.qB φ t ζ x y) *
                (-2 * D.mB t x y ζ i * dmext φ i (D.mB t x y ζ))) := by
        rw [Qtest, Qtest, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ζ _ => ?_
        rw [← mul_sub]
        congr 1
        have hfac : D.qB φ t ζ x (flipCoord i y) ^ 2 - D.qB φ t ζ x y ^ 2
            = (D.qB φ t ζ x (flipCoord i y) + D.qB φ t ζ x y) *
              (D.qB φ t ζ x (flipCoord i y) - D.qB φ t ζ x y) := by ring
        rw [hfac, D.qB_flip_y_sub φ t ζ x y i]
      rw [if_pos hY, hcoef, hdiff, abs_mul, abs_mul, mul_comm
        |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)| |D.Sc t i x|,
        mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [pgm, Finset.mul_sum, ← Finset.mul_sum]
      calc |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)| *
            |∑ ζ : Cube n, D.Hlik t ζ x *
              ((D.qB φ t ζ x (flipCoord i y) + D.qB φ t ζ x y) *
                (-2 * D.mB t x y ζ i * dmext φ i (D.mB t x y ζ)))|
          ≤ |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)| *
            ∑ ζ : Cube n, D.Hlik t ζ x *
              (2 * (2 * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|)) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
            refine Finset.sum_le_sum fun ζ _ => ?_
            have hH := D.Hlik_nonneg htT.le ζ x
            rw [abs_mul, abs_of_nonneg hH]
            refine mul_le_mul_of_nonneg_left ?_ hH
            have hq1 := hq01 ζ x (flipCoord i y)
            have hq2 := hq01 ζ x y
            have hsum2 : |D.qB φ t ζ x (flipCoord i y) + D.qB φ t ζ x y| ≤ 2 := by
              rw [abs_of_nonneg (by linarith [hq1.1, hq2.1])]
              linarith [hq1.2, hq2.2]
            have hmB : |D.mB t x y ζ i| ≤ D.aB t + D.bB t := by
              have h1 := D.abs_mB_le_one ht x y ζ i
              have h2 : |D.mB t x y ζ i| ≤ |D.aB t * toR (y i)|
                  + |D.bB t * toR (x i) * toR (y i) * toR (ζ i)| := by
                simp only [mB]
                exact abs_add_le _ _
              have e1 : |D.aB t * toR (y i)| = D.aB t := by
                rw [abs_mul, abs_toR, mul_one, abs_of_nonneg (D.aB_nonneg ht)]
              have e2 : |D.bB t * toR (x i) * toR (y i) * toR (ζ i)| = D.bB t := by
                rw [abs_mul, abs_mul, abs_mul, abs_toR, abs_toR, abs_toR,
                  abs_of_nonneg (D.bB_nonneg ht)]
                ring
              rw [e1, e2] at h2
              exact h2
            calc |(D.qB φ t ζ x (flipCoord i y) + D.qB φ t ζ x y) *
                  (-2 * D.mB t x y ζ i * dmext φ i (D.mB t x y ζ))|
                = |D.qB φ t ζ x (flipCoord i y) + D.qB φ t ζ x y| *
                  (2 * |D.mB t x y ζ i| * |dmext φ i (D.mB t x y ζ)|) := by
                  rw [abs_mul, abs_mul, abs_mul]
                  norm_num
              _ ≤ 2 * (2 * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|) := by
                  have hd2 : (0:ℝ) ≤ |dmext φ i (D.mB t x y ζ)| := abs_nonneg _
                  have s1 : |D.qB φ t ζ x (flipCoord i y) + D.qB φ t ζ x y| *
                        (2 * |D.mB t x y ζ i| * |dmext φ i (D.mB t x y ζ)|)
                      ≤ 2 * (2 * |D.mB t x y ζ i|
                        * |dmext φ i (D.mB t x y ζ)|) :=
                    mul_le_mul_of_nonneg_right hsum2 (by positivity)
                  have s2 : |D.mB t x y ζ i| * |dmext φ i (D.mB t x y ζ)|
                      ≤ (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)| :=
                    mul_le_mul_of_nonneg_right hmB hd2
                  linarith
        _ ≤ ∑ ζ : Cube n, D.Hlik t ζ x *
              (2 * (2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)
                  * D.pwt t i x ζ| * (D.aB t + D.bB t)
                * |dmext φ i (D.mB t x y ζ)|)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun ζ _ => ?_
            have hH := D.Hlik_nonneg htT.le ζ x
            have hpwt : D.pwt t i x ζ = 1 := by
              simp only [pwt, if_pos hs]
            rw [hpwt, mul_one]
            calc |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)| *
                  (D.Hlik t ζ x * (2 * (2 * (D.aB t + D.bB t)
                    * |dmext φ i (D.mB t x y ζ)|)))
                = D.Hlik t ζ x * (2 * (2
                    * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)|
                    * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|)) := by
                  ring
              _ ≤ _ := le_of_eq rfl
        _ = 2 * ∑ ζ : Cube n, D.Hlik t ζ x *
              (2 * |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.pwt t i x ζ|
                * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun ζ _ => ?_
            have hpwt : D.pwt t i x ζ = 1 := by
              simp only [pwt, if_pos hs]
            rw [hpwt, mul_one]
            ring
    · -- `V`-only branch (`Y ≥ 1`)
      have hY' : 1 ≤ D.Y t i x := not_lt.mp hY
      have hs : ¬ (0 < D.Sc t i x) := by
        simp only [Sc]; push_neg; linarith
      rw [if_neg hY]
      rcases eq_or_lt_of_le hY' with hY1 | hY1
      · have hSc : D.Sc t i x = 0 := by simp only [Sc, ← hY1]; ring
        have hz : D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀) = 0 := by
          rw [← hY1, Real.one_rpow]; ring
        rw [hSc, hz]
        simp
      · have hcoef : -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2)
            = powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) * D.Sc t i x := by
          simp only [Sc]
          rw [rpow_sub_eq hY1]
          ring
        have hHflip : ∀ ζ : Cube n, D.Hlik t ζ (flipCoord i x)
            = D.Hlik t ζ x * D.pwt t i x ζ := by
          intro ζ
          have hY0 : D.Y t i x ≠ 0 := ne_of_gt hYpos
          have h0 : D.Hlik t ζ x ≠ 0 := (D.Hlik_pos htT ζ x).ne'
          simp only [pwt, if_neg hs]
          rw [← D.Hlik_flipCoord_mul_Y htT i ζ x]
          field_simp
        have hpwt0 : ∀ ζ : Cube n, 0 ≤ D.pwt t i x ζ := by
          intro ζ
          simp only [pwt, if_neg hs]
          exact div_nonneg (D.lam_pos ht i x ζ).le hYpos.le
        have hdiff : D.Qtest φ t (flipCoord i x) (flipCoord i y)
              - D.Qtest φ t (flipCoord i x) y
            = ∑ ζ : Cube n, D.Hlik t ζ x * (D.pwt t i x ζ *
                ((D.qB φ t ζ (flipCoord i x) (flipCoord i y)
                    + D.qB φ t ζ (flipCoord i x) y) *
                  (-2 * (D.aB t * toR (y i)
                      - D.bB t * toR (x i) * toR (y i) * toR (ζ i))
                    * dmext φ i (D.mB t x y ζ)))) := by
          rw [Qtest, Qtest, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun ζ _ => ?_
          rw [← mul_sub, hHflip ζ]
          have hfac : D.qB φ t ζ (flipCoord i x) (flipCoord i y) ^ 2
                - D.qB φ t ζ (flipCoord i x) y ^ 2
              = (D.qB φ t ζ (flipCoord i x) (flipCoord i y)
                  + D.qB φ t ζ (flipCoord i x) y) *
                (D.qB φ t ζ (flipCoord i x) (flipCoord i y)
                  - D.qB φ t ζ (flipCoord i x) y) := by ring
          rw [mul_assoc, hfac, D.qB_flip_y_flip_x_sub φ t ζ x y i]
        rw [hcoef, hdiff, abs_mul, abs_mul, mul_comm
          |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)| |D.Sc t i x|, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hperζ : ∀ ζ : Cube n,
            |D.Hlik t ζ x * (D.pwt t i x ζ *
              ((D.qB φ t ζ (flipCoord i x) (flipCoord i y)
                  + D.qB φ t ζ (flipCoord i x) y) *
                (-2 * (D.aB t * toR (y i)
                    - D.bB t * toR (x i) * toR (y i) * toR (ζ i))
                  * dmext φ i (D.mB t x y ζ))))|
              ≤ D.Hlik t ζ x * (D.pwt t i x ζ *
                (2 * (2 * (D.aB t + D.bB t)
                  * |dmext φ i (D.mB t x y ζ)|))) := by
          intro ζ
          have hH := D.Hlik_nonneg htT.le ζ x
          have hq1 := hq01 ζ (flipCoord i x) (flipCoord i y)
          have hq2 := hq01 ζ (flipCoord i x) y
          have hsum2 : |D.qB φ t ζ (flipCoord i x) (flipCoord i y)
              + D.qB φ t ζ (flipCoord i x) y| ≤ 2 := by
            rw [abs_of_nonneg (by linarith [hq1.1, hq2.1])]
            linarith [hq1.2, hq2.2]
          have hpc : |D.aB t * toR (y i)
              - D.bB t * toR (x i) * toR (y i) * toR (ζ i)| ≤ D.aB t + D.bB t := by
            have h := D.abs_pcf_le ht i x y ζ
            simpa only [pcf, if_neg hs] using h
          rw [abs_mul, abs_of_nonneg hH, abs_mul, abs_of_nonneg (hpwt0 ζ)]
          refine mul_le_mul_of_nonneg_left ?_ hH
          refine mul_le_mul_of_nonneg_left ?_ (hpwt0 ζ)
          calc |(D.qB φ t ζ (flipCoord i x) (flipCoord i y)
                + D.qB φ t ζ (flipCoord i x) y) *
              (-2 * (D.aB t * toR (y i)
                  - D.bB t * toR (x i) * toR (y i) * toR (ζ i))
                * dmext φ i (D.mB t x y ζ))|
              = |D.qB φ t ζ (flipCoord i x) (flipCoord i y)
                  + D.qB φ t ζ (flipCoord i x) y| *
                (2 * |D.aB t * toR (y i)
                    - D.bB t * toR (x i) * toR (y i) * toR (ζ i)|
                  * |dmext φ i (D.mB t x y ζ)|) := by
                rw [abs_mul, abs_mul, abs_mul]
                norm_num
            _ ≤ 2 * (2 * (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)|) := by
                have hd2 : (0:ℝ) ≤ |dmext φ i (D.mB t x y ζ)| := abs_nonneg _
                have s1 : |D.qB φ t ζ (flipCoord i x) (flipCoord i y)
                      + D.qB φ t ζ (flipCoord i x) y| *
                      (2 * |D.aB t * toR (y i)
                          - D.bB t * toR (x i) * toR (y i) * toR (ζ i)|
                        * |dmext φ i (D.mB t x y ζ)|)
                    ≤ 2 * (2 * |D.aB t * toR (y i)
                        - D.bB t * toR (x i) * toR (y i) * toR (ζ i)|
                      * |dmext φ i (D.mB t x y ζ)|) :=
                  mul_le_mul_of_nonneg_right hsum2 (by positivity)
                have s2 : |D.aB t * toR (y i)
                      - D.bB t * toR (x i) * toR (y i) * toR (ζ i)|
                      * |dmext φ i (D.mB t x y ζ)|
                    ≤ (D.aB t + D.bB t) * |dmext φ i (D.mB t x y ζ)| :=
                  mul_le_mul_of_nonneg_right hpc hd2
                linarith
        calc |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)| *
              |∑ ζ : Cube n, D.Hlik t ζ x * (D.pwt t i x ζ *
                ((D.qB φ t ζ (flipCoord i x) (flipCoord i y)
                    + D.qB φ t ζ (flipCoord i x) y) *
                  (-2 * (D.aB t * toR (y i)
                      - D.bB t * toR (x i) * toR (y i) * toR (ζ i))
                    * dmext φ i (D.mB t x y ζ))))|
            ≤ |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)| *
              ∑ ζ : Cube n, D.Hlik t ζ x * (D.pwt t i x ζ *
                (2 * (2 * (D.aB t + D.bB t)
                  * |dmext φ i (D.mB t x y ζ)|))) := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact le_trans (Finset.abs_sum_le_sum_abs _ _)
                (Finset.sum_le_sum fun ζ _ => hperζ ζ)
          _ = 2 * D.pgm φ ℓ θ t x₀ i x y := by
              rw [pgm, Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun ζ _ => ?_
              have habsmul : |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)
                  * D.pwt t i x ζ|
                  = |powerRatio (D.dbar ℓ θ x₀) (D.Y t i x)| * D.pwt t i x ζ := by
                rw [abs_mul, abs_of_nonneg (hpwt0 ζ)]
              rw [habsmul]
              ring
  -- (E') assemble: `ℓ¹`–`ℓ²` and the extracted engine
  have hE1 : |D.pertQ φ ℓ θ x₀ t x y|
      ≤ 2 * ∑ i, |D.Sc t i x| * D.pgm φ ℓ θ t x₀ i x y := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := hB i
    calc |(if D.Y t i x < 1 then
          (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
            (D.Qtest φ t x (flipCoord i y) - D.Qtest φ t x y)
        else
          -((D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2) *
            (D.Qtest φ t (flipCoord i x) (flipCoord i y)
              - D.Qtest φ t (flipCoord i x) y))|
        ≤ |D.Sc t i x| * (2 * D.pgm φ ℓ θ t x₀ i x y) := h
      _ = 2 * (|D.Sc t i x| * D.pgm φ ℓ θ t x₀ i x y) := by ring
  have hE2 : ∑ i, |D.Sc t i x| * D.pgm φ ℓ θ t x₀ i x y
      ≤ Real.sqrt (∑ i, D.Sc t i x ^ 2)
        * Real.sqrt (∑ i, D.pgm φ ℓ θ t x₀ i x y ^ 2) := by
    have h := sum_le_sqrt_mul_sqrt Finset.univ (fun i => |D.Sc t i x|)
      (fun i => D.pgm φ ℓ θ t x₀ i x y)
      (fun i _ => abs_nonneg _)
      (fun i _ => D.pgm_nonneg ht htT.le φ x₀ i x y)
    have e1 : ∀ i : Fin n, |D.Sc t i x| ^ 2 = D.Sc t i x ^ 2 :=
      fun i => sq_abs _
    rw [Finset.sum_congr rfl fun i _ => e1 i] at h
    exact h
  have hE3 : Real.sqrt (∑ i, D.pgm φ ℓ θ t x₀ i x y ^ 2)
      ≤ Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
        * Real.sqrt (D.Gam φ t x y) := by
    have h8k : (0 : ℝ) ≤ 8 * kappa D.a := by linarith
    have hA1 : (0 : ℝ) ≤ 8 * kappa D.a * Lam D.a ^ 2 := mul_nonneg h8k (sq_nonneg _)
    have hA2 : (0 : ℝ) ≤ 8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 :=
      mul_nonneg hA1 (sq_nonneg _)
    have hsqrt : Real.sqrt (8 * kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2
          * D.Gam φ t x y)
        = Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
          * Real.sqrt (D.Gam φ t x y) := by
      rw [Real.sqrt_mul hA2, Real.sqrt_mul hA1, Real.sqrt_mul h8k,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_sq hLam0,
        Real.sqrt_sq hd0]
    rw [← hsqrt]
    exact Real.sqrt_le_sqrt (D.pgm_sq_sum_le ht φ x₀ x y)
  calc |D.pertQ φ ℓ θ x₀ t x y|
      ≤ 2 * ∑ i, |D.Sc t i x| * D.pgm φ ℓ θ t x₀ i x y := hE1
    _ ≤ 2 * (Real.sqrt (∑ i, D.Sc t i x ^ 2)
          * Real.sqrt (∑ i, D.pgm φ ℓ θ t x₀ i x y ^ 2)) := by
        have := hE2; linarith
    _ ≤ 2 * (Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a * D.dbar ℓ θ x₀
          * Real.sqrt (∑ i, D.Sc t i x ^ 2) * Real.sqrt (D.Gam φ t x y)) := by
        have hs0 : (0:ℝ) ≤ Real.sqrt (∑ i, D.Sc t i x ^ 2) := Real.sqrt_nonneg _
        have h := mul_le_mul_of_nonneg_left hE3 hs0
        nlinarith [h]

/-- Alive jump pairing against `Q` (mirror of the `U`-version). -/
private lemma jrate_Q_pair_alive (φ : Cube n → ℝ) {ℓ θ : ℝ} (x₀ : Cube n)
    (B : Set (Cube n)) (t : ℝ) (x y : Cube n) :
    ∑ τ : JSt n, D.jrate (D.dbar ℓ θ x₀) B t (x, y, true) τ *
        (D.Qtest φ t τ.1 τ.2.1 - D.Qtest φ t x y)
      = (∑ i, D.Y t i x *
          (D.Qtest φ t (flipCoord i x) (flipCoord i y) - D.Qtest φ t x y) / 2)
        + D.pertQ φ ℓ θ x₀ t x y := by
  rw [D.jrate_pair_true' (D.dbar ℓ θ x₀) B t x y
    (fun τ => D.Qtest φ t τ.1 τ.2.1 - D.Qtest φ t x y), pertQ,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hY : D.Y t i x < 1
  · simp only [if_pos hY]
    ring
  · simp only [if_neg hY]
    ring

/-- Dead jump pairing against `Q`. -/
private lemma jrate_Q_pair_dead (φ : Cube n → ℝ) (dd : ℝ)
    (B : Set (Cube n)) (t : ℝ) (x y : Cube n) :
    ∑ τ : JSt n, D.jrate dd B t (x, y, false) τ *
        (D.Qtest φ t τ.1 τ.2.1 - D.Qtest φ t x y)
      = ∑ i, D.Y t i x *
          (D.Qtest φ t (flipCoord i x) (flipCoord i y) - D.Qtest φ t x y) / 2 := by
  rw [D.jrate_pair_false' dd B t x y
    (fun τ => D.Qtest φ t τ.1 τ.2.1 - D.Qtest φ t x y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The `Q`-pairing of the flow in cell `k`. -/
private noncomputable def qPair (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ s : JSt n, c.π k t s * D.Qtest φ t s.1 s.2.1

/-- The alive `q²`-perturbation integrand. -/
private noncomputable def pertQPair (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ s : JSt n, (if s.2.2 = true then
    c.π k t s * D.pertQ φ ℓ θ x₀ t s.1 s.2.1 else 0)

/-- The (full-sector) `a_t²`-energy integrand. -/
private noncomputable def apPair (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ s : JSt n, c.π k t s * D.apInt φ t s.1 s.2.1

/-- Cell derivative of the `Q`-pairing: alive perturbation plus twice the
`a_t²`-energy (both sectors) [LGF eq (4.20)]. -/
private lemma qPair_hasDeriv (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) {k : ℕ} (hk : k < c.K) {t : ℝ}
    (ht : t ∈ Set.Icc (c.z k) (c.z (k + 1))) :
    HasDerivWithinAt (D.qPair φ c k)
      (D.pertQPair φ c k t + 2 * D.apPair φ c k t)
      (Set.Icc (c.z k) (c.z (k + 1))) t := by
  classical
  have hzo : c.z (k + 1) ≤ obsT := D.cell_le_obsT c hk
  have htT : t < D.T := lt_of_le_of_lt (le_trans ht.2 hzo) D.obsT_lt_T
  have hg : ∀ s : JSt n,
      HasDerivWithinAt (fun u => D.Qtest φ u s.1 s.2.1)
        (-(∑ i, D.Y t i s.1 *
          (D.Qtest φ t (flipCoord i s.1) (flipCoord i s.2.1)
            - D.Qtest φ t s.1 s.2.1) / 2) + 2 * D.apInt φ t s.1 s.2.1)
        (Set.Icc (c.z k) (c.z (k + 1))) t :=
    fun s => (D.hasDerivAt_Qtest φ htT s.1 s.2.1).hasDerivWithinAt
  have hpair := hasDerivWithinAt_pairing (c.is.glued.flow k hk) ht hg
  have hval : (∑ s : JSt n,
      (matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s
          * D.Qtest φ t s.1 s.2.1
        + c.π k t s * (-(∑ i, D.Y t i s.1 *
            (D.Qtest φ t (flipCoord i s.1) (flipCoord i s.2.1)
              - D.Qtest φ t s.1 s.2.1) / 2) + 2 * D.apInt φ t s.1 s.2.1)))
      = D.pertQPair φ c k t + 2 * D.apPair φ c k t := by
    have hsplit : ∀ s : JSt n,
        matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s
            * D.Qtest φ t s.1 s.2.1
          + c.π k t s * (-(∑ i, D.Y t i s.1 *
              (D.Qtest φ t (flipCoord i s.1) (flipCoord i s.2.1)
                - D.Qtest φ t s.1 s.2.1) / 2) + 2 * D.apInt φ t s.1 s.2.1)
        = (matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s
            * D.Qtest φ t s.1 s.2.1
          + c.π k t s * -(∑ i, D.Y t i s.1 *
              (D.Qtest φ t (flipCoord i s.1) (flipCoord i s.2.1)
                - D.Qtest φ t s.1 s.2.1) / 2))
          + c.π k t s * (2 * D.apInt φ t s.1 s.2.1) := by
      intro s; ring
    rw [Finset.sum_congr rfl fun s _ => hsplit s, Finset.sum_add_distrib]
    have hfirst : (∑ s : JSt n,
        (matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s
            * D.Qtest φ t s.1 s.2.1
          + c.π k t s * -(∑ i, D.Y t i s.1 *
              (D.Qtest φ t (flipCoord i s.1) (flipCoord i s.2.1)
                - D.Qtest φ t s.1 s.2.1) / 2)))
        = D.pertQPair φ c k t := by
      rw [Finset.sum_add_distrib]
      have hA : ∑ s : JSt n,
          matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s
            * D.Qtest φ t s.1 s.2.1
          = ∑ σ : JSt n, c.π k t σ *
              (∑ τ : JSt n, D.jrate (D.dbar ℓ θ x₀)
                (D.barrier ℓ ((c.z k + c.z (k + 1)) / 2)) t σ τ *
                (D.Qtest φ t τ.1 τ.2.1 - D.Qtest φ t σ.1 σ.2.1)) := by
        simp only [cellGen]
        exact matVec_fwdOf_pairing _ _ _
      rw [hA, ← Finset.sum_add_distrib, pertQPair]
      refine Finset.sum_congr rfl fun σ _ => ?_
      obtain ⟨x, y, b⟩ := σ
      cases b with
      | true =>
        rw [D.jrate_Q_pair_alive φ x₀ _ t x y]
        have hcond : (((x, y, true) : JSt n).2.2 = true) := rfl
        rw [if_pos hcond]
        ring
      | false =>
        rw [D.jrate_Q_pair_dead φ _ _ t x y]
        have hif : (if ((x, y, false) : JSt n).2.2 = true then
            c.π k t (x, y, false) * D.pertQ φ ℓ θ x₀ t x y else 0) = 0 := by
          simp
        rw [hif]
        ring
    have hsecond : (∑ s : JSt n, c.π k t s * (2 * D.apInt φ t s.1 s.2.1))
        = 2 * D.apPair φ c k t := by
      rw [apPair, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hfirst, hsecond]
  have hfun : (fun u => ∑ s : JSt n, c.π k u s * D.Qtest φ u s.1 s.2.1)
      = D.qPair φ c k := rfl
  rw [hfun, hval] at hpair
  exact hpair

private lemma continuousOn_Qtest (φ : Cube n → ℝ) {a b : ℝ} (hb : b < D.T)
    (x y : Cube n) :
    ContinuousOn (fun t => D.Qtest φ t x y) (Set.Icc a b) := fun t ht =>
  ((D.hasDerivAt_Qtest φ (lt_of_le_of_lt ht.2 hb) x y).continuousAt).continuousWithinAt

/-- `max`-form of the `q²`-perturbation coefficients. -/
private lemma pertQ_eq_max_form (φ : Cube n → ℝ) (ℓ θ : ℝ) (x₀ : Cube n)
    {t : ℝ} (ht : t ≤ D.T) (x y : Cube n) :
    D.pertQ φ ℓ θ x₀ t x y
      = ∑ i, (max (1 - D.Y t i x ^ D.dbar ℓ θ x₀) 0 / 2 *
          (D.Qtest φ t x (flipCoord i y) - D.Qtest φ t x y)
        - max (D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) 0 / 2 *
          (D.Qtest φ t (flipCoord i x) (flipCoord i y)
            - D.Qtest φ t (flipCoord i x) y)) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hY0 : 0 < D.Y t i x := D.Y_pos ht i x
  have hd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
  have hd1 : D.dbar ℓ θ x₀ ≤ 1 := by
    have := D.dbar_lt_half ℓ θ x₀; linarith
  by_cases hY : D.Y t i x < 1
  · have h1 : D.Y t i x ^ D.dbar ℓ θ x₀ ≤ 1 :=
      Real.rpow_le_one hY0.le hY.le hd0
    have h2 : D.Y t i x ≤ D.Y t i x ^ (1 - D.dbar ℓ θ x₀) := by
      have := Real.rpow_le_rpow_of_exponent_ge hY0 hY.le
        (show 1 - D.dbar ℓ θ x₀ ≤ 1 by linarith)
      simpa [Real.rpow_one] using this
    rw [if_pos hY, max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · push_neg at hY
    have h1 : 1 ≤ D.Y t i x ^ D.dbar ℓ θ x₀ := Real.one_le_rpow hY hd0
    have h2 : D.Y t i x ^ (1 - D.dbar ℓ θ x₀) ≤ D.Y t i x := by
      have := Real.rpow_le_rpow_of_exponent_le hY
        (show 1 - D.dbar ℓ θ x₀ ≤ 1 by linarith)
      simpa [Real.rpow_one] using this
    rw [if_neg (not_lt.mpr hY), max_eq_right (by linarith),
      max_eq_left (by linarith)]
    ring

private lemma continuousOn_pertQ (φ : Cube n → ℝ) (ℓ θ : ℝ) (x₀ : Cube n)
    {a b : ℝ} (hb : b < D.T) (x y : Cube n) :
    ContinuousOn (fun t => D.pertQ φ ℓ θ x₀ t x y) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Iic D.T := fun t ht =>
    le_of_lt (lt_of_le_of_lt ht.2 hb)
  have hforms : ∀ t ∈ Set.Icc a b, D.pertQ φ ℓ θ x₀ t x y
      = ∑ i, (max (1 - D.Y t i x ^ D.dbar ℓ θ x₀) 0 / 2 *
          (D.Qtest φ t x (flipCoord i y) - D.Qtest φ t x y)
        - max (D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) 0 / 2 *
          (D.Qtest φ t (flipCoord i x) (flipCoord i y)
            - D.Qtest φ t (flipCoord i x) y)) := fun t ht =>
    D.pertQ_eq_max_form φ ℓ θ x₀ (hsub ht) x y
  refine ContinuousOn.congr ?_ hforms
  refine continuousOn_finset_sum _ fun i _ => ?_
  have hYc : ContinuousOn (fun t => D.Y t i x) (Set.Icc a b) :=
    (D.continuousOn_Y i x).mono hsub
  have hYne : ∀ t ∈ Set.Icc a b, D.Y t i x ≠ 0 := fun t ht =>
    (D.Y_pos (hsub ht) i x).ne'
  have hr1 : ContinuousOn (fun t => D.Y t i x ^ D.dbar ℓ θ x₀) (Set.Icc a b) :=
    hYc.rpow_const fun t ht => Or.inl (hYne t ht)
  have hr2 : ContinuousOn (fun t => D.Y t i x ^ (1 - D.dbar ℓ θ x₀))
      (Set.Icc a b) := hYc.rpow_const fun t ht => Or.inl (hYne t ht)
  exact ((ContinuousOn.div_const (contOn_max
        (continuousOn_const.sub hr1) continuousOn_const) 2).mul
      ((D.continuousOn_Qtest φ hb x (flipCoord i y)).sub
        (D.continuousOn_Qtest φ hb x y))).sub
    ((ContinuousOn.div_const (contOn_max
        (hYc.sub hr2) continuousOn_const) 2).mul
      ((D.continuousOn_Qtest φ hb (flipCoord i x) (flipCoord i y)).sub
        (D.continuousOn_Qtest φ hb (flipCoord i x) y)))

private lemma continuousOn_apInt (φ : Cube n → ℝ) {a b : ℝ} (hb : b ≤ obsT)
    (hbT : b < D.T) (x y : Cube n) :
    ContinuousOn (fun t => D.apInt φ t x y) (Set.Icc a b) := by
  simp only [apInt]
  refine continuousOn_finset_sum _ fun ζ _ => ContinuousOn.mul
    (D.continuousOn_Hlik' hbT ζ x) ?_
  refine continuousOn_finset_sum _ fun i _ => ?_
  exact ((D.continuousOn_lam' hb i x ζ).mul
      ((D.continuousOn_aB' hb).pow 2)).mul
    ((D.continuousOn_dmext_mB' hb φ i x y ζ).pow 2)

private lemma apInt_nonneg (φ : Cube n → ℝ) {t : ℝ} (ht : t ≤ obsT)
    (x y : Cube n) : 0 ≤ D.apInt φ t x y := by
  refine Finset.sum_nonneg fun ζ _ => mul_nonneg
    (D.Hlik_nonneg (le_trans ht D.obsT_lt_T.le) ζ x) ?_
  exact Finset.sum_nonneg fun i _ => mul_nonneg
    (mul_nonneg (D.lam_pos ht i x ζ).le (sq_nonneg _)) (sq_nonneg _)

/-- The full-sector `a²`-energy of a flow. -/
private noncomputable def apE (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) : ℝ :=
  ∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1), D.apPair φ c k t

/-- **The carré-du-champ chain** [LGF eq (4.20)]: the accumulated `a²`-energy
is controlled by the endpoints and the `q²`-perturbation. -/
private lemma apE_le (B : Finset (Cube n)) {ℓ θ : ℝ}
    (hθ0' : 0 ≤ θ) (hθ1 : obsT - 1 ≤ θ) (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) :
    2 * D.apE (fun w => if w ∈ B then (1 : ℝ) else 0) c
      ≤ 1 + 2 * (Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a
          * D.dbar ℓ θ x₀ * (Real.sqrt (D.scoreEnergy c)
            * Real.sqrt (D.gamE (fun w => if w ∈ B then (1 : ℝ) else 0) c))) := by
  classical
  set φ : Cube n → ℝ := fun w => if w ∈ B then (1 : ℝ) else 0 with hφdef
  have hφ01 : ∀ w, φ w = 0 ∨ φ w = 1 := by
    intro w; by_cases hw : w ∈ B <;> simp [hφdef, hw]
  have hK : 0 < c.K := c.is.grid.pos
  have hmono : ∀ k, k < c.K → c.z k ≤ c.z (k + 1) := c.is.grid.mono
  have hcellT : ∀ k, k < c.K → c.z (k + 1) < D.T := fun k hk =>
    lt_of_le_of_lt (D.cell_le_obsT c hk) D.obsT_lt_T
  set Cst := Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a with hCst
  have hCst0 : 0 ≤ Cst := by
    have h3 : (0:ℝ) ≤ Lam D.a := le_trans zero_le_one (one_le_Lam D.ha0 D.ha1)
    have h1 : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ Real.sqrt (kappa D.a) := Real.sqrt_nonneg _
    positivity
  have hd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
  -- continuity of the integrands on each cell
  have hpQc : ∀ k, k < c.K → ContinuousOn (D.pertQPair φ c k)
      (Set.Icc (c.z k) (c.z (k + 1))) := by
    intro k hk
    refine continuousOn_finset_sum _ fun s _ => ?_
    by_cases hs : s.2.2
    · simp only [pertQPair, if_pos hs]
      exact ((c.is.glued.flow k hk).cont s).mul
        (D.continuousOn_pertQ φ ℓ θ x₀ (hcellT k hk) s.1 s.2.1)
    · simp only [pertQPair, if_neg hs]
      exact continuousOn_const
  have hapc : ∀ k, k < c.K → ContinuousOn (D.apPair φ c k)
      (Set.Icc (c.z k) (c.z (k + 1))) := by
    intro k hk
    refine continuousOn_finset_sum _ fun s _ => ?_
    exact ((c.is.glued.flow k hk).cont s).mul
      (D.continuousOn_apInt φ (D.cell_le_obsT c hk) (hcellT k hk) s.1 s.2.1)
  have hpQint : ∀ k, k < c.K →
      IntervalIntegrable (D.pertQPair φ c k) MeasureTheory.volume
        (c.z k) (c.z (k + 1)) := fun k hk =>
    ContinuousOn.intervalIntegrable
      (by rw [Set.uIcc_of_le (hmono k hk)]; exact hpQc k hk)
  have hapint : ∀ k, k < c.K →
      IntervalIntegrable (D.apPair φ c k) MeasureTheory.volume
        (c.z k) (c.z (k + 1)) := fun k hk =>
    ContinuousOn.intervalIntegrable
      (by rw [Set.uIcc_of_le (hmono k hk)]; exact hapc k hk)
  -- the chain
  have hnode_eq : ∀ k, k + 1 < c.K →
      D.qPair φ c (k + 1) (c.z (k + 1)) = D.qPair φ c k (c.z (k + 1)) := by
    intro k hk1
    have hnode := c.is.glued.node k hk1
    simp only [qPair, hnode]
    exact D.killTr_pair_pos ℓ (c.z (k + 1)) (c.π k (c.z (k + 1)))
      (fun v w => D.Qtest φ (c.z (k + 1)) v w)
  have hucont : ∀ k, k < c.K →
      ContinuousOn (D.qPair φ c k) (Set.Icc (c.z k) (c.z (k + 1))) :=
    fun k hk t ht => (D.qPair_hasDeriv φ c hk ht).continuousWithinAt
  have hchain := chain_eq (u := D.qPair φ c)
    (φ := fun k t => D.pertQPair φ c k t + 2 * D.apPair φ c k t) hK
    hmono hucont (fun k hk t ht => D.qPair_hasDeriv φ c hk ht)
    (fun k hk => (hpQint k hk).add ((hapint k hk).const_mul 2)) hnode_eq
  -- split the integral of the sum
  have hsplitint : ∀ k, k < c.K →
      (∫ t in c.z k..c.z (k + 1),
          (D.pertQPair φ c k t + 2 * D.apPair φ c k t))
        = (∫ t in c.z k..c.z (k + 1), D.pertQPair φ c k t)
          + 2 * ∫ t in c.z k..c.z (k + 1), D.apPair φ c k t := by
    intro k hk
    rw [intervalIntegral.integral_add (hpQint k hk) ((hapint k hk).const_mul 2),
      intervalIntegral.integral_const_mul]
  have hchain2 : D.qPair φ c (c.K - 1) (c.z c.K) - D.qPair φ c 0 (c.z 0)
      = (∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
          D.pertQPair φ c k t) + 2 * D.apE φ c := by
    rw [hchain]
    have hre : ∀ k ∈ Finset.range c.K,
        (∫ t in c.z k..c.z (k + 1),
          (fun k t => D.pertQPair φ c k t + 2 * D.apPair φ c k t) k t)
        = (∫ t in c.z k..c.z (k + 1), D.pertQPair φ c k t)
          + 2 * ∫ t in c.z k..c.z (k + 1), D.apPair φ c k t := fun k hk =>
      hsplitint k (Finset.mem_range.mp hk)
    rw [Finset.sum_congr rfl hre, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  -- endpoint bounds
  have hend : D.qPair φ c (c.K - 1) (c.z c.K) ≤ 1 := by
    have hk : c.K - 1 < c.K := Nat.sub_lt hK Nat.one_pos
    have hsucc : c.K - 1 + 1 = c.K := Nat.succ_pred_eq_of_pos hK
    have hz : c.z (c.K - 1) ≤ c.z c.K := by
      have h := hmono (c.K - 1) hk
      rwa [hsucc] at h
    have hmem : c.z c.K ∈ Set.Icc (c.z (c.K - 1)) (c.z (c.K - 1 + 1)) := by
      rw [hsucc]
      exact ⟨hz, le_rfl⟩
    have hobsT : c.z c.K ≤ obsT := le_of_eq c.is.grid.last
    calc D.qPair φ c (c.K - 1) (c.z c.K)
        ≤ ∑ s : JSt n, c.π (c.K - 1) (c.z c.K) s * 1 := by
          refine Finset.sum_le_sum fun s _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact (D.Qtest_mem01 hφ01 hobsT s.1 s.2.1).2
          · exact D.cflow_nonneg hθ c hk hmem s
      _ = 1 := by
          simp only [mul_one]
          exact D.cflow_mass hθ c hk hmem
  have hstart : 0 ≤ D.qPair φ c 0 (c.z 0) := by
    have h0K : 0 < c.K := hK
    have hmem : c.z 0 ∈ Set.Icc (c.z 0) (c.z 1) := ⟨le_rfl, hmono 0 h0K⟩
    refine Finset.sum_nonneg fun s _ => mul_nonneg
      (D.cflow_nonneg hθ c h0K hmem s) ?_
    have hz0 : c.z 0 ≤ obsT := by
      rw [c.is.grid.first]; exact hθ
    exact (D.Qtest_mem01 hφ01 hz0 s.1 s.2.1).1
  -- the perturbation total, bounded as in (B3)–(B5) with the factor 2
  have hpert : |∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
        D.pertQPair φ c k t|
      ≤ 2 * (Cst * D.dbar ℓ θ x₀ * (Real.sqrt (D.scoreEnergy c)
          * Real.sqrt (D.gamE φ c))) := by
    -- pointwise |pertQPair| ≤ 2·Cst·δ̄·√scInt·√gamInt (state-CS as in B1)
    have hptw : ∀ k, k < c.K → ∀ t ∈ Set.Icc (c.z k) (c.z (k + 1)),
        |D.pertQPair φ c k t|
          ≤ 2 * (Cst * D.dbar ℓ θ x₀ *
            (Real.sqrt (D.scInt c k t)
              * Real.sqrt (∑ s : JSt n, c.π k t s *
                  D.Gam φ t s.1 s.2.1))) := by
      intro k hk t ht
      have htB : t ≤ obsT := le_trans ht.2 (D.cell_le_obsT c hk)
      have htθ : θ ≤ t := by
        have h0 := D.grid_le'' c k 0 (Nat.zero_le k) hk.le
        rw [c.is.grid.first] at h0
        exact le_trans h0 ht.1
      have hπ0 : ∀ s : JSt n, 0 ≤ c.π k t s := fun s =>
        D.cflow_nonneg hθ c hk ht s
      set p : JSt n → ℝ := fun s => if s.2.2 then c.π k t s else 0 with hpdef
      have hp0 : ∀ s : JSt n, 0 ≤ p s := by
        intro s
        by_cases hs : s.2.2 <;> simp [hpdef, hs, hπ0 s]
      have hstep12 : |D.pertQPair φ c k t|
          ≤ ∑ s : JSt n, p s * (2 * (Cst * D.dbar ℓ θ x₀ *
              (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
                * Real.sqrt (D.Gam φ t s.1 s.2.1)))) := by
        have h1 : |D.pertQPair φ c k t|
            ≤ ∑ s : JSt n, p s * |D.pertQ φ ℓ θ x₀ t s.1 s.2.1| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          refine Finset.sum_le_sum fun s _ => ?_
          by_cases hs : s.2.2
          · simp [pertQPair, hpdef, hs, abs_mul, abs_of_nonneg (hπ0 s)]
          · simp [pertQPair, hpdef, hs]
        refine le_trans h1 (Finset.sum_le_sum fun s _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hp0 s)
        have h := D.abs_pertQ_le (θ := θ) (ℓ := ℓ) (x₀ := x₀) htθ htB
          (le_trans htθ htB) hφ01 s.1 s.2.1
        calc |D.pertQ φ ℓ θ x₀ t s.1 s.2.1| ≤ _ := h
          _ = 2 * (Cst * D.dbar ℓ θ x₀ *
              (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
                * Real.sqrt (D.Gam φ t s.1 s.2.1))) := by rw [hCst]; ring
      have hstep3 : ∑ s : JSt n, p s * (2 * (Cst * D.dbar ℓ θ x₀ *
            (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
              * Real.sqrt (D.Gam φ t s.1 s.2.1))))
          = 2 * (Cst * D.dbar ℓ θ x₀) * ∑ s : JSt n, p s *
              (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
                * Real.sqrt (D.Gam φ t s.1 s.2.1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
      have hstep4 : ∑ s : JSt n, p s *
            (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
              * Real.sqrt (D.Gam φ t s.1 s.2.1))
          ≤ Real.sqrt (∑ s : JSt n, p s * ∑ i, D.Sc t i s.1 ^ 2)
            * Real.sqrt (∑ s : JSt n, p s * D.Gam φ t s.1 s.2.1) :=
        weighted_cs Finset.univ p _ _ (fun s _ => hp0 s)
          (fun s _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
          (fun s _ => D.Gam_nonneg htB φ s.1 s.2.1)
      have hfac1 : (∑ s : JSt n, p s * ∑ i, D.Sc t i s.1 ^ 2)
          = D.scInt c k t := by
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hs : s.2.2 <;> simp [hpdef, scInt, hs]
      have hfac2 : (∑ s : JSt n, p s * D.Gam φ t s.1 s.2.1)
          ≤ ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1 := by
        refine Finset.sum_le_sum fun s _ => ?_
        by_cases hs : s.2.2
        · simp [hpdef, hs]
        · simp only [hpdef, if_neg hs, zero_mul]
          exact mul_nonneg (hπ0 s) (D.Gam_nonneg htB φ s.1 s.2.1)
      calc |D.pertQPair φ c k t|
          ≤ 2 * (Cst * D.dbar ℓ θ x₀) * ∑ s : JSt n, p s *
              (Real.sqrt (∑ i, D.Sc t i s.1 ^ 2)
                * Real.sqrt (D.Gam φ t s.1 s.2.1)) := by
            rw [← hstep3]; exact hstep12
        _ ≤ 2 * (Cst * D.dbar ℓ θ x₀) *
            (Real.sqrt (D.scInt c k t)
              * Real.sqrt (∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := by
            refine mul_le_mul_of_nonneg_left ?_
              (by positivity)
            refine le_trans hstep4 ?_
            rw [hfac1]
            exact mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt hfac2) (Real.sqrt_nonneg _)
        _ = 2 * (Cst * D.dbar ℓ θ x₀ *
            (Real.sqrt (D.scInt c k t)
              * Real.sqrt (∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1))) := by
            ring
    -- integrate cells, Cauchy–Schwarz, collect (as in B3–B5)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hcell : ∀ k, k < c.K →
        |∫ t in c.z k..c.z (k + 1), D.pertQPair φ c k t|
          ≤ 2 * (Cst * D.dbar ℓ θ x₀) *
            (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)
              * Real.sqrt (∫ t in c.z k..c.z (k + 1),
                  ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := by
      intro k hk
      have hzk := hmono k hk
      have habs : IntervalIntegrable (fun t => |D.pertQPair φ c k t|)
          MeasureTheory.volume (c.z k) (c.z (k + 1)) :=
        ContinuousOn.intervalIntegrable
          (by rw [Set.uIcc_of_le hzk]; exact (hpQc k hk).abs)
      have hrhs : IntervalIntegrable (fun t => 2 * (Cst * D.dbar ℓ θ x₀) *
          (Real.sqrt (D.scInt c k t) * Real.sqrt (∑ s : JSt n, c.π k t s *
            D.Gam φ t s.1 s.2.1)))
          MeasureTheory.volume (c.z k) (c.z (k + 1)) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hzk]
        exact continuousOn_const.mul
          (((D.continuousOn_scInt c hk).sqrt).mul
            ((D.continuousOn_gamInt φ c hk).sqrt))
      calc |∫ t in c.z k..c.z (k + 1), D.pertQPair φ c k t|
          ≤ ∫ t in c.z k..c.z (k + 1), |D.pertQPair φ c k t| :=
            intervalIntegral.abs_integral_le_integral_abs hzk
        _ ≤ ∫ t in c.z k..c.z (k + 1), 2 * (Cst * D.dbar ℓ θ x₀) *
              (Real.sqrt (D.scInt c k t) * Real.sqrt (∑ s : JSt n, c.π k t s *
                D.Gam φ t s.1 s.2.1)) := by
            refine intervalIntegral.integral_mono_on hzk habs hrhs fun t ht => ?_
            have h := hptw k hk t ht
            calc |D.pertQPair φ c k t| ≤ _ := h
              _ = 2 * (Cst * D.dbar ℓ θ x₀) *
                  (Real.sqrt (D.scInt c k t)
                    * Real.sqrt (∑ s : JSt n, c.π k t s *
                        D.Gam φ t s.1 s.2.1)) := by ring
        _ = 2 * (Cst * D.dbar ℓ θ x₀) * ∫ t in c.z k..c.z (k + 1),
              Real.sqrt (D.scInt c k t) * Real.sqrt (∑ s : JSt n, c.π k t s *
                D.Gam φ t s.1 s.2.1) := by
            rw [← intervalIntegral.integral_const_mul]
        _ ≤ 2 * (Cst * D.dbar ℓ θ x₀) *
            (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)
              * Real.sqrt (∫ t in c.z k..c.z (k + 1),
                  ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact intervalIntegral_sqrt_mul_le hzk (D.continuousOn_scInt c hk)
              (D.continuousOn_gamInt φ c hk)
              (fun t ht => D.scInt_nonneg hθ c hk ht)
              (fun t ht => D.gamInt_nonneg φ hθ c hk ht)
    calc ∑ k ∈ Finset.range c.K, |∫ t in c.z k..c.z (k + 1),
          D.pertQPair φ c k t|
        ≤ ∑ k ∈ Finset.range c.K, 2 * (Cst * D.dbar ℓ θ x₀) *
            (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)
              * Real.sqrt (∫ t in c.z k..c.z (k + 1),
                  ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) :=
          Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.mp hk)
      _ = 2 * (Cst * D.dbar ℓ θ x₀) * ∑ k ∈ Finset.range c.K,
            (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)
              * Real.sqrt (∫ t in c.z k..c.z (k + 1),
                  ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (Cst * D.dbar ℓ θ x₀) *
          (Real.sqrt (D.scoreEnergy c) * Real.sqrt (D.gamE φ c)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h := sum_le_sqrt_mul_sqrt (Finset.range c.K)
            (fun k => Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t))
            (fun k => Real.sqrt (∫ t in c.z k..c.z (k + 1),
              ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1))
            (fun k _ => Real.sqrt_nonneg _) (fun k _ => Real.sqrt_nonneg _)
          have e1 : ∀ k ∈ Finset.range c.K,
              (Real.sqrt (∫ t in c.z k..c.z (k + 1), D.scInt c k t)) ^ 2
                = ∫ t in c.z k..c.z (k + 1), D.scInt c k t := fun k hk =>
            Real.sq_sqrt (intervalIntegral.integral_nonneg
              (hmono k (Finset.mem_range.mp hk))
              (fun t ht => D.scInt_nonneg hθ c (Finset.mem_range.mp hk) ht))
          have e2 : ∀ k ∈ Finset.range c.K,
              (Real.sqrt (∫ t in c.z k..c.z (k + 1),
                  ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1)) ^ 2
                = ∫ t in c.z k..c.z (k + 1),
                    ∑ s : JSt n, c.π k t s * D.Gam φ t s.1 s.2.1 := fun k hk =>
            Real.sq_sqrt (intervalIntegral.integral_nonneg
              (hmono k (Finset.mem_range.mp hk))
              (fun t ht => D.gamInt_nonneg φ hθ c (Finset.mem_range.mp hk) ht))
          rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at h
          exact h
      _ = 2 * (Cst * D.dbar ℓ θ x₀ *
          (Real.sqrt (D.scoreEnergy c) * Real.sqrt (D.gamE φ c))) := by ring
  -- collect
  have h2apE : 2 * D.apE φ c
      = (D.qPair φ c (c.K - 1) (c.z c.K) - D.qPair φ c 0 (c.z 0))
        - ∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
            D.pertQPair φ c k t := by
    rw [hchain2]; ring
  have hperts := neg_abs_le (∑ k ∈ Finset.range c.K,
    ∫ t in c.z k..c.z (k + 1), D.pertQPair φ c k t)
  calc 2 * D.apE φ c
      = (D.qPair φ c (c.K - 1) (c.z c.K) - D.qPair φ c 0 (c.z 0))
        - ∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
            D.pertQPair φ c k t := h2apE
    _ ≤ 1 + |∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
            D.pertQPair φ c k t| := by
        have := hend; have := hstart
        linarith
    _ ≤ 1 + 2 * (Cst * D.dbar ℓ θ x₀ * (Real.sqrt (D.scoreEnergy c)
          * Real.sqrt (D.gamE φ c))) := by linarith [hpert]
    _ = 1 + 2 * (Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a
          * D.dbar ℓ θ x₀ * (Real.sqrt (D.scoreEnergy c)
            * Real.sqrt (D.gamE φ c))) := by rw [hCst]

/-- The `b_t²`-energy of a flow. -/
private noncomputable def bpE (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) : ℝ :=
  ∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
    ∑ s : JSt n, c.π k t s * D.bpInt φ t s.1 s.2.1

private lemma continuousOn_bpInt (φ : Cube n → ℝ) {a b : ℝ} (hb : b ≤ obsT)
    (hbT : b < D.T) (x y : Cube n) :
    ContinuousOn (fun t => D.bpInt φ t x y) (Set.Icc a b) := by
  simp only [bpInt]
  refine continuousOn_finset_sum _ fun ζ _ => ContinuousOn.mul
    (D.continuousOn_Hlik' hbT ζ x) ?_
  refine continuousOn_finset_sum _ fun i _ => ?_
  exact ((D.continuousOn_lam' hb i x ζ).mul
      ((D.continuousOn_bB' hb).pow 2)).mul
    ((D.continuousOn_dmext_mB' hb φ i x y ζ).pow 2)

/-- Splitting the `Γ`-energy into its `a²`- and `b²`-parts. -/
private lemma gamE_eq (φ : Cube n → ℝ) {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) : D.gamE φ c = D.apE φ c + D.bpE φ c := by
  simp only [gamE, apE, bpE, apPair, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < c.K := Finset.mem_range.mp hk
  have hzk : c.z k ≤ c.z (k + 1) := c.is.grid.mono k hk'
  have hb : c.z (k + 1) ≤ obsT := D.cell_le_obsT c hk'
  have hbT : c.z (k + 1) < D.T := lt_of_le_of_lt hb D.obsT_lt_T
  have hapi : IntervalIntegrable (fun t => ∑ s : JSt n, c.π k t s *
      D.apInt φ t s.1 s.2.1) MeasureTheory.volume (c.z k) (c.z (k + 1)) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hzk]
    exact continuousOn_finset_sum _ fun s _ =>
      ((c.is.glued.flow k hk').cont s).mul
        (D.continuousOn_apInt φ hb hbT s.1 s.2.1)
  have hbpi : IntervalIntegrable (fun t => ∑ s : JSt n, c.π k t s *
      D.bpInt φ t s.1 s.2.1) MeasureTheory.volume (c.z k) (c.z (k + 1)) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hzk]
    exact continuousOn_finset_sum _ fun s _ =>
      ((c.is.glued.flow k hk').cont s).mul
        (D.continuousOn_bpInt φ hb hbT s.1 s.2.1)
  rw [← intervalIntegral.integral_add hapi hbpi]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun sJ _ => ?_
  rw [← mul_add, ← D.Gam_eq_ap_add_bp φ t sJ.1 sJ.2.1]

/-- The `b²`-energy is at most `κ/4` [LGF eq (4.19)]. -/
private lemma bpE_le (B : Finset (Cube n)) {ℓ θ : ℝ}
    (hθ1 : obsT - 1 ≤ θ) (hθ : θ ≤ obsT) {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) :
    D.bpE (fun w => if w ∈ B then (1 : ℝ) else 0) c ≤ kappa D.a / 4 := by
  classical
  set φ : Cube n → ℝ := fun w => if w ∈ B then (1 : ℝ) else 0 with hφdef
  have hφ01 : ∀ w, φ w = 0 ∨ φ w = 1 := by
    intro w; by_cases hw : w ∈ B <;> simp [hφdef, hw]
  have hk4 : (0 : ℝ) ≤ kappa D.a / 4 := by
    have := one_lt_kappa D.ha0 D.ha1; linarith
  have hmono : ∀ k, k < c.K → c.z k ≤ c.z (k + 1) := c.is.grid.mono
  have hcell : ∀ k, k < c.K →
      (∫ t in c.z k..c.z (k + 1), ∑ s : JSt n, c.π k t s *
          D.bpInt φ t s.1 s.2.1)
        ≤ kappa D.a / 4 * (c.z (k + 1) - c.z k) := by
    intro k hk
    have hzk := hmono k hk
    have hb : c.z (k + 1) ≤ obsT := D.cell_le_obsT c hk
    have hbT : c.z (k + 1) < D.T := lt_of_le_of_lt hb D.obsT_lt_T
    have hint : IntervalIntegrable (fun t => ∑ s : JSt n, c.π k t s *
        D.bpInt φ t s.1 s.2.1) MeasureTheory.volume (c.z k) (c.z (k + 1)) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hzk]
      exact continuousOn_finset_sum _ fun s _ =>
        ((c.is.glued.flow k hk).cont s).mul
          (D.continuousOn_bpInt φ hb hbT s.1 s.2.1)
    have hptw : ∀ t ∈ Set.Icc (c.z k) (c.z (k + 1)),
        (∑ s : JSt n, c.π k t s * D.bpInt φ t s.1 s.2.1) ≤ kappa D.a / 4 := by
      intro t ht
      have htB : t ≤ obsT := le_trans ht.2 hb
      have htθ : θ ≤ t := by
        have h0 := D.grid_le'' c k 0 (Nat.zero_le k) hk.le
        rw [c.is.grid.first] at h0
        exact le_trans h0 ht.1
      have hbp : ∀ s : JSt n, D.bpInt φ t s.1 s.2.1 ≤ kappa D.a / 4 := by
        intro s
        have h := D.bpart_Gam_le (ℓ := ℓ) (θ := θ) htθ htB hφ01
          (x := s.1) (y := s.2.1) (le_trans htB D.obsT_lt_T.le)
        simpa only [bpInt] using h
      calc ∑ s : JSt n, c.π k t s * D.bpInt φ t s.1 s.2.1
          ≤ ∑ s : JSt n, c.π k t s * (kappa D.a / 4) := by
            refine Finset.sum_le_sum fun s _ => ?_
            exact mul_le_mul_of_nonneg_left (hbp s)
              (D.cflow_nonneg hθ c hk ht s)
        _ = kappa D.a / 4 := by
            rw [← Finset.sum_mul, D.cflow_mass hθ c hk ht, one_mul]
    calc (∫ t in c.z k..c.z (k + 1), ∑ s : JSt n, c.π k t s *
          D.bpInt φ t s.1 s.2.1)
        ≤ ∫ _t in c.z k..c.z (k + 1), kappa D.a / 4 :=
          intervalIntegral.integral_mono_on hzk hint
            intervalIntegrable_const hptw
      _ = kappa D.a / 4 * (c.z (k + 1) - c.z k) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  calc D.bpE φ c
      ≤ ∑ k ∈ Finset.range c.K, kappa D.a / 4 * (c.z (k + 1) - c.z k) :=
        Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.mp hk)
    _ = kappa D.a / 4 * (c.z c.K - c.z 0) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => c.z k)]
    _ ≤ kappa D.a / 4 := by
        have h1 : c.z c.K = obsT := c.is.grid.last
        have h2 : c.z 0 = θ := c.is.grid.first
        rw [h1, h2]
        nlinarith [hk4]

/-- Per-flow closure: `gamE ≤ κ + Cst·δ̄·√scoreE·√gamE` [LGF eq (4.21)]. -/
private lemma gamE_le (B : Finset (Cube n)) {ℓ θ : ℝ}
    (hθ0' : 0 ≤ θ) (hθ1 : obsT - 1 ≤ θ) (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) :
    D.gamE (fun w => if w ∈ B then (1 : ℝ) else 0) c
      ≤ kappa D.a + Real.sqrt 8 * Real.sqrt (kappa D.a) * Lam D.a
          * D.dbar ℓ θ x₀ * (Real.sqrt (D.scoreEnergy c)
            * Real.sqrt (D.gamE (fun w => if w ∈ B then (1 : ℝ) else 0) c)) := by
  have hap := D.apE_le B hθ0' hθ1 hθ c
  have hbp := D.bpE_le B hθ1 hθ c
  have hsplit := D.gamE_eq (fun w => if w ∈ B then (1 : ℝ) else 0) c
  have hκ := one_lt_kappa D.ha0 D.ha1
  -- `1/2 + κ/4 ≤ κ` for `κ > 1`
  nlinarith [hap, hbp, hsplit]

/-- **Localized total variation bound** [LGF Lemma 3.3]: there is a universal
`C` such that for all data, `θ ∈ [T_o-1, T_o]`, `ℓ > 0`, flow families, and
`A ⊆ ℰ_θ`,
`D_A ≤ C(κ_a Λ_a √(𝒮_A·ℙ(A)) + κ_a Λ_a² 𝒮_A)`. -/
theorem DA_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (D : Dat n) (ℓ θ : ℝ), 0 < ℓ →
      obsT - 1 ≤ θ → θ ≤ obsT → ∀ (Φ : D.CFlowFamily ℓ θ)
      (A : Finset (Cube n)), A ⊆ D.activeF ℓ θ →
      D.DA Φ A ≤ C * (kappa D.a * Lam D.a
          * Real.sqrt (D.SA Φ A * D.probA θ A)
        + kappa D.a * Lam D.a ^ 2 * D.SA Φ A) := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro n D ℓ θ hℓ hθ1 hθ Φ A hA
  have hθ0' : (0 : ℝ) ≤ θ := by
    have : (1 : ℝ) ≤ obsT := by norm_num [obsT]
    linarith
  set κ := kappa D.a with hκdef
  set Λ := Lam D.a with hΛdef
  have hκ1 : 1 < κ := one_lt_kappa D.ha0 D.ha1
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hΛ1 : (1 : ℝ) ≤ Λ := one_le_Lam D.ha0 D.ha1
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  set Cst := Real.sqrt 8 * Real.sqrt κ * Λ with hCst
  have hCst0 : 0 ≤ Cst := by positivity
  have hCst_sq : Cst ^ 2 = 8 * κ * Λ ^ 2 := by
    have h8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    have hκs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ0.le
    rw [hCst, mul_pow, mul_pow, h8, hκs]
  -- the optimal test set
  obtain ⟨B, hB⟩ := D.exists_DA_eq hθ Φ A
  set φ : Cube n → ℝ := fun w => if w ∈ B then (1 : ℝ) else 0 with hφdef
  set YA := ∑ x₀ ∈ A, D.startW θ x₀ * D.gamE φ (Φ x₀) with hYAdef
  have hSA0 : 0 ≤ D.SA Φ A := D.SA_nonneg hθ Φ A
  have hprobA0 : 0 ≤ D.probA θ A :=
    Finset.sum_nonneg fun x₀ _ => D.startW_nonneg'' hθ x₀
  have hYA0 : 0 ≤ YA := Finset.sum_nonneg fun x₀ _ =>
    mul_nonneg (D.startW_nonneg'' hθ x₀) (D.gamE_nonneg φ hθ (Φ x₀))
  -- step 1: the discrepancy bound through `√SA·√YA`
  have hD1 : D.DA Φ A ≤ Cst * (Real.sqrt (D.SA Φ A) * Real.sqrt YA) := by
    rw [hB]
    exact D.abs_sum_Dtest_le B hθ0' hθ1 hθ Φ A
  -- step 2: `YA ≤ 2κ·probA + Cst²·SA`
  have hYA_le : YA ≤ 2 * κ * D.probA θ A + Cst ^ 2 * D.SA Φ A := by
    have hstep : YA ≤ κ * D.probA θ A + Cst * (Real.sqrt (D.SA Φ A)
        * Real.sqrt YA) := by
      have h1 : YA ≤ ∑ x₀ ∈ A, D.startW θ x₀ *
          (κ + Cst * D.dbar ℓ θ x₀ * (Real.sqrt (D.scoreEnergy (Φ x₀))
            * Real.sqrt (D.gamE φ (Φ x₀)))) := by
        refine Finset.sum_le_sum fun x₀ hx₀ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (D.startW_nonneg'' hθ x₀)
        have h := D.gamE_le B hθ0' hθ1 hθ (Φ x₀)
        calc D.gamE φ (Φ x₀) ≤ _ := h
          _ = κ + Cst * D.dbar ℓ θ x₀ * (Real.sqrt (D.scoreEnergy (Φ x₀))
              * Real.sqrt (D.gamE φ (Φ x₀))) := by rw [hCst, hκdef, hΛdef]
      have h2 : ∑ x₀ ∈ A, D.startW θ x₀ *
          (κ + Cst * D.dbar ℓ θ x₀ * (Real.sqrt (D.scoreEnergy (Φ x₀))
            * Real.sqrt (D.gamE φ (Φ x₀))))
          = κ * D.probA θ A + Cst * ∑ x₀ ∈ A, D.startW θ x₀ *
              (Real.sqrt (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))
                * Real.sqrt (D.gamE φ (Φ x₀))) := by
        simp only [probA]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x₀ _ => ?_
        have hd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
        have hsq : Real.sqrt (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))
            = D.dbar ℓ θ x₀ * Real.sqrt (D.scoreEnergy (Φ x₀)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hd0]
        rw [hsq]
        ring
      have h3 : ∑ x₀ ∈ A, D.startW θ x₀ *
          (Real.sqrt (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))
            * Real.sqrt (D.gamE φ (Φ x₀)))
          ≤ Real.sqrt (D.SA Φ A) * Real.sqrt YA := by
        have hcs := weighted_cs A (fun x₀ => D.startW θ x₀)
          (fun x₀ => D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))
          (fun x₀ => D.gamE φ (Φ x₀))
          (fun x₀ _ => D.startW_nonneg'' hθ x₀)
          (fun x₀ _ => mul_nonneg (sq_nonneg _)
            (D.scoreEnergy_nonneg hθ (Φ x₀)))
          (fun x₀ _ => D.gamE_nonneg φ hθ (Φ x₀))
        have hSAeq : (∑ x₀ ∈ A, D.startW θ x₀ *
            (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))) = D.SA Φ A := by
          refine Finset.sum_congr rfl fun x₀ _ => ?_
          ring
        rw [hSAeq] at hcs
        exact hcs
      calc YA
          ≤ ∑ x₀ ∈ A, D.startW θ x₀ *
              (κ + Cst * D.dbar ℓ θ x₀ * (Real.sqrt (D.scoreEnergy (Φ x₀))
                * Real.sqrt (D.gamE φ (Φ x₀)))) := h1
        _ = κ * D.probA θ A + Cst * ∑ x₀ ∈ A, D.startW θ x₀ *
              (Real.sqrt (D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀))
                * Real.sqrt (D.gamE φ (Φ x₀))) := h2
        _ ≤ κ * D.probA θ A + Cst * (Real.sqrt (D.SA Φ A) * Real.sqrt YA) := by
          have := mul_le_mul_of_nonneg_left h3 hCst0
          linarith
    -- AM–GM absorption
    have hAM : Cst * (Real.sqrt (D.SA Φ A) * Real.sqrt YA)
        ≤ YA / 2 + Cst ^ 2 * D.SA Φ A / 2 := by
      have hsY : Real.sqrt YA ^ 2 = YA := Real.sq_sqrt hYA0
      have hsS : Real.sqrt (D.SA Φ A) ^ 2 = D.SA Φ A := Real.sq_sqrt hSA0
      have hprod : Cst ^ 2 * Real.sqrt (D.SA Φ A) ^ 2
          = Cst ^ 2 * D.SA Φ A := by rw [hsS]
      nlinarith [sq_nonneg (Real.sqrt YA - Cst * Real.sqrt (D.SA Φ A)),
        hsY, hprod]
    linarith
  -- step 3: assemble, `√(a+b) ≤ √a + √b`
  have hsqrt_add : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
      have h1 := Real.sq_sqrt ha
      have h2 := Real.sq_sqrt hb
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    calc Real.sqrt (a + b)
        ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
      _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)
  have hterm1 : Cst * Real.sqrt (2 * κ) = 4 * κ * Λ := by
    rw [hCst]
    have h2κ : Real.sqrt (2 * κ) = Real.sqrt 2 * Real.sqrt κ :=
      Real.sqrt_mul (by norm_num) _
    have h82 : Real.sqrt 8 * Real.sqrt 2 = 4 := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]
      rw [show (8 : ℝ) * 2 = 4 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have hκκ : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ0.le
    calc Real.sqrt 8 * Real.sqrt κ * Λ * (Real.sqrt 2 * Real.sqrt κ)
        = (Real.sqrt 8 * Real.sqrt 2) * (Real.sqrt κ * Real.sqrt κ) * Λ := by
          ring
      _ = 4 * κ * Λ := by rw [h82, hκκ]
  have hterm2 : Cst * Real.sqrt (Cst ^ 2) = 8 * κ * Λ ^ 2 := by
    rw [Real.sqrt_sq hCst0, ← sq, hCst_sq]
  calc D.DA Φ A
      ≤ Cst * (Real.sqrt (D.SA Φ A) * Real.sqrt YA) := hD1
    _ ≤ Cst * (Real.sqrt (D.SA Φ A) *
          Real.sqrt (2 * κ * D.probA θ A + Cst ^ 2 * D.SA Φ A)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCst0
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hYA_le)
          (Real.sqrt_nonneg _)
    _ ≤ Cst * (Real.sqrt (D.SA Φ A) *
          (Real.sqrt (2 * κ * D.probA θ A)
            + Real.sqrt (Cst ^ 2 * D.SA Φ A))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCst0
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        exact hsqrt_add _ _ (by positivity) (by positivity)
    _ = Cst * Real.sqrt (2 * κ) * Real.sqrt (D.SA Φ A * D.probA θ A)
        + Cst * Real.sqrt (Cst ^ 2) * D.SA Φ A := by
        have e1 : Real.sqrt (2 * κ * D.probA θ A)
            = Real.sqrt (2 * κ) * Real.sqrt (D.probA θ A) :=
          Real.sqrt_mul (by positivity) _
        have e2 : Real.sqrt (Cst ^ 2 * D.SA Φ A)
            = Real.sqrt (Cst ^ 2) * Real.sqrt (D.SA Φ A) :=
          Real.sqrt_mul (sq_nonneg _) _
        have e3 : Real.sqrt (D.SA Φ A) * Real.sqrt (D.probA θ A)
            = Real.sqrt (D.SA Φ A * D.probA θ A) :=
          (Real.sqrt_mul hSA0 _).symm
        have e4 : Real.sqrt (D.SA Φ A) * Real.sqrt (D.SA Φ A) = D.SA Φ A :=
          Real.mul_self_sqrt hSA0
        rw [e1, e2]
        calc Cst * (Real.sqrt (D.SA Φ A) *
              (Real.sqrt (2 * κ) * Real.sqrt (D.probA θ A)
                + Real.sqrt (Cst ^ 2) * Real.sqrt (D.SA Φ A)))
            = Cst * Real.sqrt (2 * κ) *
                (Real.sqrt (D.SA Φ A) * Real.sqrt (D.probA θ A))
              + Cst * Real.sqrt (Cst ^ 2) *
                (Real.sqrt (D.SA Φ A) * Real.sqrt (D.SA Φ A)) := by ring
          _ = _ := by rw [e3, e4]
    _ = 4 * κ * Λ * Real.sqrt (D.SA Φ A * D.probA θ A)
        + 8 * κ * Λ ^ 2 * D.SA Φ A := by rw [hterm1, hterm2]
    _ ≤ 8 * (κ * Λ * Real.sqrt (D.SA Φ A * D.probA θ A)
        + κ * Λ ^ 2 * D.SA Φ A) := by
        have hs0 : 0 ≤ Real.sqrt (D.SA Φ A * D.probA θ A) := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg hκ0.le hΛ0) hs0,
          mul_nonneg (mul_nonneg hκ0.le (sq_nonneg Λ)) hSA0]

end Dat

end Talagrand
