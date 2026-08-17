import TalagrandConvConjecture.Lemmas.Quantities

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
  exact ((ContinuousOn.div_const (ContinuousOn.max
        (continuousOn_const.sub hr1) continuousOn_const) 2).mul
      ((D.continuousOn_Utest φ hb x (flipCoord i y)).sub
        (D.continuousOn_Utest φ hb x y))).sub
    ((ContinuousOn.div_const (ContinuousOn.max
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
    hF.intervalIntegrable (by rwa [Set.uIcc_of_le hab])
  have hGi : IntervalIntegrable G MeasureTheory.volume a b :=
    hG.intervalIntegrable (by rwa [Set.uIcc_of_le hab])
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
      have hlam_sq : lam ^ 2 = (IG + ε) / (IF + ε) :=
        Real.sq_sqrt (div_nonneg hIGε.le hIFε.le)
      have h1 : lam * (IF + ε) = Real.sqrt ((IF + ε) * (IG + ε)) := by
        rw [hlam, ← Real.sqrt_sq hIFε.le, ← Real.sqrt_mul (sq_nonneg _)]
        congr 1
        field_simp
        ring
      have h2 : (IG + ε) / lam = Real.sqrt ((IF + ε) * (IG + ε)) := by
        rw [eq_comm, div_eq_iff hlam0.ne', hlam,
          ← Real.sqrt_sq hIGε.le, ← Real.sqrt_mul_self hIFε.le]
        rw [← Real.sqrt_mul (mul_self_nonneg _), ← Real.sqrt_mul
          (mul_nonneg hIFε.le hIGε.le)]
        congr 1
        field_simp
        ring
      have hle1 : lam * IF ≤ lam * (IF + ε) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam0.le
      have hle2 : IG / lam ≤ (IG + ε) / lam := by
        have h := mul_le_mul_of_nonneg_right (show IG ≤ IG + ε by linarith)
          (le_of_lt (inv_pos.mpr hlam0))
        simpa [div_eq_mul_inv] using h
      calc (lam * IF + IG / lam) / 2
          ≤ (lam * (IF + ε) + (IG + ε) / lam) / 2 := by linarith
        _ = Real.sqrt ((IF + ε) * (IG + ε)) := by rw [h1, h2]; ring
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
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i ∈ s, p i * (Real.sqrt (u i) * Real.sqrt (v i))
      ≤ Real.sqrt (∑ i ∈ s, p i * u i) * Real.sqrt (∑ i ∈ s, p i * v i) := by
  by_cases hall : ∀ i ∈ s, 0 ≤ u i ∧ 0 ≤ v i
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
  · push_neg at hall
    obtain ⟨i₀, hi₀, hneg⟩ := hall
    exact absurd hneg (by
      push_neg
      intro hu
      by_contra hv
      push_neg at hv
      exact absurd hu (not_le.mpr (by linarith [hv])) |>.elim) |>.elim

/-! #### Continuity toolbox (all in `t`, on closed cells below `T_o`) -/

private lemma continuous_gamB : Continuous gam := by
  have : Continuous fun t : ℝ => -(obsT - t) :=
    (continuous_const.sub continuous_id).neg
  exact Real.continuous_exp.comp this

private lemma continuousOn_aB' {a b : ℝ} (hb : b ≤ obsT) :
    ContinuousOn D.aB (Set.Icc a b) := by
  refine ContinuousOn.div
    ((D.continuous_gamB.mul continuous_const).continuousOn)
    ((continuous_const.sub (continuous_const.mul
      (D.continuous_gamB.pow 2))).continuousOn) ?_
  intro t ht
  exact ne_of_gt (D.den_pos (le_trans ht.2 hb))

private lemma continuousOn_bB' {a b : ℝ} (hb : b ≤ obsT) :
    ContinuousOn D.bB (Set.Icc a b) := by
  refine ContinuousOn.div
    ((continuous_const.mul (continuous_const.sub
      (D.continuous_gamB.pow 2))).continuousOn)
    ((continuous_const.sub (continuous_const.mul
      (D.continuous_gamB.pow 2))).continuousOn) ?_
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
  refine Finset.sum_nonneg fun s _ => ?_
  by_cases hs : s.2.2
  · simp only [scInt, if_pos hs]
    exact mul_nonneg (D.cflow_nonneg hθ c hk ht s)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · simp only [scInt, if_neg hs]

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
      · simp only [if_pos hs, hpdef, abs_mul, abs_of_nonneg (hπ0 s)]
      · simp [hpdef, hs]
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
  sorry

end Dat

end Talagrand
