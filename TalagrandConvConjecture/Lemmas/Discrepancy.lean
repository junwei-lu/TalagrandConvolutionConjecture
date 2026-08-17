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
    have hq := D.hasDerivAt_qB φ t ζ x y
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
  sorry

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
