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

/-- Terminal value: `U_{T_o}(x,y) = φ(y)`. -/
theorem Utest_obsT (φ : Cube n → ℝ) (x y : Cube n) :
    D.Utest φ obsT x y = φ y := by
  sorry

/-- Space-time harmonicity of `U` for the synchronized joint generator
[LGF §4.1]: `∂_t U_t(x,y) = -½∑_i Y_i(t,x)·Δ_i^{xy}U_t(x,y)`. -/
theorem hasDerivAt_Utest (φ : Cube n → ℝ) {t : ℝ} (ht : t < D.T)
    (x y : Cube n) :
    HasDerivAt (fun t => D.Utest φ t x y)
      (-(∑ i, D.Y t i x *
          (D.Utest φ t (flipCoord i x) (flipCoord i y) - D.Utest φ t x y) / 2))
      t := by
  sorry

/-- Diagonal transport: `g(t,x) := U_t(x,x)` is space-time harmonic for the
reverse generator (synchronized flips preserve the diagonal), with
`g(T_o,·) = φ`; hence by the `V`-marginal property,
`𝔼_{x₀}[φ(V_{T_o})] = U_θ(x₀,x₀)` [LGF eq (4.10) via Lemma 5.1]. -/
theorem term_V_eq_Utest_diag {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) (φ : Cube n → ℝ) :
    ∑ s, c.term s * φ s.1 = D.Utest φ θ x₀ x₀ := by
  sorry

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
  sorry

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
