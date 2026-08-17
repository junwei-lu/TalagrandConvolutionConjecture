import TalagrandConvConjecture.Flow.Coupling
import TalagrandConvConjecture.Profile

/-!
# The localized quantities of [LGF §3]

Given data `D`, level `ℓ`, start time `θ`, and a family `Φ` of coupling
flows (one per starting point), this file defines, for `A` a set of starting
points (all events of [LGF §3] are `V_θ`-measurable, i.e. sets of starting
points; `𝔼[1_A ·] = ∑_{x₀∈A} ν_{T-θ}(x₀)·𝔼_{x₀}[·]`):

* `startW D θ x₀ = ν_{T-θ}({x₀})` — the law of `V_θ`;
* `probA` = `ℙ(A)`;
* `scoreEnergy c` — `𝔼_{x₀}∫_θ^τ ∑_i S_i(t,V_t)² dt` for one flow `c`;
* `SA` — the stopped score energy `𝒮_A` [LGF eq (3.3)];
* `DtestF c B` — `𝔼_{x₀}[1_B(W_{T_o}) - 1_B(V_{T_o})]`;
* `DA` — the localized total variation `D_A` [LGF eq (3.3)], defined as the
  half-`L¹` distance (equal to the sup over test sets, see `abs_Dtest_le_DA`);
* `Aband`/`Bband` — the terminal band masses `A_θ(r)`, `B_θ(r)`
  [LGF Lemma 3.4];
* the active set `activeF = ℰ_θ` as a `Finset`.
-/

namespace Talagrand

namespace Dat

variable {n : ℕ} (D : Dat n)

open Classical

/-- Law of `V_θ`: `startW θ x₀ = ν_{T-θ}({x₀}) = f_{T-θ}(x₀)/2^n`. -/
noncomputable def startW (θ : ℝ) (x₀ : Cube n) : ℝ := D.revDensity θ x₀

/-- `ℙ(V_θ ∈ A)`. -/
noncomputable def probA (θ : ℝ) (A : Finset (Cube n)) : ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀

/-- The active event `ℰ_θ = {R_θ ≥ 2α}` as a `Finset` [LGF eq (3.2)]. -/
noncomputable def activeF (ℓ θ : ℝ) : Finset (Cube n) :=
  Finset.univ.filter fun x₀ => 2 * alphaC ≤ D.Rgap ℓ θ x₀

/-- Alive-sector score energy of one coupling flow:
`𝔼_{x₀}[∫_θ^τ ∑_i S_i(t,V_{t-})² dt]` [LGF eq (3.3), inner integral]. -/
noncomputable def scoreEnergy {ℓ θ : ℝ} {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) :
    ℝ :=
  ∑ k ∈ Finset.range c.K, ∫ t in c.z k..c.z (k + 1),
    ∑ s : JSt n, (if s.2.2 then c.π k t s * ∑ i, D.Sc t i s.1 ^ 2 else 0)

/-- The stopped score energy `𝒮_A = 𝔼[1_A δ̄² ∫_θ^τ ∑_i S_i² dt]`
[LGF eq (3.3)]. -/
noncomputable def SA {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) :
    ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀ * D.dbar ℓ θ x₀ ^ 2 * D.scoreEnergy (Φ x₀)

/-- Signed terminal test discrepancy for one flow:
`𝔼_{x₀}[1_B(W_{T_o})] - 𝔼_{x₀}[1_B(V_{T_o})]`. -/
noncomputable def DtestF {ℓ θ : ℝ} {x₀ : Cube n} (c : D.CFlow ℓ θ x₀)
    (B : Finset (Cube n)) : ℝ :=
  ∑ s : JSt n, c.term s *
    ((if s.2.1 ∈ B then (1 : ℝ) else 0) - (if s.1 ∈ B then (1 : ℝ) else 0))

/-- The localized total variation distance `D_A` [LGF eq (3.3)], as the
half-`L¹` distance between the `A`-localized terminal laws of `W` and `V`. -/
noncomputable def DA {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) :
    ℝ :=
  (∑ w : Cube n, |∑ x₀ ∈ A, D.startW θ x₀ *
    (∑ s : JSt n, (Φ x₀).term s *
      ((if s.2.1 = w then (1 : ℝ) else 0) - (if s.1 = w then (1 : ℝ) else 0)))|)
    / 2

/-- Every test set is dominated by `D_A`:
`|ℙ(A, W_{T_o} ∈ B) - ℙ(A, V_{T_o} ∈ B)| ≤ D_A` [LGF eq (3.3)]. -/
theorem abs_Dtest_le_DA {ℓ θ : ℝ} (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ)
    (A B : Finset (Cube n)) :
    |∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B| ≤ D.DA Φ A := by
  sorry

/-- `D_A` is attained by some test set (finite optimal test
`B* = {w : ν w < μ w}`). -/
theorem exists_DA_eq {ℓ θ : ℝ} (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) :
    ∃ B : Finset (Cube n),
      D.DA Φ A = |∑ x₀ ∈ A, D.startW θ x₀ * D.DtestF (Φ x₀) B| := by
  sorry

/-- Subadditivity of `D` over a disjoint decomposition of `A`
[LGF, proof of Prop 3.2, Step 1]. -/
theorem DA_biUnion_le {ℓ θ : ℝ} (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (E : ι → Finset (Cube n))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (E i) (E j)) :
    D.DA Φ (I.biUnion E) ≤ ∑ i ∈ I, D.DA Φ (E i) := by
  sorry

/-- Terminal `V`-band mass
`A_θ^{[A]}(r) = ℙ(V_θ ∈ A, F_{T_o}(V_{T_o}) ∈ (r, r+1])` [LGF Lemma 3.4]. -/
noncomputable def Aband {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (r : ℝ) : ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
    (if D.F obsT s.1 ∈ Set.Ioc r (r + 1) then (1 : ℝ) else 0)

/-- Terminal `W`-band mass
`B_θ^{[A]}(r) = ℙ(V_θ ∈ A, F_{T_o}(W_{T_o}) ∈ (r, r+1])` [LGF §4.3]. -/
noncomputable def Bband {ℓ θ : ℝ} (Φ : D.CFlowFamily ℓ θ)
    (A : Finset (Cube n)) (r : ℝ) : ℝ :=
  ∑ x₀ ∈ A, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
    (if D.F obsT s.2.1 ∈ Set.Ioc r (r + 1) then (1 : ℝ) else 0)

/-- Nonnegativity of band masses. -/
lemma Aband_nonneg {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) (r : ℝ) :
    0 ≤ D.Aband Φ A r := by
  sorry

/-- Band masses are dominated by full-space profile mass:
`A_θ^{[A]}(r) ≤ 𝔄_{t_a}((r,r+1])` [LGF eq (3.14)]. -/
theorem Aband_le_profile {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n)) (r : ℝ) :
    D.Aband Φ A r ≤ profile D.f D.tA (Set.Ioc r (r + 1)) := by
  sorry

/-- Splitting over the active partition:
`𝔄_{t_a}((ℓ,ℓ+1]) = A_θ^{[ℰ]}(ℓ) + A_θ^{[ℰᶜ]}(ℓ)` [LGF eq (3.14)]. -/
theorem profile_eq_Aband_add {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ) :
    profile D.f D.tA (Set.Ioc ℓ (ℓ + 1))
      = D.Aband Φ (D.activeF ℓ θ) ℓ + D.Aband Φ (D.activeF ℓ θ)ᶜ ℓ := by
  sorry

/-- The start-weight sums are exactly profile masses of the start-time layer:
`∑_{x₀ : F_θ(x₀) ∈ I} ν_{T-θ}(x₀) = 𝔄_{T-θ}(I)` [LGF, Step 1 of Prop 3.2]. -/
theorem sum_startW_eq_profile (θ : ℝ) (I : Set ℝ) :
    ∑ x₀ ∈ Finset.univ.filter (fun x₀ => D.F θ x₀ ∈ I), D.startW θ x₀
      = profile D.f (D.T - θ) I := by
  sorry

end Dat

end Talagrand
