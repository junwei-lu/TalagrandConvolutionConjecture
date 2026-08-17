import TalagrandConvConjecture.Lemmas.Quantities

/-!
# The switched power supermartingale: terminal weighted comparison
[LGF Proposition 4.1]

Weight functions (the power gap `Ξ_t` of [LGF eq (4.12)], with the dead
sector's frozen value `F_τ(V_τ)` replaced by its lower bound `ℓ+1` — the only
form used downstream, see the deviation note):

`NW t (x,y,alive) = exp(F_t(y) - (1-δ̄)F_t(x) - δ̄F_θ(x₀))`
`NW t (x,y,dead)  = exp(F_t(y) - F_t(x) + δ̄(ℓ+1 - F_θ(x₀)))`

**Deviation from [LGF Prop 4.1]**: the paper's supermartingale weight `M_t`
uses `F_τ(V_τ)` (a path functional) in the dead sector; since
`F_τ(V_τ) ≥ ℓ+1` always, `NW ≤ M` pathwise, and the `NW`-weighted terminal
comparison proved here is (very slightly) weaker — but it is exactly what the
proof of [LGF Lemma 3.4] consumes. The alive sector is unchanged.

The proof pairs the flow against `NW_t(s)·H_t(W-part of s)` where `H` is the
space-time harmonic extension of the terminal test `h ≥ 0` for the
unperturbed reverse dynamics in the `W`-slot; the cell drift is
`-½∑_i[(1-δ̄) + δ̄Y_i - Y_i^{δ̄}]·(NW·H) ≤ 0` by AM–GM [LGF eq (4.13)-(4.14)],
dead cells have zero drift, and node transfers decrease the pairing (weight
ratio `e^{δ̄(ℓ+1-F)} ≤ 1` on transferred states, `H ≥ 0`).
-/

namespace Talagrand

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- The terminal comparison weight `N` (see the module docstring; equals
`e^{Ξ_t}` of [LGF eq (4.12)] on the alive sector and lower-bounds it on the
dead sector). -/
noncomputable def NW (ℓ θ : ℝ) (x₀ : Cube n) (t : ℝ) (s : JSt n) : ℝ :=
  if s.2.2 then
    Real.exp (D.F t s.2.1 - (1 - D.dbar ℓ θ x₀) * D.F t s.1
      - D.dbar ℓ θ x₀ * D.F θ x₀)
  else
    Real.exp (D.F t s.2.1 - D.F t s.1 + D.dbar ℓ θ x₀ * (ℓ + 1 - D.F θ x₀))

/-- **Weighted terminal comparison** [LGF Prop 4.1, `N`-weighted form]:
for every nonnegative terminal test `h` and every starting point,
`𝔼_{x₀}[N_{T_o}·h(W_{T_o})] ≤ 𝔼_{x₀}[h(V_{T_o})]`. -/
theorem weighted_comparison {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) (h : Cube n → ℝ)
    (hh : ∀ w, 0 ≤ h w) :
    ∑ s, D.NW ℓ θ x₀ obsT s * c.term s * h s.2.1
      ≤ ∑ s, c.term s * h s.1 := by
  sorry

/-- The localized form over a set of starting points [LGF
eq (4.14)]: for `A ⊆ G`,
`∑_{x₀∈A} ν(x₀)·𝔼_{x₀}[N h(W)] ≤ ∑_{x₀∈A} ν(x₀)·𝔼_{x₀}[h(V)]`. -/
theorem weighted_comparison_localized {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n))
    (h : Cube n → ℝ) (hh : ∀ w, 0 ≤ h w) :
    ∑ x₀ ∈ A, D.startW θ x₀ *
        ∑ s, D.NW ℓ θ x₀ obsT s * (Φ x₀).term s * h s.2.1
      ≤ ∑ x₀ ∈ A, D.startW θ x₀ * ∑ s, (Φ x₀).term s * h s.1 := by
  sorry

/-- Pointwise lower bound for the terminal weight on the crossing event
[LGF, proof of Lemma 3.4]: for `x₀ ∈ ℰ_θ` and a terminal state `s` with
`F_{T_o}(W) ∈ (ℓ+j, ℓ+j+1]` and `F_{T_o}(V) ≤ ℓ+1` (alive sector) —
resp. any dead-sector state with those `F`-values —
`N_{T_o}(s) ≥ e^{α+j-1} = e^{j+4}`. -/
theorem NW_ge_on_crossing {ℓ θ : ℝ} {x₀ : Cube n}
    (hx₀ : x₀ ∈ D.activeF ℓ θ) {s : JSt n} {j : ℝ} (hj : 0 ≤ j)
    (hW : ℓ + j < D.F obsT s.2.1) (hV : D.F obsT s.1 ≤ ℓ + 1) :
    Real.exp (alphaC + j - 1) ≤ D.NW ℓ θ x₀ obsT s := by
  sorry

end Dat

end Talagrand
