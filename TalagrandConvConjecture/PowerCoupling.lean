import TalagrandConvConjecture.Reverse.Setup

/-!
# The power splitting and its pointwise estimates [LGF §4]

The power coupling of [LGF §4] splits each reverse edge ratio `Y` into two
geometric powers, governed by a frozen exponent `δ̄ ∈ [0,1)`:

* `powerRatio d Y = (1-Y^d)/(1-Y)` for `Y < 1`, `d` at `Y = 1`,
  `(Y-Y^{1-d})/(Y-1)` for `Y > 1` — this is `δ_i` of [LGF §4] with
  `d = δ̄`, `Y = Y_i(t,x)`;
* frozen data at start time `θ`: `Rgap = [ℓ - F_θ(x₀)]₊`, active event
  `ℰ_θ = {Rgap ≥ 2α}`, `δ̄ = α·1_{ℰ}/(Rgap+1)` with `α = 5`
  [LGF eq (3.2)].

Pointwise estimates:
* `0 ≤ powerRatio ≤ Λ_a·d` on `[κ⁻¹, κ]` [LGF Lemma 5.2];
* the conditioned power bound [LGF eq (4.11)];
* the AM–GM drift defect `Y^d ≤ (1-d) + dY` [LGF eq (4.13)];
* the score convexity `2(κ-1)(Y log Y - Y + 1) ≥ log κ·(1-Y)²` on
  `[κ⁻¹,κ]` [C eq (40); LGF §4.4];
* basic facts about `Λ_a = κ log κ/(κ-1)` and `K_a = κ^{3/2}√Λ_a`.
-/

namespace Talagrand

/-- The universal stopping-level constant `α = 5` of [LGF eq (3.2)]. -/
def alphaC : ℝ := 5

/-- `Λ_a = κ_a·log κ_a/(κ_a - 1)` [LGF §3]. -/
noncomputable def Lam (a : ℝ) : ℝ :=
  kappa a * Real.log (kappa a) / (kappa a - 1)

/-- The power-splitting coefficient `δ_i` of [LGF §4] as a function of the
frozen exponent `d = δ̄` and the edge ratio `Y = Y_i(t,x)`:
`powerRatio δ̄ Y = δ_i(t,x)`. -/
noncomputable def powerRatio (d Y : ℝ) : ℝ :=
  if Y < 1 then (1 - Y ^ d) / (1 - Y)
  else if Y = 1 then d
  else (Y - Y ^ (1 - d)) / (Y - 1)

section OneDim

variable {κ d Y : ℝ}

/-- `1 ≤ Λ_a ≤ κ_a` (from `(κ-1)/κ ≤ log κ ≤ κ-1`) [LGF, proof of
Prop 3.2]. -/
lemma one_le_Lam {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 1 ≤ Lam a := by
  sorry

lemma Lam_le_kappa {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Lam a ≤ kappa a := by
  sorry

/-- `K_a² = κ_a³·Λ_a` [LGF, Step 1 of Prop 3.2]. -/
lemma Ka_sq_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Ka a ^ 2 = kappa a ^ 3 * Lam a := by
  sorry

lemma powerRatio_nonneg (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hY : 0 < Y) :
    0 ≤ powerRatio d Y := by
  sorry

/-- **Size of the power perturbation** [LGF Lemma 5.2]: on `[κ⁻¹, κ]`,
`powerRatio d Y ≤ (κ·log κ/(κ-1))·d`. -/
theorem powerRatio_le (hκ : 1 < κ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hY1 : κ⁻¹ ≤ Y) (hY2 : Y ≤ κ) :
    powerRatio d Y ≤ κ * Real.log κ / (κ - 1) * d := by
  sorry

/-- The two splitting identities: for `Y < 1`,
`(1 - Y^d)/2 = powerRatio d Y·(1-Y)/2`; for `Y > 1`,
`(Y - Y^{1-d})/2 = -powerRatio d Y·(1-Y)/2` [LGF §4, interpretation of the
coupling rates; proof of Lemma 5.1]. -/
lemma one_sub_rpow_eq (hY0 : 0 < Y) (hY : Y < 1) :
    (1 - Y ^ d) / 2 = powerRatio d Y * ((1 - Y) / 2) := by
  sorry

lemma rpow_sub_eq (hY : 1 < Y) :
    (Y - Y ^ (1 - d)) / 2 = -(powerRatio d Y * ((1 - Y) / 2)) := by
  sorry

/-- **AM–GM drift defect** [LGF eq (4.13)]: for `Y > 0`, `d ∈ [0,1]`,
`Y^d ≤ (1-d) + d·Y`; hence the switched power drift is nonpositive. -/
theorem rpow_le_one_sub_add_mul (hY : 0 < Y) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    Y ^ d ≤ (1 - d) + d * Y := by
  sorry

/-- **Score convexity** [C eq (40)]: for `κ > 1` and `Y ∈ [κ⁻¹, κ]`,
`2(κ-1)(Y·log Y - Y + 1) ≥ log κ·(1-Y)²`; equivalently
`½(Y log Y - Y + 1) ≥ (log κ/(κ-1))·S²` with `S = (1-Y)/2`. -/
theorem score_convexity (hκ : 1 < κ) (hY1 : κ⁻¹ ≤ Y) (hY2 : Y ≤ κ) :
    Real.log κ * (1 - Y) ^ 2 ≤ 2 * (κ - 1) * (Y * Real.log Y - Y + 1) := by
  sorry

/-- The conditioned-coefficient bound, `S ≤ 0` branch [LGF §5.3]: for
`Y ≥ 1` in `[κ⁻¹,κ]` and `λ > 0`,
`λ·(1 - Y^{-d})/(Y-1) ≤ λ·d` — packaged as the statement actually used:
`(λ·powerRatio d Y/Y) ≤ λ·d` for `Y > 1`. -/
lemma lam_mul_powerRatio_div_le (hY : 1 < Y) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    lam * powerRatio d Y / Y ≤ lam * d := by
  sorry

end OneDim

/-! ## Frozen data at the perturbation start [LGF eq (3.2)] -/

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- Remaining gap `R_θ = [ℓ - F_θ(x₀)]₊` at start time `θ`, starting point
`x₀` [LGF eq (3.2)]. -/
noncomputable def Rgap (ℓ θ : ℝ) (x₀ : Cube n) : ℝ := max (ℓ - D.F θ x₀) 0

/-- The active (excess-gap) event `ℰ_θ = {R_θ ≥ 2α}` as a set of starting
points [LGF eq (3.2)]. -/
def activeSet (ℓ θ : ℝ) : Set (Cube n) := {x₀ | 2 * alphaC ≤ D.Rgap ℓ θ x₀}

open Classical in
/-- Frozen perturbation size `δ̄ = α·1_{ℰ_θ}/(R_θ+1)` [LGF eq (3.2)]. -/
noncomputable def dbar (ℓ θ : ℝ) (x₀ : Cube n) : ℝ :=
  if 2 * alphaC ≤ D.Rgap ℓ θ x₀ then alphaC / (D.Rgap ℓ θ x₀ + 1) else 0

lemma Rgap_nonneg (ℓ θ : ℝ) (x₀ : Cube n) : 0 ≤ D.Rgap ℓ θ x₀ :=
  le_max_right _ _

lemma dbar_nonneg (ℓ θ : ℝ) (x₀ : Cube n) : 0 ≤ D.dbar ℓ θ x₀ := by
  sorry

/-- `δ̄ ≤ α/(2α+1) < 1/2` on the active set, `0` off it. -/
lemma dbar_lt_half (ℓ θ : ℝ) (x₀ : Cube n) : D.dbar ℓ θ x₀ < 1 / 2 := by
  sorry

/-- On the active set, `δ̄·(R_θ+1) = α` [LGF, proof of Lemma 3.4]. -/
lemma dbar_mul_Rgap_add_one {ℓ θ : ℝ} {x₀ : Cube n}
    (h : x₀ ∈ D.activeSet ℓ θ) :
    D.dbar ℓ θ x₀ * (D.Rgap ℓ θ x₀ + 1) = alphaC := by
  sorry

/-- Off the active set `δ̄ = 0` (the coupling degenerates to `W = V`). -/
lemma dbar_eq_zero {ℓ θ : ℝ} {x₀ : Cube n} (h : x₀ ∉ D.activeSet ℓ θ) :
    D.dbar ℓ θ x₀ = 0 := by
  sorry

open Classical in
/-- **Conditioned power bound** [LGF eq (4.11)]: for `t ≤ T_o`, on the active
set, writing `d = δ̄`,
`(δ_i·(1_{S_i>0} + r_{t,i}^ζ·1_{S_i≤0}))² ≤ κ_a·Λ_a²·δ̄²·λ_{t,i}^ζ(x)`,
where `δ_i = powerRatio δ̄ Y` and `r_{t,i}^ζ = λ_{t,i}^ζ/Y_i`. -/
theorem conditioned_power_bound {ℓ θ t : ℝ} (ht : t ≤ obsT) {x₀ : Cube n}
    (i : Fin n) (x ζ : Cube n) :
    (powerRatio (D.dbar ℓ θ x₀) (D.Y t i x) *
        (if 0 < D.Sc t i x then 1 else D.lam t i x ζ / D.Y t i x)) ^ 2
      ≤ kappa D.a * Lam D.a ^ 2 * D.dbar ℓ θ x₀ ^ 2 * D.lam t i x ζ := by
  sorry

end Dat

end Talagrand
