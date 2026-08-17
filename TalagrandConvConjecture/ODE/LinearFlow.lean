import Mathlib

/-!
# Finite-dimensional linear ODE flows

Existence, uniqueness, positivity, and mass bounds for
`y'(t) = A(t)·y(t)` on a compact interval `[a,b]`, with `A : ℝ → S → S → ℝ`
continuous in `t` on a finite state space `S`.

This is the "master equation" backbone of the de-probabilized formalization
of [LGF]: the reverse heat process, the coupled process, and their killed and
weighted variants ([LGF §2.2, §4]) are all instances (cell-wise, between the
finitely many barrier-crossing times).

Conventions: `y t : S → ℝ` is a column of masses;
`(matVecA A t y) s = ∑ s', A t s s' * y s'`. Positivity requires the Metzler
condition (off-diagonal entries `≥ 0`), mass bounds require column-sum
conditions (`∑_s A t s s' = 0` for conservation, `≤ 0` for sub-conservation).
-/

namespace Talagrand

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Action of the time-dependent matrix. -/
def matVec (A : S → S → ℝ) (y : S → ℝ) : S → ℝ := fun s => ∑ s', A s s' * y s'

/-- `IsLinFlow A a b y` : `y` solves `y' = A(t) y` on `[a,b]`
(continuity on `[a,b]`, derivative within `[a,b]` at every point). -/
structure IsLinFlow (A : ℝ → S → S → ℝ) (a b : ℝ) (y : ℝ → S → ℝ) : Prop where
  cont : ∀ s, ContinuousOn (fun t => y t s) (Set.Icc a b)
  deriv : ∀ s, ∀ t ∈ Set.Icc a b,
    HasDerivWithinAt (fun t => y t s) (matVec (A t) (y t) s) (Set.Icc a b) t

/-- **Existence** of the linear flow with prescribed initial value. -/
theorem exists_linFlow (A : ℝ → S → S → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    (y₀ : S → ℝ) :
    ∃ y : ℝ → S → ℝ, IsLinFlow A a b y ∧ y a = y₀ := by
  sorry

/-- **Uniqueness**: two flows with the same initial value agree on `[a,b]`. -/
theorem linFlow_unique {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    {y z : ℝ → S → ℝ} (hy : IsLinFlow A a b y) (hz : IsLinFlow A a b z)
    (h0 : y a = z a) : ∀ t ∈ Set.Icc a b, y t = z t := by
  sorry

/-- **Positivity** (Metzler): if all off-diagonal entries of `A t` are `≥ 0`
on `[a,b]` and `y a ≥ 0`, then `y t ≥ 0` on `[a,b]`. -/
theorem linFlow_nonneg {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    (hMetzler : ∀ t ∈ Set.Icc a b, ∀ s s', s ≠ s' → 0 ≤ A t s s')
    {y : ℝ → S → ℝ} (hy : IsLinFlow A a b y) (h0 : ∀ s, 0 ≤ y a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ y t s := by
  sorry

/-- **Mass conservation**: if all column sums of `A t` vanish
(`∑_s A t s s' = 0`), the total mass `∑_s y t s` is constant. -/
theorem linFlow_mass_eq {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcol : ∀ t ∈ Set.Icc a b, ∀ s', ∑ s, A t s s' = 0)
    {y : ℝ → S → ℝ} (hy : IsLinFlow A a b y) :
    ∀ t ∈ Set.Icc a b, ∑ s, y t s = ∑ s, y a s := by
  sorry

/-- **Mass sub-conservation**: if column sums are `≤ 0` and `y ≥ 0` along the
flow, the total mass is nonincreasing. -/
theorem linFlow_mass_le {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcol : ∀ t ∈ Set.Icc a b, ∀ s', ∑ s, A t s s' ≤ 0)
    {y : ℝ → S → ℝ} (hy : IsLinFlow A a b y)
    (hpos : ∀ t ∈ Set.Icc a b, ∀ s, 0 ≤ y t s) :
    ∀ t ∈ Set.Icc a b, ∑ s, y t s ≤ ∑ s, y a s := by
  sorry

/-- Derivative of a pairing `t ↦ ∑_s y t s · g t s` along the flow:
`d/dt ⟨y_t, g_t⟩ = ⟨A(t)y_t, g_t⟩ + ⟨y_t, ∂_t g_t⟩`. The workhorse for all
martingale-type arguments ([LGF §4]: Duhamel, supermartingale, score
energy). -/
theorem hasDerivWithinAt_pairing {A : ℝ → S → S → ℝ} {a b : ℝ}
    {y : ℝ → S → ℝ} (hy : IsLinFlow A a b y) {g : ℝ → S → ℝ} {g' : S → ℝ}
    {t : ℝ} (ht : t ∈ Set.Icc a b)
    (hg : ∀ s, HasDerivWithinAt (fun t => g t s) (g' s) (Set.Icc a b) t) :
    HasDerivWithinAt (fun t => ∑ s, y t s * g t s)
      (∑ s, (matVec (A t) (y t) s * g t s + y t s * g' s)) (Set.Icc a b) t := by
  sorry

/-- **Comparison/domination**: if `z` solves the same Metzler ODE with an
extra nonnegative source against a nonnegative flow (`z' = A z + r`,
`r ≥ 0` pointwise), and `z a ≥ y a ≥ 0`, then `z ≥ y` on `[a,b]`.
(Used to compare weighted flows against tilted lower-bound flows.) -/
theorem linFlow_le_of_source {A : ℝ → S → S → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ s s', ContinuousOn (fun t => A t s s') (Set.Icc a b))
    (hMetzler : ∀ t ∈ Set.Icc a b, ∀ s s', s ≠ s' → 0 ≤ A t s s')
    {y z : ℝ → S → ℝ} (hy : IsLinFlow A a b y)
    (hzc : ∀ s, ContinuousOn (fun t => z t s) (Set.Icc a b))
    (hz : ∀ s, ∀ t ∈ Set.Icc a b, ∃ r ≥ 0,
      HasDerivWithinAt (fun t => z t s) (matVec (A t) (z t) s + r)
        (Set.Icc a b) t)
    (h0 : ∀ s, y a s ≤ z a s) (hy0 : ∀ s, 0 ≤ y a s) :
    ∀ t ∈ Set.Icc a b, ∀ s, y t s ≤ z t s := by
  sorry

end Talagrand
