import TalagrandConvConjecture.ODE.LinearFlow
import TalagrandConvConjecture.Analysis.PiecewiseFTC

/-!
# Glued linear flows across a time grid

The stopped coupling of [LGF §4] is realized as a linear ODE on the sectored
state space, glued across the finitely many times at which the moving barrier
`{F_t ≥ ℓ+1}` changes (killing transfers happen at those nodes). This file
provides the generic gadget:

* `IsGluedFlow K z A Tr y₀ y`: `y k` solves the cell-`k` linear ODE on
  `[z k, z (k+1)]`, with node condition
  `y (k+1) (z (k+1)) = Tr (k+1) · (y k (z (k+1)))` and initial condition
  `y 0 (z 0) = Tr 0 · y₀`;
* existence, positivity, and mass transport;
* scalar chaining lemmas (`chain_le`, `chain_eq`) turning cell-wise
  derivative bounds plus node inequalities into endpoint estimates.
-/

namespace Talagrand

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Forward (master-equation) matrix of a nonnegative out-rate table
`q s s' = rate of jumping s → s'`: off-diagonal in-flux plus diagonal
out-flux. Columns sum to zero by construction. -/
def fwdOf (q : S → S → ℝ) : S → S → ℝ :=
  fun s s' => q s' s - (if s = s' then ∑ s'', q s s'' else 0)

lemma fwdOf_offdiag_nonneg {q : S → S → ℝ} (hq : ∀ s s', 0 ≤ q s s')
    {s s' : S} (h : s ≠ s') : 0 ≤ fwdOf q s s' := by
  simp [fwdOf, h, hq]

lemma fwdOf_col_sum (q : S → S → ℝ) (hq : ∀ s, q s s = 0) (s' : S) :
    ∑ s, fwdOf q s s' = 0 := by
  sorry

/-- A glued flow: on each cell `[z k, z (k+1)]`, `y k` solves the linear ODE
with generator `A k`; at each node the state is pushed through the transfer
matrix `Tr`. -/
structure IsGluedFlow (K : ℕ) (z : ℕ → ℝ) (A : ℕ → ℝ → S → S → ℝ)
    (Tr : ℕ → S → S → ℝ) (y₀ : S → ℝ) (y : ℕ → ℝ → S → ℝ) : Prop where
  mono : ∀ k, k < K → z k ≤ z (k + 1)
  flow : ∀ k, k < K → IsLinFlow (A k) (z k) (z (k + 1)) (y k)
  init : y 0 (z 0) = matVec (Tr 0) y₀
  node : ∀ k, k + 1 < K → y (k + 1) (z (k + 1)) = matVec (Tr (k + 1)) (y k (z (k + 1)))

/-- Existence of glued flows (cells solved by `exists_linFlow`, glued by
recursion). -/
theorem exists_gluedFlow (K : ℕ) (z : ℕ → ℝ) (A : ℕ → ℝ → S → S → ℝ)
    (Tr : ℕ → S → S → ℝ) (y₀ : S → ℝ)
    (hz : ∀ k, k < K → z k ≤ z (k + 1))
    (hA : ∀ k, k < K → ∀ s s',
      ContinuousOn (fun t => A k t s s') (Set.Icc (z k) (z (k + 1)))) :
    ∃ y, IsGluedFlow K z A Tr y₀ y := by
  sorry

/-- Positivity of a glued flow: Metzler cells + nonnegative transfers +
nonnegative initial data. -/
theorem gluedFlow_nonneg {K : ℕ} {z : ℕ → ℝ} {A : ℕ → ℝ → S → S → ℝ}
    {Tr : ℕ → S → S → ℝ} {y₀ : S → ℝ} {y : ℕ → ℝ → S → ℝ}
    (hy : IsGluedFlow K z A Tr y₀ y)
    (hA : ∀ k, k < K → ∀ s s',
      ContinuousOn (fun t => A k t s s') (Set.Icc (z k) (z (k + 1))))
    (hM : ∀ k, k < K → ∀ t ∈ Set.Icc (z k) (z (k + 1)), ∀ s s', s ≠ s' →
      0 ≤ A k t s s')
    (hTr : ∀ k s s', 0 ≤ Tr k s s') (h0 : ∀ s, 0 ≤ y₀ s) :
    ∀ k, k < K → ∀ t ∈ Set.Icc (z k) (z (k + 1)), ∀ s, 0 ≤ y k t s := by
  sorry

/-- Mass conservation for a glued flow whose cells conserve mass
(column sums `0`) and whose transfers are stochastic on the support
(`∑_s Tr k s s' = 1`). -/
theorem gluedFlow_mass {K : ℕ} {z : ℕ → ℝ} {A : ℕ → ℝ → S → S → ℝ}
    {Tr : ℕ → S → S → ℝ} {y₀ : S → ℝ} {y : ℕ → ℝ → S → ℝ}
    (hy : IsGluedFlow K z A Tr y₀ y)
    (hcol : ∀ k, k < K → ∀ t ∈ Set.Icc (z k) (z (k + 1)), ∀ s',
      ∑ s, A k t s s' = 0)
    (hTr : ∀ k s', ∑ s, Tr k s s' = 1) :
    ∀ k, k < K → ∀ t ∈ Set.Icc (z k) (z (k + 1)),
      ∑ s, y k t s = ∑ s, y₀ s := by
  sorry

/-- **Scalar chaining, inequality form**: if `u k` is continuous on cell `k`
with `u_k' ≤ φ k` there (as a `HasDerivWithinAt` bound), the node values do
not increase (`u (k+1) (z (k+1)) ≤ u k (z (k+1))`), and `φ k` is interval
integrable, then
`u (K-1) (z K) ≤ u 0 (z 0) + ∑_{k<K} ∫_{z k}^{z (k+1)} φ k`. -/
theorem chain_le {K : ℕ} (hK : 0 < K) {z : ℕ → ℝ} {u φ : ℕ → ℝ → ℝ}
    (hz : ∀ k, k < K → z k ≤ z (k + 1))
    (hu : ∀ k, k < K → ContinuousOn (u k) (Set.Icc (z k) (z (k + 1))))
    (hd : ∀ k, k < K → ∀ t ∈ Set.Icc (z k) (z (k + 1)), ∃ v ≤ φ k t,
      HasDerivWithinAt (u k) v (Set.Icc (z k) (z (k + 1))) t)
    (hφ : ∀ k, k < K, IntervalIntegrable (φ k) MeasureTheory.volume (z k) (z (k + 1)))
    (hnode : ∀ k, k + 1 < K → u (k + 1) (z (k + 1)) ≤ u k (z (k + 1))) :
    u (K - 1) (z K) ≤ u 0 (z 0)
      + ∑ k ∈ Finset.range K, ∫ t in z k..z (k + 1), φ k t := by
  sorry

/-- **Scalar chaining, equality form**: continuous `u k` with exact
derivative `φ k` on cells and exact node matching gives
`u (K-1) (z K) = u 0 (z 0) + ∑_{k<K} ∫ φ k`. -/
theorem chain_eq {K : ℕ} (hK : 0 < K) {z : ℕ → ℝ} {u φ : ℕ → ℝ → ℝ}
    (hz : ∀ k, k < K → z k ≤ z (k + 1))
    (hu : ∀ k, k < K → ContinuousOn (u k) (Set.Icc (z k) (z (k + 1))))
    (hd : ∀ k, k < K → ∀ t ∈ Set.Icc (z k) (z (k + 1)),
      HasDerivWithinAt (u k) (φ k t) (Set.Icc (z k) (z (k + 1))) t)
    (hφ : ∀ k, k < K, IntervalIntegrable (φ k) MeasureTheory.volume (z k) (z (k + 1)))
    (hnode : ∀ k, k + 1 < K → u (k + 1) (z (k + 1)) = u k (z (k + 1))) :
    u (K - 1) (z K) = u 0 (z 0)
      + ∑ k ∈ Finset.range K, ∫ t in z k..z (k + 1), φ k t := by
  sorry

/-- Monotone-decrease chaining (no integral): `u_k' ≤ 0` on cells, node
values nonincreasing ⟹ `u (K-1) (z K) ≤ u 0 (z 0)`. -/
theorem chain_mono {K : ℕ} (hK : 0 < K) {z : ℕ → ℝ} {u : ℕ → ℝ → ℝ}
    (hz : ∀ k, k < K → z k ≤ z (k + 1))
    (hu : ∀ k, k < K → ContinuousOn (u k) (Set.Icc (z k) (z (k + 1))))
    (hd : ∀ k, k < K → ∀ t ∈ Set.Icc (z k) (z (k + 1)), ∃ v ≤ (0 : ℝ),
      HasDerivWithinAt (u k) v (Set.Icc (z k) (z (k + 1))) t)
    (hnode : ∀ k, k + 1 < K → u (k + 1) (z (k + 1)) ≤ u k (z (k + 1))) :
    u (K - 1) (z K) ≤ u 0 (z 0) := by
  sorry

end Talagrand
