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
  simp only [fwdOf, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    sub_self]

/-- Total mass is preserved by a matrix whose columns sum to one. -/
lemma sum_matVec_of_col_sum_one {T : S → S → ℝ} (hT : ∀ s', ∑ s, T s s' = 1)
    (v : S → ℝ) : ∑ s, matVec T v s = ∑ s, v s := by
  simp only [matVec]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, hT]

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
  classical
  have hex : ∀ (k : ℕ) (v : S → ℝ), ∃ w : ℝ → S → ℝ,
      (k < K → IsLinFlow (A k) (z k) (z (k + 1)) w) ∧ w (z k) = v := by
    intro k v
    by_cases hk : k < K
    · obtain ⟨w, hw, hw0⟩ := exists_linFlow (A k) (hz k hk) (hA k hk) v
      exact ⟨w, fun _ => hw, hw0⟩
    · exact ⟨fun _ => v, fun h => absurd h hk, rfl⟩
  choose F hF1 hF2 using hex
  refine ⟨fun k => Nat.rec (motive := fun _ => ℝ → S → ℝ) (F 0 (matVec (Tr 0) y₀))
    (fun k prev => F (k + 1) (matVec (Tr (k + 1)) (prev (z (k + 1))))) k,
    hz, ?_, hF2 0 _, fun k _ => hF2 (k + 1) _⟩
  intro k hk
  cases k with
  | zero => exact hF1 0 _ hk
  | succ n => exact hF1 (n + 1) _ hk

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
  intro k
  induction k with
  | zero =>
    intro hk
    refine linFlow_nonneg (hy.mono 0 hk) (hA 0 hk) (hM 0 hk) (hy.flow 0 hk) fun s => ?_
    rw [hy.init]
    exact Finset.sum_nonneg fun s' _ => mul_nonneg (hTr 0 s s') (h0 s')
  | succ n ih =>
    intro hk
    have hnK : n < K := lt_trans (Nat.lt_succ_self n) hk
    refine linFlow_nonneg (hy.mono (n + 1) hk) (hA (n + 1) hk) (hM (n + 1) hk)
      (hy.flow (n + 1) hk) fun s => ?_
    rw [hy.node n hk]
    refine Finset.sum_nonneg fun s' _ => mul_nonneg (hTr (n + 1) s s') ?_
    exact ih hnK (z (n + 1)) (Set.right_mem_Icc.2 (hy.mono n hnK)) s'

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
  intro k
  induction k with
  | zero =>
    intro hk t ht
    rw [linFlow_mass_eq (hy.mono 0 hk) (hcol 0 hk) (hy.flow 0 hk) t ht, hy.init]
    exact sum_matVec_of_col_sum_one (hTr 0) y₀
  | succ n ih =>
    intro hk t ht
    have hnK : n < K := lt_trans (Nat.lt_succ_self n) hk
    rw [linFlow_mass_eq (hy.mono (n + 1) hk) (hcol (n + 1) hk) (hy.flow (n + 1) hk) t ht,
      hy.node n hk, sum_matVec_of_col_sum_one (hTr (n + 1))]
    exact ih hnK (z (n + 1)) (Set.right_mem_Icc.2 (hy.mono n hnK))

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
    (hφ : ∀ k, k < K → IntervalIntegrable (φ k) MeasureTheory.volume (z k) (z (k + 1)))
    (hnode : ∀ k, k + 1 < K → u (k + 1) (z (k + 1)) ≤ u k (z (k + 1))) :
    u (K - 1) (z K) ≤ u 0 (z 0)
      + ∑ k ∈ Finset.range K, ∫ t in z k..z (k + 1), φ k t := by
  have aux : ∀ m, m < K → u m (z (m + 1)) ≤ u 0 (z 0)
      + ∑ k ∈ Finset.range (m + 1), ∫ t in z k..z (k + 1), φ k t := by
    intro m
    induction m with
    | zero =>
      intro h0K
      have hcell := sub_le_integral_of_hasDerivWithinAt_le (hz 0 h0K) (hu 0 h0K)
        (hd 0 h0K) (hφ 0 h0K)
      rw [Finset.sum_range_succ, Finset.sum_range_zero]
      linarith
    | succ m ih =>
      intro hm
      have hmK : m < K := lt_trans (Nat.lt_succ_self m) hm
      have h1 := ih hmK
      have h2 := hnode m hm
      have h3 := sub_le_integral_of_hasDerivWithinAt_le (hz (m + 1) hm) (hu (m + 1) hm)
        (hd (m + 1) hm) (hφ (m + 1) hm)
      rw [Finset.sum_range_succ]
      linarith
  have hKm : K - 1 + 1 = K := Nat.succ_pred_eq_of_pos hK
  have := aux (K - 1) (Nat.sub_lt hK Nat.one_pos)
  rwa [hKm] at this

/-- **Scalar chaining, equality form**: continuous `u k` with exact
derivative `φ k` on cells and exact node matching gives
`u (K-1) (z K) = u 0 (z 0) + ∑_{k<K} ∫ φ k`. -/
theorem chain_eq {K : ℕ} (hK : 0 < K) {z : ℕ → ℝ} {u φ : ℕ → ℝ → ℝ}
    (hz : ∀ k, k < K → z k ≤ z (k + 1))
    (hu : ∀ k, k < K → ContinuousOn (u k) (Set.Icc (z k) (z (k + 1))))
    (hd : ∀ k, k < K → ∀ t ∈ Set.Icc (z k) (z (k + 1)),
      HasDerivWithinAt (u k) (φ k t) (Set.Icc (z k) (z (k + 1))) t)
    (hφ : ∀ k, k < K → IntervalIntegrable (φ k) MeasureTheory.volume (z k) (z (k + 1)))
    (hnode : ∀ k, k + 1 < K → u (k + 1) (z (k + 1)) = u k (z (k + 1))) :
    u (K - 1) (z K) = u 0 (z 0)
      + ∑ k ∈ Finset.range K, ∫ t in z k..z (k + 1), φ k t := by
  have cell : ∀ k, k < K → (∫ t in z k..z (k + 1), φ k t) = u k (z (k + 1)) - u k (z k) := by
    intro k hk
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (hz k hk) (hu k hk)
      (fun x hx => hasDerivWithinAt_Ioi_of_Icc hx (hd k hk x ⟨hx.1.le, hx.2.le⟩)) (hφ k hk)
  have aux : ∀ m, m < K → u m (z (m + 1)) = u 0 (z 0)
      + ∑ k ∈ Finset.range (m + 1), ∫ t in z k..z (k + 1), φ k t := by
    intro m
    induction m with
    | zero =>
      intro h0K
      have h := cell 0 h0K
      rw [Finset.sum_range_succ, Finset.sum_range_zero]
      linarith
    | succ m ih =>
      intro hm
      have hmK : m < K := lt_trans (Nat.lt_succ_self m) hm
      have h1 := ih hmK
      have h2 := hnode m hm
      have h3 := cell (m + 1) hm
      rw [Finset.sum_range_succ]
      linarith
  have hKm : K - 1 + 1 = K := Nat.succ_pred_eq_of_pos hK
  have := aux (K - 1) (Nat.sub_lt hK Nat.one_pos)
  rwa [hKm] at this

/-- Monotone-decrease chaining (no integral): `u_k' ≤ 0` on cells, node
values nonincreasing ⟹ `u (K-1) (z K) ≤ u 0 (z 0)`. -/
theorem chain_mono {K : ℕ} (hK : 0 < K) {z : ℕ → ℝ} {u : ℕ → ℝ → ℝ}
    (hz : ∀ k, k < K → z k ≤ z (k + 1))
    (hu : ∀ k, k < K → ContinuousOn (u k) (Set.Icc (z k) (z (k + 1))))
    (hd : ∀ k, k < K → ∀ t ∈ Set.Icc (z k) (z (k + 1)), ∃ v ≤ (0 : ℝ),
      HasDerivWithinAt (u k) v (Set.Icc (z k) (z (k + 1))) t)
    (hnode : ∀ k, k + 1 < K → u (k + 1) (z (k + 1)) ≤ u k (z (k + 1))) :
    u (K - 1) (z K) ≤ u 0 (z 0) := by
  have aux : ∀ m, m < K → u m (z (m + 1)) ≤ u 0 (z 0) := by
    intro m
    induction m with
    | zero =>
      intro h0K
      exact le_of_hasDerivWithinAt_nonpos (hz 0 h0K) (hu 0 h0K) (hd 0 h0K)
    | succ m ih =>
      intro hm
      have hmK : m < K := lt_trans (Nat.lt_succ_self m) hm
      have h1 := ih hmK
      have h2 := hnode m hm
      have h3 := le_of_hasDerivWithinAt_nonpos (hz (m + 1) hm) (hu (m + 1) hm) (hd (m + 1) hm)
      linarith
  have hKm : K - 1 + 1 = K := Nat.succ_pred_eq_of_pos hK
  have := aux (K - 1) (Nat.sub_lt hK Nat.one_pos)
  rwa [hKm] at this

end Talagrand
