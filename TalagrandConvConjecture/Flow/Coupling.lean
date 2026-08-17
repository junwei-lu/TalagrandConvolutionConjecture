import TalagrandConvConjecture.Flow.Glued
import TalagrandConvConjecture.PowerCoupling
import TalagrandConvConjecture.Bridge

/-!
# The stopped power coupling as a glued flow [LGF §3–4]

Fix data `D`, tail level `ℓ`, start time `θ ∈ [T_o - 1, T_o]`, and starting
point `x₀`. The coupled pair `(V_t, W_t)` with predictable stopping indicator
`1_{t ≤ τ}` ([LGF eq (4.1)], `τ` from [LGF eq (3.1)]) is a Markov process on
the sectored state space `JSt n = Cube n × Cube n × Bool` (sector `true` =
"alive", i.e. `t ≤ τ`). Its law solves a linear master equation whose
coefficients are continuous except at the finitely many crossing times of the
barrier `{x | F_t(x) ≥ ℓ+1}`; at those nodes, alive mass sitting on a
newly-barrier state is transferred to the dead sector (`τ` fires by
continuous crossing). Jumps of `V` into the barrier land directly in the dead
sector (`τ` fires by jump).

Alive-sector out-rates (frozen exponent `d = δ̄(x₀)`, `Y = Y_i(t,x)`;
[LGF §4, interpretation of the coupling]):
* `Y < 1`: synchronized flip `(σ_i x, σ_i y)` at rate `Y/2`; `W`-only flip
  `(x, σ_i y)` at rate `(1 - Y^d)/2`;
* `Y ≥ 1`: synchronized flip at rate `Y^{1-d}/2`; `V`-only flip `(σ_i x, y)`
  at rate `(Y - Y^{1-d})/2`.
Dead sector: synchronized flips at rate `Y/2`. `V`-moving jumps land in the
dead sector iff the new `V`-position is in the cell's barrier.

`IsCouplingFlow` packages a glued flow for these rates on an admissible grid;
existence and the basic transport properties are provided. All quantities of
[LGF §3] (`𝒮_A`, `D_A`, `A_θ(r)`, `B_θ(ℓ)`) are defined from a bundled
`CFlowFamily`.
-/

namespace Talagrand

variable {n : ℕ}

/-- Sectored joint state space: `(V-position, W-position, alive?)`. -/
abbrev JSt (n : ℕ) := Cube n × Cube n × Bool

open Classical in
/-- Initial vector: unit mass at `(x₀, x₀, alive)`. (The `Tr 0` step of the
glued flow then kills it if `x₀` is already in the barrier at `θ`, matching
`τ = θ` in [LGF eq (3.1)].) -/
noncomputable def initVec (x₀ : Cube n) : JSt n → ℝ := fun s =>
  if s = (x₀, x₀, true) then 1 else 0

namespace Dat

variable (D : Dat n)

/-- The moving barrier `{x | F_t(x) ≥ ℓ+1}` of the stopping time
[LGF eq (3.1)]. -/
def barrier (ℓ t : ℝ) : Set (Cube n) := {x | ℓ + 1 ≤ D.F t x}

/-- An admissible grid on `[θ, T_o]`: monotone nodes from `θ` to `T_o` such
that no barrier crossing `F_t(x) = ℓ+1` happens in any open cell. On such a
grid the barrier is constant on each open cell. -/
structure AdmissibleGrid (ℓ θ : ℝ) (K : ℕ) (z : ℕ → ℝ) : Prop where
  pos : 0 < K
  first : z 0 = θ
  last : z K = obsT
  mono : ∀ k, k < K → z k ≤ z (k + 1)
  nocross : ∀ k, k < K → ∀ t ∈ Set.Ioo (z k) (z (k + 1)), ∀ x : Cube n,
    D.F t x ≠ ℓ + 1

/-- Existence of an admissible grid: barrier crossings are roots of a nonzero
polynomial in `e^{-(T-t)}` (constant coefficient `1 ≠ e^{ℓ+1}`), hence
finitely many; sort them. -/
theorem exists_admissibleGrid (ℓ : ℝ) (hℓ : 0 < ℓ) {θ : ℝ} (hθ : θ ≤ obsT) :
    ∃ K z, D.AdmissibleGrid ℓ θ K z := by
  sorry

/-- Barrier membership is constant on open cells of an admissible grid
(intermediate value theorem plus `nocross`). -/
theorem barrier_const_on_cell {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k < K)
    {t t' : ℝ} (ht : t ∈ Set.Ioo (z k) (z (k + 1)))
    (ht' : t' ∈ Set.Ioo (z k) (z (k + 1))) (x : Cube n) :
    x ∈ D.barrier ℓ t ↔ x ∈ D.barrier ℓ t' := by
  sorry

open Classical in
/-- Alive/dead out-rate table at time `t`, with frozen exponent `d` and
current-cell barrier `B`. `jrate D d B t s s'` is the jump rate from `s` to
`s'` (zero on the diagonal and for non-neighbors). -/
noncomputable def jrate (d : ℝ) (B : Set (Cube n)) (t : ℝ) :
    JSt n → JSt n → ℝ := fun s s' =>
  match s, s' with
  | (x, y, b), (x', y', b') =>
    ∑ i : Fin n,
      (-- synchronized flip along coordinate i
        (if x' = flipCoord i x ∧ y' = flipCoord i y ∧
            (b' = (b && decide (x' ∉ B))) then
          (if b then
            (if D.Y t i x < 1 then D.Y t i x / 2
             else D.Y t i x ^ (1 - d) / 2)
           else D.Y t i x / 2)
        else 0)
      + -- W-only flip (alive only, Y < 1)
        (if b ∧ b' = true ∧ x' = x ∧ y' = flipCoord i y ∧ D.Y t i x < 1 then
          (1 - D.Y t i x ^ d) / 2
        else 0)
      + -- V-only flip (alive only, Y ≥ 1)
        (if b ∧ y' = y ∧ x' = flipCoord i x ∧ ¬(D.Y t i x < 1) ∧
            (b' = decide (x' ∉ B)) then
          (D.Y t i x - D.Y t i x ^ (1 - d)) / 2
        else 0))

open Classical in
/-- Node transfer: alive mass on a state in the closed barrier at the node
time is moved to the dead sector (continuous crossing of `τ`); everything
else is unchanged. `killTr D ℓ t` as a matrix (entries in `{0,1}`). -/
noncomputable def killTr (ℓ t : ℝ) : JSt n → JSt n → ℝ := fun s s' =>
  match s, s' with
  | (x, y, b), (x', y', b') =>
    if x = x' ∧ y = y' ∧
        (b = (b' && decide (x' ∉ D.barrier ℓ t))) then 1 else 0

/-- Cell generator: forward matrix of the out-rates, with the cell barrier
sampled at the cell midpoint. -/
noncomputable def cellGen (ℓ θ d : ℝ) (z : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    JSt n → JSt n → ℝ :=
  fwdOf (jrate D d (D.barrier ℓ ((z k + z (k + 1)) / 2)) t)


/-! ### Helper lemmas on the rate table and the transfers

These are bookkeeping facts about `jrate`, `killTr`, `initVec` and `cellGen`
feeding the generic glued-flow machinery of `Flow/Glued.lean`. -/

private lemma flipCoord_ne_self (i : Fin n) (x : Cube n) : flipCoord i x ≠ x := by
  intro h
  have h1 := congrFun h i
  rw [flipCoord_self] at h1
  have h2 : toR (-(x i)) = toR (x i) := by rw [h1]
  rw [toR_neg] at h2
  exact toR_ne_zero (x i) (by linarith)

private lemma continuousOn_if_const {α : Type*} [TopologicalSpace α] {s : Set α}
    (P : Prop) [Decidable P] {f g : α → ℝ} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) :
    ContinuousOn (fun a => if P then f a else g a) s := by
  by_cases h : P
  · simpa only [if_pos h] using hf
  · simpa only [if_neg h] using hg

/-- Off-diagonal, monotone chaining of grid nodes. -/
private lemma grid_mono_le {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) : ∀ {i j : ℕ}, i ≤ j → j ≤ K → z i ≤ z j := by
  intro i j hij hj
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · rw [h]
      · have him : i ≤ m := Nat.lt_succ_iff.mp h
        exact le_trans (ih him (le_trans (Nat.le_succ m) hj))
          (hg.mono m (Nat.lt_of_succ_le hj))

private lemma grid_le_obsT {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k ≤ K) : z k ≤ obsT := by
  rw [← hg.last]; exact D.grid_mono_le hg hk le_rfl

private lemma grid_theta_le {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k ≤ K) : θ ≤ z k := by
  rw [← hg.first]; exact D.grid_mono_le hg (Nat.zero_le k) hk

open Classical in
/-- `min`/`max` reformulation of `jrate`, manifestly continuous in `t`
(helper only). -/
private noncomputable def jrateC (d : ℝ) (B : Set (Cube n)) (t : ℝ) :
    JSt n → JSt n → ℝ := fun s s' =>
  match s, s' with
  | (x, y, b), (x', y', b') =>
    ∑ i : Fin n,
      ((if x' = flipCoord i x ∧ y' = flipCoord i y ∧
            (b' = (b && decide (x' ∉ B))) then
          (if b then min (D.Y t i x) (D.Y t i x ^ (1 - d)) / 2
           else D.Y t i x / 2)
        else 0)
      + (if b ∧ b' = true ∧ x' = x ∧ y' = flipCoord i y then
          max (1 - D.Y t i x ^ d) 0 / 2
        else 0)
      + (if b ∧ y' = y ∧ x' = flipCoord i x ∧ (b' = decide (x' ∉ B)) then
          max (D.Y t i x - D.Y t i x ^ (1 - d)) 0 / 2
        else 0))

private lemma rpow_one_sub_le {Y d : ℝ} (hd0 : 0 ≤ d) (hY : 1 ≤ Y) :
    Y ^ (1 - d) ≤ Y := by
  calc Y ^ (1 - d) ≤ Y ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    _ = Y := Real.rpow_one Y

private lemma le_rpow_one_sub {Y d : ℝ} (hd0 : 0 ≤ d) (hY0 : 0 < Y) (hY : Y ≤ 1) :
    Y ≤ Y ^ (1 - d) := by
  calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
    _ ≤ Y ^ (1 - d) := Real.rpow_le_rpow_of_exponent_ge hY0 hY (by linarith)

private lemma jrate_eq_jrateC {d : ℝ} (hd0 : 0 ≤ d) (B : Set (Cube n)) {t : ℝ}
    (ht : t ≤ D.T) (s s' : JSt n) : D.jrate d B t s s' = D.jrateC d B t s s' := by
  obtain ⟨x, y, b⟩ := s
  obtain ⟨x', y', b'⟩ := s'
  classical
  simp only [jrate, jrateC]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hY : 0 < D.Y t i x := D.Y_pos ht i x
  by_cases hY1 : D.Y t i x < 1
  · have e1 : min (D.Y t i x) (D.Y t i x ^ (1 - d)) = D.Y t i x :=
      min_eq_left (le_rpow_one_sub hd0 hY hY1.le)
    have e2 : max (1 - D.Y t i x ^ d) 0 = 1 - D.Y t i x ^ d := by
      refine max_eq_left ?_
      have : D.Y t i x ^ d ≤ 1 := Real.rpow_le_one hY.le hY1.le hd0
      linarith
    have e3 : max (D.Y t i x - D.Y t i x ^ (1 - d)) 0 = 0 := by
      refine max_eq_right ?_
      have := le_rpow_one_sub hd0 hY hY1.le
      linarith
    simp only [e1, e2, e3, hY1, and_true, not_true_eq_false, false_and, and_false,
      zero_div, ite_self, if_true, reduceIte]
  · have hY1' : 1 ≤ D.Y t i x := not_lt.mp hY1
    have e1 : min (D.Y t i x) (D.Y t i x ^ (1 - d)) = D.Y t i x ^ (1 - d) :=
      min_eq_right (rpow_one_sub_le hd0 hY1')
    have e2 : max (1 - D.Y t i x ^ d) 0 = 0 := by
      refine max_eq_right ?_
      have : (1 : ℝ) ≤ D.Y t i x ^ d := Real.one_le_rpow hY1' hd0
      linarith
    have e3 : max (D.Y t i x - D.Y t i x ^ (1 - d)) 0
        = D.Y t i x - D.Y t i x ^ (1 - d) := by
      refine max_eq_left ?_
      have := rpow_one_sub_le hd0 hY1'
      linarith
    simp only [e1, e2, e3, hY1, not_false_eq_true, true_and, and_false, zero_div,
      ite_self, if_false]

private lemma continuousOn_jrateC {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (B : Set (Cube n)) (s s' : JSt n) {a b : ℝ} (hbT : b ≤ D.T) :
    ContinuousOn (fun t => D.jrateC d B t s s') (Set.Icc a b) := by
  obtain ⟨x, y, bb⟩ := s
  obtain ⟨x', y', b'⟩ := s'
  classical
  simp only [jrateC]
  refine continuousOn_finset_sum _ fun i _ => ?_
  have hY : ContinuousOn (fun t => D.Y t i x) (Set.Icc a b) :=
    (D.continuousOn_Y i x).mono fun t ht => le_trans ht.2 hbT
  have hr1 : ContinuousOn (fun t => D.Y t i x ^ (1 - d)) (Set.Icc a b) :=
    hY.rpow_const fun t _ => Or.inr (by linarith)
  have hr2 : ContinuousOn (fun t => D.Y t i x ^ d) (Set.Icc a b) :=
    hY.rpow_const fun t _ => Or.inr hd0
  have hmin : ContinuousOn (fun t => min (D.Y t i x) (D.Y t i x ^ (1 - d)))
      (Set.Icc a b) :=
    ContinuousOn.inf hY hr1
  have hmax2 : ContinuousOn (fun t => max (1 - D.Y t i x ^ d) 0) (Set.Icc a b) :=
    ContinuousOn.sup (ContinuousOn.sub continuousOn_const hr2) continuousOn_const
  have hmax3 : ContinuousOn (fun t => max (D.Y t i x - D.Y t i x ^ (1 - d)) 0)
      (Set.Icc a b) :=
    ContinuousOn.sup (ContinuousOn.sub hY hr1) continuousOn_const
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · exact continuousOn_if_const _
      (continuousOn_if_const _ (ContinuousOn.div_const hmin 2)
        (ContinuousOn.div_const hY 2)) continuousOn_const
  · exact continuousOn_if_const _ (ContinuousOn.div_const hmax2 2) continuousOn_const
  · exact continuousOn_if_const _ (ContinuousOn.div_const hmax3 2) continuousOn_const

private lemma continuousOn_jrate {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (B : Set (Cube n)) (s s' : JSt n) {a b : ℝ} (hbT : b ≤ D.T) :
    ContinuousOn (fun t => D.jrate d B t s s') (Set.Icc a b) :=
  (D.continuousOn_jrateC hd0 hd1 B s s' hbT).congr
    fun t ht => D.jrate_eq_jrateC hd0 B (le_trans ht.2 hbT) s s'

private lemma continuousOn_cellGen {ℓ θ d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (z : ℕ → ℝ) (k : ℕ) (hbT : z (k + 1) ≤ D.T) (s s' : JSt n) :
    ContinuousOn (fun t => D.cellGen ℓ θ d z k t s s')
      (Set.Icc (z k) (z (k + 1))) := by
  classical
  simp only [cellGen, fwdOf]
  refine ContinuousOn.sub (D.continuousOn_jrate hd0 hd1 _ _ _ hbT) ?_
  exact continuousOn_if_const _
    (continuousOn_finset_sum _ fun s'' _ =>
      D.continuousOn_jrate hd0 hd1 _ _ _ hbT) continuousOn_const

private lemma jrate_nonneg {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (B : Set (Cube n)) {t : ℝ} (ht : t ≤ D.T) (s s' : JSt n) :
    0 ≤ D.jrate d B t s s' := by
  obtain ⟨x, y, b⟩ := s
  obtain ⟨x', y', b'⟩ := s'
  classical
  simp only [jrate]
  refine Finset.sum_nonneg fun i _ => ?_
  have hY : 0 < D.Y t i x := D.Y_pos ht i x
  have hrp : 0 < D.Y t i x ^ (1 - d) := Real.rpow_pos_of_pos hY _
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · split_ifs <;> linarith
  · split_ifs with h
    · have hY1 : D.Y t i x < 1 := h.2.2.2.2
      have : D.Y t i x ^ d ≤ 1 := Real.rpow_le_one hY.le hY1.le hd0
      linarith
    · exact le_rfl
  · split_ifs with h
    · have hY1 : 1 ≤ D.Y t i x := not_lt.mp h.2.2.2.1
      have := rpow_one_sub_le hd0 hY1
      linarith
    · exact le_rfl

private lemma jrate_diag {d : ℝ} (B : Set (Cube n)) (t : ℝ) (s : JSt n) :
    D.jrate d B t s s = 0 := by
  obtain ⟨x, y, b⟩ := s
  classical
  simp only [jrate]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hx : ¬ (x = flipCoord i x) := fun h => flipCoord_ne_self i x h.symm
  have hy : ¬ (y = flipCoord i y) := fun h => flipCoord_ne_self i y h.symm
  simp [hx, hy]

private lemma killTr_nonneg (ℓ t : ℝ) (s s' : JSt n) : 0 ≤ D.killTr ℓ t s s' := by
  obtain ⟨x, y, b⟩ := s
  obtain ⟨x', y', b'⟩ := s'
  classical
  simp only [killTr]
  split_ifs <;> norm_num

/-- For a fixed target `s'` there is exactly one source, so the columns of
`killTr` sum to `1`. -/
private lemma killTr_col_sum (ℓ t : ℝ) (s' : JSt n) :
    ∑ s, D.killTr ℓ t s s' = 1 := by
  classical
  obtain ⟨x', y', b'⟩ := s'
  have key : ∀ s : JSt n, D.killTr ℓ t s (x', y', b')
      = if s = (x', y', (b' && decide (x' ∉ D.barrier ℓ t))) then 1 else 0 := by
    intro s
    obtain ⟨x, y, b⟩ := s
    simp only [killTr, Prod.mk.injEq]
    all_goals (refine if_congr ?_ rfl rfl; tauto)
  rw [Finset.sum_congr rfl fun s _ => key s]
  simp

private lemma initVec_nonneg (x₀ : Cube n) (s : JSt n) : 0 ≤ initVec x₀ s := by
  classical
  simp only [initVec]
  split_ifs <;> norm_num

private lemma initVec_sum (x₀ : Cube n) : ∑ s, initVec (n := n) x₀ s = 1 := by
  classical
  simp only [initVec]
  simp

/-- `IsCouplingFlow D ℓ θ x₀ K z π`: `π` is a glued flow for the stopped
power coupling started at `(x₀, x₀)` at time `θ`, on the admissible grid
`z`. -/
structure IsCouplingFlow (ℓ θ : ℝ) (x₀ : Cube n) (K : ℕ) (z : ℕ → ℝ)
    (π : ℕ → ℝ → JSt n → ℝ) : Prop where
  grid : D.AdmissibleGrid ℓ θ K z
  glued : IsGluedFlow K z (D.cellGen ℓ θ (D.dbar ℓ θ x₀) z)
    (fun k => D.killTr ℓ (z k)) (initVec x₀) π

/-- A bundled coupling flow for one starting point. -/
structure CFlow (ℓ θ : ℝ) (x₀ : Cube n) where
  K : ℕ
  z : ℕ → ℝ
  π : ℕ → ℝ → JSt n → ℝ
  is : D.IsCouplingFlow ℓ θ x₀ K z π

/-- A family of coupling flows, one per starting point (the grids may
differ). -/
def CFlowFamily (ℓ θ : ℝ) := ∀ x₀ : Cube n, D.CFlow ℓ θ x₀

/-- **Existence of the coupling flow** [LGF §4; C Lemma 6 well-posedness]. -/
theorem exists_cflow (ℓ : ℝ) (hℓ : 0 < ℓ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) (x₀ : Cube n) : Nonempty (D.CFlow ℓ θ x₀) := by
  obtain ⟨K, z, hg⟩ := D.exists_admissibleGrid ℓ hℓ hθ
  have hd0 := D.dbar_nonneg ℓ θ x₀
  have hd1 : D.dbar ℓ θ x₀ ≤ 1 := by
    have := D.dbar_lt_half ℓ θ x₀; linarith
  obtain ⟨π, hπ⟩ := exists_gluedFlow K z (D.cellGen ℓ θ (D.dbar ℓ θ x₀) z)
    (fun k => D.killTr ℓ (z k)) (initVec x₀) hg.mono
    (fun k hk s s' => D.continuousOn_cellGen hd0 hd1 z k
      (le_trans (D.grid_le_obsT hg (Nat.succ_le_of_lt hk)) (le_of_lt D.obsT_lt_T)) s s')
  exact ⟨⟨K, z, π, ⟨hg, hπ⟩⟩⟩

end Dat

/-- Terminal (time `T_o`) sub-law of a coupling flow (`D` implicit so that
`c.term` dot-notation resolves). -/
noncomputable def Dat.CFlow.term {n : ℕ} {D : Dat n} {ℓ θ : ℝ} {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) : JSt n → ℝ := c.π (c.K - 1) obsT

namespace Dat

variable (D : Dat n)


/-! ## Transport properties of the coupling flow -/

variable {ℓ θ : ℝ} {x₀ : Cube n}

/-- Nonnegativity of the flow. -/
theorem cflow_nonneg (hθ : θ ≤ obsT) (c : D.CFlow ℓ θ x₀)
    {k : ℕ} (hk : k < c.K) {t : ℝ} (ht : t ∈ Set.Icc (c.z k) (c.z (k + 1)))
    (s : JSt n) : 0 ≤ c.π k t s := by
  have hd0 := D.dbar_nonneg ℓ θ x₀
  have hd1 : D.dbar ℓ θ x₀ ≤ 1 := by
    have := D.dbar_lt_half ℓ θ x₀; linarith
  have hT : ∀ j : ℕ, j < c.K → c.z (j + 1) ≤ D.T := fun j hj =>
    le_trans (D.grid_le_obsT c.is.grid (Nat.succ_le_of_lt hj)) (le_of_lt D.obsT_lt_T)
  refine gluedFlow_nonneg c.is.glued
    (fun j hj a a' => D.continuousOn_cellGen hd0 hd1 _ _ (hT j hj) a a')
    (fun j hj t' ht' a a' hne => ?_)
    (fun j a a' => D.killTr_nonneg _ _ a a') (fun a => initVec_nonneg x₀ a) k hk t ht s
  exact fwdOf_offdiag_nonneg
    (fun u u' => D.jrate_nonneg hd0 hd1 _ (le_trans ht'.2 (hT j hj)) u u') hne

/-- Total mass conservation: `∑_s π_t(s) = 1` throughout. -/
theorem cflow_mass (hθ : θ ≤ obsT) (c : D.CFlow ℓ θ x₀)
    {k : ℕ} (hk : k < c.K) {t : ℝ} (ht : t ∈ Set.Icc (c.z k) (c.z (k + 1))) :
    ∑ s, c.π k t s = 1 := by
  have hcol : ∀ j, j < c.K → ∀ t' ∈ Set.Icc (c.z j) (c.z (j + 1)), ∀ s',
      ∑ s, D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z j t' s s' = 0 :=
    fun j _ t' _ s' => fwdOf_col_sum _ (fun a => D.jrate_diag _ _ a) s'
  rw [gluedFlow_mass c.is.glued hcol (fun j s' => D.killTr_col_sum ℓ (c.z j) s') k hk t ht,
    initVec_sum]

/-- Alive-sector support: alive mass never sits on a state of the current
cell's barrier (interior of the cell), and at the cell's endpoints alive mass
sits only on states with `F ≤ ℓ+1`. Stated in the endpoint form used
downstream: alive terminal mass satisfies `F_{T_o}(x) ≤ ℓ+1`. -/
theorem cflow_alive_support (hθ : θ ≤ obsT) (c : D.CFlow ℓ θ x₀)
    (x y : Cube n) (h : ℓ + 1 < D.F obsT x) :
    c.term (x, y, true) = 0 := by
  sorry

/-- The `V`-marginal of the coupling flow is the plain reverse flow: for
every sector-blind, `y`-blind test `g` the terminal pairing is transport of
`g` along the unperturbed reverse process from `(θ, x₀)` to `T_o`
[LGF Lemma 5.1, joint filtration / reverse marginal]. Concretely: the
`V`-marginal pairing equals the value at `(θ, x₀)` of the space-time
harmonic extension of `g`. -/
theorem cflow_V_marginal (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT) (c : D.CFlow ℓ θ x₀)
    (g : ℝ → Cube n → ℝ)
    (hg_cont : ∀ x, ContinuousOn (fun t => g t x) (Set.Icc θ obsT))
    (hg_deriv : ∀ x, ∀ t ∈ Set.Icc θ obsT,
      HasDerivWithinAt (fun t => g t x) (-(D.revGen t (g t) x))
        (Set.Icc θ obsT) t) :
    ∑ s, c.term s * g obsT s.1 = g θ x₀ := by
  sorry

end Dat

end Talagrand
