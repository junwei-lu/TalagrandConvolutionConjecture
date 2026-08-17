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

/-- The heat flow is a polynomial of degree `≤ n` in the correlation `ρ`. -/
private lemma exists_heatPoly (f : Cube n → ℝ) (x : Cube n) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧ ∀ ρ : ℝ, p.eval ρ = smooth ρ f x := by
  classical
  refine ⟨∑ y : Cube n, Polynomial.C (f y) *
      ∏ i : Fin n, (Polynomial.C (toR (x i) * toR (y i) / 2) * Polynomial.X
        + Polynomial.C (1 / 2)), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun y _ => ?_
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_C, zero_add]
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      Polynomial.natDegree_linear_le) ?_
    simp
  · intro ρ
    rw [Polynomial.eval_finset_sum, smooth_eq_kernel_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    ring

private lemma smooth_zero_eq_unifE (f : Cube n → ℝ) (x : Cube n) :
    smooth 0 f x = unifE f := by
  rw [smooth_eq_kernel_sum, unifE, Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h1 : ∀ j : Fin n, (1 + (0 : ℝ) * toR (x j) * toR (y j)) / 2 = 1 / 2 := by
    intro j; ring
  rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) => h1 j]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, one_pow]
  have h2 : ((2 : ℝ)) ^ n ≠ 0 := by positivity
  field_simp

/-- Intermediate value theorem for the log-density: the level `ℓ+1` between
`F a x` and `F b x` is attained on `[a,b]`. -/
private lemma exists_cross {ℓ a b : ℝ} (hab : a ≤ b) (hbT : b ≤ D.T) (x : Cube n)
    (h : (D.F a x < ℓ + 1 ∧ ℓ + 1 ≤ D.F b x) ∨
      (D.F b x < ℓ + 1 ∧ ℓ + 1 ≤ D.F a x)) :
    ∃ c ∈ Set.Icc a b, D.F c x = ℓ + 1 := by
  have hcont : ContinuousOn (fun t => D.F t x) (Set.Icc a b) :=
    (D.continuousOn_F x).mono fun t ht => le_trans ht.2 hbT
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨c, hc, hc2⟩ := intermediate_value_Icc hab hcont ⟨h1.le, h2⟩
    exact ⟨c, hc, hc2⟩
  · obtain ⟨c, hc, hc2⟩ := intermediate_value_Icc' hab hcont ⟨h1.le, h2⟩
    exact ⟨c, hc, hc2⟩

/-- Existence of an admissible grid: barrier crossings are roots of a nonzero
polynomial in `e^{-(T-t)}` (constant coefficient `1 ≠ e^{ℓ+1}`), hence
finitely many; sort them. -/
theorem exists_admissibleGrid (ℓ : ℝ) (hℓ : 0 < ℓ) {θ : ℝ} (hθ : θ ≤ obsT) :
    ∃ K z, D.AdmissibleGrid ℓ θ K z := by
  classical
  rcases eq_or_lt_of_le hθ with hθeq | hθlt
  · -- degenerate case `θ = T_o`: a single (empty) cell
    refine ⟨1, fun k => if k = 0 then θ else obsT, Nat.one_pos, by simp, by simp,
      ?_, ?_⟩
    · intro k hk
      obtain rfl : k = 0 := Nat.lt_one_iff.mp hk
      simpa using hθ
    · intro k hk t ht x _
      obtain rfl : k = 0 := Nat.lt_one_iff.mp hk
      simp only [Set.mem_Ioo, zero_add, if_pos, one_ne_zero, if_false] at ht
      rw [← hθeq] at ht
      exact absurd (lt_trans ht.1 ht.2) (lt_irrefl θ)
  -- main case: finitely many crossing times, taken as nodes
  choose p hpdeg hpev using fun x : Cube n => exists_heatPoly D.f x
  have hfsPoly : ∀ (u : ℝ) (x : Cube n), D.fs u x
      = ∑ k ∈ Finset.range (n + 1), (p x).coeff k * Real.exp (-u) ^ k := by
    intro u x
    rw [Dat.fs, heatAt, ← hpev x (Real.exp (-u)),
      Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hpdeg x))]
  have hcoeff0 : ∀ x : Cube n, (p x).coeff 0 = 1 := by
    intro x
    rw [Polynomial.coeff_zero_eq_eval_zero, hpev x 0, smooth_zero_eq_unifE, D.hm]
  have hexp : (1 : ℝ) < Real.exp (ℓ + 1) := by
    have := Real.add_one_le_exp (ℓ + 1); linarith
  have hfin0 : {u : ℝ | ∃ x : Cube n, D.fs u x = Real.exp (ℓ + 1)}.Finite := by
    have hne : ∀ x : Cube n, Real.exp (ℓ + 1) ≠ (p x).coeff 0 := by
      intro x; rw [hcoeff0 x]; exact ne_of_gt hexp
    have hFin := finite_setOf_expPoly_family_eq (N := n + 1)
      (fun (x : Cube n) k => (p x).coeff k) (fun _ => Real.exp (ℓ + 1)) hne
    refine hFin.subset ?_
    intro u hu
    obtain ⟨x, hx⟩ := hu
    exact ⟨x, by rw [← hfsPoly u x]; exact hx⟩
  have hZfin : ((fun t => D.T - t) ⁻¹'
      {u : ℝ | ∃ x : Cube n, D.fs u x = Real.exp (ℓ + 1)} ∩ Set.Icc θ obsT).Finite :=
    Set.Finite.inter_of_left
      (Set.Finite.preimage (Set.injOn_of_injective fun a b hab => by
        simpa using neg_injective (by linarith [hab] : -a = -b)) hfin0) _
  set S : Finset ℝ := insert θ (insert obsT hZfin.toFinset) with hSdef
  have hθS : θ ∈ S := Finset.mem_insert_self _ _
  have hobsS : obsT ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hmemS : ∀ v ∈ S, θ ≤ v ∧ v ≤ obsT := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨le_rfl, hθ⟩
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨hθ, le_rfl⟩
    · exact ⟨(hZfin.mem_toFinset.mp hv).2.1, (hZfin.mem_toFinset.mp hv).2.2⟩
  have hcard : 2 ≤ S.card :=
    Finset.one_lt_card.mpr ⟨θ, hθS, obsT, hobsS, ne_of_lt hθlt⟩
  have hcard0 : 0 < S.card := by omega
  set e := S.orderIsoOfFin (rfl : S.card = S.card) with hedef
  have hmem_e : ∀ j : Fin S.card, (e j).1 ∈ S := fun j => (e j).2
  have hmono_e : ∀ i j : Fin S.card, i ≤ j → (e i).1 ≤ (e j).1 := fun i j hij =>
    Subtype.coe_le_coe.mpr (e.monotone hij)
  have hlt_e : ∀ i j : Fin S.card, (e i).1 < (e j).1 → i < j := fun i j h =>
    e.lt_iff_lt.mp (Subtype.coe_lt_coe.mp h)
  have hsurj : ∀ v ∈ S, ∃ j : Fin S.card, (e j).1 = v := by
    intro v hv
    exact ⟨e.symm ⟨v, hv⟩, by rw [OrderIso.apply_symm_apply]⟩
  refine ⟨S.card - 1,
    fun k => if h : k < S.card then (e ⟨k, h⟩).1 else obsT, ?_⟩
  have hzv : ∀ (k : ℕ) (h : k < S.card),
      (if h' : k < S.card then (e ⟨k, h'⟩).1 else obsT) = (e ⟨k, h⟩).1 :=
    fun k h => dif_pos h
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · -- `z 0 = θ`
    rw [hzv 0 hcard0]
    obtain ⟨j, hj⟩ := hsurj θ hθS
    refine le_antisymm ?_ (hmemS _ (hmem_e _)).1
    rw [← hj]; exact hmono_e _ _ (Fin.le_def.mpr (Nat.zero_le _))
  · -- `z K = T_o`
    have hlt : S.card - 1 < S.card := by omega
    rw [hzv _ hlt]
    obtain ⟨j, hj⟩ := hsurj obsT hobsS
    refine le_antisymm (hmemS _ (hmem_e _)).2 ?_
    rw [← hj]
    exact hmono_e _ _ (Fin.le_def.mpr
      (show (j : ℕ) ≤ S.card - 1 from by have := j.isLt; omega))
  · -- monotone
    intro k hk
    rw [hzv k (by omega), hzv (k + 1) (by omega)]
    exact hmono_e _ _ (Fin.mk_le_mk.mpr (by omega))
  · -- no crossing inside an open cell
    intro k hk t ht x hx
    have h1 : k < S.card := by omega
    have h2 : k + 1 < S.card := by omega
    rw [hzv k h1, hzv (k + 1) h2] at ht
    have hθt : θ ≤ t := le_trans (hmemS _ (hmem_e ⟨k, h1⟩)).1 ht.1.le
    have htobs : t ≤ obsT := le_trans ht.2.le (hmemS _ (hmem_e ⟨k + 1, h2⟩)).2
    have hTt : 0 ≤ D.T - t := by
      have := D.obsT_lt_T; linarith
    have hpos : 0 < D.fs (D.T - t) x := D.fs_pos hTt x
    have hfsx : D.fs (D.T - t) x = Real.exp (ℓ + 1) := by
      simp only [Dat.F] at hx
      rw [← hx, Real.exp_log hpos]
    have htS : t ∈ S :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (hZfin.mem_toFinset.mpr ⟨⟨x, hfsx⟩, ⟨hθt, htobs⟩⟩))
    obtain ⟨j, hj⟩ := hsurj t htS
    have hkj : (⟨k, h1⟩ : Fin S.card) < j := hlt_e _ _ (by rw [hj]; exact ht.1)
    have hkj' : k < (j : ℕ) := hkj
    have : (e ⟨k + 1, h2⟩).1 ≤ t := by
      rw [← hj]
      exact hmono_e _ _ (Fin.le_def.mpr (show k + 1 ≤ (j : ℕ) from by omega))
    exact absurd ht.2 (not_lt.mpr this)

/-- Barrier membership is constant on open cells of an admissible grid
(intermediate value theorem plus `nocross`). -/
theorem barrier_const_on_cell {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k < K)
    {t t' : ℝ} (ht : t ∈ Set.Ioo (z k) (z (k + 1)))
    (ht' : t' ∈ Set.Ioo (z k) (z (k + 1))) (x : Cube n) :
    x ∈ D.barrier ℓ t ↔ x ∈ D.barrier ℓ t' := by
  have hbT : ∀ u ∈ Set.Ioo (z k) (z (k + 1)), u ≤ D.T := by
    intro u hu
    have h1 : u < z (k + 1) := hu.2
    have h2 : z (k + 1) ≤ obsT := D.grid_le_obsT hg (Nat.succ_le_of_lt hk)
    have := D.obsT_lt_T
    linarith
  have key : ∀ u ∈ Set.Ioo (z k) (z (k + 1)), ∀ u' ∈ Set.Ioo (z k) (z (k + 1)),
      ℓ + 1 ≤ D.F u x → ℓ + 1 ≤ D.F u' x := by
    intro u hu u' hu' hb
    by_contra hb'
    rw [not_le] at hb'
    rcases le_total u' u with hle | hle
    · obtain ⟨c, hc, hc2⟩ := D.exists_cross hle (hbT u hu) x (Or.inl ⟨hb', hb⟩)
      exact hg.nocross k hk c
        ⟨lt_of_lt_of_le hu'.1 hc.1, lt_of_le_of_lt hc.2 hu.2⟩ x hc2
    · obtain ⟨c, hc, hc2⟩ := D.exists_cross hle (hbT u' hu') x (Or.inr ⟨hb', hb⟩)
      exact hg.nocross k hk c
        ⟨lt_of_lt_of_le hu.1 hc.1, lt_of_le_of_lt hc.2 hu'.2⟩ x hc2
  exact ⟨fun h => key t ht t' ht' h, fun h => key t' ht' t ht h⟩

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
    fun _ ht => D.jrate_eq_jrateC hd0 B (le_trans ht.2 hbT) s s'

private lemma continuousOn_fwdOf {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (B : Set (Cube n)) {a b : ℝ} (hbT : b ≤ D.T) (s s' : JSt n) :
    ContinuousOn (fun t => fwdOf (D.jrate d B t) s s') (Set.Icc a b) := by
  classical
  simp only [fwdOf]
  refine ContinuousOn.sub (D.continuousOn_jrate hd0 hd1 _ _ _ hbT) ?_
  exact continuousOn_if_const _
    (continuousOn_finset_sum _ fun s'' _ =>
      D.continuousOn_jrate hd0 hd1 _ _ _ hbT) continuousOn_const

private lemma continuousOn_cellGen {ℓ θ d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (z : ℕ → ℝ) (k : ℕ) (hbT : z (k + 1) ≤ D.T) (s s' : JSt n) :
    ContinuousOn (fun t => D.cellGen ℓ θ d z k t s s')
      (Set.Icc (z k) (z (k + 1))) :=
  D.continuousOn_fwdOf hd0 hd1 _ hbT s s'

private lemma jrate_nonneg {d : ℝ} (hd0 : 0 ≤ d) (_hd1 : d ≤ 1)
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

/-! ### Pairing identities (generator duality) -/

/-- One-target jump sums: `P1` has a unique target, `P2` contributes nothing to
the test (its target has the same `V`-coordinate), `P3` has a unique target
under the side condition `Q3`. -/
private lemma sum_three_jumps (P1 P2 P3 : JSt n → Prop)
    [DecidablePred P1] [DecidablePred P2] [DecidablePred P3]
    (Q3 : Prop) [Decidable Q3] (s1 s3 : JSt n) (r1 r2 r3 : ℝ) (f : JSt n → ℝ)
    (h1 : ∀ s, P1 s ↔ s = s1) (h2 : ∀ s, P2 s → f s = 0)
    (h3 : ∀ s, P3 s ↔ (Q3 ∧ s = s3)) :
    ∑ s : JSt n, ((if P1 s then r1 else 0) + (if P2 s then r2 else 0)
        + (if P3 s then r3 else 0)) * f s
      = r1 * f s1 + (if Q3 then r3 * f s3 else 0) := by
  classical
  have key : ∀ s : JSt n, ((if P1 s then r1 else 0) + (if P2 s then r2 else 0)
      + (if P3 s then r3 else 0)) * f s
      = (if s = s1 then r1 * f s1 else 0)
        + (if Q3 ∧ s = s3 then r3 * f s3 else 0) := by
    intro s
    have e2 : (if P2 s then r2 else 0) * f s = 0 := by
      by_cases hp : P2 s
      · rw [h2 s hp, mul_zero]
      · rw [if_neg hp, zero_mul]
    have e1 : (if P1 s then r1 else 0) * f s = if s = s1 then r1 * f s1 else 0 := by
      by_cases hp : P1 s
      · have hs := (h1 s).mp hp
        rw [if_pos hp, if_pos hs, hs]
      · rw [if_neg hp, if_neg (fun hEq => hp ((h1 s).mpr hEq)), zero_mul]
    have e3 : (if P3 s then r3 else 0) * f s
        = if Q3 ∧ s = s3 then r3 * f s3 else 0 := by
      by_cases hp : P3 s
      · have hs := (h3 s).mp hp
        rw [if_pos hp, if_pos hs, hs.2]
      · rw [if_neg hp, if_neg (fun hEq => hp ((h3 s).mpr hEq)), zero_mul]
    rw [add_mul, add_mul, e1, e2, e3, add_zero]
  rw [Finset.sum_congr rfl fun s _ => key s, Finset.sum_add_distrib]
  congr 1
  · simp
  · by_cases hq : Q3
    · simp only [hq, true_and, if_true]
      simp
    · simp only [hq, false_and, if_false, Finset.sum_const_zero]

/-- **Generator duality** for the forward matrix of an out-rate table. -/
private lemma fwdOf_pairing_generic (q : JSt n → JSt n → ℝ) (v w : JSt n → ℝ) :
    ∑ s, matVec (fwdOf q) v s * w s
      = ∑ s, v s * (∑ s', q s s' * (w s' - w s)) := by
  have hL : ∀ s : JSt n, matVec (fwdOf q) v s * w s
      = (∑ s' : JSt n, q s' s * v s' * w s)
        - (∑ s'' : JSt n, q s s'') * v s * w s := by
    intro s
    simp only [matVec, fwdOf, Finset.sum_mul, sub_mul, ite_mul, zero_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_ite_eq]
    simp
  have e1 : ∑ s : JSt n, ∑ s' : JSt n, q s' s * v s' * w s
      = ∑ s : JSt n, ∑ s' : JSt n, q s s' * v s * w s' :=
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (a b : JSt n) => q b a * v b * w a)
  have e2 : ∑ s : JSt n, (∑ s'' : JSt n, q s s'') * v s * w s
      = ∑ s : JSt n, ∑ s' : JSt n, q s s' * v s * w s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun s _ => hL s, Finset.sum_sub_distrib, e1, e2,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s' _ => by ring

/-- The out-jumps of the coupling move the `V`-coordinate with total rate
`Y_i/2` (the sector split and the `W`-only jumps are invisible to a
`y`-blind, sector-blind test), so the `V`-marginal generator is `revGen`. -/
private lemma jrate_pairing_state {d : ℝ} (B : Set (Cube n)) (t : ℝ) (s : JSt n)
    (h : Cube n → ℝ) :
    ∑ s' : JSt n, D.jrate d B t s s' * (h s'.1 - h s.1) = D.revGen t h s.1 := by
  classical
  obtain ⟨x, y, b⟩ := s
  simp only [jrate, revGen]
  rw [Finset.sum_congr rfl fun s' _ => Finset.sum_mul _ _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans (sum_three_jumps _ _ _ (b = true ∧ ¬(D.Y t i x < 1))
    ((flipCoord i x, flipCoord i y, (b && decide (flipCoord i x ∉ B))) : JSt n)
    ((flipCoord i x, y, decide (flipCoord i x ∉ B)) : JSt n) _ _ _ _ ?_ ?_ ?_) ?_
  · intro s'
    constructor
    · refine fun hc => Prod.ext_iff.mpr ⟨hc.1, Prod.ext_iff.mpr ⟨hc.2.1, ?_⟩⟩
      rw [hc.2.2, hc.1]
    · intro hEq
      subst hEq
      exact ⟨rfl, rfl, rfl⟩
  · intro s' hs'
    rw [hs'.2.2.1, sub_self]
  · intro s'
    constructor
    · refine fun hc => ⟨⟨hc.1, hc.2.2.2.1⟩,
        Prod.ext_iff.mpr ⟨hc.2.2.1, Prod.ext_iff.mpr ⟨hc.2.1, ?_⟩⟩⟩
      rw [hc.2.2.2.2, hc.2.2.1]
    · intro hc
      obtain ⟨⟨hb, hY⟩, hEq⟩ := hc
      subst hEq
      exact ⟨hb, rfl, rfl, hY, rfl⟩
  · rcases Bool.eq_false_or_eq_true b with hb | hb <;>
      by_cases hY1 : D.Y t i x < 1 <;> simp [hb, hY1] <;> ring

open Classical in
/-- The unique source of a node transfer: `killTr` is a `{0,1}` matrix with one
nonzero entry per column. -/
private lemma killTr_eq_single (ℓ t : ℝ) (s s' : JSt n) :
    D.killTr ℓ t s s'
      = if s = (s'.1, s'.2.1, (s'.2.2 && decide (s'.1 ∉ D.barrier ℓ t))) then 1
        else 0 := by
  classical
  obtain ⟨x, y, b⟩ := s
  obtain ⟨x', y', b'⟩ := s'
  simp only [killTr, Prod.mk.injEq]

/-- The node transfers preserve the pairing with a sector-blind, `y`-blind
test (they only move mass between sectors at fixed positions). -/
private lemma killTr_pairing (ℓ t : ℝ) (v : JSt n → ℝ) (h : Cube n → ℝ) :
    ∑ s : JSt n, matVec (D.killTr ℓ t) v s * h s.1 = ∑ s : JSt n, v s * h s.1 := by
  classical
  simp only [matVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  have key : ∀ s : JSt n, D.killTr ℓ t s s' * v s' * h s.1
      = if s = (s'.1, s'.2.1, (s'.2.2 && decide (s'.1 ∉ D.barrier ℓ t))) then
          v s' * h s'.1 else 0 := by
    intro s
    rw [D.killTr_eq_single ℓ t s s']
    by_cases hs : s = ((s'.1, s'.2.1, (s'.2.2 && decide (s'.1 ∉ D.barrier ℓ t))) : JSt n)
    · rw [if_pos hs, if_pos hs, hs]
      simp
    · rw [if_neg hs, if_neg hs, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun s _ => key s]
  simp

/-! ### The alive sector avoids the barrier -/

/-- The cell barrier (sampled at the midpoint) is contained in the barrier at
the left node: a state acquiring the barrier strictly inside the cell would
force a crossing there. -/
private lemma barrier_mid_subset {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k < K) {x : Cube n}
    (hx : x ∈ D.barrier ℓ ((z k + z (k + 1)) / 2)) : x ∈ D.barrier ℓ (z k) := by
  by_contra hcon
  simp only [barrier, Set.mem_setOf_eq, not_le] at hcon hx
  have hzmono : z k ≤ z (k + 1) := hg.mono k hk
  have hmid : z k ≤ (z k + z (k + 1)) / 2 := by linarith
  have hmidT : (z k + z (k + 1)) / 2 ≤ D.T := by
    have h1 : z (k + 1) ≤ obsT := D.grid_le_obsT hg (Nat.succ_le_of_lt hk)
    have h2 : z k ≤ obsT := D.grid_le_obsT hg (le_of_lt hk)
    have := D.obsT_lt_T
    linarith
  obtain ⟨cc, hcc, hcc2⟩ := D.exists_cross hmid hmidT x (Or.inl ⟨hcon, hx⟩)
  have hne1 : z k < cc :=
    lt_of_le_of_ne hcc.1 (by intro hEq; rw [← hEq] at hcc2; linarith)
  have hlt : z k < z (k + 1) := by linarith [hcc.2]
  exact hg.nocross k hk cc ⟨hne1, by linarith [hcc.2]⟩ x hcc2

/-- The node transfer clears alive mass on the barrier at the node time. -/
private lemma killTr_kills {ℓ t : ℝ} (v : JSt n → ℝ) {s : JSt n}
    (hs1 : s.2.2 = true) (hs2 : s.1 ∈ D.barrier ℓ t) :
    matVec (D.killTr ℓ t) v s = 0 := by
  classical
  obtain ⟨x, y, b⟩ := s
  simp only at hs1 hs2
  subst hs1
  refine Finset.sum_eq_zero fun s' _ => ?_
  obtain ⟨x', y', b'⟩ := s'
  have hdec : decide (x ∉ D.barrier ℓ t) = false := by simp [hs2]
  have hz : D.killTr ℓ t (x, y, true) (x', y', b') = 0 := by
    simp only [killTr]
    refine if_neg ?_
    rintro ⟨hxx, -, h3⟩
    rw [← hxx, hdec, Bool.and_false] at h3
    exact Bool.noConfusion h3
  rw [hz, zero_mul]

/-- No alive in-flux to a barred state from a state that is not itself alive
and barred: sync and `V`-only jumps land alive only off the barrier, and
`W`-only jumps do not move the `V`-coordinate. -/
private lemma jrate_into_bad {d : ℝ} {B : Set (Cube n)} {t : ℝ} {s s' : JSt n}
    (hs1 : s.2.2 = true) (hs2 : s.1 ∈ B) (hs' : ¬ (s'.2.2 = true ∧ s'.1 ∈ B)) :
    D.jrate d B t s' s = 0 := by
  classical
  obtain ⟨x, y, b⟩ := s
  obtain ⟨x'', y'', b''⟩ := s'
  simp only at hs1 hs2 hs'
  subst hs1
  simp only [jrate]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hdec : decide (x ∉ B) = false := by simp [hs2]
  rcases Bool.eq_false_or_eq_true b'' with hb | hb
  · have hxne : x ≠ x'' := fun hEq => hs' ⟨hb, by rw [← hEq]; exact hs2⟩
    simp [hb, hdec, hxne]
  · simp [hb, hdec]

open Classical in
/-- **Cell invariant**: alive mass never sits on the cell barrier. The
alive-and-barred states form a closed sub-system (no in-flux from other
states) with zero initial data, hence carry no mass, by uniqueness for the
truncated generator. -/
private lemma cell_alive_zero {d : ℝ} {B : Set (Cube n)} {a b : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hab : a ≤ b) (hbT : b ≤ D.T)
    {π : ℝ → JSt n → ℝ}
    (hflow : IsLinFlow (fun t => fwdOf (D.jrate d B t)) a b π)
    (h0 : ∀ s : JSt n, s.2.2 = true → s.1 ∈ B → π a s = 0) :
    ∀ t ∈ Set.Icc a b, ∀ s : JSt n, s.2.2 = true → s.1 ∈ B → π t s = 0 := by
  classical
  -- no in-flux into an alive barred state from any other state
  have hnoflux : ∀ (t : ℝ) (u v : JSt n), (u.2.2 = true ∧ u.1 ∈ B) →
      ¬ (v.2.2 = true ∧ v.1 ∈ B) → fwdOf (D.jrate d B t) u v = 0 := by
    intro t u v hu hv
    have hne : u ≠ v := fun hEq => hv (hEq ▸ hu)
    simp only [fwdOf, if_neg hne, sub_zero]
    exact D.jrate_into_bad hu.1 hu.2 hv
  -- the truncated generator and the barred part of the flow
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ → JSt n → JSt n → ℝ, A' = fun t u v =>
      if (u.2.2 = true ∧ u.1 ∈ B) ∧ (v.2.2 = true ∧ v.1 ∈ B) then
        fwdOf (D.jrate d B t) u v else 0 := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → JSt n → ℝ, σ = fun t s =>
      if s.2.2 = true ∧ s.1 ∈ B then π t s else 0 := ⟨_, rfl⟩
  have hA'cont : ∀ u v : JSt n, ContinuousOn (fun t => A' t u v) (Set.Icc a b) := by
    intro u v
    rw [hA']
    exact continuousOn_if_const _ (D.continuousOn_fwdOf hd0 hd1 B hbT u v)
      continuousOn_const
  have hmv : ∀ (t : ℝ) (s : JSt n), (s.2.2 = true ∧ s.1 ∈ B) →
      matVec (A' t) (σ t) s = matVec (fwdOf (D.jrate d B t)) (π t) s := by
    intro t s hs
    simp only [matVec]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v.2.2 = true ∧ v.1 ∈ B
    · rw [hA', hσ]
      simp only [if_pos hv, if_pos (And.intro hs hv)]
    · rw [hnoflux t s v hs hv, hA', hσ]
      simp only [if_neg hv, if_neg (fun h : (s.2.2 = true ∧ s.1 ∈ B) ∧
        (v.2.2 = true ∧ v.1 ∈ B) => hv h.2), zero_mul, mul_zero]
  have h1 : IsLinFlow A' a b σ := by
    refine ⟨fun s => ?_, fun s t ht => ?_⟩
    · by_cases hs : s.2.2 = true ∧ s.1 ∈ B
      · rw [hσ]; simpa only [if_pos hs] using hflow.cont s
      · rw [hσ]; simpa only [if_neg hs] using
          (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc a b))
    · by_cases hs : s.2.2 = true ∧ s.1 ∈ B
      · rw [hmv t s hs, hσ]
        simpa only [if_pos hs] using hflow.deriv s t ht
      · have hzero : matVec (A' t) (σ t) s = 0 := by
          simp only [matVec, hA']
          refine Finset.sum_eq_zero fun v _ => ?_
          rw [if_neg (fun h : (s.2.2 = true ∧ s.1 ∈ B) ∧
            (v.2.2 = true ∧ v.1 ∈ B) => hs h.1), zero_mul]
        rw [hzero, hσ]
        simpa only [if_neg hs] using
          (hasDerivWithinAt_const t (Set.Icc a b) (0 : ℝ))
  have h2 : IsLinFlow A' a b (fun _ _ => 0) := by
    refine ⟨fun s => continuousOn_const, fun s t ht => ?_⟩
    have hzero : matVec (A' t) (fun _ => (0 : ℝ)) s = 0 := by simp [matVec]
    rw [hzero]
    exact hasDerivWithinAt_const _ _ _
  have hinit : σ a = (fun _ => (0 : ℝ)) := by
    funext s
    by_cases hs : s.2.2 = true ∧ s.1 ∈ B
    · rw [hσ]; simp only [if_pos hs]; exact h0 s hs.1 hs.2
    · rw [hσ]; simp only [if_neg hs]
  have huniq := linFlow_unique hab hA'cont h1 h2 hinit
  intro t ht s hs1 hs2
  have hthis := congrFun (huniq t ht) s
  rw [hσ] at hthis
  simpa only [if_pos (And.intro hs1 hs2)] using hthis

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
  classical
  obtain ⟨j, hjK⟩ : ∃ j, c.K = j + 1 := ⟨c.K - 1, by have := c.is.grid.pos; omega⟩
  have hjlt : j < c.K := by omega
  have hd0 := D.dbar_nonneg ℓ θ x₀
  have hd1 : D.dbar ℓ θ x₀ ≤ 1 := by
    have := D.dbar_lt_half ℓ θ x₀; linarith
  have hzmono : c.z j ≤ c.z (j + 1) := c.is.grid.mono j hjlt
  have hlast : c.z (j + 1) = obsT := by rw [← hjK]; exact c.is.grid.last
  have hzT : c.z (j + 1) ≤ D.T := by
    rw [hlast]; exact le_of_lt D.obsT_lt_T
  -- the starting value of the last cell is cleared on the barrier at the node
  have hinit : ∀ s : JSt n, s.2.2 = true →
      s.1 ∈ D.barrier ℓ ((c.z j + c.z (j + 1)) / 2) → c.π j (c.z j) s = 0 := by
    intro s hs1 hs2
    have hsB : s.1 ∈ D.barrier ℓ (c.z j) :=
      D.barrier_mid_subset c.is.grid hjlt hs2
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [c.is.glued.init]
      exact D.killTr_kills _ hs1 hsB
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [c.is.glued.node m (by omega)]
      exact D.killTr_kills _ hs1 hsB
  have hinv := D.cell_alive_zero hd0 hd1 hzmono hzT (c.is.glued.flow j hjlt) hinit
  -- the terminal state is in the last cell's barrier
  have hxB : x ∈ D.barrier ℓ ((c.z j + c.z (j + 1)) / 2) := by
    by_contra hcon
    simp only [barrier, Set.mem_setOf_eq, not_le] at hcon
    have hmid2 : (c.z j + c.z (j + 1)) / 2 ≤ obsT := by rw [← hlast]; linarith
    obtain ⟨cc, hcc, hcc2⟩ := D.exists_cross hmid2 (le_of_lt D.obsT_lt_T) x
      (Or.inl ⟨hcon, h.le⟩)
    have hne1 : (c.z j + c.z (j + 1)) / 2 < cc :=
      lt_of_le_of_ne hcc.1 (by intro hEq; rw [← hEq] at hcc2; linarith)
    have hne2 : cc < obsT :=
      lt_of_le_of_ne hcc.2 (by intro hEq; rw [hEq] at hcc2; linarith)
    exact c.is.grid.nocross j hjlt cc
      ⟨by linarith, by rw [hlast]; exact hne2⟩ x hcc2
  have hterm : c.term = c.π j obsT := by
    simp only [Dat.CFlow.term, hjK, Nat.add_sub_cancel]
  rw [hterm]
  exact hinv obsT ⟨by rw [← hlast]; exact hzmono, le_of_eq hlast.symm⟩
    (x, y, true) rfl hxB

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
  classical
  have hgrid := c.is.grid
  have hK := hgrid.pos
  have hcell : ∀ k, k < c.K → Set.Icc (c.z k) (c.z (k + 1)) ⊆ Set.Icc θ obsT := by
    intro k hk u hu
    exact ⟨le_trans (D.grid_theta_le hgrid (le_of_lt hk)) hu.1,
      le_trans hu.2 (D.grid_le_obsT hgrid (Nat.succ_le_of_lt hk))⟩
  -- cell-wise: the pairing is constant
  have hu_cont : ∀ k, k < c.K →
      ContinuousOn (fun t => ∑ s, c.π k t s * g t s.1)
        (Set.Icc (c.z k) (c.z (k + 1))) := by
    intro k hk
    refine continuousOn_finset_sum _ fun s _ => ?_
    exact ContinuousOn.mul ((c.is.glued.flow k hk).cont s)
      ((hg_cont s.1).mono (hcell k hk))
  have hu_deriv : ∀ k, k < c.K → ∀ t ∈ Set.Icc (c.z k) (c.z (k + 1)),
      HasDerivWithinAt (fun t => ∑ s, c.π k t s * g t s.1) 0
        (Set.Icc (c.z k) (c.z (k + 1))) t := by
    intro k hk t ht
    have hflow := c.is.glued.flow k hk
    have hgd : ∀ s : JSt n, HasDerivWithinAt (fun t => g t s.1)
        (-(D.revGen t (g t) s.1)) (Set.Icc (c.z k) (c.z (k + 1))) t :=
      fun s => (hg_deriv s.1 t (hcell k hk ht)).mono (hcell k hk)
    have hpair := hasDerivWithinAt_pairing hflow ht hgd
    have hdual : ∑ s : JSt n,
        matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s * g t s.1
          = ∑ s : JSt n, c.π k t s * D.revGen t (g t) s.1 := by
      simp only [cellGen]
      rw [fwdOf_pairing_generic]
      exact Finset.sum_congr rfl fun s _ =>
        congrArg (fun r => c.π k t s * r) (D.jrate_pairing_state _ t s (g t))
    have hzero : ∑ s : JSt n,
        (matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s * g t s.1
          + c.π k t s * -(D.revGen t (g t) s.1)) = 0 := by
      rw [Finset.sum_add_distrib, hdual]
      have h2 : ∑ s : JSt n, c.π k t s * -(D.revGen t (g t) s.1)
          = -∑ s : JSt n, c.π k t s * D.revGen t (g t) s.1 := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [h2, add_neg_cancel]
    simpa only [hzero] using hpair
  -- node-wise: the transfers preserve the pairing
  have hnode : ∀ k, k + 1 < c.K →
      (∑ s, c.π (k + 1) (c.z (k + 1)) s * g (c.z (k + 1)) s.1)
        = ∑ s, c.π k (c.z (k + 1)) s * g (c.z (k + 1)) s.1 := by
    intro k hk
    rw [c.is.glued.node k hk]
    exact D.killTr_pairing ℓ (c.z (k + 1)) (c.π k (c.z (k + 1))) (g (c.z (k + 1)))
  have hchain := chain_eq hK (z := c.z)
    (u := fun k t => ∑ s, c.π k t s * g t s.1) (φ := fun _ _ => 0)
    hgrid.mono hu_cont hu_deriv (fun k _ => intervalIntegrable_const) hnode
  simp only [intervalIntegral.integral_zero, Finset.sum_const_zero, add_zero] at hchain
  rw [hgrid.last] at hchain
  simp only [Dat.CFlow.term]
  rw [hchain, c.is.glued.init, D.killTr_pairing, hgrid.first]
  simp only [initVec, ite_mul, zero_mul, one_mul]
  rw [Finset.sum_ite_eq' Finset.univ ((x₀, x₀, true) : JSt n)
    (fun s => g θ s.1)]
  simp

end Dat

end Talagrand
