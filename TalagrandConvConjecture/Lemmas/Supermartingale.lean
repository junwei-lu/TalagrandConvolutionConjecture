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

/-! ### Generic finite-sum helpers -/

/-- A rate `if`-term with a uniquely determined target collapses. -/
private lemma sum_state_eq {n : ℕ} {P : JSt n → Prop} [DecidablePred P] {τ₀ : JSt n}
    (hP : ∀ τ, P τ ↔ τ = τ₀) (r : ℝ) (f : JSt n → ℝ) :
    ∑ τ : JSt n, (if P τ then r else 0) * f τ = r * f τ₀ := by
  classical
  have key : ∀ τ : JSt n, (if P τ then r else 0) * f τ = if τ = τ₀ then r * f τ₀ else 0 := by
    intro τ
    by_cases hτ : τ = τ₀
    · rw [if_pos hτ, if_pos ((hP τ).mpr hτ), hτ]
    · rw [if_neg hτ, if_neg (fun hc => hτ ((hP τ).mp hc)), zero_mul]
  simp [key]

/-- Transposed action of a forward matrix against a test function is the
backward generator of the rate table. -/
private lemma fwdOf_transpose_pair {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (g : S → ℝ) (σ : S) :
    ∑ s, fwdOf q s σ * g s = ∑ s, q σ s * (g s - g σ) := by
  classical
  have h2 : ∑ s, (if s = σ then ∑ s'', q s s'' else 0) * g s = (∑ s'', q σ s'') * g σ := by
    simp
  simp only [fwdOf, sub_mul, Finset.sum_sub_distrib, h2, mul_sub]
  rw [← Finset.sum_mul]

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

/-! ### Grid bookkeeping -/

/-- Nodes of an admissible grid are monotone up to `K`. -/
private lemma grid_mono {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) :
    ∀ b, b ≤ K → ∀ a, a ≤ b → z a ≤ z b := by
  intro b
  induction b with
  | zero => intro _ a ha; simp only [Nat.le_zero] at ha; simp [ha]
  | succ m ih =>
    intro hm a ha
    rcases Nat.eq_or_lt_of_le ha with h | h
    · exact le_of_eq (by rw [h])
    · exact le_trans (ih (Nat.le_of_succ_le hm) a (Nat.lt_succ_iff.mp h))
        (hg.mono m (Nat.lt_of_succ_le hm))

/-- Grid nodes lie in `[θ, T_o]`. -/
private lemma grid_mem {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k ≤ K) :
    θ ≤ z k ∧ z k ≤ obsT := by
  refine ⟨?_, ?_⟩
  · have := D.grid_mono hg k hk 0 (Nat.zero_le _)
    rwa [hg.first] at this
  · have := D.grid_mono hg K le_rfl k hk
    rwa [hg.last] at this

/-- On a cell of an admissible grid, membership in the cell barrier (sampled
at the midpoint) forces `F_t ≥ ℓ+1` at *every* time of the closed cell: the
barrier is constant on the open cell and `F` is continuous. -/
private lemma cell_barrier_F {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k < K) {t : ℝ}
    (ht : t ∈ Set.Icc (z k) (z (k + 1))) {w : Cube n}
    (hw : w ∈ D.barrier ℓ ((z k + z (k + 1)) / 2)) : ℓ + 1 ≤ D.F t w := by
  have hmono : z k ≤ z (k + 1) := hg.mono k hk
  rcases eq_or_lt_of_le hmono with heq | hlt
  · -- degenerate cell: `t` is the midpoint
    have hteq : t = z k := le_antisymm (by rw [heq]; exact ht.2) ht.1
    have hmid : (z k + z (k + 1)) / 2 = z k := by rw [← heq]; ring
    have hFeq : D.F ((z k + z (k + 1)) / 2) w = D.F t w := by rw [hmid, hteq]
    rw [← hFeq]; exact hw
  · have hmidmem : (z k + z (k + 1)) / 2 ∈ Set.Ioo (z k) (z (k + 1)) :=
      ⟨by linarith, by linarith⟩
    have hopen : ∀ v ∈ Set.Ioo (z k) (z (k + 1)), ℓ + 1 ≤ D.F v w := fun v hv =>
      (D.barrier_const_on_cell hg hk hmidmem hv w).mp hw
    have hsubT : Set.Icc (z k) (z (k + 1)) ⊆ Set.Iic D.T := fun v hv =>
      le_trans (le_trans hv.2 (D.grid_mem hg (Nat.succ_le_of_lt hk)).2) D.obsT_lt_T.le
    have hcont : ContinuousOn (fun v => D.F v w) (Set.Icc (z k) (z (k + 1))) :=
      (D.continuousOn_F w).mono hsubT
    have hcl : IsClosed (Set.Icc (z k) (z (k + 1)) ∩
        (fun v => D.F v w) ⁻¹' Set.Ici (ℓ + 1)) :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Set.Ioo (z k) (z (k + 1)) ⊆
        Set.Icc (z k) (z (k + 1)) ∩ (fun v => D.F v w) ⁻¹' Set.Ici (ℓ + 1) :=
      fun v hv => ⟨⟨hv.1.le, hv.2.le⟩, hopen v hv⟩
    have hcl2 := hcl.closure_subset_iff.2 hsub
    rw [closure_Ioo (ne_of_lt hlt)] at hcl2
    exact (hcl2 ht).2

/-! ### The backward harmonic extension in the `W`-slot -/

/-- Matrix of the reverse generator `L̃_t` acting on functions of the cube. -/
private noncomputable def revMat (t : ℝ) (x x' : Cube n) : ℝ :=
  (∑ i, if x' = flipCoord i x then D.Y t i x / 2 else 0)
    - (if x' = x then ∑ i, D.Y t i x / 2 else 0)

private lemma matVec_revMat (t : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    matVec (D.revMat t) g x = D.revGen t g x := by
  classical
  have h1 : ∑ x' : Cube n, (∑ i, if x' = flipCoord i x then D.Y t i x / 2 else 0) * g x'
      = ∑ i, D.Y t i x / 2 * g (flipCoord i x) := by
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by simp
  have h2 : ∑ x' : Cube n, (if x' = x then ∑ i, D.Y t i x / 2 else 0) * g x'
      = (∑ i, D.Y t i x / 2) * g x := by simp
  simp only [matVec, revMat, sub_mul, Finset.sum_sub_distrib, h1, h2, revGen]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma revMat_offdiag (t : ℝ) (ht : t ≤ D.T) {x x' : Cube n} (hxx : x ≠ x') :
    0 ≤ D.revMat t x x' := by
  classical
  have : (if x' = x then ∑ i, D.Y t i x / 2 else 0) = 0 :=
    if_neg fun hc => hxx hc.symm
  rw [revMat, this, sub_zero]
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hc : x' = flipCoord i x
  · simp only [if_pos hc]; have := (D.Y_pos ht i x).le; linarith
  · simp [hc]

private lemma continuousOn_revMat {θ : ℝ} (hθ : θ ≤ obsT) (r : ℝ → ℝ)
    (hr : ContinuousOn r (Set.Icc θ obsT))
    (hrm : Set.MapsTo r (Set.Icc θ obsT) (Set.Iic D.T)) (x x' : Cube n) :
    ContinuousOn (fun u => D.revMat (r u) x x') (Set.Icc θ obsT) := by
  classical
  have hY : ∀ i : Fin n, ContinuousOn (fun u => D.Y (r u) i x) (Set.Icc θ obsT) :=
    fun i => (D.continuousOn_Y i x).comp hr hrm
  refine ContinuousOn.sub ?_ ?_
  · exact continuousOn_finset_sum _ fun i _ => by
      by_cases hc : x' = flipCoord i x
      · simpa [hc] using (hY i).div_const 2
      · simpa [hc] using continuousOn_const
  · by_cases hc : x' = x
    · simpa [hc] using continuousOn_finset_sum _ fun i _ => (hY i).div_const 2
    · simpa [hc] using continuousOn_const

/-- Backward harmonic extension of a nonnegative terminal test `h` for the
reverse dynamics: `∂_t H_t = -L̃_t H_t` on `[θ, T_o]`, `H_{T_o} = h`, `H ≥ 0`.
Obtained from `exists_linFlow` for the time-reversed generator. -/
private lemma exists_bwdExt {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (h : Cube n → ℝ) (hh : ∀ w, 0 ≤ h w) :
    ∃ H : ℝ → Cube n → ℝ,
      (∀ x, ContinuousOn (fun t => H t x) (Set.Icc θ obsT)) ∧
      (∀ x, ∀ t ∈ Set.Icc θ obsT,
        HasDerivWithinAt (fun t => H t x) (-(D.revGen t (H t) x)) (Set.Icc θ obsT) t) ∧
      H obsT = h ∧ (∀ t ∈ Set.Icc θ obsT, ∀ x, 0 ≤ H t x) := by
  classical
  have hTo : obsT ≤ D.T := D.obsT_lt_T.le
  set r : ℝ → ℝ := fun u => θ + obsT - u with hr_def
  have hrc : ContinuousOn r (Set.Icc θ obsT) := (continuous_const.sub continuous_id).continuousOn
  have hrmaps : Set.MapsTo r (Set.Icc θ obsT) (Set.Icc θ obsT) := by
    rintro u ⟨h1, h2⟩; exact ⟨by simp [hr_def]; linarith, by simp [hr_def]; linarith⟩
  have hrT : Set.MapsTo r (Set.Icc θ obsT) (Set.Iic D.T) := fun u hu =>
    le_trans (hrmaps hu).2 hTo
  obtain ⟨G, hG, hG0⟩ :=
    exists_linFlow (fun u => D.revMat (r u)) hθ
      (fun x x' => D.continuousOn_revMat hθ r hrc hrT x x') h
  have hGnn : ∀ u ∈ Set.Icc θ obsT, ∀ x, 0 ≤ G u x := by
    refine linFlow_nonneg hθ (fun x x' => D.continuousOn_revMat hθ r hrc hrT x x')
      ?_ hG ?_
    · intro u hu x x' hxx
      exact D.revMat_offdiag (r u) (hrT hu) hxx
    · intro x; rw [hG0]; exact hh x
  refine ⟨fun t => G (r t), fun x => ?_, fun x t ht => ?_, ?_, fun t ht x => hGnn _ (hrmaps ht) x⟩
  · exact ((hG.cont x).comp hrc hrmaps)
  · have hrt : HasDerivWithinAt r (-1) (Set.Icc θ obsT) t := by
      simpa [hr_def] using
        ((hasDerivAt_const t (θ + obsT)).sub (hasDerivAt_id t)).hasDerivWithinAt
    have hcomp := (hG.deriv x (r t) (hrmaps ht)).comp t hrt hrmaps
    have hrr : r (r t) = t := by simp only [hr_def]; ring
    have : matVec (D.revMat (r (r t))) (G (r t)) x = D.revGen t (fun w => G (r t) w) x := by
      rw [hrr]; exact D.matVec_revMat t _ x
    simpa [Function.comp, this] using hcomp
  · funext x; simp [hr_def, hG0]

/-! ### Elementary properties of the weight `NW` -/

private lemma NW_true (ℓ θ : ℝ) (x₀ : Cube n) (t : ℝ) (x y : Cube n) :
    D.NW ℓ θ x₀ t (x, y, true)
      = Real.exp (D.F t y - (1 - D.dbar ℓ θ x₀) * D.F t x
          - D.dbar ℓ θ x₀ * D.F θ x₀) := rfl

private lemma NW_false (ℓ θ : ℝ) (x₀ : Cube n) (t : ℝ) (x y : Cube n) :
    D.NW ℓ θ x₀ t (x, y, false)
      = Real.exp (D.F t y - D.F t x + D.dbar ℓ θ x₀ * (ℓ + 1 - D.F θ x₀)) := rfl

private lemma NW_pos (ℓ θ : ℝ) (x₀ : Cube n) (t : ℝ) (s : JSt n) :
    0 < D.NW ℓ θ x₀ t s := by
  rw [NW]; split <;> exact Real.exp_pos _

/-- Passing from the alive to the dead sector multiplies the weight by
`e^{δ̄(ℓ+1-F_t(x))}`. -/
private lemma NW_false_eq (ℓ θ : ℝ) (x₀ : Cube n) (t : ℝ) (x y : Cube n) :
    D.NW ℓ θ x₀ t (x, y, false)
      = D.NW ℓ θ x₀ t (x, y, true)
        * Real.exp (D.dbar ℓ θ x₀ * (ℓ + 1 - D.F t x)) := by
  rw [D.NW_true, D.NW_false, ← Real.exp_add]; congr 1; ring

private lemma F_flip_eq {t : ℝ} (ht : t ≤ D.T) (i : Fin n) (x : Cube n) :
    D.F t (flipCoord i x) = D.F t x + Real.log (D.Y t i x) := by
  have := D.F_flipCoord_sub_of_le ht i x; linarith

/-- Synchronized flip, alive landing: the weight ratio is `X_i·Y_i^{δ̄-1}`. -/
private lemma NW_flip_both (ℓ θ : ℝ) (x₀ : Cube n) {t : ℝ} (ht : t ≤ D.T)
    (i : Fin n) (x y : Cube n) :
    D.NW ℓ θ x₀ t (flipCoord i x, flipCoord i y, true)
      = D.NW ℓ θ x₀ t (x, y, true)
        * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1)) := by
  have hX : 0 < D.Y t i y := D.Y_pos ht i y
  have hY : 0 < D.Y t i x := D.Y_pos ht i x
  have hc : D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1)
      = Real.exp (Real.log (D.Y t i y)
          + Real.log (D.Y t i x) * (D.dbar ℓ θ x₀ - 1)) := by
    rw [Real.exp_add, Real.exp_log hX, Real.rpow_def_of_pos hY]
  rw [D.NW_true, D.NW_true, hc, ← Real.exp_add]
  congr 1
  rw [D.F_flip_eq ht i x, D.F_flip_eq ht i y]; ring

/-- `W`-only flip: the weight ratio is `X_i`. -/
private lemma NW_flip_W (ℓ θ : ℝ) (x₀ : Cube n) {t : ℝ} (ht : t ≤ D.T)
    (i : Fin n) (x y : Cube n) :
    D.NW ℓ θ x₀ t (x, flipCoord i y, true)
      = D.NW ℓ θ x₀ t (x, y, true) * D.Y t i y := by
  have hX : 0 < D.Y t i y := D.Y_pos ht i y
  rw [D.NW_true, D.NW_true, ← Real.exp_log hX, ← Real.exp_add]
  congr 1
  rw [D.F_flip_eq ht i y]; ring

/-- `V`-only flip, alive landing: the weight ratio is `Y_i^{δ̄-1}`. -/
private lemma NW_flip_V (ℓ θ : ℝ) (x₀ : Cube n) {t : ℝ} (ht : t ≤ D.T)
    (i : Fin n) (x y : Cube n) :
    D.NW ℓ θ x₀ t (flipCoord i x, y, true)
      = D.NW ℓ θ x₀ t (x, y, true) * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) := by
  have hY : 0 < D.Y t i x := D.Y_pos ht i x
  rw [D.NW_true, D.NW_true, Real.rpow_def_of_pos hY, ← Real.exp_add]
  congr 1
  rw [D.F_flip_eq ht i x]; ring

/-- Synchronized flip out of the dead sector: the weight ratio is `X_i/Y_i`. -/
private lemma NW_flip_both_dead (ℓ θ : ℝ) (x₀ : Cube n) {t : ℝ} (ht : t ≤ D.T)
    (i : Fin n) (x y : Cube n) :
    D.NW ℓ θ x₀ t (flipCoord i x, flipCoord i y, false)
      = D.NW ℓ θ x₀ t (x, y, false) * (D.Y t i y / D.Y t i x) := by
  have hX : 0 < D.Y t i y := D.Y_pos ht i y
  have hY : 0 < D.Y t i x := D.Y_pos ht i x
  have hc : D.Y t i y / D.Y t i x
      = Real.exp (Real.log (D.Y t i y) - Real.log (D.Y t i x)) := by
    rw [Real.exp_sub, Real.exp_log hX, Real.exp_log hY]
  rw [D.NW_false, D.NW_false, hc, ← Real.exp_add]
  congr 1
  rw [D.F_flip_eq ht i x, D.F_flip_eq ht i y]; ring

/-! ### Time derivative of the weight -/

/-- `∂_t N_t(s) = N_t(s)·(∑_i S_i(t,W) - c_s·∑_i S_i(t,V))` with `c_s = 1-δ̄`
on the alive sector and `c_s = 1` on the dead sector (use `∂_t F_t = ∑_i S_i`,
[LGF eq (3.8)]). -/
private lemma hasDerivAt_NW (ℓ θ : ℝ) (x₀ : Cube n) {t : ℝ} (ht : t ≤ D.T)
    (s : JSt n) :
    HasDerivAt (fun t => D.NW ℓ θ x₀ t s)
      (D.NW ℓ θ x₀ t s * ((∑ i, D.Sc t i s.2.1)
        - (if s.2.2 then 1 - D.dbar ℓ θ x₀ else 1) * (∑ i, D.Sc t i s.1))) t := by
  obtain ⟨x, y, b⟩ := s
  have hFx := D.hasDerivAt_F ht x
  have hFy := D.hasDerivAt_F ht y
  cases b with
  | false =>
    have hif : (if ((x, y, false) : JSt n).2.2 then 1 - D.dbar ℓ θ x₀ else (1 : ℝ))
        = 1 := by simp
    rw [hif, one_mul]
    exact ((hFy.sub hFx).add_const (D.dbar ℓ θ x₀ * (ℓ + 1 - D.F θ x₀))).exp
  | true =>
    have hif : (if ((x, y, true) : JSt n).2.2 then 1 - D.dbar ℓ θ x₀ else (1 : ℝ))
        = 1 - D.dbar ℓ θ x₀ := by simp
    rw [hif]
    exact ((hFy.sub (hFx.const_mul (1 - D.dbar ℓ θ x₀))).sub_const
      (D.dbar ℓ θ x₀ * D.F θ x₀)).exp

private lemma continuousOn_NW (ℓ θ : ℝ) (x₀ : Cube n) {a b : ℝ} (hbT : b ≤ D.T)
    (s : JSt n) : ContinuousOn (fun t => D.NW ℓ θ x₀ t s) (Set.Icc a b) :=
  fun t ht =>
    (D.hasDerivAt_NW ℓ θ x₀ (le_trans ht.2 hbT) s).continuousAt.continuousWithinAt

/-! ### The node transfers decrease the weighted pairing -/

open Classical in
/-- Killing a state (alive → dead) at a time when it sits on the barrier does
not increase the weight: the ratio is `e^{δ̄(ℓ+1-F_t)} ≤ 1`. -/
private lemma NW_kill_le (ℓ θ : ℝ) (x₀ : Cube n) (t : ℝ) (x y : Cube n) (b : Bool) :
    D.NW ℓ θ x₀ t (x, y, (b && decide (x ∉ D.barrier ℓ t)))
      ≤ D.NW ℓ θ x₀ t (x, y, b) := by
  classical
  by_cases hx : x ∈ D.barrier ℓ t
  · have hdec : decide (x ∉ D.barrier ℓ t) = false := by simp [hx]
    rw [hdec, Bool.and_false]
    cases b with
    | false => exact le_rfl
    | true =>
      have hxF : ℓ + 1 ≤ D.F t x := hx
      have hdd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
      have hex : Real.exp (D.dbar ℓ θ x₀ * (ℓ + 1 - D.F t x)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      rw [D.NW_false_eq]
      exact mul_le_of_le_one_right (D.NW_pos ℓ θ x₀ t (x, y, true)).le hex
  · have hdec : decide (x ∉ D.barrier ℓ t) = true := by simp [hx]
    rw [hdec, Bool.and_true]

private lemma initVec_nonneg' (x₀ : Cube n) (s : JSt n) : 0 ≤ initVec x₀ s := by
  classical
  simp only [initVec]
  split_ifs <;> norm_num

/-- A node transfer does not increase the `N`-weighted pairing against a
nonnegative, `V`-blind test. -/
private lemma killTr_pairing_le (ℓ θ : ℝ) (x₀ : Cube n) (t : ℝ) {Hf : Cube n → ℝ}
    (hHf : ∀ w, 0 ≤ Hf w) {v : JSt n → ℝ} (hv : ∀ s, 0 ≤ v s) :
    ∑ s, matVec (D.killTr ℓ t) v s * (D.NW ℓ θ x₀ t s * Hf s.2.1)
      ≤ ∑ s, v s * (D.NW ℓ θ x₀ t s * Hf s.2.1) := by
  classical
  have hexp : ∑ s : JSt n, matVec (D.killTr ℓ t) v s * (D.NW ℓ θ x₀ t s * Hf s.2.1)
      = ∑ σ : JSt n, v σ *
          (D.NW ℓ θ x₀ t (σ.1, σ.2.1, (σ.2.2 && decide (σ.1 ∉ D.barrier ℓ t)))
            * Hf σ.2.1) := by
    simp only [matVec, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have key : ∀ s : JSt n, D.killTr ℓ t s σ * v σ * (D.NW ℓ θ x₀ t s * Hf s.2.1)
        = if s = (σ.1, σ.2.1, (σ.2.2 && decide (σ.1 ∉ D.barrier ℓ t))) then
            v σ * (D.NW ℓ θ x₀ t (σ.1, σ.2.1, (σ.2.2 && decide (σ.1 ∉ D.barrier ℓ t)))
              * Hf σ.2.1)
          else 0 := by
      intro s
      have hk : D.killTr ℓ t s σ
          = if s = (σ.1, σ.2.1, (σ.2.2 && decide (σ.1 ∉ D.barrier ℓ t))) then 1
            else 0 := by
        obtain ⟨x, y, b⟩ := s
        obtain ⟨x', y', b'⟩ := σ
        simp only [killTr, Prod.mk.injEq]
      rw [hk]
      by_cases hs : s = ((σ.1, σ.2.1, (σ.2.2 && decide (σ.1 ∉ D.barrier ℓ t))) : JSt n)
      · rw [if_pos hs, if_pos hs, hs]; simp
      · rw [if_neg hs, if_neg hs, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl fun s _ => key s]
    simp
  rw [hexp]
  refine Finset.sum_le_sum fun σ _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (hv σ)
  exact mul_le_mul_of_nonneg_right
    (D.NW_kill_le ℓ θ x₀ t σ.1 σ.2.1 σ.2.2) (hHf σ.2.1)

/-! ### Expansion of the jump-rate pairing -/

open Classical in
private lemma jrate_apply (dd : ℝ) (B : Set (Cube n)) (t : ℝ)
    (x y : Cube n) (b : Bool) (τ : JSt n) :
    D.jrate dd B t (x, y, b) τ
      = ∑ i : Fin n,
        ((if τ.1 = flipCoord i x ∧ τ.2.1 = flipCoord i y ∧
              (τ.2.2 = (b && decide (τ.1 ∉ B))) then
            (if b then
              (if D.Y t i x < 1 then D.Y t i x / 2
               else D.Y t i x ^ (1 - dd) / 2)
             else D.Y t i x / 2)
          else 0)
        + (if b ∧ τ.2.2 = true ∧ τ.1 = x ∧ τ.2.1 = flipCoord i y ∧ D.Y t i x < 1 then
            (1 - D.Y t i x ^ dd) / 2
          else 0)
        + (if b ∧ τ.2.1 = y ∧ τ.1 = flipCoord i x ∧ ¬(D.Y t i x < 1) ∧
              (τ.2.2 = decide (τ.1 ∉ B)) then
            (D.Y t i x - D.Y t i x ^ (1 - dd)) / 2
          else 0)) := by
  obtain ⟨x', y', b'⟩ := τ; rfl

open Classical in
/-- Alive-sector jump pairing, expanded coordinate by coordinate. -/
private lemma jrate_pair_true (dd : ℝ) (B : Set (Cube n)) (t : ℝ)
    (x y : Cube n) (f : JSt n → ℝ) :
    ∑ τ : JSt n, D.jrate dd B t (x, y, true) τ * f τ
      = ∑ i : Fin n,
        ((if D.Y t i x < 1 then D.Y t i x / 2 else D.Y t i x ^ (1 - dd) / 2)
            * f (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))
        + (if D.Y t i x < 1 then (1 - D.Y t i x ^ dd) / 2 else 0)
            * f (x, flipCoord i y, true)
        + (if D.Y t i x < 1 then 0 else (D.Y t i x - D.Y t i x ^ (1 - dd)) / 2)
            * f (flipCoord i x, y, decide (flipCoord i x ∉ B))) := by
  simp_rw [D.jrate_apply dd B t x y true, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine sum_state_eq
      (P := fun τ : JSt n => τ.1 = flipCoord i x ∧ τ.2.1 = flipCoord i y ∧
        (τ.2.2 = (true && decide (τ.1 ∉ B))))
      (τ₀ := (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))) ?_ _ _
    intro τ
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [h1, Bool.true_and] at h3
      exact Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, h3⟩⟩
    · rintro rfl; exact ⟨rfl, rfl, by simp⟩
  · by_cases hY : D.Y t i x < 1
    · rw [if_pos hY]
      refine sum_state_eq
        (P := fun τ : JSt n => True ∧ τ.2.2 = true ∧ τ.1 = x ∧
          τ.2.1 = flipCoord i y ∧ D.Y t i x < 1)
        (τ₀ := (x, flipCoord i y, true)) ?_ _ _
      intro τ
      constructor
      · rintro ⟨-, h2, h3, h4, -⟩
        exact Prod.ext_iff.mpr ⟨h3, Prod.ext_iff.mpr ⟨h4, h2⟩⟩
      · rintro rfl; exact ⟨trivial, rfl, rfl, rfl, hY⟩
    · rw [if_neg hY, zero_mul]
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [if_neg (fun hc => hY hc.2.2.2.2), zero_mul]
  · by_cases hY : D.Y t i x < 1
    · rw [if_pos hY, zero_mul]
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [if_neg (fun hc => hc.2.2.2.1 hY), zero_mul]
    · rw [if_neg hY]
      refine sum_state_eq
        (P := fun τ : JSt n => True ∧ τ.2.1 = y ∧ τ.1 = flipCoord i x ∧
          ¬(D.Y t i x < 1) ∧ (τ.2.2 = decide (τ.1 ∉ B)))
        (τ₀ := (flipCoord i x, y, decide (flipCoord i x ∉ B))) ?_ _ _
      intro τ
      constructor
      · rintro ⟨-, h2, h3, -, h5⟩
        rw [h3] at h5
        exact Prod.ext_iff.mpr ⟨h3, Prod.ext_iff.mpr ⟨h2, h5⟩⟩
      · rintro rfl; exact ⟨trivial, rfl, rfl, hY, rfl⟩

open Classical in
/-- Dead-sector jump pairing: synchronized flips only. -/
private lemma jrate_pair_false (dd : ℝ) (B : Set (Cube n)) (t : ℝ)
    (x y : Cube n) (f : JSt n → ℝ) :
    ∑ τ : JSt n, D.jrate dd B t (x, y, false) τ * f τ
      = ∑ i : Fin n, D.Y t i x / 2 * f (flipCoord i x, flipCoord i y, false) := by
  simp_rw [D.jrate_apply dd B t x y false, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h2 : ∑ τ : JSt n,
      (if (false : Bool) ∧ τ.2.2 = true ∧ τ.1 = x ∧ τ.2.1 = flipCoord i y ∧
          D.Y t i x < 1 then (1 - D.Y t i x ^ dd) / 2 else 0) * f τ = 0 := by
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [if_neg (by rintro ⟨h, -⟩; exact Bool.noConfusion h), zero_mul]
  have h3 : ∑ τ : JSt n,
      (if (false : Bool) ∧ τ.2.1 = y ∧ τ.1 = flipCoord i x ∧ ¬(D.Y t i x < 1) ∧
          (τ.2.2 = decide (τ.1 ∉ B)) then
        (D.Y t i x - D.Y t i x ^ (1 - dd)) / 2 else 0) * f τ = 0 := by
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [if_neg (by rintro ⟨h, -⟩; exact Bool.noConfusion h), zero_mul]
  rw [h2, h3, add_zero, add_zero]
  refine sum_state_eq
    (P := fun τ : JSt n => τ.1 = flipCoord i x ∧ τ.2.1 = flipCoord i y ∧
      (τ.2.2 = ((false : Bool) && decide (τ.1 ∉ B))))
    (τ₀ := (flipCoord i x, flipCoord i y, false)) ?_ _ _
  intro τ
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [Bool.false_and] at h3
    exact Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, h3⟩⟩
  · rintro rfl; exact ⟨rfl, rfl, by simp⟩

/-! ### The pointwise cell inequality [LGF, proof of Prop 4.1] -/

private lemma sum_regroup {m : ℕ} (Q a c : ℝ) (F u v w : Fin m → ℝ) :
    (∑ i, F i) + (Q * ((∑ i, u i) - c * (∑ i, v i)) * a + Q * (-(∑ i, w i)))
      = ∑ i, (F i + Q * (u i - c * v i) * a + Q * (-(w i))) := by
  have e0 : ∑ i, (u i - c * v i) = (∑ i, u i) - c * (∑ i, v i) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have e1 : Q * ((∑ i, u i) - c * (∑ i, v i)) * a = ∑ i, Q * (u i - c * v i) * a := by
    rw [← e0, Finset.mul_sum, Finset.sum_mul]
  have e2 : Q * (-(∑ i, w i)) = ∑ i, Q * (-(w i)) := by
    simp [Finset.mul_sum]
  rw [e1, e2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Dead sector: the weighted pairing has exactly zero drift. -/
private lemma bracket_dead {ℓ θ : ℝ} {x₀ : Cube n} {B : Set (Cube n)} {t : ℝ}
    (ht : t ≤ D.T) {Hf : Cube n → ℝ} (x y : Cube n) :
    (∑ τ : JSt n, D.jrate (D.dbar ℓ θ x₀) B t (x, y, false) τ *
        (D.NW ℓ θ x₀ t τ * Hf τ.2.1 - D.NW ℓ θ x₀ t (x, y, false) * Hf y))
      + (D.NW ℓ θ x₀ t (x, y, false) * ((∑ i, D.Sc t i y)
            - 1 * (∑ i, D.Sc t i x)) * Hf y
         + D.NW ℓ θ x₀ t (x, y, false) * (-(D.revGen t Hf y))) = 0 := by
  rw [D.jrate_pair_false, revGen, sum_regroup]
  refine Finset.sum_eq_zero fun i _ => ?_
  show D.Y t i x / 2 * (D.NW ℓ θ x₀ t (flipCoord i x, flipCoord i y, false) * Hf (flipCoord i y)
        - D.NW ℓ θ x₀ t (x, y, false) * Hf y)
      + D.NW ℓ θ x₀ t (x, y, false) * (D.Sc t i y - 1 * D.Sc t i x) * Hf y
      + D.NW ℓ θ x₀ t (x, y, false) * (-(D.Y t i y * (Hf (flipCoord i y) - Hf y) / 2)) = 0
  rw [D.NW_flip_both_dead ℓ θ x₀ ht i x y]
  have hY : D.Y t i x ≠ 0 := (D.Y_pos ht i x).ne'
  simp only [Sc]
  field_simp
  ring

/-- Alive sector: the weighted pairing drifts down by the AM–GM defect. -/
private lemma bracket_alive {ℓ θ : ℝ} {x₀ : Cube n} {B : Set (Cube n)} {t : ℝ}
    (ht : t ≤ D.T) (hB : ∀ w : Cube n, w ∈ B → ℓ + 1 ≤ D.F t w)
    {Hf : Cube n → ℝ} (hHnn : ∀ w, 0 ≤ Hf w) (x y : Cube n) :
    (∑ τ : JSt n, D.jrate (D.dbar ℓ θ x₀) B t (x, y, true) τ *
        (D.NW ℓ θ x₀ t τ * Hf τ.2.1 - D.NW ℓ θ x₀ t (x, y, true) * Hf y))
      + (D.NW ℓ θ x₀ t (x, y, true) * ((∑ i, D.Sc t i y)
            - (1 - D.dbar ℓ θ x₀) * (∑ i, D.Sc t i x)) * Hf y
         + D.NW ℓ θ x₀ t (x, y, true) * (-(D.revGen t Hf y))) ≤ 0 := by
  classical
  have hdd0 : 0 ≤ D.dbar ℓ θ x₀ := D.dbar_nonneg ℓ θ x₀
  have hdd1 : D.dbar ℓ θ x₀ ≤ 1 :=
    le_of_lt (lt_trans (D.dbar_lt_half ℓ θ x₀) (by norm_num))
  -- Step 1: bound the jump part coordinatewise.
  have hjump : (∑ τ : JSt n, D.jrate (D.dbar ℓ θ x₀) B t (x, y, true) τ *
        (D.NW ℓ θ x₀ t τ * Hf τ.2.1 - D.NW ℓ θ x₀ t (x, y, true) * Hf y))
      ≤ ∑ i : Fin n, D.NW ℓ θ x₀ t (x, y, true) *
          (D.Y t i y / 2 * Hf (flipCoord i y)
            - (1 + D.Y t i x - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 * Hf y) := by
    rw [D.jrate_pair_true]
    refine Finset.sum_le_sum fun i _ => ?_
    have hYi : 0 < D.Y t i x := D.Y_pos ht i x
    have hXi : 0 < D.Y t i y := D.Y_pos ht i y
    have hWp : 0 < D.NW ℓ θ x₀ t (x, y, true) := D.NW_pos ℓ θ x₀ t _
    have hqp : 0 < D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) := Real.rpow_pos_of_pos hYi _
    have hay : 0 ≤ Hf y := hHnn y
    have hay' : 0 ≤ Hf (flipCoord i y) := hHnn _
    have hpq : D.Y t i x * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1)
        = D.Y t i x ^ D.dbar ℓ θ x₀ := by
      have hh := Real.rpow_add hYi 1 (D.dbar ℓ θ x₀ - 1)
      rw [Real.rpow_one] at hh
      rw [show (1 : ℝ) + (D.dbar ℓ θ x₀ - 1) = D.dbar ℓ θ x₀ by ring] at hh
      exact hh.symm
    have hrq : D.Y t i x ^ (1 - D.dbar ℓ θ x₀) * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) = 1 := by
      rw [← Real.rpow_add hYi,
        show (1 - D.dbar ℓ θ x₀) + (D.dbar ℓ θ x₀ - 1) = (0 : ℝ) by ring, Real.rpow_zero]
    -- landing bounds (dead landings are dominated by their alive forms)
    have hT1 : D.NW ℓ θ x₀ t (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))
          * Hf (flipCoord i y)
        ≤ D.NW ℓ θ x₀ t (x, y, true) * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1))
          * Hf (flipCoord i y) := by
      by_cases hmem : flipCoord i x ∈ B
      · rw [decide_eq_false (not_not_intro hmem)]
        have hex : Real.exp (D.dbar ℓ θ x₀ * (ℓ + 1 - D.F t (flipCoord i x))) ≤ 1 := by
          refine Real.exp_le_one_iff.mpr ?_
          have := hB _ hmem
          nlinarith
        have hpos : 0 ≤ D.NW ℓ θ x₀ t (x, y, true)
            * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1)) * Hf (flipCoord i y) := by
          have : 0 < D.NW ℓ θ x₀ t (x, y, true)
              * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1)) := by positivity
          exact mul_nonneg this.le hay'
        calc D.NW ℓ θ x₀ t (flipCoord i x, flipCoord i y, false) * Hf (flipCoord i y)
            = (D.NW ℓ θ x₀ t (x, y, true)
                * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1)) * Hf (flipCoord i y))
              * Real.exp (D.dbar ℓ θ x₀ * (ℓ + 1 - D.F t (flipCoord i x))) := by
              rw [D.NW_false_eq ℓ θ x₀ t (flipCoord i x) (flipCoord i y),
                D.NW_flip_both ℓ θ x₀ ht i x y]; ring
          _ ≤ (D.NW ℓ θ x₀ t (x, y, true)
                * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1)) * Hf (flipCoord i y)) * 1 :=
              mul_le_mul_of_nonneg_left hex hpos
          _ = _ := mul_one _
      · rw [decide_eq_true hmem, D.NW_flip_both ℓ θ x₀ ht i x y]
    have hT3 : D.NW ℓ θ x₀ t (flipCoord i x, y, decide (flipCoord i x ∉ B)) * Hf y
        ≤ D.NW ℓ θ x₀ t (x, y, true) * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) * Hf y := by
      by_cases hmem : flipCoord i x ∈ B
      · rw [decide_eq_false (not_not_intro hmem)]
        have hex : Real.exp (D.dbar ℓ θ x₀ * (ℓ + 1 - D.F t (flipCoord i x))) ≤ 1 := by
          refine Real.exp_le_one_iff.mpr ?_
          have := hB _ hmem
          nlinarith
        have hpos : 0 ≤ D.NW ℓ θ x₀ t (x, y, true)
            * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) * Hf y := by
          have : 0 < D.NW ℓ θ x₀ t (x, y, true) * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) := by
            positivity
          exact mul_nonneg this.le hay
        calc D.NW ℓ θ x₀ t (flipCoord i x, y, false) * Hf y
            = (D.NW ℓ θ x₀ t (x, y, true) * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) * Hf y)
              * Real.exp (D.dbar ℓ θ x₀ * (ℓ + 1 - D.F t (flipCoord i x))) := by
              rw [D.NW_false_eq ℓ θ x₀ t (flipCoord i x) y,
                D.NW_flip_V ℓ θ x₀ ht i x y]; ring
          _ ≤ (D.NW ℓ θ x₀ t (x, y, true) * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) * Hf y) * 1 :=
              mul_le_mul_of_nonneg_left hex hpos
          _ = _ := mul_one _
      · rw [decide_eq_true hmem, D.NW_flip_V ℓ θ x₀ ht i x y]
    have hT2 : D.NW ℓ θ x₀ t (x, flipCoord i y, true)
        = D.NW ℓ θ x₀ t (x, y, true) * D.Y t i y := D.NW_flip_W ℓ θ x₀ ht i x y
    show (if D.Y t i x < 1 then D.Y t i x / 2
            else D.Y t i x ^ (1 - D.dbar ℓ θ x₀) / 2)
          * (D.NW ℓ θ x₀ t (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))
              * Hf (flipCoord i y) - D.NW ℓ θ x₀ t (x, y, true) * Hf y)
        + (if D.Y t i x < 1 then (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 else 0)
          * (D.NW ℓ θ x₀ t (x, flipCoord i y, true) * Hf (flipCoord i y)
              - D.NW ℓ θ x₀ t (x, y, true) * Hf y)
        + (if D.Y t i x < 1 then 0
            else (D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2)
          * (D.NW ℓ θ x₀ t (flipCoord i x, y, decide (flipCoord i x ∉ B)) * Hf y
              - D.NW ℓ θ x₀ t (x, y, true) * Hf y)
        ≤ _
    by_cases hY1 : D.Y t i x < 1
    · rw [if_pos hY1, if_pos hY1, if_pos hY1, hT2]
      have hR1 : (0 : ℝ) ≤ D.Y t i x / 2 := by linarith
      have hstep := mul_le_mul_of_nonneg_left
        (show D.NW ℓ θ x₀ t (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))
              * Hf (flipCoord i y) - D.NW ℓ θ x₀ t (x, y, true) * Hf y
            ≤ D.NW ℓ θ x₀ t (x, y, true) * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1))
              * Hf (flipCoord i y) - D.NW ℓ θ x₀ t (x, y, true) * Hf y by linarith) hR1
      have hid : D.Y t i x / 2 *
            (D.NW ℓ θ x₀ t (x, y, true) * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1))
              * Hf (flipCoord i y) - D.NW ℓ θ x₀ t (x, y, true) * Hf y)
          + (1 - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 *
            (D.NW ℓ θ x₀ t (x, y, true) * D.Y t i y * Hf (flipCoord i y)
              - D.NW ℓ θ x₀ t (x, y, true) * Hf y)
          + 0 * (D.NW ℓ θ x₀ t (flipCoord i x, y, decide (flipCoord i x ∉ B)) * Hf y
              - D.NW ℓ θ x₀ t (x, y, true) * Hf y)
          = D.NW ℓ θ x₀ t (x, y, true) *
            (D.Y t i y / 2 * Hf (flipCoord i y)
              - (1 + D.Y t i x - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 * Hf y) := by
        rw [← hpq]; ring
      linarith [hstep, hid]
    · rw [if_neg hY1, if_neg hY1, if_neg hY1, hT2]
      have hR1 : (0 : ℝ) ≤ D.Y t i x ^ (1 - D.dbar ℓ θ x₀) / 2 :=
        le_of_lt (by positivity)
      have hR3 : (0 : ℝ) ≤ (D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2 := by
        have h1 : (1 : ℝ) ≤ D.Y t i x := not_lt.mp hY1
        have := Real.rpow_le_rpow_of_exponent_le h1
          (show 1 - D.dbar ℓ θ x₀ ≤ (1 : ℝ) by linarith)
        rw [Real.rpow_one] at this
        linarith
      have hstep1 := mul_le_mul_of_nonneg_left
        (show D.NW ℓ θ x₀ t (flipCoord i x, flipCoord i y, decide (flipCoord i x ∉ B))
              * Hf (flipCoord i y) - D.NW ℓ θ x₀ t (x, y, true) * Hf y
            ≤ D.NW ℓ θ x₀ t (x, y, true) * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1))
              * Hf (flipCoord i y) - D.NW ℓ θ x₀ t (x, y, true) * Hf y by linarith) hR1
      have hstep3 := mul_le_mul_of_nonneg_left
        (show D.NW ℓ θ x₀ t (flipCoord i x, y, decide (flipCoord i x ∉ B)) * Hf y
              - D.NW ℓ θ x₀ t (x, y, true) * Hf y
            ≤ D.NW ℓ θ x₀ t (x, y, true) * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) * Hf y
              - D.NW ℓ θ x₀ t (x, y, true) * Hf y by linarith) hR3
      have hid : D.Y t i x ^ (1 - D.dbar ℓ θ x₀) / 2 *
            (D.NW ℓ θ x₀ t (x, y, true) * (D.Y t i y * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1))
              * Hf (flipCoord i y) - D.NW ℓ θ x₀ t (x, y, true) * Hf y)
          + 0 * (D.NW ℓ θ x₀ t (x, y, true) * D.Y t i y * Hf (flipCoord i y)
              - D.NW ℓ θ x₀ t (x, y, true) * Hf y)
          + (D.Y t i x - D.Y t i x ^ (1 - D.dbar ℓ θ x₀)) / 2 *
            (D.NW ℓ θ x₀ t (x, y, true) * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) * Hf y
              - D.NW ℓ θ x₀ t (x, y, true) * Hf y)
          = D.NW ℓ θ x₀ t (x, y, true) *
            (D.Y t i y / 2 * Hf (flipCoord i y)
              - (1 + D.Y t i x - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 * Hf y) := by
        linear_combination (D.NW ℓ θ x₀ t (x, y, true) * D.Y t i y * Hf (flipCoord i y) / 2
            - D.NW ℓ θ x₀ t (x, y, true) * Hf y / 2) * hrq
          + (D.NW ℓ θ x₀ t (x, y, true) * Hf y / 2) * hpq
      linarith [hstep1, hstep3, hid]
  -- Step 2: regroup and apply AM–GM coordinatewise.
  refine le_trans (add_le_add hjump le_rfl) ?_
  rw [revGen, sum_regroup]
  refine Finset.sum_nonpos fun i _ => ?_
  have hYi : 0 < D.Y t i x := D.Y_pos ht i x
  have hWp : 0 < D.NW ℓ θ x₀ t (x, y, true) := D.NW_pos ℓ θ x₀ t _
  have hay : 0 ≤ Hf y := hHnn y
  have hAM := rpow_le_one_sub_add_mul hYi hdd0 hdd1
  show D.NW ℓ θ x₀ t (x, y, true) *
        (D.Y t i y / 2 * Hf (flipCoord i y)
          - (1 + D.Y t i x - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 * Hf y)
      + D.NW ℓ θ x₀ t (x, y, true) *
        (D.Sc t i y - (1 - D.dbar ℓ θ x₀) * D.Sc t i x) * Hf y
      + D.NW ℓ θ x₀ t (x, y, true) *
        (-(D.Y t i y * (Hf (flipCoord i y) - Hf y) / 2)) ≤ 0
  have hkey : D.NW ℓ θ x₀ t (x, y, true) *
        (D.Y t i y / 2 * Hf (flipCoord i y)
          - (1 + D.Y t i x - D.Y t i x ^ D.dbar ℓ θ x₀) / 2 * Hf y)
      + D.NW ℓ θ x₀ t (x, y, true) *
        (D.Sc t i y - (1 - D.dbar ℓ θ x₀) * D.Sc t i x) * Hf y
      + D.NW ℓ θ x₀ t (x, y, true) *
        (-(D.Y t i y * (Hf (flipCoord i y) - Hf y) / 2))
      = D.NW ℓ θ x₀ t (x, y, true) * Hf y *
        ((D.Y t i x ^ D.dbar ℓ θ x₀ - (1 - D.dbar ℓ θ x₀)
          - D.dbar ℓ θ x₀ * D.Y t i x) / 2) := by
    simp only [Sc]; ring
  rw [hkey]
  have h1 : D.Y t i x ^ D.dbar ℓ θ x₀ - (1 - D.dbar ℓ θ x₀)
      - D.dbar ℓ θ x₀ * D.Y t i x ≤ 0 := by linarith
  nlinarith [mul_nonneg hWp.le hay]

/-- **Weighted terminal comparison** [LGF Prop 4.1, `N`-weighted form]:
for every nonnegative terminal test `h` and every starting point,
`𝔼_{x₀}[N_{T_o}·h(W_{T_o})] ≤ 𝔼_{x₀}[h(V_{T_o})]`. -/
theorem weighted_comparison {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) (h : Cube n → ℝ)
    (hh : ∀ w, 0 ≤ h w) :
    ∑ s, D.NW ℓ θ x₀ obsT s * c.term s * h s.2.1
      ≤ ∑ s, c.term s * h s.1 := by
  classical
  obtain ⟨H, hHcont, hHderiv, hHterm, hHnn⟩ := D.exists_bwdExt hθ0 hθ h hh
  have hgrid := c.is.grid
  have hK : 0 < c.K := hgrid.pos
  have hToT : obsT ≤ D.T := D.obsT_lt_T.le
  have hcell : ∀ k, k < c.K → Set.Icc (c.z k) (c.z (k + 1)) ⊆ Set.Icc θ obsT := by
    intro k hk t ht
    exact ⟨le_trans (D.grid_mem hgrid (le_of_lt hk)).1 ht.1,
      le_trans ht.2 (D.grid_mem hgrid (Nat.succ_le_of_lt hk)).2⟩
  -- cell-wise continuity of the `N`-weighted pairing
  have hu_cont : ∀ k, k < c.K →
      ContinuousOn (fun t => ∑ s, c.π k t s * (D.NW ℓ θ x₀ t s * H t s.2.1))
        (Set.Icc (c.z k) (c.z (k + 1))) := by
    intro k hk
    refine continuousOn_finset_sum _ fun s _ => ?_
    refine ContinuousOn.mul ((c.is.glued.flow k hk).cont s) (ContinuousOn.mul ?_ ?_)
    · exact D.continuousOn_NW ℓ θ x₀
        (le_trans (D.grid_mem hgrid (Nat.succ_le_of_lt hk)).2 hToT) s
    · exact (hHcont s.2.1).mono (hcell k hk)
  -- cell-wise nonpositive drift: AM–GM on the alive sector, zero on the dead one
  have hu_deriv : ∀ k, k < c.K → ∀ t ∈ Set.Icc (c.z k) (c.z (k + 1)),
      ∃ v ≤ (0 : ℝ),
        HasDerivWithinAt (fun t => ∑ s, c.π k t s * (D.NW ℓ θ x₀ t s * H t s.2.1)) v
          (Set.Icc (c.z k) (c.z (k + 1))) t := by
    intro k hk t ht
    have htθ : t ∈ Set.Icc θ obsT := hcell k hk ht
    have htT : t ≤ D.T := le_trans htθ.2 hToT
    have hB : ∀ w : Cube n, w ∈ D.barrier ℓ ((c.z k + c.z (k + 1)) / 2) →
        ℓ + 1 ≤ D.F t w := fun w hw => D.cell_barrier_F hgrid hk ht hw
    have hHt : ∀ w, 0 ≤ H t w := fun w => hHnn t htθ w
    have hgs : ∀ s : JSt n,
        HasDerivWithinAt (fun t => D.NW ℓ θ x₀ t s * H t s.2.1)
          (D.NW ℓ θ x₀ t s * ((∑ i, D.Sc t i s.2.1)
              - (if s.2.2 then 1 - D.dbar ℓ θ x₀ else 1) * (∑ i, D.Sc t i s.1))
            * H t s.2.1
            + D.NW ℓ θ x₀ t s * (-(D.revGen t (H t) s.2.1)))
          (Set.Icc (c.z k) (c.z (k + 1))) t := fun s =>
      ((D.hasDerivAt_NW ℓ θ x₀ htT s).hasDerivWithinAt).mul
        ((hHderiv s.2.1 t htθ).mono (hcell k hk))
    refine ⟨_, ?_, hasDerivWithinAt_pairing (c.is.glued.flow k hk) ht hgs⟩
    -- generator duality: the flow half of the drift is a jump-rate pairing
    have hdual : ∑ s : JSt n,
          matVec (D.cellGen ℓ θ (D.dbar ℓ θ x₀) c.z k t) (c.π k t) s
            * (D.NW ℓ θ x₀ t s * H t s.2.1)
        = ∑ σ : JSt n, c.π k t σ *
            (∑ s : JSt n,
              D.jrate (D.dbar ℓ θ x₀) (D.barrier ℓ ((c.z k + c.z (k + 1)) / 2)) t σ s
                * (D.NW ℓ θ x₀ t s * H t s.2.1 - D.NW ℓ θ x₀ t σ * H t σ.2.1)) := by
      simp only [cellGen, matVec, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      have hpull : ∑ s : JSt n,
            fwdOf (D.jrate (D.dbar ℓ θ x₀)
                (D.barrier ℓ ((c.z k + c.z (k + 1)) / 2)) t) s σ * c.π k t σ
              * (D.NW ℓ θ x₀ t s * H t s.2.1)
          = c.π k t σ * ∑ s : JSt n,
            fwdOf (D.jrate (D.dbar ℓ θ x₀)
                (D.barrier ℓ ((c.z k + c.z (k + 1)) / 2)) t) s σ
              * (D.NW ℓ θ x₀ t s * H t s.2.1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [hpull, fwdOf_transpose_pair]
    -- the pointwise cell inequality
    have hbracket : ∀ σ : JSt n,
        (∑ s : JSt n,
            D.jrate (D.dbar ℓ θ x₀) (D.barrier ℓ ((c.z k + c.z (k + 1)) / 2)) t σ s
              * (D.NW ℓ θ x₀ t s * H t s.2.1 - D.NW ℓ θ x₀ t σ * H t σ.2.1))
          + (D.NW ℓ θ x₀ t σ * ((∑ i, D.Sc t i σ.2.1)
                - (if σ.2.2 then 1 - D.dbar ℓ θ x₀ else 1) * (∑ i, D.Sc t i σ.1))
              * H t σ.2.1
            + D.NW ℓ θ x₀ t σ * (-(D.revGen t (H t) σ.2.1))) ≤ 0 := by
      intro σ
      obtain ⟨x, y, bb⟩ := σ
      cases bb with
      | false => exact le_of_eq (D.bracket_dead htT x y)
      | true => exact D.bracket_alive htT hB hHt x y
    rw [Finset.sum_add_distrib, hdual, ← Finset.sum_add_distrib]
    refine Finset.sum_nonpos fun σ _ => ?_
    rw [← mul_add]
    have hz := mul_le_mul_of_nonneg_left (hbracket σ) (D.cflow_nonneg hθ c hk ht σ)
    rwa [mul_zero] at hz
  -- node transfers do not increase the pairing
  have hu_node : ∀ k, k + 1 < c.K →
      (∑ s, c.π (k + 1) (c.z (k + 1)) s
          * (D.NW ℓ θ x₀ (c.z (k + 1)) s * H (c.z (k + 1)) s.2.1))
        ≤ ∑ s, c.π k (c.z (k + 1)) s
          * (D.NW ℓ θ x₀ (c.z (k + 1)) s * H (c.z (k + 1)) s.2.1) := by
    intro k hk
    have hkK : k < c.K := lt_trans (Nat.lt_succ_self k) hk
    have hmem : c.z (k + 1) ∈ Set.Icc (c.z k) (c.z (k + 1)) :=
      Set.right_mem_Icc.2 (hgrid.mono k hkK)
    rw [c.is.glued.node k hk]
    exact D.killTr_pairing_le ℓ θ x₀ (c.z (k + 1))
      (fun w => hHnn _ (hcell k hkK hmem) w)
      (fun s => D.cflow_nonneg hθ c hkK hmem s)
  have hchain := chain_mono hK (z := c.z)
    (u := fun k t => ∑ s, c.π k t s * (D.NW ℓ θ x₀ t s * H t s.2.1))
    hgrid.mono hu_cont hu_deriv hu_node
  rw [hgrid.last, hgrid.first] at hchain
  -- the starting value: `Tr 0` either keeps the weight `1` or kills it to `≤ 1`
  have hstart : (∑ s, c.π 0 θ s * (D.NW ℓ θ x₀ θ s * H θ s.2.1)) ≤ H θ x₀ := by
    have h0 : c.π 0 θ = matVec (D.killTr ℓ θ) (initVec x₀) := by
      have h1 := c.is.glued.init
      simp only [hgrid.first] at h1
      exact h1
    have hle := D.killTr_pairing_le ℓ θ x₀ θ
      (fun w => hHnn θ ⟨le_rfl, hθ⟩ w) (fun s => initVec_nonneg' x₀ s)
    have hval : ∑ s : JSt n, initVec x₀ s * (D.NW ℓ θ x₀ θ s * H θ s.2.1)
        = D.NW ℓ θ x₀ θ ((x₀, x₀, true) : JSt n) * H θ x₀ := by
      simp only [initVec, ite_mul, zero_mul, one_mul]
      rw [Finset.sum_ite_eq' Finset.univ ((x₀, x₀, true) : JSt n)
        (fun s => D.NW ℓ θ x₀ θ s * H θ s.2.1)]
      simp
    have hNW1 : D.NW ℓ θ x₀ θ ((x₀, x₀, true) : JSt n) = 1 := by
      rw [D.NW_true, show D.F θ x₀ - (1 - D.dbar ℓ θ x₀) * D.F θ x₀
        - D.dbar ℓ θ x₀ * D.F θ x₀ = 0 by ring, Real.exp_zero]
    rw [hval, hNW1, one_mul] at hle
    rw [h0]
    exact hle
  -- the `V`-marginal is the plain reverse flow
  have hVm : ∑ s, c.term s * h s.1 = H θ x₀ := by
    have hmarg := D.cflow_V_marginal hθ0 hθ c H hHcont hHderiv
    rwa [hHterm] at hmarg
  have hterm : (∑ s, D.NW ℓ θ x₀ obsT s * c.term s * h s.2.1)
      = ∑ s, c.π (c.K - 1) obsT s * (D.NW ℓ θ x₀ obsT s * H obsT s.2.1) := by
    rw [hHterm]
    exact Finset.sum_congr rfl fun s _ => by simp only [Dat.CFlow.term]; ring
  rw [hterm, hVm]
  exact le_trans hchain hstart

/-- The localized form over a set of starting points [LGF
eq (4.14)]: for `A ⊆ G`,
`∑_{x₀∈A} ν(x₀)·𝔼_{x₀}[N h(W)] ≤ ∑_{x₀∈A} ν(x₀)·𝔼_{x₀}[h(V)]`. -/
theorem weighted_comparison_localized {ℓ θ : ℝ} (hℓ : 0 < ℓ) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) (Φ : D.CFlowFamily ℓ θ) (A : Finset (Cube n))
    (h : Cube n → ℝ) (hh : ∀ w, 0 ≤ h w) :
    ∑ x₀ ∈ A, D.startW θ x₀ *
        ∑ s, D.NW ℓ θ x₀ obsT s * (Φ x₀).term s * h s.2.1
      ≤ ∑ x₀ ∈ A, D.startW θ x₀ * ∑ s, (Φ x₀).term s * h s.1 := by
  refine Finset.sum_le_sum fun x₀ _ => ?_
  have hTθ : 0 ≤ D.T - θ := by have := D.obsT_lt_T; linarith
  have hw : 0 ≤ D.startW θ x₀ := by
    have := D.fs_pos hTθ x₀
    simp only [startW, revDensity]
    positivity
  exact mul_le_mul_of_nonneg_left
    (D.weighted_comparison hℓ hθ0 hθ (Φ x₀) h hh) hw

/-- Pointwise lower bound for the terminal weight on the crossing event
[LGF, proof of Lemma 3.4]: for `x₀ ∈ ℰ_θ` and a terminal state `s` with
`F_{T_o}(W) ∈ (ℓ+j, ℓ+j+1]` and `F_{T_o}(V) ≤ ℓ+1` (alive sector) —
resp. any dead-sector state with those `F`-values —
`N_{T_o}(s) ≥ e^{α+j-1} = e^{j+4}`. -/
theorem NW_ge_on_crossing {ℓ θ : ℝ} {x₀ : Cube n}
    (hx₀ : x₀ ∈ D.activeF ℓ θ) {s : JSt n} {j : ℝ} (hj : 0 ≤ j)
    (hW : ℓ + j < D.F obsT s.2.1) (hV : D.F obsT s.1 ≤ ℓ + 1) :
    Real.exp (alphaC + j - 1) ≤ D.NW ℓ θ x₀ obsT s := by
  classical
  set d := D.dbar ℓ θ x₀ with hd_def
  set R := D.Rgap ℓ θ x₀ with hR_def
  have hR : 2 * alphaC ≤ R := by
    simpa [activeF, Finset.mem_filter, hR_def] using hx₀
  have hact : x₀ ∈ D.activeSet ℓ θ := hR
  have halpha : (0 : ℝ) < alphaC := by norm_num [alphaC]
  have hRpos : 0 < R := lt_of_lt_of_le (by linarith) hR
  -- on the active set the positive part is attained
  have hFθ : D.F θ x₀ = ℓ - R := by
    have h1 : 0 < ℓ - D.F θ x₀ := by
      rcases lt_max_iff.mp (hR_def ▸ hRpos) with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have : R = ℓ - D.F θ x₀ := by
      rw [hR_def, Rgap]; exact max_eq_left h1.le
    linarith
  have hdR : d * (R + 1) = alphaC := D.dbar_mul_Rgap_add_one hact
  have hd0 : 0 ≤ d := D.dbar_nonneg ℓ θ x₀
  have hd1 : d < 1 / 2 := D.dbar_lt_half ℓ θ x₀
  rw [NW]
  split
  · -- alive sector
    refine Real.exp_le_exp.2 ?_
    have h1 : (1 - d) * D.F obsT s.1 ≤ (1 - d) * (ℓ + 1) :=
      mul_le_mul_of_nonneg_left hV (by linarith)
    have key : (1 - d) * (ℓ + 1) + d * (ℓ - R) = ℓ + 1 - alphaC := by
      rw [← hdR]; ring
    rw [hFθ]
    linarith
  · -- dead sector
    refine Real.exp_le_exp.2 ?_
    have key : d * (ℓ + 1 - (ℓ - R)) = alphaC := by rw [← hdR]; ring
    rw [hFθ]
    linarith

end Dat

end Talagrand
