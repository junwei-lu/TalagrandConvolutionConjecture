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

private lemma F_flip_eq {t : ℝ} (i : Fin n) (x : Cube n) :
    D.F t (flipCoord i x) = D.F t x + Real.log (D.Y t i x) := by
  have := D.F_flipCoord_sub t i x; linarith

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
  rw [D.F_flip_eq i x, D.F_flip_eq i y]; ring

/-- `W`-only flip: the weight ratio is `X_i`. -/
private lemma NW_flip_W (ℓ θ : ℝ) (x₀ : Cube n) {t : ℝ} (ht : t ≤ D.T)
    (i : Fin n) (x y : Cube n) :
    D.NW ℓ θ x₀ t (x, flipCoord i y, true)
      = D.NW ℓ θ x₀ t (x, y, true) * D.Y t i y := by
  have hX : 0 < D.Y t i y := D.Y_pos ht i y
  rw [D.NW_true, D.NW_true, ← Real.exp_log hX, ← Real.exp_add]
  congr 1
  rw [D.F_flip_eq i y]; ring

/-- `V`-only flip, alive landing: the weight ratio is `Y_i^{δ̄-1}`. -/
private lemma NW_flip_V (ℓ θ : ℝ) (x₀ : Cube n) {t : ℝ} (ht : t ≤ D.T)
    (i : Fin n) (x y : Cube n) :
    D.NW ℓ θ x₀ t (flipCoord i x, y, true)
      = D.NW ℓ θ x₀ t (x, y, true) * D.Y t i x ^ (D.dbar ℓ θ x₀ - 1) := by
  have hY : 0 < D.Y t i x := D.Y_pos ht i x
  rw [D.NW_true, D.NW_true, Real.rpow_def_of_pos hY, ← Real.exp_add]
  congr 1
  rw [D.F_flip_eq i x]; ring

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
  rw [D.F_flip_eq i x, D.F_flip_eq i y]; ring

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
