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
