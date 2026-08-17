import TalagrandConvConjecture.Lemmas.ScoreEnergy
import TalagrandConvConjecture.Lemmas.Discrepancy
import TalagrandConvConjecture.Lemmas.BandContraction

/-!
# The fixed-band anti-concentration estimate [LGF Proposition 3.2]

`𝔄_{t_a}((ℓ, ℓ+1]) ≲ K_a/√ℓ` for every `ℓ > 0`.

Proof [LGF §3.1], three steps for `ℓ ≥ C·K_a²`:
1. *Active discrepancy*: decompose `ℰ_θ` into gap layers `E_r(θ)`
   (`r ≤ R_θ < r+1`), bound each `D_{E_r}` via [LGF Lemma 3.3] +
   [LGF Lemma 3.5], average over `θ ∈ [T_o-1, T_o]` using the windowed
   profile bound [C Lemma 4]: `∫ D_{ℰ_θ} dθ ≲ K_a/√ℓ` — realized here as a
   pointwise-in-`θ` bound by an explicit measurable majorant with small
   integral.
2. *Inactive starting points*: `Ā_θ(ℓ) = ℙ(ℰ_θᶜ, F_{T_o}(V_{T_o}) ∈ band)`;
   near layers via the profile bound, far layers via the `e^{-F}`-martingale
   Chebyshev estimate `ℙ(F_{T_o}(V_{T_o}) ≤ ℓ+1 | V_θ = x₀) ≤ e^{ℓ+1-F_θ(x₀)}`.
3. *Closing the recurrence*: combine with [LGF Lemma 3.4]; pick a good `θ` by
   the mean-value principle; run the geometric-band bootstrap
   (`ϱ* = c₀/((1-c₀)(e-1)) < 1`) on `𝓜_ℓ = sup_{r≥ℓ} √r·𝔄_{t_a}((r,r+1])`.
For `ℓ < C·K_a²` the trivial bound `𝔄 ≤ 1 ≤ K_a√C/√ℓ` applies.
-/

namespace Talagrand

namespace Dat

variable {n : ℕ} (D : Dat n)

/-- Coupling-flow families exist for every admissible `(ℓ, θ)`. -/
theorem exists_cflowFamily (ℓ : ℝ) (hℓ : 0 < ℓ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) : Nonempty (D.CFlowFamily ℓ θ) :=
  ⟨fun x₀ => (D.exists_cflow ℓ hℓ hθ0 hθ x₀).some⟩

/-- Terminal sub-law of a coupling flow is nonnegative (the terminal time
`T_o` sits in the last cell of the grid). -/
lemma cflow_term_nonneg {ℓ θ : ℝ} (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (s : JSt n) : 0 ≤ c.term s := by
  have hK : 0 < c.K := c.is.grid.pos
  have hk : c.K - 1 < c.K := Nat.sub_lt hK Nat.one_pos
  have hsucc : c.K - 1 + 1 = c.K := Nat.succ_pred_eq_of_pos hK
  have hmono : c.z (c.K - 1) ≤ c.z (c.K - 1 + 1) := c.is.grid.mono _ hk
  have hlast : c.z (c.K - 1 + 1) = obsT := by rw [hsucc]; exact c.is.grid.last
  have ht : obsT ∈ Set.Icc (c.z (c.K - 1)) (c.z (c.K - 1 + 1)) :=
    ⟨by rw [← hlast]; exact hmono, hlast.ge⟩
  exact D.cflow_nonneg hθ c hk ht s

/-- **Reciprocal-martingale tail bound** [LGF, Step 2 of Prop 3.2]: for any
coupling flow from `x₀`,
`𝔼_{x₀}[1_{F_{T_o}(V_{T_o}) ≤ c}] ≤ e^{c - F_θ(x₀)}` for every `c`. -/
theorem term_V_tail_le {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT) {x₀ : Cube n}
    (c : D.CFlow ℓ θ x₀) (cLev : ℝ) :
    ∑ s : JSt n, c.term s * (if D.F obsT s.1 ≤ cLev then (1 : ℝ) else 0)
      ≤ Real.exp (cLev - D.F θ x₀) := by
  classical
  have hsub : Set.Icc θ obsT ⊆ Set.Iic D.T := fun t ht =>
    le_trans ht.2 (le_of_lt D.obsT_lt_T)
  have hmarg : ∑ s : JSt n, c.term s * Real.exp (-(D.F obsT s.1))
      = Real.exp (-(D.F θ x₀)) := by
    refine D.cflow_V_marginal hθ0 hθ c (fun t x => Real.exp (-(D.F t x)))
      (fun x => (((D.continuousOn_F x).mono hsub).neg).rexp) ?_
    intro x t ht
    exact (D.hasDerivAt_exp_neg_F (hsub ht) x).hasDerivWithinAt
  have hterm : ∀ s : JSt n, 0 ≤ c.term s := fun s => D.cflow_term_nonneg hθ c s
  have hle : ∀ s : JSt n, c.term s * (if D.F obsT s.1 ≤ cLev then (1 : ℝ) else 0)
      ≤ Real.exp cLev * (c.term s * Real.exp (-(D.F obsT s.1))) := by
    intro s
    by_cases h : D.F obsT s.1 ≤ cLev
    · rw [if_pos h, mul_one]
      have h1 : (1 : ℝ) ≤ Real.exp cLev * Real.exp (-(D.F obsT s.1)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      calc c.term s = c.term s * 1 := (mul_one _).symm
        _ ≤ c.term s * (Real.exp cLev * Real.exp (-(D.F obsT s.1))) :=
            mul_le_mul_of_nonneg_left h1 (hterm s)
        _ = Real.exp cLev * (c.term s * Real.exp (-(D.F obsT s.1))) := by ring
    · rw [if_neg h, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (hterm s) (Real.exp_pos _).le)
  calc ∑ s : JSt n, c.term s * (if D.F obsT s.1 ≤ cLev then (1 : ℝ) else 0)
      ≤ ∑ s : JSt n, Real.exp cLev * (c.term s * Real.exp (-(D.F obsT s.1))) :=
        Finset.sum_le_sum fun s _ => hle s
    _ = Real.exp cLev * ∑ s : JSt n, c.term s * Real.exp (-(D.F obsT s.1)) := by
        rw [← Finset.mul_sum]
    _ = Real.exp cLev * Real.exp (-(D.F θ x₀)) := by rw [hmarg]
    _ = Real.exp (cLev - D.F θ x₀) := by
        rw [← Real.exp_add, ← sub_eq_add_neg]

/-! ### The backward (terminal-value) extension of a test function

`revFwdMat` is the transpose of the matrix of `revGen`; the terminal-value
problem `∂_t g = -revGen g`, `g_{T_o} = φ` is therefore solved by reversing
time in `exists_linFlow`, and the pairing `⟨ν_{T-t}, g_t⟩` is constant. -/

/-- Summing `revFwdMat` against its *first* index reproduces the reverse
generator: `∑_x revFwdMat_t(x,y)·g(x) = (L̃_t g)(y)`. -/
lemma sum_revFwdMat_mul (t : ℝ) (g : Cube n → ℝ) (y : Cube n) :
    ∑ x : Cube n, D.revFwdMat t x y * g x = D.revGen t g y := by
  classical
  have e1 : ∀ x : Cube n, D.revFwdMat t x y * g x
      = (∑ i, if x = flipCoord i y then D.Y t i y / 2 * g x else 0)
        - (if x = y then (∑ i, D.Y t i x / 2) * g x else 0) := by
    intro x
    rw [revFwdMat, sub_mul, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by
        by_cases h : x = flipCoord i y <;> simp [h]
    · by_cases h : x = y <;> simp [h]
  rw [Finset.sum_congr rfl fun x _ => e1 x, Finset.sum_sub_distrib,
    Finset.sum_comm]
  have e2 : ∀ i : Fin n,
      (∑ x : Cube n, if x = flipCoord i y then D.Y t i y / 2 * g x else 0)
        = D.Y t i y / 2 * g (flipCoord i y) := fun i => by simp
  have e3 : (∑ x : Cube n, if x = y then (∑ i, D.Y t i x / 2) * g x else 0)
      = (∑ i, D.Y t i y / 2) * g y := by simp
  rw [Finset.sum_congr rfl fun i _ => e2 i, e3, revGen, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Continuity in `t` of the forward matrix entries on `(-∞, T]`. -/
lemma continuousOn_revFwdMat (x x' : Cube n) :
    ContinuousOn (fun t => D.revFwdMat t x x') (Set.Iic D.T) := by
  classical
  simp only [revFwdMat]
  refine ContinuousOn.sub (continuousOn_finset_sum _ fun i _ => ?_) ?_
  · by_cases h : x = flipCoord i x'
    · simp only [if_pos h]
      exact (D.continuousOn_Y i x').div_const 2
    · simp only [if_neg h]; exact continuousOn_const
  · by_cases h : x = x'
    · simp only [if_pos h]
      exact continuousOn_finset_sum _ fun i _ => (D.continuousOn_Y i x).div_const 2
    · simp only [if_neg h]; exact continuousOn_const

/-- Backward (terminal-value) extension: for every `φ` there is `g` on
`[θ, T_o]` with `∂_t g_t = -L̃_t g_t` and `g_{T_o} = φ`. -/
lemma exists_backFlow {θ : ℝ} (hθ : θ ≤ obsT) (φ : Cube n → ℝ) :
    ∃ g : ℝ → Cube n → ℝ,
      (∀ x, ContinuousOn (fun t => g t x) (Set.Icc θ obsT)) ∧
      (∀ x, ∀ t ∈ Set.Icc θ obsT,
        HasDerivWithinAt (fun t => g t x) (-(D.revGen t (g t) x))
          (Set.Icc θ obsT) t) ∧
      g obsT = φ := by
  classical
  have hmaps : Set.MapsTo (fun t => θ + obsT - t) (Set.Icc θ obsT)
      (Set.Icc θ obsT) := fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hmapsT : Set.MapsTo (fun t => θ + obsT - t) (Set.Icc θ obsT)
      (Set.Iic D.T) := fun t ht => by
    have := (hmaps ht).2
    have h2 : obsT ≤ D.T := D.obsT_lt_T.le
    exact le_trans this h2
  have hcontσ : ContinuousOn (fun t : ℝ => θ + obsT - t) (Set.Icc θ obsT) := by
    fun_prop
  set A : ℝ → Cube n → Cube n → ℝ :=
    fun t x x' => D.revFwdMat (θ + obsT - t) x' x with hA
  have hAc : ∀ x x', ContinuousOn (fun t => A t x x') (Set.Icc θ obsT) :=
    fun x x' => (D.continuousOn_revFwdMat x' x).comp hcontσ hmapsT
  obtain ⟨w, hw, hw0⟩ := exists_linFlow A hθ hAc φ
  refine ⟨fun t => w (θ + obsT - t), fun x => (hw.cont x).comp hcontσ hmaps,
    ?_, ?_⟩
  · intro x t ht
    have hσ : HasDerivWithinAt (fun t : ℝ => θ + obsT - t) (-1)
        (Set.Icc θ obsT) t := by
      simpa using
        (((hasDerivAt_const t (θ + obsT)).sub (hasDerivAt_id t)).hasDerivWithinAt
          (s := Set.Icc θ obsT))
    have hd := hw.deriv x (θ + obsT - t) (hmaps ht)
    have key : HasDerivWithinAt (fun t => w (θ + obsT - t) x)
        (matVec (A (θ + obsT - t)) (w (θ + obsT - t)) x * (-1))
        (Set.Icc θ obsT) t := hd.comp t hσ hmaps
    have harg : θ + obsT - (θ + obsT - t) = t := by ring
    have hval : matVec (A (θ + obsT - t)) (w (θ + obsT - t)) x
        = D.revGen t (w (θ + obsT - t)) x := by
      simp only [hA, matVec, harg]
      exact D.sum_revFwdMat_mul t (w (θ + obsT - t)) x
    rw [hval, mul_neg_one] at key
    exact key
  · funext x
    show w (θ + obsT - obsT) x = φ x
    rw [show θ + obsT - obsT = θ from by ring]
    exact congrFun hw0 x

open Classical in
/-- The `V`-terminal band mass over all starting points is the profile:
`∑_{x₀} ν_{T-θ}(x₀)·𝔼_{x₀}[1_{F_{T_o}(V) ∈ I}] = 𝔄_{t_a}(I)`
[LGF eq (3.14), `V_{T_o} ∼ ν_{t_a}`]. -/
theorem sum_term_V_eq_profile {ℓ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT)
    (Φ : D.CFlowFamily ℓ θ) (I : Set ℝ) :
    ∑ x₀ : Cube n, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
        (if D.F obsT s.1 ∈ I then (1 : ℝ) else 0)
      = profile D.f D.tA I := by
  classical
  obtain ⟨g, hgc, hgd, hgT⟩ :=
    D.exists_backFlow hθ (fun x => if D.F obsT x ∈ I then (1 : ℝ) else 0)
  have hgTx : ∀ x : Cube n,
      g obsT x = if D.F obsT x ∈ I then (1 : ℝ) else 0 := fun x => congrFun hgT x
  -- the reverse law is a flow for `revFwdMat`
  have hTle : ∀ t ∈ Set.Icc θ obsT, t ≤ D.T := fun t ht =>
    le_trans ht.2 D.obsT_lt_T.le
  have hν : IsLinFlow D.revFwdMat θ obsT (fun t => D.revDensity t) := by
    refine ⟨fun x t ht => ?_, fun x t ht => ?_⟩
    · exact ((D.hasDerivAt_revDensity (hTle t ht) x).continuousAt).continuousWithinAt
    · exact (D.hasDerivAt_revDensity (hTle t ht) x).hasDerivWithinAt
  -- the pairing has vanishing derivative
  have hpair : ∀ t ∈ Set.Icc θ obsT,
      HasDerivWithinAt (fun t => ∑ x : Cube n, D.revDensity t x * g t x) 0
        (Set.Icc θ obsT) t := by
    intro t ht
    have h := hasDerivWithinAt_pairing hν ht (g := g)
      (g' := fun x => -(D.revGen t (g t) x)) (fun x => hgd x t ht)
    have e1 : ∑ x : Cube n, matVec (D.revFwdMat t) (D.revDensity t) x * g t x
        = ∑ x : Cube n, D.revDensity t x * D.revGen t (g t) x := by
      simp only [matVec, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [← D.sum_revFwdMat_mul t (g t) x', Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    have e2 : ∑ x : Cube n, D.revDensity t x * (-(D.revGen t (g t) x))
        = -∑ x : Cube n, D.revDensity t x * D.revGen t (g t) x := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hzero : ∑ x : Cube n, (matVec (D.revFwdMat t) (D.revDensity t) x * g t x
        + D.revDensity t x * (-(D.revGen t (g t) x))) = 0 := by
      rw [Finset.sum_add_distrib, e1, e2, add_neg_cancel]
    rwa [hzero] at h
  -- hence it is constant
  have hconst : ∑ x : Cube n, D.revDensity obsT x * g obsT x
      = ∑ x : Cube n, D.revDensity θ x * g θ x := by
    rcases eq_or_lt_of_le hθ with heq | hlt
    · rw [heq]
    · refine constant_of_derivWithin_zero
        (fun t ht => (hpair t ht).differentiableWithinAt)
        (fun t ht => (hpair t ⟨ht.1, ht.2.le⟩).derivWithin
          (uniqueDiffOn_Icc hlt t ⟨ht.1, ht.2.le⟩))
        obsT (Set.right_mem_Icc.2 hθ)
  -- the left-hand side is the pairing at time `θ`
  have hmarg : ∀ x₀ : Cube n,
      ∑ s : JSt n, (Φ x₀).term s * (if D.F obsT s.1 ∈ I then (1 : ℝ) else 0)
        = g θ x₀ := by
    intro x₀
    have h := D.cflow_V_marginal hθ0 hθ (Φ x₀) g hgc hgd
    simpa only [hgTx] using h
  have hL : ∑ x₀ : Cube n, D.startW θ x₀ * ∑ s : JSt n, (Φ x₀).term s *
        (if D.F obsT s.1 ∈ I then (1 : ℝ) else 0)
      = ∑ x₀ : Cube n, D.revDensity θ x₀ * g θ x₀ :=
    Finset.sum_congr rfl fun x₀ _ => by rw [hmarg x₀]; rfl
  -- and the pairing at time `T_o` is the profile
  have hTsub : D.T - obsT = D.tA := by
    show D.tA + obsT - obsT = D.tA
    ring
  have hterm : ∀ x : Cube n, D.revDensity obsT x * g obsT x
      = I.indicator (fun _ => heatAt D.f D.tA x)
          (Real.log (heatAt D.f D.tA x)) / 2 ^ n := by
    intro x
    have hF : D.F obsT x = Real.log (heatAt D.f D.tA x) := by
      show Real.log (D.fs (D.T - obsT) x) = _
      rw [hTsub]; rfl
    have hd : D.revDensity obsT x = heatAt D.f D.tA x / 2 ^ n := by
      show D.fs (D.T - obsT) x / 2 ^ n = _
      rw [hTsub]; rfl
    rw [hgTx, hF, hd]
    by_cases h : Real.log (heatAt D.f D.tA x) ∈ I
    · rw [if_pos h, Set.indicator_of_mem h]; ring
    · rw [if_neg h, Set.indicator_of_notMem h]; ring
  have hR : ∑ x : Cube n, D.revDensity obsT x * g obsT x = profile D.f D.tA I := by
    rw [profile, unifE, Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => hterm x
  rw [hL, ← hconst, hR]

/-- Vanishing of high bands: `𝔄_{t_a}((r,r+1]) = 0` once `r` exceeds
`max_x log f_{t_a}(x)`. -/
theorem exists_profile_vanish :
    ∃ B : ℝ, ∀ r : ℝ, B ≤ r → profile D.f D.tA (Set.Ioc r (r + 1)) = 0 := by
  classical
  refine ⟨1 + ∑ x : Cube n, |Real.log (heatAt D.f D.tA x)|, fun r hr => ?_⟩
  have hnot : ∀ x : Cube n,
      Real.log (heatAt D.f D.tA x) ∉ Set.Ioc r (r + 1) := by
    intro x hx
    have h1 : |Real.log (heatAt D.f D.tA x)|
        ≤ ∑ y : Cube n, |Real.log (heatAt D.f D.tA y)| :=
      Finset.single_le_sum (f := fun y : Cube n => |Real.log (heatAt D.f D.tA y)|)
        (fun y _ => abs_nonneg _) (Finset.mem_univ x)
    have h2 := le_abs_self (Real.log (heatAt D.f D.tA x))
    have h3 := hx.1
    linarith
  have hz : (fun x : Cube n => (Set.Ioc r (r + 1)).indicator
      (fun _ => heatAt D.f D.tA x) (Real.log (heatAt D.f D.tA x)))
      = fun _ : Cube n => (0 : ℝ) := by
    funext x
    exact Set.indicator_of_notMem (hnot x) _
  simp only [profile, hz]
  exact unifE_const 0

end Dat

/-- **Fixed-band anti-concentration** [LGF Proposition 3.2]: there is a
universal `C` with `𝔄_{t_a}((ℓ,ℓ+1]) ≤ C·K_a/√ℓ` for all data and `ℓ > 0`. -/
theorem fixed_band :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (D : Dat n) (ℓ : ℝ), 0 < ℓ →
      profile D.f D.tA (Set.Ioc ℓ (ℓ + 1))
        ≤ C * Ka D.a / Real.sqrt ℓ := by
  sorry

end Talagrand
