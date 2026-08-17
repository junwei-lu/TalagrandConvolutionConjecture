import TalagrandConvConjecture.FixedBand

/-!
# Talagrand's convolution conjecture [LGF Theorem 1.1]

From the fixed-band estimate [LGF Prop 3.2] to the weak-type bound: for
strictly positive `f`, the layer-cake/geometric-series argument of
[LGF, proof of Thm 1.1]; general `f ≥ 0` by the strictly positive
approximation `(f+ε)/(1+ε)`.

Two deviations from the write-up of [LGF], both only affecting the value of
the universal constant (never the statement):

* the level shift `u ↝ v` needed because the bands `(ℓ+j, ℓ+j+1]` are
  left-open is done at the *explicit* level `v = (1+u)/2` instead of by a
  limit `v ↑ u`; since `√u ≤ (1+u)/2` (AM–GM) one has `log v ≥ (log u)/2` and
  `u/v ≤ 2`, so the cost is the factor `2√2 ≤ 3` (`level_transfer`);
* likewise the approximation `f ↝ (f+ε)/(1+ε)` of general `f ≥ 0` by a
  strictly positive density is used at the *explicit* value `ε = 1`, for
  which the level `u` becomes exactly `(1+u)/2` and `level_transfer` applies
  verbatim.
-/

namespace Talagrand

variable {n : ℕ}

/-- `T_{μ_a} = P_{t_a}`: the biased convolution is the heat flow at time
`t_a = -log a` [LGF §2.1]. -/
lemma biasedConv_eq_heatAt {a : ℝ} (ha : 0 < a) (f : Cube n → ℝ) :
    biasedConv a f = heatAt f (-Real.log a) := by
  funext x
  show ∑ y, biasedWeight a y * f (x * y) = smooth (Real.exp (-(-Real.log a))) f x
  rw [neg_neg, Real.exp_log ha, smooth_eq_conv]

/-! ### Elementary auxiliaries -/

/-- The biased weights form a probability vector, `∑_y μ_a({y}) = 1`. -/
private lemma sum_biasedWeight (ρ : ℝ) : ∑ y : Cube n, biasedWeight ρ y = 1 := by
  have h := sum_cubeKernel (n := n) (fun _ => ρ)
  simpa [cubeKernel, biasedWeight] using h

/-- `𝔼_λ` commutes with finite sums. -/
private lemma unifE_sum {ι : Type*} (s : Finset ι) (F : ι → Cube n → ℝ) :
    unifE (fun x => ∑ j ∈ s, F j x) = ∑ j ∈ s, unifE (F j) := by
  simp only [unifE, Finset.sum_div]
  rw [Finset.sum_comm]

/-- `𝔼_λ (c₁·g + c₂) = c₁·𝔼_λ g + c₂`. -/
private lemma unifE_affine (c₁ c₂ : ℝ) (g : Cube n → ℝ) :
    unifE (fun x => c₁ * g x + c₂) = c₁ * unifE g + c₂ := by
  simp only [unifE_add, unifE_smul, unifE_const]

/-- `e^{-j} = (e^{-1})^j`. -/
private lemma exp_neg_nat (j : ℕ) : Real.exp (-(j : ℝ)) = Real.exp (-1) ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← ih, ← Real.exp_add]
    push_cast
    ring_nf

private lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-1)]

/-- Geometric series bound `∑_{j<m} e^{-j} ≤ 2` (since `e^{-1} ≤ ½`). -/
private lemma sum_exp_neg_pow_le (m : ℕ) :
    ∑ j ∈ Finset.range m, Real.exp (-1) ^ j ≤ 2 := by
  have key : ∀ k : ℕ,
      ∑ j ∈ Finset.range k, Real.exp (-1) ^ j ≤ 2 - 2 * Real.exp (-1) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hp : (0 : ℝ) ≤ Real.exp (-1) ^ k := by positivity
      nlinarith [exp_neg_one_le_half]
  have hp : (0 : ℝ) ≤ Real.exp (-1) ^ m := by positivity
  linarith [key m]

/-! ### The layer-cake step -/

/-- **Layer cake** [LGF, proof of Thm 1.1]: if the size-biased band masses of a
density `g` obey `𝔄((r,r+1]) ≤ B/√r` for every `r > 0`, then
`λ(log g > ℓ) ≤ 2B/(e^ℓ √ℓ)` for every `ℓ > 0`.

Decompose `{log g > ℓ}` into the bands `(ℓ+j, ℓ+j+1]`, `j ∈ ℕ` (finitely many
suffice since `g ≤ 2^n`), use `1 ≤ e^{-(ℓ+j)}·g` on the `j`-th band, and sum the
resulting geometric series `∑_j e^{-j}·B/√(ℓ+j) ≤ 2B/√ℓ`. -/
private lemma unifMeas_log_gt_le {g : Cube n → ℝ} (hg : ∀ x, 0 < g x)
    (hmass : unifE g = 1) {ℓ : ℝ} (hℓ : 0 < ℓ) {B : ℝ} (hB : 0 ≤ B)
    (hprof : ∀ r : ℝ, 0 < r →
      unifE (fun x => (Set.Ioc r (r + 1)).indicator (fun _ => g x)
          (Real.log (g x))) ≤ B / Real.sqrt r) :
    unifMeas {x | ℓ < Real.log (g x)} ≤ 2 * B / (Real.exp ℓ * Real.sqrt ℓ) := by
  classical
  have hs0 : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  -- finitely many bands suffice: `g ≤ 2^n`
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ x, Real.log (g x) ≤ ℓ + J := by
    refine ⟨⌈(n : ℝ) * Real.log 2⌉₊, fun x => ?_⟩
    have h2 : ((2 : ℝ)) ^ n ≠ 0 := by positivity
    have hsum : ∑ x : Cube n, g x = 2 ^ n := by
      rw [unifE, div_eq_iff h2, one_mul] at hmass
      exact hmass
    have hle : g x ≤ 2 ^ n := by
      rw [← hsum]
      exact Finset.single_le_sum (f := g) (fun i _ => (hg i).le) (Finset.mem_univ x)
    calc Real.log (g x) ≤ Real.log ((2 : ℝ) ^ n) := Real.log_le_log (hg x) hle
      _ = n * Real.log 2 := Real.log_pow 2 n
      _ ≤ (⌈(n : ℝ) * Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ℓ + (⌈(n : ℝ) * Real.log 2⌉₊ : ℝ) := by linarith
  -- step 1: cover `{log g > ℓ}` by the bands
  have step1 : unifMeas {x | ℓ < Real.log (g x)}
      ≤ ∑ j ∈ Finset.range (J + 1),
          unifMeas {x : Cube n | Real.log (g x) ∈
            Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)} := by
    have hrw : ∑ j ∈ Finset.range (J + 1),
        unifMeas {x : Cube n | Real.log (g x) ∈
            Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)}
        = unifE (fun x => ∑ j ∈ Finset.range (J + 1),
            Set.indicator {x : Cube n | Real.log (g x) ∈
              Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)} (fun _ => (1 : ℝ)) x) :=
      (unifE_sum _ _).symm
    rw [unifMeas, hrw]
    refine unifE_mono fun x => ?_
    by_cases hx : ℓ < Real.log (g x)
    · have hx' : x ∈ {x : Cube n | ℓ < Real.log (g x)} := hx
      rw [Set.indicator_of_mem hx']
      -- the band index
      have hd0 : 0 < Real.log (g x) - ℓ := by linarith
      have hdJ : Real.log (g x) - ℓ ≤ (J : ℝ) := by linarith [hJ x]
      have hc1 : 1 ≤ ⌈Real.log (g x) - ℓ⌉₊ := Nat.ceil_pos.mpr hd0
      have hcJ : ⌈Real.log (g x) - ℓ⌉₊ ≤ J := Nat.ceil_le.mpr hdJ
      set j : ℕ := ⌈Real.log (g x) - ℓ⌉₊ - 1 with hjdef
      have hjcast : (j : ℝ) = (⌈Real.log (g x) - ℓ⌉₊ : ℝ) - 1 := by
        rw [hjdef, Nat.cast_sub hc1]; norm_num
      have hjlt : (j : ℝ) < Real.log (g x) - ℓ := by
        have := Nat.ceil_lt_add_one (a := Real.log (g x) - ℓ) hd0.le
        rw [hjcast]; linarith
      have hjge : Real.log (g x) - ℓ ≤ (j : ℝ) + 1 := by
        have := Nat.le_ceil (Real.log (g x) - ℓ)
        rw [hjcast]; linarith
      have hjmem : j ∈ Finset.range (J + 1) := Finset.mem_range.mpr (by omega)
      have hband : x ∈ {x : Cube n | Real.log (g x) ∈
          Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)} := by
        constructor <;> linarith
      refine le_trans (le_of_eq ?_)
        (Finset.single_le_sum
          (f := fun j : ℕ => Set.indicator {x : Cube n | Real.log (g x) ∈
            Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)} (fun _ => (1 : ℝ)) x)
          (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x) hjmem)
      exact (Set.indicator_of_mem hband (fun _ => (1 : ℝ))).symm
    · have hx' : x ∉ {x : Cube n | ℓ < Real.log (g x)} := hx
      rw [Set.indicator_of_notMem hx']
      exact Finset.sum_nonneg fun i _ =>
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
  -- step 2: on the `j`-th band, `1 ≤ e^{-(ℓ+j)}·g`
  have step2 : ∀ j : ℕ,
      unifMeas {x : Cube n | Real.log (g x) ∈
          Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)}
        ≤ (B / (Real.exp ℓ * Real.sqrt ℓ)) * Real.exp (-1) ^ j := by
    intro j
    have hr : 0 < ℓ + (j : ℝ) := by positivity
    have hmid : unifMeas {x : Cube n | Real.log (g x) ∈
        Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)}
        ≤ Real.exp (-(ℓ + (j : ℝ))) *
          unifE (fun x => (Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)).indicator
            (fun _ => g x) (Real.log (g x))) := by
      rw [unifMeas, ← unifE_smul]
      refine unifE_mono fun x => ?_
      by_cases hx : Real.log (g x) ∈ Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)
      · have hx' : x ∈ {x : Cube n | Real.log (g x) ∈
            Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)} := hx
        rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
        have h1 : Real.exp (ℓ + (j : ℝ)) < g x :=
          (Real.lt_log_iff_exp_lt (hg x)).mp hx.1
        have h2 : (0 : ℝ) < Real.exp (ℓ + (j : ℝ)) := Real.exp_pos _
        rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ h2]
        linarith
      · have hx' : x ∉ {x : Cube n | Real.log (g x) ∈
            Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)} := hx
        rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
        simp
    refine le_trans hmid ?_
    have hstep : Real.exp (-(ℓ + (j : ℝ))) *
        unifE (fun x => (Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)).indicator
          (fun _ => g x) (Real.log (g x)))
        ≤ Real.exp (-(ℓ + (j : ℝ))) * (B / Real.sqrt (ℓ + (j : ℝ))) :=
      mul_le_mul_of_nonneg_left (hprof _ hr) (Real.exp_pos _).le
    refine le_trans hstep ?_
    have hexp : Real.exp (-(ℓ + (j : ℝ))) = Real.exp (-ℓ) * Real.exp (-1) ^ j := by
      rw [← exp_neg_nat j, ← Real.exp_add, show -ℓ + -(j : ℝ) = -(ℓ + (j : ℝ)) by ring]
    have hsle : Real.sqrt ℓ ≤ Real.sqrt (ℓ + (j : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have hdiv : B / Real.sqrt (ℓ + (j : ℝ)) ≤ B / Real.sqrt ℓ := by
      apply div_le_div_of_nonneg_left hB hs0 hsle
    have hne1 : Real.exp ℓ ≠ 0 := (Real.exp_pos ℓ).ne'
    have hne2 : Real.sqrt ℓ ≠ 0 := hs0.ne'
    calc Real.exp (-(ℓ + (j : ℝ))) * (B / Real.sqrt (ℓ + (j : ℝ)))
        ≤ Real.exp (-(ℓ + (j : ℝ))) * (B / Real.sqrt ℓ) :=
          mul_le_mul_of_nonneg_left hdiv (Real.exp_pos _).le
      _ = (B / (Real.exp ℓ * Real.sqrt ℓ)) * Real.exp (-1) ^ j := by
          rw [hexp, Real.exp_neg]
          field_simp
  -- step 3: sum the geometric series
  calc unifMeas {x | ℓ < Real.log (g x)}
      ≤ ∑ j ∈ Finset.range (J + 1),
          unifMeas {x : Cube n | Real.log (g x) ∈
            Set.Ioc (ℓ + (j : ℝ)) (ℓ + (j : ℝ) + 1)} := step1
    _ ≤ ∑ j ∈ Finset.range (J + 1),
          (B / (Real.exp ℓ * Real.sqrt ℓ)) * Real.exp (-1) ^ j :=
        Finset.sum_le_sum fun j _ => step2 j
    _ = (B / (Real.exp ℓ * Real.sqrt ℓ)) *
          ∑ j ∈ Finset.range (J + 1), Real.exp (-1) ^ j := by
        rw [← Finset.mul_sum]
    _ ≤ (B / (Real.exp ℓ * Real.sqrt ℓ)) * 2 :=
        mul_le_mul_of_nonneg_left (sum_exp_neg_pow_le _)
          (div_nonneg hB (by positivity))
    _ = 2 * B / (Real.exp ℓ * Real.sqrt ℓ) := by ring

/-- **Level transfer**: a weak-type bound at the shifted level `v = (1+u)/2`
upgrades to the level `u` at the cost of the factor `2√2 ≤ 3`. Uses
`√u ≤ (1+u)/2` (AM–GM), whence `log u ≤ 2·log v` and `u ≤ 2v`. -/
private lemma level_transfer {m B u : ℝ} (hu : 1 < u) (hm : 0 ≤ m) (hB : 0 ≤ B)
    (h : (1 + u) / 2 * m * Real.sqrt (Real.log ((1 + u) / 2)) ≤ B) :
    u * m ≤ 3 * B / Real.sqrt (Real.log u) := by
  set v : ℝ := (1 + u) / 2 with hvdef
  have hu0 : (0 : ℝ) < u := by linarith
  have hv1 : 1 < v := by rw [hvdef]; linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hlv : 0 < Real.log v := Real.log_pos hv1
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hsq : Real.sqrt u ≤ v := by
    have h0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
    have h1 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
    rw [hvdef]; nlinarith
  have hlog2 : Real.log u / 2 ≤ Real.log v := by
    have hle := Real.log_le_log (Real.sqrt_pos.mpr hu0) hsq
    rwa [Real.log_sqrt hu0.le] at hle
  have hLle : Real.sqrt (Real.log u) ≤ Real.sqrt 2 * Real.sqrt (Real.log v) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs2 : Real.sqrt 2 ≤ 1.5 := by
    have hle : Real.sqrt 2 ≤ Real.sqrt ((1.5 : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.5)] at hle
  have hL : 0 < Real.sqrt (Real.log u) := Real.sqrt_pos.mpr hlu
  rw [le_div_iff₀ hL]
  calc u * m * Real.sqrt (Real.log u)
      ≤ (2 * v * m) * (Real.sqrt 2 * Real.sqrt (Real.log v)) := by
        refine mul_le_mul ?_ hLle (Real.sqrt_nonneg _) ?_
        · nlinarith
        · nlinarith
    _ = (2 * Real.sqrt 2) * (v * m * Real.sqrt (Real.log v)) := by ring
    _ ≤ (2 * Real.sqrt 2) * B :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ 3 * B := by nlinarith [mul_nonneg (sub_nonneg.mpr hs2) hB]

/-- The strictly positive case of [LGF Theorem 1.1]: for `D : Dat n` and
`u > 1`, `u·λ(P_{t_a}f ≥ u) ≤ C·K_a/√(log u)`. -/
theorem main_of_pos :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (D : Dat n) (u : ℝ), 1 < u →
      u * unifMeas {x | u ≤ biasedConv D.a D.f x}
        ≤ C * Ka D.a / Real.sqrt (Real.log u) := by
  obtain ⟨C₀, hC₀, hband⟩ := fixed_band
  refine ⟨6 * C₀, by linarith, ?_⟩
  intro n D u hu
  have hKa : 0 ≤ Ka D.a := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hgpos : ∀ x, 0 < heatAt D.f D.tA x := fun x => D.fs_pos D.tA_pos.le x
  have hgmass : unifE (heatAt D.f D.tA) = 1 := D.unifE_fs D.tA
  have htA : D.tA = -Real.log D.a := rfl
  have hconv : biasedConv D.a D.f = heatAt D.f D.tA := by
    rw [htA]; exact biasedConv_eq_heatAt D.ha0 D.f
  -- the shifted level
  set v : ℝ := (1 + u) / 2 with hvdef
  have hv1 : 1 < v := by rw [hvdef]; linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hvu : v < u := by rw [hvdef]; linarith
  have hlv : 0 < Real.log v := Real.log_pos hv1
  -- the band hypothesis, in indicator form
  have hprof : ∀ r : ℝ, 0 < r →
      unifE (fun x => (Set.Ioc r (r + 1)).indicator (fun _ => heatAt D.f D.tA x)
        (Real.log (heatAt D.f D.tA x))) ≤ (C₀ * Ka D.a) / Real.sqrt r := by
    intro r hr
    exact hband D r hr
  -- layer cake at level `log v`
  have hlayer := unifMeas_log_gt_le hgpos hgmass hlv (mul_nonneg hC₀.le hKa) hprof
  rw [Real.exp_log hv0] at hlayer
  -- the superlevel set at `u` sits inside `{log f_{t_a} > log v}`
  have hsub : {x : Cube n | u ≤ biasedConv D.a D.f x}
      ⊆ {x : Cube n | Real.log v < Real.log (heatAt D.f D.tA x)} := by
    intro x hx
    have hxg : u ≤ heatAt D.f D.tA x := by rw [hconv] at hx; exact hx
    exact (Real.log_lt_log_iff hv0 (hgpos x)).mpr (by linarith)
  have hA : unifMeas {x : Cube n | u ≤ biasedConv D.a D.f x}
      ≤ 2 * (C₀ * Ka D.a) / (v * Real.sqrt (Real.log v)) :=
    le_trans (unifMeas_mono hsub) hlayer
  -- transfer from level `v` to level `u`
  have hm : (0 : ℝ) ≤ unifMeas {x : Cube n | u ≤ biasedConv D.a D.f x} :=
    unifMeas_nonneg _
  have hpos : 0 < v * Real.sqrt (Real.log v) := by
    have := Real.sqrt_pos.mpr hlv; positivity
  have hA' : v * unifMeas {x : Cube n | u ≤ biasedConv D.a D.f x} *
      Real.sqrt (Real.log v) ≤ 2 * (C₀ * Ka D.a) := by
    have := (le_div_iff₀ hpos).mp hA
    linarith
  have hfin := level_transfer (m := unifMeas {x : Cube n | u ≤ biasedConv D.a D.f x})
    (B := 2 * (C₀ * Ka D.a)) hu hm (by positivity) hA'
  calc u * unifMeas {x : Cube n | u ≤ biasedConv D.a D.f x}
      ≤ 3 * (2 * (C₀ * Ka D.a)) / Real.sqrt (Real.log u) := hfin
    _ = 6 * C₀ * Ka D.a / Real.sqrt (Real.log u) := by ring

/-- **Talagrand's convolution conjecture** [LGF Theorem 1.1], pointwise-in-`f`
form: there is a universal constant `C` such that for every dimension `n`,
bias `0 < a < 1`, level `u > 1`, and probability density `f` on the cube
(`f ≥ 0`, `𝔼_λ f = 1`),
`u·λ({T_{μ_a} f ≥ u}) ≤ C·K_a/√(log u)`. -/
theorem talagrand_convolution_conjecture :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (a u : ℝ) (f : Cube n → ℝ),
        0 < a → a < 1 → 1 < u → (∀ x, 0 ≤ f x) → unifE f = 1 →
        u * unifMeas {x | u ≤ biasedConv a f x}
          ≤ C * Ka a / Real.sqrt (Real.log u) := by
  obtain ⟨C, hC, hmain⟩ := main_of_pos
  refine ⟨3 * C, by linarith, ?_⟩
  intro n a u f ha0 ha1 hu hf hm
  have hKa : 0 ≤ Ka a := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  -- the strictly positive approximation at `ε = 1`
  have hf1pos : ∀ x, 0 < (f x + 1) / 2 := fun x => by linarith [hf x]
  have hf1mass : unifE (fun x => (f x + 1) / 2) = 1 := by
    have hrw : (fun x : Cube n => (f x + 1) / 2)
        = fun x => (1 / 2 : ℝ) * f x + 1 / 2 := by funext x; ring
    rw [hrw, unifE_affine, hm]; norm_num
  -- convolution is affine in `f`
  have hbc : ∀ x : Cube n, biasedConv a (fun x => (f x + 1) / 2) x
      = (biasedConv a f x + 1) / 2 := by
    intro x
    simp only [biasedConv]
    have hterm : ∀ y : Cube n, biasedWeight a y * ((f (x * y) + 1) / 2)
        = biasedWeight a y * f (x * y) / 2 + biasedWeight a y / 2 :=
      fun y => by ring
    rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_div, sum_biasedWeight]
    ring
  -- apply the strictly positive case at the shifted level
  have hD := hmain (⟨a, ha0, ha1, fun x => (f x + 1) / 2, hf1pos, hf1mass⟩ : Dat n)
    ((1 + u) / 2) (by linarith)
  dsimp only at hD
  have hset : {x : Cube n | (1 + u) / 2 ≤ biasedConv a (fun x => (f x + 1) / 2) x}
      = {x : Cube n | u ≤ biasedConv a f x} := by
    ext x
    simp only [Set.mem_setOf_eq, hbc x]
    constructor <;> intro h <;> linarith
  rw [hset] at hD
  -- transfer from level `(1+u)/2` to level `u`
  have hm0 : (0 : ℝ) ≤ unifMeas {x : Cube n | u ≤ biasedConv a f x} :=
    unifMeas_nonneg _
  have hL : 0 < Real.sqrt (Real.log ((1 + u) / 2)) :=
    Real.sqrt_pos.mpr (Real.log_pos (by linarith))
  have hD' : (1 + u) / 2 * unifMeas {x : Cube n | u ≤ biasedConv a f x} *
      Real.sqrt (Real.log ((1 + u) / 2)) ≤ C * Ka a := (le_div_iff₀ hL).mp hD
  have hfin := level_transfer (m := unifMeas {x : Cube n | u ≤ biasedConv a f x})
    (B := C * Ka a) hu hm0 (mul_nonneg hC.le hKa) hD'
  calc u * unifMeas {x : Cube n | u ≤ biasedConv a f x}
      ≤ 3 * (C * Ka a) / Real.sqrt (Real.log u) := hfin
    _ = 3 * C * Ka a / Real.sqrt (Real.log u) := by ring

/-- **Talagrand's convolution conjecture**, `ψ`-form [LGF eq (1.1)]:
`ψ_{μ_a}(u) ≤ C·K_a/√(log u)` for all `0 < a < 1`, `u > 1`, `n`. -/
theorem talagrand_convolution_conjecture_psi :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (a u : ℝ), 0 < a → a < 1 → 1 < u →
        psi a n u ≤ C * Ka a / Real.sqrt (Real.log u) := by
  obtain ⟨C, hC, hmain⟩ := talagrand_convolution_conjecture
  refine ⟨C, hC, ?_⟩
  intro n a u ha0 ha1 hu
  haveI : Nonempty {f : Cube n → ℝ // (∀ x, 0 ≤ f x) ∧ unifE f = 1} :=
    ⟨⟨fun _ => 1, fun _ => zero_le_one, unifE_const 1⟩⟩
  rw [psi]
  exact ciSup_le fun F => hmain n a u F.1 ha0 ha1 hu F.2.1 F.2.2

end Talagrand
