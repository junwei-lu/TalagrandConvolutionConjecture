# Task: close every `sorry` in Profile.lean  ([C Lemma 4])

Touch-set: TalagrandConvConjecture/Profile.lean only. Do not change
statements. You may add private helpers in the file. Read CLAUDE.md.
You may USE (as available lemmas) everything stated in Cube/*.lean,
Analysis/*.lean even if their proofs are still `sorry` in your worktree —
they are being proved in parallel; do NOT try to prove them yourself; just
`exact`/`apply` them.

## Hints, following [C, proof of Lemma 4] (§3.5 of ref/Chen/main.tex)

* `profile_nonneg`, `profile_le_one`: indicator ≤ heatAt pointwise, then
  `unifE_mono`, `unifE_smooth` and `hm`.
* `profile_le_ent` (entropy step): with `E = {x | log f_s x ∈ (ℓ, ℓ+1]}` and
  `φ := ℓ·1_E - log(1 + (e^ℓ-1)·λ(E))` (a function on the cube), check
  `𝔼_λ e^φ = 1` (compute the two-valued sum exactly as [C eq (39)]), apply
  `sum_mul_le_ent` with weights `w x = 2^{-n}` and `g = h_s = localizedTest`
  (translate `unifE` sums to `∑ w·(...)`). Then chain (i)–(iii) of
  [C eq (entropy_vs_anti_concentration_profile)]:
  `∫ h_s 1_E = 𝔄_s((ℓ,ℓ+1])` since `χ = 1` on `[0,1]`
  (`cutoff_eq_one`); `∫ h_s ≤ 1`; `λ(E) ≤ e^{-ℓ}𝔄_s`;
  `log(1+x) ≤ x` (`Real.log_le_sub_one_of_pos` on `1+x`); and `ℓ ≥ 2` to
  absorb: `ℓ𝔄 - 𝔄 ≥ (ℓ/2)𝔄`.
* `dirichlet_le_flux_integral` (coarea): pointwise, for each `x, i`:
  `√(h_s(σ_i x)) - √(h_s x) = ψ_ℓ(log f_s(σ_i x)) - ψ_ℓ(log f_s x)` with
  `ψ_ℓ = sqrtTest ℓ` (`√(f·χ(log f - ℓ)²) = e^{(log f)/2}·χ(log f - ℓ)`
  needs `χ ≥ 0` and `f > 0`: `Real.sqrt_eq_iff`/`Real.sqrt_mul`,
  `Real.exp_log`, `Real.sqrt_sq` of nonneg). Apply `sqrtTest_sq_diff_le`,
  translate the `uIoc`-measure factor into
  `∫_{ℓ-1}^{ℓ+2} 1_{e^u ∈ uIoc(f_s x, f_s σ_i x)} du` (the measure of
  `{u ∈ (ℓ-1,ℓ+2) : e^u ∈ uIoc(...)}`; parametrize by `u = log`), and
  `|e^b - e^a| = |Δ_i f_s|` (`Real.exp_log`). Then sum over `i` and average;
  swap `unifE`-sum with the `u`-integral
  (`intervalIntegral.integral_finset_sum`). Constant slack is generous.
* `levelExcess_sub_eq`: fix `u > 0`. `s ↦ levelExcess f s u` is a finite sum
  of `s ↦ max (heatAt f s x - e^u) 0`; off the finitely many crossing times
  (`finite_setOf_expPoly_family_eq` applied to
  `heatAt f s x = mext f (e^{-s}·toR x)`, a polynomial in `e^{-s}` with
  constant coefficient `unifE f = 1 ≠ e^u` — derive the polynomial shape
  from the finite-sum definition of `mext` by multiplying out, or prove a
  small helper `∃ p : Polynomial ℝ, ∀ s, heatAt f s x = p.eval (exp (-s)) ∧
  p.coeff 0 = unifE f`) each term has derivative
  `1_{heatAt > e^u}·∂_s heatAt` (chain rule for `max·` at non-touching
  points; `hasDerivAt_smooth_exp` supplies `∂_s heatAt = cubeLap`). The
  identity `∑_x 1_{f_s(x)>e^u}·cubeLap f_s(x)/2^n = -levelFlux f s u`:
  expand `cubeLap`, pair `x` with `σ_i x` (`sum_comp_flipCoord`), and check
  the sign bookkeeping: contributions cancel unless `e^u` separates
  `f_s(x)` from `f_s(σ_i x)`, in which case the signed sum equals
  `-|Δ_i f_s|·(uIoc indicator)` after symmetrization (this reproduces
  `𝔈(1_{>e^u}, f_s) ≥ 0`, [C eq (derivative_F_s)] and the display after).
  Then `sub_eq_integral_of_finite_exceptions`.
* `flux_time_integral_le_one`: from `levelExcess_sub_eq` on `[0, S]`:
  `∫_0^S levelFlux = levelExcess 0 - levelExcess S ≤ levelExcess f 0 u ≤ 1`
  (`levelExcess ≥ 0`, `levelExcess f 0 u ≤ unifE f = 1` — note
  `heatAt f 0 = f` via `smooth_one` and `Real.exp_zero`).
* `profile_time_integral_le` (master): chain
  `profile ≤ (2/ℓ)·entUnif h_s ≤ (2/ℓ)·(LSI) ≤ (2·256/ℓ)·∫_{ℓ-1}^{ℓ+2} flux du`
  pointwise in `s`; integrate over `s ∈ (0, S]`, swap the `(s,u)` integrals
  (Tonelli for nonneg: work in `ℝ≥0∞` or use
  `intervalIntegral` ↔ set-integral conversions; integrands are bounded
  measurable — `measurable_profile`-style arguments), apply
  `flux_time_integral_le_one` for each `u`, get
  `∫_0^S profile ≤ (512·3)/ℓ`; let `S → ∞` via `lintegral` monotone
  convergence (`MeasureTheory.lintegral_iSup` or
  `iSup` over `S ∈ ℕ`). Choose `C = 4096` say (any explicit constant that
  dominates; adjust freely — only the statement's `∃ C` matters).
* `profile_window_integral_le`: monotonicity of the `lintegral` over
  `Ioc s₁ s₂ ⊆ Ioi 0` + `ofReal`-integral comparisons
  (`MeasureTheory.integral_le_lintegral`-style / 
  `intervalIntegral` of nonneg bounded = `toReal` of the lintegral).
  Mind `s₁ = 0` allowed: `Ioc 0 s₂ ⊆ Ioi 0` still fine (endpoint measure 0).
* `measurable_profile`: finite sum of products
  `continuous (s ↦ heatAt f s x)` × indicator of a Borel condition in `s`
  (preimage of `I` under the continuous `s ↦ log (heatAt f s x)`).

Gate: `lake build TalagrandConvConjecture.Profile`, zero sorry (the file may
still WARN about upstream sorries in imported files — that's fine; only
Profile.lean must be sorry-free). Commit when green.
