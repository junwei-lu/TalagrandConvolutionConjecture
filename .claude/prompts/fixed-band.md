# SESSION RULES (read first)

THERE IS NO WAKEUP AND NO NOTIFICATION — this is a single non-interactive
`claude -p` run. If you stop issuing tool calls the session ENDS IMMEDIATELY
and every uncommitted line is swept into an unverified auto-commit. A previous
attempt at a task like this was lost exactly that way (its last line was
"I'll wait for the background waiter to notify me — standing by."). NEVER
say you are waiting for anything; there is nothing that can wake you.

- Run every `lake build` in the FOREGROUND and read its output directly.
  NEVER background a build (`&`), never poll with `until pgrep ...` loops,
  never `sleep` while "waiting" for a build.
- Builds are fast here (shared Mathlib cache): `lake build <YourModule>`
  rebuilds only your files and their few project deps.
- COMMIT AFTER EACH LEMMA COMPILES (git add the touched files + commit with
  a one-line message). Do not batch all work into one final commit.
- Before ending: run the gate build one final time in the foreground, ensure
  it is green, commit everything, and print a 5-line summary. Then stop.
- Keep each response bounded (~150 lines); long tool outputs are fine.

# Task: close every `sorry` in FixedBand.lean  ([LGF Proposition 3.2])

Touch-set: TalagrandConvConjecture/FixedBand.lean. Do not change statements;
private helpers welcome (in-file). Read CLAUDE.md and the module docstring.
Use the stated APIs of ALL Lemmas/* files, Flow/*, Profile.lean,
PowerCoupling.lean, Reverse/Setup.lean (their proofs may be in progress in
parallel — apply the statements).

## Hints ([LGF §3.1, proof of Prop 3.2])

* `exists_cflowFamily`: `exists_cflow` + choice (`Classical.choice` per
  `x₀`, e.g. `fun x₀ => (D.exists_cflow ℓ hℓ hθ0 hθ x₀).some`).
* `term_V_tail_le`: `cflow_V_marginal` applied to
  `g t x := Real.exp (-(D.F t x))` (backward-harmonic:
  `hasDerivAt_exp_neg_F` gives `∂_t g = -(revGen g)` — convert `HasDerivAt`
  to `HasDerivWithinAt`; continuity from differentiability) yields
  `∑ term·e^{-F obsT (V)} = e^{-F θ x₀}`. Chebyshev pointwise:
  `1_{F ≤ c} ≤ e^{c}·e^{-F}` (`Real.exp_le_exp`, `Real.exp_log`…), multiply
  by `term ≥ 0` (`cflow_nonneg`) and sum; `Real.exp_sub`.
* `sum_term_V_eq_profile`: as described in the score-energy prompt's
  Quantities part (backward extension of the indicator via reversed
  `exists_linFlow`; `cflow_V_marginal`; pairing constancy with
  `revDensity`; `T - obsT = tA`). If the same private lemma was already
  proved in Lemmas/Quantities.lean, refactor is NOT allowed (touch-set!) —
  just reprove locally or `exact` it if it happens to be public.
* `exists_profile_vanish`: take
  `B := (Finset.univ.image (fun x => D.F obsT x)).max' + 1`-style bound
  (cube nonempty? for `n = 0` also fine — `Finset.univ.Nonempty` since
  `Cube n` is inhabited); if `log (heatAt f tA x) = F obsT x ≤ B - 1 < r`
  for all `x`, the indicator in `profile` is 0 everywhere.
* `fixed_band`: the big assembly. Structure:
  - Obtain the universal constants: `C₄` from `profile_window_integral_le`
    ([C Lemma 4]), `C_D` from `DA_le`.
  - Fix `D, ℓ`. Set `κ := kappa D.a`, `Λ := Lam D.a`, `K := Ka D.a`.
    Facts: `1 < κ` (`one_lt_kappa`), `1 ≤ Λ ≤ κ` (`one_le_Lam`,
    `Lam_le_kappa`), `1 ≤ K` (`one_le_Ka`), `K² = κ³Λ` (`Ka_sq_eq`).
  - Case `ℓ ≤ C·K²` (with the big `C` chosen at the end): trivial:
    `profile ≤ 1 ≤ √(C·K²)/√ℓ·1 ≤ C'·K/√ℓ` (`profile_le_one`,
    `Real.sqrt` monotone; note `K ≥ 1`).
  - Case `ℓ > C·K²` (so in particular `ℓ ≥ 64`, ensured by `C ≥ 64`):
    For each `θ ∈ [T_o-1, T_o]` pick `Φ θ` — you need a FAMILY of families
    measurable in θ?? NO: the mean-value trick avoids it. Define the
    EXPLICIT majorant `Err : ℝ → ℝ` (a function of `θ` only through
    `startW`-sums = profiles at time `T-θ`):
    `Err θ := c₁·[ ∑_{r=10}^{m-1} (K/√(r+1) + κ²Λ/(r+1) + κ²Λ²/(r+1)²)·P_r θ
                 + (K/√ℓ + κ²Λ/ℓ + κ²Λ²/ℓ²)
                 + ∑_{q} P^near_q θ + ∑_{k} e^{-1-k}·P^far_k θ ]`
    where `P_r θ := ∑_{x₀ : F θ x₀ ∈ (ℓ-r-1, ℓ-r]} startW θ x₀
    = profile D.f (T-θ) ((ℓ-r-1, ℓ-r])` (`sum_startW_eq_profile`!),
    `m := ⌊ℓ/2⌋`, near-layers `q = -10…1`, far-layers `k ∈ ℕ` cut at the
    vanishing bound (use `exists_profile_vanish`-style boundedness or keep
    the tsum finite via geometric domination).
    Steps, for EVERY θ in `[T_o-1, T_o]` and any family `Φ`:
    (1) [Step 1] `DA Φ (activeF) ≤` (layer decomposition `DA_biUnion_le`
    over `E_r := {x₀ : r ≤ Rgap < r+1}` for `10 ≤ r < m` and
    `E_∞ := {Rgap ≥ m}`; per-layer `DA_le` + `SA_le` + `probA(E_r) = P_r θ`
    (`Rgap ∈ [r, r+1) ⟺ F θ x₀ ∈ (ℓ-r-1, ℓ-r]` for `r > 0`;
    `√(xy) ≤ √x√y`, `√(u+v) ≤ √u+√v`, `√(κ-1) ≤ κ`, `probA ≤ 1` for E_∞,
    `Rgap ≥ m ⟹ 1/(R+1) ≤ 1/m ≤ 2/ℓ`…) — bound by the Err-θ pieces.
    (2) [Step 2] `Aband Φ (activeFᶜ) ℓ ≤ ∑_near P^near + ∑_far e^{-1-k}P^far`:
    inactive means `Rgap < 2α = 10` i.e. `F θ x₀ > ℓ - 10`; near region
    `F θ x₀ ≤ ℓ + 2` covered by 12 unit layers (each with V-band mass
    `≤ startW`-mass: drop the terminal condition); far region
    `F θ x₀ ∈ (ℓ+2+k, ℓ+3+k]`: terminal band `(ℓ,ℓ+1]` forces
    `F(V_{T_o}) ≤ ℓ+1`, apply `term_V_tail_le` with `cLev = ℓ+1`:
    conditional mass `≤ e^{ℓ+1-F θ x₀} ≤ e^{-1-k}`.
    (3) [Step 3] `profile_eq_Aband_add` + `band_contraction` give, for every
    θ and Φ:
    `profile(band ℓ) ≤ Err-pieces(θ) + (c₀/(1-c₀))·∑'_j e^{-j}·profile(band ℓ+j)`
    (using `Aband ≤ profile` for the future bands, `Aband_le_profile`;
    `1 - c₀ > 0`: `c₀ = e^{-4} < 1`: `Real.exp_lt_one` for negative arg).
  - Mean value in θ: `Err` is measurable (finite sums of
    profile-compositions: `measurable_profile` composed with the continuous
    `θ ↦ T - θ` — or argue via `sum_startW_eq_profile` and measurability of
    each indicator-sum directly), bounded, and
    `∫_{T_o-1}^{T_o} Err ≤ c₂·K/√ℓ`: each `∫ P_r θ dθ =
    ∫_{tA}^{tA+1} profile (band (ℓ-r-1)) ≤ C₄/(ℓ-r-1) ≤ 2C₄/ℓ` for
    `r < m` (change of variables θ ↦ T-θ:
    `intervalIntegral.integral_comp_sub_left`-family; `ℓ-r-1 ≥ ℓ/2 - 1 ≥ 2`
    needs `ℓ ≥ 8`… careful arithmetic; `T-(T_o) = tA ≥ 0` and window length
    1 ✓ `profile_window_integral_le` applies since `ℓ-r-1 > 2`); sums:
    `∑_{r<m} 1/√(r+1) ≤ 2√m ≤ 2√ℓ`, `∑ 1/(r+1) ≤ 1 + log ℓ`-bound
    (dominate by `∑_{r<m} 1/(r+1) ≤ m`? too lossy — use the harmonic bound
    via comparison with `∫`; Mathlib: `Finset.sum_div`… simplest: prove
    `∑_{r ∈ range m} 1/(r+1) ≤ 1 + Real.log m` by induction with
    `Real.add_one_le_exp`/`Real.log` bounds, or use
    `Real.add_pow…`; there may be `harmonic` series bounds in Mathlib —
    search `harmonic`), `∑ 1/(r+1)² ≤ 2` (`Finset.sum_range_le`… classic:
    `1/(r+1)² ≤ 1/(r(r+1)) = 1/r - 1/(r+1)` telescoping for `r ≥ 1`).
    Then absorb the lower-order terms using `ℓ ≥ C·K²`:
    `κ²Λ·(1+log ℓ)/ℓ ≤ c·K/√ℓ` ⟺ `κ²Λ(1+log ℓ) ≤ cK√ℓ`: from
    `K² = κ³Λ`: `κ²Λ = K²/κ ≤ K²` and `(1+log ℓ)/√ℓ ≤ c'/√C`-type bounds
    (`x ↦ log x/√x` bounded by `2/e`-ish: prove `log x ≤ 2√x`… i.e.
    `Real.log_le_sub_one_of_pos` on `√x`: `log x = 2 log √x ≤ 2(√x - 1) ≤
    2√x` ✓ clean!). Follow [LGF eq (3.11)-(3.13)] but with generous
    constants — everything is `∃ C`.
    Then `∃ θ*` with `Err θ* ≤ ⨍ Err ≤ c₂K/√ℓ`
    (`MeasureTheory.exists_le_setAverage` on `[T_o-1,T_o]`, measure 1;
    integrability: bounded measurable on finite measure).
  - Instantiate `Φ := (exists_cflowFamily … θ*).some`, plug into (3) at θ*,
    get the recurrence
    `profile(band r) ≤ c₃K/√r + ϱ*·(sup-form)` for EVERY `r ≥ C·K²`
    — NOTE the recurrence must hold for all such `r` (rerun the whole
    argument with `ℓ := r`), so structure the proof as: first prove
    `key : ∀ r ≥ C·K², profile(band r) ≤ c₃·K/√r +
      (c₀/(1-c₀))·∑'_j e^{-j}·profile(band (r+j))`.
  - Bootstrap: let `M := ⨆ r : ℝ, if C·K² ≤ r then √r·profile(band r) else 0`
    — or cleaner: `M := sSup ((fun r => √r·profile (band r)) ''
    (Set.Ici (C·K²)))`; bounded above (`profile ≤ 1`, and vanishing beyond
    `B` by `exists_profile_vanish` so `√r·profile ≤ √(max…)`: BddAbove via
    the explicit bound `√(B+1+C·K²… )`? — simplest: `√r·profile(band r) ≤
    √B'` where `B'` bounds the support: for `r ≤ B'` use `profile ≤ 1`;
    for `r > B'`, value 0). Nonempty image ✓. From `key`:
    `√r·profile(band r) ≤ c₃K + ϱ*·∑' e^{-j}·√r·profile(band (r+j))
    ≤ c₃K + ϱ*'·M` with
    `ϱ*' = (c₀/(1-c₀))·∑'e^{-j}·(√r/√(r+j) ≤ 1)·…` — use
    `√r ≤ √(r+j)` and `∑'_{j≥1} e^{-j} = e⁻¹/(1-e⁻¹) = 1/(e-1)`
    (`tsum_geometric_of_lt_one`); numeric: `ϱ* := e^{-4}/((1-e^{-4})(e-1))
    < 1/15` — prove with `Real.exp_one_gt_d9`-style bounds or crude
    `2 < e < 3`: `e^{-4} < 1/16`, `1-e^{-4} > 15/16`, `e-1 > 1`.
    `csSup`-manipulation (`Real.iSup`/`csSup_le`, `le_csSup`) yields
    `M ≤ c₃K + ϱ*M` hence `M ≤ c₃K/(1-ϱ*)`. Conclude for each
    `r ≥ CK²`: `profile ≤ M/√r ≤ c₄K/√r`.
  - Combine cases into the single `∃ C`.

This is a long file (1000+ lines with helpers) — proceed lemma by lemma,
committing intermediate progress. If a statement fails, mark
`-- STATEMENT-ISSUE` and continue.

Gate: `lake build TalagrandConvConjecture.FixedBand`, zero sorry. Commit.
