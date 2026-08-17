# SESSION RULES (read first)

THERE IS NO WAKEUP AND NO NOTIFICATION — single non-interactive `claude -p`
run. Stopping tool calls ENDS the session; uncommitted work is swept into an
unverified auto-commit. NEVER background a build or poll/sleep-wait. Run
foreground `lake build`, read output. COMMIT AFTER EACH LEMMA COMPILES.

# Task: close the single `sorry` in FixedBand.lean — `fixed_band` ([LGF Prop 3.2])

Touch-set: TalagrandConvConjecture/FixedBand.lean ONLY. The `fixed_band`
statement is frozen; add private helpers freely. Read CLAUDE.md + the WHOLE
FILE first — proved already: `exists_cflowFamily`, `cflow_term_nonneg`,
`term_V_tail_le`, `sum_term_V_eq_profile`, `exists_profile_vanish`, and the
elementary bounds (`sum_inv_sqrt_le`, `sum_inv_le_one_add_log`,
`log_le_two_mul_sqrt`, `log_le_four_mul_sqrt_sqrt`, `kappa_mul_Lam_le`,
`kappa_sq_Lam_log_le`). Available from other files (all proved or frozen):
`DA_le` (Lemmas/Discrepancy — may still be sorried in your worktree; USE IT
AS A BLACK BOX), `SA_le`+`scoreEnergy_le` (Lemmas/ScoreEnergy — ditto),
`band_contraction`+`Aband_summable` (Lemmas/BandContraction),
`weighted_comparison_localized` etc. (Supermartingale),
`profile_window_integral_le` (Profile; note it yields `∃ C` — extract the
constant ONCE at the top), `Aband_le_profile`, `profile_eq_Aband_add`,
`sum_startW_eq_profile`, `DA_biUnion_le` (Quantities), `dbar`/`Rgap` algebra
(PowerCoupling), `one_le_Ka`/`Ka_sq_eq`/`one_le_Lam`/`Lam_le_kappa`.

Follow the 3-step plan in the module docstring ([LGF §3.1]) precisely:
- Step 1 (active discrepancy): layer decomposition `E_r` (r = 10..m-1,
  `m = ⌊ℓ/2⌋`) + `E_∞`; per-layer `DA_le` + `SA_le`;
  `probA(E_r) ≤ P_r θ = profile (T-θ) ((ℓ-r-1, ℓ-r])`
  (`sum_startW_eq_profile`; `Rgap ∈ [r, r+1) ⟺ F θ x₀ ∈ (ℓ-r-1, ℓ-r]` for
  `r ≥ 10 > 0` — mind `Rgap = max(ℓ - F) 0`). Build the explicit majorant
  `Err θ` (a FINITE sum of profiles at time `T-θ` plus constants) with
  pointwise bound `DA(activeF) + Aband(activeFᶜ) ≤ Err θ` for every
  `θ ∈ [T_o-1, T_o]` and every family `Φ` (get `Φ θ` from
  `exists_cflowFamily` inside the θ-average argument — the bound must hold
  for EVERY choice, so quantify accordingly).
- Step 2 (inactive): near layers (q = -10..1, 12 unit intervals) by
  dropping the terminal condition; far layers by `term_V_tail_le`
  (`e^{ℓ+1-F} ≤ e^{-1-k}`) with the finite cutoff from
  `exists_profile_vanish`-style boundedness (`heatAt_le_pow`-type bound in
  Profile, or the `J`-cutoff pattern from Main.lean's layer cake — mimic).
- Step 3: θ-average. `∫_{T_o-1}^{T_o} Err ≤ c·K/√ℓ` when `ℓ ≥ C·K²` using
  `profile_window_integral_le` per layer (change of variables θ ↦ T-θ:
  `intervalIntegral.integral_comp_...`; window `[tA, tA+1]`, need
  `ℓ-r-1 > 2` ⟸ `r < m = ⌊ℓ/2⌋`, `ℓ ≥ 64`), the elementary sum bounds, and
  the absorption lemmas (`kappa_sq_Lam_log_le` etc.). Then
  `MeasureTheory.exists_le_setAverage` (or `exists_setAverage_le` — check
  direction) on `[T_o-1, T_o]` picks `θ*` with `Err θ* ≤ ∫ Err` — for
  measurability: `Err` is a finite sum of compositions
  `θ ↦ profile f (T-θ) I` = finite sums of indicators of preimages under
  continuous maps (`measurable_profile` in Profile + composition with the
  continuous affine `θ ↦ T-θ`); integrability: bounded (profiles ≤ 1) on a
  finite-measure interval.
  Close the recurrence: for every `r` with `r ≥ C·K²`,
  `profile(band r) ≤ c₃K/√r + ϱ*·∑'_j e^{-j-1}·profile(band (r+j+1))` from
  `band_contraction` at `θ*(r)` + `profile_eq_Aband_add` +
  `Aband_le_profile`; bootstrap via
  `M := sSup ((fun r => √r·profile(band r)) '' Set.Ici (C·K²))`
  (BddAbove from `exists_profile_vanish` + `profile ≤ 1`; nonempty),
  `ϱ* = e^{-4}/((1-e^{-4})(e-1)) < 1` numerically via `Real.exp_one_gt_d9`
  and `Real.exp_lt_exp` (crude `e > 2`: `e^{-4} < 1/16` etc.), conclude
  `M ≤ c₄K` hence the bound for `ℓ ≥ CK²`; the `ℓ < CK²` case is
  `profile ≤ 1 ≤ √C·K/√ℓ` (`profile_le_one` needs `0 ≤ tA` = `tA_pos.le`).

Long file expected; commit each private lemma. STATEMENT-ISSUE + sorry if
something resists; do NOT silently change `fixed_band`.

Gate: `lake build TalagrandConvConjecture.FixedBand` — zero sorry in this
file (upstream sorries in Discrepancy/ScoreEnergy are fine). Commit.
