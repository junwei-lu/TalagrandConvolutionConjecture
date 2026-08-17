# SESSION RULES (read first)

THERE IS NO WAKEUP AND NO NOTIFICATION — single non-interactive `claude -p`
run. Stopping tool calls ENDS the session; uncommitted work is swept into an
unverified auto-commit. NEVER background a build or poll/sleep-wait. Run
foreground `lake build`, read output. COMMIT AFTER EACH STEP COMPILES.

# Task: close the single `sorry` in Lemmas/ScoreEnergy.lean — `scoreEnergy_le`

Touch-set: TalagrandConvConjecture/Lemmas/ScoreEnergy.lean ONLY. Statements
frozen. Read CLAUDE.md and the WHOLE FILE first — a previous session proved
`SA_le`, nonnegativity, and helpers (cell sign dichotomy for F, jrate
nonnegativity, influx vanishing). Only `scoreEnergy_le` (= [LGF Lemma 3.5]
first part) remains.

Design (module docstring): pair the flow against
`G t (x,y,alive) = F t x`, `G t (·,·,dead) = ℓ+1+log κ_a`:
`u k t := ∑_s c.π k t s·G t s`. Cell-wise, `hasDerivWithinAt_pairing` +
pointwise: V-moving jumps from alive sources carry total rate `Y_i/2`
(min/max split of sync + V-only recombines — check the existing jrate
helpers), landing value `F t (σ_i x)` (alive) or `ℓ+1+logκ ≥ F t (σ_i x)`
(dead landing needs `F t x < ℓ+1` on the alive support in-cell — use the
alive-support invariant from Flow/Coupling (`cflow_alive_support` is
terminal-only; the IN-CELL version may need re-derivation or use the
cell-invariant helpers in Flow/Coupling if public — if not public, redo the
small argument locally with the sign-dichotomy helper already in this file)
plus `F_flipCoord_sub_of_le` + `Y_le_kappa` + `Real.log` monotonicity.
W-only flips leave `G` unchanged; dead cells: `∂_t G = 0` and sync flips
cancel. So
`d/dt u ≥ ⟨π^{alive}, ∑_i S_i + ½∑_i Y_i log Y_i⟩ = ⟨π^{alive}, ½∑(Y logY - Y + 1)⟩`
(the compensator; use `hasDerivAt_F` for `∂_t G` on alive).
Nodes: transferred states have `F_{z_k}(x) ∈ [ℓ+1 - hmm, ≤ ℓ+1]` by cell
continuity ⟹ `u` increases (`G` jumps from `F ≤ ℓ+1` to `ℓ+1+logκ ≥ F`).
Chain (adapt `chain_le` to the ≥ direction by negation), endpoints:
`u(start) ≥ F θ x₀ ∧ u(start) ≥ min(...)` — case split `x₀ ∈ barrier θ`;
`u(end) ≤ ℓ+1+logκ` (mass 1, alive terminal `F ≤ ℓ+1` via
`cflow_alive_support`, `logκ ≥ 0`). Get
`∫ compensator ≤ Rgap + 1 + logκ` (case split on `Rgap = 0` vs `> 0`).
Conclude with `score_convexity` (PowerCoupling; needs `Y ∈ [κ⁻¹,κ]` from
`Y_le_kappa`/`kappa_inv_le_Y`, `1 < κ` from `one_lt_kappa`) pointwise under
`π ≥ 0`, and cell-wise `intervalIntegral.integral_mono_on` (integrands
continuous on compact cells — continuity of `π` from the flow, of `Y` from
`continuousOn_Y`).

Gate: `lake build TalagrandConvConjecture.Lemmas.ScoreEnergy` — zero sorry.
Commit.

NOTE (added after prompt creation): `D.cflow_alive_cell` is now PUBLIC in
Flow/Coupling.lean — the per-cell alive-support invariant. Use it directly for
the in-cell "alive mass has F ≤ ℓ+1" step (combine with the file's private
`cell_F_le`); do not re-derive it.
