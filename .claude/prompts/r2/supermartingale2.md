# SESSION RULES (read first)

THERE IS NO WAKEUP AND NO NOTIFICATION — single non-interactive `claude -p`
run. Stopping tool calls ENDS the session; uncommitted work is swept into an
unverified auto-commit. NEVER background a build or poll/sleep-wait. Run
foreground `lake build`, read output. COMMIT AFTER EACH STEP COMPILES.

# Task: close the single `sorry` in Lemmas/Supermartingale.lean — `weighted_comparison`

Touch-set: TalagrandConvConjecture/Lemmas/Supermartingale.lean ONLY. Do not
change any statement. Read CLAUDE.md, then READ THE WHOLE FILE FIRST — a
previous session built ALL scaffolding (private helpers `exists_bwdExt`
backward harmonic extension, `NW_*` weight-ratio identities, `jrate_pair_*`
pairing expansions, `bracket_alive` = the AM-GM cell drift inequality,
`bracket_dead` = exact zero dead drift, `grid_*` bookkeeping,
`fwdOf_transpose_pair`, `sum_regroup`). Your job is ONLY the final assembly of
`weighted_comparison` from those helpers, following the module docstring and
the design in the last session's commit messages (`git log --oneline -8`).

Assembly sketch (see file docstring): obtain `H` from `exists_bwdExt` for the
terminal test `h` (H ≥ 0 by the Metzler positivity built into the helper);
define per-cell `u k t := ∑_s c.π k t s · NW ℓ θ x₀ t s · H t s.2.1`; prove
each cell has nonincreasing `u` via `hasDerivWithinAt_pairing` (Flow/Glued or
ODE/LinearFlow — check which name exists) + the pointwise inequality from
`bracket_alive`/`bracket_dead` (multiplied by `π ≥ 0` = `cflow_nonneg`);
node transfers decrease `u` (killTr moves alive→dead at `F ≥ ℓ+1`, and
`NW_false_eq`-type ratio `e^{d(ℓ+1-F)} ≤ 1`, `H ≥ 0`); chain with
`chain_mono` (Flow/Glued); endpoints via `NW_true` at `θ` (`= 1` when
`W = V = x₀`), `Tr 0` kill case `≤ 1`, and `H θ x₀ = ∑ term·h(V)` via
`cflow_V_marginal`. If `weighted_comparison_localized` is already proved from
`weighted_comparison`, don't touch it.

Gate: `lake build TalagrandConvConjecture.Lemmas.Supermartingale` — zero
sorry, statements unchanged. Commit.
