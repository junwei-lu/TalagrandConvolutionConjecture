# SESSION RULES (read first)

THERE IS NO WAKEUP AND NO NOTIFICATION — single non-interactive `claude -p`
run. Stopping tool calls ENDS the session; uncommitted work is swept into an
unverified auto-commit. NEVER background a build or poll/sleep-wait. Run
foreground `lake build`, read output. COMMIT AFTER EACH LEMMA COMPILES.

# Task: close the single `sorry` in Lemmas/Discrepancy.lean — `DA_le` ([LGF Lemma 3.3])

Touch-set: TalagrandConvConjecture/Lemmas/Discrepancy.lean ONLY. The `DA_le`
statement is frozen. You MAY add private helpers. Read CLAUDE.md and the
WHOLE FILE first — proved already: `Utest_obsT`, `hasDerivAt_Utest` (guard
`ht : t < D.T`), `term_V_eq_Utest_diag`, `abs_pert_Utest_le`
([LGF eq (4.17)] pointwise), `bpart_Gam_le`, discrete Cauchy-Schwarz helpers
(`cs_sq`, `sum_le_sqrt_mul_sqrt`, `sq_weighted_le`). Also available:
`hasDerivAt_qB_sq` (Bridge; guard `t ≠ D.T`), `conditioned_power_bound`
(PowerCoupling), `weighted bridge estimate lam_mul_bB_sq_le` (Bridge),
`level_one` (Cube/LevelOne), `chain_eq` (Flow/Glued), `cflow_*`
(Flow/Coupling), `abs_Dtest_le_DA`/`exists_DA_eq`/`DA_biUnion_le`
(Lemmas/Quantities), `SA` defs. Follow the plan in the module docstring +
[LGF §4.1] (ref/main/main.tex, in the repo parent — if not present in the
worktree, the docstrings carry the full plan).

Assembly ([LGF proof of Lemma 3.3]):
1. Fix `A ⊆ activeF`, pick the optimal test `B` via `exists_DA_eq`; set
   `φ = indicator B` (`{0,1}`-valued).
2. Duhamel: per `x₀ ∈ A`, chain `u k t := ∑_s π k t s·Utest φ t s.1 s.2.1`
   with `chain_eq`: cell derivative = alive perturbation term (the
   synchronized parts cancel against `∂_t U` = `hasDerivAt_Utest`; the
   dead sector is purely synchronized). Mind `t < D.T` inside cells
   (`t ≤ obsT < T`). Endpoints: `u(end) = 𝔼_{x₀}[φ(W)]` (`Utest_obsT`),
   `u(start) = 𝔼_{x₀}[φ(V)]` (`term_V_eq_Utest_diag` + `killTr` initial
   handling — diagonal `Utest θ x₀ x₀` unchanged by the sector).
3. Bound the cell integrand by `abs_pert_Utest_le`, then Cauchy–Schwarz in
   time and in `x₀` (`sum_le_sqrt_mul_sqrt`) to get
   `|∑_A startW·Dtest| ≤ √8·√κ·Λ·√(SA)·√(Y_A)` with a private
   `Y_A := ∑_A startW·∑_k ∫_{cell} ⟨π, Γ φ t (V,W)⟩` (define it; `Γ = Gam`).
4. `Y_A` closure [LGF eq (4.19)-(4.21)]: split `Gam` into `aB²`+`bB²` parts.
   `bB²`-part ≤ `κ/4·probA·(length ≤ 1)` by `bpart_Gam_le` + mass
   (`cflow_mass`) + `T_o - θ ≤ 1` (from `obsT - 1 ≤ θ`). `aB²`-part: chain
   `v k t := ∑_s π k t s·(∑_ζ Hlik t ζ s.1·qB φ t ζ s.1 s.2.1 ^ 2)` with
   `chain_eq`; cell derivative = `2·(aB²-part integrand) + (perturbation on
   H·q²)` via `hasDerivAt_qB_sq` + `hasDerivAt_Hlik` and the SAME
   recombination algebra as in `hasDerivAt_Utest`'s proof (mimic it);
   endpoints ∈ [0, probA] (`0 ≤ qB ≤ 1` from `mext_mem_Icc` +
   `abs_mB_le_one`, `sum_Hlik`, mass). Bound the `H·q²` perturbation by
   `2×` the `abs_pert_Utest_le`-type bound (`|Δ(q²)| ≤ 2|Δq|` since
   `q ∈ [0,1]` — the same coefficient allocation; you may need a `q²`
   variant of the pointwise bound — prove it as a private lemma reusing the
   same skeleton). Get `Y_A ≤ C₁(κ·probA + √κΛ√(SA·Y_A))`; solve by Young
   (`ab ≤ a²/2 + b²/2` calibrated) to `Y_A ≤ C₂(κ·probA + κΛ²·SA)`.
5. Substitute back; `√(x+y) ≤ √x + √y` (prove or find), `√κ√κ = κ`,
   assemble the `∃ C` with a generous explicit constant (e.g. C = 64).
   Watch: `SA ≥ 0` (`SA_nonneg`), `probA ≥ 0`.

This is the hardest remaining file; work incrementally, commit each helper.
If a statement resists, leave `sorry` + `-- STATEMENT-ISSUE` and continue.

Gate: `lake build TalagrandConvConjecture.Lemmas.Discrepancy` — zero sorry.
Commit.
