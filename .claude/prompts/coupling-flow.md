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

# Task: close every `sorry` in Flow/Coupling.lean

Touch-set: TalagrandConvConjecture/Flow/Coupling.lean only. Do not change
statements; you may add private helper lemmas in the file. Read CLAUDE.md.
Use the APIs of Flow/Glued.lean, ODE/LinearFlow.lean, Reverse/Setup.lean,
PowerCoupling.lean, Analysis/PiecewiseFTC.lean freely (their statements are
fixed; some proofs may still be in progress in parallel worktrees — that's
fine).

## Hints

* `exists_admissibleGrid`: the crossing set
  `Zc = {t ∈ [θ, obsT] | ∃ x, D.F t x = ℓ+1}` is finite:
  `F t x = ℓ+1 ⟺ fs (T-t) x = e^{ℓ+1}` (`Real.log` vs `Real.exp`, `fs_pos`),
  and `s ↦ fs s x` is a polynomial in `e^{-s}` with constant coefficient
  `unifE f = 1 ≠ e^{ℓ+1}` (as `ℓ > 0`): use
  `finite_setOf_expPoly_family_eq` (PiecewiseFTC) after writing
  `fs (T-t) x = ∑_y (∏_i (1 + e^{-(T-t)}·toR..)/2)·f y` and expanding the
  product into powers of `e^{-(T-t)}` — a clean way: prove a helper
  `∃ p : Polynomial ℝ, (∀ s, heatAt f s x = p.eval (Real.exp (-s))) ∧
  p.coeff 0 = unifE f` by induction on the sum/product structure (or
  directly: `heatAt f s x = mext f (e^{-s}·toR x)` and `mext` along a line
  is polynomial — build `p` as `∑_y f y·∏(...)` via
  `Polynomial` algebra with `Polynomial.eval_finset_sum`,
  `Polynomial.eval_prod`). Note `e^{-(T-t)} = e^{-T}·e^{t}`; adapt the
  variable (the family lemma is stated for `exp (-t) ^ k` — precompose with
  `t ↦ T - t`, which preserves finiteness via `Set.Finite.preimage` of an
  injective affine map). Then sort `Zc ∪ {θ, obsT}` into an increasing
  enumeration: use `Set.Finite.toFinset` and `Finset.sort (· ≤ ·)`; define
  `z k` = `k`-th element (pad by repeating the last for `k ≥` length).
  `nocross` holds because all crossings are nodes.
* `barrier_const_on_cell`: if membership differed at `t, t'` in the open
  cell, IVT (`intermediate_value_Icc` on the continuous `t ↦ D.F t x`,
  `continuousOn_F` — note `t ≤ obsT < T`) would produce a crossing
  `F = ℓ+1` inside the open cell, contradicting `nocross`. Mind strict vs
  non-strict: membership is `ℓ+1 ≤ F`; if `F t x ≥ ℓ+1 > F t' x` then some
  `t''` between has `F = ℓ+1` (IVT), and `t'' ∈` open cell ✓ contradiction;
  equality case `F t x = ℓ+1` is itself excluded by `nocross`.
* `exists_cflow`: `exists_admissibleGrid` + `exists_gluedFlow`. For the
  cell-generator continuity: `jrate` entries are finite sums of terms
  `if (state conditions) then (continuous function of t) else 0` — the
  conditions do NOT depend on `t` (the barrier is the fixed midpoint
  sample!), except through `D.Y t i x < 1`-style GUARDS — CAREFUL: the
  guards `D.Y t i x < 1` DO depend on `t` and can switch inside a cell,
  making `jrate` discontinuous in `t`!  RESOLUTION: at a switch point
  `Y = 1`, the two branch values agree: sync rate `Y/2 = Y^{1-d}/2 = 1/2`,
  W-only `(1-Y^d)/2 = 0`, V-only `(Y-Y^{1-d})/2 = 0` — so each matrix entry
  is a CONTINUOUS function of `(t, Y)` despite the `if`: prove continuity
  via `Continuous.if` with the frontier-agreement condition
  (`continuous_if` requires the two branches to agree on the frontier of
  the condition set), or rewrite each entry as a `min`/`max`-free
  composition: e.g. sync rate `= min (Y/2) (Y^{1-d}/2)`? (For `Y<1`:
  `Y < Y^{1-d}`? `Y^{1-d} ≥ Y` for `Y ≤ 1` ✓ since exponent `1-d ≤ 1`;
  for `Y ≥ 1`: `Y^{1-d} ≤ Y` ✓. So sync rate `= min(Y, Y^{1-d})/2` ✓
  continuous!) Similarly W-only `= max(1 - Y^d, 0)/2`? For `Y<1`:
  `1-Y^d ≥ 0` ✓; for `Y ≥ 1`: `1 - Y^d ≤ 0` ✓ so
  `max (1-Y^d) 0 / 2` ✓ agrees with the `if` form. V-only
  `= max (Y - Y^{1-d}) 0 / 2` ✓. RECOMMENDED: prove three tiny lemmas
  rewriting the `if`-forms as `min`/`max` forms, then continuity is
  `Continuous.min/max` + `Real.continuous_rpow`-style (base `Y > 0`
  continuous in `t` by `continuousOn_Y`; rpow continuity at positive base:
  `ContinuousOn.rpow_const` with base ≠ 0).
* `cflow_nonneg`: `gluedFlow_nonneg` (rates ≥ 0 → `fwdOf` Metzler via
  `fwdOf_offdiag_nonneg`; `killTr ≥ 0`; init ≥ 0). Rate nonnegativity:
  `Y > 0` (`Y_pos`, `t ≤ obsT ≤ T`), `Y^{1-d} ≤ Y` or `≥`-cases as above,
  `d = dbar ∈ [0, 1/2)` (`dbar_nonneg`, `dbar_lt_half`).
* `cflow_mass`: `gluedFlow_mass`: cell column sums vanish by `fwdOf_col_sum`
  (need `jrate s s = 0`: each summand's state condition forces a coordinate
  flip, impossible for `s' = s` — `flipCoord i x ≠ x` since
  `(flipCoord i x) i = -(x i) ≠ x i` in `ℤˣ`); `killTr` columns sum to 1
  (exactly one target per source). Initial mass: `∑ initVec = 1`.
* `cflow_alive_support`: show the stronger invariant by induction over
  cells: for every cell `k` and `t` in the cell, alive mass vanishes on
  states `x` with `x ∈` (cell barrier) — via `linFlow_unique` applied to the
  subsystem supported off the bad set: concretely, prove that the function
  `π̃ k t s := if s.2.2 = true ∧ s.1 ∈ B_k then 0 else π k t s` is ALSO a
  solution of the same cell ODE with the same initial value (in-rates into
  bad states from good states vanish by the rate design: sync/V-only jumps
  land alive only if the target V-position `∉ B_k`; W-only jumps keep `x`),
  and initial values on bad states are 0 (transfers kill exactly the
  closed-barrier states at the node, and the node barrier ⊇ cell barrier
  near the node… careful: the transfer at `z_k` uses `barrier ℓ (z k)`
  while the cell uses the midpoint barrier `B_k`; these may differ! A state
  in `B_k` but not in `barrier (z k)` (barrier acquired just after the node)
  would carry alive mass at the node — but then `F_{z k}(x) < ℓ+1 ≤
  F_{mid}(x)`, so by IVT there's a crossing in the open cell —
  contradiction with `nocross` UNLESS `F_{z k}(x) = ℓ+1` exactly (allowed:
  node IS the crossing) — then `barrier (z k)` contains x (`≤` is closed:
  `ℓ+1 ≤ F` ✓ equality counts) ✓. So: `B_k ⊆ barrier ℓ (z k)` — prove this
  containment lemma via IVT/`nocross` and closedness; then node transfers do
  clear all of `B_k`.) For the final statement at `t = obsT` with
  `ℓ+1 < F obsT x` (strict): if `x ∉ B_{K-1}` (x alive-allowed in the last
  cell) then by cell-constancy and continuity `F obsT x ≤ ℓ+1` —
  contradiction with strict; so `x ∈ B_{K-1}` and the invariant gives 0.
* `cflow_V_marginal`: chain over cells (`chain_eq` with `φ = 0`, or a direct
  induction): on each cell, `u k t := ∑_s π k t s·g t (s.1)` has zero
  derivative: `hasDerivWithinAt_pairing` + the algebraic identity
  `∑_s (A_k(t) π) s · g t (s.1) = ∑_s π s · (revGen t (g t)) (s.1)`
  — prove this as a pure-algebra lemma about `fwdOf (jrate ...)` applied to
  `x`-only functions: transpose the sum (`Finset.sum_comm`), for each
  source `s` the out-jumps that move `x` (sync + V-only) carry total rate
  `Y_i/2` regardless of branch (`min(Y,Y^{1-d})/2 + max(Y-Y^{1-d},0)/2 =
  Y/2`) and land at `flipCoord i x` in SOME sector — `g` is sector-blind so
  the sector split is invisible; W-only jumps don't change the `g`-value
  (cancel). Then `+ ∑_s π s·∂_t g t (s.1)` cancels by the backward
  hypothesis `hg_deriv`. Node transfers preserve the pairing exactly
  (`killTr` moves mass between sectors at fixed `(x,y)`; `g` sector-blind):
  `∑_s (matVec (killTr) v) s·g(s.1) = ∑_s v s·g(s.1)` — algebra. Conclude
  `u` is constant across the whole grid; evaluate at both ends
  (`init`: `matVec (killTr θ) initVec` still has all mass at V-position
  `x₀`). Mind the `K-1`/range indexing as in `chain_eq`.

Gate: `lake build TalagrandConvConjecture.Flow.Coupling`, zero sorry.
Commit when green.
