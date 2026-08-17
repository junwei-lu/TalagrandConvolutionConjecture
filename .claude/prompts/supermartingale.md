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

# Task: close every `sorry` in Lemmas/Supermartingale.lean

Touch-set: TalagrandConvConjecture/Lemmas/Supermartingale.lean. Do not
change statements; private helpers welcome. Read CLAUDE.md and the module
docstring (the `N`-weighted design and its deviation note). Use stated APIs
from Flow/*, Reverse/Setup, PowerCoupling (in-progress proofs elsewhere are
fine to use).

## Proof of `weighted_comparison` ([LGF Prop 4.1], N-form)

Let `d := dbar ℓ θ x₀`, and let `H : ℝ → Cube n → ℝ` be the backward
harmonic extension of `h` for the reverse dynamics **in the `W`-slot**:
obtain from `exists_linFlow` time-reversed (as in the score-energy/marginal
files): `∂_t H_t = -L̃_t H_t` on `[θ, obsT]`, `H obsT = h`. Positivity
`H ≥ 0`: `linFlow_nonneg` on the reversed flow (the reversed generator is
Metzler: off-diagonal entries `Y_i/2 ≥ 0`).

Pair `u k t := ∑_s c.π k t s · NW ℓ θ x₀ t s · H t s.2.1`, apply
`hasDerivWithinAt_pairing` (test `g t s := NW t s·H t (s.2.1)`;
differentiate `NW` via `hasDerivAt_F` and `Real.exp`: 
`∂_t NW t (x,y,alive) = NW·(∑Sc t · y-args − (1-d)∑Sc t · x-args)` etc.).

Key pointwise cell inequality (`π ≥ 0`): for alive source `(x,y)` off the
cell barrier,
`⟨A_k-column, NW·H⟩ + π·∂_t(NW·H) ≤ 0` coordinatewise; this is exactly the
computation of [LGF, proof of Prop 4.1]:
* synchronized flip (rate `min(Y,Y^{1-d})/2`, landing multiplier
  `NW(post)/NW(pre)`): alive landing: multiplier `= X_i/Y_i^{1-d}` where
  `X_i = Y t i y` (ratio at the W-position) — from
  `F t (σ_i y) - F t y = log X_i` and `F t (σ_i x) - F t x = log Y_i`;
  dead landing: multiplier `= (X_i/Y_i^{1-d})·e^{d(ℓ+1-F t (σ_i x))} ≤
  X_i/Y_i^{1-d}` (landing has `F t (σ_i x) ≥ ℓ+1` in-cell). Use `H ≥ 0`
  to keep the inequality direction when replacing dead-landing terms by
  alive-form terms.
* W-only flip (`Y<1`, rate `(1-Y^d)/2`): multiplier `X_i`.
* V-only flip (`Y≥1`, rate `(Y-Y^{1-d})/2`): multiplier `Y_i^{-(1-d)}`
  (alive landing) resp. `≤` that (dead landing).
* Summing, per coordinate `i`, the weighted `W`-flip coefficient is exactly
  `X_i/2` — the "restored rate" identities of [LGF, proof of Prop 4.1]:
  `Y<1`: `(Y/2)(X/Y^{1-d}) + ((1-Y^d)/2)X = X/2·(Y^d + 1 - Y^d) = X/2`
  — WAIT recompute: `(Y/2)·X/Y^{1-d} = (X/2)·Y^d` ✓ plus `(1-Y^d)/2·X`
  ✓ total `X/2` ✓. `Y≥1`: `(Y^{1-d}/2)·X/Y^{1-d} = X/2` ✓ (V-only jumps
  contribute to the `H`-slot nothing since `y` unchanged, but to the drift
  defect via the multiplier `Y^{-(1-d)}`).
  The remaining (non-`H`-moving) terms sum to the drift defect
  `-½∑_i[(1-d) + d·Y_i - Y_i^d]·NW·H ≤ 0` by
  `rpow_le_one_sub_add_mul` (PowerCoupling) — redo [LGF]'s one-coordinate
  computation:
  relative drift `= w_i - (1-d)v_i + (Y/2)(X/Y^{1-d} - 1) + ((1-Y^d)/2)(X-1)`
  with `v = (1-Y)/2, w = (1-X)/2`, which simplifies (`ring_nf`) to
  `X/2·(coefficient) - ½[(1-d) + dY - Y^d]` where the `X`-part is the
  restored-rate part matching `-L̃H` in the `W`-slot; the backward equation
  `∂_t H = -L̃H` (with rates `X_i/2` at the W-position!) cancels it.
  Follow [LGF, eq (4.13)-(4.14)]. For dead sources: multiplier `X/Y`,
  drift `∑Sc(y)-∑Sc(x)`, same cancellation, defect ZERO.
* Node transfers DECREASE `u`: transferred states multiply `NW` by
  `e^{d(ℓ+1-F_{z_k}(x))} ≤ 1` (transferred states satisfy
  `F_{z_k}(x) ≥ ℓ+1`), and `H ≥ 0`.

Chain with `chain_mono` (Flow/Glued). Endpoints:
`u(end) = ∑_s NW obsT s·term s·h(s.2.1)` ✓ (H obsT = h);
`u(start)`: after `Tr 0`: if `x₀ ∉ barrier`: mass at `(x₀,x₀,alive)` with
`NW θ = exp(F θ x₀ - (1-d)F θ x₀ - d·F θ x₀) = exp 0 = 1`, so
`u(start) = H θ x₀`; if `x₀ ∈ barrier`: dead with
`NW θ (x₀,x₀,dead) = exp(d(ℓ+1-F θ x₀)) ≤ 1` (then `F θ x₀ ≥ ℓ+1`), so
`u(start) ≤ H θ x₀` — good either way.
Finally `H θ x₀ = ∑_s term s·h s.1` by `cflow_V_marginal` (the backward
extension qualifies as its `g`). Conclude.

* `weighted_comparison_localized`: sum the per-`x₀` inequality with
  nonnegative weights `startW`.
* `NW_ge_on_crossing`: unfold `NW`; two sectors:
  alive: exponent `> (ℓ+j) - (1-d)(ℓ+1) - d(ℓ - R) = j - 1 + d(R+1)
  = j - 1 + α` using `F θ x₀ = ℓ - Rgap` (valid on the active set since
  `Rgap ≥ 2α > 0` forces `Rgap = ℓ - F θ x₀`) and
  `dbar_mul_Rgap_add_one`; dead: exponent
  `≥ (ℓ+j) - (ℓ+1) + d(ℓ+1 - (ℓ-R)) = j - 1 + d(R+1)` ✓ same. `Real.exp`
  monotone. (`alphaC = 5`.)

Gate: `lake build TalagrandConvConjecture.Lemmas.Supermartingale`, zero
sorry. Commit when green.
