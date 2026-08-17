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

# Task: close every `sorry` in Lemmas/Quantities.lean and Lemmas/ScoreEnergy.lean

Touch-set: TalagrandConvConjecture/Lemmas/Quantities.lean,
TalagrandConvConjecture/Lemmas/ScoreEnergy.lean. Do not change statements;
private helpers welcome. Read CLAUDE.md. Use all stated APIs from
Flow/Coupling.lean, Flow/Glued.lean, Reverse/Setup.lean, PowerCoupling.lean,
Profile.lean (proofs may be in progress elsewhere — just apply the
statements).

## Quantities.lean hints

* `abs_Dtest_le_DA` / `exists_DA_eq`: set
  `μ w := ∑_{x₀∈A} startW·(W-terminal mass at w)`,
  `ν w := ∑_{x₀∈A} startW·(V-terminal mass at w)`; then
  `∑_{x₀} startW·DtestF (Φ x₀) B = ∑_{w∈B} (μ w - ν w)` (swap sums; the
  `if `-sums select `w`). Since `∑_w μ w = ∑_w ν w` (both are
  `∑_{x₀∈A} startW·(total mass) = probA`; use `cflow_mass` — mind that
  `∑_s term s·(∑_w if s.2.1 = w …)` telescopes), the classical fact
  `|∑_{w∈B}(μ-ν)| ≤ ½∑_w|μ-ν|` holds for every `B`, with equality at
  `B* = {w | ν w < μ w}`: prove via
  `∑_{B}(μ-ν) = ∑_B (μ-ν)⁺ - ∑_B (μ-ν)⁻ ≤ ∑_univ (μ-ν)⁺` and
  `∑(μ-ν)⁺ = ∑(μ-ν)⁻ = ½∑|μ-ν|` (from `∑(μ-ν) = 0`;
  `abs = pos-part + neg-part`).
* `DA_biUnion_le`: triangle inequality for the inner absolute values
  (`Finset.abs_sum_le_sum_abs` after swapping the `x₀`-sum into the
  biUnion decomposition `Finset.sum_biUnion` with disjointness).
* `Aband_nonneg`: `cflow_nonneg` at the terminal cell + nonneg summands
  (`startW ≥ 0` from `fs_pos`).
* `Aband_le_profile` and `profile_eq_Aband_add`: both follow from
  `sum_term_V_eq_profile` (stated in FixedBand.lean — it is in your import
  closure? NO: FixedBand imports these files, not vice versa. So prove the
  needed identity here as a private lemma, or note that
  `Aband Φ univ r = profile ...` : prove a PRIVATE copy
  `private lemma sum_term_V_eq_profile'` in Quantities.lean with the proof
  below, and use it; FixedBand's public version can then be closed by the
  fixed-band agent using the same technique — do NOT import FixedBand.)
  Technique for `∑_{x₀} startW θ x₀·(V-terminal pairing with 1_{F∈I})
  = profile D.f D.tA I`:
  (1) Build the backward harmonic extension `g` of the indicator: obtain it
  from `exists_linFlow` run backwards: define `g` via the flow of the
  time-reversed ODE `d/ds w = revGen-adjoint`… concretely: apply
  `exists_linFlow` on `[θ, obsT]` to the generator
  `Abwd t := ` (matrix of `-revGen (θ+obsT-t)`)… simplest: get
  `w : ℝ → Cube n → ℝ` with `w' r = (matrix of revGen (θ+obsT-r)) applied`,
  `w θ = indicator`, then `g t x := w (θ+obsT-t) x` satisfies
  `∂_t g = -revGen t g` and `g obsT = indicator`. Check the matrix of
  `revGen` is continuous (`continuousOn_Y`).
  (2) `cflow_V_marginal` gives per-`x₀`:
  `(V-terminal pairing) = g θ x₀`.
  (3) `∑_{x₀} startW θ x₀ · g θ x₀ = ∑_x revDensity obsT x·g obsT x`
  (pairing of the explicit forward density with the backward solution is
  constant in `t`: differentiate `t ↦ ∑_x revDensity t x·g t x` using
  `hasDerivAt_revDensity` + the `g`-ODE; the cross terms cancel by
  transposing the `revFwdMat` sum — algebra lemma:
  `∑_x (∑_{x'} revFwdMat t x x'·v x')·g x = ∑_x v x·(revGen t g x)`;
  then `HasDerivAt` constant + `Constant`-from-zero-derivative on
  `[θ, obsT]`).
  (4) `revDensity obsT x = fs tA x/2^n` (`T - obsT = tA`) and the pairing
  with the indicator of `{log fs tA ∈ I}` IS `profile D.f D.tA I` — unfold
  `profile`, `unifE`, `F obsT x = log (fs tA x)`.
* `sum_startW_eq_profile`: direct unfolding: LHS
  `= ∑_{x₀} 1_{F θ x₀ ∈ I}·fs (T-θ) x₀/2^n = profile D.f (T-θ) I`
  (`F θ = log fs (T-θ)`; `heatAt = fs`). Pure rewriting.

## ScoreEnergy.lean hints (see the module docstring for the design)

* `scoreEnergy_le`: Fix the flow `c`. Define the cell-wise scalar
  `u k t := ∑_s c.π k t s·G t s` with
  `G t (x,y,alive) = D.F t x`, `G t (·,·,dead) = ℓ+1+log κ_a`.
  On each cell, `hasDerivWithinAt_pairing` + the pointwise inequality
  `⟨A_k π, G⟩ + ⟨π, ∂_t G⟩ ≥ ⟨π^{alive}, ½∑_i(Y log Y + 1 - Y)⟩` where
  `π ≥ 0` (`cflow_nonneg`): expand `fwdOf (jrate ...)`; for alive sources
  the `V`-moving jumps carry total rate `Y_i/2` and land at `G`-value
  either `F t (σ_i x)` (alive landing) or `ℓ+1+logκ ≥ F t (σ_i x)` (dead
  landing: the landing is in the cell barrier… WAIT, we need
  `F t (σ_i x) ≤ ℓ+1+logκ` for the INEQUALITY DIRECTION: dead landings
  REPLACE `F(σ_i x)` by the LARGER `ℓ+1+logκ`?? Check the needed direction:
  we want `d/dt u ≥ ⟨π^a, compensator⟩`, i.e. dead-landing terms
  `rate·(G(dead) - F(x)) ≥ rate·(F(σ_i x) - F(x))`, i.e.
  `ℓ+1+logκ ≥ F t (σ_i x)`: the source is alive so `F t x < ℓ+1`
  (alive-support — the in-cell version: alive mass sits only off the cell
  barrier where `F < ℓ+1` on the open cell; at endpoints `≤ ℓ+1`;
  to keep it simple prove the inequality with `π^{alive}` supported off
  `B_k` — you may multiply by the indicator using the support lemma) and
  `F t (σ_i x) = F t x + log Y_i ≤ ℓ+1+logκ` (`F_flipCoord_sub`,
  `Y_le_kappa`, `Real.log_le_log`). W-only jumps: `G` unchanged (alive
  target, same `x`) — contribute 0. Dead-internal: `G` constant — 0.
  `∂_t G`: `hasDerivAt_F` on alive (`= ∑ Sc`), 0 on dead. Total:
  `⟨π^a, ∑Sc + (L̃F-with-dead-relaxation)⟩ ≥ ⟨π^a, ∑Sc + ½∑Y_i log Y_i⟩
  = ⟨π^a, ½∑(1 - Y_i + Y_i log Y_i)⟩` ✓.
  Node transfers only increase `u`… CAREFUL direction: transfers move alive
  mass at `x` (with `F_{z_k}(x) ≥ ℓ+1`… so `F ≤ ℓ+1`? both:
  transferred states have `ℓ+1 ≤ F_{z_k}(x)` — hmm then
  `G` jumps from `F_{z_k}(x) ≥ ℓ+1` to `ℓ+1+logκ` — INCREASE requires
  `F_{z_k}(x) ≤ ℓ+1+logκ`: alive mass just before the node had `F < ℓ+1`
  on the open cell, so by continuity `F_{z_k}(x) ≤ ℓ+1` ✓ (use the
  cell-constancy/IVT as in `cflow_alive_support`). So
  `u_{k+1}(z_{k+1}) ≥ u_k(z_{k+1})` ✓.
  Chain (use `chain_le` applied to `-u` or an analogous `chain_ge` you
  prove locally from `chain_le` by negation): get
  `∫-compensator total ≤ u(end) - u(start)`.
  Endpoints: `u(start)`: after `Tr 0`, either all mass alive at `x₀`
  (`u = F θ x₀`) or dead (`u = ℓ+1+logκ`, and then all future compensator
  integrals vanish since alive ≡ 0 — handle as a separate easy case, or
  keep the unified bound `u(start) ≥ min(F θ x₀, ℓ+1+logκ)`…
  simplest: case split on `x₀ ∈ barrier ℓ θ`).
  `u(end) ≤ (ℓ+1+logκ)·(total mass) = ℓ+1+logκ` (`cflow_mass`,
  alive terminal `F ≤ ℓ+1` by support, `logκ ≥ 0`).
  Then `compensator-integral ≤ (ℓ+1+logκ) - F θ x₀ ≤ Rgap + 1 + logκ`
  (`Rgap = max (ℓ - F θ x₀) 0`; two cases). Finally
  `scoreEnergy = ∫⟨π^a, ∑Sc²⟩ ≤ (κ-1)/logκ·∫⟨π^a, ½∑(YlogY+1-Y)⟩` by
  `score_convexity` (PowerCoupling; `Y ∈ [κ⁻¹,κ]` from `Y_le_kappa` etc.)
  pointwise with `π ≥ 0`, monotonicity of cell integrals
  (`intervalIntegral.integral_mono_on` — integrability: continuous
  integrands on compact cells; `1 < κ` from `one_lt_kappa`).
* `SA_le`: unfold `SA`; per `x₀ ∈ A ⊆ activeF`, multiply `scoreEnergy_le`
  by `startW·dbar²` (`startW ≥ 0`), use `dbar = α/(R+1)` on the active set
  and `(κ-1)/logκ = κ/Λ` (`Lam` algebra, `logκ > 0`):
  `dbar²·(κ/Λ)·(R+1+logκ) = α²·[κ/(Λ(R+1)) + κlogκ/(Λ(R+1)²)]`
  and `κlogκ/Λ = κ-1` ✓; `α = 5`, `α² = 25`. Sum.
* `scoreEnergy_nonneg`, `SA_nonneg`: nonneg integrands
  (`cflow_nonneg`, squares), `intervalIntegral.integral_nonneg` per cell
  (cells ordered by `grid.mono`).

Gate: `lake build TalagrandConvConjecture.Lemmas.ScoreEnergy`, zero sorry in
both files. Commit when green.
