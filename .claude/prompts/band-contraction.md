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

# Task: close every `sorry` in Lemmas/BandContraction.lean

Touch-set: TalagrandConvConjecture/Lemmas/BandContraction.lean. Do not
change statements; private helpers welcome. Read CLAUDE.md. Use stated APIs
from Lemmas/Supermartingale.lean, Lemmas/Quantities.lean, Flow/*.

## Hints ([LGF §4.3])

* `band_crossing_le`: apply `weighted_comparison_localized` with
  `A = activeF`, `h := indicator of {w | F obsT w ∈ (ℓ+j, ℓ+j+1]}`.
  On the event in the LHS, `NW obsT s ≥ e^{α+j-1}` by `NW_ge_on_crossing`
  (with real `j := (j:ℕ)`; `F obsT s.2.1 > ℓ+j` from the `Ioc`
  membership). So
  `e^{α+j-1}·LHS ≤ ∑∑ NW·term·h(W) ≤ ∑∑ term·h(V) = Aband (ℓ+j)`.
  Rearrange: `LHS ≤ e^{1-α}e^{-j}·Aband (ℓ+j)` (`Real.exp_add` algebra).
  Mind: the LHS indicator has the `∧ F(V) ≤ ℓ+1` condition — dominate it by
  dropping conditions AFTER multiplying by `NW ≥ e^{...}` (all terms
  nonneg: `cflow_nonneg`, `startW ≥ 0`, `NW > 0`).
* `Aband_summable`: `Aband Φ A r ≤ 1` for all `r` (mass bounds:
  `cflow_mass`, `startW`-sum `= probA ≤ 1`… prove `probA θ univ = 1` via
  `unifE_fs`; or bound `Aband ≤ probA ≤ 1`), then compare with the
  geometric series `Summable.of_nonneg_of_le` +
  `summable_geometric_of_lt_one` (ratio `e⁻¹`; rewrite
  `exp (-(j+1)) = exp(-1)·(exp (-1))^j` via `Real.exp_neg`,
  `Real.exp_nat_mul`-style).
* `band_contraction`: follow [LGF §4.3] exactly:
  (i) `j = 0` case of `band_crossing_le` gives
  `B∧V≤ℓ+1-mass ≤ c₀·Aband ℓ`;
  (ii) `Bband ℓ ≤ (that mass) + ℙ(ℰ, W∈band ℓ, V > ℓ+1)`
  ≤ `c₀·Aband ℓ + ℙ(ℰ, F(W) > ℓ+1 ≥ hmm` — [LGF] route:
  `Bband ℓ ≤ c₀ Aband ℓ + ℙ(ℰ, F(V) > ℓ+1 ≥ F(W))`
  … follow the displayed chain in [LGF §4.3] literally:
  1. `Bband ℓ ≤ c₀·Aband ℓ + ℙ(ℰ, F(V) > ℓ+1 ≥ F(W))` — decompose the
     `W ∈ band ℓ` event by whether `F(V) ≤ ℓ+1` (indicator algebra;
     note `W ∈ band ℓ ⟹ F(W) ≤ ℓ+1`).
  2. `ℙ(ℰ, F(V) > ℓ+1 ≥ F(W)) ≤ ℙ(ℰ, F(W) > ℓ+1 ≥ F(V)) + D_{ℰ}`:
     test `B := {w | F obsT w > ℓ+1}` in `abs_Dtest_le_DA`:
     `ℙ(ℰ, V ∈ B) - ℙ(ℰ, W ∈ B) ≤ D` and
     `ℙ(ℰ, V∈B, W∈B^c) - ℙ(ℰ, W∈B, V∈B^c) = ℙ(ℰ,V∈B) - ℙ(ℰ,W∈B)`
     (add/subtract the both-in-B mass).
  3. `ℙ(ℰ, F(W) > ℓ+1 ≥ F(V)) = ∑_{j≥1} (crossing events) ≤
     c₀∑_{j≥1}e^{-j}Aband (ℓ+j)`: partition `(ℓ+1, ∞)` into bands
     `(ℓ+j, ℓ+j+1]`, `j ≥ 1` — the partition is FINITE in effect
     (`F obsT` is bounded on the finite cube: beyond
     `max_x F obsT x` all terms vanish), so either work with a finite sum
     up to `⌈max F⌉` and dominate by the tsum (all terms nonneg,
     `Summable.sum_le_tsum`), or directly: the event-sum equals a tsum by
     `tsum_eq_sum` of eventually-zero terms.
  4. `Aband ℓ ≤ Bband ℓ + D_{ℰ}`: test `B := {w | F obsT w ∈ (ℓ,ℓ+1]}` in
     `abs_Dtest_le_DA`.
  Combine 1–4 and rearrange to the stated inequality (all quantities
  finite; the tsum manipulation needs `Aband_summable`).

Gate: `lake build TalagrandConvConjecture.Lemmas.BandContraction`, zero
sorry. Commit when green.
