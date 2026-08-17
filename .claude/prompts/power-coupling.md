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

# Task: close every `sorry` in PowerCoupling.lean and Statement.lean

Touch-set: TalagrandConvConjecture/PowerCoupling.lean and the three
well-posedness lemmas at the bottom of
TalagrandConvConjecture/Statement.lean (`Ka_pos`, `one_le_Ka`,
`bddAbove_psi_family`). Do not change statements. Read CLAUDE.md.

## Statement.lean hints

* `Ka_pos`, `one_le_Ka`: `1 < κ` (`one_lt_kappa`); the standard bounds
  `(κ-1)/κ ≤ log κ ≤ κ - 1` (`Real.log_le_sub_one_of_pos`,
  `Real.one_sub_inv_le_log_of_pos`? — the lower bound is
  `log κ ≥ 1 - 1/κ = (κ-1)/κ`: from `log (1/κ) ≤ 1/κ - 1`); hence
  `log κ/(κ-1) ∈ [1/κ, 1]`, so `Ka = κ²√(logκ/(κ-1)) ≥ κ²·κ^{-1/2} ≥ 1`.
  `Real.sqrt` monotone; `Real.one_le_sqrt` etc.
* `bddAbove_psi_family`: `mul_unifMeas_le_unifE` (Basic) with
  `biasedConv a f ≥ 0` (sum of nonneg; `biasedWeight ≥ 0` needs `|a| ≤ 1`)
  and `unifE (biasedConv a f) = 1`: prove via `smooth_eq_conv` backwards or
  directly: swap sums, translation invariance `sum_comp_mul_right`,
  `∑_y biasedWeight a y = 1` (from `sum_cubeKernel` with the constant
  vector, as in Cube/Heat).

## PowerCoupling.lean hints

* `one_le_Lam`, `Lam_le_kappa`: same log bounds as above:
  `Λ = κ·logκ/(κ-1) ∈ [1, κ]`.
* `Ka_sq_eq`: `Ka² = κ⁴·(logκ/(κ-1))` (`Real.sq_sqrt` of nonneg) and
  `κ³Λ = κ⁴logκ/(κ-1)` ✓ `ring`-able after `Real.sq_sqrt`.
* `powerRatio_nonneg`: case split; for `Y < 1`: `Y^d ≤ 1`
  (`Real.rpow_le_one` for `0 ≤ Y ≤ 1, 0 ≤ d`), both numerator and
  denominator ≥ 0. For `Y > 1`: `Y^{1-d} ≤ Y^1 = Y`
  (`Real.rpow_le_rpow_of_exponent_le`, `1 ≤ Y`).
* `powerRatio_le` ([LGF Lemma 5.2]): 
  - `Y < 1` branch: `1 - Y^d = 1 - e^{d·log Y} ≤ -d·log Y`
    (`Real.add_one_le_exp`: `1 + x ≤ eˣ` at `x = d log Y`), so
    `powerRatio ≤ d·(-log Y)/(1-Y)`. Then show `(-log y)/(1-y)` is
    monotone DECREASING on `(0,1)` — equivalently prove directly
    `(-log Y)/(1-Y) ≤ (log κ·κ)/(κ-1)` for `Y ∈ [κ⁻¹, 1)`: cross-multiply
    to `(-log Y)(κ-1) ≤ κ·logκ·(1-Y)`; substitute the bound
    `-log Y ≤ log κ` (from `Y ≥ κ⁻¹`, `Real.log_le_log`) — CAREFUL, that
    alone gives `(κ-1)·logκ ≤ κlogκ(1-Y)` which needs `1-Y ≥ (κ-1)/κ`,
    i.e. `Y ≤ κ⁻¹` — only the endpoint! So do prove the monotonicity: for
    `g(y) = -log y/(1-y)` on `(0,1)`, `g' ≤ 0` ⟺
    `-(1-y)/y + log y·(-1)·...` — compute:
    `g'(y) = [-(1-y)/y + (-log y)]/(1-y)²`·sign-check: numerator
    `N(y) = -(1-y)/y - log y·(-1)`… safest: show
    `N(y) = -1/y + 1 - log y·(-1)`… Do it cleanly: prove
    `h(y) := (-log y)·(κ-1) - Λκ-form`… RECOMMENDED clean route: prove the
    monotone lemma `∀ y ∈ (0,1), (-log y)·y ≤ …` via the auxiliary
    inequality `1 - 1/y ≤ log y ≤ y - 1`: from `log y ≥ 1 - 1/y = -(1-y)/y`:
    `-log y ≤ (1-y)/y`, hence `(-log y)/(1-y) ≤ 1/y ≤ κ`. That gives
    `powerRatio ≤ d·κ` — NOT quite `d·Λ`… but `Λ ≥ 1` and we need `≤ Λ·d`
    with `Λ = κlogκ/(κ-1) ≤ κ`: `d·κ ≤ d·Λ` is FALSE in general
    (`Λ ≤ κ`). So the sharp monotonicity IS needed:
    `y ↦ -log y/(1-y)` decreasing on `(0,1)`: derivative sign reduces to
    `y·log y ≤ y - 1`… let me give you the precise route:
    `d/dy[-log y/(1-y)] = [-(1-y)/y + (-log y)]·(1-y)^{-2}`·… the numerator
    (times y): `-(1-y) - y·log y = y - 1 - y log y ≤ 0` ⟺
    `y log y ≥ y - 1` ⟺ `log y ≥ 1 - 1/y` ✓ (standard:
    `Real.one_sub_inv_le_log_of_pos` or from `log(1/y) ≤ 1/y - 1`).
    So the derivative of `-log y/(1-y)` is
    `(y - 1 - y·log y)/(y(1-y)²) ≤ 0` ✓. Formalize with
    `HasDerivAt.div` + a monotonicity-from-derivative lemma
    (`AntitoneOn` via `antitoneOn_of_deriv_nonpos` on the interval
    `[κ⁻¹, 1)`... interval `Icc κ⁻¹ c` for `c < 1` then limit, or use
    `Ioo 0 1` with `interior`), and evaluate at the left endpoint:
    `g(κ⁻¹) = logκ/(1-κ⁻¹) = κlogκ/(κ-1) = Λ` ✓.
  - `Y = 1`: `powerRatio = d ≤ Λd` by `Λ ≥ 1`.
  - `Y > 1` branch: `Y - Y^{1-d} = Y(1 - Y^{-d}) ≤ Y·d·log Y`
    (`1 - e^{-dlogY} ≤ d·logY`), so `powerRatio ≤ d·(Y logY)/(Y-1)`; show
    `y ↦ y·log y/(y-1)` INCREASING on `(1,∞)`: derivative numerator
    `(log y + 1)(y-1) - y log y = y - 1 - log y ≥ 0` ✓
    (`Real.log_le_sub_one_of_pos`). Evaluate at `κ`: `κlogκ/(κ-1) = Λ` ✓.
* `one_sub_rpow_eq`, `rpow_sub_eq`: unfold `powerRatio` (`if` branches),
  `field_simp` with `1 - Y ≠ 0` resp. `Y - 1 ≠ 0`.
* `rpow_le_one_sub_add_mul` (AM–GM): `Real.geom_mean_le_arith_mean2_weighted`
  with weights `(1-d, d)` and points `(1, Y)`:
  `1^{1-d}·Y^d ≤ (1-d)·1 + d·Y`; `Real.one_rpow`.
* `score_convexity` ([C eq (40)]): define
  `h(Y) = 2(κ-1)(Y log Y - Y + 1) - log κ·(1-Y)²`;
  `h(1) = 0`, `h'(Y) = 2(κ-1)·log Y + 2logκ(1-Y)`, `h'(1) = 0`,
  `h''(Y) = 2(κ-1)/Y - 2logκ`. `h'' ≥ 0` iff `Y ≤ (κ-1)/logκ =: Y*`;
  `1 ≤ Y* ` (`logκ ≤ κ-1`). On `[κ⁻¹, Y*]`: convex with double root at 1
  (`κ⁻¹ ≤ 1 ≤ Y*`) ⟹ `h ≥ 0` (split `[κ⁻¹,1]` and `[1,Y*]`: on each, sign
  of `h'` from `h''`-sign and `h'(1)=0`). On `[Y*, κ]` (if `Y* < κ`):
  concave, so `h ≥ min(h(Y*), h(κ))`; `h(Y*) ≥ 0` from the convex part;
  `h(κ) = 2(κ-1)(κlogκ - κ + 1) - logκ(κ-1)² = (κ-1)[(κ+1)logκ - 2(κ-1)]
  ≥ 0` ⟺ `logκ ≥ 2(κ-1)/(κ+1)`: prove this auxiliary via the derivative of
  `logx - 2(x-1)/(x+1)` being `(x-1)²/(x(x+1)²) ≥ 0` and value 0 at 1.
  (Alternatively `nlinarith` with several log-bound hints may close
  branches — try, but have the structured proof ready.)
* `lam_mul_powerRatio_div_le`: for `Y > 1`:
  `powerRatio d Y/Y = (1 - Y^{-d})/(Y-1)·(...)`: compute
  `powerRatio d Y / Y = (1 - Y^{-d})/(Y-1)` (using
  `Y^{1-d}/Y = Y^{-d}`, `Real.rpow_natCast`/`rpow_sub` with `Y > 0`), then
  `1 - Y^{-d} ≤ d·log Y ≤ d·(Y-1)` gives the ratio `≤ d`; multiply by
  `lam ≥ 0`.
* `dbar` lemmas: unfold `dbar`/`Rgap`; `alphaC = 5`; arithmetic
  (`Rgap ≥ 2α ⟹ α/(R+1) ≤ α/(2α+1) < 1/2`).
* `conditioned_power_bound` ([LGF eq (4.11)]): case split on the sign of
  `Sc = (1-Y)/2` (i.e. `Y < 1`, `Y = 1`, `Y > 1`); `S > 0` branch:
  `powerRatio ≤ Λ·δ̄` (`powerRatio_le`) and `λ ≥ κ⁻¹` so
  `(Λδ̄)² ≤ κΛ²δ̄²·λ`. `S = 0` (`Y = 1`): `powerRatio = δ̄` and the factor
  is `λ/1 = λ ≤ κ`: `(δ̄λ)² = δ̄²λ·λ ≤ δ̄²λ·κ ≤ κΛ²δ̄²λ` (`Λ ≥ 1`).
  `S < 0` (`Y > 1`): factor `λ/Y`; use `lam_mul_powerRatio_div_le` to get
  `powerRatio·λ/Y ≤ λ·δ̄`, then `(λδ̄)² ≤ κΛ²δ̄²λ` as before. Needs
  `κ⁻¹ ≤ Y ≤ κ` (`Y_le_kappa` etc. from Reverse/Setup with `t ≤ obsT`),
  `λ` bounds (`lam_le_kappa`, `kappa_inv_le_lam`), `Λ ≥ 1`, `δ̄ ∈ [0,1)`.

Gate: `lake build TalagrandConvConjecture.PowerCoupling TalagrandConvConjecture.Statement`,
zero sorry in the two files. Commit when green.
