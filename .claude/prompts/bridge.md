# Task: close every `sorry` in Bridge.lean

Touch-set: TalagrandConvConjecture/Bridge.lean only. Do not change
statements. Read CLAUDE.md. Use statements from Cube/*.lean and
Reverse/Setup.lean freely (proved in parallel).

## Hints ([LGF §4.1, §5.2]; all pure algebra + 1-D calculus)

* Ranges: `gam t = e^{-(2-t)} ∈ (0,1]` for `t ≤ 2 = obsT`. Denominator
  `1 - a²γ² > 0` (`a < 1`, `γ ≤ 1`). `aB, bB ≥ 0`;
  `aB + bB = (a+γ)/(1+aγ)` (factor `1-a²γ² = (1-aγ)(1+aγ)` and
  `γ(1-a²) + a(1-γ²) = (a+γ)(1-aγ)`); `≤ 1` since `a+γ ≤ 1+aγ`
  (⟺ `(1-a)(1-γ) ≥ 0`). `|mB| ≤ aB + bB` by `|toR| = 1` and triangle.
* `mB_flip_y` / `mB_flip_xy`: `funext j`; case `j = i` vs `j ≠ i`
  (`flipCoord_self`, `flipCoord_ne`, `Function.update_self`,
  `Function.update_of_ne`); note `toR (-(u)) = -toR u` and for `flip_xy`
  the product `toR(x i)·toR(y i)` is invariant while `aB·toR(y i)` flips.
* `qB_flip_y_sub` etc.: `mext_update_neg` (Cube/Multilinear) at the vector
  `mB`, rewritten along `mB_flip_y`; for `qB_flip_y_flip_x_sub` apply the
  same with base point `flipCoord i x` and express
  `mB t (flipCoord i x) y ζ = update (mB t x y ζ) i (aB·y_i - bB·x_iy_iζ_i)`
  (helper lemma; only the `i`-th coordinate changes sign of the `bB` part).
  Also `dmext` is insensitive to the `i`-th coordinate (`dmext_update`).
* `hasDerivAt_mB`: with `ε := toR (x i)·toR (ζ i) = ±1`, reduce to the 1-D
  identities `d/dt (aB ± bB) = λ^{±}·aB` where
  `λ^{±} = (1∓aγ)/(1±aγ)`; `HasDerivAt` of `gam` is `gam` itself; then
  `field_simp`/`ring` with `1-a²γ² = (1-aγ)(1+aγ) ≠ 0`. (Checked by hand:
  `d/dt[(a+γ)/(1+aγ)] = γ(1-a²)/(1+aγ)² = λ⁺·aB` ✓ and symmetric.) Note
  `lam t i x ζ` from Reverse/Setup uses `ρ_t = e^{-(T-t)} = a·γ_t`
  (`T = tA + obsT`, `e^{-tA} = a` needs `Real.exp_log` on `a > 0`) —
  prove the helper `ρ_t = D.a * D.gam t` first.
* `hasDerivAt_qB`: `hasDerivAt_mext_comp` with `z t = mB t x y ζ` and
  `z' i = lam·aB·toR (y i)` (from `hasDerivAt_mB`), giving derivative
  `∑ i dmext·λ_i·aB·y_i`; rewrite the claimed RHS via `qB_flip_xy_sub`.
* `hasDerivAt_qB_sq`: `HasDerivAt.pow` on `hasDerivAt_qB` + the algebraic
  square-difference expansion: for each i,
  `Δ_i^{xy}(q²) = 2q·Δ_i^{xy}q + (Δ_i^{xy}q)²` and
  `(Δ_i^{xy}q)² = 4·aB²·(dmext)²` (from `qB_flip_xy_sub`, `toR² = 1`).
  Assemble; this is the carré-du-champ bookkeeping [LGF eq (4.9)].
* `lam_mul_bB_sq_le`: with `ε = ±1`:
  `lam·bB²/(1-(mB_i)²) = a²(1-γ²)/((1-a²)(1-a²γ²))` — direct `field_simp;
  ring_nf` computation using `mB_i = toR(y i)·(aB + bB·ε)` and
  `(mB_i)² = (aB+εbB)²`; then bound `(1-γ²)/(1-a²γ²) ≤ 1`. Need
  `1 - (mB_i)² > 0`? At `γ = 1`: `aB = 1, bB = 0`, `m² = 1` — the statement
  has `≤` with RHS `0` and LHS `lam·0 = 0` ✓ fine; handle the `bB = 0`
  boundary by direct substitution if the division route degenerates
  (case-split on `γ = 1` i.e. `t = obsT`, or better: prove the polynomial
  identity `lam·bB²·(1-a²)·(1-a²γ²) = a²(1-γ²)·(1-(mB_i)²)·(...)`-form
  avoiding division entirely, then compare).

Gate: `lake build TalagrandConvConjecture.Bridge`, zero sorry. Commit when
green.
