# Task: close every `sorry` in ODE/LinearFlow.lean and Flow/Glued.lean

Touch-set: TalagrandConvConjecture/ODE/LinearFlow.lean,
TalagrandConvConjecture/Flow/Glued.lean. Do not change the statements of the
public theorems. You MAY add private helper lemmas/definitions in these files.
Read CLAUDE.md.

## LinearFlow.lean hints (the finite-dimensional linear ODE package)

State space `S → ℝ` is finite-dimensional; equip computations with the sup
or Euclidean norm via `EuclideanSpace ℝ S` or `PiLp` as convenient — or work
coordinatewise and avoid norms where possible.

* `exists_linFlow`: two routes; pick one and commit.
  (1) Mathlib Picard–Lindelöf: `Mathlib/Analysis/ODE/PicardLindelof.lean`
  (`IsPicardLindelof`, `exists_eq_forall_mem_Icc_hasDerivWithinAt`). The
  vector field `f t y = matVec (A t) y` is continuous in `t` and globally
  Lipschitz on `Icc a b` (Lipschitz constant
  `L = sup_t ‖A t‖`, finite by compactness/continuity). PL gives local
  solutions; get the whole interval by subdividing `[a,b]` into `m` pieces
  short enough for the PL radius condition (the a priori bound
  `‖y‖ ≤ ‖y₀‖e^{L(b-a)}` by Grönwall keeps the ball uniform), then glue by
  strong induction.
  (2) Bespoke Picard iteration in `C([a,b], S → ℝ)` (sup norm), with
  `ContractingWith.fixedPoint` after subdividing so `L·Δ < 1/2`.
  Route (1) with subdivision is recommended.
* `linFlow_unique`: Grönwall — `Mathlib/Analysis/ODE/Gronwall.lean`
  (`ODE_solution_unique_of_mem_Icc` and friends); the field is
  `K`-Lipschitz in `y` uniformly on the compact time interval.
* `linFlow_nonneg`: first prove the `ε`-shifted version: let
  `y_ε` solve `y' = A y + ε·1` (existence: absorb the constant by one extra
  dimension, or redo the existence proof with an affine field — simplest:
  prove existence for affine fields `y' = A t y + c` in the same way and
  specialize `c = 0` for `exists_linFlow`). For `y_ε` with `y_ε a = y₀ + ε·1`:
  if some coordinate ever hits `0`, take the infimum time `t*` of
  `{t | ∃ s, y_ε t s ≤ 0}`; at `t*` some coordinate `j` has value `0`,
  others `≥ 0`, so `(y_ε)'_j(t*) = ∑_{k≠j} A_{jk} y_k + A_{jj}·0 + ε ≥ ε > 0`
  (Metzler); but a function positive on `[a, t*)` reaching `0` at `t*` has
  left derivative `≤ 0` — contradiction (formalize via
  `HasDerivWithinAt` at `t*` from the left and the sign of difference
  quotients). Then let `ε ↓ 0` using continuous dependence: `‖y - y_ε‖ ≤
  C·ε` by Grönwall applied to the difference (`norm_le_gronwallBound_of_norm_deriv_right_le`).
  Alternative cleaner route: prove nonnegativity directly for `y` by
  considering `m(t) = min_s y t s` and a Grönwall bound on the negative part
  `‖min(y,0)‖`; choose whichever closes.
* `linFlow_mass_eq` / `linFlow_mass_le`: differentiate `t ↦ ∑_s y t s`
  (`HasDerivWithinAt.sum`); the derivative is `∑_{s'} (∑_s A s s') y s'`
  which is `0` (resp. `≤ 0` given `y ≥ 0`); conclude by
  `constant_of_derivWithin_zero` / monotonicity lemmas from `MeanValue`.
* `hasDerivWithinAt_pairing`: `HasDerivWithinAt.sum` + `.mul`.
* `linFlow_le_of_source`: apply the nonnegativity argument to `z - y`
  (its derivative is `A(z-y) + r`, `r ≥ 0`; same `ε`-argument, the source
  only helps).

## Glued.lean hints

* `fwdOf_col_sum`: split the sum; `∑_s q s' s - ∑_s [diagonal term]`; the
  diagonal indicator picks `s = s'`.
* `exists_gluedFlow`: strong induction over `k`, using `exists_linFlow` per
  cell with initial value `matVec (Tr k) (previous endpoint)`. Define the
  sequence by `Nat.rec` on pieces and package.
* `gluedFlow_nonneg` / `gluedFlow_mass`: induct over cells using
  `linFlow_nonneg` / `linFlow_mass_eq`; transfers preserve nonnegativity
  (`matVec` of nonneg matrix) resp. total mass (`hTr` column sums 1:
  `∑_s matVec (Tr k) v s = ∑_{s'} (∑_s Tr k s s') v s' = ∑ v`).
* `chain_le` / `chain_eq` / `chain_mono`: induction on `K`; each cell gives
  `u k (z (k+1)) - u k (z k) ≤ ∫ φ k` via
  `sub_le_integral_of_finite_exceptions` (PiecewiseFTC, with empty
  exceptional set — or Mathlib's
  `integral_eq_sub_of_hasDeriv_right_of_le` directly; note
  `HasDerivWithinAt (Icc)` restricts to the open interval). Chain with the
  node inequalities. Mind `K - 1` + `Finset.range K` indexing: prove the
  auxiliary statement `∀ m ≤ K-1, u m (z (m+1)) ≤ u 0 (z 0) + ∑_{k≤m} ∫...`
  by induction on `m`.

Gate: `lake build TalagrandConvConjecture.Flow.Glued`, zero sorry in both
files. Commit when green.
