# Task: close every `sorry` in Cube/Entropy.lean and Cube/LogSobolev.lean

Touch-set: TalagrandConvConjecture/Cube/Entropy.lean,
TalagrandConvConjecture/Cube/LogSobolev.lean. Do not change statements.
Read CLAUDE.md.

## Entropy.lean hints

* `mul_le_mul_log_sub_add_exp` (Young): for `g > 0`:
  `gφ - g log g = g·log(e^φ/g) ≤ g·(e^φ/g - 1) = e^φ - g` via
  `Real.log_le_sub_one_of_pos`; `g = 0` case is `0 ≤ e^φ`.
* `sum_mul_le_ent`: first prove it when `∑ w g = 1`: sum Young pointwise,
  `∑ w e^φ ≤ 1`, and `log(∑ w g) = log 1 = 0`. For general `g` with
  `m := ∑ w g`: if `m = 0` then `w i·g i = 0` for all `i` (nonneg summands),
  both sides are `0`-ish (LHS `= ∑ w g φ = 0`, `ent = 0`); if `m > 0`, apply
  the normalized case to `g/m` and multiply by `m` (both sides are
  positively homogeneous in `g`: `ent w (c•g) = c·ent w g` — prove as a
  helper using `Real.log_mul`).
* `ent_nonneg`: from `sum_mul_le_ent` with `φ = 0`.
* `ent_average_le`: via the sup representation. Prove the helper: for every
  `ε > 0` there is `φ` with `∑ w e^φ ≤ 1` and
  `ent w g ≤ ∑ w g φ + ε` — take `φ i = log(g i/m) - c_M` on `{g i > 0}`
  and `φ i = -M` elsewhere, `c_M = log(1 + e^{-M}·(mass of {g=0}))`, `M`
  large; OR avoid attainment: prove
  `ent w (∑ p k • h k) ≤ ∑ p k · ent w (h k)` directly: apply
  `sum_mul_le_ent`-style Young with the SINGLE optimizer of the left side:
  φ* built from `ḡ := ∑ p k h k`; then
  `ent w ḡ = ∑_i w ḡ φ* (+ ε-slack) = ∑_k p_k·(∑_i w (h k) φ*) ≤ ∑_k p_k·ent w (h k) (+ ε)`
  using `sum_mul_le_ent` for each `k` with the same `φ*`. Let `ε → 0`
  (`le_of_forall_pos_le_add`).
* `entUnif_le_sum_pairEnt` (tensorization): induct on `n`. Use the
  equivalence `Cube (n+1) ≃ Cube n × ℤˣ` (e.g. `Fin.consEquiv` or
  `(Equiv.piFinSucc n ℤˣ)`; pick whichever composes best) to split sums.
  Exact chain identity:
  `Ent_{μ_{n+1}}(h) = 𝔼_rest[Ent_{coord}(h)] + Ent_{μ_n}(𝔼_coord h)`
  (pure algebra: add and subtract `∑ (𝔼_coord h)·log(𝔼_coord h)`), then
  induction hypothesis on `Ent_{μ_n}(𝔼_coord h)` and `ent_average_le` to
  push `𝔼_coord` inside each pair-entropy. Keep careful track of which
  coordinate `pairEnt i` refers to under the equivalence.
  This is the hardest lemma of the package — allow generous helper lemmas
  (private, in the same file).

## LogSobolev.lean hints

* `one_add_mul_log_add_le`: `h(u) = 2u² - (1+u)log(1+u) - (1-u)log(1-u)`;
  `h(0) = h'(0) = 0`, `h''(u) = 4 - 2/(1-u²) ≥ 0` iff `u² ≤ 1/2`. On
  `[0, 1/√2]`: convexity (`h'' ≥ 0`) + double root ⟹ `h ≥ 0` (e.g. show
  `h' ≥ 0` there since `h'' ≥ 0` and `h'(0) = 0`, then `h ≥ h(0) = 0`).
  On `[1/√2, 1]`: `h` is concave there (`h'' ≤ 0`), so
  `h ≥ min(h(1/√2), h(1))`; check `h(1/√2) > 0` numerically
  (`log` bounds: `log x ≤ x - 1` etc. or `nlinarith` with
  `Real.log_le_sub_one_of_pos` instances) and `h(1) = 2 - 2·log 2 > 0`
  (`Real.log_two_lt_d9`-style bounds exist: `Real.log_two_lt_d9`).
  At `u = 1` note `(1-u)·log(1-u) = 0·log 0 = 0` (junk value `log 0 = 0`).
  Watch continuity at `u = 1`: for the concavity-endpoint argument use
  `Real.continuous_mul_log` (continuity of `x·log x`).
* `half_le_one_sub_sqrt_one_sub`: `√(1-v) ≤ 1 - v/2` since
  `(1 - v/2)² = 1 - v + v²/4 ≥ 1 - v` (`Real.sqrt_le_left`-style:
  `Real.sqrt_le_iff` or `Real.sqrt_le_sqrt` + `Real.sqrt_sq`).
* `two_point_LSI`: WLOG `α² + β² > 0` (else both `0`, LHS `= 0`). Set
  `S := (α²+β²)/2`, `u := (α²-β²)/(α²+β²) ∈ [-1,1]`. Then
  LHS `= S·[½((1+u)log(1+u) + (1-u)log(1-u))]` (use
  `log(α²) = log(S(1+u)) = log S + log(1+u)`, valid also when `α = 0`
  i.e. `u = -1` by the junk-value convention — split that case) and
  `(α-β)² = 2S(1 - √(1-u²))` (compute `αβ = S√(1-u²)`:
  `α²β² = S²(1-u²)`, `Real.sqrt_mul_self`, signs nonneg). Conclude by the
  two 1-D lemmas. WLOG `u ≥ 0` by symmetry (swap α β).
* `cube_LSI`: `entUnif h ≤ ∑_i 𝔼[pairEnt i h]` (tensorization) and
  `pairEnt i h x ≤ (√(h(σ_i x)) - √(h x))²` = `two_point_LSI` at
  `α = √(h x)`, `β = √(h (σ_i x))` (use `Real.sq_sqrt (hh x)`), then sum.

Gate: `lake build TalagrandConvConjecture.Cube.LogSobolev`, zero sorry in
both files. Commit when green.
