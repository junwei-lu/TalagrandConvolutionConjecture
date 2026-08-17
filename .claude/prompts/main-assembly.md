# Task: close every `sorry` in Main.lean

Touch-set: TalagrandConvConjecture/Main.lean. Do not change statements.
Read CLAUDE.md. Use `fixed_band` (FixedBand.lean), Profile/Statement/Cube
APIs (proofs may be in progress elsewhere).

## Hints ([LGF, proof of Theorem 1.1])

* `biasedConv_eq_heatAt`: `heatAt f (-log a) = smooth (e^{log a}) f =
  smooth a f` (`Real.exp_log`, `ha`), and `smooth_eq_conv`; `funext`.
* `main_of_pos`: obtain `C₀` from `fixed_band`. Fix `D, u > 1`;
  `ℓ_u := Real.log u > 0`. Layer-cake:
  `unifMeas {x | u ≤ P_{tA}f x} ≤ (1/u)·∑_{j : ℕ} e^{-j}·𝔄_{tA}((ℓ_u+j, ℓ_u+j+1])`:
  pointwise, for `x` with `f_{tA}(x) ≥ u`: `log f_{tA}(x) ≥ ℓ_u` falls in
  exactly one band `(ℓ_u+j, ℓ_u+j+1]` with `j = ⌊log f - ℓ_u⌋`-ish — mind
  the boundary `log f = ℓ_u` (left-open bands MISS it!). FIX as [LGF] does:
  bound `λ(P f ≥ u) ≤ λ(P f > v)` for any `1 < v < u`, run the argument at
  level `v` (`ℓ_v = log v`, `log f > ℓ_v` DOES fall in a band `j ≥ 0`), get
  `u·λ(...) ≤ (u/v)·∑_j e^{-j}·C₀K/√(ℓ_v+j) ≤ (u/v)·C₀K/√(log v)·∑e^{-j}`
  and let `v ↑ u` (take `v := √u·…`? cleanest: `v = u^{1/2}`? NO — that
  loses. Take the limit: the RHS is continuous in `v` at `u`; use
  `le_of_forall_lt`-style or `Filter.Tendsto` at `v → u⁻`; simplest
  formal route: for every `ε ∈ (0, u-1)` apply at `v = u - ε` then
  `tendsto` / `le_of_forall_pos_le_add`).
  Also pointwise band-mass extraction:
  `1_{log f_{tA}(x) ∈ (band j)}·f_{tA}(x) ≥ e^{ℓ_v+j}·1_{...}` gives
  `λ(log f ∈ band j) ≤ e^{-(ℓ_v+j)}·𝔄(band j)`; sum with
  `λ(log f > ℓ_v) = ∑_j λ(log f ∈ band j)` (finite effective sum /
  tsum with vanishing tail — `f_{tA}` bounded: reuse
  `exists_profile_vanish`-style boundedness or `tsum_eq_sum`).
  `∑_j e^{-j}/√(ℓ_v+j) ≤ (1/√ℓ_v)·∑ e^{-j} = (1/√ℓ_v)·e/(e-1)`
  (`tsum_geometric_of_lt_one`, monotonicity `√ℓ_v ≤ √(ℓ_v+j)`).
* `talagrand_convolution_conjecture`: from `main_of_pos` + ε-approximation
  [LGF]: given `f ≥ 0`, `unifE f = 1`, `ε > 0`, set
  `f_ε := fun x => (f x + ε)/(1+ε)`: strictly positive,
  `unifE f_ε = 1` (`unifE_add`, `unifE_smul`, `unifE_const`), so
  `D_ε : Dat n` is valid data. `biasedConv a f_ε =
  (biasedConv a f + ε)/(1+ε)` (linearity of the finite sum;
  `∑ biasedWeight = 1`). Hence
  `{x | u ≤ biasedConv a f x} = {x | u_ε ≤ biasedConv a f_ε x}` with
  `u_ε := (u+ε)/(1+ε) > 1` (check `1 < u`). Apply `main_of_pos` at
  `(f_ε, u_ε)`: `u_ε·λ(E) ≤ C·K/√(log u_ε)`; multiply to `u·λ(E) =
  (u/u_ε)·u_ε·λ(E) ≤ (u/u_ε)·C·K/√(log u_ε)`; let `ε → 0`:
  `u_ε → u`, `log u_ε → log u` (continuity of `log`, `u > 1`), conclude by
  a limiting argument (`ge_of_tendsto` on a sequence `ε = 1/(k+1)`,
  `Filter.Tendsto` algebra). Watch: the final constant must not change with
  ε — it doesn't. Alternatively avoid limits: choose ε explicitly small in
  terms of a slack factor `2` and absorb into `C` — the limit route is
  cleaner.
* `talagrand_convolution_conjecture_psi`: `Real.iSup_le` (`ciSup_le`) over
  the subtype using the pointwise theorem; the index type may be empty?
  No: `f ≡ 1` is a member (`unifE_const`) — still, `ciSup_le` works for
  nonempty; supply the instance `Nonempty` with `⟨⟨fun _ => 1, …⟩⟩`.
  RHS ≥ 0 needed if using `Real.iSup_le'`-variants; `Ka_pos`, `√log u > 0`.

Gate: `lake build TalagrandConvConjecture.Main`, zero sorry. Commit.
