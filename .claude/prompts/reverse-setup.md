# Task: close every `sorry` in Reverse/Setup.lean

Touch-set: TalagrandConvConjecture/Reverse/Setup.lean only. Do not change
statements. Read CLAUDE.md. You may use all statements from Cube/*.lean
(being proved in parallel — just apply them).

## Hints

* `fs_pos`: `smooth_pos` with `|e^{-s}| ≤ 1` for `s ≥ 0`.
* `fs_zero`: `smooth_one` + `Real.exp_zero` (note `heatAt f 0 = smooth 1 f`).
* `unifE_fs`: `unifE_smooth` + `D.hm`.
* `Y_pos`, `Y_le_kappa`, `kappa_inv_le_Y`: `fs_pos` (need `T - t ≥ 0`: from
  `t ≤ T` resp. `t ≤ obsT = 2 ≤ T`); edge ratio `smooth_flipCoord_le` with
  `a' = D.a`: for `t ≤ obsT`, `e^{-(T-t)} ≤ e^{-tA} = a`
  (`Real.exp_le_exp`, `Real.exp_log` on `a > 0`; `tA = -log a`). The lower
  bound follows from the upper bound applied at `flipCoord i x` and
  `Y_flipCoord` (or symmetric argument). `kappa` is `(1+a)/(1-a)`.
* `Y_flipCoord`: `flipCoord_flipCoord` + `inv_div`.
* `F_flipCoord_sub`: `Real.log_div` (`fs_pos ≠ 0`).
* `hasDerivAt_F`: `Real.hasDerivAt_log` composed (chain rule) with
  `t ↦ fs (T-t) x`; the latter has derivative `+cubeLap (fs (T-t)) x`
  — careful with signs: `s ↦ heatAt f s x` has derivative `cubeLap` at `s`
  (`hasDerivAt_smooth_exp`), and `t ↦ T - t` has derivative `-1`, so
  `d/dt fs(T-t) = -cubeLap(fs (T-t))`. Wait: recompute! `HasDerivAt.comp`:
  gives `-cubeLap (fs (T-t)) x`. Then
  `∂_t F = -cubeLap/fs = -½∑(Y_i - 1) = ∑ S_i` — expand `cubeLap`,
  `D.Y`, `D.Sc`, use `fs_pos` to divide. For `HasDerivAt` at boundary
  `t = T`: fine, `fs` is defined and positive in a neighborhood of `s = 0`
  (positivity of `f` plus continuity — actually `hs : 0 ≤ s` is needed for
  `fs_pos`; near `t = T`, `T - t` is near `0` possibly negative: use
  continuity of `s ↦ fs s x` and `fs 0 x = f x > 0` to get positivity on a
  neighborhood; `Real.hasDerivAt_log` only needs the value at the point ≠ 0,
  and the composition needs `fs (T-t) x` differentiable which holds
  everywhere).
* `continuousOn_F`, `continuousOn_Y`: continuity of
  `t ↦ fs (T-t) x` (`continuous_smooth_exp` composed), positivity on `Iic T`,
  `Real.continuousOn_log`-style or `ContinuousOn.log`/`ContinuousOn.div`
  with nonvanishing denominators.
* `hasDerivAt_exp_neg_F`: chain rule `Real.hasDerivAt_exp` ∘ `hasDerivAt_F`;
  then the algebraic identity
  `e^{-F}·∑S_i = -L̃(e^{-F})` pointwise: expand `revGen`,
  `e^{-F(σ_i x)} = e^{-F(x)}/Y_i` (`F_flipCoord_sub`, `Real.exp_sub`,
  `Real.exp_log` of `Y_pos`); both sides equal
  `e^{-F}·½∑(1 - Y_i)`... check: `L̃(e^{-F})(x) = ½∑Y_i(e^{-F}/Y_i - e^{-F})
  = e^{-F}·½∑(1 - Y_i) = e^{-F}·∑S_i`. So the claimed derivative
  `-(revGen ...)` equals `-e^{-F}∑S_i`... CAREFUL with the sign: the
  derivative of `e^{-F}` is `-e^{-F}·∑S_i` and `revGen(e^{-F}) = +e^{-F}∑S_i`,
  so the statement `HasDerivAt (fun t => exp (-F)) (-(revGen ...))` is
  consistent. If you find a sign mismatch, STOP and mark STATEMENT-ISSUE —
  do not silently flip.
* `hasDerivAt_revDensity`: expand `revFwdMat`; the claimed identity reduces
  (after the `if`-sums collapse via `flipCoord` bijections) to
  `d/dt fs(T-t)(x) = ½∑_i (fs(T-t)(σ_i x)·(Y_i(t, σ_i x)) - ...)`:
  use `Y t i (flipCoord i x)·fs(T-t)(flipCoord i x) = fs (T-t) x` (from the
  definition of `Y` — this is the flux identity making `ν_{T-t}` the exact
  solution) and the heat equation (`hasDerivAt_smooth_exp` with the chain
  rule sign as in `hasDerivAt_F`). Helper suggestion: first prove
  `∑ x', D.revFwdMat t x x' * D.revDensity t x'
    = -(cubeLap (D.fs (D.T - t)) x) / 2 ^ n`.
* `Hlik` lemmas: `Hlik_pos/`nonneg`: numerator product positive for
  `ρ = e^{-(T-t)} < 1` (`one_add_mul_toR_pos` needs `|ρ·toR(x j)·toR(ζ j)| < 1`),
  `D.hf`, `fs_pos`. `sum_Hlik`: `∑_ζ (∏ ...)·f ζ = fs (T-t) x` is exactly
  `smooth_eq_kernel_sum` read backwards; divide.
* `Hlik_flipCoord_mul_Y`: only the `i`-th kernel factor changes under
  `flipCoord i x`; ratio algebra with `fs_pos`, `toR` facts; `lam` matches.
* `lam` bounds: `(1-ρε)/(1+ρε)` for `ε = ±1`, `0 < ρ ≤ a < 1` — direct
  case analysis, `div_le_div`, `kappa` algebra.
* `hasDerivAt_Hlik`: differentiate the explicit formula (product rule /
  quotient rule; the kernel `∏(1+ρ_t x_jζ_j)/2` has
  `ρ_t' = ρ_t`, so its derivative is `ρ_t·∑_j x_jζ_j·∏_{k≠j}(...)/2` — use
  `HasDerivAt.finset_prod` or `hasDerivAt_mext_comp`-style reorganization;
  note the kernel IS `2^n·cubeKernel`-shaped at `z_j = ρ_t x_jζ_j`).
  Then verify the harmonicity identity pointwise (algebra with the same
  flip-ratio manipulations; this mirrors the classical computation that
  `H^ζ` is the Doob `h`-transform likelihood, [LGF §5.2]). This is the
  hardest item in the file; a clean route: write
  `Hlik t ζ x = (2^n·cubeKernel (fun j => ρ_t·toR (ζ j)) x)·f ζ·2^{-n} / fs (T-t) x`
  — hmm, rather set `N t := ∏_j (1+ρ_t·toR(x j)·toR(ζ j))/2` and prove
  (i) `d/dt N = N·∑_j σ_j`-form or directly
  (ii) `(∂_t + L̃_t)(N / fs(T-t)) = 0` by computing both `∂_t N` (product
  rule) and `L̃(N/fs)` using
  `N(σ_i x)/N(x) = (1-ρx_iζ_i)/(1+ρx_iζ_i) = lam` — the cancellation is
  the identity `∂_t log N - ∂_t log fs(T-t) + ½∑(lam_i - ... )`… follow
  [LGF §5.2]; conclude. Take time; add helpers.

Gate: `lake build TalagrandConvConjecture.Reverse.Setup`, zero sorry.
Commit when green.
