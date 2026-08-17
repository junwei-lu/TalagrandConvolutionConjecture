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

# Task: close every `sorry` in Cube/Basic.lean, Cube/Multilinear.lean, Cube/Heat.lean

Touch-set (ONLY these files):
- TalagrandConvConjecture/Cube/Basic.lean
- TalagrandConvConjecture/Cube/Multilinear.lean
- TalagrandConvConjecture/Cube/Heat.lean

Do NOT change any statement (signature/hypotheses/conclusion). Fix broken
inline proofs if any remain. Read CLAUDE.md first.

## Proof hints

* `sum_cubeKernel`: swap product and sum with `Finset.prod_univ_sum`
  (over `Fintype.piFinset`; note `Cube n = Fin n → ℤˣ` is a pi type and
  `Fintype.piFinset_univ`). Each coordinate factor sums to `1`:
  `(1+z)/2 + (1-z)/2 = 1`.
* `mext_toR`: `∏_i (1 + x_i y_i)/2` is `1` if `y = x` and `0` otherwise
  (some factor is `(1-1)/2 = 0` when `y_j ≠ x_j`; use `Finset.sum_eq_single x`
  and `Finset.prod_eq_zero`).
* `mext_update`, `dmext_update`, `mext_update_neg`, `hasDerivAt_mext_update`:
  expand `cubeKernel` as (factor i)·(product over `univ.erase i`), via
  `Finset.prod_erase_mul` / `Finset.mul_prod_erase`. The `i`-th factor is
  affine in `z i`; everything else is constant in `z i`
  (`Function.update_self`, `Function.update_of_ne`).
* `hasDerivAt_mext_comp`: write `mext f (z t) = ∑_y (∏_i ...)·f y` and use
  `HasDerivAt.sum`, `HasDerivAt.finset_prod` (exists in Mathlib as
  `HasDerivAt.finset_prod` — check; otherwise induct with `HasDerivAt.mul`),
  then reorganize the resulting sum into `∑ i dmext · z' i` by swapping sums.
* `mext_smooth_eq` (master composition): expand both sides, swap the two cube
  sums, and use per-coordinate
  `∑_{ε=±1} (1+zε)/2·(1+ρεw)/2 = (1+ρzw)/2` (expand: cross terms cancel
  since `ε² = 1`), then `Finset.prod_univ_sum` again.
* `smooth_eq_conv`: substitute `y ↦ x*y` (`sum_comp_mul_right`-style bijection,
  `Equiv.mulLeft`/`mulRight`), using `toR_mul` and `toR_mul_self`.
* `smooth_smooth`: from `mext_smooth_eq` at `z = ρ'·toR x`... careful with
  order: `smooth ρ (smooth ρ' f) x = mext (smooth ρ' f) (ρ·toR x)
  = mext f (ρ'·(ρ·toR x))` by `mext_smooth_eq` (with the roles of ρ,ρ'
  as in the statement); note multiplication commutes.
* `unifE_smooth`: use `smooth_eq_conv`, swap sums, translation invariance
  `sum_comp_mul_right`, and `∑_y biasedWeight ρ y = 1` (= `sum_cubeKernel`
  specialized, via `biasedWeight ρ y = cubeKernel (fun _ => ρ) y`).
* `smooth_pos`: all kernel terms nonneg (`cubeKernel_nonneg`), sum of kernels
  is 1 so some kernel is positive; that term contributes `> 0` since `f > 0`.
  (Or: `Finset.sum_pos'` with the witness `y` from `∑ kernel = 1 > 0`.)
* `hasDerivAt_smooth_exp`: chain rule: `s ↦ exp(-s)` has derivative
  `-exp(-s)`; `ρ ↦ mext f (ρ·toR x)` has derivative
  `∑ i dmext f i (·)·toR (x i)` (from `hasDerivAt_mext_comp`). Identify with
  `cubeLap (smooth ρ f) x = -ρ·∑_i toR (x i)·dmext f i (ρ·toR x)` — prove
  this via `mext_update_neg`: flipping `x i` negates the `i`-th coordinate of
  `ρ·toR x`, so
  `smooth ρ f (flipCoord i x) - smooth ρ f x = -2ρ·toR (x i)·dmext f i (·)`.
* `smooth_flipCoord_le` (edge ratio, [C Lemma 5]): use `smooth_eq_kernel_sum`;
  the two sums have pointwise kernel ratio
  `(1-ρx_jz_j... )`: only the `i`-th factor differs:
  `(1 - ρ x_i z_i)/(1 + ρ x_i z_i) ≤ (1+a')/(1-a')` when `|ρ| ≤ a' < 1`;
  conclude with `sum_div_le_of_ratio_le` (in Multilinear.lean).
* `smooth_eq_kernel_sum`: substitute `z = x*y` in the conv form
  (`smooth_eq_conv`), i.e. `y = x*z`, and `toR (x j) * toR ((x*z) j)
  = toR (z j)`... rather: `(x*y) j`'s kernel: rewrite
  `1 + ρ·toR(y j) = 1 + ρ·toR(x j)·toR((x*y) j)` using `toR_mul_self`.

## Gate

Cluster build (from the worktree):
`lake build TalagrandConvConjecture.Cube.Basic TalagrandConvConjecture.Cube.Multilinear TalagrandConvConjecture.Cube.Heat`
Done = compiles with ZERO sorry in these three files. Commit with a clear
message when green.
