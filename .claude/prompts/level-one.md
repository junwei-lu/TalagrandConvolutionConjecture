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

# Task: close every `sorry` in Cube/LevelOne.lean

Touch-set: TalagrandConvConjecture/Cube/LevelOne.lean only. Do not change
statements. Read CLAUDE.md.

## Proof hints (direct Bessel, no typeclass inner-product spaces)

Setup: `𝔼_z[g] := ∑_y cubeKernel z y * g y = mext g z`. Product structure:
expectations of products of single-coordinate factors factorize — prove tiny
helper lemmas by the same `Finset.prod_univ_sum` swap used in
`sum_cubeKernel` (Cube/Multilinear.lean), or reduce to already-proved
statements:
* `sum_cubeKernel_mul_centered`: expand `toR (y i) - z i`; the term
  `∑ kernel·g·y_i` relates to `dmext` by splitting the kernel at coordinate
  `i` (as in `mext_update`): with `K_i = (1+z_i y_i)/2`,
  `y_i·K_i = (z_i... )`: use the identity
  `toR (y i)·(1 + z i·toR (y i)) = z i + toR (y i)` (since `toR² = 1`), which
  gives `∑ kernel·g·y_i = z_i·mext g z + (1-z_i²)·dmext g i z`.
  Then subtract `z_i·mext g z`.
* `sum_cubeKernel_centered_mul_centered` (i ≠ j): factorize the two
  centered coordinates; each has biased mean `0`:
  `∑_{ε=±1} (1+z ε)/2·(ε - z) = 0`.
* `sum_cubeKernel_centered_sq`: single-coordinate second moment:
  `∑_{ε=±1} (1+zε)/2·(ε-z)² = 1 - z²`.
* `level_one`: let `s := Finset.univ.filter (fun i => |z i| < 1)`,
  `c i := dmext φ i z` and expand
  `0 ≤ 𝔼_z[(φ - mext φ z - ∑_{i∈s} c i·(y_i - z_i))²]`.
  Cross terms via the three lemmas above give
  `0 ≤ 𝔼φ² - (𝔼φ)² - 2∑_s c_i(1-z_i²)c_i + ∑_s c_i²(1-z_i²)`, i.e.
  `∑_{i∈s} (1-z_i²)(∂_iφ)² ≤ 𝔼φ² - (𝔼φ)²`. Then `𝔼φ² = 𝔼φ = mext φ z`
  because `φ` is `{0,1}`-valued (`φ x ^ 2 = φ x` pointwise). Finally the
  full sum over `i` equals the sum over `s` since `|z i| = 1` makes the
  `i`-th term vanish (`1 - z i² = 0`).

Gate: `lake build TalagrandConvConjecture.Cube.LevelOne`, zero sorry.
Commit when green.
