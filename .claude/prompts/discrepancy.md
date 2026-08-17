# Task: close every `sorry` in Lemmas/Discrepancy.lean  ([LGF Lemma 3.3])

Touch-set: TalagrandConvConjecture/Lemmas/Discrepancy.lean. Do not change
the statements of the existing theorems; you MAY add private helper
lemmas/defs in the file. Read CLAUDE.md and the module docstring. This is
the deepest file of the project — follow [LGF §4.1] closely
(ref/main/main.tex, proof of Lemma 3.3, plus §5.2–5.3). Use stated APIs
from Bridge.lean, Reverse/Setup.lean, PowerCoupling.lean, Flow/*,
Lemmas/Quantities.lean, Cube/LevelOne.lean.

## Sub-results already stated (close them in order)

1. `Utest_obsT`: at `t = obsT`: `gam = 1`, `aB = 1`, `bB = 0`
   (`Real.exp_zero`; `field_simp` with `1 - a² ≠ 0`), so
   `mB obsT x y ζ = toR∘y` and `qB φ obsT ζ x y = φ y` (`mext_toR`). Then
   `∑_ζ Hlik·φ y = φ y` by `sum_Hlik` (`obsT ≤ T`).
2. `hasDerivAt_Utest`: product rule (`HasDerivAt.mul`, `HasDerivAt.sum`)
   with `hasDerivAt_Hlik` and `hasDerivAt_qB`; then the ALGEBRAIC
   rearrangement: with `r_i := Hlik(σ_i x)/Hlik(x)` and
   `r_i·Y_i = lam_i` (`Hlik_flipCoord_mul_Y`), check
   `Y_i·(Hlik(σx)qB(σx,σy) - Hlik(x)qB(x,y))
    = Hlik(x)·[lam_i·(qB(σx,σy) - qB(x,y))] + qB(σx,σy)·[Y_i·(Hlik(σx) - ...)]`
   — follow [LGF §4.1]'s displayed computation
   `(∂_t + L̄⁰)(H^ζ q^ζ) = q(∂_t+L̃)H + H(∂_t+𝓛^{0,ζ})q = 0`
   summand-by-summand: expand both harmonicity facts and match terms
   (pure algebra; `Hlik_pos` for divisions or better avoid division:
   multiply through by `Hlik x`).
3. `term_V_eq_Utest_diag`: define `g t x := Utest φ t x x`; from (2), the
   diagonal satisfies `∂_t g = -revGen t g` (the synchronized difference at
   `(x,x)` is the `V`-difference of `g` — note
   `Utest(σ_i x, σ_i x)` IS `g (σ_i x)` ✓). Continuity: from
   differentiability (or `continuousOn` composition). Apply
   `cflow_V_marginal`.
4. `abs_pert_Utest_le` (pointwise [LGF eq (4.17)]): write the LHS sum's
   `i`-th term via the splitting identities `one_sub_rpow_eq`,
   `rpow_sub_eq` (PowerCoupling) as `δ_i·S_i·(Δ-terms)` with
   `δ_i = powerRatio (dbar) (Y_i)`; expand `Utest`'s `y`-differences via
   `qB_flip_y_sub` and `qB_flip_y_flip_x_sub` (Bridge) — for the second,
   note `Hlik (σ_i x)·(qB-difference at σ_i x) =
   Hlik x·r_i·(...)` and `r_i = lam_i/Y_i`. Get the form
   `|∑_i ∑_ζ Hlik·δ_i·S_i·(1 or r_i)·(-2 c_i^ζ)·dmext φ i (mB)|` with
   `|c_i^ζ| ≤ aB + bB ≤ 1`… follow [LGF]: use `|c|² ≤ 2(aB² + bB²)`,
   the conditioned power bound `conditioned_power_bound`
   (`(δ_i(1∨r_i))² ≤ κΛ²δ̄²·lam_i`), and two Cauchy–Schwarz steps:
   over `i` (`Finset.inner_mul_le_norm_mul_norm` or
   `Finset.sum_mul_sq_le_sq_mul_sq`) and over `ζ` with weights `Hlik`
   (`∑_ζ Hlik = 1`, `Hlik ≥ 0`). Constant: `2·√2 = √8` ✓ generous.
5. `bpart_Gam_le` ([LGF eq (4.19)] pointwise): `lam·bB² ≤
   a²/(1-a²)·(1-(mB_i)²)` (`lam_mul_bB_sq_le`), then the level-one
   inequality `level_one` at `z = mB t x y ζ` (`abs_mB_le_one`;
   `{0,1}`-valued `hφ`) bounds `∑_i (1-(mB_i)²)·dmext² ≤ ¼`
   (`self_sub_sq_le_quarter` + `mext_mem_Icc` gives `mext φ (mB) ∈ [0,1]`,
   so `mext - mext² ≤ ¼`), then `∑_ζ Hlik·(¼·a²/(1-a²)) ≤ κ/4`
   (`sum_Hlik`, `a²/(1-a²) ≤ κ`: algebra with `kappa`).
6. `DA_le` (the master assembly, [LGF proof of Lemma 3.3]): fix a test set
   `B` attaining `DA` (`exists_DA_eq`) and let `φ := indicator of B`
   (`{0,1}`-valued ✓). Duhamel: for each `x₀ ∈ A`, chain
   `u k t := ∑_s π k t s·Utest φ t (s.1) (s.2.1)` over the grid
   (`chain_eq`): cell derivative `= ⟨π^{alive}, 𝓑_t U_t⟩` — compute
   `⟨A_k π, U⟩ + ⟨π, ∂_t U⟩` where `∂_t U` from (2) cancels the
   SYNCHRONIZED part `L̄⁰` of the generator (both sectors! dead = pure
   `L̄⁰`); the alive-sector EXCESS rates (W-only `(1-Y^d)/2` for `Y<1`;
   for `Y≥1` the sync deficit `(Y^{1-d}-Y)/2` plus the V-only
   `(Y-Y^{1-d})/2` recombine into the `Δ_i^y(·)(σ_i x, y)` form — the
   algebra: `(sync-deficit)·[U(σx,σy)-U(x,y)] + (V-only)·[U(σx,y)-U(x,y)]
   = (V-only)·[U(σx,y)-U(σx,σy)]` since sync-deficit `= -(V-only)`)
   give exactly the LHS of (4). CAREFUL with sector-blindness: `U` is
   sector-blind, and dead-vs-alive landings of the same jump agree ✓.
   Node transfers preserve the pairing (sector-blind test) ✓ node condition
   of `chain_eq` holds with equality.
   Endpoints: `u(end) = 𝔼_{x₀}[φ(W_{T_o})]` (via `Utest_obsT`);
   `u(start) = Utest φ θ x₀ x₀ = 𝔼_{x₀}[φ(V_{T_o})]` (3).
   So `DtestF (Φ x₀) B = ∑_k ∫_{cell} ⟨π^{alive}, 𝓑U⟩`.
   Then: `|⟨π^a, 𝓑U⟩| ≤ ⟨π^a, |𝓑U|⟩ ≤ √8√κΛ·δ̄·⟨π^a, √(∑S²)·√Γ⟩
   ≤ √8√κΛ·δ̄·√⟨π^a, ∑S²⟩·√⟨π^a, Γ⟩` (Cauchy–Schwarz w.r.t. the finite
   nonneg measure `π^a`; `Finset.inner_mul_le_norm_mul_norm`-style:
   `(∑ p·f·g)² ≤ (∑p f²)(∑p g²)` — prove as helper via
   `Finset.sum_mul_sq_le_sq_mul_sq` with `√(p)f, √(p)g`).
   Integrate over cells and sum over `x₀∈A` with weights `startW`; TWO more
   Cauchy–Schwarz (time and `x₀`) give
   `|∑ startW·Dtest| ≤ √8√κΛ·√(SA)·√(Y_A)` with
   `Y_A := ∑_{x₀∈A} startW·∑_k∫⟨π^a hmm — use the FULL π (alive+dead ≥
   alive) if convenient⟩, Γ⟩` — define `Y_A` as a private def.
   For the time/x₀ Cauchy–Schwarz over sums of integrals, use
   `inner_mul_le_norm_mul_norm` on appropriate finite sums after bounding
   each `∫_{cell}` by CS for integrals
   (`intervalIntegral` CS: `(∫ fg)² ≤ (∫f²)(∫g²)` — via
   `MeasureTheory.integral_mul_le_Lp_mul_Lq` (p=q=2) on the restricted
   measure, or prove the sum-level CS directly by viewing
   `∑_k ∫ = ∫` over the union and applying L² CS once).
   Next, `Y_A ≤ C·(κ·probA + κΛ²·SA)` [LGF eq (4.21)]:
   split `Γ = aB²-part + bB²-part`;
   `bB²`-part `≤ (κ/4)·probA·(T_o - θ ≤ 1)` by (5) + mass;
   `aB²`-part (`Ψ_a`): chain, per ζ then summed with weights, the pairing
   `v k t := ∑_s π k t s·(∑_ζ Hlik t ζ (s.1)·qB φ t ζ (s.1) (s.2.1)²)`
   via `chain_eq`: cell derivative
   `= 2 aB²·⟨π, ∑_ζ Hlik·∑_i lam_i·dmext²⟩ + ⟨π^{alive}, 𝓑(∑_ζ H q²)⟩`
   (carré du champ `hasDerivAt_qB_sq` + the same `H`-twist algebra as (2);
   dead sector contributes only the first term)… note the FIRST term is
   exactly the `aB²`-part integrand `⟨π, Γ_a⟩·2`. Endpoints in `[0, probA]`
   (`0 ≤ q ≤ 1` via `mext_mem_Icc`, `∑Hlik = 1`, mass). The `𝓑(Hq²)` term:
   `|Δ(q²)| ≤ 2|Δq|` (`q ∈ [0,1]`), so it is bounded by twice the (4)-type
   bound with `Γ` — gives `Ψ_a ≤ probA + √8√κΛ·√(SA)·√(Y_A)·2`-ish.
   Collect: `Y_A ≤ C₁(κ·probA + √κΛ√(SA·Y_A))`; solve the quadratic
   (Young: `√κΛ√(SA)√(Y_A) ≤ ½Y_A/C₁ + C₂κΛ²SA`… i.e.
   `ab ≤ εa² + b²/(4ε)`) to get [LGF eq (4.21)]:
   `Y_A ≤ C(κ·probA + κΛ²·SA)`. Substitute back:
   `DA ≤ √8√κΛ√SA·√(C(κ probA + κΛ²SA)) ≤ C'(κΛ√(SA·probA) + κΛ²SA)`
   (`√(x+y) ≤ √x + √y`, `√κ·√κ = κ`, `Λ ≥ 1`).
   Assemble the ∃C statement (pick the explicit constant generously).

Take your time; this file may reach 1500+ lines with helpers. If any stated
theorem seems false as stated, STOP on it, add
`-- STATEMENT-ISSUE: ...` with details, leave its sorry, and continue with
the others.

Gate: `lake build TalagrandConvConjecture.Lemmas.Discrepancy`, zero sorry
(or sorries only under documented STATEMENT-ISSUEs). Commit when done.
