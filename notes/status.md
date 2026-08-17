# TalagrandConvConjecture — status

Updated: 2026-08-17 — **CAMPAIGN COMPLETE**

## Headline — DONE

**`Talagrand.talagrand_convolution_conjecture` is fully proved.**
- Full-library gate: `lake build` exit 0, **zero sorries** (main = 81348d4).
- Axioms audit (`AxiomsCheck.lean`): all 8 audited theorems (both headline
  forms, `fixed_band`, `DA_le`, `weighted_comparison`, `scoreEnergy_le`,
  `band_contraction`, `profile_time_integral_le`) depend only on
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
Provenance: DA_le laptop-proved; fixed_band, weighted_comparison,
scoreEnergy_le lane-proved; band_contraction lane+laptop repairs; all other
modules from the round-1 sixteen-lane fan-out. Statement repairs (falsity
witnesses in-file): unguarded F_flipCoord_sub, hasDerivAt_mB chain,
Profile 0 ≤ s family, expPoly family lemma at N = 0.

## Work packages / fan-out ledger

| package | files | branch | state |
|---|---|---|---|
| cube-foundations | Cube/{Basic,Multilinear,Heat} | tal/cube-foundations | agent running |
| level-one | Cube/LevelOne | tal/level-one | agent running |
| entropy-lsi | Cube/{Entropy,LogSobolev} | tal/entropy-lsi | agent running |
| cutoff-ftc | Analysis/{Cutoff,PiecewiseFTC} | tal/cutoff-ftc | agent running |
| linear-flow | ODE/LinearFlow, Flow/Glued | tal/linear-flow | agent running |
| profile | Profile | tal/profile | agent running |
| reverse-setup | Reverse/Setup | tal/reverse-setup | agent running |
| bridge | Bridge | tal/bridge | queued (post-gate) |
| power-coupling | PowerCoupling, Statement (3 lemmas) | tal/power-coupling | queued (post-gate) |
| coupling-flow | Flow/Coupling | tal/coupling-flow | queued (wave 2) |
| score-energy | Lemmas/{Quantities,ScoreEnergy} | tal/score-energy | queued (wave 2) |
| supermartingale | Lemmas/Supermartingale | tal/supermartingale | queued (wave 2) |
| band-contraction | Lemmas/BandContraction | tal/band-contraction | queued (wave 2) |
| discrepancy | Lemmas/Discrepancy | tal/discrepancy | queued (wave 2) |
| fixed-band | FixedBand | tal/fixed-band | queued (wave 2) |
| main-assembly | Main | tal/main-assembly | queued (wave 2) |

Prompts: `.claude/prompts/<package>.md` (proof routes hand-verified).

## Verification protocol per branch
1. `lean-fasrc-build --worktree tal/<x> TalagrandConvConjecture.<Module>` —
   fresh build, zero sorry in the touch-set files.
2. Diff review: statements unchanged, no new hypotheses, touch-set respected,
   no lakefile/manifest/toolchain/umbrella edits, no `axiom`.
3. Merge into laptop main (disjoint files → clean merges), re-gate.

Final: full-lib zero-sorry build + `#print axioms` on the headline theorems.
