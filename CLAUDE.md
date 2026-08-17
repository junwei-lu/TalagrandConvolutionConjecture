# TalagrandConvConjecture — project charter

Formalization of **Talagrand's convolution conjecture on the Boolean hypercube**
(Lu–Guo–Fang, "Weak-Type Bounds for Convolution on the Boolean Hypercube",
`talagrand/ref/main/main.tex` in the parent working folder; referred to as
**[LGF]** below). External inputs come from Chen 2026 ([C], `ref/Chen/main.tex`)
and Xiang–Zhang 2026 ([XZ], `ref/XZ/main.tex`).

Headline target: `Talagrand.talagrand_convolution_conjecture` in
`TalagrandConvConjecture/Statement.lean` — for every `0 < a < 1`, `u > 1`, `n`,
and density `f ≥ 0` with `𝔼_λ f = 1`,
`u·λ(T_{μ_a} f ≥ u) ≤ C·K_a/√(log u)` with a universal `C`,
where `K_a = κ_a² (log κ_a/(κ_a-1))^{1/2}`, `κ_a = (1+a)/(1-a)`.

## Ground rules

- **Independent Lake project.** Own toolchain (`v4.29.1`), own manifest.
  Mathlib pinned to tag `v4.29.1` (same rev as StatLean so the cluster's
  shared compiled Mathlib applies). StatLean is required from GitHub
  (`StatLean/Stat-Lean` @ `a13a30b6`) — usable like Mathlib, never edited here.
- **Never run `lake update`.** Never edit `lakefile.lean`, `lake-manifest.json`,
  `lean-toolchain` (laptop session owns them).
- **No `axiom`, no `admit`.** `sorry` only as a named, well-stated debt.
- Builds run on FAS-RC via the `lean-on-fasrc` skill; the laptop never runs
  `lake build`.
- Every `theorem`/`def` formalizing a paper statement carries a docstring with
  the paper tag (e.g. `[LGF Lemma 3.3]`, `[C Lemma 4]`, `[LGF eq (17)]`).
  Deviations from the paper (different constants, strengthened/weakened forms)
  must be stated in the docstring.

## Design (read before touching the probability layer)

The paper's stochastic objects are formalized **without** any path-space
probability ("de-probabilized"): all processes on the finite cube are replaced
by solutions of finite-dimensional linear ODEs (Kolmogorov/master equations),
martingale arguments become derivative-sign arguments for pairings
`t ↦ ∑_s π_t(s)·g_t(s)`, and the stopping time `τ` (first entry of the
log-density of the reverse process into `[ℓ+1,∞)`) is realized by an
alive/dead two-sector flow glued across the finitely many "crossing times"
(finiteness = finiteness of roots of a polynomial in `e^{-t}`). The
supermartingale of [LGF §4.2] is replaced by the slightly weaker terminal
`N`-weighted comparison, which is exactly what [LGF Lemma 3.4]'s proof
consumes. Main-theorem faithfulness is unaffected: the headline statement is
purely finite/analytic.

Module map (import order):
`Cube/Basic → Cube/Multilinear → Cube/Heat → Statement`;
`Cube/LevelOne` ([C Lemma 7]); `Cube/Entropy`, `Cube/LogSobolev`,
`Analysis/Cutoff`, `Analysis/PiecewiseFTC`, `Profile` ([C Lemma 4]);
`ODE/LinearFlow`; `Reverse/Setup`; `Bridge`; `PowerCoupling`;
`Flow/*` (glued flows); `Lemmas/*` ([LGF Lemmas 3.3–3.6]); `FixedBand`
([LGF Prop 3.2]); `Main` ([LGF Thm 1.1]).

## Cluster subagent rules

- Work only in the files named by your prompt (touch-set). Never edit
  `TalagrandConvConjecture.lean` (umbrella), lakefile/manifest/toolchain,
  or files outside your touch-set.
- Close `sorry`s without changing the statements. If a statement appears
  false or unprovable as stated, do NOT silently change it: leave the `sorry`,
  and record the issue in a comment `-- STATEMENT-ISSUE: <explanation>` above
  the declaration, plus a falsity witness if you have one.
- `lake build TalagrandConvConjecture.<Module>` is the gate; a module is done
  when it compiles with zero `sorry` and no new hypotheses on public lemmas.
