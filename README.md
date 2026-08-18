# Talagrand's Convolution Conjecture — a Lean 4 formalization

A complete, machine-checked proof of the paper "Weak-Type Bounds for Convolution on the Boolean Hypercube" by Junwei Lu, Shengtao Guo, Ethan X. Fang, [https://arxiv.org/abs/2608.15515](https://arxiv.org/abs/2608.15515), formalized in Lean 4 over
[Mathlib](https://github.com/leanprover-community/mathlib4). This proves the [Talagrand's convolution conjecture](https://michel.talagrand.net/Korea13.pdf).
The library compiles with **zero `sorry`** and the headline theorem depends
only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Talagrand's Convolution Conjecture

Let $\lambda$ be the uniform measure on the hypercube $ \{ -1,1 \}^n$ and, for a
bias $0 < a < 1$, let $T_{\mu_a} f = f * \mu_a$ denote convolution with the
$a$-biased product measure $\mu_a$. Talagrand (1989) conjectured that
convolution smooths tails strictly beyond Markov's inequality, by a factor
$1/\sqrt{\log u}$. The theorem proved here: there is a universal constant
$C$ such that for every $n \ge 0$, every $0 < a < 1$, every density
$f \ge 0$ with $\mathbb{E}_\lambda f = 1$, and every $u > 1$,

$$u \cdot \lambda(\{\, T_{\mu_a} f \ge u ) \le \frac{C\, K_a}{\sqrt{\log u}}, K_a = \kappa_a^2 \sqrt{\frac{\log \kappa_a}{\kappa_a - 1}}, \kappa_a = \frac{1+a}{1-a}.$$

The formalization follows the proof of

- J. Lu, S. Guo, E. X. Fang, *Weak-Type Bounds for Convolution on the Boolean
  Hypercube* (**[LGF]** in docstring tags),

which builds on

- Y. Chen, *Talagrand's convolution conjecture up to $\log\log$ via perturbed
  reverse heat*, 2026 (**[C]**), and
- Y. Xiang, Z. Zhang, *Layerwise Terminal Discrepancy in Chen's Reverse-Heat
  Coupling on the Boolean Cube*, 2026 (**[XZ]**).

All intermediate results of these papers that the proof needs (Chen's
time-smoothed entropy profile and level-one bounds, the reverse-heat coupling,
the discrepancy/score-energy/band-contraction lemmas, the fixed-band
proposition) are formalized in this repository; nothing is assumed.

## Where the main theorem is

The headline statements are in
[`TalagrandConvConjecture/Main.lean`](TalagrandConvConjecture/Main.lean):

```lean
theorem talagrand_convolution_conjecture :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (a u : ℝ) (f : Cube n → ℝ),
        0 < a → a < 1 → 1 < u → (∀ x, 0 ≤ f x) → unifE f = 1 →
        u * unifMeas {x | u ≤ biasedConv a f x}
          ≤ C * Ka a / Real.sqrt (Real.log u)
```

together with the equivalent tail-functional form
`talagrand_convolution_conjecture_psi`. The primitive definitions
(`Cube`, uniform expectation `unifE`, normalized counting measure `unifMeas`,
the convolution operator `biasedConv`, and the constants `kappa`, `Ka`) live in
[`TalagrandConvConjecture/Statement.lean`](TalagrandConvConjecture/Statement.lean)
and are deliberately elementary — finite sums over `{-1,1}^n` — so the
statement can be audited without trusting any of the proof machinery.

Rough module map (paper tags in docstrings):
`Cube/*` (hypercube analysis: heat semigroup, entropy, log-Sobolev with
constant 4, level-one Fourier bound [C Lemma 7]) → `Profile` (time-smoothed
profile, [C Lemma 4]) → `ODE/LinearFlow`, `Reverse/Setup`, `Flow/*`
(the reverse-heat process, de-probabilized as finite-dimensional linear ODE
flows with an alive/dead two-sector gluing replacing the stopping time) →
`Lemmas/*` ([LGF Lemmas 3.3–3.6]) → `FixedBand` ([LGF Prop 3.2]) → `Main`
([LGF Thm 1.1]).

## How to certify the proof

Prerequisites: [`elan`](https://github.com/leanprover/elan) (the Lean
toolchain manager). The pinned toolchain (`lean-toolchain`,
Lean `v4.29.1`) is installed automatically on first build.

```bash
git clone https://github.com/junwei-lu/TalagrandConvolutionConjecture.git
cd TalagrandConvolutionConjecture
lake exe cache get    # download the prebuilt Mathlib cache (avoids compiling Mathlib)
lake build            # compile the whole library
```

`lake build` must finish with no errors **and no `sorry` warnings** — the
library contains none (`grep -rn "sorry" TalagrandConvConjecture/` returns
nothing). The declared StatLean dependency is fetched but contributes no
compiled module to the proof.

Then check the axiom footprint of the main results:

```bash
lake env lean AxiomsCheck.lean
```

Expected output — every listed theorem, including the headline, reports
exactly Lean's three standard axioms:

```
'Talagrand.talagrand_convolution_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
'Talagrand.talagrand_convolution_conjecture_psi' depends on axioms: [propext, Classical.choice, Quot.sound]
...
```

No `axiom` or `admit` appears anywhere in the repository, so this output
certifies that the theorem is proved unconditionally within Lean's standard
foundations.
