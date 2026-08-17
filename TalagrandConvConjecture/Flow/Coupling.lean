import TalagrandConvConjecture.Flow.Glued
import TalagrandConvConjecture.PowerCoupling
import TalagrandConvConjecture.Bridge

/-!
# The stopped power coupling as a glued flow [LGF §3–4]

Fix data `D`, tail level `ℓ`, start time `θ ∈ [T_o - 1, T_o]`, and starting
point `x₀`. The coupled pair `(V_t, W_t)` with predictable stopping indicator
`1_{t ≤ τ}` ([LGF eq (4.1)], `τ` from [LGF eq (3.1)]) is a Markov process on
the sectored state space `JSt n = Cube n × Cube n × Bool` (sector `true` =
"alive", i.e. `t ≤ τ`). Its law solves a linear master equation whose
coefficients are continuous except at the finitely many crossing times of the
barrier `{x | F_t(x) ≥ ℓ+1}`; at those nodes, alive mass sitting on a
newly-barrier state is transferred to the dead sector (`τ` fires by
continuous crossing). Jumps of `V` into the barrier land directly in the dead
sector (`τ` fires by jump).

Alive-sector out-rates (frozen exponent `d = δ̄(x₀)`, `Y = Y_i(t,x)`;
[LGF §4, interpretation of the coupling]):
* `Y < 1`: synchronized flip `(σ_i x, σ_i y)` at rate `Y/2`; `W`-only flip
  `(x, σ_i y)` at rate `(1 - Y^d)/2`;
* `Y ≥ 1`: synchronized flip at rate `Y^{1-d}/2`; `V`-only flip `(σ_i x, y)`
  at rate `(Y - Y^{1-d})/2`.
Dead sector: synchronized flips at rate `Y/2`. `V`-moving jumps land in the
dead sector iff the new `V`-position is in the cell's barrier.

`IsCouplingFlow` packages a glued flow for these rates on an admissible grid;
existence and the basic transport properties are provided. All quantities of
[LGF §3] (`𝒮_A`, `D_A`, `A_θ(r)`, `B_θ(ℓ)`) are defined from a bundled
`CFlowFamily`.
-/

namespace Talagrand

variable {n : ℕ}

/-- Sectored joint state space: `(V-position, W-position, alive?)`. -/
abbrev JSt (n : ℕ) := Cube n × Cube n × Bool

namespace Dat

variable (D : Dat n)

/-- The moving barrier `{x | F_t(x) ≥ ℓ+1}` of the stopping time
[LGF eq (3.1)]. -/
def barrier (ℓ t : ℝ) : Set (Cube n) := {x | ℓ + 1 ≤ D.F t x}

/-- An admissible grid on `[θ, T_o]`: monotone nodes from `θ` to `T_o` such
that no barrier crossing `F_t(x) = ℓ+1` happens in any open cell. On such a
grid the barrier is constant on each open cell. -/
structure AdmissibleGrid (ℓ θ : ℝ) (K : ℕ) (z : ℕ → ℝ) : Prop where
  pos : 0 < K
  first : z 0 = θ
  last : z K = obsT
  mono : ∀ k, k < K → z k ≤ z (k + 1)
  nocross : ∀ k, k < K → ∀ t ∈ Set.Ioo (z k) (z (k + 1)), ∀ x : Cube n,
    D.F t x ≠ ℓ + 1

/-- Existence of an admissible grid: barrier crossings are roots of a nonzero
polynomial in `e^{-(T-t)}` (constant coefficient `1 ≠ e^{ℓ+1}`), hence
finitely many; sort them. -/
theorem exists_admissibleGrid (ℓ : ℝ) (hℓ : 0 < ℓ) {θ : ℝ} (hθ : θ ≤ obsT) :
    ∃ K z, D.AdmissibleGrid ℓ θ K z := by
  sorry

/-- Barrier membership is constant on open cells of an admissible grid
(intermediate value theorem plus `nocross`). -/
theorem barrier_const_on_cell {ℓ θ : ℝ} {K : ℕ} {z : ℕ → ℝ}
    (hg : D.AdmissibleGrid ℓ θ K z) {k : ℕ} (hk : k < K)
    {t t' : ℝ} (ht : t ∈ Set.Ioo (z k) (z (k + 1)))
    (ht' : t' ∈ Set.Ioo (z k) (z (k + 1))) (x : Cube n) :
    x ∈ D.barrier ℓ t ↔ x ∈ D.barrier ℓ t' := by
  sorry

open Classical in
/-- Alive/dead out-rate table at time `t`, with frozen exponent `d` and
current-cell barrier `B`. `jrate D d B t s s'` is the jump rate from `s` to
`s'` (zero on the diagonal and for non-neighbors). -/
noncomputable def jrate (d : ℝ) (B : Set (Cube n)) (t : ℝ) :
    JSt n → JSt n → ℝ := fun s s' =>
  match s, s' with
  | (x, y, b), (x', y', b') =>
    ∑ i : Fin n,
      (-- synchronized flip along coordinate i
        (if x' = flipCoord i x ∧ y' = flipCoord i y ∧
            (b' = (b && decide (x' ∉ B))) then
          (if b then
            (if D.Y t i x < 1 then D.Y t i x / 2
             else D.Y t i x ^ (1 - d) / 2)
           else D.Y t i x / 2)
        else 0)
      + -- W-only flip (alive only, Y < 1)
        (if b ∧ b' = true ∧ x' = x ∧ y' = flipCoord i y ∧ D.Y t i x < 1 then
          (1 - D.Y t i x ^ d) / 2
        else 0)
      + -- V-only flip (alive only, Y ≥ 1)
        (if b ∧ y' = y ∧ x' = flipCoord i x ∧ ¬(D.Y t i x < 1) ∧
            (b' = decide (x' ∉ B)) then
          (D.Y t i x - D.Y t i x ^ (1 - d)) / 2
        else 0))

open Classical in
/-- Node transfer: alive mass on a state in the closed barrier at the node
time is moved to the dead sector (continuous crossing of `τ`); everything
else is unchanged. `killTr D ℓ t` as a matrix (entries in `{0,1}`). -/
noncomputable def killTr (ℓ t : ℝ) : JSt n → JSt n → ℝ := fun s s' =>
  match s, s' with
  | (x, y, b), (x', y', b') =>
    if x = x' ∧ y = y' ∧
        (b = (b' && decide (x' ∉ D.barrier ℓ t))) then 1 else 0

/-- Cell generator: forward matrix of the out-rates, with the cell barrier
sampled at the cell midpoint. -/
noncomputable def cellGen (ℓ θ d : ℝ) (z : ℕ → ℝ) (k : ℕ) (t : ℝ) :
    JSt n → JSt n → ℝ :=
  fwdOf (jrate D d (D.barrier ℓ ((z k + z (k + 1)) / 2)) t)

/-- Initial vector: unit mass at `(x₀, x₀, alive)`. (The `Tr 0` step of the
glued flow then kills it if `x₀` is already in the barrier at `θ`, matching
`τ = θ` in [LGF eq (3.1)].) -/
noncomputable def initVec (x₀ : Cube n) : JSt n → ℝ := fun s =>
  if s = (x₀, x₀, true) then 1 else 0

/-- `IsCouplingFlow D ℓ θ x₀ K z π`: `π` is a glued flow for the stopped
power coupling started at `(x₀, x₀)` at time `θ`, on the admissible grid
`z`. -/
structure IsCouplingFlow (ℓ θ : ℝ) (x₀ : Cube n) (K : ℕ) (z : ℕ → ℝ)
    (π : ℕ → ℝ → JSt n → ℝ) : Prop where
  grid : D.AdmissibleGrid ℓ θ K z
  glued : IsGluedFlow K z (D.cellGen ℓ θ (D.dbar ℓ θ x₀) z)
    (fun k => D.killTr ℓ (z k)) (D.initVec x₀) π

/-- A bundled coupling flow for one starting point. -/
structure CFlow (ℓ θ : ℝ) (x₀ : Cube n) where
  K : ℕ
  z : ℕ → ℝ
  π : ℕ → ℝ → JSt n → ℝ
  is : D.IsCouplingFlow ℓ θ x₀ K z π

/-- A family of coupling flows, one per starting point (the grids may
differ). -/
def CFlowFamily (ℓ θ : ℝ) := ∀ x₀ : Cube n, D.CFlow ℓ θ x₀

/-- **Existence of the coupling flow** [LGF §4; C Lemma 6 well-posedness]. -/
theorem exists_cflow (ℓ : ℝ) (hℓ : 0 < ℓ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ obsT) (x₀ : Cube n) : Nonempty (D.CFlow ℓ θ x₀) := by
  sorry

/-- Terminal (time `T_o`) sub-law of a coupling flow. -/
noncomputable def CFlow.term {ℓ θ : ℝ} {x₀ : Cube n} (c : D.CFlow ℓ θ x₀) :
    JSt n → ℝ := c.π (c.K - 1) obsT

/-! ## Transport properties of the coupling flow -/

variable {ℓ θ : ℝ} {x₀ : Cube n}

/-- Nonnegativity of the flow. -/
theorem cflow_nonneg (hθ : θ ≤ obsT) (c : D.CFlow ℓ θ x₀)
    {k : ℕ} (hk : k < c.K) {t : ℝ} (ht : t ∈ Set.Icc (c.z k) (c.z (k + 1)))
    (s : JSt n) : 0 ≤ c.π k t s := by
  sorry

/-- Total mass conservation: `∑_s π_t(s) = 1` throughout. -/
theorem cflow_mass (hθ : θ ≤ obsT) (c : D.CFlow ℓ θ x₀)
    {k : ℕ} (hk : k < c.K) {t : ℝ} (ht : t ∈ Set.Icc (c.z k) (c.z (k + 1))) :
    ∑ s, c.π k t s = 1 := by
  sorry

/-- Alive-sector support: alive mass never sits on a state of the current
cell's barrier (interior of the cell), and at the cell's endpoints alive mass
sits only on states with `F ≤ ℓ+1`. Stated in the endpoint form used
downstream: alive terminal mass satisfies `F_{T_o}(x) ≤ ℓ+1`. -/
theorem cflow_alive_support (hθ : θ ≤ obsT) (c : D.CFlow ℓ θ x₀)
    (x y : Cube n) (h : ℓ + 1 < D.F obsT x) :
    c.term (x, y, true) = 0 := by
  sorry

/-- The `V`-marginal of the coupling flow is the plain reverse flow: for
every sector-blind, `y`-blind test `g` the terminal pairing is transport of
`g` along the unperturbed reverse process from `(θ, x₀)` to `T_o`
[LGF Lemma 5.1, joint filtration / reverse marginal]. Concretely: the
`V`-marginal pairing equals the value at `(θ, x₀)` of the space-time
harmonic extension of `g`. -/
theorem cflow_V_marginal (hθ0 : 0 ≤ θ) (hθ : θ ≤ obsT) (c : D.CFlow ℓ θ x₀)
    (g : ℝ → Cube n → ℝ)
    (hg_cont : ∀ x, ContinuousOn (fun t => g t x) (Set.Icc θ obsT))
    (hg_deriv : ∀ x, ∀ t ∈ Set.Icc θ obsT,
      HasDerivWithinAt (fun t => g t x) (-(D.revGen t (g t) x))
        (Set.Icc θ obsT) t) :
    ∑ s, c.term s * g obsT s.1 = g θ x₀ := by
  sorry

end Dat

end Talagrand
