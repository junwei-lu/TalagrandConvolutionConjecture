import TalagrandConvConjecture.Cube.Basic

/-!
# Entropy on finite probability spaces and tensorization on the cube

`ent w g = ∑ w i·g i·log(g i) - (∑ w i·g i)·log(∑ w i·g i)` for nonnegative
`g` and probability weights `w` on a finite index type (with the convention
`0·log 0 = 0`, which is automatic since `Real.log 0 = 0`).

Contents (needed for [C Lemma 4], the time-smoothed profile bound):
* the variational lower bound `∑ w g φ ≤ ent w g` whenever `∑ w e^φ ≤ 1`
  [C eq (entropy variational form)];
* the exact chain identity `ent_{μ⊗ν} h = 𝔼_μ[ent_ν h] + ent_μ(𝔼_ν h)`;
* "entropy of an average ≤ average of entropies" (from the variational sup
  representation);
* subadditivity/tensorization over the cube:
  `entUnif h ≤ ∑_i 𝔼_λ[pairEnt i h]` where `pairEnt i h x` is the entropy of
  `h` restricted to the two-point pair `{x, σ_i x}` with uniform weights.
-/

namespace Talagrand

variable {ι : Type*} [Fintype ι]

/-- Entropy functional `Ent_w(g)` on a finite space with weights `w`. -/
noncomputable def ent (w g : ι → ℝ) : ℝ :=
  ∑ i, w i * (g i * Real.log (g i)) -
    (∑ i, w i * g i) * Real.log (∑ i, w i * g i)

/-- Pointwise Young inequality `g·φ ≤ g·log g - g + e^φ` for `g ≥ 0`. -/
lemma mul_le_mul_log_sub_add_exp {g φ : ℝ} (hg : 0 ≤ g) :
    g * φ ≤ g * Real.log g - g + Real.exp φ := by
  rcases eq_or_lt_of_le hg with h | h
  · rw [← h]
    simpa using (Real.exp_pos φ).le
  · have hg0 : g ≠ 0 := ne_of_gt h
    have hlog : Real.log (Real.exp φ / g) ≤ Real.exp φ / g - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos φ) h)
    rw [Real.log_div (Real.exp_ne_zero φ) hg0, Real.log_exp] at hlog
    have key : g * (φ - Real.log g) ≤ g * (Real.exp φ / g - 1) :=
      mul_le_mul_of_nonneg_left hlog h.le
    have hcalc : g * (Real.exp φ / g - 1) = Real.exp φ - g := by
      field_simp
    rw [hcalc, mul_sub] at key
    linarith

/-- `(g/m)·log(g/m) = (g·log g - g·log m)/m` for `g ≥ 0`, `m > 0` (the `g = 0`
case uses the junk value `log 0 = 0`). -/
private lemma mul_log_div {g m : ℝ} (hg : 0 ≤ g) (hm : 0 < m) :
    g / m * Real.log (g / m) = (g * Real.log g - g * Real.log m) / m := by
  rcases eq_or_lt_of_le hg with h | h
  · rw [← h]; simp
  · rw [Real.log_div (ne_of_gt h) (ne_of_gt hm), mul_sub, div_mul_eq_mul_div,
      div_mul_eq_mul_div, ← sub_div]

/-- Normalized form of the variational bound (`∑ w g = 1`). -/
private lemma sum_mul_le_ent_norm (w g φ : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hg : ∀ i, 0 ≤ g i) (hφ : ∑ i, w i * Real.exp (φ i) ≤ 1)
    (h1 : ∑ i, w i * g i = 1) :
    ∑ i, w i * (g i * φ i) ≤ ∑ i, w i * (g i * Real.log (g i)) := by
  have step : ∑ i, w i * (g i * φ i)
      ≤ ∑ i, w i * (g i * Real.log (g i) - g i + Real.exp (φ i)) :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (mul_le_mul_log_sub_add_exp (hg i)) (hw i)
  have expand : ∑ i, w i * (g i * Real.log (g i) - g i + Real.exp (φ i))
      = ∑ i, (w i * (g i * Real.log (g i)) - w i * g i + w i * Real.exp (φ i)) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1] at step
  linarith

/-- **Variational lower bound for entropy**: if `w` are probability weights,
`g ≥ 0`, and `∑ w e^φ ≤ 1`, then `∑ w·g·φ ≤ Ent_w(g)`. [C, proof of Lemma 4,
step (entropy_vs_anti_concentration_profile).] -/
theorem sum_mul_le_ent (w g φ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hg : ∀ i, 0 ≤ g i) (hφ : ∑ i, w i * Real.exp (φ i) ≤ 1) :
    ∑ i, w i * (g i * φ i) ≤ ent w g := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ i, w i * g i := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hg i)
  rcases eq_or_lt_of_le hM0 with hz | hpos
  · have hzero : ∀ i, w i * g i = 0 := by
      intro i
      refine (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hw j) (hg j))).1 ?_ i (Finset.mem_univ i)
      rw [← hM, ← hz]
    have hL : ∑ i, w i * (g i * φ i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [← mul_assoc, hzero i, zero_mul]
    have hE : ∑ i, w i * (g i * Real.log (g i)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [← mul_assoc, hzero i, zero_mul]
    rw [hL]
    simp only [ent, hE, ← hM, ← hz]
    simp
  · have hMne : M ≠ 0 := ne_of_gt hpos
    have hG1 : ∑ i, w i * (g i / M) = 1 := by
      have e : ∑ i, w i * (g i / M) = (∑ i, w i * g i) / M := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, ← hM, div_self hMne]
    have hnorm : ∑ i, w i * (g i / M * φ i)
        ≤ ∑ i, w i * (g i / M * Real.log (g i / M)) :=
      sum_mul_le_ent_norm w (fun i => g i / M) φ hw
        (fun i => div_nonneg (hg i) hpos.le) hφ hG1
    have hL : ∑ i, w i * (g i / M * φ i) = (∑ i, w i * (g i * φ i)) / M := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hR : ∑ i, w i * (g i / M * Real.log (g i / M))
        = (∑ i, w i * (g i * Real.log (g i)) - M * Real.log M) / M := by
      have h1 : ∀ i ∈ (Finset.univ : Finset ι),
          w i * (g i / M * Real.log (g i / M))
            = (w i * (g i * Real.log (g i)) - w i * g i * Real.log M) / M := by
        intro i _
        rw [mul_log_div (hg i) hpos]
        ring
      rw [Finset.sum_congr rfl h1, ← Finset.sum_div, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← hM]
    rw [hL, hR] at hnorm
    have h2 := mul_le_mul_of_nonneg_right hnorm hpos.le
    rw [div_mul_cancel₀ _ hMne, div_mul_cancel₀ _ hMne] at h2
    simp only [ent, ← hM]
    exact h2

/-- Entropy is nonnegative for probability weights and nonnegative `g`. -/
lemma ent_nonneg (w g : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hg : ∀ i, 0 ≤ g i) : 0 ≤ ent w g := by
  have h := sum_mul_le_ent w g (fun _ => 0) hw hw1 hg (by simpa using hw1.le)
  simpa using h

/-- Entropy of an average is at most the average of entropies: for probability
weights `p` on `κ` and `w` on `ι`, and `h : κ → ι → ℝ` nonnegative,
`Ent_w(∑_k p k • h k) ≤ ∑_k p k · Ent_w(h k)`. (From the sup representation:
`Ent_w` is a supremum of linear functionals.) -/
theorem ent_average_le {κ : Type*} [Fintype κ] (p : κ → ℝ) (w : ι → ℝ)
    (h : κ → ι → ℝ) (hp : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hh : ∀ k i, 0 ≤ h k i) :
    ent w (fun i => ∑ k, p k * h k i) ≤ ∑ k, p k * ent w (h k) := by
  set G : ι → ℝ := fun i => ∑ k, p k * h k i with hGdef
  have hGi : ∀ i, G i = ∑ k, p k * h k i := fun i => rfl
  have hGnn : ∀ i, 0 ≤ G i := fun i => by
    rw [hGi i]; exact Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (hh k i)
  have hRnn : 0 ≤ ∑ k, p k * ent w (h k) :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (hp k) (ent_nonneg w (h k) hw hw1 (hh k))
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ i, w i * G i := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hGnn i)
  rcases eq_or_lt_of_le hM0 with hz | hpos
  · have hzero : ∀ i, w i * G i = 0 := by
      intro i
      refine (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hw j) (hGnn j))).1 ?_ i (Finset.mem_univ i)
      rw [← hM, ← hz]
    have hE : ∑ i, w i * (G i * Real.log (G i)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [← mul_assoc, hzero i, zero_mul]
    have hent : ent w G = 0 := by
      simp only [ent, hE, ← hM, ← hz]; simp
    rw [hent]
    exact hRnn
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ M * δ ≤ ε :=
      ⟨ε / M, div_pos hε hpos,
        le_of_eq (by rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hpos)])⟩
    obtain ⟨φ, hφdef⟩ : ∃ φ : ι → ℝ,
        ∀ i, φ i = Real.log ((G i / M + δ) / (1 + δ)) := ⟨_, fun _ => rfl⟩
    have hδ1 : (0:ℝ) < 1 + δ := by linarith
    have hpos' : ∀ i, 0 < (G i / M + δ) / (1 + δ) := by
      intro i
      have : 0 ≤ G i / M := div_nonneg (hGnn i) hpos.le
      exact div_pos (by linarith) hδ1
    have hexpφ : ∀ i, Real.exp (φ i) = (G i / M + δ) / (1 + δ) := by
      intro i; rw [hφdef i]; exact Real.exp_log (hpos' i)
    have hsumexp : ∑ i, w i * Real.exp (φ i) ≤ 1 := by
      have e : ∑ i, w i * Real.exp (φ i)
          = (∑ i, (w i * (G i / M) + δ * w i)) / (1 + δ) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by rw [hexpφ i]; ring
      have e2 : ∑ i, w i * (G i / M) = 1 := by
        have e3 : ∑ i, w i * (G i / M) = (∑ i, w i * G i) / M := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [e3, ← hM, div_self (ne_of_gt hpos)]
      have e4 : ∑ i, (w i * (G i / M) + δ * w i) = 1 + δ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hw1, mul_one, e2]
      rw [e, e4, div_self (ne_of_gt hδ1)]
    -- lower bound for the linear functional at `φ`
    have hterm : ∀ i, w i * (G i * Real.log (G i) - G i * Real.log M
        - G i * Real.log (1 + δ)) ≤ w i * (G i * φ i) := by
      intro i
      rcases eq_or_lt_of_le (hGnn i) with h0 | h0
      · rw [← h0]; simp
      · have h1 : (0:ℝ) < G i / M := div_pos h0 hpos
        have h2 : Real.log (G i / M) ≤ Real.log (G i / M + δ) :=
          Real.log_le_log h1 (by linarith)
        have h3 : φ i = Real.log (G i / M + δ) - Real.log (1 + δ) := by
          rw [hφdef i]
          exact Real.log_div (by linarith) (ne_of_gt hδ1)
        have h4 : Real.log (G i / M) = Real.log (G i) - Real.log M :=
          Real.log_div (ne_of_gt h0) (ne_of_gt hpos)
        have h5 : Real.log (G i) - Real.log M - Real.log (1 + δ) ≤ φ i := by
          rw [h3, ← h4]; linarith
        have h6 : 0 ≤ w i * G i := mul_nonneg (hw i) (hGnn i)
        have h7 := mul_le_mul_of_nonneg_left h5 h6
        nlinarith [h7]
    have hd : ent w G ≤ ∑ i, w i * (G i * φ i) + M * Real.log (1 + δ) := by
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
      have expand : ∑ i, w i * (G i * Real.log (G i) - G i * Real.log M
            - G i * Real.log (1 + δ))
          = ∑ i, w i * (G i * Real.log (G i)) - M * Real.log M
            - M * Real.log (1 + δ) := by
        have h1 : ∀ i ∈ (Finset.univ : Finset ι),
            w i * (G i * Real.log (G i) - G i * Real.log M
              - G i * Real.log (1 + δ))
            = w i * (G i * Real.log (G i)) - w i * G i * Real.log M
              - w i * G i * Real.log (1 + δ) := fun i _ => by ring
        rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← hM]
      rw [expand] at hsum
      simp only [ent, ← hM]
      linarith
    have hb : ∀ k, ∑ i, w i * (h k i * φ i) ≤ ent w (h k) := fun k =>
      sum_mul_le_ent w (h k) φ hw hw1 (hh k) hsumexp
    have hc : ∑ i, w i * (G i * φ i)
        = ∑ k, p k * (∑ i, w i * (h k i * φ i)) := by
      have e1 : ∀ i ∈ (Finset.univ : Finset ι),
          w i * (G i * φ i) = ∑ k, p k * (w i * (h k i * φ i)) := by
        intro i _
        rw [hGi i, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [Finset.sum_congr rfl e1, Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    have he : M * Real.log (1 + δ) ≤ ε := by
      have hlog : Real.log (1 + δ) ≤ δ := by
        have := Real.log_le_sub_one_of_pos hδ1
        linarith
      nlinarith [hM0]
    have hfin : ∑ k, p k * (∑ i, w i * (h k i * φ i))
        ≤ ∑ k, p k * ent w (h k) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hb k) (hp k)
    rw [hc] at hd
    linarith

variable {n : ℕ}

/-- Entropy of `h` under the uniform measure on the cube. -/
noncomputable def entUnif (h : Cube n → ℝ) : ℝ :=
  unifE (fun x => h x * Real.log (h x)) - unifE h * Real.log (unifE h)

/-- Two-point entropy of `h` along the `i`-th edge at `x`: entropy of the pair
`(h x, h (σ_i x))` under uniform weights `(1/2, 1/2)`. Symmetric in
`x ↔ σ_i x`. -/
noncomputable def pairEnt (i : Fin n) (h : Cube n → ℝ) (x : Cube n) : ℝ :=
  (h x * Real.log (h x) + h (flipCoord i x) * Real.log (h (flipCoord i x))) / 2
    - (h x + h (flipCoord i x)) / 2 * Real.log ((h x + h (flipCoord i x)) / 2)

/-! ### Two-point entropy as a function of the two values -/

/-- The two-point entropy of the pair of values `(s, t)` with uniform weights. -/
private noncomputable def ent2 (s t : ℝ) : ℝ :=
  (s * Real.log s + t * Real.log t) / 2 - (s + t) / 2 * Real.log ((s + t) / 2)

private lemma pairEnt_eq_ent2 (i : Fin n) (g : Cube n → ℝ) (x : Cube n) :
    pairEnt i g x = ent2 (g x) (g (flipCoord i x)) := rfl

private lemma ent_fin2 (g : Fin 2 → ℝ) :
    ent (fun _ : Fin 2 => (1:ℝ)/2) g = ent2 (g 0) (g 1) := by
  simp only [ent, ent2, Fin.sum_univ_two]
  rw [show (1:ℝ)/2 * g 0 + 1/2 * g 1 = (g 0 + g 1) / 2 by ring]
  ring

/-- Convexity of the two-point entropy. -/
private lemma ent2_avg_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    ent2 ((a + c) / 2) ((b + d) / 2) ≤ (ent2 a b + ent2 c d) / 2 := by
  have hp1 : ∑ _k : Fin 2, (1:ℝ)/2 = 1 := by
    rw [Fin.sum_univ_two]; norm_num
  have hnn : ∀ (k i : Fin 2), 0 ≤ (![![a,b],![c,d]] : Fin 2 → Fin 2 → ℝ) k i := by
    intro k i
    fin_cases k <;> fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const, Matrix.cons_val_fin_one] <;> assumption
  have key : ent (fun _ : Fin 2 => (1:ℝ)/2)
        (fun i => ∑ k, (1:ℝ)/2 * (![![a,b],![c,d]] : Fin 2 → Fin 2 → ℝ) k i)
      ≤ ∑ k, (1:ℝ)/2 * ent (fun _ : Fin 2 => (1:ℝ)/2)
        ((![![a,b],![c,d]] : Fin 2 → Fin 2 → ℝ) k) :=
    ent_average_le _ _ _ (fun _ => by norm_num) hp1 (fun _ => by norm_num) hp1 hnn
  rw [ent_fin2] at key
  have e0 : ∑ k, (1:ℝ)/2 * (![![a,b],![c,d]] : Fin 2 → Fin 2 → ℝ) k 0
      = (a + c) / 2 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have e1 : ∑ k, (1:ℝ)/2 * (![![a,b],![c,d]] : Fin 2 → Fin 2 → ℝ) k 1
      = (b + d) / 2 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  rw [e0, e1] at key
  refine key.trans (le_of_eq ?_)
  rw [Fin.sum_univ_two, ent_fin2, ent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-! ### Splitting the cube along the first coordinate -/

private lemma sum_units (f : ℤˣ → ℝ) : ∑ u : ℤˣ, f u = f 1 + f (-1) := by
  rw [UnitsInt.univ, Finset.sum_pair (by decide)]

private lemma sum_cube_succ (F : Cube (n+1) → ℝ) :
    ∑ x : Cube (n+1), F x
      = ∑ y : Cube n, (F (Fin.cons 1 y) + F (Fin.cons (-1) y)) := by
  have h1 : ∑ p : ℤˣ × Cube n, F (Fin.cons p.1 p.2) = ∑ x : Cube (n+1), F x :=
    Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n+1) => ℤˣ) _ _ fun _ => rfl
  rw [← h1, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun y _ => sum_units _

private lemma unifE_succ (F : Cube (n+1) → ℝ) :
    unifE F
      = unifE (fun y : Cube n => (F (Fin.cons 1 y) + F (Fin.cons (-1) y)) / 2) := by
  unfold unifE
  rw [sum_cube_succ, ← Finset.sum_div, pow_succ]
  ring

private lemma unifE_sub (f g : Cube n → ℝ) :
    unifE (fun x => f x - g x) = unifE f - unifE g := by
  simp [unifE, Finset.sum_sub_distrib, sub_div]

private lemma flipCoord_zero_cons_one (y : Cube n) :
    flipCoord (0 : Fin (n+1)) (Fin.cons 1 y) = Fin.cons (-1) y := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [flipCoord_self, Fin.cons_zero, Fin.cons_zero]
  · intro i
    rw [flipCoord_ne (Fin.succ_ne_zero i), Fin.cons_succ, Fin.cons_succ]

private lemma flipCoord_succ_cons (i : Fin n) (u : ℤˣ) (y : Cube n) :
    flipCoord i.succ (Fin.cons u y) = Fin.cons u (flipCoord i y) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [flipCoord_ne (Ne.symm (Fin.succ_ne_zero i)), Fin.cons_zero, Fin.cons_zero]
  · intro k
    by_cases hk : k = i
    · subst hk
      rw [flipCoord_self, Fin.cons_succ, Fin.cons_succ, flipCoord_self]
    · rw [flipCoord_ne (fun hc => hk (Fin.succ_injective n hc)), Fin.cons_succ,
        Fin.cons_succ, flipCoord_ne hk]

private lemma pairEnt_flip (i : Fin n) (h : Cube n → ℝ) (x : Cube n) :
    pairEnt i h (flipCoord i x) = pairEnt i h x := by
  unfold pairEnt
  rw [flipCoord_flipCoord,
    show h (flipCoord i x) + h x = h x + h (flipCoord i x) from add_comm _ _]
  ring

private lemma pairEnt_succ_cons (i : Fin n) (u : ℤˣ) (h : Cube (n+1) → ℝ)
    (y : Cube n) :
    pairEnt i.succ h (Fin.cons u y) = pairEnt i (fun z => h (Fin.cons u z)) y := by
  unfold pairEnt
  rw [flipCoord_succ_cons]

private lemma unifE_pairEnt_zero (h : Cube (n+1) → ℝ) :
    unifE (fun x : Cube (n+1) => pairEnt 0 h x)
      = unifE (fun y : Cube n => pairEnt 0 h (Fin.cons 1 y)) := by
  rw [unifE_succ (fun x : Cube (n+1) => pairEnt 0 h x)]
  refine congrArg unifE (funext fun y => ?_)
  have hsym : pairEnt (0 : Fin (n+1)) h (Fin.cons (-1) y)
      = pairEnt 0 h (Fin.cons 1 y) := by
    have hf := pairEnt_flip (0 : Fin (n+1)) h (Fin.cons 1 y)
    rwa [flipCoord_zero_cons_one] at hf
  rw [hsym]
  ring

/-- Exact chain rule for the entropy on `Cube (n+1)` split along coordinate `0`. -/
private lemma entUnif_succ_chain (h : Cube (n+1) → ℝ) :
    entUnif h
      = unifE (fun y : Cube n => pairEnt 0 h (Fin.cons 1 y))
        + entUnif (fun y : Cube n =>
            (h (Fin.cons 1 y) + h (Fin.cons (-1) y)) / 2) := by
  have e1 : unifE (fun x : Cube (n+1) => h x * Real.log (h x))
      = unifE (fun y : Cube n =>
          (h (Fin.cons 1 y) * Real.log (h (Fin.cons 1 y))
            + h (Fin.cons (-1) y) * Real.log (h (Fin.cons (-1) y))) / 2) :=
    unifE_succ _
  have e2 : unifE h
      = unifE (fun y : Cube n =>
          (h (Fin.cons 1 y) + h (Fin.cons (-1) y)) / 2) := unifE_succ h
  have e3 : ∀ y : Cube n, pairEnt (0 : Fin (n+1)) h (Fin.cons 1 y)
      = (h (Fin.cons 1 y) * Real.log (h (Fin.cons 1 y))
          + h (Fin.cons (-1) y) * Real.log (h (Fin.cons (-1) y))) / 2
        - (h (Fin.cons 1 y) + h (Fin.cons (-1) y)) / 2
          * Real.log ((h (Fin.cons 1 y) + h (Fin.cons (-1) y)) / 2) := by
    intro y
    unfold pairEnt
    rw [flipCoord_zero_cons_one]
  have e4 : unifE (fun y : Cube n => pairEnt 0 h (Fin.cons 1 y))
      = unifE (fun y : Cube n =>
          (h (Fin.cons 1 y) * Real.log (h (Fin.cons 1 y))
            + h (Fin.cons (-1) y) * Real.log (h (Fin.cons (-1) y))) / 2)
        - unifE (fun y : Cube n =>
            (h (Fin.cons 1 y) + h (Fin.cons (-1) y)) / 2
              * Real.log ((h (Fin.cons 1 y) + h (Fin.cons (-1) y)) / 2)) := by
    rw [← unifE_sub]
    exact congrArg unifE (funext e3)
  simp only [entUnif]
  rw [e1, e2, e4]
  ring

private lemma entUnif_le_sum_pairEnt_aux : ∀ (n : ℕ) (h : Cube n → ℝ),
    (∀ x, 0 ≤ h x) → entUnif h ≤ ∑ i, unifE (fun x => pairEnt i h x) := by
  intro n
  induction n with
  | zero =>
    intro h _
    have hu : ∀ g : Cube 0 → ℝ, unifE g = g (fun _ => 1) := by
      intro g
      have hcongr : ∀ x : Cube 0, g x = g (fun _ => 1) :=
        fun x => congrArg g (Subsingleton.elim x _)
      unfold unifE
      rw [Finset.sum_congr rfl (fun x _ => hcongr x), Finset.sum_const,
        Finset.card_univ, Fintype.card_unique]
      norm_num
    simp only [entUnif, hu, Finset.univ_eq_empty, Finset.sum_empty]
    simp
  | succ n ih =>
    intro h hh
    have hHnn : ∀ y : Cube n,
        0 ≤ (h (Fin.cons 1 y) + h (Fin.cons (-1) y)) / 2 := by
      intro y
      have h1 := hh (Fin.cons 1 y)
      have h2 := hh (Fin.cons (-1) y)
      linarith
    have hIH := ih (fun y => (h (Fin.cons 1 y) + h (Fin.cons (-1) y)) / 2) hHnn
    have hstep : ∀ i : Fin n,
        unifE (fun y : Cube n => pairEnt i
            (fun z => (h (Fin.cons 1 z) + h (Fin.cons (-1) z)) / 2) y)
          ≤ unifE (fun x : Cube (n+1) => pairEnt i.succ h x) := by
      intro i
      rw [unifE_succ (fun x : Cube (n+1) => pairEnt i.succ h x)]
      refine unifE_mono fun y => ?_
      dsimp only
      rw [pairEnt_succ_cons, pairEnt_succ_cons]
      simp only [pairEnt_eq_ent2]
      exact ent2_avg_le (hh _) (hh _) (hh _) (hh _)
    have hzero : unifE (fun y : Cube n => pairEnt (0 : Fin (n+1)) h (Fin.cons 1 y))
        = unifE (fun x : Cube (n+1) => pairEnt 0 h x) :=
      (unifE_pairEnt_zero h).symm
    simp only [Fin.sum_univ_succ]
    rw [entUnif_succ_chain h]
    refine add_le_add (le_of_eq hzero) (hIH.trans ?_)
    exact Finset.sum_le_sum fun i _ => hstep i

/-- **Tensorization (subadditivity) of entropy over the cube**:
`Ent_λ(h) ≤ ∑_i 𝔼_λ[pairEnt i h]`. Standard chain-rule induction on `n` using
`ent_average_le`. -/
theorem entUnif_le_sum_pairEnt {h : Cube n → ℝ} (hh : ∀ x, 0 ≤ h x) :
    entUnif h ≤ ∑ i, unifE (fun x => pairEnt i h x) :=
  entUnif_le_sum_pairEnt_aux n h hh

end Talagrand
