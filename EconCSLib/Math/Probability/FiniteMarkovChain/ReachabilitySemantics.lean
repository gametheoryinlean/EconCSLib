/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteMarkovChain.Reachability
import EconCSLib.Math.Probability.FiniteMarkovChain.Semantics

/-!
# Semantics of exact finite-chain reachability

The executable reachability solver works for every finite rational chain,
including chains with closed nonterminal recurrent classes.  This leaf proves
that its internally generated pruned system is nonsingular, identifies the
computed vectors by their Bellman equations, validates the terminal plus
nontermination `FiniteLaw`, and proves the late-hit truncation identity.
-/

namespace FiniteMarkovChain.Chain

open Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.Operator

variable {n m : ℕ} (C : Chain n m)

/-! ## Certified pruned system -/

/-- The internally generated pruned chain passes the existing complete
finite-state absorption checker. -/
theorem reachableChain_autoCheck : C.reachableChain.autoCheck = true := by
  rw [C.reachableChain.autoCheck_iff_reaches]
  intro i
  cases hi : C.canReachTerminal i with
  | false =>
      refine ⟨1, ?_⟩
      simp [survival, C.reachableChain_Q,
        C.reachableQ_of_unreachable_source i hi]
  | true =>
      refine ⟨n, ?_⟩
      rw [C.canReachTerminal_eq_true_iff] at hi
      apply lt_of_le_of_lt _ hi
      simp only [survival, C.reachableChain_Q]
      exact Finset.sum_le_sum fun j _ =>
        C.reachableQ_pow_le_Q_pow n i j

/-- The pruned rational Bellman matrix is nonsingular for every input chain.
This is a theorem about the matrix computed from the chain, rather than a
certificate required from a caller. -/
theorem reachabilityMatrix_det_ne_zero :
    C.reachabilityMatrix.det ≠ 0 := by
  have hdet := C.reachableChain.det_ne_zero C.reachableChain_autoCheck
  simpa [reachabilityMatrix, C.reachableChain_Q] using hdet

/-- Cramer's executable vector satisfies its pruned Bellman system. -/
theorem solveReachable_system (b : Fin n → ℚ) :
    C.reachabilityMatrix *ᵥ C.solveReachable b = C.reachableRhs b := by
  unfold solveReachable
  rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
    inv_mul_cancel₀ C.reachabilityMatrix_det_ne_zero, one_smul]

/-- The pruned system has a unique solution. -/
theorem solveReachable_unique (b : Fin n → ℚ) {x : Fin n → ℚ}
    (hx : C.reachabilityMatrix *ᵥ x = C.reachableRhs b) :
    x = C.solveReachable b := by
  apply (Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det C.reachabilityMatrix).mpr
      (isUnit_iff_ne_zero.mpr C.reachabilityMatrix_det_ne_zero)))
  exact hx.trans (C.solveReachable_system b).symm

/-- Cramer's solution in fixed-point form. -/
theorem solveReachable_pruned_bellman (b : Fin n → ℚ) :
    C.solveReachable b = C.reachableRhs b +
      C.reachableQ *ᵥ C.solveReachable b := by
  have hs := C.solveReachable_system b
  rw [reachabilityMatrix, Matrix.sub_mulVec, Matrix.one_mulVec] at hs
  funext i
  have hi := congrFun hs i
  simp only [Pi.sub_apply, Pi.add_apply] at hi ⊢
  linarith

/-- A solution has value zero at every state outside the reachable class. -/
theorem solveReachable_eq_zero_of_unreachable (b : Fin n → ℚ)
    (i : Fin n) (hi : C.canReachTerminal i = false) :
    C.solveReachable b i = 0 := by
  have h := congrFun (C.solveReachable_pruned_bellman b) i
  simp [reachableRhs, hi, Matrix.mulVec, dotProduct] at h
  exact h

/-- An unreachable state has no positive original terminal edge. -/
theorem R_eq_zero_of_unreachable (i : Fin n)
    (hi : C.canReachTerminal i = false) (terminal : Fin m) :
    C.R i terminal = 0 := by
  have hnot : ¬ C.survival 1 i < 1 := by
    intro h
    have : C.canReachTerminal i = true :=
      (C.canReachTerminal_iff_eventually i).2 ⟨1, h⟩
    simp [hi] at this
  have hnpos : ¬ 0 < C.R i terminal := by
    intro hpositive
    exact hnot ((C.survival_succ_lt_one_iff 0 i).2
      (Or.inl ⟨terminal, hpositive⟩))
  exact le_antisymm (le_of_not_gt hnpos) (C.R_nonneg i terminal)

/-- A positive edge into the reachable class would itself make the source
reachable.  Hence such an edge is zero from an unreachable source. -/
theorem Q_eq_zero_of_unreachable_to_reachable (i j : Fin n)
    (hi : C.canReachTerminal i = false)
    (hj : C.canReachTerminal j = true) :
    C.Q i j = 0 := by
  rw [C.canReachTerminal_iff_eventually] at hj
  obtain ⟨horizon, hj⟩ := hj
  have hnpos : ¬ 0 < C.Q i j := by
    intro hpositive
    have hsource : C.survival (horizon + 1) i < 1 :=
      (C.survival_succ_lt_one_iff horizon i).2
        (Or.inr ⟨j, hpositive, hj⟩)
    have : C.canReachTerminal i = true :=
      (C.canReachTerminal_iff_eventually i).2
        ⟨horizon + 1, hsource⟩
    simp [hi] at this
  exact le_antisymm (le_of_not_gt hnpos) (C.Q_nonneg i j)

private theorem reachableRhs_eq_of_zero (b : Fin n → ℚ)
    (hb : ∀ i, C.canReachTerminal i = false → b i = 0) :
    C.reachableRhs b = b := by
  funext i
  cases hi : C.canReachTerminal i with
  | false => simp [reachableRhs, hi, hb i hi]
  | true => simp [reachableRhs, hi]

private theorem reachableQ_mulVec_eq_Q_mulVec (x : Fin n → ℚ)
    (hx : ∀ i, C.canReachTerminal i = false → x i = 0) :
    C.reachableQ *ᵥ x = C.Q *ᵥ x := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  cases hi : C.canReachTerminal i with
  | false =>
      cases hj : C.canReachTerminal j with
      | false => simp [C.reachableQ_of_unreachable_source i hi, hx j hj]
      | true =>
          simp [C.reachableQ_of_unreachable_source i hi,
            C.Q_eq_zero_of_unreachable_to_reachable i j hi hj]
  | true =>
      cases hj : C.canReachTerminal j with
      | false => simp [reachableQ, reachableTransient, hi, hj, hx j hj]
      | true => simp [C.reachableQ_of_reachable i j hi hj]

/-- If a Bellman right-hand side is zero outside the reachable class, the
pruned result satisfies the original chain's Bellman equation. -/
theorem solveReachable_bellman (b : Fin n → ℚ)
    (hb : ∀ i, C.canReachTerminal i = false → b i = 0) :
    C.solveReachable b = b + C.Q *ᵥ C.solveReachable b := by
  calc
    C.solveReachable b = C.reachableRhs b +
        C.reachableQ *ᵥ C.solveReachable b :=
      C.solveReachable_pruned_bellman b
    _ = b + C.Q *ᵥ C.solveReachable b := congrArg₂ (.+.)
      (C.reachableRhs_eq_of_zero b hb)
      (C.reachableQ_mulVec_eq_Q_mulVec (C.solveReachable b)
        (C.solveReachable_eq_zero_of_unreachable b))

private theorem totalRhs_zero_of_unreachable (i : Fin n)
    (hi : C.canReachTerminal i = false) :
    (C.R *ᵥ (fun _ => 1)) i = 0 := by
  simp [Matrix.mulVec, dotProduct, C.R_eq_zero_of_unreachable i hi]

/-- Eventual reach probability satisfies the original, unpruned Bellman
equation and is zero on states with no positive terminal route. -/
theorem reachProbability_bellman :
    C.reachProbability = (C.R *ᵥ fun _ => 1) +
      C.Q *ᵥ C.reachProbability := by
  exact C.solveReachable_bellman _ C.totalRhs_zero_of_unreachable

/-- Each specified terminal probability satisfies its original Bellman
equation. -/
theorem terminalProbability_bellman (terminal : Fin m) :
    C.terminalProbability terminal = (fun i => C.R i terminal) +
      C.Q *ᵥ C.terminalProbability terminal := by
  exact C.solveReachable_bellman _
    (fun i hi => C.R_eq_zero_of_unreachable i hi terminal)

/-- The zero-on-nonhit reward satisfies its original Bellman equation. -/
theorem zeroOnNonhitReward_bellman :
    C.zeroOnNonhitReward = C.R *ᵥ C.reward +
      C.Q *ᵥ C.zeroOnNonhitReward := by
  apply C.solveReachable_bellman
  intro i hi
  simp [Matrix.mulVec, dotProduct, C.R_eq_zero_of_unreachable i hi]

local notation "Pr" => C.reachableQ.map (Rat.castHom ℝ)

/-! ## Nonnegative solutions and normalized outcome law -/

private theorem summable_reachable_powers :
    Summable (fun horizon : ℕ => Pr ^ horizon) := by
  simpa [C.reachableChain_Q] using
    C.reachableChain.summable_powers C.reachableChain_autoCheck

private theorem reachable_series_solution (b x : Fin n → ℚ)
    (hx : C.reachabilityMatrix *ᵥ x = C.reachableRhs b) :
    (∑' horizon : ℕ, Pr ^ horizon) *ᵥ
        (fun i => (C.reachableRhs b i : ℝ)) =
      fun i => (x i : ℝ) := by
  have hr : (1 - Pr) *ᵥ (fun i => (x i : ℝ)) =
      fun i => (C.reachableRhs b i : ℝ) := by
    have heq : C.reachabilityMatrix.map (Rat.castHom ℝ) = 1 - Pr := by
      simp [reachabilityMatrix, Matrix.map_sub]
    rw [← heq]
    funext i
    change (C.reachabilityMatrix.map (Rat.castHom ℝ) *ᵥ
      ((Rat.castHom ℝ) ∘ x)) i = _
    rw [← RingHom.map_mulVec, hx]
    rfl
  rw [← hr, Matrix.mulVec_mulVec,
    C.summable_reachable_powers.tsum_pow_mul_one_sub,
    Matrix.one_mulVec]

private theorem reachable_series_entry_nonneg (i j : Fin n) :
    0 ≤ (∑' horizon : ℕ, Pr ^ horizon) i j := by
  have hs := Pi.hasSum.mp
    (Pi.hasSum.mp C.summable_reachable_powers.hasSum i) j
  rw [← hs.tsum_eq]
  apply tsum_nonneg
  intro horizon
  rw [← Matrix.map_pow]
  change 0 ≤ ((C.reachableQ ^ horizon) i j : ℝ)
  exact_mod_cast Matrix.pow_apply_nonneg C.reachableQ_nonneg horizon i j

/-- The inverse of the generated pruned system is positive on every
nonnegative rational right-hand side. -/
theorem solveReachable_nonneg (b : Fin n → ℚ)
    (hb : ∀ i, 0 ≤ b i) (i : Fin n) :
    0 ≤ C.solveReachable b i := by
  have hseries := C.reachable_series_solution b (C.solveReachable b)
    (C.solveReachable_system b)
  have hrhs (j : Fin n) : 0 ≤ C.reachableRhs b j := by
    simp only [reachableRhs]
    split <;> simp [hb]
  have hnonneg :
      0 ≤ ((∑' horizon : ℕ, Pr ^ horizon) *ᵥ
        (fun j => (C.reachableRhs b j : ℝ))) i := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (C.reachable_series_entry_nonneg i j)
      (by exact_mod_cast hrhs j)
  rw [hseries] at hnonneg
  change 0 ≤ (C.solveReachable b i : ℝ) at hnonneg
  exact_mod_cast hnonneg

/-- Every computed terminal probability is nonnegative. -/
theorem terminalProbability_nonneg (terminal : Fin m) (i : Fin n) :
    0 ≤ C.terminalProbability terminal i := by
  apply C.solveReachable_nonneg
  exact fun j => C.R_nonneg j terminal

/-- The computed eventual-hit probability is nonnegative. -/
theorem reachProbability_nonneg (i : Fin n) :
    0 ≤ C.reachProbability i := by
  apply C.solveReachable_nonneg
  intro j
  simpa [Matrix.mulVec, dotProduct] using
    (Finset.sum_nonneg fun terminal (_ : terminal ∈ Finset.univ) =>
      C.R_nonneg j terminal)

private theorem sum_terminalProbability_system :
    C.reachabilityMatrix *ᵥ
        (fun i => ∑ terminal, C.terminalProbability terminal i) =
      C.reachableRhs (C.R *ᵥ fun _ => 1) := by
  funext i
  change (∑ j, C.reachabilityMatrix i j *
      ∑ terminal, C.terminalProbability terminal j) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterminal : ∀ terminal : Fin m,
      (∑ j, C.reachabilityMatrix i j *
        C.terminalProbability terminal j) =
        C.reachableRhs (fun j => C.R j terminal) i := by
    intro terminal
    exact congrFun (C.solveReachable_system
      (fun j => C.R j terminal)) i
  calc
    (∑ terminal, ∑ j, C.reachabilityMatrix i j *
        C.terminalProbability terminal j) =
        ∑ terminal, C.reachableRhs (fun j => C.R j terminal) i :=
      Finset.sum_congr rfl fun terminal _ => hterminal terminal
    _ = C.reachableRhs (C.R *ᵥ fun _ => 1) i := by
      cases hi : C.canReachTerminal i with
      | false => simp [reachableRhs, hi]
      | true => simp [reachableRhs, hi, Matrix.mulVec, dotProduct]

/-- The probability of reaching any terminal is the sum of the disjoint
specified-terminal probabilities. -/
theorem sum_terminalProbability :
    (fun i => ∑ terminal, C.terminalProbability terminal i) =
      C.reachProbability := by
  exact C.solveReachable_unique _ C.sum_terminalProbability_system

private theorem totalRhs_add_reachableRow_le_one (i : Fin n) :
    C.reachableRhs (C.R *ᵥ fun _ => 1) i +
        (C.reachableQ *ᵥ fun _ => 1) i ≤ 1 := by
  cases hi : C.canReachTerminal i with
  | false => simp [reachableRhs, hi, Matrix.mulVec, dotProduct]
  | true =>
      simp only [reachableRhs, hi, if_true, Matrix.mulVec, dotProduct, mul_one]
      calc
        (∑ a, C.R i a) + ∑ j, C.reachableQ i j ≤
            (∑ a, C.R i a) + ∑ j, C.Q i j := by
          gcongr with j
          exact C.reachableQ_le_Q i j
        _ = 1 := by rw [add_comm, C.row_sum i]

private lemma reachableQ_mulVec_complement (value : Fin n → ℚ) (j : Fin n) :
    let complement : Fin n → ℚ := fun x =>
      if C.canReachTerminal x then 1 - value x else 0
    (C.reachableQ *ᵥ complement) j =
      (C.reachableQ *ᵥ fun _ => 1) j - (C.reachableQ *ᵥ value) j := by
  dsimp only
  let complement : Fin n → ℚ := fun x =>
    if C.canReachTerminal x then 1 - value x else 0
  change (C.reachableQ *ᵥ complement) j =
    (C.reachableQ *ᵥ fun _ => 1) j - (C.reachableQ *ᵥ value) j
  simp only [Matrix.mulVec, dotProduct, mul_one]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases hx : C.canReachTerminal x with
  | false =>
      have hcx : complement x = 0 := by
        simp only [complement, hx, Bool.false_eq_true, if_false]
      have hqx : C.reachableQ j x = 0 := by
        simp [reachableQ, reachableTransient, hx]
      rw [hcx, hqx]
      ring
  | true =>
      have hcx : complement x = 1 - value x := by
        simp only [complement, hx, if_true]
      rw [hcx]
      ring

private lemma reachProbability_complement_system :
    let gap : Fin n → ℚ := fun j =>
      1 - (C.reachableRhs (C.R *ᵥ fun _ => 1) j +
        (C.reachableQ *ᵥ fun _ => 1) j)
    let complement : Fin n → ℚ := fun j =>
      if C.canReachTerminal j then 1 - C.reachProbability j else 0
    C.reachabilityMatrix *ᵥ complement = C.reachableRhs gap := by
  dsimp only
  let gap : Fin n → ℚ := fun j =>
    1 - (C.reachableRhs (C.R *ᵥ fun _ => 1) j +
      (C.reachableQ *ᵥ fun _ => 1) j)
  let complement : Fin n → ℚ := fun j =>
    if C.canReachTerminal j then 1 - C.reachProbability j else 0
  change C.reachabilityMatrix *ᵥ complement = C.reachableRhs gap
  funext j
  simp only [reachabilityMatrix, Matrix.sub_mulVec,
    Matrix.one_mulVec, Pi.sub_apply]
  have hp := congrFun (C.solveReachable_pruned_bellman
    (C.R *ᵥ fun _ => 1)) j
  cases hj : C.canReachTerminal j with
  | false =>
      have hc : complement j = 0 := by simp only [complement, hj, Bool.false_eq_true, if_false]
      have hq : (C.reachableQ *ᵥ complement) j = 0 := by
        simp [Matrix.mulVec, dotProduct,
          C.reachableQ_of_unreachable_source j hj]
      have hr : C.reachableRhs gap j = 0 := by simp [reachableRhs, hj]
      rw [hc, hq, hr]
      ring
  | true =>
      have hc : complement j = 1 - C.reachProbability j := by
        simp only [complement, hj, if_true]
      have hr : C.reachableRhs gap j = gap j := by
        simp [reachableRhs, hj]
      have hrow := C.reachableQ_mulVec_complement C.reachProbability j
      have hp' : C.reachProbability j =
          C.reachableRhs (C.R *ᵥ fun _ => 1) j +
            (C.reachableQ *ᵥ C.reachProbability) j := hp
      have hterminalRhs : C.reachableRhs (C.R *ᵥ fun _ => 1) j =
          (C.R *ᵥ fun _ => 1) j := by simp [reachableRhs, hj]
      rw [hterminalRhs] at hp'
      rw [hc, hrow, hr]
      dsimp only [gap] at ⊢
      linarith

/-- Eventual terminal reachability has probability at most one. -/
theorem reachProbability_le_one (i : Fin n) : C.reachProbability i ≤ 1 := by
  let gap : Fin n → ℚ := fun j =>
    1 - (C.reachableRhs (C.R *ᵥ fun _ => 1) j +
      (C.reachableQ *ᵥ fun _ => 1) j)
  have hgap (j : Fin n) : 0 ≤ gap j := by
    dsimp [gap]
    linarith [C.totalRhs_add_reachableRow_le_one j]
  let complement : Fin n → ℚ := fun j =>
    if C.canReachTerminal j then 1 - C.reachProbability j else 0
  have hsystem : C.reachabilityMatrix *ᵥ complement = C.reachableRhs gap :=
    C.reachProbability_complement_system
  have hcomp : complement = C.solveReachable gap :=
    C.solveReachable_unique gap hsystem
  cases hi : C.canReachTerminal i with
  | false =>
      rw [reachProbability, C.solveReachable_eq_zero_of_unreachable _ i hi]
      norm_num
  | true =>
      have hnonneg := C.solveReachable_nonneg gap hgap i
      rw [← hcomp] at hnonneg
      have hc : complement i = 1 - C.reachProbability i := by
        simp only [complement, hi, if_true]
      rw [hc] at hnonneg
      linarith

/-- The residual mass assigned to nontermination is nonnegative. -/
theorem nonterminationProbability_nonneg (i : Fin n) :
    0 ≤ C.nonterminationProbability i := by
  unfold nonterminationProbability
  linarith [C.reachProbability_le_one i]

/-- The outcome-vector checker always succeeds. -/
theorem outcomeWeightsValid_eq_true (i : Fin n) :
    C.outcomeWeightsValid i = true := by
  rw [outcomeWeightsValid]
  simp only [decide_eq_true_eq]
  refine ⟨(fun terminal => C.terminalProbability_nonneg terminal i),
    C.nonterminationProbability_nonneg i, ?_⟩
  rw [show (∑ terminal, C.terminalProbability terminal i) =
      C.reachProbability i by
    exact congrFun C.sum_terminalProbability i]
  simp [nonterminationProbability]

/-- The checked terminal/nontermination law is produced for every start. -/
theorem outcomeLaw?_isSome (i : Fin n) : C.outcomeLaw? i ≠ none := by
  rw [C.outcomeLaw?_eq_some_iff]
  exact C.outcomeWeightsValid_eq_true i

/-- The total API is exactly the successful checked construction. -/
theorem outcomeLaw?_eq_some_outcomeLaw (i : Fin n) :
    C.outcomeLaw? i = some (C.outcomeLaw i) := by
  unfold outcomeLaw
  cases h : C.outcomeLaw? i with
  | none => exact (C.outcomeLaw?_isSome i h).elim
  | some law => simp

private lemma outcomeWeights_valid (i : Fin n) :
    (∀ terminal, 0 ≤ C.terminalProbability terminal i) ∧
      0 ≤ C.nonterminationProbability i ∧
      (∑ terminal, C.terminalProbability terminal i) +
        C.nonterminationProbability i = 1 := by
  simpa [outcomeWeightsValid] using C.outcomeWeightsValid_eq_true i

/-- Point mass of an original terminal in the returned executable law. -/
theorem outcomeLaw_mass_some (i : Fin n) (terminal : Fin m) :
    ((C.outcomeLaw i).mass (some terminal) : ℚ) =
      C.terminalProbability terminal i := by
  have hv := C.outcomeWeights_valid i
  simp [outcomeLaw, outcomeLaw?, hv, FiniteLaw.mass,
    FiniteLaw.eventMass]
  rw [List.sum_ofFn]
  simp
  rw [Rat.coe_toNNRat _ (C.terminalProbability_nonneg terminal i)]

/-- The `none` atom has exactly the nontermination probability. -/
theorem outcomeLaw_mass_none (i : Fin n) :
    ((C.outcomeLaw i).mass none : ℚ) =
      C.nonterminationProbability i := by
  have hv := C.outcomeWeights_valid i
  simp [outcomeLaw, outcomeLaw?, hv, FiniteLaw.mass,
    FiniteLaw.eventMass]
  rw [List.sum_ofFn]
  simp
  rw [Rat.coe_toNNRat _ (C.nonterminationProbability_nonneg i)]

private theorem reachableQ_mulVec_zero_of_unreachable (x : Fin n → ℚ)
    (i : Fin n) (hi : C.canReachTerminal i = false) :
    (C.reachableQ *ᵥ x) i = 0 := by
  simp [Matrix.mulVec, dotProduct,
    C.reachableQ_of_unreachable_source i hi]

private theorem reachableQ_pow_mulVec_zero_of_unreachable
    (x : Fin n → ℚ)
    (hx : ∀ i, C.canReachTerminal i = false → x i = 0)
    (horizon : ℕ) (i : Fin n) (hi : C.canReachTerminal i = false) :
    (C.reachableQ ^ horizon *ᵥ x) i = 0 := by
  cases horizon with
  | zero => simpa using hx i hi
  | succ horizon =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact C.reachableQ_mulVec_zero_of_unreachable _ i hi

private theorem Q_pow_mulVec_eq_reachableQ_pow_mulVec
    (x : Fin n → ℚ)
    (hx : ∀ i, C.canReachTerminal i = false → x i = 0)
    (horizon : ℕ) :
    C.Q ^ horizon *ᵥ x = C.reachableQ ^ horizon *ᵥ x := by
  induction horizon with
  | zero => rfl
  | succ horizon ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      rw [← C.reachableQ_mulVec_eq_Q_mulVec
        (C.reachableQ ^ horizon *ᵥ x)
        (C.reachableQ_pow_mulVec_zero_of_unreachable x hx horizon)]
      rw [Matrix.mulVec_mulVec, ← pow_succ']

/-- Late-hit mass is nonnegative even when the chain has a positive
nontermination probability. -/
theorem lateHitMass_nonneg (horizon : ℕ) (i : Fin n) :
    0 ≤ C.lateHitMass horizon i := by
  simp only [lateHitMass, Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (C.pow_nonneg horizon i j)
      (C.reachProbability_nonneg j)

/-- The late-hit remainder tends to zero.  Survival itself need not tend to
zero: mass trapped in closed nonterminal classes is excluded by the eventual
reach-probability vector. -/
theorem tendsto_lateHitMass_zero (i : Fin n) :
    Filter.Tendsto (fun horizon => (C.lateHitMass horizon i : ℝ))
      Filter.atTop (nhds 0) := by
  have hmatrix : Filter.Tendsto (fun horizon : ℕ => Pr ^ horizon)
      Filter.atTop (nhds 0) :=
    C.summable_reachable_powers.tendsto_atTop_zero
  have hentry (j : Fin n) :
      Filter.Tendsto (fun horizon : ℕ => (Pr ^ horizon) i j)
        Filter.atTop (nhds 0) :=
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hmatrix i) j)
  have hsum : Filter.Tendsto
      (fun horizon : ℕ => ∑ j, (Pr ^ horizon) i j *
        (C.reachProbability j : ℝ)) Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_finsetSum Finset.univ fun j _ =>
        (hentry j).mul_const (C.reachProbability j : ℝ))
  have heq (horizon : ℕ) :
      (C.lateHitMass horizon i : ℝ) =
        ∑ j, (Pr ^ horizon) i j * (C.reachProbability j : ℝ) := by
    rw [lateHitMass,
      C.Q_pow_mulVec_eq_reachableQ_pow_mulVec C.reachProbability
        (C.solveReachable_eq_zero_of_unreachable
          (C.R *ᵥ fun _ => 1)) horizon]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Matrix.map_pow]
    change (Rat.castHom ℝ) (∑ x, (C.reachableQ ^ horizon) i x *
      C.reachProbability x) =
      ∑ j, (Rat.castHom ℝ) ((C.reachableQ ^ horizon) i j) *
        (Rat.castHom ℝ) (C.reachProbability j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact map_mul (Rat.castHom ℝ) _ _
  simpa only [heq] using hsum

/-! ## First-hit series and tail limits -/

/-- Exact finite-horizon decomposition of eventual reachability. -/
theorem reachProbability_eq_hits_add_late (horizon : ℕ) (i : Fin n) :
    C.reachProbability i =
      (∑ r ∈ Finset.range horizon, ∑ terminal, C.hit r i terminal) +
        C.lateHitMass horizon i := by
  have hunroll := congrFun
    (C.bellman_unroll (C.R *ᵥ fun _ => 1) C.reachProbability
      C.reachProbability_bellman horizon) i
  simpa [lateHitMass, hit, Matrix.mulVec, dotProduct,
    Matrix.mulVec_mulVec, Matrix.mul_apply] using hunroll

private theorem survival_add_firstHits (horizon : ℕ) (i : Fin n) :
    C.survival horizon i +
      (∑ r ∈ Finset.range horizon, ∑ terminal, C.hit r i terminal) = 1 := by
  have hrun := C.run_expect horizon i (fun _ => 1) (fun _ _ => 1)
  have hconstant : Sum.elim (fun _ : Fin n => (1 : ℚ))
      (fun _ : ℕ × Fin m => 1) = fun _ => 1 := by
    funext result
    cases result <;> rfl
  rw [hconstant, FiniteLaw.expectRat_const] at hrun
  simpa [survival, Matrix.mulVec, dotProduct] using hrun.symm

/-- The Boolean reachability classifier is exact for the computed eventual
probability. -/
theorem canReachTerminal_iff_reachProbability_pos (i : Fin n) :
    C.canReachTerminal i = true ↔ 0 < C.reachProbability i := by
  constructor
  · intro hi
    have hsurvival := (C.canReachTerminal_eq_true_iff i).1 hi
    have hdecomp := C.reachProbability_eq_hits_add_late n i
    have hmass := C.survival_add_firstHits n i
    have hlate := C.lateHitMass_nonneg n i
    linarith
  · intro hpositive
    cases hi : C.canReachTerminal i with
    | false =>
        rw [reachProbability,
          C.solveReachable_eq_zero_of_unreachable _ i hi] at hpositive
        exact (lt_irrefl 0 hpositive).elim
    | true => rfl

/-- Exact finite-horizon decomposition for one specified terminal. -/
theorem terminalProbability_eq_hits_add_late (terminal : Fin m)
    (horizon : ℕ) (i : Fin n) :
    C.terminalProbability terminal i =
      (∑ r ∈ Finset.range horizon, C.hit r i terminal) +
        (C.Q ^ horizon *ᵥ C.terminalProbability terminal) i := by
  have hunroll := congrFun
    (C.bellman_unroll (fun j => C.R j terminal)
      (C.terminalProbability terminal)
      (C.terminalProbability_bellman terminal) horizon) i
  simpa [hit, Matrix.mulVec, dotProduct, Matrix.mul_apply] using hunroll

/-- A specified terminal's eventual probability is bounded by the probability
of reaching some terminal. -/
theorem terminalProbability_le_reachProbability (terminal : Fin m) (i : Fin n) :
    C.terminalProbability terminal i ≤ C.reachProbability i := by
  rw [← show (∑ a, C.terminalProbability a i) = C.reachProbability i by
    exact congrFun C.sum_terminalProbability i]
  exact Finset.single_le_sum
    (fun a _ => C.terminalProbability_nonneg a i) (Finset.mem_univ terminal)

/-- The specified-terminal remainder also tends to zero. -/
theorem tendsto_terminalProbability_late_zero (terminal : Fin m) (i : Fin n) :
    Filter.Tendsto
      (fun horizon => ((C.Q ^ horizon *ᵥ
        C.terminalProbability terminal) i : ℝ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro horizon
    exact_mod_cast Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
      mul_nonneg (C.pow_nonneg horizon i j)
        (C.terminalProbability_nonneg terminal j)
  · intro horizon
    change ((C.Q ^ horizon *ᵥ C.terminalProbability terminal) i : ℝ) ≤
      (C.lateHitMass horizon i : ℝ)
    exact_mod_cast Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left
        (C.terminalProbability_le_reachProbability terminal j)
        (C.pow_nonneg horizon i j)
  · exact C.tendsto_lateHitMass_zero i

/-- Each computed terminal probability is exactly the sum of its infinite
first-hit series. -/
theorem hasSum_terminalHit_general (terminal : Fin m) (i : Fin n) :
    HasSum (fun horizon => (C.hit horizon i terminal : ℝ))
      (C.terminalProbability terminal i : ℝ) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun horizon => by exact_mod_cast C.hit_nonneg horizon i terminal)]
  have hlate := C.tendsto_terminalProbability_late_zero terminal i
  have hsub : Filter.Tendsto
      (fun horizon => (C.terminalProbability terminal i : ℝ) -
        ((C.Q ^ horizon *ᵥ C.terminalProbability terminal) i : ℝ))
      Filter.atTop (nhds (C.terminalProbability terminal i : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hlate)
  apply hsub.congr'
  filter_upwards [] with horizon
  have hdecomp := C.terminalProbability_eq_hits_add_late terminal horizon i
  exact_mod_cast (by linarith [hdecomp])

/-- The all-terminal first-hit series sums to `reachProbability`; the missing
mass is exactly `nonterminationProbability`. -/
theorem hasSum_firstHit_general (i : Fin n) :
    HasSum (fun horizon => ∑ terminal, (C.hit horizon i terminal : ℝ))
      (C.reachProbability i : ℝ) := by
  have hs : HasSum (fun horizon =>
      ∑ terminal, (C.hit horizon i terminal : ℝ))
      (∑ terminal, (C.terminalProbability terminal i : ℝ)) :=
    hasSum_sum (s := Finset.univ) fun terminal _ =>
      C.hasSum_terminalHit_general terminal i
  convert hs using 1
  rw [← Rat.cast_sum]
  congr 1
  exact (congrFun C.sum_terminalProbability i).symm

/-! ## Terminal rewards and remainder bounds -/

/-- The zero-on-nonhit reward is the terminal reward averaged with the exact
eventual terminal probabilities.  Closed nonterminal classes contribute zero. -/
theorem zeroOnNonhitReward_eq_terminalProbability (i : Fin n) :
    C.zeroOnNonhitReward i =
      ∑ terminal, C.terminalProbability terminal i * C.reward terminal := by
  let value : Fin n → ℚ := fun j =>
    ∑ terminal, C.terminalProbability terminal j * C.reward terminal
  have hsystem : C.reachabilityMatrix *ᵥ value =
      C.reachableRhs (C.R *ᵥ C.reward) := by
    funext j
    change (∑ state, C.reachabilityMatrix j state *
      ∑ terminal, C.terminalProbability terminal state * C.reward terminal) = _
    rw [show (∑ state, C.reachabilityMatrix j state *
        ∑ terminal, C.terminalProbability terminal state * C.reward terminal) =
        ∑ state, ∑ terminal, C.reachabilityMatrix j state *
          (C.terminalProbability terminal state * C.reward terminal) by
      apply Finset.sum_congr rfl
      intro state _
      rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
    have hterminal : ∀ terminal : Fin m,
        (∑ state, C.reachabilityMatrix j state *
          C.terminalProbability terminal state) =
          C.reachableRhs (fun state => C.R state terminal) j := by
      intro terminal
      exact congrFun (C.solveReachable_system
        (fun state => C.R state terminal)) j
    calc
      (∑ terminal, ∑ state, C.reachabilityMatrix j state *
          (C.terminalProbability terminal state * C.reward terminal)) =
          ∑ terminal, C.reachableRhs (fun state => C.R state terminal) j *
            C.reward terminal := by
        apply Finset.sum_congr rfl
        intro terminal _
        calc
          (∑ state, C.reachabilityMatrix j state *
              (C.terminalProbability terminal state * C.reward terminal)) =
              ∑ state, (C.reachabilityMatrix j state *
                C.terminalProbability terminal state) * C.reward terminal := by
            apply Finset.sum_congr rfl
            intro state _
            ring
          _ =
              (∑ state, C.reachabilityMatrix j state *
                C.terminalProbability terminal state) * C.reward terminal := by
            rw [Finset.sum_mul]
          _ = C.reachableRhs (fun state => C.R state terminal) j *
                C.reward terminal := by rw [hterminal terminal]
      _ = C.reachableRhs (C.R *ᵥ C.reward) j := by
        cases hj : C.canReachTerminal j with
        | false => simp [reachableRhs, hj]
        | true => simp [reachableRhs, hj, Matrix.mulVec, dotProduct]
  have hvalue : value = C.zeroOnNonhitReward :=
    C.solveReachable_unique _ hsystem
  exact congrFun hvalue.symm i

/-- Exact truncation identity for zero-on-nonhit terminal reward. -/
theorem zeroOnNonhitReward_eq_hits_add_remainder (horizon : ℕ) (i : Fin n) :
    C.zeroOnNonhitReward i =
      (∑ r ∈ Finset.range horizon,
        ∑ terminal, C.hit r i terminal * C.reward terminal) +
      (C.Q ^ horizon *ᵥ C.zeroOnNonhitReward) i := by
  have hunroll := congrFun
    (C.bellman_unroll (C.R *ᵥ C.reward) C.zeroOnNonhitReward
      C.zeroOnNonhitReward_bellman horizon) i
  simpa [hit, Matrix.mulVec, dotProduct, Matrix.mulVec_mulVec,
    Matrix.mul_apply] using hunroll

/-- A uniform terminal-reward bound controls the zero-on-nonhit value by the
eventual probability of reaching a terminal. -/
theorem abs_zeroOnNonhitReward_le (bound : ℚ)
    (hbound : ∀ terminal, |C.reward terminal| ≤ bound) (i : Fin n) :
    |C.zeroOnNonhitReward i| ≤ bound * C.reachProbability i := by
  rw [C.zeroOnNonhitReward_eq_terminalProbability]
  calc
    |∑ terminal, C.terminalProbability terminal i * C.reward terminal| ≤
        ∑ terminal, |C.terminalProbability terminal i * C.reward terminal| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ terminal, C.terminalProbability terminal i * |C.reward terminal| := by
      apply Finset.sum_congr rfl
      intro terminal _
      rw [abs_mul, abs_of_nonneg (C.terminalProbability_nonneg terminal i)]
    _ ≤ ∑ terminal, C.terminalProbability terminal i * bound := by
      apply Finset.sum_le_sum
      intro terminal _
      exact mul_le_mul_of_nonneg_left (hbound terminal)
        (C.terminalProbability_nonneg terminal i)
    _ = bound * (∑ terminal, C.terminalProbability terminal i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro terminal _
      ring
    _ = bound * C.reachProbability i := by
      rw [show (∑ terminal, C.terminalProbability terminal i) =
        C.reachProbability i by exact congrFun C.sum_terminalProbability i]

/-- Certified A13 truncation bound.  It remains valid when nontermination has
positive probability, because `lateHitMass` excludes executions that will
never hit a terminal. -/
theorem abs_zeroOnNonhitReward_remainder_le (bound : ℚ)
    (hbound : ∀ terminal, |C.reward terminal| ≤ bound)
    (horizon : ℕ) (i : Fin n) :
    |(C.Q ^ horizon *ᵥ C.zeroOnNonhitReward) i| ≤
      bound * C.lateHitMass horizon i := by
  simp only [Matrix.mulVec, dotProduct]
  calc
    |∑ j, (C.Q ^ horizon) i j * C.zeroOnNonhitReward j| ≤
        ∑ j, |(C.Q ^ horizon) i j * C.zeroOnNonhitReward j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, (C.Q ^ horizon) i j * |C.zeroOnNonhitReward j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (C.pow_nonneg horizon i j)]
    _ ≤ ∑ j, (C.Q ^ horizon) i j *
        (bound * C.reachProbability j) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (C.abs_zeroOnNonhitReward_le bound hbound j)
        (C.pow_nonneg horizon i j)
    _ = bound * (∑ j, (C.Q ^ horizon) i j * C.reachProbability j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = bound * C.lateHitMass horizon i := by
      rfl

end FiniteMarkovChain.Chain
