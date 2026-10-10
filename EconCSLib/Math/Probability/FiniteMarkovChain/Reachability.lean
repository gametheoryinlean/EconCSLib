/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteMarkovChain

/-!
# Exact reachability for finite rational Markov chains

This executable leaf removes the global-absorption restriction of
`FiniteMarkovChain.Chain.autoSolve`.  It first classifies the transient states
from which a terminal state is reachable through positive-probability edges.
The classification is finite: a witness, when one exists, has length at most
the number of transient states.

States outside that class are assigned boundary value zero.  On the remaining
states, Cramer's rule solves a pruned rational Bellman system.  Consequently a
closed nonterminal recurrent class is represented explicitly by
`nonterminationProbability`, rather than being rejected by an absorption
precondition.

The module contains only finite rational computation.  Its analytic
identification with eventual hitting probabilities is in
`FiniteMarkovChain.ReachabilitySemantics`.
-/

namespace FiniteMarkovChain.Chain

open Matrix
open scoped BigOperators

variable {n m : ℕ} (C : Chain n m)

/-! ## Reachable transient subsystem -/

/-- Whether a terminal state is reachable with positive probability.

The test is finite: `finite_horizon_complete` proves that inspecting the
`n`-step survival probability is complete. -/
def canReachTerminal (i : Fin n) : Bool :=
  decide (C.survival n i < 1)

@[simp]
theorem canReachTerminal_eq_true_iff (i : Fin n) :
    C.canReachTerminal i = true ↔ C.survival n i < 1 := by
  simp [canReachTerminal]

@[simp]
theorem canReachTerminal_eq_false_iff (i : Fin n) :
    C.canReachTerminal i = false ↔ 1 ≤ C.survival n i := by
  simp [canReachTerminal, not_lt]

/-- The finite test agrees with positive-probability terminal reachability at
some finite horizon. -/
theorem canReachTerminal_iff_eventually (i : Fin n) :
    C.canReachTerminal i = true ↔
      ∃ horizon, C.survival horizon i < 1 := by
  rw [C.canReachTerminal_eq_true_iff]
  exact (C.finite_horizon_complete i).symm

/-- Keep transitions whose source and target can both reach a terminal state.
All other transitions are sent to a zero boundary. -/
def reachableTransient : Matrix (Fin n) (Fin n) ℚ≥0 := fun i j =>
  if C.canReachTerminal i && C.canReachTerminal j then C.transient i j else 0

/-- The rational matrix underlying `reachableTransient`. -/
def reachableQ : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  C.reachableTransient i j

theorem reachableQ_nonneg (i j : Fin n) : 0 ≤ C.reachableQ i j :=
  (C.reachableTransient i j).property

theorem reachableQ_le_Q (i j : Fin n) : C.reachableQ i j ≤ C.Q i j := by
  simp only [reachableQ, reachableTransient]
  split <;> simp [Q]

@[simp]
theorem reachableQ_of_unreachable_source (i : Fin n)
    (hi : C.canReachTerminal i = false) (j : Fin n) :
    C.reachableQ i j = 0 := by
  simp [reachableQ, reachableTransient, hi]

@[simp]
theorem reachableQ_of_reachable (i j : Fin n)
    (hi : C.canReachTerminal i = true)
    (hj : C.canReachTerminal j = true) :
    C.reachableQ i j = C.Q i j := by
  simp [reachableQ, reachableTransient, Q, hi, hj]

/-- The pruned matrix has no larger finite-step coefficients than the original
transient matrix. -/
theorem reachableQ_pow_le_Q_pow (horizon : ℕ) (i j : Fin n) :
    (C.reachableQ ^ horizon) i j ≤ (C.Q ^ horizon) i j := by
  induction horizon generalizing i j with
  | zero => simp
  | succ horizon ih =>
      simp only [pow_succ', Matrix.mul_apply]
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul (C.reachableQ_le_Q i k) (ih k j)
        (Matrix.pow_apply_nonneg C.reachableQ_nonneg horizon k j)
        (C.Q_nonneg i k)

/-- Total one-step mass retained by the reachable-state subsystem. -/
def reachableRowMass (i : Fin n) : ℚ≥0 :=
  ∑ j, C.reachableTransient i j

private theorem coe_reachableRowMass (i : Fin n) :
    (C.reachableRowMass i : ℚ) = ∑ j, C.reachableQ i j := by
  change (NNRat.castHom ℚ) (∑ j, C.reachableTransient i j) =
    ∑ j, (NNRat.castHom ℚ) (C.reachableTransient i j)
  exact map_sum (NNRat.castHom ℚ) _ _

theorem reachableRowMass_le_one (i : Fin n) : C.reachableRowMass i ≤ 1 := by
  rw [← NNRat.coe_le_coe]
  rw [C.coe_reachableRowMass]
  change (∑ j, C.reachableQ i j) ≤ (1 : ℚ)
  calc
    (∑ j, C.reachableQ i j) ≤ ∑ j, C.Q i j :=
      Finset.sum_le_sum fun j _ => C.reachableQ_le_Q i j
    _ ≤ 1 := by
      have hr := Finset.sum_nonneg
        (fun a (_ : a ∈ Finset.univ) => C.R_nonneg i a)
      linarith [C.row_sum i]

/-- A normalized auxiliary chain whose transient matrix is `reachableQ`.
Missing row mass exits immediately to a private terminal bearing the source
index.  The auxiliary terminals are only a proof device; computed terminal
probabilities still use the original terminal matrix `R`. -/
def reachableChain : Chain n n where
  transient := C.reachableTransient
  terminal i a := if a = i then 1 - C.reachableRowMass i else 0
  normalized i := by
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    apply NNRat.ext
    rw [NNRat.coe_add, NNRat.coe_sub (C.reachableRowMass_le_one i)]
    change (C.reachableRowMass i : ℚ) +
      (1 - (C.reachableRowMass i : ℚ)) = 1
    ring
  reward := fun _ => 0

@[simp]
theorem reachableChain_Q : C.reachableChain.Q = C.reachableQ := rfl

/-! ## Exact solver and outcome law -/

/-- Coefficient matrix of every pruned Bellman system. -/
def reachabilityMatrix : Matrix (Fin n) (Fin n) ℚ :=
  1 - C.reachableQ

/-- Mask a Bellman right-hand side outside the reachable class. -/
def reachableRhs (b : Fin n → ℚ) (i : Fin n) : ℚ :=
  if C.canReachTerminal i then b i else 0

/-- Direct executable Cramer vector.  The companion semantics module proves
that `reachabilityMatrix.det` is always nonzero; callers do not provide an
inverse or a nonsingularity certificate. -/
def solveReachable (b : Fin n → ℚ) : Fin n → ℚ :=
  C.reachabilityMatrix.det⁻¹ • C.reachabilityMatrix.cramer (C.reachableRhs b)

/-- Exact probability of ever reaching any original terminal state. -/
def reachProbability : Fin n → ℚ :=
  C.solveReachable (C.R *ᵥ fun _ => 1)

/-- Exact eventual first-hit probability of a specified original terminal. -/
def terminalProbability (terminal : Fin m) : Fin n → ℚ :=
  C.solveReachable (fun i => C.R i terminal)

/-- Exact probability of never reaching an original terminal. -/
def nonterminationProbability (i : Fin n) : ℚ :=
  1 - C.reachProbability i

/-- Terminal reward with every nonterminating execution assigned value zero. -/
def zeroOnNonhitReward : Fin n → ℚ :=
  C.solveReachable (C.R *ᵥ C.reward)

/-- Raw rational weights underlying the finite terminal/nontermination law. -/
def outcomeWeight : Option (Fin m) → Fin n → ℚ
  | some terminal => C.terminalProbability terminal
  | none => C.nonterminationProbability

/-- Decide whether the computed raw outcome vector is already a probability
vector.  The semantic leaf proves that this checker succeeds for every chain. -/
def outcomeWeightsValid (i : Fin n) : Bool :=
  decide ((∀ terminal, 0 ≤ C.terminalProbability terminal i) ∧
    0 ≤ C.nonterminationProbability i ∧
    (∑ terminal, C.terminalProbability terminal i) +
      C.nonterminationProbability i = 1)

/-- Convert the exact rational result to a `FiniteLaw` after checking its
nonnegativity and normalization.  `none` is an internal certificate failure,
not the chain's nontermination outcome; the latter is the `none` atom inside a
successful law. -/
def outcomeLaw? (i : Fin n) : Option (FiniteLaw (Option (Fin m))) :=
  if h : (∀ terminal, 0 ≤ C.terminalProbability terminal i) ∧
      0 ≤ C.nonterminationProbability i ∧
      (∑ terminal, C.terminalProbability terminal i) +
        C.nonterminationProbability i = 1 then
    some {
      atoms := (List.ofFn fun terminal =>
        (some terminal, (C.terminalProbability terminal i).toNNRat)) ++
        [(none, (C.nonterminationProbability i).toNNRat)]
      normalized := by
        simp only [List.map_append, Function.comp_def,
          List.sum_append, List.sum_ofFn, List.map_ofFn, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [← NNRat.toNNRat_sum_of_nonneg (fun terminal _ => h.1 terminal)]
        rw [← Rat.toNNRat_add (Finset.sum_nonneg fun terminal _ => h.1 terminal) h.2.1]
        simp [h.2.2]
    }
  else none

/-- Total executable terminal/nontermination law.  The fallback is unreachable:
`outcomeWeightsValid_eq_true` in the semantic leaf proves that the checked
construction always succeeds for a normalized finite rational chain. -/
def outcomeLaw (i : Fin n) : FiniteLaw (Option (Fin m)) :=
  (C.outcomeLaw? i).getD (FiniteLaw.pure none)

@[simp]
theorem outcomeLaw?_eq_some_iff (i : Fin n) :
    C.outcomeLaw? i ≠ none ↔ C.outcomeWeightsValid i = true := by
  simp [outcomeLaw?, outcomeWeightsValid]

/-! ## Finite-horizon decompositions -/

/-- Probability mass that is still transient at horizon `H` and will
eventually hit a terminal afterwards.  This differs from `survival`: closed
nonterminal classes contribute to survival but have zero late-hit mass. -/
def lateHitMass (horizon : ℕ) (i : Fin n) : ℚ :=
  (C.Q ^ horizon *ᵥ C.reachProbability) i

theorem lateHitMass_zero (i : Fin n) :
    C.lateHitMass 0 i = C.reachProbability i := by
  simp [lateHitMass]

theorem lateHitMass_succ (horizon : ℕ) (i : Fin n) :
    C.lateHitMass (horizon + 1) i =
      ∑ j, C.Q i j * C.lateHitMass horizon j := by
  unfold lateHitMass
  rw [pow_succ']
  change ((C.Q * C.Q ^ horizon) *ᵥ C.reachProbability) i =
    (C.Q *ᵥ (C.Q ^ horizon *ᵥ C.reachProbability)) i
  rw [Matrix.mulVec_mulVec]

/-- Finite Bellman unrolling.  It applies to the reach-probability vector, to
each terminal-probability vector, and to zero-on-nonhit rewards once their
Bellman equations have been established. -/
theorem bellman_unroll (b x : Fin n → ℚ)
    (hx : x = b + C.Q *ᵥ x) (horizon : ℕ) :
    x = (∑ r ∈ Finset.range horizon, C.Q ^ r *ᵥ b) +
      C.Q ^ horizon *ᵥ x := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      calc
        x = (∑ r ∈ Finset.range horizon, C.Q ^ r *ᵥ b) +
            C.Q ^ horizon *ᵥ x := ih
        _ = (∑ r ∈ Finset.range horizon, C.Q ^ r *ᵥ b) +
            C.Q ^ horizon *ᵥ (b + C.Q *ᵥ x) :=
          congrArg (fun y : Fin n → ℚ =>
            (∑ r ∈ Finset.range horizon, C.Q ^ r *ᵥ b) +
              C.Q ^ horizon *ᵥ y) hx
        _ = ((∑ r ∈ Finset.range horizon, C.Q ^ r *ᵥ b) +
              C.Q ^ horizon *ᵥ b) + C.Q ^ (horizon + 1) *ᵥ x := by
          rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← pow_succ]
          simp only [add_assoc]
        _ = (∑ r ∈ Finset.range (horizon + 1), C.Q ^ r *ᵥ b) +
              C.Q ^ (horizon + 1) *ᵥ x := by
          rw [Finset.sum_range_succ]

end FiniteMarkovChain.Chain
