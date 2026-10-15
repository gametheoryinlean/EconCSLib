/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteMarkovChain.Semantics

/-!
# Exact finite absorbing-chain examples

These models use the library's `FiniteMarkovChain.Chain` directly. Read the
geometric model first, then the two-stage and cyclic models, and finally the
full-domain rejection example. Runtime regressions live in
`tests/FiniteMarkovChainSmoke.lean`; the propositions below are ordinary Lean
proofs instantiating the library's analytic correctness theorems.
-/

namespace Examples.FiniteMarkovChain

open _root_.FiniteMarkovChain MeasureTheory

section Models

/-- A fair repeat-or-stop experiment with terminal reward six. -/
def geometric : Chain 1 1 where
  transient _ _ := 1 / 2
  terminal _ _ := 1 / 2
  normalized := by intro i; norm_num
  reward _ := 6

/-- One mandatory transition followed by a geometric wait and two terminal outcomes. -/
def twoStage : Chain 2 2 where
  transient i j := if j = 1 then if i = 0 then 1 else 1 / 2 else 0
  terminal i _ := if i = 0 then 0 else 1 / 4
  normalized := by intro i; fin_cases i <;> norm_num [Fin.sum_univ_two]
  reward a := if a = 0 then -2 else 6

/-- A two-state cycle with a fair chance to exit on every second transition. -/
def cyclic : Chain 2 1 where
  transient i j := if i = 0 then if j = 1 then 1 else 0
    else if j = 0 then 1 / 2 else 0
  terminal i _ := if i = 0 then 0 else 1 / 2
  normalized := by intro i; fin_cases i <;> norm_num [Fin.sum_univ_two]
  reward _ := 5

/-- State zero terminates immediately; state one is a closed class. -/
def partiallyClosed : Chain 2 1 where
  transient i j := if i = 1 ∧ j = 1 then 1 else 0
  terminal i _ := if i = 0 then 1 else 0
  normalized := by intro i; fin_cases i <;> norm_num [Fin.sum_univ_two]
  reward _ := 6

/-- No transient starts: absorption is vacuous and terminal values remain defined. -/
def noTransient : Chain 0 1 where
  transient i := Fin.elim0 i
  terminal i := Fin.elim0 i
  normalized i := Fin.elim0 i
  reward _ := -3

end Models

section GeometricSemantics

private lemma geometric_reaches (i : Fin 1) :
    ∃ horizon, geometric.survival horizon i < 1 := by
  refine ⟨1, ?_⟩
  norm_num [Chain.survival, Chain.Q, geometric]

/-- The automatic checker certifies the actual geometric model. -/
lemma geometric_autoCheck : geometric.autoCheck = true :=
  geometric.autoCheck_iff_reaches.mpr geometric_reaches

/-- The joint first-hit law is normalized, although finite runs retain unfinished mass. -/
theorem geometric_firstHit_probability :
    IsProbabilityMeasure (Measure.sum fun p : ℕ × Fin 1 =>
      ENNReal.ofReal (geometric.hit p.1 0 p.2 : ℝ) • Measure.dirac p) :=
  geometric.firstHit_probability geometric_autoCheck 0

/-- Exact automatic solving succeeds without a caller-supplied candidate or inverse. -/
theorem geometric_solver_succeeds : ∃ result, geometric.autoSolve = .ok result :=
  geometric.autoSolve_success_iff.mpr
    (geometric.autoCheck_iff_absorbsAll.mp geometric_autoCheck)

/-- The concrete geometric model has expected reward six and expected duration two. -/
theorem geometric_integrals :
    let μ := Measure.sum fun p : ℕ × Fin 1 =>
      ENNReal.ofReal (geometric.hit p.1 0 p.2 : ℝ) • Measure.dirac p
    (∫ p : ℕ × Fin 1, (geometric.reward p.2 : ℝ) ∂μ) = 6 ∧
      (∫ p : ℕ × Fin 1, ((p.1 + 1 : ℕ) : ℝ) ∂μ) = 2 := by
  obtain ⟨v, t, _, hv, ht, _, _, hs⟩ := geometric.autoSolve_correct geometric_autoCheck
  have hv0 := congrFun hv 0
  have ht0 := congrFun ht 0
  norm_num [Matrix.mulVec, dotProduct, Chain.Q, Chain.R, geometric] at hv0 ht0
  have hv6 : v 0 = 6 := by linarith
  have ht2 : t 0 = 2 := by linarith
  obtain ⟨_, _, _, he, hd⟩ := hs 0
  simpa only [hv6, ht2, Rat.cast_ofNat] using And.intro he hd

end GeometricSemantics

section Consumer

variable {n m : ℕ} (C : Chain n m)
variable (h : C.autoCheck = true)

include h

/-- A consumer can use a computed value-duration pair as the actual pair of integrals. -/
theorem computed_integrals (i : Fin n) (value duration : ℚ)
    (result : C.autoSolve.map (fun vt => (vt.1 (.inl i), vt.2 (.inl i))) =
      .ok (value, duration)) :
    let μ := Measure.sum fun p : ℕ × Fin m =>
      ENNReal.ofReal (C.hit p.1 i p.2 : ℝ) • Measure.dirac p
    (∫ p : ℕ × Fin m, (C.reward p.2 : ℝ) ∂μ) = (value : ℝ) ∧
      (∫ p : ℕ × Fin m, ((p.1 + 1 : ℕ) : ℝ) ∂μ) = (duration : ℝ) :=
  C.autoSolve_integrals h i value duration result

end Consumer

end Examples.FiniteMarkovChain
