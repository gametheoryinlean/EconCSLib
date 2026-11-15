/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.ExactRealController



section

/-!
# Closed exact-real executions

The empty external alphabet forbids oracle calls and callback computation. Cost is
accumulated from the concrete controller, including input and output copying.
-/
namespace EconCSLib.OpenProblem.New.ExactRealController

/-- A successful explicit output, a fault, or exhausted simulation fuel. -/
inductive ClosedTermination
  | halted (words : List ℕ) (reals : List ℝ)
  | faulted
  | outOfFuel

structure ClosedResult where
  termination : ClosedTermination
  cost : ℕ

/-- One closed finite program; there is no external request constructor value. -/
noncomputable def executeClosed (width : ℕ) (program : Program Empty) :
    ℕ → State → ClosedResult
  | 0, _ => ⟨.outOfFuel, 0⟩
  | fuel + 1, state =>
      let next := step width program state
      match next.status with
      | .running =>
          let rest := executeClosed width program fuel next.state
          { rest with cost := next.cost + rest.cost }
      | .halted words reals => ⟨.halted words reals, next.cost⟩
      | .faulted => ⟨.faulted, next.cost⟩
      | .request operation _ _ _ _ => nomatch operation

/-- Public canonical initialization, with address-capacity checks and copying cost. -/
noncomputable def runClosed (width : ℕ) (program : Program Empty) (fuel : ℕ)
    (wordInput : List ℕ) (realInput : List ℝ) : ClosedResult := by
  classical
  exact if wordInput.length < WordRAM.wordModulus width ∧
      realInput.length ≤ WordRAM.wordModulus width ∧
      ∀ word ∈ wordInput, WordRAM.FitsInWord width word then
    let result := executeClosed width program fuel (State.initial width wordInput realInput)
    { result with cost := initialCost program wordInput realInput + result.cost }
  else ⟨.faulted, initialCost program wordInput realInput⟩

/-- More simulation fuel cannot change a terminal result or its price. -/
theorem executeClosed_add_fuel_of_terminal (width : ℕ) (program : Program Empty)
    (fuel extra : ℕ) (state : State)
    (terminal : (executeClosed width program fuel state).termination ≠ .outOfFuel) :
    executeClosed width program (fuel + extra) state =
      executeClosed width program fuel state := by
  induction fuel generalizing state with
  | zero => simp [executeClosed] at terminal
  | succ fuel ih =>
      cases hstep : step width program state with
      | mk next status cost =>
          cases status with
          | running =>
              have h : (executeClosed width program fuel next).termination ≠ .outOfFuel := by
                simpa [executeClosed, hstep] using terminal
              simp only [Nat.succ_add, executeClosed, hstep]
              rw [ih next h]
          | halted words reals => simp [Nat.succ_add, executeClosed, hstep]
          | faulted => simp [Nat.succ_add, executeClosed, hstep]
          | request operation a b c d => exact Empty.elim operation

/-- Even a faulty or zero-fuel execution pays for its public input and code. -/
theorem runClosed_cost_ge_initial (width : ℕ) (program : Program Empty) (fuel : ℕ)
    (wordInput : List ℕ) (realInput : List ℝ) :
    initialCost program wordInput realInput ≤
      (runClosed width program fuel wordInput realInput).cost := by
  classical
  simp only [runClosed]
  split_ifs <;> simp

end EconCSLib.OpenProblem.New.ExactRealController

end
