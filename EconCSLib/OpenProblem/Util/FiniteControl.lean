/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fin.Basic

/-!
# Explicitly finite control flow for ordinary Lean functions

These are ordinary executable Lean definitions, not a deep embedding.  They
make the termination budget of common loops a visible natural argument, so a
source-cost reader can derive a uniform upper bound without reconstructing a
general well-founded termination proof.

The functions do not attach a complexity claim by themselves.  A caller must
still relate `fuel` or `count` to its chosen input-size measure.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM.FiniteControl

/-- Execute `step` at most `count` times.  The index counts down from
`count - 1` to zero. -/
def repeatFuel {State : Type*} : ℕ → (ℕ → State → State) → State → State
  | 0, _, state => state
  | count + 1, step, state => repeatFuel count step (step count state)

/-- Pure while-loop with an explicit iteration budget.  It stops when the
condition is false or after `fuel` successful iterations. -/
def whileFuel {State : Type*} :
    ℕ → (State → Bool) → (State → State) → State → State
  | 0, _, _, state => state
  | fuel + 1, condition, step, state =>
      if condition state then
        whileFuel fuel condition step (step state)
      else state

/-- Fold over exactly the finite indices `0, ..., count - 1`. -/
def foldFin {State : Type*} (count : ℕ)
    (step : State → Fin count → State) (initial : State) : State :=
  Fin.foldl count step initial

/-- Search a finite prefix and return the first index accepted by `predicate`.
No index at or beyond `bound` is inspected. -/
def findFirst (bound : ℕ) (predicate : ℕ → Bool) : Option ℕ :=
  (List.range bound).find? predicate

end EconCSLib.OpenProblem.UnitCostRAM.FiniteControl
