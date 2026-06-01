/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic
import Mathlib.Data.Rat.Cast.Defs

/-!
# EconCSLib.Examples.EntryDeterrence

The Entry Deterrence game: a classic 2-player extensive-form game.

```
                    Player 0
                   /        \
              Enter          Stay Out
               |               |
           Player 1          (1, 3)
           /      \
     Accommodate  Fight
        |           |
      (2, 2)      (0, 0)
```

## References

* [MSZ] Example 7.1
-/

/-! ### States and actions -/

inductive EDState | root | afterEnter | stayOut | accommodate | fight
  deriving DecidableEq, Repr, Inhabited

inductive EntrantAction | Enter | StayOut
  deriving DecidableEq, Repr, Inhabited

inductive IncumbentAction | Accommodate | Fight
  deriving DecidableEq, Repr, Inhabited

instance : Nonempty EntrantAction := ⟨.Enter⟩
instance : Nonempty IncumbentAction := ⟨.Accommodate⟩

open EDState EntrantAction IncumbentAction

@[reducible] def edAction : EDState → Type
  | root => EntrantAction
  | afterEnter => IncumbentAction
  | stayOut => Empty
  | accommodate => Empty
  | fight => Empty


/-! ### Game definition -/

@[reducible] def ED : ExtensiveGame (Fin 2) ℚ where
  State := EDState
  Action := edAction
  next s a := match s, a with
    | root, (Enter : edAction root) => afterEnter
    | root, (StayOut : edAction root) => stayOut
    | afterEnter, (Accommodate : edAction afterEnter) => accommodate
    | afterEnter, (Fight : edAction afterEnter) => fight
  init := root
  mover s := match s with
    | root => some 0
    | afterEnter => some 1
    | _ => none
  payoff s i := match s, i.val with
    | stayOut, 0 => 1
    | stayOut, _ => 3
    | accommodate, _ => 2
    | fight, _ => 0
    | _, _ => 0

/-! ### Verification -/

-- Terminal states (edAction s = Empty, so IsEmpty holds)
example : IsEmpty (edAction stayOut) := inferInstance
example : IsEmpty (edAction accommodate) := inferInstance
example : IsEmpty (edAction fight) := inferInstance

-- Non-terminal states (have at least one action)
example : Nonempty (edAction root) := ⟨Enter⟩
example : Nonempty (edAction afterEnter) := ⟨Accommodate⟩

-- Player assignment
example : ED.mover root = some 0 := rfl
example : ED.mover afterEnter = some 1 := rfl

-- Transitions
example : ED.next root Enter = afterEnter := rfl
example : ED.next root StayOut = stayOut := rfl
example : ED.next afterEnter Accommodate = accommodate := rfl
example : ED.next afterEnter Fight = fight := rfl

-- Payoffs
example : ED.payoff accommodate 0 = 2 := rfl
example : ED.payoff accommodate 1 = 2 := rfl
example : ED.payoff stayOut 0 = 1 := rfl
example : ED.payoff stayOut 1 = 3 := rfl
example : ED.payoff fight 0 = 0 := rfl
example : ED.payoff fight 1 = 0 := rfl
