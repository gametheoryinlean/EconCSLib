/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution

/-!
# Terminal-aware stopped execution

This regression verifies that a history policy is never queried for an action
after execution has reached a terminal state.
-/

namespace Examples.TerminalStoppedExecution

inductive State
  | root
  | terminal

def arena : Arena where
  State := State
  Action
    | .root => PUnit
    | .terminal => PEmpty
  next
    | .root, _ => .terminal

def policy : arena.HistoryPolicy State.root :=
  fun current hnonterminal => by
    cases h : current.1 with
    | root =>
        exact PUnit.unit
    | terminal =>
        have hterminal : arena.IsTerminal current.1 := by
          rw [h]
          exact ⟨fun action => nomatch action⟩
        exact (hnonterminal hterminal).elim

local instance terminalDecidable :
    (s : arena.State) → Decidable (arena.IsTerminal s) :=
  fun s =>
    match s with
    | .root =>
        isFalse fun hterminal =>
          hterminal.false PUnit.unit
    | .terminal =>
        isTrue ⟨fun action => nomatch action⟩

theorem one_step_reaches_terminal :
    (arena.stoppedHistory policy 1).1 = State.terminal := by
  have hroot :
      ¬ arena.IsTerminal
        (Arena.HistoryFrom.nil arena State.root).1 := by
    intro hterminal
    exact hterminal.false PUnit.unit
  rw [Arena.stoppedHistory,
    arena.stoppedHistoryFrom_succ_of_not_terminal
      policy (Arena.HistoryFrom.nil arena State.root) 0 hroot]
  rfl

theorem extra_fuel_does_not_move :
    arena.stoppedHistory policy 5 = arena.stoppedHistory policy 1 := by
  have hterminal : arena.IsTerminal (arena.stoppedHistory policy 1).1 := by
    rw [one_step_reaches_terminal]
    change IsEmpty PEmpty
    exact ⟨fun action => nomatch action⟩
  simpa using
    arena.stoppedHistoryFrom_add_of_terminal
      policy (Arena.HistoryFrom.nil arena State.root) 1 4 hterminal

end Examples.TerminalStoppedExecution
