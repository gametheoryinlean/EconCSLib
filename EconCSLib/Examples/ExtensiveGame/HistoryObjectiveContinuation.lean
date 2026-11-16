/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.HistoryDiamond
import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete

/-!
# History-sensitive objective continuation regression

Two distinct one-step histories merge into the same terminal world state.
The payoff-free terminal-objective continuation semantics nevertheless
distinguishes them because it evaluates the complete accumulated history,
not only the endpoint.
-/

namespace Examples.HistoryObjectiveContinuation

open HistoryDiamond

/-- The diamond dynamics controlled by one player at its root. -/
def base : ControlledGame Unit where
  toArena := arena
  init := State.root
  mover
    | .root => some ()
    | .terminal => none

/-- Complete information is sufficient for the one-decision regression. -/
abbrev game : ExtensiveGame.ControlledObservedGame Unit :=
  ExtensiveGame.ControlledObservedGame.completeInformation base

local instance terminalDecidable :
    (state : base.State) → Decidable (base.isTerminal state) :=
  fun state => match state with
    | .root => isFalse (fun h => h.false false)
    | .terminal => isTrue ⟨PEmpty.elim⟩

example : decide (base.isTerminal State.root) = false ∧
    decide (base.isTerminal State.terminal) = true := by
  native_decide

/-- The controlled diamond has no non-player-controlled reachable decision. -/
theorem noChance : base.NoChance := by
  intro state hnonterminal
  cases state with
  | root =>
      exact ⟨(), rfl⟩
  | terminal =>
      exact False.elim
        (hnonterminal (by
          show IsEmpty PEmpty
          infer_instance))

/-- Reachable no-chance certificate used by pure continuation execution. -/
def noChanceOnHistories : base.NoChanceOnHistories :=
  noChance.noChanceOnHistories

/-- The left and right absolute histories, sharing one terminal endpoint. -/
def leftCurrent : base.History :=
  ⟨State.terminal, left⟩

def rightCurrent : base.History :=
  ⟨State.terminal, right⟩

theorem leftCurrent_terminal :
    base.isTerminal leftCurrent.1 := by
  show IsEmpty PEmpty
  infer_instance

theorem rightCurrent_terminal :
    base.isTerminal rightCurrent.1 := by
  show IsEmpty PEmpty
  infer_instance

theorem rightCurrent_ne_leftCurrent :
    rightCurrent ≠ leftCurrent := by
  intro heq
  have hhistory : right = left := by
    cases heq
  exact left_ne_right hhistory.symm

/-- Executable zero-fuel termination plan at the left continuation. -/
def pureTerminationPlanAt_left :
    game.PureTerminationPlanAt noChanceOnHistories leftCurrent where
  fuel := fun _profile => 0
  terminal := fun _profile => leftCurrent_terminal

/-- Executable zero-fuel termination plan at the right continuation. -/
def pureTerminationPlanAt_right :
    game.PureTerminationPlanAt noChanceOnHistories rightCurrent where
  fuel := fun _profile => 0
  terminal := fun _profile => rightCurrent_terminal

section RouteObjective

/-- Decide left-route equality by the recorded action, not its endpoint. -/
local instance historyLeftDecidable (history : base.History) :
    Decidable (history = leftCurrent) := by
  rcases history with ⟨state, path⟩
  cases path with
  | nil => exact isFalse (by intro h; cases h)
  | @snoc previous path action =>
    cases path with
    | nil =>
      cases action
      · exact isTrue rfl
      · exact isFalse (by intro h; cases h)
    | @snoc earlier path previousAction =>
      cases earlier with
      | root => exact PEmpty.elim action
      | terminal => exact PEmpty.elim previousAction

/-- The original equality test now compares the actual root action. -/
def routeObjective :
    base.toArena.TerminalOutcome base.init Bool :=
  fun terminalHistory =>
    if terminalHistory.1 = leftCurrent then false else true

/-- The complete pure profile choosing the concrete left root action. -/
def profile : game.PureProfile := by
  intro player information
  rcases information with ⟨⟨⟨state, history⟩, hmover, hdecision⟩, hrepresented⟩
  cases state with
  | root => exact false
  | terminal => cases hmover

/-- The left continuation evaluates the left occurrence. -/
theorem left_outcome :
    (game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories leftCurrent
      pureTerminationPlanAt_left).outcome profile = false := by
  classical
  change
    (if game.terminalHistoryFrom profile noChanceOnHistories
          leftCurrent (pureTerminationPlanAt_left.fuel profile) = leftCurrent
      then false else true) = false
  rw [game.terminalHistoryFrom_eq_of_terminal
    profile noChanceOnHistories leftCurrent
    (pureTerminationPlanAt_left.fuel profile)
    (pureTerminationPlanAt_left.terminal profile) 0 leftCurrent_terminal]
  simp

/-- The right continuation evaluates the distinct right occurrence despite
sharing the left continuation's endpoint state. -/
theorem right_outcome :
    (game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories rightCurrent
      pureTerminationPlanAt_right).outcome profile = true := by
  classical
  change
    (if game.terminalHistoryFrom profile noChanceOnHistories
          rightCurrent (pureTerminationPlanAt_right.fuel profile) = leftCurrent
      then false else true) = true
  rw [game.terminalHistoryFrom_eq_of_terminal
    profile noChanceOnHistories rightCurrent
    (pureTerminationPlanAt_right.fuel profile)
    (pureTerminationPlanAt_right.terminal profile) 0 rightCurrent_terminal]
  simp [rightCurrent_ne_leftCurrent]

/-- The two continuation game forms distinguish occurrence histories that an
endpoint-payoff semantics alone cannot distinguish. -/
theorem continuation_outcomes_ne :
    (game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories leftCurrent
      pureTerminationPlanAt_left).outcome profile ≠
    (game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories rightCurrent
      pureTerminationPlanAt_right).outcome profile := by
  rw [left_outcome, right_outcome]
  simp

-- Both terminal occurrences and an actual root step execute without choice.
example :
    (fun left right : Bool => left = false ∧ right = true)
    ((game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories leftCurrent
      pureTerminationPlanAt_left).outcome profile)
    ((game.terminalObjectiveContinuationGameForm
      routeObjective noChanceOnHistories rightCurrent
      pureTerminationPlanAt_right).outcome profile) ∧
    decide (base.toArena.stoppedHistoryFrom
      (ExtensiveGame.ControlledObservedGame.PureProfile.toHistoryPolicy
        (G := game) profile noChanceOnHistories)
      (Arena.HistoryFrom.nil base.toArena base.init) 1 = leftCurrent) = true := by
  native_decide

end RouteObjective

/-- An endpoint-payoff observed game on the same controlled carrier. -/
def endpointGame : ExtensiveGame.ObservedGame Unit Bool :=
  ExtensiveGame.ObservedGame.ofControlledObservedGame game
    (fun state _player =>
      match state with
      | .root => false
      | .terminal => true)

local instance endpointTerminalDecidable :
    (state : endpointGame.base.State) →
      Decidable (endpointGame.base.isTerminal state) :=
  terminalDecidable

/-- Adding endpoint payoffs does not change the controlled termination
certificate. -/
def endpointPureTerminationPlanAt_left :
    endpointGame.PureTerminationPlanAt noChanceOnHistories leftCurrent :=
  pureTerminationPlanAt_left

/-- The historical endpoint-payoff continuation is definitionally the
terminal-objective specialization on this concrete game. -/
theorem endpoint_payoff_specialization :
    endpointGame.terminalContinuationGameForm
        noChanceOnHistories leftCurrent
        endpointPureTerminationPlanAt_left =
      endpointGame.toControlledObservedGame.terminalObjectiveContinuationGameForm
          endpointGame.base.terminalPayoffOutcome
          noChanceOnHistories leftCurrent
          endpointPureTerminationPlanAt_left :=
  endpointGame.terminalContinuationGameForm_eq_terminalObjective
    noChanceOnHistories leftCurrent endpointPureTerminationPlanAt_left

end Examples.HistoryObjectiveContinuation
