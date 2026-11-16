/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete

/-!
# Reachable no-chance regression

This model has a one-step reachable strategic game and an ambient,
nonterminal nature state on a disjoint unreachable side of the Arena. It
formally refutes global `NoChance`, proves `NoChanceOnHistories`, and uses the
reachable certificate in canonical pure execution and termination-certified
continuation infrastructure.
-/

namespace Examples.ReachableNoChance

/-- The first bit selects the unreachable ghost component; the second records
whether the reachable one-step game has terminated. -/
abbrev State := Bool × Bool

/-- Reachable play has one root action. Ghost states have a looping action and
the reachable terminal state has none. -/
def Action : State → Type
  | (false, false) => Unit
  | (false, true) => Empty
  | (true, _) => Unit

/-- The reachable root terminates after one action; ghost states loop. -/
def next : (state : State) → Action state → State
  | (false, false), _ => (false, true)
  | (false, true), action => nomatch action
  | (true, done), _ => (true, done)

/-- Ambient Arena with an unreachable ghost component. -/
def arena : Arena where
  State := State
  Action := Action
  next := next

/-- Payoff-aware base used only to reuse the standard observed presentation. -/
def base : ExtensiveGame Unit Unit where
  toArena := arena
  init := (false, false)
  mover
    | (false, false) => some ()
    | _ => none
  payoff := fun _ _ => ()

/-- Complete-information observation of the one-step reachable game. -/
def game : ExtensiveGame.ObservedGame Unit Unit :=
  ExtensiveGame.ObservedGame.completeInformation base

local instance terminalDecidable :
    (state : game.base.State) →
      Decidable (game.base.isTerminal state) :=
  fun state => match state with
    | (false, false) => isFalse (fun h => h.false ())
    | (false, true) => isTrue ⟨Empty.elim⟩
    | (true, _) => isFalse (fun h => h.false ())

example : decide (game.base.isTerminal (false, false)) = false ∧
    decide (game.base.isTerminal (false, true)) = true ∧
    decide (game.base.isTerminal (true, false)) = false ∧
    decide (game.base.isTerminal (true, true)) = false := by
  native_decide

/-- Every complete history from the initial state remains on the reachable
component. -/
theorem history_not_ghost
    {state : arena.State}
    (history : arena.History base.init state) :
    state.1 = false := by
  induction history with
  | nil => rfl
  | @snoc state history action ih =>
      rcases state with ⟨ghost, done⟩
      cases ghost with
      | false =>
          cases done with
          | false => rfl
          | true => exact nomatch action
      | true =>
          simp at ih

/-- The ambient ghost state makes global no-chance false. -/
theorem not_globalNoChance :
    ¬ game.base.NoChance := by
  intro hNoChance
  have hnonterminal :
      ¬ game.base.isTerminal (true, false) := by
    exact not_isEmpty_iff.mpr ⟨()⟩
  rcases hNoChance (true, false) hnonterminal with ⟨i, hmover⟩
  simp [game, base] at hmover

/-- All legal histories generated from the initial state are chance-free. -/
theorem noChanceOnHistories :
    game.base.NoChanceOnHistories := by
  intro history hnonterminal
  have hside := history_not_ghost history.2
  rcases history with ⟨⟨ghost, done⟩, path⟩
  simp only at hside
  subst ghost
  cases done with
  | false =>
      exact ⟨(), rfl⟩
  | true =>
      exact
        (hnonterminal (by
          change IsEmpty Empty
          infer_instance)).elim

/-- The decision-history presentation has no ghost information states. -/
theorem allDecisionInfoRepresented :
    game.AllDecisionInfoRepresented := by
  intro i information
  refine ⟨
    { history := information.1
      mover := information.2.1
      decision := information.2.2
      infoAt_eq := rfl }⟩

/-- Every reachable player-labelled history is the nonterminal root. -/
theorem decisionMoverCoherent :
    game.DecisionMoverCoherent := by
  intro history i hmover
  have hside := history_not_ghost history.2
  rcases history with ⟨⟨ghost, done⟩, path⟩
  simp only at hside
  subst ghost
  cases done with
  | false => exact ⟨()⟩
  | true =>
      simp [game, base] at hmover

/-- The complete pure profile selects the sole legal action at each decision. -/
def profile : game.PureProfile := by
  intro player information
  rcases information with ⟨⟨⟨⟨ghost, done⟩, history⟩, hmover, hdecision⟩, hrepresented⟩
  cases ghost with
  | false =>
    cases done with
    | false => exact ()
    | true => cases hmover
  | true => exact ()

/-- Reachable no-chance is sufficient to build the canonical pure history
policy; the unreachable nature state is never queried. -/
def pureHistoryPolicy :
    game.base.toArena.HistoryPolicy game.base.init :=
  ExtensiveGame.ControlledObservedGame.PureProfile.toHistoryPolicy
    (G := game.toControlledObservedGame) profile noChanceOnHistories

/-- Executable one-step termination plan from the initial history. -/
def pureTerminationPlanInitially :
    game.PureTerminationPlanAt noChanceOnHistories
      (Arena.HistoryFrom.nil game.base.toArena game.base.init) where
  fuel := fun _profile => 1
  terminal := by
    intro arbitraryProfile
    let current :=
      Arena.HistoryFrom.nil game.base.toArena game.base.init
    have hnonterminal : ¬game.base.isTerminal current.1 := by
      change ¬IsEmpty Unit
      intro hterminal
      exact hterminal.false ()
    change game.base.isTerminal
      (game.stoppedHistoryFrom arbitraryProfile noChanceOnHistories current 1).1
    rw [ExtensiveGame.ObservedGame.stoppedHistoryFrom]
    rw [Arena.stoppedHistoryFrom_succ_of_not_terminal
      (ExtensiveGame.ControlledObservedGame.PureProfile.toHistoryPolicy
        (G := game.toControlledObservedGame)
        arbitraryProfile noChanceOnHistories)
      current 0 hnonterminal]
    rw [Arena.stoppedHistoryFrom_zero]
    change IsEmpty Empty
    infer_instance

/-- The total pure continuation game form is available from reachable
no-chance even though the global arena contains an unreachable nature node. -/
def initialContinuationGameForm :
    GameForm Unit :=
  game.terminalContinuationGameForm noChanceOnHistories
    (Arena.HistoryFrom.nil game.base.toArena game.base.init)
    pureTerminationPlanInitially

-- A zero horizon stays at the root; one actual policy step terminates.
example :
    (fun before after : Bool × Bool =>
      before = (false, false) ∧ after = (false, true))
    (game.base.toArena.stoppedHistoryFrom pureHistoryPolicy
      (Arena.HistoryFrom.nil game.base.toArena game.base.init) 0).1
    (game.base.toArena.stoppedHistoryFrom pureHistoryPolicy
      (Arena.HistoryFrom.nil game.base.toArena game.base.init) 1).1 := by
  native_decide

end Examples.ReachableNoChance
