/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Winning

/-!
# Logical winning import boundary

The winning facade exposes winning conditions, pure/quasi winning strategies,
determinacy predicates, and explicit finite/well-founded hypothesis packages.
It does not import stochastic path laws or analytic kernels.
-/

#check Arena.WinningConditionFrom.IsTwoPlayerZeroSum
#check ExtensiveGame.ControlledObservedGame.HasPathwiseWinningStrategy
#check ExtensiveGame.ControlledObservedGame.IsTwoPlayerDetermined
#check ExtensiveGame.ControlledObservedGame.FiniteTwoPlayerHypotheses
#check ExtensiveGame.ControlledObservedGame.FiniteTwoPlayerHypotheses.isTwoPlayerDetermined
#check ExtensiveGame.ControlledObservedGame.WellFoundedTwoPlayerHypotheses
#check ExtensiveGame.ControlledObservedGame.BackwardInductionData
#check ExtensiveGame.ControlledObservedGame.backwardWinner
#check ExtensiveGame.ControlledObservedGame.backwardStrategy
#check ExtensiveGame.ControlledObservedGame.WellFoundedTwoPlayerHypotheses.isTwoPlayerDetermined
#check ExtensiveGame.ControlledObservedGame.WellFoundedPrefixHypotheses
#check ExtensiveGame.ControlledObservedGame.WellFoundedPrefixHypotheses.isTwoPlayerDetermined
#check ExtensiveGame.ObservedGame.HasPathwiseWinningStrategy
#check ExtensiveGame.ObservedGame.HasPureProfileExtension
#check ExtensiveGame.ObservedGame.HasStrategicWinningStrategy
#check ExtensiveGame.ObservedGame.EveryCompatiblePlayRealizableByPureProfile
#check ExtensiveGame.ObservedGame.HasWinningQuasiStrategy
#check ExtensiveGame.ObservedGame.HasSomePathwiseWinningStrategy
#check ExtensiveGame.ObservedGame.IsTwoPlayerDetermined
#check ExtensiveGame.ObservedGame.FiniteTwoPlayerHypotheses
#check ExtensiveGame.ObservedGame.WellFoundedPrefixHypotheses

/--
error: Unknown constant `ExtensiveGame.ObservedGame.HasWinningStrategy`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.HasWinningStrategy

/--
error: Unknown constant `ExtensiveGame.ObservedGame.WinningStrategies`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.WinningStrategies

/--
error: Unknown constant `ExtensiveGame.ObservedGame.IsDetermined`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.IsDetermined

/--
error: Unknown constant `ExtensiveGame.ObservedGame.isDetermined_of_hasWinningStrategy`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.isDetermined_of_hasWinningStrategy

/--
error: Unknown constant `ExtensiveGame.ObservedGame.isDetermined_iff_isTwoPlayerDetermined`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.isDetermined_iff_isTwoPlayerDetermined

/--
error: Unknown constant `ExtensiveGame.ObservedGame.not_both_haveWinningStrategy`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.not_both_haveWinningStrategy

/--
error: Unknown constant `Arena.pathLaw`
-/
#guard_msgs in
#check Arena.pathLaw

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena

namespace Examples.ExecutableBackwardInduction

open ExtensiveGame
open ExtensiveGame.ControlledObservedGame

/-- A one-state terminal controlled game used to execute the backward winner. -/
def terminalBase : ControlledGame (Fin 2) where
  State := Unit
  Action := fun _ => (PEmpty : Type)
  next := fun _ action => nomatch action
  init := ()
  mover := fun _ => none

/-- The terminal game has no decision-information coordinates. -/
def terminalGame : ControlledObservedGame (Fin 2) where
  base := terminalBase
  InfoState := fun _ => (PEmpty : Type)
  infoAt := fun history _ hmover _ => by
    simp [terminalBase] at hmover
  InfoAction := fun _ information => nomatch information
  actionEquiv := fun history _ hmover _ => by
    simp [terminalBase] at hmover
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  infoObserve := fun _ information => nomatch information
  infoAt_observe := by
    intro history _ hmover _
    simp [terminalBase] at hmover

/-- Player zero wins the unique complete play. -/
def terminalWinningCondition : terminalGame.base.WinningCondition :=
  fun i _ => i = 0

theorem terminal_isTerminal :
    terminalGame.base.isTerminal () := by
  change IsEmpty PEmpty
  infer_instance

def terminalHypotheses :
    terminalGame.WellFoundedTwoPlayerHypotheses
      terminalWinningCondition where
  wellFounded :=
    Arena.HasLengthBoundAt.isWellFoundedAt
      (Arena.HasLengthBoundAt.of_terminal
      (current := Arena.HistoryFrom.nil terminalBase.toArena ())
      terminal_isTerminal)
  noChance := by
    intro history hnonterminal
    exact (hnonterminal terminal_isTerminal).elim
  perfectInformation := by
    intro _ _ _ firstMover _ _ _ _
    change (none : Option (Fin 2)) = some _ at firstMover
    contradiction
  zeroSum := by
    intro _play
    change
      (((0 : Fin 2) = 0) ∧ ¬ ((1 : Fin 2) = 0)) ∨
        (¬ ((0 : Fin 2) = 0) ∧ (1 : Fin 2) = 0)
    exact Or.inl ⟨rfl, by decide⟩

def terminalData :
    terminalGame.BackwardInductionData terminalWinningCondition where
  terminalDecidable := fun state => by
    cases state
    exact isTrue terminal_isTerminal
  terminalWinner := fun _ _ => 0
  terminalWinner_mem := by
    intro _ _
    rfl
  actions := fun _ => []
  actions_complete := by
    intro history action
    exact nomatch action
  representative := fun _ information => nomatch information.1

/-- Executable regression: the backward recursion computes player zero as
the winner of the terminal game. -/
example :
    backwardWinner terminalHypotheses terminalData
        (Arena.HistoryFrom.nil terminalBase.toArena ()) = 0 := by
  native_decide

end Examples.ExecutableBackwardInduction
