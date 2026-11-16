/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Core

/-!
# Core/discrete import boundary

The core facade provides typed deterministic and stochastic history execution
plus payoff-free controlled information. Payoff-aware observed games, infinite
event-time execution, and discrete kernel arenas remain opt-in.
-/

#check ControlledGame
#check ExtensiveGame.ControlledObservedGame
#check ExtensiveGame.ControlledObservedGame.completeInformation
#check ExtensiveGame.ControlledObservedGame.ContinuationRootPresentation.initialOnly
#check ExtensiveGame.ControlledObservedGame.ContinuationRootPresentation.allHistories
#check ExtensiveGame.ControlledObservedGame.SubgameSystem.initialOnly
#check ExtensiveGame.ControlledObservedGame.isLawfulSubgameRoot_relabelPlayers_iff
#check ExtensiveGame.ControlledObservedGame.SubgameSystem.relabelPlayers
#check ExtensiveGame.ControlledObservedGame.CompleteSubgameSystem.relabelPlayers
#check Arena.CompletePlayFromHistory
#check Arena.HasLengthBoundAt
#check Arena.IsWellFoundedAt
#check ExtensiveGame.ControlledObservedGame.AllDecisionInfoRepresented
#check ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses
#check ExtensiveGame.ControlledObservedGame.RecallCertificate
#check ExtensiveGame.ControlledObservedGame.SignalRecallCertificate
#check ExtensiveGame.ControlledObservedGame.PublicRecallCertificate
#check Arena.StochasticHistoryPolicy

/--
error: Unknown constant `ExtensiveGame.ObservedGame`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame

/--
error: Unknown identifier `KernelArena`
-/
#guard_msgs in
#check KernelArena

/--
error: Unknown constant `Arena.pathLaw`
-/
#guard_msgs in
#check Arena.pathLaw

/--
error: Unknown constant `ExtensiveGame.ObservedChanceGame.withChanceKernel`
-/
#guard_msgs in
#check ExtensiveGame.ObservedChanceGame.withChanceKernel

namespace CompleteInformationInstanceBoundary

open ExtensiveGame

variable {N : Type*} (base : ControlledGame N) (i : N)

abbrev observed :=
  ControlledObservedGame.completeInformation base

/-- Decidable equality on histories is reused without a constructor-specific
typeclass assumption. -/
example [DecidableEq (base.toArena.HistoryFrom base.init)] :
    DecidableEq ((observed base).Observation i) :=
  inferInstance

/-- Finite histories induce finite decision-history information subtypes
without requiring decidable mover equality. -/
example [Finite (base.toArena.HistoryFrom base.init)] :
    Finite ((observed base).InfoState i) :=
  inferInstance

end CompleteInformationInstanceBoundary

namespace TerminalMoverDecisionBoundary

open ExtensiveGame

/-- A terminal one-state game whose irrelevant mover label is deliberately
left unnormalized. -/
def terminalPlayerLabeledBase : ControlledGame Unit where
  State := Unit
  Action := fun _state => Empty
  next := fun _state action => nomatch action
  init := ()
  mover := fun _state => some ()

/-- Every state of the one-state game is terminal. -/
theorem terminalPlayerLabeledBase_isTerminal
    (state : terminalPlayerLabeledBase.State) :
    terminalPlayerLabeledBase.isTerminal state :=
  ⟨fun action => nomatch action⟩

/-- Complete information creates no decision coordinate from a terminal
player label. This is the regression for the nonterminal `infoAt` contract. -/
theorem decisionHistory_isEmpty :
    IsEmpty
      (ControlledObservedGame.CompleteInformation.DecisionHistory
        terminalPlayerLabeledBase ()) :=
  ⟨fun information =>
    (not_nonempty_iff.mpr
      (terminalPlayerLabeledBase_isTerminal information.1.1))
      information.property.2⟩

/-- The resulting strategy is the unique vacuous function on an empty
decision-information carrier. -/
def vacuousPureStrategy :
    (ControlledObservedGame.completeInformation terminalPlayerLabeledBase).PureStrategy
      () :=
  fun information =>
    (decisionHistory_isEmpty.false information.1).elim

end TerminalMoverDecisionBoundary
