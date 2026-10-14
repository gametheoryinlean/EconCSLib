/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Objective

/-!
# Objective import boundary

The objective facade exposes measure-free complete plays, structural
termination certificates, history-sensitive outcomes, and winning conditions
without importing chance execution, infinite probability laws, equilibrium,
or analytic kernels.
-/

#check Arena.CompletePlayFromHistory
#check ControlledGame
#check ExtensiveGame.ControlledObservedGame
#check Arena.HasLengthBoundAt
#check Arena.IsWellFoundedAt
#check Arena.TerminalHistoryFrom
#check Arena.TerminalOutcome
#check Arena.PathOutcome
#check Arena.CompletePlayFromHistory.resume
#check Arena.PathOutcome.afterHistory
#check Arena.WinningCondition
#check Arena.WinningCondition.afterHistory
#check Arena.WinningConditionFrom.PrefixDecision
#check Arena.CompletePlayAgreementCylinderFrom
#check Arena.Set.IsPrefixOpenOn
#check Arena.CompletePlayFromHistory.prefixMeasurableSpace
#check ExtensiveGame.terminalPayoffOutcome
#check ExtensiveGame.ObservedGame.HasEventClockSignalPerfectRecall
#check ExtensiveGame.ObservedGame.HasEventClockPublicPerfectRecall
#check ExtensiveGame.ObservedGame.HasPathwiseWinningStrategy
#check ExtensiveGame.ObservedGame.HasStrategicWinningStrategy
#check ExtensiveGame.ObservedGame.QuasiStrategy
#check ExtensiveGame.ObservedGame.HasWinningQuasiStrategy

/--
error: Unknown constant `Arena.PathOutcomeFromHistory.continueAt`
-/
#guard_msgs in
#check Arena.PathOutcomeFromHistory.continueAt

/--
error: Unknown constant `Arena.WinningConditionFrom.continueAt`
-/
#guard_msgs in
#check Arena.WinningConditionFrom.continueAt

/--
error: Unknown constant `Arena.WinningConditionFrom.mem_continueAt_iff`
-/
#guard_msgs in
#check Arena.WinningConditionFrom.mem_continueAt_iff

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

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena
