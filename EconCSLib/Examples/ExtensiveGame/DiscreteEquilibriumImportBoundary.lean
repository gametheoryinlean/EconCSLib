/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete

/-!
# Discrete equilibrium import boundary

Finite-fuel pure, behavioral, mixed, and Kuhn equilibrium semantics remain
available without the measure-valued execution and path-utility layers.
-/

#check ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff
#check ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff
#check ExtensiveGame.ObservedChanceGame.finiteKuhn_isNash_iff
#check ExtensiveGame.ObservedChanceGame.finiteLawMixedToBehavioral_boundedHistoryLaw
#check ExtensiveGame.ObservedChanceGame.finiteKuhn_boundedHistoryLaw_specialization
#check ExtensiveGame.ObservedGame.DiscreteGeneralStrategy
#check ExtensiveGame.ObservedGame.DiscreteGeneralProfile.behavioralProfileLaw
#check ExtensiveGame.ObservedChanceGame.BoundedCompleteHistorySemantics
#check ExtensiveGame.ObservedChanceGame.BoundedCompleteHistorySemantics.CompleteHistoryLawRealization
#check ExtensiveGame.ControlledObservedGame.ContinuationSemantics
#check ExtensiveGame.ControlledObservedGame.terminalObjectiveContinuationGameForm
#check ExtensiveGame.ControlledObservedGame.pathObjectiveContinuationGameForm
#check ExtensiveGame.ControlledObservedGame.IsPureTerminalNashOnRoots
#check ExtensiveGame.ControlledObservedGame.IsPureTerminalSubgamePerfectOn
#check ExtensiveGame.ControlledObservedGame.IsPureTerminalStandardSubgamePerfect
#check ExtensiveGame.ControlledObservedGame.IsPurePathStandardSubgamePerfect
#check ExtensiveGame.ControlledObservedGame.Iso.TerminalObjectiveCompatible
#check ExtensiveGame.ControlledObservedGame.Iso.terminalObjective_isNash_iff
#check ExtensiveGame.ControlledObservedGame.InformationRefinement.TerminalObjectiveCompatible
#check ExtensiveGame.ControlledObservedGame.InformationRefinement.terminalObjective_isNash_of_map
#check ExtensiveGame.ControlledObservedGame.ContinuationSemantics.IsEvaluatorContinuationEquilibriumAt
#check ExtensiveGame.ControlledObservedGame.ContinuationSemantics.isEvaluatorContinuationEquilibriumAt_iff_of_surjective
#check ExtensiveGame.ObservedGame.ofControlledObservedGame
#check ExtensiveGame.ObservedGame.relabelPlayers
#check ExtensiveGame.ObservedGame.relabelPureProfileEquiv
#check ExtensiveGame.ObservedGame.ContinuationSemantics
#check ExtensiveGame.ObservedGame.terminalContinuationGameForm_eq_terminalObjective

/--
error: Unknown constant `ExtensiveGame.ObservedGame.ArbitraryMeasurePureProfileLaw`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.ArbitraryMeasurePureProfileLaw

/--
error: Unknown constant `ExtensiveGame.ObservedGame.GeneralStrategy`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.GeneralStrategy

/--
error: Unknown constant `ExtensiveGame.ObservedGame.GeneralProfile`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.GeneralProfile

/--
error: Unknown constant `ExtensiveGame.ObservedGame.BehavioralStrategy.toGeneral`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.BehavioralStrategy.toGeneral

/--
error: Unknown constant `ExtensiveGame.ObservedGame.BehavioralProfile.toGeneral`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.BehavioralProfile.toGeneral

/--
error: Unknown constant `ExtensiveGame.ObservedGame.PureStrategy.toGeneral`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.PureStrategy.toGeneral

/--
error: Unknown constant `ExtensiveGame.ObservedGame.PureProfile.toGeneral`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.PureProfile.toGeneral

/--
error: Unknown constant `ExtensiveGame.ObservedGame.GeneralProfile.behavioralProfileLaw`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.GeneralProfile.behavioralProfileLaw

/--
error: Unknown constant `ExtensiveGame.ObservedGame.GeneralProfile.deviate`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.GeneralProfile.deviate

/--
error: Unknown constant `ExtensiveGame.ObservedGame.GeneralProfile.deviate_same`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.GeneralProfile.deviate_same

/--
error: Unknown constant `ExtensiveGame.ObservedGame.GeneralProfile.deviate_of_ne`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.GeneralProfile.deviate_of_ne

/--
error: Unknown constant `ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff_viaContinuationFamily`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff_viaContinuationFamily

/--
error: Unknown constant `ExtensiveGame.ObservedGame.InformationRefinement.isPureNashOnRootsAtFuel_of_map_viaContinuationSimulation`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedGame.InformationRefinement.isPureNashOnRootsAtFuel_of_map_viaContinuationSimulation

/--
error: Unknown constant `ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff_viaInformationRefinement`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff_viaInformationRefinement

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

/--
error: Unknown identifier `ProbabilityTheory.Kernel`
-/
#guard_msgs in
#check ProbabilityTheory.Kernel

/--
error: Unknown constant `ExtensiveGame.ObservedGame.MeasurableHistoryModel.PathUtility`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.MeasurableHistoryModel.PathUtility
