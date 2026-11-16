/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Infrastructure
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Morphism
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.DiscreteLaw
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.DiscretePath
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Analytic
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Semantics
import EconCSLib.GameTheory.ExtensiveGame.Observed.Semantics

/-!
# Controlled API import boundaries

The two canonical aggregate facades re-export declarations from their
responsibility leaves while remaining declaration-free. The controlled
payoff-free families and state-payoff adapters elaborate together under
disjoint namespaces.
-/

#check ExtensiveGame.ControlledObservedGame
#check ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses
#check ExtensiveGame.ControlledObservedGame.RecallCertificate
#check ExtensiveGame.ControlledObservedGame.PureStrategyAvailabilityCertificate
#check ExtensiveGame.ControlledObservedGame.ReachablePureStrategyModelCertificate
#check ExtensiveGame.ControlledObservedGame.SignalTraceBuilder
#check ExtensiveGame.ControlledObservedGame.HasEventClockSignalPerfectRecall
#check ExtensiveGame.ControlledObservedGame.SubgameSystem
#check ExtensiveGame.ControlledObservedGame.Iso
#check ExtensiveGame.ControlledObservedGame.Iso.mapSubgameSystem
#check ExtensiveGame.ControlledObservedGame.Iso.perfectRecall_iff
#check ExtensiveGame.ControlledObservedGame.ContinuationSemantics
#check ExtensiveGame.ControlledObservedGame.ContinuationSemantics.IsEvaluatorContinuationEquilibriumAt
#check ExtensiveGame.ControlledObservedGame.CompletePathLawSemantics
#check ExtensiveGame.ControlledObservedGame.CompletePathLawSemantics.HistoryTransformLawEquivalentAt
#check ExtensiveGame.ControlledObservedGame.CompletePathLawSemantics.TerminalHistoryLawEquivalentAt
#check ExtensiveGame.DiscreteControlledObservedChanceGame
#check ExtensiveGame.ObservedGame.ContinuationSemantics
#check ExtensiveGame.ObservedGame.PayoffCompatibleIso
#check ExtensiveGame.ObservedGame.pureStrategy_toControlled
#check ExtensiveGame.ObservedChanceGame.toDiscreteControlledObservedChanceGame
#check ExtensiveGame.ObservedChanceGame.ofDiscreteControlledObservedChanceGame
#check
  ExtensiveGame.ObservedChanceGame.ofDiscreteControlledObservedChanceGame_toControlled
#check
  ExtensiveGame.ObservedChanceGame.ofDiscreteControlledObservedChanceGame_toControlled_payoff

namespace ExtensiveGame.ControlledApiImportBoundary

universe uN uU uA uS uO uI uP

/-- The payoff-aware projection preserves independent action and state
universes: the result uses `uA` for both base and information actions, and
retains `uS` for the base state. -/
example {N : Type uN} {U : Type uU}
    (G : ObservedGame.{uN, uU, uA, uS, uO, uI, uP} N U) :
    ControlledObservedGame.{uN, uA, uS, uO, uI, uP} N :=
  G.toControlledObservedGame

end ExtensiveGame.ControlledApiImportBoundary
