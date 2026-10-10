/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall

/-!
# Recall import boundary

The payoff-free recall leaf exposes general represented-decision witnesses and
recall certificates without importing finite-EFG or structural history-length
infrastructure.
-/

#check ExtensiveGame.ControlledObservedGame.DecisionInfoWitness
#check ExtensiveGame.ControlledObservedGame.RecallCertificate
#check ExtensiveGame.ControlledObservedGame.SignalRecallCertificate
#check ExtensiveGame.ControlledObservedGame.PublicRecallCertificate
#check ExtensiveGame.ControlledObservedGame.SignalTraceBuilder
#check ExtensiveGame.ControlledObservedGame.SignalTraceBuilder.HasPerfectRecall
#check ExtensiveGame.ControlledObservedGame.HasEventClockSignalPerfectRecall
#check ExtensiveGame.ControlledObservedGame.HasEventClockPublicPerfectRecall
#check ExtensiveGame.ControlledObservedGame.eventClockSignalTraceBuilder

/--
error: Unknown constant `ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses`
-/
#guard_msgs in
#check ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses

/--
error: Unknown constant `Arena.HasLengthBoundFrom`
-/
#guard_msgs in
#check Arena.HasLengthBoundFrom
