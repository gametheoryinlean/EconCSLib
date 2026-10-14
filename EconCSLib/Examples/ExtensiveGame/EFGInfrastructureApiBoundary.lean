/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Restart
import EconCSLib.GameTheory.GameForm.LimitSPE

/-!
# EFG infrastructure API boundary

This compilation guard fixes three infrastructure decisions:

* declared or designated roots are not named standard subgame roots;
* equilibrium on a supplied root system is named `SubgamePerfectOn`, while
  complete coverage is named `StandardSubgamePerfect`;
* certificate-specific restart equilibrium routes are private, and consumers
  use the canonical state-compatibility transfer.

It also checks that the full discrete-to-analytic infinite-path law bridge is
available from the analytic/restart tier.
-/

#check Arena.pathLaw_eq_historyKernelArena_toMeasurable_pathMeasure

#check
  ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility.isNashAt_iff_isNashAtContinuation_of_compatible

#check
  ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility.isFreshRestartStandardSubgamePerfect_iff_isStandardSubgamePerfect_of_compatible

/--
error: Unknown constant `ContinuationGameForm.IsSubgameRoot`
-/
#guard_msgs in
#check ContinuationGameForm.IsSubgameRoot

/--
error: Unknown constant `IndexedContinuationGameForm.IsSPEForPayoff`
-/
#guard_msgs in
#check IndexedContinuationGameForm.IsSPEForPayoff

/--
error: Unknown constant `ExtensiveGame.ObservedGame.IsSubgameRoot`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.IsSubgameRoot

/--
error: Unknown constant `ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility.isNashAt_iff_isNashAtContinuation_of_partialStepCompatible`
-/
#guard_msgs in
#check
  ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility.isNashAt_iff_isNashAtContinuation_of_partialStepCompatible
