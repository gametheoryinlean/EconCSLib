/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic

/-!
# Analytic/relations and equilibrium import boundary

The analytic execution facade includes measurable-kernel execution and
presentation assembly. Equilibrium transfer and fresh-restart compatibility
remain opt-in.
-/

#check MeasurableKernelArena
#check ExtensiveGame.ObservedGame.MeasurableHistoryModel.discrete

namespace CompleteInformationMeasurableInstanceBoundary

open ExtensiveGame

variable {N U : Type*} (base : ExtensiveGame N U) (i : N)

abbrev observed :=
  ObservedGame.completeInformation base

/-- A caller-selected measurable space on complete histories is inherited by
the generated observation and information carriers. -/
example [MeasurableSpace (base.toArena.HistoryFrom base.init)] :
    MeasurableSpace ((observed base).InfoState i) :=
  inferInstance

end CompleteInformationMeasurableInstanceBoundary

/--
error: Unknown constant `ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff

/--
error: Unknown constant `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt
