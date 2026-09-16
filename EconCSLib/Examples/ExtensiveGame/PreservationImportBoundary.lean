/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Preservation

/-!
# Preservation facade import boundary

The recommended preservation facade resolves every advertised relation
strength without placing measure-valued law vocabulary in the discrete
relations facade.
-/

#check ExtensiveGame.Preservation.StructuralHom
#check ExtensiveGame.Preservation.StrictIso
#check ExtensiveGame.Preservation.InformationRefinement
#check ExtensiveGame.Preservation.WeakSimulation
#check ExtensiveGame.Preservation.CompleteHistoryLawRealization
#check ExtensiveGame.Preservation.CompletePathLawRealization
#check ExtensiveGame.Preservation.PathLawCoupling
#check ExtensiveGame.Preservation.StrictCompilerPreservation
#check ExtensiveGame.Preservation.WeakCompilerPreservation

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena

/--
error: Unknown constant `ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.Iso.isPureNashOnRootsAtFuel_iff
