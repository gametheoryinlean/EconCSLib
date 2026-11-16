/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Relations.Discrete

/-!
# Discrete relation import boundary

Strict structural relations, information refinements, PMF trajectory
couplings, and weak simulations do not require infinite path measures or
non-atomic kernels.
-/

#check Arena.WeakSimulation
#check ExtensiveGame.Arena.Iso.map_stochasticHistoryLawFrom
#check ExtensiveGame.ObservedGame.InformationRefinement
#check KernelArena.Simulation.PolicyMatch

/--
error: Unknown constant `ExtensiveGame.Preservation.StrictIso`
-/
#guard_msgs in
#check ExtensiveGame.Preservation.StrictIso

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
