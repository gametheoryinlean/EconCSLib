/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite

/-!
# Infinite discrete execution import boundary

Infinite finite-law-driven paths intentionally introduce supplied probability
measures while remaining independent of both kernel construction and the
non-atomic `MeasurableKernelArena` stack.
-/

#check Arena.stochasticHistoryLawFrom
#check Arena.pathMarginal
#check Arena.pathLaw
#check MeasureTheory.ProbabilityMeasure

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena
