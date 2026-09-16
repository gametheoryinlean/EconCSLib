/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Restart

/-!
# Restart/compilation import boundary

Fresh-restart compatibility extends equilibrium independently of the compiler
branch. Reference compilers and FOSG serialization remain opt-in through
`Interface.Compilation.Discrete`.
-/

#check
  ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt

/--
error: Unknown identifier `GameTree.Kuhn_exists_occurrencePureSPE`
-/
#guard_msgs in
#check GameTree.Kuhn_exists_occurrencePureSPE
