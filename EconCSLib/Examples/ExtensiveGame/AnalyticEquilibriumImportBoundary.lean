/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic
import Lean.Elab.Command

/-!
# Analytic equilibrium import boundary

The analytic equilibrium layer reuses the discrete equilibrium surface and
adds measurable-kernel path utility and
continuation semantics, while Restart and Compilation remain independent
branches.
-/

#check ExtensiveGame.ObservedChanceGame.finiteKuhn_isNash_iff
#check ExtensiveGame.ObservedGame.MeasurableHistoryModel.PathUtility
#check ExtensiveGame.ObservedGame.MeasurableHistoryModel.BoundedPathUtility.IsNashOnPresentation

/--
error: Unknown constant `ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt

/--
error: Unknown identifier `GameTree.Kuhn_exists_occurrencePureSPE`
-/
#guard_msgs in
#check GameTree.Kuhn_exists_occurrencePureSPE

/-! Conditional laws require an explicit positive-mass witness. -/

open MeasureTheory
open ExtensiveGame.ObservedGame

example {G : ExtensiveGame.ObservedGame Unit ℝ}
    {model : MeasurableHistoryModel G}
    {presentation : MeasurableKernelPresentation G model}
    (profile : presentation.KernelBehavioralProfile)
    [MeasurableKernelPresentation.KernelBehavioralProfile.ConditionalContinuation profile]
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    (initialHistory root : CompleteHistory G)
    (hpositive : profile.canonicalContinuationPrefixMass initialHistory root ≠ 0) :
    Measure (ℕ → model.toArena.PathEvent) := by
  fail_if_success exact profile.conditionalContinuationEventPathMeasure initialHistory root
  exact profile.conditionalContinuationEventPathMeasure initialHistory root hpositive

/-! Deferred prototype declarations must not enter the shipped analytic facade. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[
      `ExtensiveGame.ObservedGame.ArbitraryMeasurePureProfileLaw,
      `ExtensiveGame.ObservedChanceGame.SequentialDecisionEvaluator] do
    if env.contains name then
      throwError "Deferred EFG prototype leaked into the release: {name}"
