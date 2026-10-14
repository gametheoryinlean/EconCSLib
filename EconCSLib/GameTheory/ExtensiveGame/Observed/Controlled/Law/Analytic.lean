/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.Core

/-!
# Analytic-kernel adapter to controlled complete-path semantics

This downstream adapter packages the actual state/history-path law generated
by `MeasurableKernelPresentation` in the same payoff-free
`CompletePathLawSemantics` used by supplied discrete path execution. Player strategy
carriers and their measurable profile assembly are supplied explicitly.

The analytic executor already proves normalization.  Canonical
`Arena.IsCompletePlayPathFrom` support is an explicit adapter premise because
the general measurable-kernel executor also supports stochastic state arenas
whose paths are not deterministic `Arena.next` histories.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedGame.MeasurableKernelPresentation

universe uN uU uStrategy

variable {N : Type uN} {U : Type uU}
  {G : ObservedGame N U}
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}

local instance modelHistoryMeasurable :
    MeasurableSpace G.toControlledObservedGame.base.History :=
  model.historyMeasurable

/-- Package an assembled analytic behavioral model as the common lawful
complete-history probability semantics. -/
noncomputable def kernelBehavioralCompletePathLawSemantics
    (Strategy : N → Type uStrategy)
    (assemble :
      (∀ i, Strategy i) →
        presentation.KernelBehavioralProfile)
    (lawful :
      ∀ (profile : ∀ i, Strategy i)
        (current : G.toControlledObservedGame.base.History),
        ∀ᵐ path ∂(assemble profile).statePathMeasure current,
          G.toControlledObservedGame.base.toArena.IsCompletePlayPathFrom
            current path) :
    @ControlledObservedGame.CompletePathLawSemantics
      N G.toControlledObservedGame model.historyMeasurable := by
  letI : MeasurableSpace
      G.toControlledObservedGame.base.History :=
    model.historyMeasurable
  exact
    { Strategy := Strategy
      pathLaw := fun profile current =>
        (assemble profile).statePathMeasure current
      pathLaw_isProbability := by
        intro profile current
        unfold KernelBehavioralProfile.statePathMeasure
        exact
          MeasurableKernelArena.EventHistoryActionPolicy.statePathMeasure_isProbability
            _ _ _
      pathLaw_ae_legal := lawful
      boundedCompleteHistoryLaw := fun profile current time =>
        ((assemble profile).statePathMeasure current).map
          (fun path => path time)
      boundedCompleteHistoryLaw_eq_map := by
        intro _profile _current _time
        rfl }

/-- The analytic adapter realizes the existing kernel-generated state/history
path law definitionally. -/
theorem kernelBehavioralCompletePathLawSemantics_realizesExecution
    (Strategy : N → Type uStrategy)
    (assemble :
      (∀ i, Strategy i) →
        presentation.KernelBehavioralProfile)
    (lawful :
      ∀ (profile : ∀ i, Strategy i)
        (current : G.toControlledObservedGame.base.History),
        ∀ᵐ path ∂(assemble profile).statePathMeasure current,
          G.toControlledObservedGame.base.toArena.IsCompletePlayPathFrom
            current path) :
    @ControlledObservedGame.CompletePathLawSemantics.RealizesExecution
      N G.toControlledObservedGame model.historyMeasurable
      (kernelBehavioralCompletePathLawSemantics
        Strategy assemble lawful)
      (fun profile current =>
        (assemble profile).statePathMeasure current) := by
  intro _profile _current
  rfl

end ExtensiveGame.ObservedGame.MeasurableKernelPresentation
