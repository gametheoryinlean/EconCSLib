/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Execution

/-!
# Nonmeasurable action-fiber legality boundary

This is the strict regression for a formerly unsound legality certificate.
Both the Boolean state space and the dependent action bundle carry the bottom
measurable space.  A constant Dirac kernel always selects the bundle based at
`true`.  At input `false`, the nonempty but nonmeasurable `false` fiber has
outer measure one, even though the selected bundle is almost surely outside
that fiber.

Consequently, the legacy numerical equation

```lean
kernel state (actionFiber state) = 1
```

does not express almost-sure legality without a measurability premise.  The
current `ActionPolicy.legal` field states the genuine a.e. property directly
and therefore rejects this kernel without imposing measurable singletons on
the arena.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.NonmeasurableFiberLegalityBoundary

open MeasurableKernelArena

/-- Bottom measurable spaces make every nontrivial Boolean singleton
nonmeasurable. -/
noncomputable def arena : MeasurableKernelArena where
  State := Bool
  Action := fun _ => Unit
  stateMeasurable := ⊥
  actionBundleMeasurable := ⊥
  stateProjection_measurable := by
    intro set hset
    rw [MeasurableSpace.measurableSet_bot_iff] at hset ⊢
    rcases hset with rfl | rfl
    · exact Or.inl Set.preimage_empty
    · exact Or.inr Set.preimage_univ
  transition :=
    @Kernel.const
      (Σ _state : Bool, Unit) Bool
      ⊥ ⊥
      (@Measure.dirac Bool ⊥ false)
  transition_isMarkov := by
    exact Kernel.const.instIsMarkovKernel

/-- The bundle that is actually selected by the bad raw kernel. -/
def illegalBundle : arena.ActionBundle :=
  ⟨true, ()⟩

/-- A constant raw kernel which selects a `true`-based bundle even at input
`false`. -/
noncomputable def badKernel :
    Kernel arena.State arena.ActionBundle :=
  Kernel.const arena.State (Measure.dirac illegalBundle)

@[simp]
theorem badKernel_apply (state : arena.State) :
    badKernel state = Measure.dirac illegalBundle :=
  Kernel.const_apply _ _

/-- The `false` action fiber is nonempty, despite being nonmeasurable. -/
theorem falseFiber_nonempty :
    (arena.actionFiber false).Nonempty := by
  exact ⟨⟨false, ()⟩, rfl⟩

/-- In the bottom measurable space, the measurable hull of the nonempty
`false` fiber is the whole action-bundle space. -/
theorem toMeasurable_falseFiber_eq_univ :
    toMeasurable (Measure.dirac illegalBundle)
        (arena.actionFiber false) =
      Set.univ := by
  have hmeasurable :
      MeasurableSet
        (toMeasurable (Measure.dirac illegalBundle)
          (arena.actionFiber false)) :=
    measurableSet_toMeasurable _ _
  change
    @MeasurableSet arena.ActionBundle ⊥
      (toMeasurable (Measure.dirac illegalBundle)
        (arena.actionFiber false)) at hmeasurable
  rw [MeasurableSpace.measurableSet_bot_iff] at hmeasurable
  rcases hmeasurable with hempty | huniv
  · obtain ⟨bundle, hbundle⟩ := falseFiber_nonempty
    have hinHull :
        bundle ∈
          toMeasurable (Measure.dirac illegalBundle)
            (arena.actionFiber false) :=
      subset_toMeasurable _ _ hbundle
    rw [hempty] at hinHull
    exact hinHull.elim
  · exact huniv

/-- The legacy numerical condition falsely reports full mass on the
`false`-based action fiber. -/
theorem old_mass_one_at_false :
    badKernel false (arena.actionFiber false) = 1 := by
  rw [badKernel_apply]
  calc
    Measure.dirac illegalBundle (arena.actionFiber false) =
        Measure.dirac illegalBundle
          (toMeasurable (Measure.dirac illegalBundle)
            (arena.actionFiber false)) :=
      (measure_toMeasurable (arena.actionFiber false)).symm
    _ = Measure.dirac illegalBundle Set.univ := by
      rw [toMeasurable_falseFiber_eq_univ]
    _ = 1 := measure_univ

/-- The actual selected bundle is not based at `false`. -/
theorem illegalBundle_not_mem_falseFiber :
    illegalBundle ∉ arena.actionFiber false := by
  simp [illegalBundle, MeasurableKernelArena.actionFiber]

/-- The `false` action fiber is genuinely nonmeasurable in the chosen bottom
measurable space. -/
theorem falseFiber_not_measurable :
    ¬ MeasurableSet (arena.actionFiber false) := by
  intro hmeasurable
  change
    @MeasurableSet arena.ActionBundle ⊥
      (arena.actionFiber false) at hmeasurable
  rw [MeasurableSpace.measurableSet_bot_iff] at hmeasurable
  rcases hmeasurable with hempty | huniv
  · obtain ⟨bundle, hbundle⟩ := falseFiber_nonempty
    rw [hempty] at hbundle
    exact hbundle.elim
  · exact illegalBundle_not_mem_falseFiber (by simp [huniv])

/-- Despite the numerical outer-measure equation, the selected bundle is not
almost surely in the `false` action fiber. -/
theorem not_ae_mem_falseFiber :
    ¬ ∀ᵐ stateAction ∂badKernel false,
        stateAction ∈ arena.actionFiber false := by
  intro hae
  rw [badKernel_apply] at hae
  have hzero :
      Measure.dirac illegalBundle
          (arena.actionFiber false)ᶜ =
        0 := by
    exact mem_ae_iff.mp hae
  have hone :
      Measure.dirac illegalBundle
          (arena.actionFiber false)ᶜ =
        1 :=
    Measure.dirac_apply_of_mem illegalBundle_not_mem_falseFiber
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- No current action policy can hide the bad raw kernel behind the legacy
outer-measure equation. -/
theorem no_actionPolicy_with_badKernel :
    ¬ ∃ policy : arena.ActionPolicy,
        policy.kernel = badKernel := by
  rintro ⟨policy, hkernel⟩
  have hlegal :=
    policy.legal false
      (by
        intro hempty
        exact hempty.false ())
  rw [hkernel] at hlegal
  exact not_ae_mem_falseFiber hlegal

end Examples.NonmeasurableFiberLegalityBoundary
