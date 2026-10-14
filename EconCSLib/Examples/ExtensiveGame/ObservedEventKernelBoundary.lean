/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.ObservedEvent
import EconCSLib.Examples.ExtensiveGame.EventHistoryKernelBoundary

/-!
# Measurable event-information strictness boundary

This regression equips the one-state/two-looping-action arena from
`EventHistoryKernelBoundary` with a blind information structure. The blind
statistic maps every event prefix at a fixed time to `Unit`, whereas full
event information distinguishes prefixes that record different actions.

Every policy on the blind information structure must choose exactly the same
action measure at the two witness prefixes. The action-repeating raw event
policy chooses distinct Dirac laws, so it has no blind-information
representation. Conversely, a concrete blind policy pulls back to full
information with exactly the same compiled executor and whole event-path law.

This is an information-partition regression. It does not add player movers,
bridge `ObservedGame`, or claim anything about reachability, recall, payoffs,
or equilibrium.
-/

open MeasureTheory ProbabilityTheory

namespace EconCSLib.Examples.ExtensiveGame.ObservedEventKernelBoundary

open EventHistoryKernelBoundary

/-- The information statistic that sees nothing beyond event time. -/
def blindInformation :
    MeasurableKernelArena.EventInformation eventArena where
  Information := fun _ => Unit
  informationMeasurable := fun _ => ⊤
  informationAt := fun _ _ => ()
  informationAt_measurable := fun _ => measurable_const

/-- Full event information measurably refines the blind statistic. -/
def fullToBlind :
    MeasurableKernelArena.EventInformation.Hom
      (MeasurableKernelArena.EventInformation.full eventArena)
      blindInformation where
  map := fun _ _ => ()
  map_measurable := fun _ => measurable_const
  map_informationAt := by
    intro time history
    rfl

/-- The blind statistic identifies the two action-distinct witnesses. -/
@[simp]
theorem blindInformation_witness_eq :
    blindInformation.informationAt 1 falseActionPrefix =
      blindInformation.informationAt 1 trueActionPrefix :=
  rfl

/-- Full event information distinguishes the same two witnesses. -/
theorem fullInformation_witness_ne :
    (MeasurableKernelArena.EventInformation.full eventArena).informationAt
        1 falseActionPrefix ≠
      (MeasurableKernelArena.EventInformation.full eventArena).informationAt
        1 trueActionPrefix := by
  intro hprefix
  apply latestAction_witness_ne
  rw [show falseActionPrefix = trueActionPrefix from hprefix]

/-- The arena has no terminal state, so its terminal set is measurable. -/
theorem eventArena_measurableSet_terminalSet :
    MeasurableSet eventArena.terminalSet := by
  change
    @MeasurableSet eventArena.State ⊤
      eventArena.terminalSet
  exact MeasurableSpace.measurableSet_top

/-- A blind policy that always selects `false`. -/
noncomputable def blindFalsePolicy :
    MeasurableKernelArena.EventInformation.ActionPolicy
      blindInformation where
  kernel := fun _ =>
    Kernel.deterministic
      (fun _ =>
        (⟨(), false⟩ : eventArena.ActionBundle))
      measurable_const
  terminal_zero := by
    intro time history hterminal
    exact (hterminal.false false).elim
  nonterminal_isProbability := by
    intro time history hnonterminal
    infer_instance
  legal := by
    intro time history hnonterminal
    rw [Kernel.deterministic_apply]
    have hstate :
        () = MeasurableKernelArena.latestEventState time history :=
      Subsingleton.elim _ _
    have hfiber :
        MeasurableSet
          (eventArena.actionFiber
            (MeasurableKernelArena.latestEventState time history)) :=
      eventArena.measurableSet_actionFiber _
    apply (ae_dirac_iff hfiber).2
    simp [hstate]

/-- Pulling the concrete blind policy back to full information does not alter
its compiled raw event policy. -/
theorem blindFalsePolicy_pullback_compiles_exactly :
    MeasurableKernelArena.EventInformation.ActionPolicy.toEventHistoryActionPolicy
        (blindFalsePolicy.pullback fullToBlind) =
      blindFalsePolicy.toEventHistoryActionPolicy :=
  MeasurableKernelArena.EventInformation.ActionPolicy.pullback_toEventHistoryActionPolicy
    blindFalsePolicy fullToBlind

/-- Pulling the concrete blind policy back to full information preserves its
complete infinite event-path law. -/
theorem blindFalsePolicy_pullback_pathMeasure
    (initialState : eventArena.State) :
    (MeasurableKernelArena.EventInformation.ActionPolicy.toEventHistoryActionPolicy
        (blindFalsePolicy.pullback fullToBlind)).pathMeasure
          eventArena_measurableSet_terminalSet initialState =
      blindFalsePolicy.toEventHistoryActionPolicy.pathMeasure
        eventArena_measurableSet_terminalSet initialState :=
  MeasurableKernelArena.EventInformation.ActionPolicy.pullback_pathMeasure
    blindFalsePolicy fullToBlind
    eventArena_measurableSet_terminalSet initialState

/-- The action-repeating raw event policy is exactly representable under full
event information. -/
theorem eventPolicy_fullInformation_roundtrip :
    MeasurableKernelArena.EventInformation.ActionPolicy.toEventHistoryActionPolicy
        eventPolicy.toFullInformationActionPolicy =
      eventPolicy :=
  MeasurableKernelArena.EventHistoryActionPolicy.toFullInformationActionPolicy_toEventHistoryActionPolicy
    eventPolicy

/-- No policy indexed by the blind statistic agrees with the action-repeating
raw event policy. Blind information merges the witnesses, while the raw policy
assigns different Dirac action measures. -/
theorem no_blind_information_representation :
    ¬ ∃ policy :
        MeasurableKernelArena.EventInformation.ActionPolicy
          blindInformation,
      policy.toEventHistoryActionPolicy = eventPolicy := by
  rintro ⟨policy, hcompile⟩
  have hblind :
      policy.toEventHistoryActionPolicy.kernel
          1 falseActionPrefix =
        policy.toEventHistoryActionPolicy.kernel
          1 trueActionPrefix :=
    policy.compiled_kernel_eq_of_informationAt_eq
      1 falseActionPrefix trueActionPrefix
      blindInformation_witness_eq
  have hfalse := congrArg
    (fun compiled : eventArena.EventHistoryActionPolicy =>
      compiled.kernel 1 falseActionPrefix)
    hcompile
  have htrue := congrArg
    (fun compiled : eventArena.EventHistoryActionPolicy =>
      compiled.kernel 1 trueActionPrefix)
    hcompile
  change
    policy.toEventHistoryActionPolicy.kernel
        1 falseActionPrefix =
      eventPolicy.kernel 1 falseActionPrefix
    at hfalse
  change
    policy.toEventHistoryActionPolicy.kernel
        1 trueActionPrefix =
      eventPolicy.kernel 1 trueActionPrefix
    at htrue
  have hdirac :
      Measure.dirac
          (⟨(), false⟩ : eventArena.ActionBundle) =
        Measure.dirac
          (⟨(), true⟩ : eventArena.ActionBundle) := by
    rw [eventPolicy_kernel_apply] at hfalse htrue
    simpa using hfalse.symm.trans (hblind.trans htrue)
  have hsingleton :
      MeasurableSet
        ({(⟨(), false⟩ : eventArena.ActionBundle)} :
          Set eventArena.ActionBundle) := by
    change
      @MeasurableSet eventArena.ActionBundle ⊤
        {(⟨(), false⟩ : eventArena.ActionBundle)}
    exact MeasurableSpace.measurableSet_top
  have happly := congrArg
    (fun measure : Measure eventArena.ActionBundle =>
      measure {(⟨(), false⟩ : eventArena.ActionBundle)})
    hdirac
  change
    Measure.dirac
        (⟨(), false⟩ : eventArena.ActionBundle)
        {(⟨(), false⟩ : eventArena.ActionBundle)} =
      Measure.dirac
        (⟨(), true⟩ : eventArena.ActionBundle)
        {(⟨(), false⟩ : eventArena.ActionBundle)}
    at happly
  rw [Measure.dirac_apply' _ hsingleton,
    Measure.dirac_apply' _ hsingleton] at happly
  simp at happly

end EconCSLib.Examples.ExtensiveGame.ObservedEventKernelBoundary
