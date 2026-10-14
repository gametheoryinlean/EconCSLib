/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Factorization

/-!
# Time-indexed information rebasing for measurable-kernel restarts

This regression uses a one-state, two-action measurable-kernel arena and an
event-information family whose type at time `time` is `Fin (time + 1)`.
Hence the fresh and absolute information types genuinely vary with the
clock.

A measurable rebase sends any absolute clock tag to the target fresh tag. A
stationary information policy is natural along that rebase and therefore
compiles to a root-uniform restart-compatible raw policy. A second policy
selects different Boolean actions at time zero and positive times; it uses
the same valid rebase but fails both kernel naturality and compiled restart
compatibility.

The example separates existence of a measurable information transport from
behavioral naturality along that transport.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.MeasurableKernelRestartInformationRebaseBoundary

open MeasurableKernelArena

/-- One nonterminal state with two Boolean actions and a deterministic
self-loop. -/
def discreteArena : KernelArena where
  State := Unit
  Action := fun _ => Bool
  next := fun _ _ => FiniteLaw.pure ()

/-- Analytic top-measurable embedding of the one-state arena. -/
noncomputable abbrev arena : MeasurableKernelArena :=
  discreteArena.toMeasurable

/-- Bundle a Boolean action at the unique state. -/
def actionBundle (action : Bool) :
    arena.ActionBundle :=
  ⟨(), action⟩

local instance actionBundleMeasurableSingletonClass :
    MeasurableSingletonClass arena.ActionBundle where
  measurableSet_singleton := by
    intro _
    exact MeasurableSpace.measurableSet_top

local instance stateMeasurableSingletonClass :
    MeasurableSingletonClass arena.State where
  measurableSet_singleton := by
    intro _
    exact MeasurableSpace.measurableSet_top

/-- A genuinely time-indexed information family. At time `time`, its value
type has exactly `time + 1` elements, and every concrete prefix receives the
last clock tag. -/
def clockInformation :
    arena.EventInformation where
  Information := fun time => Fin (time + 1)
  informationMeasurable := fun _ => ⊤
  informationAt := fun time _ => Fin.last time
  informationAt_measurable := fun _ =>
    measurable_const

/-- Rebase any absolute clock tag to the distinguished tag of the target
fresh time. This map is measurable but neither injectivity nor invertibility
is required. -/
def clockRebase :
    EventInformation.FreshRestartRebase
      clockInformation where
  rebase := fun _ _ offset _ =>
    Fin.last offset
  rebase_measurable := by
    intro start initialPrefix offset
    exact measurable_const
  rebase_informationAt_splice := by
    intro start initialPrefix offset freshPrefix hrooted
    rfl

/-- A stationary information policy choosing `false` at every clock tag. -/
noncomputable def stationaryInformationPolicy :
    EventInformation.ActionPolicy
      clockInformation := by
  classical
  exact
    { kernel := fun _ =>
        Kernel.deterministic
          (fun _ => actionBundle false)
          measurable_const
      terminal_zero := by
        intro time finitePrefix hterminal
        exact (hterminal.false false).elim
      nonterminal_isProbability := by
        intro time finitePrefix hnonterminal
        rw [Kernel.deterministic_apply]
        infer_instance
      legal := by
        intro time finitePrefix hnonterminal
        rw [Kernel.deterministic_apply]
        apply
          (ae_dirac_iff
            (arena.measurableSet_actionFiber _)).2
        rfl }

/-- The stationary policy is natural along the time-indexed clock rebase. -/
theorem stationaryInformationPolicy_isFreshRestartRebaseNatural :
    EventInformation.ActionPolicy.IsFreshRestartRebaseNatural
      stationaryInformationPolicy clockRebase := by
  intro start initialPrefix offset informationValue
  simp [
    stationaryInformationPolicy,
    clockRebase,
    Kernel.deterministic_apply]

/-- Consequently, compilation of the stationary time-indexed information
policy is root-uniform restart compatible. -/
theorem stationaryCompiledPolicy_freshRestartRootedActionKernelCompatible :
    EventHistoryActionPolicy.IsFreshRestartRootedActionKernelCompatible
      stationaryInformationPolicy.toEventHistoryActionPolicy :=
  EventInformation.ActionPolicy.IsFreshRestartRebaseNatural.compiledPolicy_freshRestartRootedActionKernelCompatible
    stationaryInformationPolicy_isFreshRestartRebaseNatural

/-- Boolean action selected by the strict time-indexed information policy:
`false` at fresh time zero and `true` at every positive time. -/
def selectedAction (time : ℕ) :
    Bool :=
  decide (0 < time)

/-- A valid information policy whose action kernel depends on the absolute
clock rather than on its information value. -/
noncomputable def timeSensitiveInformationPolicy :
    EventInformation.ActionPolicy
      clockInformation := by
  classical
  exact
    { kernel := fun time =>
        Kernel.deterministic
          (fun _ => actionBundle (selectedAction time))
          measurable_const
      terminal_zero := by
        intro time finitePrefix hterminal
        exact (hterminal.false false).elim
      nonterminal_isProbability := by
        intro time finitePrefix hnonterminal
        rw [Kernel.deterministic_apply]
        infer_instance
      legal := by
        intro time finitePrefix hnonterminal
        rw [Kernel.deterministic_apply]
        apply
          (ae_dirac_iff
            (arena.measurableSet_actionFiber _)).2
        rfl }

/-- The selected action bundles at positive and zero time are distinct. -/
theorem actionBundle_true_ne_false :
    actionBundle true ≠ actionBundle false := by
  intro hequal
  have haction :=
    Sigma.mk.inj_iff.mp hequal
  exact
    Bool.false_ne_true
      (eq_of_heq haction.2).symm

/-- An arbitrary retained prefix through absolute time one. -/
def retainedPrefix :
    arena.ContinuationPrefix 1 :=
  fun _ => ((), Sum.inl ())

/-- The canonical fresh prefix at the unique state. -/
def freshPrefix :
    arena.ContinuationPrefix 0 :=
  fun _ => ((), Sum.inl ())

/-- The fresh prefix is canonically rooted at the retained latest state. -/
theorem freshPrefix_rooted :
    IsInitialEventRootedPrefix
      (latestEventState 1 retainedPrefix)
      0 freshPrefix := by
  change
    IsInitialEventRootedPrefix () 0 freshPrefix
  unfold IsInitialEventRootedPrefix
  funext time
  have htime : time.1 = 0 :=
    Nat.eq_zero_of_le_zero
      (Finset.mem_Iic.mp time.2)
  simp [
    setInitialPrefix,
    initialEvent,
    freshPrefix,
    htime]

/-- The measurable clock rebase does not by itself make the strict
time-sensitive information policy natural. -/
theorem timeSensitiveInformationPolicy_not_freshRestartRebaseNatural :
    ¬ EventInformation.ActionPolicy.IsFreshRestartRebaseNatural
        timeSensitiveInformationPolicy clockRebase := by
  intro hnatural
  have htime :=
    hnatural
      1 retainedPrefix 0 (Fin.last 1)
  apply
    (dirac_ne_dirac actionBundle_true_ne_false)
  simpa [
    timeSensitiveInformationPolicy,
    selectedAction,
    clockRebase,
    Kernel.deterministic_apply] using htime

/-- The compiled strict time-indexed policy also fails root-uniform
behavioral restart compatibility at the retained time-one prefix. -/
theorem timeSensitiveCompiledPolicy_not_freshRestartRootedActionKernelCompatible :
    ¬ EventHistoryActionPolicy.IsFreshRestartRootedActionKernelCompatible
        timeSensitiveInformationPolicy.toEventHistoryActionPolicy := by
  intro hcompatible
  have htime :=
    hcompatible
      1 retainedPrefix 0 freshPrefix
      freshPrefix_rooted
  apply
    (dirac_ne_dirac actionBundle_true_ne_false)
  simpa [
    EventInformation.ActionPolicy.toEventHistoryActionPolicy_kernel_apply,
    timeSensitiveInformationPolicy,
    selectedAction,
    clockInformation,
    Kernel.deterministic_apply] using htime

end Examples.MeasurableKernelRestartInformationRebaseBoundary
