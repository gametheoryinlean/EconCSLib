/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.ObservedChanceKernelBridgeBoundary
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation

/-!
# Strict abstract-action realization boundary

This regression uses the absent-minded history-state arena from
`ObservedChanceKernelBridgeBoundary`. A terminal-tagged information statistic
identifies the two nonterminal player histories but separates terminal
histories. Hence failure of the old concrete-bundle policy cannot be blamed on
merging terminal and nonterminal prefixes.

The old `EventInformation.ActionPolicy` is still uninhabited: one measure on
concrete action bundles cannot have mass one on the two distinct
complete-history state fibers. The new `RealizedActionPolicy` is inhabited.
Its common abstract action type is `Unit`, its nonterminal abstract law is the
same Dirac law at both histories, and its fixed history-dependent realization
maps that one abstract choice into the appropriate concrete dependent action
fiber.

Thus the example proves strict expressive gain of the realization layer while
retaining exact information consistency at the abstract level.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.RealizedInformationBoundary

open Examples.AbsentMinded
open Examples.ObservedChanceKernelBridgeBoundary
open MeasurableKernelArena

local instance rungMeasurableSpace :
    MeasurableSpace Rung :=
  ⊤

instance liftedActionBundleMeasurableSingleton :
    MeasurableSingletonClass liftedArena.ActionBundle where
  measurableSet_singleton _ := by
    change
      @MeasurableSet liftedArena.ActionBundle ⊤
        ({_} : Set liftedArena.ActionBundle)
    exact MeasurableSpace.measurableSet_top

/-- Tag only terminal versus nonterminal endpoints. Both recurring player
decisions receive `false`; the terminal endpoint receives `true`. -/
def terminalTag : Rung → Bool
  | .s0 => false
  | .s1 => false
  | .s2 => true

theorem measurable_terminalTag :
    @Measurable Rung Bool ⊤ ⊤ terminalTag := by
  exact fun _ _ => MeasurableSpace.measurableSet_top

theorem measurable_historyEndpoint :
    @Measurable liftedArena.State Rung ⊤ ⊤ Sigma.fst := by
  exact fun _ _ => MeasurableSpace.measurableSet_top

/-- A fixed analytic information structure that merges exactly the two
recurring nonterminal decision states relevant to the regression, while
retaining a distinct terminal tag. -/
def terminalTaggedInformation :
    EventInformation liftedArena where
  Information := fun _ => Bool
  informationMeasurable := fun _ => ⊤
  informationAt := fun time history =>
    terminalTag
      (MeasurableKernelArena.latestEventState time history).1
  informationAt_measurable := by
    intro time
    exact measurable_terminalTag.comp
      (measurable_historyEndpoint.comp
        (MeasurableKernelArena.measurable_latestEventState time))

@[simp]
theorem terminalTaggedInformation_firstPrefix :
    terminalTaggedInformation.informationAt 0 firstPrefix = false :=
  rfl

@[simp]
theorem terminalTaggedInformation_secondPrefix :
    terminalTaggedInformation.informationAt 0 secondPrefix = false :=
  rfl

/-- The completed history after the second unique player action. -/
def terminalHistory : liftedArena.State :=
  ⟨Rung.s2, secondDecision.2.snoc ()⟩

/-- A total concrete bundle realization. Its terminal branch is an arbitrary
fallback that is never sampled because terminal abstract laws are zero. -/
def realizeBundle (history : liftedArena.State) :
    liftedArena.ActionBundle :=
  match history with
  | ⟨Rung.s0, path⟩ =>
      ⟨⟨Rung.s0, path⟩, ()⟩
  | ⟨Rung.s1, path⟩ =>
      ⟨⟨Rung.s1, path⟩, ()⟩
  | ⟨Rung.s2, _path⟩ =>
      ⟨firstDecision, ()⟩

theorem measurable_realizeBundle :
    Measurable realizeBundle := by
  change
    @Measurable
      liftedArena.State liftedArena.ActionBundle
      ⊤ ⊤ realizeBundle
  exact fun _ _ => MeasurableSpace.measurableSet_top

/-- At every nonterminal lifted history, the realization bundle is based at
that exact history state. -/
theorem realizeBundle_fst_of_nonterminal
    (history : liftedArena.State)
    (hnonterminal :
      ¬ IsEmpty (liftedArena.Action history)) :
    (realizeBundle history).1 = history := by
  rcases history with ⟨state, path⟩
  cases state with
  | s0 =>
      rfl
  | s1 =>
      rfl
  | s2 =>
      exact
        (hnonterminal
          (show IsEmpty
              (liftedArena.Action
                (⟨Rung.s2, path⟩ : liftedArena.State)) from
            ⟨PEmpty.elim⟩)).elim

/-- The fixed action realization uses one abstract `Unit` action at every time
and realizes it deterministically according to the concrete latest history.
-/
noncomputable def unitRealization :
    EventInformation.ActionRealization
      terminalTaggedInformation where
  AbstractAction := fun _ => Unit
  abstractActionMeasurable := fun _ => ⊤
  kernel := fun time =>
    Kernel.deterministic
      (fun input =>
        realizeBundle
          (MeasurableKernelArena.latestEventState time input.1))
      (measurable_realizeBundle.comp
        ((MeasurableKernelArena.measurable_latestEventState time).comp
          measurable_fst))
  kernel_isSFinite := by
    intro time
    infer_instance

/-- Terminal abstract information value. -/
def terminalInformationSet : Set Bool :=
  {true}

theorem terminalInformationSet_measurable :
    @MeasurableSet Bool ⊤ terminalInformationSet :=
  MeasurableSpace.measurableSet_top

/-- Killed abstract action kernel: zero at the terminal tag and Dirac `Unit`
at the shared nonterminal tag. -/
noncomputable def unitAbstractKernel :
    @Kernel Bool Unit ⊤ ⊤ := by
  classical
  exact
    Kernel.piecewise terminalInformationSet_measurable
      0
      (Kernel.deterministic (fun _ => ()) measurable_const)

instance unitAbstractKernel_isSFinite :
    IsSFiniteKernel unitAbstractKernel := by
  rw [unitAbstractKernel]
  infer_instance

@[simp]
theorem unitAbstractKernel_false :
    unitAbstractKernel false = Measure.dirac () := by
  classical
  rw [unitAbstractKernel, Kernel.piecewise_apply]
  simp [terminalInformationSet]
  exact Kernel.deterministic_apply measurable_const false

@[simp]
theorem unitAbstractKernel_true :
    unitAbstractKernel true = 0 := by
  classical
  rw [unitAbstractKernel, Kernel.piecewise_apply]
  simp [terminalInformationSet]

/-- A terminal lifted history has the terminal information tag. -/
theorem terminalTag_eq_true_of_terminal
    (history : liftedArena.State)
    (hterminal : IsEmpty (liftedArena.Action history)) :
    terminalTag history.1 = true := by
  rcases history with ⟨state, path⟩
  cases state with
  | s0 =>
      exact (hterminal.false ()).elim
  | s1 =>
      exact (hterminal.false ()).elim
  | s2 =>
      rfl

/-- A nonterminal lifted history has the shared nonterminal information tag.
-/
theorem terminalTag_eq_false_of_nonterminal
    (history : liftedArena.State)
    (hnonterminal : ¬ IsEmpty (liftedArena.Action history)) :
    terminalTag history.1 = false := by
  rcases history with ⟨state, path⟩
  cases state with
  | s0 =>
      rfl
  | s1 =>
      rfl
  | s2 =>
      exact
        (hnonterminal
          (show IsEmpty
              (liftedArena.Action
                (⟨Rung.s2, path⟩ : liftedArena.State)) from
            ⟨PEmpty.elim⟩)).elim

@[simp]
theorem unitRealization_kernel_apply
    (time : ℕ) (history : liftedArena.EventPrefix time)
    (abstractAction : unitRealization.AbstractAction time) :
    unitRealization.kernel time (history, abstractAction) =
      Measure.dirac
        (realizeBundle
          (MeasurableKernelArena.latestEventState time history)) := by
  exact Kernel.deterministic_apply
    (measurable_realizeBundle.comp
      ((MeasurableKernelArena.measurable_latestEventState time).comp
        measurable_fst))
    (history, abstractAction)

/-- The abstract `Unit` policy is well formed and realizes legally at every
nonterminal prefix. -/
noncomputable def unitPolicy :
    EventInformation.RealizedActionPolicy unitRealization where
  abstractKernel := fun _ => unitAbstractKernel
  abstractKernel_isSFinite := fun _ =>
    unitAbstractKernel_isSFinite
  terminal_zero := by
    intro time history hterminal
    change
      unitAbstractKernel
        (terminalTag
          (MeasurableKernelArena.latestEventState
            time history).1) = 0
    rw [terminalTag_eq_true_of_terminal
      (MeasurableKernelArena.latestEventState time history)
      hterminal]
    exact unitAbstractKernel_true
  nonterminal_isProbability := by
    intro time history hnonterminal
    change
      IsProbabilityMeasure
        (unitAbstractKernel
          (terminalTag
            (MeasurableKernelArena.latestEventState
              time history).1))
    rw [terminalTag_eq_false_of_nonterminal
      (MeasurableKernelArena.latestEventState time history)
      hnonterminal]
    rw [unitAbstractKernel_false]
    infer_instance
  realization_isProbability := by
    intro time history hnonterminal
    exact Filter.Eventually.of_forall fun abstractAction => by
      rw [unitRealization_kernel_apply]
      infer_instance
  realization_legal := by
    intro time history hnonterminal
    change
      ∀ᵐ stateAction
          ∂(unitAbstractKernel
              (terminalTag
                (MeasurableKernelArena.latestEventState
                  time history).1)).bind
            (fun abstractAction =>
              unitRealization.kernel time (history, abstractAction)),
        stateAction ∈
          liftedArena.actionFiber
            (MeasurableKernelArena.latestEventState time history)
    rw [
      terminalTag_eq_false_of_nonterminal
        (MeasurableKernelArena.latestEventState time history)
        hnonterminal,
      unitAbstractKernel_false]
    change
      ∀ᵐ stateAction
          ∂(Measure.dirac ()).bind
            (Kernel.sectR
              (unitRealization.kernel time) history),
        stateAction ∈
          liftedArena.actionFiber
            (MeasurableKernelArena.latestEventState time history)
    have hbind :
        (Measure.dirac ()).bind
            (Kernel.sectR
              (unitRealization.kernel time) history) =
          unitRealization.kernel time (history, ()) := by
      exact
        (Measure.dirac_bind
          (Kernel.sectR
            (unitRealization.kernel time) history).measurable
          ())
    rw [hbind, unitRealization_kernel_apply]
    apply
      (ae_dirac_iff
        (liftedArena.measurableSet_actionFiber _)).2
    exact
      realizeBundle_fst_of_nonterminal _ hnonterminal

/-- At every terminal event prefix, compilation produces the killed zero
concrete action law. -/
theorem unitPolicy_compiled_terminal
    (time : ℕ) (history : liftedArena.EventPrefix time)
    (hterminal :
      IsEmpty
        (liftedArena.Action
          (MeasurableKernelArena.latestEventState time history))) :
    unitPolicy.toEventHistoryActionPolicy.kernel time history = 0 :=
  unitPolicy.toEventHistoryActionPolicy.terminal_zero
    time history hterminal

/-- At every nonterminal event prefix, compilation is the Dirac law at the
unique bundle based at that exact latest complete history. -/
theorem unitPolicy_compiled_nonterminal
    (time : ℕ) (history : liftedArena.EventPrefix time)
    (hnonterminal :
      ¬ IsEmpty
        (liftedArena.Action
          (MeasurableKernelArena.latestEventState time history))) :
    unitPolicy.toEventHistoryActionPolicy.kernel time history =
      Measure.dirac
        (realizeBundle
          (MeasurableKernelArena.latestEventState time history)) := by
  rw [
    EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy_kernel_apply]
  change
    (unitAbstractKernel
      (terminalTag
        (MeasurableKernelArena.latestEventState time history).1)).bind
        (fun abstractAction =>
          unitRealization.kernel time (history, abstractAction)) =
      _
  rw [
    terminalTag_eq_false_of_nonterminal
      (MeasurableKernelArena.latestEventState time history)
      hnonterminal,
    unitAbstractKernel_false]
  calc
    (Measure.dirac ()).bind
          (Kernel.sectR (unitRealization.kernel time) history) =
        Kernel.sectR (unitRealization.kernel time) history () :=
      Measure.dirac_bind
        (Kernel.sectR
          (unitRealization.kernel time) history).measurable
        ()
    _ = _ := by
      rw [Kernel.sectR_apply]
      exact unitRealization_kernel_apply time history ()

@[simp]
theorem unitPolicy_abstractKernel
    (time : ℕ) (information : Bool) :
    unitPolicy.abstractKernel time information =
      unitAbstractKernel information :=
  rfl

/-- The new abstract-action policy class is concretely inhabited. -/
theorem realized_policy_nonempty :
    Nonempty
      (EventInformation.RealizedActionPolicy
        unitRealization) :=
  ⟨unitPolicy⟩

/-- The two recurring decisions receive exactly the same abstract law. -/
theorem recurring_abstract_law_eq :
    unitPolicy.abstractKernel 0
        (terminalTaggedInformation.informationAt
          0 firstPrefix) =
      unitPolicy.abstractKernel 0
        (terminalTaggedInformation.informationAt
          0 secondPrefix) :=
  unitPolicy.abstractKernel_eq_of_informationAt_eq
    0 firstPrefix secondPrefix (by rfl)

/-- The compiled concrete action law at the first decision is Dirac at the
first history state's unique legal bundle. -/
theorem compiled_firstPrefix :
    unitPolicy.toEventHistoryActionPolicy.kernel
        0 firstPrefix =
      Measure.dirac (realizeBundle firstDecision) := by
  rw [
    EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy_kernel_apply]
  rw [unitPolicy_abstractKernel]
  rw [terminalTaggedInformation_firstPrefix,
    unitAbstractKernel_false]
  change
    (Measure.dirac ()).bind
        (Kernel.sectR
          (unitRealization.kernel 0) firstPrefix) =
      Measure.dirac (realizeBundle firstDecision)
  calc
    _ =
        Kernel.sectR
          (unitRealization.kernel 0) firstPrefix () :=
      Measure.dirac_bind
        (Kernel.sectR
          (unitRealization.kernel 0) firstPrefix).measurable
        ()
    _ = _ := by
      rw [Kernel.sectR_apply]
      rw [unitRealization_kernel_apply]
      rfl

/-- The compiled concrete action law at the second decision is Dirac at the
second history state's unique legal bundle. -/
theorem compiled_secondPrefix :
    unitPolicy.toEventHistoryActionPolicy.kernel
        0 secondPrefix =
      Measure.dirac (realizeBundle secondDecision) := by
  rw [
    EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy_kernel_apply]
  rw [unitPolicy_abstractKernel]
  rw [terminalTaggedInformation_secondPrefix,
    unitAbstractKernel_false]
  change
    (Measure.dirac ()).bind
        (Kernel.sectR
          (unitRealization.kernel 0) secondPrefix) =
      Measure.dirac (realizeBundle secondDecision)
  calc
    _ =
        Kernel.sectR
          (unitRealization.kernel 0) secondPrefix () :=
      Measure.dirac_bind
        (Kernel.sectR
          (unitRealization.kernel 0) secondPrefix).measurable
        ()
    _ = _ := by
      rw [Kernel.sectR_apply]
      rw [unitRealization_kernel_apply]
      rfl

/-- The two history-dependent concrete realizations are different bundles
because their base complete-history states differ. -/
theorem realizeBundle_first_ne_second :
    realizeBundle firstDecision ≠
      realizeBundle secondDecision := by
  intro heq
  apply firstDecision_ne_secondDecision
  exact congrArg Sigma.fst heq

/-- Equal player information and equal abstract laws do not imply literally
equal concrete bundle measures at distinct history states. The realization
layer intentionally produces different Dirac bundles in the two legal
fibers. -/
theorem compiled_concrete_laws_ne :
    unitPolicy.toEventHistoryActionPolicy.kernel
        0 firstPrefix ≠
      unitPolicy.toEventHistoryActionPolicy.kernel
        0 secondPrefix := by
  rw [compiled_firstPrefix, compiled_secondPrefix]
  exact
    MeasureTheory.dirac_ne_dirac
      realizeBundle_first_ne_second

/-- Even after terminal histories are tagged separately, the old direct
concrete-bundle information policy remains impossible solely because the two
nonterminal history-state fibers differ. -/
theorem no_direct_concrete_bundle_policy :
    ¬ Nonempty
      (EventInformation.ActionPolicy
        terminalTaggedInformation) := by
  rintro ⟨policy⟩
  have hstates :=
    policy.latestEventState_eq_of_informationAt_eq
      0 firstPrefix secondPrefix
      firstPrefix_nonterminal secondPrefix_nonterminal
      (by rfl)
  apply firstDecision_ne_secondDecision
  simpa [
    firstPrefix, secondPrefix,
    MeasurableKernelArena.latestEventState,
    MeasurableKernelArena.latestEvent,
    MeasurableKernelArena.PathEvent.state,
    MeasurableKernelArena.initialEvent] using hstates

/-- Strict expressiveness separation on one fixed terminal-tagged information
structure: abstract realization policies exist, direct concrete-bundle
policies do not. -/
theorem realized_strictly_more_expressive :
    Nonempty
        (EventInformation.RealizedActionPolicy
          unitRealization) ∧
      ¬ Nonempty
        (EventInformation.ActionPolicy
          terminalTaggedInformation) :=
  ⟨realized_policy_nonempty,
    no_direct_concrete_bundle_policy⟩

end Examples.RealizedInformationBoundary
