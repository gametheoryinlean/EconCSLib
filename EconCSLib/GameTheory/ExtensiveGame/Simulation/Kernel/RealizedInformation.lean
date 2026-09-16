/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.ObservedEvent
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Kernel.RealizedInformation — history-dependent action realization

`EventInformation.ActionPolicy` chooses measures directly on the concrete
dependent `ActionBundle`. This is appropriate when equal information prefixes
have the same latest state, but it cannot represent a player information set
spanning distinct complete-history states: the corresponding concrete action
fibers are disjoint.

This module separates two roles:

* `ActionRealization` is fixed model data. It supplies a measurable abstract
  action carrier at every event time and a measurable kernel which realizes an
  abstract action at a concrete event prefix as a concrete action bundle.
* `RealizedActionPolicy` is strategy data. Its kernel is indexed only by the
  fixed information value and chooses abstract actions. At every represented
  nonterminal prefix, almost every selected abstract action must be realized
  by a probability measure concentrated on the latest concrete action fiber.

Compilation uses Mathlib's composition-product. First sample the abstract law
at the prefix's information value, then apply the prefix-dependent realization
kernel, and finally forget the abstract action. The result is a raw
`EventHistoryActionPolicy`.

Equal information therefore forces exactly equal **abstract** laws. Concrete
compiled laws at different histories are equal only under an additional
almost-everywhere equality of their realization kernels. This is the intended
imperfect-information semantics: one decision rule, realized separately in
history-specific dependent action types.

## Main definitions

* `EventInformation.ActionRealization` — fixed abstract carrier and measurable
  history-dependent realization kernel.
* `EventInformation.RealizedActionPolicy` — information-indexed abstract laws
  with almost-sure realization certificates.
* `RealizedActionPolicy.realizedKernel` — the compiled concrete action kernel.
* `RealizedActionPolicy.toEventHistoryActionPolicy` — compilation to the joint
  event executor.

## Main results

* `realizedKernel_apply` — pointwise measure-bind formula.
* `abstractKernel_eq_of_informationAt_eq` — structural information
  consistency at the correct abstract level.
* `compiled_kernel_eq_of_informationAt_eq_of_realization_ae_eq` — concrete
  equality under the necessary realization compatibility premise.
* `pullback_toEventHistoryActionPolicy` — exact compiler naturality under
  measurable information forgetting.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uS uA uI uC

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

namespace EventInformation

/-- Fixed abstract-action and concrete-realization data for an event
information structure.

The realization kernel is allowed to be zero or otherwise irrelevant on
abstract actions that a policy selects with probability zero. This permits a
single sigma carrier to contain actions for many player, chance, and
information tags without inventing concrete fallback actions for mismatched
tags. -/
structure ActionRealization
    (information : EventInformation A) where
  /-- Time-indexed common carrier on which abstract action laws live. -/
  AbstractAction : ℕ → Type uC
  /-- Measurable structure on each abstract action carrier. -/
  abstractActionMeasurable :
    ∀ time, MeasurableSpace (AbstractAction time)
  /-- Realize an abstract action at a concrete event prefix as a measure on
  concrete dependent action bundles. -/
  kernel :
    (time : ℕ) →
      Kernel
        (A.EventPrefix time × AbstractAction time)
        A.ActionBundle
  /-- Realization kernels are globally s-finite, including on irrelevant
  prefix/action pairs, so composition-product has its mathematical rather
  than junk-zero semantics. -/
  kernel_isSFinite :
    ∀ time, IsSFiniteKernel (kernel time)

instance ActionRealization.instMeasurableSpaceAbstractAction
    {information : EventInformation A}
    (realization : ActionRealization information) (time : ℕ) :
    MeasurableSpace (realization.AbstractAction time) :=
  realization.abstractActionMeasurable time

instance ActionRealization.instKernelIsSFinite
    {information : EventInformation A}
    (realization : ActionRealization information) (time : ℕ) :
    IsSFiniteKernel (realization.kernel time) :=
  realization.kernel_isSFinite time

/-- A policy on abstract information actions together with almost-sure
realization correctness.

The action realization is a parameter, not a policy field, so every strategy
and deviation in one model shares the same interpretation of abstract
actions. -/
structure RealizedActionPolicy
    {information : EventInformation A}
    (realization : ActionRealization information) where
  /-- Possibly killed abstract action kernel indexed only by information. -/
  abstractKernel :
    (time : ℕ) →
      Kernel
        (information.Information time)
        (realization.AbstractAction time)
  /-- Abstract kernels are globally s-finite, including off the image of the
  information map. -/
  abstractKernel_isSFinite :
    ∀ time, IsSFiniteKernel (abstractKernel time)
  /-- Terminal prefixes produce no abstract action mass. -/
  terminal_zero :
    ∀ time history,
      IsEmpty (A.Action (latestEventState time history)) →
        abstractKernel time
          (information.informationAt time history) = 0
  /-- Nonterminal represented prefixes have normalized abstract laws. -/
  nonterminal_isProbability :
    ∀ time history,
      ¬ IsEmpty (A.Action (latestEventState time history)) →
        IsProbabilityMeasure
          (abstractKernel time
            (information.informationAt time history))
  /-- At a represented nonterminal prefix, almost every selected abstract
  action is realized by a normalized concrete measure. -/
  realization_isProbability :
    ∀ time history
      (_hnonterminal :
        ¬ IsEmpty (A.Action (latestEventState time history))),
      ∀ᵐ abstractAction
          ∂abstractKernel time
            (information.informationAt time history),
        IsProbabilityMeasure
          (realization.kernel time (history, abstractAction))
  /-- At a represented nonterminal prefix, the compiled concrete action
  bundle lies in the latest state's fiber almost surely.

  This direct certificate is intentionally about the bound concrete law.
  Nested "almost every abstract action, then almost every realization"
  statements do not in general imply an almost-everywhere statement for a
  nonmeasurable fiber under `Measure.bind`. -/
  realization_legal :
    ∀ time history
      (_hnonterminal :
        ¬ IsEmpty (A.Action (latestEventState time history))),
      ∀ᵐ stateAction
          ∂(abstractKernel time
              (information.informationAt time history)).bind
            (fun abstractAction =>
              realization.kernel time (history, abstractAction)),
        stateAction ∈
          A.actionFiber (latestEventState time history)

namespace RealizedActionPolicy

variable
  {information : EventInformation A}
  {fine coarse : EventInformation A}
  {realization : ActionRealization information}

/-- Compatibility bridge for presentations whose state fibers are
measurable.

If the abstract law is a probability measure, almost every realization is a
probability measure, and the legacy numerical fiber equation holds almost
everywhere over abstract actions, then the bound concrete law is genuinely
almost surely legal.  The singleton-measurability assumption is deliberately
local to this bridge. -/
theorem ae_bind_mem_actionFiber_of_ae_mass_one
    [MeasurableSingletonClass A.State]
    {C : Type*} [MeasurableSpace C]
    (abstractMeasure : Measure C)
    [IsProbabilityMeasure abstractMeasure]
    (realizationKernel : Kernel C A.ActionBundle)
    (state : A.State)
    (hprobability :
      ∀ᵐ abstractAction ∂abstractMeasure,
        IsProbabilityMeasure
          (realizationKernel abstractAction))
    (hmass :
      ∀ᵐ abstractAction ∂abstractMeasure,
        realizationKernel abstractAction
            (A.actionFiber state) =
          1) :
    ∀ᵐ stateAction
        ∂abstractMeasure.bind realizationKernel,
      stateAction ∈ A.actionFiber state := by
  letI : IsProbabilityMeasure
      (abstractMeasure.bind realizationKernel) :=
    isProbabilityMeasure_bind
      realizationKernel.aemeasurable hprobability
  apply
    (mem_ae_iff_prob_eq_one₀
      (A.measurableSet_actionFiber state).nullMeasurableSet).2
  rw [
    Measure.bind_apply
      (A.measurableSet_actionFiber state)
      realizationKernel.aemeasurable]
  calc
    ∫⁻ abstractAction,
        realizationKernel abstractAction
          (A.actionFiber state) ∂abstractMeasure =
        abstractMeasure Set.univ := by
      rw [← lintegral_one]
      exact lintegral_congr_ae hmass
    _ = 1 := measure_univ

instance instAbstractKernelIsSFinite
    (policy : RealizedActionPolicy realization) (time : ℕ) :
    IsSFiniteKernel (policy.abstractKernel time) :=
  policy.abstractKernel_isSFinite time

/-- Abstract action selection after measurable comap along the fixed
information statistic. -/
def prefixAbstractKernel
    (policy : RealizedActionPolicy realization) (time : ℕ) :
    Kernel
      (A.EventPrefix time)
      (realization.AbstractAction time) :=
  Kernel.comap
    (policy.abstractKernel time)
    (information.informationAt time)
    (information.informationAt_measurable time)

instance prefixAbstractKernel_isSFinite
    (policy : RealizedActionPolicy realization) (time : ℕ) :
    IsSFiniteKernel (policy.prefixAbstractKernel time) := by
  rw [prefixAbstractKernel]
  infer_instance

@[simp]
theorem prefixAbstractKernel_apply
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time) :
    policy.prefixAbstractKernel time history =
      policy.abstractKernel time
        (information.informationAt time history) :=
  rfl

/-- Compile abstract action selection and history-dependent realization to a
concrete action-bundle kernel.

Composition-product retains the prefix while sampling the abstract action.
Taking `snd` then forgets the abstract action after realization. -/
noncomputable def realizedKernel
    (policy : RealizedActionPolicy realization) (time : ℕ) :
    Kernel (A.EventPrefix time) A.ActionBundle :=
  Kernel.snd
    (policy.prefixAbstractKernel time ⊗ₖ
      realization.kernel time)

instance realizedKernel_isSFinite
    (policy : RealizedActionPolicy realization) (time : ℕ) :
    IsSFiniteKernel (policy.realizedKernel time) := by
  rw [realizedKernel]
  infer_instance

/-- Pointwise semantics of the compiled concrete action kernel: sample the
abstract information action, then realize it at the concrete prefix. -/
theorem realizedKernel_apply
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time) :
    policy.realizedKernel time history =
      (policy.abstractKernel time
        (information.informationAt time history)).bind
          (fun abstractAction =>
            realization.kernel time (history, abstractAction)) := by
  rw [realizedKernel, Kernel.snd_apply]
  rw [Kernel.compProd_apply_eq_compProd_sectR]
  change
    (((policy.prefixAbstractKernel time) history) ⊗ₘ
      Kernel.sectR (realization.kernel time) history).snd =
        _
  rw [Measure.snd_compProd]
  rfl

/-- Compile a realized abstract information policy to the raw complete-event
executor.

The compiled executor consumes the direct almost-sure legality certificate;
no measurability of state singletons is required. -/
noncomputable def toEventHistoryActionPolicy
    (policy : RealizedActionPolicy realization) :
    A.EventHistoryActionPolicy where
  kernel := policy.realizedKernel
  terminal_zero := by
    intro time history hterminal
    rw [policy.realizedKernel_apply]
    rw [policy.terminal_zero time history hterminal]
    exact Measure.bind_zero_left _
  nonterminal_isProbability := by
    intro time history hnonterminal
    rw [policy.realizedKernel_apply]
    letI : IsProbabilityMeasure
        (policy.abstractKernel time
          (information.informationAt time history)) :=
      policy.nonterminal_isProbability
        time history hnonterminal
    exact isProbabilityMeasure_bind
      (Kernel.sectR
        (realization.kernel time) history).aemeasurable
      (policy.realization_isProbability
        time history hnonterminal)
  legal := by
    intro time history hnonterminal
    rw [policy.realizedKernel_apply]
    exact policy.realization_legal time history hnonterminal

@[simp]
theorem toEventHistoryActionPolicy_kernel_apply
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time) :
    policy.toEventHistoryActionPolicy.kernel time history =
      (policy.abstractKernel time
        (information.informationAt time history)).bind
          (fun abstractAction =>
            realization.kernel time (history, abstractAction)) :=
  policy.realizedKernel_apply time history

/-- Equal information values force exactly equal abstract action laws.

This is the information-consistency theorem appropriate for action types
whose concrete realization depends on the actual history. -/
theorem abstractKernel_eq_of_informationAt_eq
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history₁ history₂ : A.EventPrefix time)
    (hsame :
      information.informationAt time history₁ =
        information.informationAt time history₂) :
    policy.abstractKernel time
        (information.informationAt time history₁) =
      policy.abstractKernel time
        (information.informationAt time history₂) := by
  rw [hsame]

/-- Equal information gives equal concrete compiled laws only when the two
history-specific realizations agree almost everywhere under their common
abstract law.

The extra premise is mathematically necessary and prevents the false theorem
that distinct dependent action fibers receive literally equal bundle
measures. -/
theorem compiled_kernel_eq_of_informationAt_eq_of_realization_ae_eq
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history₁ history₂ : A.EventPrefix time)
    (hsame :
      information.informationAt time history₁ =
        information.informationAt time history₂)
    (hrealization :
      ∀ᵐ abstractAction
          ∂policy.abstractKernel time
            (information.informationAt time history₁),
        realization.kernel time (history₁, abstractAction) =
          realization.kernel time (history₂, abstractAction)) :
    policy.toEventHistoryActionPolicy.kernel time history₁ =
      policy.toEventHistoryActionPolicy.kernel time history₂ := by
  rw [policy.toEventHistoryActionPolicy_kernel_apply]
  rw [policy.toEventHistoryActionPolicy_kernel_apply]
  rw [← hsame]
  exact Measure.bind_congr_right hrealization

end RealizedActionPolicy

namespace ActionRealization

/-- Reuse one abstract-action realization after replacing its information
structure by a measurable refinement.

The concrete realization already receives the full prefix, so only the
abstract information index changes. -/
def pullback
    {fine coarse : EventInformation A}
    (realization : ActionRealization coarse)
    (_factor : Hom fine coarse) :
    ActionRealization fine where
  AbstractAction := realization.AbstractAction
  abstractActionMeasurable :=
    realization.abstractActionMeasurable
  kernel := realization.kernel
  kernel_isSFinite := realization.kernel_isSFinite

end ActionRealization

namespace RealizedActionPolicy

variable
  {fine coarse : EventInformation A}
  {coarseRealization : ActionRealization coarse}

/-- Pull an abstract coarse-information policy back along a measurable
fine-to-coarse factor while retaining the same concrete realization. -/
def pullback
    (policy : RealizedActionPolicy coarseRealization)
    (factor : Hom fine coarse) :
    RealizedActionPolicy (coarseRealization.pullback factor) where
  abstractKernel := fun time =>
    Kernel.comap (policy.abstractKernel time)
      (factor.map time) (factor.map_measurable time)
  abstractKernel_isSFinite := by
    intro time
    letI : IsSFiniteKernel (policy.abstractKernel time) :=
      policy.abstractKernel_isSFinite time
    exact
      ProbabilityTheory.Kernel.IsSFiniteKernel.comap
        (policy.abstractKernel time)
        (factor.map_measurable time)
  terminal_zero := by
    intro time history hterminal
    change
      policy.abstractKernel time
          (factor.map time
            (fine.informationAt time history)) = 0
    rw [factor.map_informationAt]
    exact policy.terminal_zero time history hterminal
  nonterminal_isProbability := by
    intro time history hnonterminal
    change
      IsProbabilityMeasure
        (policy.abstractKernel time
          (factor.map time
            (fine.informationAt time history)))
    rw [factor.map_informationAt]
    exact policy.nonterminal_isProbability
      time history hnonterminal
  realization_isProbability := by
    intro time history hnonterminal
    change
      ∀ᵐ abstractAction
          ∂policy.abstractKernel time
            (factor.map time
              (fine.informationAt time history)),
        IsProbabilityMeasure
          (coarseRealization.kernel time
            (history, abstractAction))
    rw [factor.map_informationAt]
    exact policy.realization_isProbability
      time history hnonterminal
  realization_legal := by
    intro time history hnonterminal
    change
      ∀ᵐ stateAction
          ∂(policy.abstractKernel time
              (factor.map time
                (fine.informationAt time history))).bind
            (fun abstractAction =>
              coarseRealization.kernel time
                (history, abstractAction)),
        stateAction ∈
          A.actionFiber (latestEventState time history)
    rw [factor.map_informationAt]
    exact policy.realization_legal
      time history hnonterminal

/-- Information pullback leaves the compiled concrete realized kernel
unchanged at every event prefix. -/
theorem pullback_realizedKernel
    (policy : RealizedActionPolicy coarseRealization)
    (factor : Hom fine coarse)
    (time : ℕ) :
    (policy.pullback factor).realizedKernel time =
      policy.realizedKernel time := by
  apply Kernel.ext
  intro history
  rw [realizedKernel_apply, realizedKernel_apply]
  change
    (policy.abstractKernel time
      (factor.map time
        (fine.informationAt time history))).bind
        (fun abstractAction =>
          coarseRealization.kernel time
            (history, abstractAction)) =
      (policy.abstractKernel time
        (coarse.informationAt time history)).bind
        (fun abstractAction =>
          coarseRealization.kernel time
            (history, abstractAction))
  rw [factor.map_informationAt]

/-- Pullback along an information factor preserves the raw compiled event
policy exactly. -/
theorem pullback_toEventHistoryActionPolicy
    (policy : RealizedActionPolicy coarseRealization)
    (factor : Hom fine coarse) :
    (policy.pullback factor).toEventHistoryActionPolicy =
      policy.toEventHistoryActionPolicy := by
  apply EventHistoryActionPolicy.ext
  funext time
  exact policy.pullback_realizedKernel factor time

/-- Pullback along an information factor preserves every stopped joint event
step kernel. -/
theorem pullback_pathStepKernel
    (policy : RealizedActionPolicy coarseRealization)
    (factor : Hom fine coarse)
    (hterminal : MeasurableSet A.terminalSet)
    (time : ℕ) :
    (policy.pullback factor).toEventHistoryActionPolicy.pathStepKernel
        hterminal time =
      policy.toEventHistoryActionPolicy.pathStepKernel
        hterminal time := by
  rw [pullback_toEventHistoryActionPolicy]

/-- Pullback along an information factor preserves the complete infinite
joint event-path law. -/
theorem pullback_pathMeasure
    (policy : RealizedActionPolicy coarseRealization)
    (factor : Hom fine coarse)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    (policy.pullback factor).toEventHistoryActionPolicy.pathMeasure
        hterminal initialState =
      policy.toEventHistoryActionPolicy.pathMeasure
        hterminal initialState := by
  rw [pullback_toEventHistoryActionPolicy]

end RealizedActionPolicy

end EventInformation

end MeasurableKernelArena
