/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Certificates

/-!
# Restart.Factorization — statistic-based compatibility constructors

Root-uniform fresh-restart compatibility need not be proved by unfolding a
policy at every spliced prefix. This module supplies a reusable sufficient
construction: factor the behavioral action kernel through a fixed measurable
statistic of complete event prefixes, then prove either that the statistic
itself, or only its resulting action law, is invariant under canonical rooted
splicing.

The statistic has one fixed measurable value type at every event time. This
is intentionally more restrictive than the time-indexed value family of
`EventInformation`, but it permits a typed equality between values computed
at fresh time `offset` and absolute time `start + offset`. The common action
law is a genuine Mathlib kernel on that value type.

The construction is sufficient, not necessary. No theorem claims that every
root-uniform policy factors through a supplied statistic. A latest-state
statistic and the stationary state-Markov policy embedding are provided as
canonical specializations. A clock-and-latest-state statistic demonstrates
the strictly weaker action-law invariant premise: its clock values may differ
while a common kernel ignores that component.

For genuinely time-varying observation types, `EventInformation` additionally
admits a measurable `FreshRestartRebase` from absolute information back to
fresh information. Naturality of a time-indexed information action policy
along that transport implies root-uniform compatibility of its compiled raw
policy; the transport need not be invertible.
-/

open MeasureTheory ProbabilityTheory

universe uZ

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

/-- A complete-event-prefix statistic with one fixed measurable value type
across all event times.

The fixed codomain makes values at fresh and absolute clocks directly
comparable. Time dependence remains available through `valueAt`; restart
compatibility follows only when a separate splice-invariance proof is
supplied.
-/
structure EventHistoryStatistic
    (A : MeasurableKernelArena) where
  /-- Common value type of the statistic at every event time. -/
  Value : Type uZ
  /-- Measurable structure on statistic values. -/
  valueMeasurable : MeasurableSpace Value
  /-- Statistic computed from a complete event prefix. -/
  valueAt :
    (time : ℕ) → A.ContinuationPrefix time → Value
  /-- The statistic is measurable at every event time. -/
  valueAt_measurable :
    ∀ time,
      @Measurable
        (A.ContinuationPrefix time) Value
        inferInstance valueMeasurable
        (valueAt time)

namespace EventHistoryStatistic

instance (statistic : A.EventHistoryStatistic) :
    MeasurableSpace statistic.Value :=
  statistic.valueMeasurable

/-- Regard a fixed-codomain history statistic as an ordinary time-indexed
event-information structure with the same value type at every time.

This embeds the restart-factorization interface into the existing observed
information-policy layer rather than creating a separate policy hierarchy.
-/
def toEventInformation
    (statistic : A.EventHistoryStatistic) :
    A.EventInformation where
  Information := fun _ => statistic.Value
  informationMeasurable := fun _ =>
    statistic.valueMeasurable
  informationAt := statistic.valueAt
  informationAt_measurable :=
    statistic.valueAt_measurable

@[simp]
theorem toEventInformation_informationAt
    (statistic : A.EventHistoryStatistic)
    (time : ℕ)
    (finitePrefix : A.ContinuationPrefix time) :
    statistic.toEventInformation.informationAt
        time finitePrefix =
      statistic.valueAt time finitePrefix :=
  rfl

/-- A statistic is fresh-restart invariant when every canonically rooted
fresh prefix and its absolute splice have exactly the same statistic value.

This is a pointwise structural condition. It includes unreachable prefixes
and deliberately avoids any generated-law or almost-everywhere weakening.
-/
def IsFreshRestartInvariant
    (statistic : A.EventHistoryStatistic) :
    Prop :=
  ∀ start initialPrefix offset freshPrefix,
    IsInitialEventRootedPrefix
        (latestEventState start initialPrefix)
        offset freshPrefix →
      statistic.valueAt
          (start + offset)
          (spliceContinuationPrefix
            start initialPrefix offset freshPrefix) =
        statistic.valueAt offset freshPrefix

/-- Behavioral invariance of a statistic/action-kernel pair under canonical
rooted splicing.

Unlike `IsFreshRestartInvariant`, this condition permits the statistic values
themselves to differ, provided that the common action kernel assigns them
exactly the same action measure.
-/
def IsFreshRestartActionLawInvariant
    (statistic : A.EventHistoryStatistic)
    (actionLaw : Kernel statistic.Value A.ActionBundle) :
    Prop :=
  ∀ start initialPrefix offset freshPrefix,
    IsInitialEventRootedPrefix
        (latestEventState start initialPrefix)
        offset freshPrefix →
      actionLaw
          (statistic.valueAt
            (start + offset)
            (spliceContinuationPrefix
              start initialPrefix offset freshPrefix)) =
        actionLaw
          (statistic.valueAt offset freshPrefix)

/-- Literal statistic invariance implies behavioral action-law invariance for
every common action kernel.
-/
theorem IsFreshRestartInvariant.actionLaw
    {statistic : A.EventHistoryStatistic}
    (hinvariant :
      statistic.IsFreshRestartInvariant)
    (actionLaw : Kernel statistic.Value A.ActionBundle) :
    statistic.IsFreshRestartActionLawInvariant
      actionLaw := by
  intro start initialPrefix offset freshPrefix hrooted
  rw [
    hinvariant
      start initialPrefix offset freshPrefix hrooted]

/-- The latest event state as a fixed-codomain measurable history statistic.
-/
def latestState (A : MeasurableKernelArena) :
    A.EventHistoryStatistic where
  Value := A.State
  valueMeasurable := inferInstance
  valueAt := latestEventState
  valueAt_measurable := measurable_latestEventState

@[simp]
theorem latestState_valueAt
    (time : ℕ)
    (finitePrefix : A.ContinuationPrefix time) :
    (latestState A).valueAt time finitePrefix =
      latestEventState time finitePrefix :=
  rfl

/-- The latest-state statistic is invariant under every canonical rooted
splice. At offset zero this uses the rooted marker premise; at positive
offsets it follows because splicing retains every positive fresh event.
-/
theorem latestState_isFreshRestartInvariant :
    (latestState A).IsFreshRestartInvariant := by
  intro start initialPrefix offset freshPrefix hrooted
  exact
    latestEventState_spliceContinuationPrefix_eq_of_rooted
      start initialPrefix offset freshPrefix hrooted

/-- Absolute clock together with latest state as one measurable statistic.

This statistic is useful when a policy representation retains an absolute
clock even though its action law ignores that component.
-/
def clockAndLatestState (A : MeasurableKernelArena) :
    A.EventHistoryStatistic where
  Value := ℕ × A.State
  valueMeasurable := inferInstance
  valueAt := fun time finitePrefix =>
    (time, latestEventState time finitePrefix)
  valueAt_measurable := fun time =>
    measurable_const.prodMk
      (measurable_latestEventState time)

@[simp]
theorem clockAndLatestState_valueAt
    (time : ℕ)
    (finitePrefix : A.ContinuationPrefix time) :
    (clockAndLatestState A).valueAt time finitePrefix =
      (time, latestEventState time finitePrefix) :=
  rfl

/-- Lift a state-indexed action kernel to clock-and-state values while
ignoring the clock coordinate.
-/
def actionLawIgnoringClock
    (actionLaw : Kernel A.State A.ActionBundle) :
    Kernel (ℕ × A.State) A.ActionBundle :=
  Kernel.comap actionLaw Prod.snd measurable_snd

@[simp]
theorem actionLawIgnoringClock_apply
    (actionLaw : Kernel A.State A.ActionBundle)
    (time : ℕ)
    (state : A.State) :
    actionLawIgnoringClock actionLaw (time, state) =
      actionLaw state :=
  rfl

/-- Although `clockAndLatestState` may distinguish fresh and absolute clocks,
an action kernel that ignores the clock is invariant on every rooted
fresh/spliced pair.
-/
theorem clockAndLatestState_actionLawIgnoringClock_isFreshRestartInvariant
    (actionLaw : Kernel A.State A.ActionBundle) :
    (clockAndLatestState A).IsFreshRestartActionLawInvariant
      (actionLawIgnoringClock actionLaw) := by
  intro start initialPrefix offset freshPrefix hrooted
  change
    actionLaw
        (latestEventState (start + offset)
          (spliceContinuationPrefix
            start initialPrefix offset freshPrefix)) =
      actionLaw (latestEventState offset freshPrefix)
  rw [
    latestEventState_spliceContinuationPrefix_eq_of_rooted
      start initialPrefix offset freshPrefix hrooted]

end EventHistoryStatistic

namespace EventInformation

/-- A measurable transport from absolute-clock information back to
fresh-clock information at a retained prefix.

The information types may genuinely vary with event time. The transport may
depend on the retained complete prefix, and it is not required to be
injective, surjective, or invertible. Its rooted-splice law is stated only on
information values represented by canonical fresh/spliced prefix pairs.
-/
structure FreshRestartRebase
    (information : A.EventInformation) where
  /-- Transport absolute information at `start + offset` back to fresh
  information at `offset`. -/
  rebase :
    (start : ℕ) →
      A.ContinuationPrefix start →
        (offset : ℕ) →
          information.Information (start + offset) →
            information.Information offset
  /-- Every fixed-root, fixed-offset transport is measurable. -/
  rebase_measurable :
    ∀ start initialPrefix offset,
      Measurable (rebase start initialPrefix offset)
  /-- On a canonically rooted fresh prefix, transporting the information of
  its absolute splice recovers the original fresh information. -/
  rebase_informationAt_splice :
    ∀ start initialPrefix offset freshPrefix,
      IsInitialEventRootedPrefix
          (latestEventState start initialPrefix)
          offset freshPrefix →
        rebase start initialPrefix offset
            (information.informationAt
              (start + offset)
              (spliceContinuationPrefix
                start initialPrefix offset freshPrefix)) =
          information.informationAt offset freshPrefix

namespace ActionPolicy

/-- Naturality of a time-indexed information action policy along a supplied
fresh-restart rebase.

This is deliberately a global structural condition on every information
value, including values not represented by a concrete event prefix. It is
therefore stronger than compiled compatibility on rooted splice pairs.
-/
def IsFreshRestartRebaseNatural
    {information : A.EventInformation}
    (policy : ActionPolicy information)
    (transport : FreshRestartRebase information) :
    Prop :=
  ∀ start initialPrefix offset informationValue,
    policy.kernel (start + offset) informationValue =
      policy.kernel offset
        (transport.rebase
          start initialPrefix offset informationValue)

/-- A time-indexed information policy that is natural along a lawful
fresh-restart rebase compiles to a root-uniform compatible raw behavioral
policy.

The proof uses naturality at the represented absolute-splice information
value and then the transport's rooted-splice law.
-/
theorem IsFreshRestartRebaseNatural.compiledPolicy_freshRestartRootedActionKernelCompatible
    {information : A.EventInformation}
    {policy : ActionPolicy information}
    {transport : FreshRestartRebase information}
    (hnatural :
      policy.IsFreshRestartRebaseNatural transport) :
    EventHistoryActionPolicy.IsFreshRestartRootedActionKernelCompatible
      policy.toEventHistoryActionPolicy := by
  intro start initialPrefix offset freshPrefix hrooted
  change
    policy.kernel (start + offset)
        (information.informationAt
          (start + offset)
          (spliceContinuationPrefix
            start initialPrefix offset freshPrefix)) =
      policy.kernel offset
        (information.informationAt offset freshPrefix)
  rw [
    hnatural
      start initialPrefix offset
      (information.informationAt
        (start + offset)
        (spliceContinuationPrefix
          start initialPrefix offset freshPrefix)),
    transport.rebase_informationAt_splice
      start initialPrefix offset freshPrefix hrooted]

end ActionPolicy

end EventInformation

namespace EventHistoryActionPolicy

/-- A raw behavioral policy factors through a measurable event-history
statistic and a common action kernel when every prefix action measure is the
action kernel evaluated at its statistic value.

The policy is already responsible for terminal zero mass, normalization, and
legality. This predicate records only the additional factorization equation.
-/
def FactorsThroughStatistic
    (policy : A.EventHistoryActionPolicy)
    (statistic : A.EventHistoryStatistic)
    (actionLaw : Kernel statistic.Value A.ActionBundle) :
    Prop :=
  ∀ time finitePrefix,
    policy.kernel time finitePrefix =
      actionLaw (statistic.valueAt time finitePrefix)

/-- A factorization proof packages the common action law as an action policy
on the statistic's existing `EventInformation` representation.

Terminal zero mass, nonterminal normalization, and legality are inherited
from the raw policy at every represented statistic value.
-/
def FactorsThroughStatistic.toInformationActionPolicy
    {policy : A.EventHistoryActionPolicy}
    {statistic : A.EventHistoryStatistic}
    {actionLaw : Kernel statistic.Value A.ActionBundle}
    (hfactor :
      policy.FactorsThroughStatistic statistic actionLaw) :
    EventInformation.ActionPolicy
      statistic.toEventInformation where
  kernel := fun _ => actionLaw
  terminal_zero := by
    intro time finitePrefix hterminal
    change
      actionLaw (statistic.valueAt time finitePrefix) = 0
    rw [← hfactor time finitePrefix]
    exact
      policy.terminal_zero
        time finitePrefix hterminal
  nonterminal_isProbability := by
    intro time finitePrefix hnonterminal
    change
      IsProbabilityMeasure
        (actionLaw
          (statistic.valueAt time finitePrefix))
    rw [← hfactor time finitePrefix]
    exact
      policy.nonterminal_isProbability
        time finitePrefix hnonterminal
  legal := by
    intro time finitePrefix hnonterminal
    change
      ∀ᵐ stateAction
          ∂actionLaw
            (statistic.valueAt time finitePrefix),
        stateAction ∈
          A.actionFiber
            (latestEventState time finitePrefix)
    rw [← hfactor time finitePrefix]
    exact
      policy.legal
        time finitePrefix hnonterminal

/-- Compiling the statistic-indexed representation obtained from a
factorization proof recovers the original raw policy exactly.
-/
theorem FactorsThroughStatistic.toInformationActionPolicy_compiles
    {policy : A.EventHistoryActionPolicy}
    {statistic : A.EventHistoryStatistic}
    {actionLaw : Kernel statistic.Value A.ActionBundle}
    (hfactor :
      policy.FactorsThroughStatistic statistic actionLaw) :
    hfactor.toInformationActionPolicy.toEventHistoryActionPolicy =
      policy := by
  apply EventHistoryActionPolicy.ext
  funext time
  apply Kernel.ext
  intro finitePrefix
  exact (hfactor time finitePrefix).symm

/-- Factorization through a statistic/action-kernel pair whose resulting
action law is fresh-restart invariant is a sufficient certificate for
root-uniform behavioral action-kernel compatibility.

This is more general than literal statistic invariance: splice-sensitive
statistic components are allowed when the common action kernel ignores their
change.
-/
theorem FactorsThroughStatistic.freshRestartRootedActionKernelCompatible_of_actionLawInvariant
    {policy : A.EventHistoryActionPolicy}
    {statistic : A.EventHistoryStatistic}
    {actionLaw : Kernel statistic.Value A.ActionBundle}
    (hfactor :
      policy.FactorsThroughStatistic statistic actionLaw)
    (hinvariant :
      statistic.IsFreshRestartActionLawInvariant
        actionLaw) :
    policy.IsFreshRestartRootedActionKernelCompatible := by
  intro start initialPrefix offset freshPrefix hrooted
  rw [
    hfactor
      (start + offset)
      (spliceContinuationPrefix
        start initialPrefix offset freshPrefix),
    hfactor offset freshPrefix]
  exact
    hinvariant
      start initialPrefix offset freshPrefix hrooted

/-- Relative to a fixed exact factorization, action-law invariance is exactly
equivalent to root-uniform behavioral action-kernel compatibility.

This converse is conditional on `hfactor`. It does not assert that an
arbitrary compatible policy admits a factorization through the chosen
statistic and action kernel.
-/
theorem FactorsThroughStatistic.isFreshRestartActionLawInvariant_iff_rootedActionKernelCompatible
    {policy : A.EventHistoryActionPolicy}
    {statistic : A.EventHistoryStatistic}
    {actionLaw : Kernel statistic.Value A.ActionBundle}
    (hfactor :
      policy.FactorsThroughStatistic statistic actionLaw) :
    statistic.IsFreshRestartActionLawInvariant actionLaw ↔
      policy.IsFreshRestartRootedActionKernelCompatible := by
  constructor
  · exact
      FactorsThroughStatistic.freshRestartRootedActionKernelCompatible_of_actionLawInvariant
        hfactor
  · intro hcompatible start initialPrefix offset freshPrefix hrooted
    rw [
      ← hfactor
        (start + offset)
        (spliceContinuationPrefix
          start initialPrefix offset freshPrefix),
      ← hfactor offset freshPrefix]
    exact
      hcompatible
        start initialPrefix offset freshPrefix hrooted

/-- Factorization through a literally fresh-restart-invariant measurable
statistic is a sufficient certificate for root-uniform behavioral
action-kernel compatibility.

No converse is asserted: root-uniform compatibility constrains only
fresh/spliced pairs and need not make the policy a function of any particular
chosen statistic.
-/
theorem FactorsThroughStatistic.freshRestartRootedActionKernelCompatible
    {policy : A.EventHistoryActionPolicy}
    {statistic : A.EventHistoryStatistic}
    {actionLaw : Kernel statistic.Value A.ActionBundle}
    (hfactor :
      policy.FactorsThroughStatistic statistic actionLaw)
    (hinvariant :
      statistic.IsFreshRestartInvariant) :
    policy.IsFreshRestartRootedActionKernelCompatible :=
  FactorsThroughStatistic.freshRestartRootedActionKernelCompatible_of_actionLawInvariant
    hfactor (hinvariant.actionLaw actionLaw)

/-- A policy whose action measure is a measurable function only of the latest
state is root-uniform fresh-restart compatible.

This is the direct latest-state specialization of statistic factorization.
It requires only the displayed factorization equation; the policy may have
been constructed through any equivalent interface.
-/
theorem freshRestartRootedActionKernelCompatible_of_latestStateKernel
    {policy : A.EventHistoryActionPolicy}
    (actionLaw : Kernel A.State A.ActionBundle)
    (hfactor :
      ∀ time finitePrefix,
        policy.kernel time finitePrefix =
          actionLaw (latestEventState time finitePrefix)) :
    policy.IsFreshRestartRootedActionKernelCompatible := by
  have hstatistic :
      policy.FactorsThroughStatistic
        (EventHistoryStatistic.latestState A)
        actionLaw := by
    intro time finitePrefix
    exact hfactor time finitePrefix
  exact
    hstatistic.freshRestartRootedActionKernelCompatible
      EventHistoryStatistic.latestState_isFreshRestartInvariant

end EventHistoryActionPolicy

namespace ActionPolicy

/-- The standard embedding of a stationary state-Markov action policy into a
complete-event-history policy factors through the latest-state statistic.
-/
theorem toEventHistoryActionPolicy_factorsThroughLatestState
    (policy : A.ActionPolicy) :
    EventHistoryActionPolicy.FactorsThroughStatistic
      policy.toHistoryActionPolicy.toEventHistoryActionPolicy
      (EventHistoryStatistic.latestState A)
      policy.kernel := by
  intro time finitePrefix
  rfl

/-- The same stationary policy embedding also factors through the richer
clock-and-latest-state statistic when its common action law ignores the clock.
This factorization is useful for the strict separation between statistic
equality and action-law equality.
-/
theorem toEventHistoryActionPolicy_factorsThroughClockAndLatestState
    (policy : A.ActionPolicy) :
    EventHistoryActionPolicy.FactorsThroughStatistic
      policy.toHistoryActionPolicy.toEventHistoryActionPolicy
      (EventHistoryStatistic.clockAndLatestState A)
      (EventHistoryStatistic.actionLawIgnoringClock
        policy.kernel) := by
  intro time finitePrefix
  rfl

/-- Every stationary state-Markov action policy has a root-uniform
fresh-restart-compatible complete-event-history embedding.
-/
theorem toEventHistoryActionPolicy_freshRestartRootedActionKernelCompatible
    (policy : A.ActionPolicy) :
    EventHistoryActionPolicy.IsFreshRestartRootedActionKernelCompatible
      policy.toHistoryActionPolicy.toEventHistoryActionPolicy :=
  EventHistoryActionPolicy.FactorsThroughStatistic.freshRestartRootedActionKernelCompatible
    policy.toEventHistoryActionPolicy_factorsThroughLatestState
    EventHistoryStatistic.latestState_isFreshRestartInvariant

end ActionPolicy

end MeasurableKernelArena
