/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.RealizedInformation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation
import EconCSLib.Math.Probability.FiniteLaw.Measure

/-!
# Analytic semantics of executable realized information

This compatibility leaf proves that the finite realized-information compiler
denotes the existing analytic `realizedKernel`. Its executable owner remains
measure-free.

The analytic information structure, realization, and policy are explicit
inputs. The bridge does not manufacture a measurable kernel from an arbitrary
finite-law-valued function: finite support of every output does not imply
measurability in the input on a general uncountable history space. Instead,
callers provide two local representation conditions:

* the analytic abstract kernel is the pushforward, along a measurable
  equivalence of abstract action carriers, of the finite abstract law;
* the analytic realization kernel at each represented abstract action is the
  weighted-Dirac interpretation of the corresponding finite concrete law.

From these local conditions, `FiniteLaw.measure_map` and
`FiniteLaw.measure_bind` derive equality of the compiled kernels. This file
introduces only correspondence theorems, with no new analytic data owner.

## Main results

* `RealizedActionPolicy.realizedKernel_eq_measure_realizedBundleLaw` — exact
  local equality between analytic composition-product compilation and finite
  `bind`/`map` compilation;
* `RealizedActionPolicy.toEventHistoryPolicy_analyticallyRealizedBy` — the
  compiled analytic event policy realizes the executable one at terminal and
  nonterminal prefixes.
-/

open MeasureTheory ProbabilityTheory

namespace KernelArena

universe uI uC uD

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      Measure.dirac (Prod.fst atom) + rest) 0 atoms

set_option quotPrecheck false in
local notation "μᵇ[" arena "|" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      @Measure.dirac (KernelArena.toMeasurable arena).ActionBundle
        (KernelArena.toMeasurable arena).actionBundleMeasurable
        (Prod.fst atom) + rest)
    0 atoms

namespace EventInformation.RealizedActionPolicy

variable
  {A : KernelArena}
  {information : A.EventInformation}
  {realization : EventInformation.ActionRealization information}

/-- Exact local correspondence between the analytic realized-action kernel
and executable finite `bind`/`map` compilation.

The measurable equivalence permits the analytic model to use a different but
isomorphic abstract-action carrier. Only the abstract law is pushed through
this equivalence; concrete realization remains prefix-dependent. -/
theorem realizedKernel_eq_measure_realizedBundleLaw
    [abstractActionMeasurable :
      ∀ time, MeasurableSpace (realization.AbstractAction time)]
    {analyticInformation : A.toMeasurable.EventInformation}
    {analyticRealization :
      MeasurableKernelArena.EventInformation.ActionRealization
        analyticInformation}
    (policy : EventInformation.RealizedActionPolicy realization)
    (analyticPolicy :
      MeasurableKernelArena.EventInformation.RealizedActionPolicy
        analyticRealization)
    (abstractActionEquiv :
      ∀ time,
        realization.AbstractAction time ≃ᵐ
          analyticRealization.AbstractAction time)
    (abstractKernel_eq :
      ∀ time
        (history : A.toMeasurable.EventPrefix time)
        (hnonterminal :
          ¬ IsEmpty
            (A.Action
              (MeasurableKernelArena.latestEventState time history))),
        analyticPolicy.abstractKernel time
            (analyticInformation.informationAt time history) =
          Measure.map (abstractActionEquiv time)
            μ[(policy.abstractLawAt time
              (EventPrefix.ofAnalytic history)
              (by simpa using hnonterminal)).atoms])
    (realizationKernel_eq :
      ∀ time
        (history : A.toMeasurable.EventPrefix time)
        (abstractAction : realization.AbstractAction time),
        analyticRealization.kernel time
            (history, abstractActionEquiv time abstractAction) =
          μᵇ[A|((realization.realizationLaw time
              (EventPrefix.ofAnalytic history) abstractAction).map
                fun action =>
                  ⟨(EventPrefix.ofAnalytic history).latestState,
                    action⟩).atoms])
    (time : ℕ) (history : A.toMeasurable.EventPrefix time)
    (hnonterminal :
      ¬ IsEmpty
        (A.Action
          (MeasurableKernelArena.latestEventState time history))) :
    analyticPolicy.realizedKernel time history =
      μᵇ[A|(policy.realizedBundleLaw time
        (EventPrefix.ofAnalytic history)
        (by simpa using hnonterminal)).atoms] := by
  letI : MeasurableSpace A.ActionBundle :=
    A.toMeasurable.actionBundleMeasurable
  let finiteHistory : A.EventPrefix time :=
    EventPrefix.ofAnalytic history
  have hfiniteNonterminal :
      ¬ IsEmpty (A.Action finiteHistory.latestState) := by
    simpa only [finiteHistory, EventPrefix.latestState_ofAnalytic] using
      hnonterminal
  let abstractLaw : FiniteLaw (realization.AbstractAction time) :=
    policy.abstractLawAt time finiteHistory hfiniteNonterminal
  let concreteLaw :
      realization.AbstractAction time → FiniteLaw A.ActionBundle :=
    fun abstractAction =>
      (realization.realizationLaw time finiteHistory abstractAction).map
        fun action => ⟨finiteHistory.latestState, action⟩
  let analyticConcreteLaw :
      analyticRealization.AbstractAction time →
        FiniteLaw A.ActionBundle :=
    fun abstractAction =>
      concreteLaw ((abstractActionEquiv time).symm abstractAction)
  have hrealization (abstractAction :
      analyticRealization.AbstractAction time) :
      analyticRealization.kernel time (history, abstractAction) =
        μᵇ[A|(analyticConcreteLaw abstractAction).atoms] := by
    have h := realizationKernel_eq time history
      ((abstractActionEquiv time).symm abstractAction)
    simpa only [MeasurableEquiv.apply_symm_apply,
      analyticConcreteLaw, concreteLaw, finiteHistory] using h
  have hrealizationFunction :
      (fun abstractAction : analyticRealization.AbstractAction time =>
        analyticRealization.kernel time (history, abstractAction)) =
      (fun abstractAction =>
        μᵇ[A|(analyticConcreteLaw abstractAction).atoms]) := by
    funext abstractAction
    exact hrealization abstractAction
  have hconcreteMeasurable :
      Measurable fun abstractAction :
          analyticRealization.AbstractAction time =>
        μᵇ[A|(analyticConcreteLaw abstractAction).atoms] := by
    rw [← hrealizationFunction]
    exact
      (Kernel.sectR (analyticRealization.kernel time) history).measurable
  have hfiniteComposition :
      (abstractLaw.map (abstractActionEquiv time)).bind
          analyticConcreteLaw =
        abstractLaw.bind concreteLaw := by
    rw [FiniteLaw.bind_map]
    congr
    funext abstractAction
    simp [analyticConcreteLaw, concreteLaw]
  have habstract := abstractKernel_eq time history hnonterminal
  change
    analyticPolicy.realizedKernel time history =
      μᵇ[A|(policy.realizedBundleLaw time finiteHistory
        hfiniteNonterminal).atoms]
  rw [MeasurableKernelArena.EventInformation.RealizedActionPolicy.realizedKernel_apply]
  rw [habstract]
  rw [FiniteLaw.measure_map abstractLaw (abstractActionEquiv time)
    (abstractActionEquiv time).measurable]
  rw [hrealizationFunction]
  calc
    _ = μ[((abstractLaw.map (abstractActionEquiv time)).bind
          analyticConcreteLaw).atoms] :=
      FiniteLaw.measure_bind
        (abstractLaw.map (abstractActionEquiv time))
        analyticConcreteLaw hconcreteMeasurable
    _ = μ[(abstractLaw.bind concreteLaw).atoms] := by
      rw [hfiniteComposition]
    _ = μᵇ[A|(policy.realizedBundleLaw time finiteHistory
          hfiniteNonterminal).atoms] := by
      rw [policy.realizedBundleLaw_eq_bind_map]
      rfl

/-- The original analytic event-history policy compiled from a compatible
realized policy denotes the executable event-history policy exactly.

At terminal prefixes both sides have killed action mass. At nonterminal
prefixes this is the local finite `bind` correspondence above. -/
theorem toEventHistoryPolicy_analyticallyRealizedBy
    [abstractActionMeasurable :
      ∀ time, MeasurableSpace (realization.AbstractAction time)]
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    {analyticInformation : A.toMeasurable.EventInformation}
    {analyticRealization :
      MeasurableKernelArena.EventInformation.ActionRealization
        analyticInformation}
    (policy : EventInformation.RealizedActionPolicy realization)
    (analyticPolicy :
      MeasurableKernelArena.EventInformation.RealizedActionPolicy
        analyticRealization)
    (abstractActionEquiv :
      ∀ time,
        realization.AbstractAction time ≃ᵐ
          analyticRealization.AbstractAction time)
    (abstractKernel_eq :
      ∀ time
        (history : A.toMeasurable.EventPrefix time)
        (hnonterminal :
          ¬ IsEmpty
            (A.Action
              (MeasurableKernelArena.latestEventState time history))),
        analyticPolicy.abstractKernel time
            (analyticInformation.informationAt time history) =
          Measure.map (abstractActionEquiv time)
            μ[(policy.abstractLawAt time
              (EventPrefix.ofAnalytic history)
              (by simpa using hnonterminal)).atoms])
    (realizationKernel_eq :
      ∀ time
        (history : A.toMeasurable.EventPrefix time)
        (abstractAction : realization.AbstractAction time),
        analyticRealization.kernel time
            (history, abstractActionEquiv time abstractAction) =
          μᵇ[A|((realization.realizationLaw time
              (EventPrefix.ofAnalytic history) abstractAction).map
                fun action =>
                  ⟨(EventPrefix.ofAnalytic history).latestState,
                    action⟩).atoms]) :
    policy.toEventHistoryPolicy.AnalyticallyRealizedBy
      analyticPolicy.toEventHistoryActionPolicy := by
  intro time history
  let finiteHistory : A.EventPrefix time :=
    EventPrefix.ofAnalytic history
  by_cases hterminal : IsEmpty (A.Action finiteHistory.latestState)
  · have hnone :
        policy.toEventHistoryPolicy.actionLaw? time finiteHistory = none :=
      (KernelArena.EventHistoryPolicy.actionLaw?_eq_none_iff
        policy.toEventHistoryPolicy time finiteHistory).2 hterminal
    rw [hnone]
    have hterminal' :
        IsEmpty
          (A.Action
            (MeasurableKernelArena.latestEventState time history)) := by
      simpa only [finiteHistory, EventPrefix.latestState_ofAnalytic] using
        hterminal
    exact
      analyticPolicy.toEventHistoryActionPolicy.terminal_zero
        time history hterminal'
  · rw [policy.toEventHistoryPolicy.actionLaw?_of_nonterminal
      time finiteHistory hterminal]
    change
      analyticPolicy.toEventHistoryActionPolicy.kernel time history =
        μᵇ[A|(policy.realizedBundleLaw time finiteHistory hterminal).atoms]
    change
      analyticPolicy.realizedKernel time history =
        μᵇ[A|(policy.realizedBundleLaw time finiteHistory hterminal).atoms]
    exact policy.realizedKernel_eq_measure_realizedBundleLaw
      analyticPolicy abstractActionEquiv abstractKernel_eq
        realizationKernel_eq time history (by
          simpa only [finiteHistory,
            EventPrefix.latestState_ofAnalytic] using hterminal)

end EventInformation.RealizedActionPolicy

end KernelArena
