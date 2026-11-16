/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.KernelBridge

/-!
# Presentation.Chance.Realized — explicit realized-information presentations

The carriers in `ObservedGame` are intentionally representation-neutral: they
do not come with measurable spaces. Consequently there is no unconditional
analytic adapter from every observed chance game to measurable
information-action kernels.

This module states the exact certificate needed by such an adapter. An
`AnalyticPresentation` fixes:

* a measurable event-information statistic on the complete-history analytic
  arena;
* one measurable, history-dependent realization kernel, shared by all
  profiles and deviations;
* a compilation of every behavioral profile to an abstract
  information-indexed realized policy;
* exact equality of the compiled raw event policy with the existing
  behavioral/chance history executor;
* a factorization of player-controlled histories through the original
  `ObservedGame.InfoState`.

The exact raw-policy equality is deliberately part of the presentation
certificate: it is the model-specific measurability and dependent-transport
obligation that cannot be inferred from the unmeasured `ObservedGame`
interface. The generic theorems below then derive exact player and chance
branches, whole state-path equality, and every finite stopped-history law.

No countability, terminal-decidability, standard-Borel, payoff, recall, or
equilibrium assumption is added to the generic realized-information
certificate. The stopped-law comparison theorem separately retains the
old bounded executor's terminal-decidability premise.

## Main definitions

* `ObservedChanceGame.AnalyticPresentation` — a truthful measurable
  presentation and exact compilation certificate.

## Main results

* `AnalyticPresentation.abstractKernel_eq_of_player_infoAt_eq` — one abstract
  law at equal original player information states.
* `AnalyticPresentation.compiled_kernel_of_mover` and
  `compiled_kernel_of_chance` — exact concrete action-bundle branches.
* `AnalyticPresentation.compiled_eventPathMeasure` — exact complete joint
  state/action event-path law.
* `AnalyticPresentation.compiled_statePathMeasure` — exact complete analytic
  state-path law.
* `AnalyticPresentation.compiled_finite_state_law` — exact finite
  stopped-history finite-law measure.
-/

open MeasureTheory ProbabilityTheory

local macro "finiteLawMeasureTop(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
      0)

namespace ExtensiveGame.ObservedChanceGame

universe uN uU uI uC

variable {N : Type uN} {U : Type uU}

/-- The measurable complete-history arena used by the observed-chance
analytic bridge. -/
noncomputable abbrev AnalyticHistoryArena
    (G : ObservedChanceGame N U) : MeasurableKernelArena :=
  (G.observed.base.toArena.historyKernelArena
    G.observed.base.init).toMeasurable

/-- Complete-history states in the discrete-to-analytic lift have measurable
singletons. This is the only singleton assumption consumed by realized-policy
compilation. -/
instance instMeasurableSingletonClassAnalyticHistoryArena
    (G : ObservedChanceGame N U) :
    MeasurableSingletonClass (AnalyticHistoryArena G).State where
  measurableSet_singleton _ :=
    MeasurableSpace.measurableSet_top

/-- A measurable realized-information presentation of an observed chance
game.

The information structure and realization kernel are fixed independently of
the behavioral profile. `toPolicy` may change only the abstract
information-indexed law and its compatibility proofs.

`compiled` is an exact equality of raw joint event policies. It is the
model-specific certificate that all tagged information/action maps,
dependent transports, and finite-law-to-measure families are measurable and have the
claimed semantics. -/
structure AnalyticPresentation
    (G : ObservedChanceGame N U) where
  /-- Fixed measurable information statistic on finite analytic event
  prefixes. -/
  information :
    MeasurableKernelArena.EventInformation.{uI}
      (AnalyticHistoryArena G)
  /-- Fixed history-dependent interpretation of abstract actions. -/
  realization :
    MeasurableKernelArena.EventInformation.ActionRealization.{uC}
      information
  /-- Compile each behavioral profile to an abstract information policy. -/
  toPolicy :
    G.observed.BehavioralProfile →
      MeasurableKernelArena.EventInformation.RealizedActionPolicy
        realization
  /-- Exact equality with the established player/chance raw event executor. -/
  compiled :
    ∀ profile,
      (toPolicy profile).toEventHistoryActionPolicy =
        MeasurableKernelArena.HistoryActionPolicy.toEventHistoryActionPolicy
          (MeasurableKernelArena.ActionPolicy.toHistoryActionPolicy
            (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable)
  /-- Map original player decision information into each time-indexed
  analytic information carrier. Only values represented by player-controlled
  histories are constrained by `player_informationAt`; injectivity on
  unreachable declared information points is not required. -/
  playerInformation :
    (time : ℕ) →
      (Σ i : N, G.observed.InfoState i) →
        information.Information time
  /-- At a player-controlled latest history, analytic information factors
  through the original player's `InfoState`. -/
  player_informationAt :
    ∀ (time : ℕ)
      (events : (AnalyticHistoryArena G).EventPrefix time)
      (i : N)
      (hmover :
        G.observed.base.mover
            (MeasurableKernelArena.latestEventState
              time events).1 =
          some i)
      (hnonterminal :
        ¬ G.observed.base.isTerminal
          (MeasurableKernelArena.latestEventState
            time events).1),
      information.informationAt time events =
        playerInformation time
          ⟨i,
            G.observed.infoAt
              (MeasurableKernelArena.latestEventState
                time events)
              i hmover
              (G.observed.base.toArena.isDecision_of_not_isTerminal _
                hnonterminal)⟩

namespace AnalyticPresentation

variable {G : ObservedChanceGame N U}

/-- The realized presentation's concrete kernel is exactly the established
stationary complete-history kernel, queried at the latest event state. -/
theorem compiled_kernel
    (presentation : AnalyticPresentation G)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time) :
    (presentation.toPolicy profile).toEventHistoryActionPolicy.kernel
        time events =
      (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable.kernel
        (MeasurableKernelArena.latestEventState time events) := by
  rw [presentation.compiled profile]
  rfl

/-- Equal original player information states force exactly equal abstract
action laws, even when the two complete-history analytic states differ. -/
theorem abstractKernel_eq_of_player_infoAt_eq
    (presentation : AnalyticPresentation G)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events₁ events₂ : (AnalyticHistoryArena G).EventPrefix time)
    (i : N)
    (hmover₁ :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState
            time events₁).1 =
        some i)
    (hnonterminal₁ :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events₁).1)
    (hmover₂ :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState
            time events₂).1 =
        some i)
    (hnonterminal₂ :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events₂).1)
    (hsame :
      G.observed.infoAt
          (MeasurableKernelArena.latestEventState time events₁)
          i hmover₁
          (G.observed.base.toArena.isDecision_of_not_isTerminal _
            hnonterminal₁) =
        G.observed.infoAt
          (MeasurableKernelArena.latestEventState time events₂)
          i hmover₂
          (G.observed.base.toArena.isDecision_of_not_isTerminal _
            hnonterminal₂)) :
    (presentation.toPolicy profile).abstractKernel time
        (presentation.information.informationAt time events₁) =
      (presentation.toPolicy profile).abstractKernel time
        (presentation.information.informationAt time events₂) := by
  apply
    (presentation.toPolicy profile).abstractKernel_eq_of_informationAt_eq
  rw [
    presentation.player_informationAt time events₁ i hmover₁
      hnonterminal₁,
    presentation.player_informationAt time events₂ i hmover₂
      hnonterminal₂,
    hsame]

/-- At a player-controlled latest history, the realized presentation's
concrete action-bundle law is exactly the measure associated to the original
information-indexed behavioral law after local `actionEquiv` realization. -/
theorem compiled_kernel_of_mover
    (presentation : AnalyticPresentation G)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
    (i : N)
    (hmover :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        some i) :
    (presentation.toPolicy profile).toEventHistoryActionPolicy.kernel
        time events =
      finiteLawMeasureTop(
        (profile.actionLawAt G.observed
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal).map
          (fun action =>
            (⟨MeasurableKernelArena.latestEventState time events,
              action⟩ :
              (AnalyticHistoryArena G).ActionBundle))) := by
  have hnonterminal' :
      ¬ IsEmpty
        ((G.observed.base.toArena.historyKernelArena
          G.observed.base.init).Action
            (MeasurableKernelArena.latestEventState time events)) :=
    hnonterminal
  rw [presentation.compiled_kernel profile time events]
  rw [
    KernelArena.Policy.toMeasurable_kernel_apply_nonterminal
      _ _ hnonterminal']
  rw [
    BehavioralProfile.toHistoryKernelPolicy_of_mover
      G profile
      (MeasurableKernelArena.latestEventState time events)
      hnonterminal i hmover]
  rfl

/-- At a chance-controlled latest history, the realized presentation's
concrete action-bundle law is exactly the declared chance finite-law measure in the
local history fiber. -/
theorem compiled_kernel_of_chance
    (presentation : AnalyticPresentation G)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    (presentation.toPolicy profile).toEventHistoryActionPolicy.kernel
        time events =
      finiteLawMeasureTop(
        (G.chanceKernel
            (MeasurableKernelArena.latestEventState time events)
            ⟨hmover, hnonterminal⟩).map
          (fun action =>
            (⟨MeasurableKernelArena.latestEventState time events,
              action⟩ :
              (AnalyticHistoryArena G).ActionBundle))) := by
  have hnonterminal' :
      ¬ IsEmpty
        ((G.observed.base.toArena.historyKernelArena
          G.observed.base.init).Action
            (MeasurableKernelArena.latestEventState time events)) :=
    hnonterminal
  rw [presentation.compiled_kernel profile time events]
  rw [
    KernelArena.Policy.toMeasurable_kernel_apply_nonterminal
      _ _ hnonterminal']
  rw [
    BehavioralProfile.toHistoryKernelPolicy_of_chance
      G profile
      (MeasurableKernelArena.latestEventState time events)
      hnonterminal hmover]
  rfl

/-- The complete joint state/action event-path law of a realized presentation
is exactly the event-history embedding of the established stationary
complete-history analytic policy. -/
theorem compiled_eventPathMeasure
    (presentation : AnalyticPresentation G)
    (profile : G.observed.BehavioralProfile)
    (initialHistory :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    (presentation.toPolicy profile).toEventHistoryActionPolicy.pathMeasure
        (G.observed.base.toArena.historyKernelArena
          G.observed.base.init).toMeasurable_measurableSet_terminalSet
        initialHistory =
      MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure
        (MeasurableKernelArena.HistoryActionPolicy.toEventHistoryActionPolicy
          (MeasurableKernelArena.ActionPolicy.toHistoryActionPolicy
            (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable))
          (G.observed.base.toArena.historyKernelArena
            G.observed.base.init).toMeasurable_measurableSet_terminalSet
          initialHistory := by
  rw [presentation.compiled profile]

/-- The complete state-path pushforward of a realized presentation is exactly
the existing stationary complete-history analytic path law. -/
theorem compiled_statePathMeasure
    (presentation : AnalyticPresentation G)
    (profile : G.observed.BehavioralProfile)
    [MeasurableKernelArena.ActionPolicy.PathExecution
      (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable
      (G.observed.base.toArena.historyKernelArena
        G.observed.base.init).toMeasurable_measurableSet_terminalSet]
    (initialHistory :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    (presentation.toPolicy profile).toEventHistoryActionPolicy.statePathMeasure
        (G.observed.base.toArena.historyKernelArena
          G.observed.base.init).toMeasurable_measurableSet_terminalSet
        initialHistory =
      (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable.pathMeasure
        (G.observed.base.toArena.historyKernelArena
          G.observed.base.init).toMeasurable_measurableSet_terminalSet
        initialHistory := by
  rw [presentation.compiled profile]
  rw [
    MeasurableKernelArena.HistoryActionPolicy.toEventHistoryActionPolicy_statePathMeasure]
  rw [
    MeasurableKernelArena.ActionPolicy.toHistoryActionPolicy_pathMeasure]

/-- Every finite state-coordinate marginal of a realized presentation is
exactly the weighted-Dirac interpretation of the original stopped
behavioral/chance history executor. -/
theorem compiled_finite_state_law
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (presentation : AnalyticPresentation G)
    (profile : G.observed.BehavioralProfile)
    (horizon : ℕ)
    (initialHistory :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    Measure.map
        (fun path : ℕ → (AnalyticHistoryArena G).State =>
            path horizon)
        ((presentation.toPolicy profile).toEventHistoryActionPolicy.statePathMeasure
            (G.observed.base.toArena.historyKernelArena
              G.observed.base.init).toMeasurable_measurableSet_terminalSet
            initialHistory) =
      finiteLawMeasureTop(
        G.observed.base.toArena.stochasticHistoryLawFrom
          (BehavioralProfile.toHistoryPolicy G profile)
          initialHistory horizon) := by
  obtain ⟨paths⟩ :=
    MeasurableKernelArena.ActionPolicy.PathExecution.nonempty
      (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable
      (G.observed.base.toArena.historyKernelArena
        G.observed.base.init).toMeasurable_measurableSet_terminalSet
  letI := paths
  obtain ⟨execution⟩ :=
    MeasurableKernelArena.ActionPolicy.EndpointExecution.nonempty
      (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable
      (G.observed.base.toArena.historyKernelArena
        G.observed.base.init).toMeasurable_measurableSet_terminalSet
  letI := execution
  rw [presentation.compiled_statePathMeasure profile initialHistory]
  change (Measure.map (fun path => path horizon)
    (MeasurableKernelArena.ActionPolicy.PathExecution.path
      (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable
      (G.observed.base.toArena.historyKernelArena
        G.observed.base.init).toMeasurable_measurableSet_terminalSet initialHistory)) = _
  rw [← MeasurableKernelArena.ActionPolicy.PathExecution.coordinate_eq]
  change
    (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable.coordinateMeasure
          (G.observed.base.toArena.historyKernelArena
            G.observed.base.init).toMeasurable_measurableSet_terminalSet
          initialHistory horizon =
      _
  rw [
    MeasurableKernelArena.ActionPolicy.coordinateMeasure_eq_endpointMeasure]
  exact
    BehavioralProfile.toMeasurable_endpointMeasure
      G profile horizon initialHistory

end AnalyticPresentation

end ExtensiveGame.ObservedChanceGame
