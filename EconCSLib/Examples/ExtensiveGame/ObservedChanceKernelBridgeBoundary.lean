/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.AbsentMinded
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Structural
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.ObservedEvent
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.KernelBridge

/-!
# Observed-chance analytic bridge and concrete-bundle boundary

This regression instantiates the complete-history analytic bridge on the
absent-minded three-rung game. The same player information state occurs at two
different nonterminal complete histories. An information-indexed behavioral
profile handles this correctly because its law is on the abstract `Unit`
information action and is realized separately at each history.

The second half records the exact boundary of the current analytic
`EventInformation.ActionPolicy`. After histories become analytic states, a
kernel into concrete state/action bundles cannot use one information value at
both player histories: legality would force the same probability measure to
have mass one on two different state fibers. The impossibility proof uses the
general `latestEventState_eq_of_informationAt_eq` theorem rather than relying
on terminal/nonterminal conflicts.

This example therefore verifies both sides of the design:

* the history-state bridge executes the behavioral profile and has the exact
  old finite stopped-history law;
* a future player-information bridge must add abstract actions with
  history-dependent realization instead of identifying concrete bundles.
-/

open MeasureTheory ProbabilityTheory

local macro "finiteLawMeasureTop(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
      0)

namespace Examples.ObservedChanceKernelBridgeBoundary

open Examples.AbsentMinded
open ExtensiveGame

/-- The absent-minded example has no chance nodes. -/
theorem noChance :
    absentMindedGame.base.NoChance := by
  intro state hnonterminal
  cases state with
  | s0 =>
      exact ⟨0, rfl⟩
  | s1 =>
      exact ⟨0, rfl⟩
  | s2 =>
      exact
        (hnonterminal
          (show IsEmpty (absentMindedGame.base.Action Rung.s2) from
            ⟨PEmpty.elim⟩)).elim

/-- View the no-chance absent-minded game through the common chance-aware
behavioral API. -/
def game : _root_.ExtensiveGame.ObservedChanceGame (Fin 1) ℤ :=
  _root_.ExtensiveGame.ObservedChanceGame.ofNoChance
    absentMindedGame noChance.noChanceOnHistories

instance terminalDecidable
    (state : game.observed.base.State) :
    Decidable (game.observed.base.isTerminal state) := by
  cases state with
  | s0 =>
      exact isFalse fun hterminal => hterminal.false ()
  | s1 =>
      exact isFalse fun hterminal => hterminal.false ()
  | s2 =>
      exact isTrue ⟨PEmpty.elim⟩

/-- The unique behavioral profile on the unique abstract information action.
The one abstract law is reused at both player histories. -/
def profile :
    game.observed.BehavioralProfile :=
  fun _ _ => FiniteLaw.pure ()

/-- The lifted policy's player branch at the first decision is exactly the
concrete realization of the information-indexed profile. -/
theorem firstDecision_player_branch :
    _root_.ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
        game profile firstDecision
        (by
          change ¬ IsEmpty Unit
          exact fun hterminal => hterminal.false ()) =
      profile.actionLawAt game.observed firstDecision 0 rfl
        (by
          change ¬ IsEmpty Unit
          exact fun hterminal => hterminal.false ()) := by
  exact
    _root_.ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy_of_mover
      game profile firstDecision
      (by
        change ¬ IsEmpty Unit
        exact fun hterminal => hterminal.false ())
      0 rfl

/-- The bridge gives exact equality of the two-step analytic endpoint measure
and the original stopped-history finite-law measure in the concrete
regression. -/
theorem analytic_two_step_endpoint_exact
    [MeasurableKernelArena.ActionPolicy.EndpointExecution
      (_root_.ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
        game profile).toMeasurable
      (game.observed.base.toArena.historyKernelArena
        game.observed.base.init).toMeasurable_measurableSet_terminalSet] :
    (_root_.ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
      game profile).toMeasurable.endpointMeasure
        (game.observed.base.toArena.historyKernelArena
          game.observed.base.init).toMeasurable_measurableSet_terminalSet
        2 firstDecision =
      finiteLawMeasureTop(
        game.observed.base.toArena.stochasticHistoryLawFrom
          (_root_.ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
            game profile)
          firstDecision 2) :=
  _root_.ExtensiveGame.ObservedChanceGame.BehavioralProfile.toMeasurable_endpointMeasure
    game profile 2 firstDecision

/-- The analytic arena whose states are complete histories of the absent-minded
game. -/
noncomputable abbrev liftedArena : MeasurableKernelArena :=
  (absentMindedGame.base.toArena.historyKernelArena
    absentMindedGame.base.init).toMeasurable

instance liftedArena_stateMeasurableSingleton :
    MeasurableSingletonClass liftedArena.State where
  measurableSet_singleton _ :=
    by
      change
        @MeasurableSet liftedArena.State ⊤
          ({_} : Set liftedArena.State)
      exact MeasurableSpace.measurableSet_top

/-- Time-zero event prefix based at the first player history. -/
def firstPrefix : liftedArena.EventPrefix 0 :=
  fun _ => (firstDecision, Sum.inl ())

/-- Time-zero event prefix based at the second player history. -/
def secondPrefix : liftedArena.EventPrefix 0 :=
  fun _ => (secondDecision, Sum.inl ())

/-- A deliberately merged statistic for the two recurring player decisions.
It is enough to expose the concrete action-bundle obstruction. -/
def mergedDecisionInformation :
    MeasurableKernelArena.EventInformation liftedArena where
  Information := fun _ => Unit
  informationMeasurable := fun _ => ⊤
  informationAt := fun _ _ => ()
  informationAt_measurable := fun _ => measurable_const

@[simp]
theorem mergedDecisionInformation_prefix_eq :
    mergedDecisionInformation.informationAt 0 firstPrefix =
      mergedDecisionInformation.informationAt 0 secondPrefix :=
  rfl

theorem firstPrefix_nonterminal :
    ¬ IsEmpty
      (liftedArena.Action
        (MeasurableKernelArena.latestEventState 0 firstPrefix)) := by
  change ¬ IsEmpty Unit
  exact fun hterminal => hterminal.false ()

theorem secondPrefix_nonterminal :
    ¬ IsEmpty
      (liftedArena.Action
        (MeasurableKernelArena.latestEventState 0 secondPrefix)) := by
  change ¬ IsEmpty Unit
  exact fun hterminal => hterminal.false ()

/-- The two complete histories are genuinely different analytic states even
though the player's decision information state is the same. -/
theorem firstDecision_ne_secondDecision :
    firstDecision ≠ secondDecision := by
  intro heq
  have hendpoint := congrArg Sigma.fst heq
  simp [firstDecision, secondDecision] at hendpoint

/-- No concrete-bundle `EventInformation.ActionPolicy` can represent the
merged recurring player information.

The contradiction uses only the two nonterminal player prefixes. It therefore
isolates the state-fiber problem and does not depend on the merged statistic's
additional treatment of the terminal history. -/
theorem no_concrete_bundle_information_policy :
    ¬ Nonempty
      (MeasurableKernelArena.EventInformation.ActionPolicy
        mergedDecisionInformation) := by
  rintro ⟨policy⟩
  have hstates :=
    policy.latestEventState_eq_of_informationAt_eq
      0 firstPrefix secondPrefix
      firstPrefix_nonterminal secondPrefix_nonterminal
      mergedDecisionInformation_prefix_eq
  apply firstDecision_ne_secondDecision
  simpa [
    firstPrefix, secondPrefix,
    MeasurableKernelArena.latestEventState,
    MeasurableKernelArena.latestEvent,
    MeasurableKernelArena.PathEvent.state,
    MeasurableKernelArena.initialEvent] using hstates

end Examples.ObservedChanceKernelBridgeBoundary
