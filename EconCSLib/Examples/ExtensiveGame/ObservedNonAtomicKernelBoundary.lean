/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.ObservedChanceMeasurableUncountableBoundary
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# A genuinely non-atomic observed-EFG behavioral law

This regression reuses the explicit uncountable complete-history model whose
unique player chooses a real number at the root.  It replaces the old
`PMF ℝ` behavioral law by unit-interval volume, represented as a measurable
kernel on the abstract action space `Set.Icc 0 1`.

The unit-interval action is realized as its underlying real action in the
existing dependent root action fiber.  The compiled concrete bundle law is
therefore the pushforward of unit-interval volume.  It is proved not to equal
`PMF.toMeasure p` for any PMF on the legal history/action bundle.

Thus the example crosses the stochastic, rather than merely carrier-size,
boundary: the chosen action law itself is non-atomic.

`RationalIntervals.probability` computes exact rational probabilities of
finite unions of closed rational intervals by inclusion-exclusion. Its
`statePathMeasure_cylinder` theorem identifies those values with the original
complete non-atomic path law. The event descriptor is executable; arbitrary
real comparisons and measure construction stay in the semantic proofs.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Examples.ObservedNonAtomicKernelBoundary

open ExtensiveGame
open MeasurableKernelArena

open ObservedChanceMeasurableUncountableBoundary

abbrev History :=
  ObservedChanceMeasurableUncountableBoundary.History
abbrev HistoryAction :=
  ObservedChanceMeasurableUncountableBoundary.HistoryAction
noncomputable abbrev AnalyticArena :=
  ObservedChanceMeasurableUncountableBoundary.AnalyticArena

local instance : MeasurableSpace History :=
  ObservedChanceMeasurableUncountableBoundary.historyMeasurable

local instance : MeasurableSpace HistoryAction :=
  ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable

local instance : MeasurableSingletonClass HistoryAction where
  measurableSet_singleton bundle := by
    refine
      ⟨({ObservedChanceMeasurableUncountableBoundary.historyActionEquiv
          bundle} : Set ℝ),
        measurableSet_singleton _, ?_⟩
    ext candidate
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact
      ObservedChanceMeasurableUncountableBoundary.historyActionEquiv.injective.eq_iff

/-- Coerce an abstract unit-interval action to the real action carrier used by
the existing realization kernel. -/
def realizationInput (time : ℕ) :
    AnalyticArena.EventPrefix time × Set.Icc (0 : ℝ) 1 →
      AnalyticArena.EventPrefix time × ℝ :=
  fun input => (input.1, input.2.1)

theorem realizationInput_measurable (time : ℕ) :
    Measurable (realizationInput time) :=
  Measurable.prod measurable_fst
    (measurable_subtype_coe.comp measurable_snd)

/-- Reuse the existing history-dependent real-action realization by measurable
comap along the unit-interval inclusion. -/
noncomputable def realizationKernel (time : ℕ) :
    Kernel
      (AnalyticArena.EventPrefix time × Set.Icc (0 : ℝ) 1)
      AnalyticArena.ActionBundle :=
  Kernel.comap
    (ObservedChanceMeasurableUncountableBoundary.realizationKernel time)
    (realizationInput time)
    (realizationInput_measurable time)

instance realizationKernel_isSFinite (time : ℕ) :
    IsSFiniteKernel (realizationKernel time) := by
  letI :
      IsSFiniteKernel
        (ObservedChanceMeasurableUncountableBoundary.realizationKernel
          time) :=
    ObservedChanceMeasurableUncountableBoundary.realization.kernel_isSFinite
      time
  unfold realizationKernel
  infer_instance

@[simp]
theorem realizationKernel_apply_nonterminal
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (action : Set.Icc (0 : ℝ) 1)
    (hnonterminal :
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1) :
    realizationKernel time (events, action) =
      Measure.dirac
        (ObservedChanceMeasurableUncountableBoundary.historyActionDecode
          action.1) := by
  change
    ObservedChanceMeasurableUncountableBoundary.realizationKernel
        time (events, action.1) =
      Measure.dirac
        (ObservedChanceMeasurableUncountableBoundary.historyActionDecode
          action.1)
  exact
    ObservedChanceMeasurableUncountableBoundary.realizationKernel_apply_nonterminal
      time events action.1 hnonterminal

@[simp]
theorem realizationKernel_apply_terminal
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (action : Set.Icc (0 : ℝ) 1)
    (hterminal :
      ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1) :
    realizationKernel time (events, action) = 0 := by
  change
    ObservedChanceMeasurableUncountableBoundary.realizationKernel
      time (events, action.1) = 0
  exact
    ObservedChanceMeasurableUncountableBoundary.realizationKernel_apply_terminal
      time events action.1 hterminal

/-- Fixed realization of unit-interval abstract actions as real concrete
actions. -/
noncomputable def realization :
    EventInformation.ActionRealization
      ObservedChanceMeasurableUncountableBoundary.eventInformation where
  AbstractAction := fun _ => Set.Icc (0 : ℝ) 1
  abstractActionMeasurable := fun _ => inferInstance
  kernel := realizationKernel
  kernel_isSFinite := by
    intro time
    infer_instance

/-- Unit-interval volume at root information and zero mass at terminal
information. -/
noncomputable def abstractMeasure :
    Bool → Measure (Set.Icc (0 : ℝ) 1)
  | false => volume
  | true => 0

/-- Measurable information-indexed non-atomic action kernel. -/
noncomputable def abstractKernel :
    Kernel Bool (Set.Icc (0 : ℝ) 1) :=
  Kernel.ofFunOfCountable abstractMeasure

@[simp]
theorem abstractKernel_false :
    abstractKernel false =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) :=
  rfl

@[simp]
theorem abstractKernel_true :
    abstractKernel true = 0 :=
  rfl

instance abstractKernel_isFinite :
    IsFiniteKernel abstractKernel := by
  refine ⟨⟨1, ENNReal.one_lt_top, ?_⟩⟩
  intro information
  cases information
  · rw [abstractKernel_false]
    exact le_of_eq measure_univ
  · rw [abstractKernel_true]
    simp

/-- A terminal complete history has terminal information. -/
theorem historyInformation_eq_true_of_terminal
    (history : History)
    (hterminal :
      ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        history.1) :
    ObservedChanceMeasurableUncountableBoundary.historyInformation history =
      true := by
  cases hinformation :
      ObservedChanceMeasurableUncountableBoundary.historyInformation history with
  | false =>
      have hroot :
          history.1 = .root :=
        ObservedChanceMeasurableUncountableBoundary.endpoint_root_of_historyInformation_eq_false
          history hinformation
      rw [hroot] at hterminal
      change IsEmpty ℝ at hterminal
      exact (hterminal.false 0).elim
  | true => rfl

/-- The genuinely non-atomic realized policy. -/
noncomputable def policy :
    EventInformation.RealizedActionPolicy realization where
  abstractKernel := fun _ => abstractKernel
  abstractKernel_isSFinite := by
    intro _time
    change IsSFiniteKernel abstractKernel
    letI : IsFiniteKernel abstractKernel :=
      abstractKernel_isFinite
    infer_instance
  terminal_zero := by
    intro _time events hterminal
    change
      abstractKernel
        (ObservedChanceMeasurableUncountableBoundary.historyInformation
          (latestEventState _time events)) =
        0
    rw [
      historyInformation_eq_true_of_terminal
        (latestEventState _time events) hterminal,
      abstractKernel_true]
  nonterminal_isProbability := by
    intro time events hnonterminal
    change
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1 at hnonterminal
    change
      IsProbabilityMeasure
        (abstractKernel
          (ObservedChanceMeasurableUncountableBoundary.historyInformation
            (latestEventState time events)))
    have hroot :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          apply (hnonterminal ?_).elim
          rw [hstate]
          change IsEmpty Empty
          exact ⟨Empty.elim⟩
    rw [
      ObservedChanceMeasurableUncountableBoundary.historyInformation_eq_false_of_endpoint_root
        (latestEventState time events) hroot,
      abstractKernel_false]
    infer_instance
  realization_isProbability := by
    intro time events hnonterminal
    change
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1 at hnonterminal
    exact Filter.Eventually.of_forall fun action => by
      change
        IsProbabilityMeasure
          (realizationKernel time (events, action))
      rw [
        realizationKernel_apply_nonterminal
          time events action hnonterminal]
      constructor
      exact Measure.dirac_apply_of_mem (Set.mem_univ _)
  realization_legal := by
    intro time events hnonterminal
    change
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1 at hnonterminal
    have hendpoint :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          exact
            (hnonterminal (by
              rw [hstate]
              change IsEmpty Empty
              exact ⟨Empty.elim⟩)).elim
    have hroot :
        latestEventState time events =
          ObservedChanceMeasurableUncountableBoundary.rootHistory :=
      ObservedChanceMeasurableUncountableBoundary.eq_rootHistory_of_endpoint_root
        (latestEventState time events) hendpoint
    change
      ∀ᵐ stateAction
          ∂(abstractKernel
              (ObservedChanceMeasurableUncountableBoundary.historyInformation
                (latestEventState time events))).bind
            (Kernel.sectR
              (realizationKernel time) events),
        stateAction ∈
          AnalyticArena.actionFiber
            (latestEventState time events)
    letI : IsProbabilityMeasure
        (abstractKernel
          (ObservedChanceMeasurableUncountableBoundary.historyInformation
            (latestEventState time events))) := by
      rw [
        ObservedChanceMeasurableUncountableBoundary.historyInformation_eq_false_of_endpoint_root
          (latestEventState time events) hendpoint,
        abstractKernel_false]
      infer_instance
    apply
      MeasurableKernelArena.EventInformation.RealizedActionPolicy.ae_bind_mem_actionFiber_of_ae_mass_one
        (abstractKernel
          (ObservedChanceMeasurableUncountableBoundary.historyInformation
            (latestEventState time events)))
        (Kernel.sectR (realizationKernel time) events)
        (latestEventState time events)
    · exact Filter.Eventually.of_forall fun action => by
        rw [
          Kernel.sectR_apply,
          realizationKernel_apply_nonterminal
            time events action hnonterminal]
        constructor
        exact Measure.dirac_apply_of_mem (Set.mem_univ _)
    · exact Filter.Eventually.of_forall fun action => by
        rw [
          Kernel.sectR_apply,
          realizationKernel_apply_nonterminal
            time events action hnonterminal]
        apply Measure.dirac_apply_of_mem
        change
          (ObservedChanceMeasurableUncountableBoundary.historyActionDecode
            action.1).1 =
            latestEventState time events
        rw [
          ObservedChanceMeasurableUncountableBoundary.historyActionDecode_fst,
          hroot]

/-- The observed structural presentation with no chance nodes.  Its fixed
chance kernel is zero because the chance branch is unreachable. -/
noncomputable def presentation :
    ObservedChanceMeasurableUncountableBoundary.game.observed.MeasurableKernelPresentation
      ObservedChanceMeasurableUncountableBoundary.measurableHistoryModel where
  information :=
    ObservedChanceMeasurableUncountableBoundary.eventInformation
  realization := realization
  playerInformation := fun _time _information => false
  player_informationAt := by
    intro time events i hmover _hnonterminal
    have hroot :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          change
            ObservedChanceMeasurableUncountableBoundary.nodeMover _ =
              some i at hmover
          rw [hstate] at hmover
          contradiction
    change
      ObservedChanceMeasurableUncountableBoundary.historyInformation
          (latestEventState time events) =
        false
    exact
      ObservedChanceMeasurableUncountableBoundary.historyInformation_eq_false_of_endpoint_root
        (latestEventState time events) hroot
  chanceKernel := fun _time => 0
  chanceKernel_isSFinite := by
    intro _time
    infer_instance

/-- The non-atomic policy packaged as a behavioral profile.  Chance
consistency is vacuous only because the strict regression has no chance
prefixes. -/
noncomputable def profile :
    presentation.KernelBehavioralProfile where
  policy := policy
  chance_eq := by
    intro time events hnonterminal hmover
    have hroot :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          exact
            (hnonterminal (by
              rw [hstate]
              change IsEmpty Empty
              exact ⟨Empty.elim⟩)).elim
    change
      ObservedChanceMeasurableUncountableBoundary.nodeMover _ =
        none at hmover
    rw [hroot] at hmover
    contradiction

/-- Nature, rather than a player, controls the otherwise identical real-action
root. -/
def chanceMover :
    ObservedChanceMeasurableUncountableBoundary.Node →
      Option Unit
  | .root => none
  | .terminal => none

/-- Structural extensive game for the strict non-atomic chance regression. -/
def chanceBase : ExtensiveGame Unit Unit where
  State := ObservedChanceMeasurableUncountableBoundary.Node
  Action := ObservedChanceMeasurableUncountableBoundary.nodeAction
  next := ObservedChanceMeasurableUncountableBoundary.nodeNext
  init := .root
  mover := chanceMover
  payoff := fun _ _ => ()

/-- No history in `chanceBase` is player-controlled. -/
theorem chanceBase_mover_ne_some
    (history :
      chanceBase.toArena.HistoryFrom chanceBase.init)
    (i : Unit) :
    chanceBase.mover history.1 ≠ some i := by
  cases i
  cases history.1 <;> simp [chanceBase, chanceMover]

/-- Observed structural game whose sole nonterminal node is a chance node.
The player information/action fields are unreachable structural data. -/
def chanceObserved : ObservedGame Unit Unit where
  base := chanceBase
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => ()
  infoAt := fun _history _i _hmover _hnonterminal => ()
  infoAt_observe :=
    fun _history _i _hmover _hnonterminal => rfl
  InfoAction := fun _ _ => ℝ
  actionEquiv := by
    intro history i hmover _hnonterminal
    exact
      (chanceBase_mover_ne_some history i hmover).elim

/-- The chance-controlled game has definitionally the same history dynamics
and therefore reuses the explicit measurable history model. -/
noncomputable def chanceHistoryModel :
    chanceObserved.MeasurableHistoryModel := by
  exact
    { historyMeasurable :=
        ObservedChanceMeasurableUncountableBoundary.historyMeasurable
      historyActionMeasurable :=
        ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
      stateProjection_measurable :=
        ObservedChanceMeasurableUncountableBoundary.stateProjection_measurable
      appendHistory_measurable :=
        ObservedChanceMeasurableUncountableBoundary.appendHistory_measurable
      transition :=
        Kernel.deterministic
          (ObservedGame.appendHistory chanceObserved)
          ObservedChanceMeasurableUncountableBoundary.appendHistory_measurable
      transition_isMarkov := by
        infer_instance
      transition_apply := by
        intro historyAction
        rw [Kernel.deterministic_apply]
      terminalSet_measurable :=
        ObservedChanceMeasurableUncountableBoundary.terminalSet_measurable
      singleton_measurable :=
        ObservedChanceMeasurableUncountableBoundary.singleton_measurable }

/-- Fixed non-atomic chance presentation.  The same unit-interval realized
kernel is now structural chance data rather than a player's strategic law. -/
noncomputable def chancePresentation :
    chanceObserved.MeasurableKernelPresentation
      chanceHistoryModel where
  information :=
    ObservedChanceMeasurableUncountableBoundary.eventInformation
  realization := realization
  playerInformation := fun _time _information => false
  player_informationAt := by
    intro _time events i hmover
    exact
      (chanceBase_mover_ne_some
        (latestEventState _time events) i hmover).elim
  chanceKernel := policy.realizedKernel
  chanceKernel_isSFinite := by
    intro time
    exact
      EventInformation.RealizedActionPolicy.realizedKernel_isSFinite
        policy time

/-- The strict chance profile uses exactly the fixed non-atomic nature law. -/
noncomputable def chanceProfile :
    chancePresentation.KernelBehavioralProfile where
  policy := policy
  chance_eq := by
    intro _time _events _hnonterminal _hmover
    rfl

/-- The concrete initial event prefix used to witness that both strict
regression branches are inhabited. -/
def rootPrefix :
    AnalyticArena.EventPrefix 0 :=
  fun _index =>
    (ObservedChanceMeasurableUncountableBoundary.rootHistory, Sum.inl ())

@[simp]
theorem latestEventState_rootPrefix :
    latestEventState 0 rootPrefix =
      ObservedChanceMeasurableUncountableBoundary.rootHistory :=
  rfl

/-- The represented root is genuinely nonterminal. -/
theorem root_nonterminal :
    ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
      (latestEventState 0 rootPrefix).1 := by
  change ¬ IsEmpty ℝ
  intro hempty
  exact hempty.false 0

/-- The strict player regression really has a player-controlled root. -/
theorem player_root_mover :
    ObservedChanceMeasurableUncountableBoundary.game.observed.base.mover
        (latestEventState 0 rootPrefix).1 =
      some () :=
  rfl

/-- The strict chance regression really has a chance-controlled root. -/
theorem chance_root_mover :
    chanceObserved.base.mover
        (latestEventState 0 rootPrefix).1 =
      none :=
  rfl

/-- Measurable injection from unit-interval actions into legal concrete
history/action bundles. -/
def packageAction (action : Set.Icc (0 : ℝ) 1) :
    HistoryAction :=
  ObservedChanceMeasurableUncountableBoundary.historyActionDecode action.1

theorem packageAction_measurable :
    Measurable packageAction :=
  ObservedChanceMeasurableUncountableBoundary.historyActionMeasurableEquiv.symm.measurable.comp
    measurable_subtype_coe

theorem packageAction_injective :
    Function.Injective packageAction := by
  intro first second heq
  apply Subtype.ext
  have hcode :=
    congrArg
      ObservedChanceMeasurableUncountableBoundary.historyActionCode heq
  simpa [packageAction] using hcode

/-- The compiled concrete root action-bundle law. -/
noncomputable def concreteRootLaw :
    Measure HistoryAction :=
  (volume : Measure (Set.Icc (0 : ℝ) 1)).map packageAction

/-- At every represented nonterminal prefix, compilation preserves the
non-atomic unit-interval law exactly. -/
theorem compiled_player_kernel_exact
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1) :
    profile.compiledPolicy.kernel time events =
      concreteRootLaw := by
  rw [
    ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.compiledPolicy_kernel,
    EventInformation.RealizedActionPolicy.realizedKernel_apply]
  change
    (abstractKernel
        (ObservedChanceMeasurableUncountableBoundary.historyInformation
          (latestEventState time events))).bind
      (fun action =>
        realizationKernel time (events, action)) =
      concreteRootLaw
  have hroot :
      (latestEventState time events).1 = .root := by
    cases hstate : (latestEventState time events).1 with
    | root => rfl
    | terminal =>
        exact
          (hnonterminal (by
            rw [hstate]
            change IsEmpty Empty
            exact ⟨Empty.elim⟩)).elim
  rw [
    ObservedChanceMeasurableUncountableBoundary.historyInformation_eq_false_of_endpoint_root
      (latestEventState time events) hroot,
    abstractKernel_false]
  simp_rw [
    realizationKernel_apply_nonterminal
      time events _ hnonterminal]
  exact
    Measure.bind_dirac_eq_map
      (volume : Measure (Set.Icc (0 : ℝ) 1))
      packageAction_measurable

/-- The same strict law is realized at the genuinely chance-controlled root.
The `hmover` premise rules out a vacuous player-only regression. -/
theorem compiled_chance_kernel_exact
    (time : ℕ)
    (events : chanceHistoryModel.toArena.EventPrefix time)
    (hnonterminal :
      ¬ chanceObserved.base.isTerminal
        (latestEventState time events).1)
    (_hmover :
      chanceObserved.base.mover
          (latestEventState time events).1 =
        none) :
    chanceProfile.compiledPolicy.kernel time events =
      concreteRootLaw := by
  change
    profile.compiledPolicy.kernel time events =
      concreteRootLaw
  exact
    compiled_player_kernel_exact
      time events hnonterminal

/-- The inhabited player root has exactly the non-atomic concrete law. -/
theorem compiled_player_root_kernel_exact :
    profile.compiledPolicy.kernel 0 rootPrefix =
      concreteRootLaw :=
  compiled_player_kernel_exact
    0 rootPrefix root_nonterminal

/-- The inhabited chance root has exactly the non-atomic concrete law. -/
theorem compiled_chance_root_kernel_exact :
    chanceProfile.compiledPolicy.kernel 0 rootPrefix =
      concreteRootLaw :=
  compiled_chance_kernel_exact
    0 rootPrefix root_nonterminal chance_root_mover

instance concreteRootLaw_noAtoms :
    NoAtoms concreteRootLaw where
  measure_singleton bundle := by
    rw [
      concreteRootLaw,
      Measure.map_apply
        packageAction_measurable
        (measurableSet_singleton bundle)]
    exact
      Set.Subsingleton.measure_zero
        (by
          intro first hfirst second hsecond
          apply packageAction_injective
          exact hfirst.trans hsecond.symm)
        (volume : Measure (Set.Icc (0 : ℝ) 1))

/-- Every singleton concrete action bundle has probability zero. -/
theorem concreteRootLaw_singleton
    (bundle : HistoryAction) :
    concreteRootLaw {bundle} = 0 :=
  measure_singleton bundle

/-- The compiled root action law is not the measure associated with any PMF
on the legal history/action bundle. -/
theorem no_discretePMF_concreteRootLaw :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        concreteRootLaw := by
  rintro ⟨p, hp⟩
  have hsupportOne :
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p p.support =
        1 :=
    (p.toMeasure_apply_eq_one_iff
      p.support_countable.measurableSet).mpr Set.Subset.rfl
  have hsupportZero :
      concreteRootLaw p.support = 0 :=
    p.support_countable.measure_zero concreteRootLaw
  rw [hp, hsupportZero] at hsupportOne
  exact zero_ne_one hsupportOne

/-- Consequently, the compiled player kernel itself has no PMF
representation. -/
theorem no_discretePMF_compiled_player_kernel
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ ObservedChanceMeasurableUncountableBoundary.game.observed.base.isTerminal
        (latestEventState time events).1) :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        profile.compiledPolicy.kernel time events := by
  simpa only [compiled_player_kernel_exact time events hnonterminal] using
    no_discretePMF_concreteRootLaw

/-- The strict chance kernel also has no PMF representation. -/
theorem no_discretePMF_compiled_chance_kernel
    (time : ℕ)
    (events : chanceHistoryModel.toArena.EventPrefix time)
    (hnonterminal :
      ¬ chanceObserved.base.isTerminal
        (latestEventState time events).1)
    (hmover :
      chanceObserved.base.mover
          (latestEventState time events).1 =
        none) :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        chanceProfile.compiledPolicy.kernel time events := by
  simpa only [
    compiled_chance_kernel_exact
      time events hnonterminal hmover] using
    no_discretePMF_concreteRootLaw

/-- The inhabited player-root kernel has no PMF representation. -/
theorem no_discretePMF_compiled_player_root_kernel :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        profile.compiledPolicy.kernel 0 rootPrefix := by
  simpa only [compiled_player_root_kernel_exact] using
    no_discretePMF_concreteRootLaw

/-- The inhabited chance-root kernel has no PMF representation. -/
theorem no_discretePMF_compiled_chance_root_kernel :
    ¬ ∃ p : PMF HistoryAction,
      @PMF.toMeasure
          HistoryAction
          ObservedChanceMeasurableUncountableBoundary.historyActionMeasurable
          p =
        chanceProfile.compiledPolicy.kernel 0 rootPrefix := by
  simpa only [compiled_chance_root_kernel_exact] using
    no_discretePMF_concreteRootLaw

/-- The general executor produces a complete joint event-path law for the
non-atomic behavioral profile. -/
noncomputable def eventPathMeasure :
    Measure (ℕ → AnalyticArena.PathEvent) :=
  profile.eventPathMeasure
    ObservedChanceMeasurableUncountableBoundary.rootHistory

/-- The corresponding complete state-path law. -/
noncomputable def statePathMeasure :
    Measure (ℕ → AnalyticArena.State) :=
  profile.statePathMeasure
    ObservedChanceMeasurableUncountableBoundary.rootHistory

/-- Read a complete history as a unit-interval action, using zero at the root
and clamping structurally possible out-of-range terminal actions.  On paths
generated by `profile`, the clamp is the identity. The value uses the
computable lattice operations on real Cauchy sequences; the order bounds
are needed only in its proof field. -/
def historyUnitAction :
    History → Set.Icc (0 : ℝ) 1 :=
  Sum.elim
      (fun _ : Unit => ⟨0, by norm_num⟩)
      (fun x => ⟨max 0 (min 1 x),
        le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩) ∘
    ObservedChanceMeasurableUncountableBoundary.historyCode

/-- The executable observation is exactly the original interval projection,
including on histories outside the support of the generated path law. -/
theorem historyUnitAction_eq_projIcc :
    historyUnitAction =
      Sum.elim (fun _ : Unit => ⟨0, by norm_num⟩)
        (Set.projIcc 0 1 zero_le_one) ∘
      ObservedChanceMeasurableUncountableBoundary.historyCode := rfl

/-- The history-to-unit-action observation is measurable. -/
theorem historyUnitAction_measurable :
    Measurable historyUnitAction := by
  rw [historyUnitAction_eq_projIcc]
  apply Measurable.comp
  · have hzero :
        @Measurable
          Unit (Set.Icc (0 : ℝ) 1)
          PUnit.instMeasurableSpace
          inferInstance
          (fun _ : Unit => ⟨0, by norm_num⟩) :=
        measurable_const
    exact
      Measurable.sumElim hzero
        continuous_projIcc.measurable
  · exact
      historyMeasurableEquiv.measurable

@[simp]
theorem historyUnitAction_terminal
    (action : Set.Icc (0 : ℝ) 1) :
    historyUnitAction
        (terminalHistory action.1) =
      action := by
  simp only [historyUnitAction, Function.comp_apply,
    historyCode_terminal,
    Sum.elim_inr]
  exact Set.projIcc_of_mem zero_le_one action.2

@[simp]
theorem appendHistory_packageAction
    (action : Set.Icc (0 : ℝ) 1) :
    ObservedGame.appendHistory
        game.observed
        (packageAction action) =
      terminalHistory action.1 :=
  rfl

/-- The represented terminal set is measurable. -/
theorem analyticTerminalSet_measurable :
    MeasurableSet AnalyticArena.terminalSet :=
  measurableHistoryModel.toArena_terminalSet_measurable

/-- The first generated state coordinate, interpreted as a unit-interval
action, has exactly unit-interval volume law. -/
theorem stateCoordinateMeasure_one_map_historyUnitAction :
    (profile.compiledPolicy.stateCoordinateMeasure
        analyticTerminalSet_measurable
        rootHistory
        1).map historyUnitAction =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  have hcoordinate :=
    profile.compiledPolicy.stateCoordinateMeasure_one_of_nonterminal
      analyticTerminalSet_measurable
      rootHistory
      (by
        change ¬ IsEmpty ℝ
        intro hempty
        exact hempty.false 0)
  have hrootPrefix :
      (fun _index : Finset.Iic 0 =>
        AnalyticArena.initialEvent rootHistory) =
        rootPrefix :=
    rfl
  rw [hrootPrefix, compiled_player_root_kernel_exact] at hcoordinate
  rw [hcoordinate]
  change
    ((Kernel.deterministic
        (ObservedGame.appendHistory
          game.observed)
        appendHistory_measurable) ∘ₘ
      concreteRootLaw).map historyUnitAction =
        (volume : Measure (Set.Icc (0 : ℝ) 1))
  rw [Measure.deterministic_comp_eq_map
    appendHistory_measurable]
  rw [concreteRootLaw]
  rw [Measure.map_map
    appendHistory_measurable
    packageAction_measurable]
  rw [Measure.map_map
    historyUnitAction_measurable
    (appendHistory_measurable.comp packageAction_measurable)]
  have hidentity :
      historyUnitAction ∘
          ObservedGame.appendHistory
            game.observed ∘
        packageAction =
      id := by
    funext action
    simp
  rw [hidentity, Measure.map_id]

/-- The midpoint of the unit interval, constructed from an exact rational. -/
def halfAction : Set.Icc (0 : ℝ) 1 :=
  ⟨((1 / 2 : ℚ) : ℝ), by norm_num⟩

/-- The rational construction is the same real midpoint. -/
@[simp]
theorem halfAction_coe : (halfAction : ℝ) = 1 / 2 := by
  norm_num [halfAction]

/-- The left endpoint of the unit interval. -/
def zeroAction : Set.Icc (0 : ℝ) 1 :=
  ⟨0, by norm_num⟩

/-- The right endpoint of the unit interval. -/
def oneAction : Set.Icc (0 : ℝ) 1 :=
  ⟨1, by norm_num⟩

/-- Histories whose interpreted unit action lies in the lower half. -/
def lowerHalfHistoryEvent : Set History :=
  historyUnitAction ⁻¹' Set.Iic halfAction

/-- A genuine one-coordinate cylinder event on the generated state path. -/
def lowerHalfCylinder :
    Set (ℕ → AnalyticArena.State) :=
  (fun path => path 1) ⁻¹' lowerHalfHistoryEvent

/-- The lower-half cylinder is measurable. -/
theorem lowerHalfCylinder_measurable :
    MeasurableSet lowerHalfCylinder :=
  (measurableSet_Iic.preimage historyUnitAction_measurable).preimage
    (measurable_pi_apply 1)

/-- The lower-half cylinder is inhabited. -/
theorem lowerHalfCylinder_nonempty :
    lowerHalfCylinder.Nonempty := by
  refine
    ⟨fun _time =>
      terminalHistory zeroAction.1,
      ?_⟩
  change
    historyUnitAction (terminalHistory zeroAction.1) ∈
      Set.Iic halfAction
  rw [historyUnitAction_terminal]
  norm_num [zeroAction, halfAction]

/-- The lower-half cylinder is a proper event. -/
theorem lowerHalfCylinder_ne_univ :
    lowerHalfCylinder ≠ Set.univ := by
  intro huniv
  have hmem :
      (fun _time =>
        terminalHistory oneAction.1) ∈
        lowerHalfCylinder := by
    rw [huniv]
    exact Set.mem_univ _
  change
    historyUnitAction (terminalHistory oneAction.1) ∈
      Set.Iic halfAction at hmem
  rw [historyUnitAction_terminal] at hmem
  have himpossible : (1 : ℝ) ≤ 1 / 2 := by
    change (1 : ℝ) ≤ (halfAction : ℝ) at hmem
    simpa only [halfAction_coe] using hmem
  norm_num at himpossible

/-- The lower-half cylinder is not empty. -/
theorem lowerHalfCylinder_ne_empty :
    lowerHalfCylinder ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp lowerHalfCylinder_nonempty

/-- The actual generated non-atomic state-path law assigns probability
one-half to the lower-half cylinder. -/
theorem statePathMeasure_lowerHalfCylinder :
    statePathMeasure lowerHalfCylinder =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  change
    profile.compiledPolicy.statePathMeasure
        analyticTerminalSet_measurable
        rootHistory
        lowerHalfCylinder =
      ENNReal.ofReal (1 / 2 : ℝ)
  calc
    _ =
        profile.compiledPolicy.stateCoordinateMeasure
          analyticTerminalSet_measurable
          rootHistory
          1 lowerHalfHistoryEvent := by
      rw [MeasurableKernelArena.EventHistoryActionPolicy.stateCoordinateMeasure]
      unfold lowerHalfCylinder
      exact
        (Measure.map_apply
          (measurable_pi_apply 1)
          (measurableSet_Iic.preimage
            historyUnitAction_measurable)).symm
    _ =
        ((profile.compiledPolicy.stateCoordinateMeasure
          analyticTerminalSet_measurable
          rootHistory
          1).map historyUnitAction)
            (Set.Iic halfAction) := by
      unfold lowerHalfHistoryEvent
      exact
        (Measure.map_apply historyUnitAction_measurable
          measurableSet_Iic).symm
    _ = (volume : Measure (Set.Icc (0 : ℝ) 1))
          (Set.Iic halfAction) := by
      rw [stateCoordinateMeasure_one_map_historyUnitAction]
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by
      simp [unitInterval.volume_Iic]

/-- The nontrivial cylinder probability is strictly positive. -/
theorem statePathMeasure_lowerHalfCylinder_pos :
    0 < statePathMeasure lowerHalfCylinder := by
  rw [statePathMeasure_lowerHalfCylinder]
  positivity

/-- The nontrivial cylinder probability is strictly below one. -/
theorem statePathMeasure_lowerHalfCylinder_lt_one :
    statePathMeasure lowerHalfCylinder < 1 := by
  rw [statePathMeasure_lowerHalfCylinder]
  norm_num

/-- A measurable total winning event on the real non-atomic state-path
carrier. It represents the logical objective in which the unique player wins
every legal realization of this presentation. -/
def winningStatePathEvent :
    Set (ℕ → AnalyticArena.State) :=
  Set.univ

/-- The non-atomic regression's winning event is measurable. -/
theorem winningStatePathEvent_measurable :
    MeasurableSet winningStatePathEvent :=
  MeasurableSet.univ

/-- The complete state-path law generated by the non-atomic kernel is a
probability measure, not merely an arbitrary measure. -/
instance statePathMeasure_isProbability :
    IsProbabilityMeasure statePathMeasure := by
  unfold statePathMeasure
  unfold
    ExtensiveGame.ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.statePathMeasure
  infer_instance

/-- The measurable total objective holds almost surely under the actual
non-atomic complete state-path law. -/
theorem winningStatePathEvent_almostSure :
    ∀ᵐ path ∂statePathMeasure,
      path ∈ winningStatePathEvent :=
  Filter.Eventually.of_forall (fun _path => Set.mem_univ _)

/-- Equivalently, the actual non-atomic law assigns probability one to the
measurable winning event. -/
theorem winningStatePathEvent_measure_eq_one :
    statePathMeasure winningStatePathEvent = 1 := by
  simp [winningStatePathEvent]

namespace RationalIntervals

/-- A closed rational interval, intersected with the unit interval. Reversed
endpoints represent the empty event. -/
def intervalEvent (bounds : ℚ × ℚ) : Set (Set.Icc (0 : ℝ) 1) :=
  {x | (bounds.1 : ℝ) ≤ x.val ∧ x.val ≤ (bounds.2 : ℝ)}

/-- Exact mass of a closed rational interval under uniform unit-interval volume. -/
def intervalMass (bounds : ℚ × ℚ) : ℚ :=
  max 0 (min 1 bounds.2 - max 0 bounds.1)

/-- Intersection keeps the greater lower bound and the smaller upper bound. -/
def intersect (left right : ℚ × ℚ) : ℚ × ℚ :=
  (max left.1 right.1, min left.2 right.2)

/-- Event described by a finite union of closed rational intervals. -/
def event : List (ℚ × ℚ) → Set (Set.Icc (0 : ℝ) 1)
  | [] => ∅
  | head :: tail => intervalEvent head ∪ event tail

/-- Exact union probability by finite inclusion-exclusion. Intersections of
intervals remain intervals, so every recursive call reduces the list length.
Overlapping, duplicate, reversed, and out-of-range intervals are allowed. -/
def probability : List (ℚ × ℚ) → ℚ
  | [] => 0
  | head :: tail => intervalMass head + probability tail -
      probability (tail.map (intersect head))
termination_by intervals => intervals.length

/-- Every rational interval event is measurable. -/
theorem intervalEvent_measurable (bounds : ℚ × ℚ) :
    MeasurableSet (intervalEvent bounds) :=
  (measurableSet_Ici.preimage measurable_subtype_coe).inter
    (measurableSet_Iic.preimage measurable_subtype_coe)

/-- The compiled finite union is measurable without a runtime real comparison. -/
theorem event_measurable (intervals : List (ℚ × ℚ)) : MeasurableSet (event intervals) := by
  induction intervals with
  | nil => exact MeasurableSet.empty
  | cons head tail ih => exact (intervalEvent_measurable head).union ih

/-- Computing endpoint intersections preserves the represented event exactly. -/
theorem intervalEvent_intersect (left right : ℚ × ℚ) :
    intervalEvent (intersect left right) = intervalEvent left ∩ intervalEvent right := by
  ext x
  simp only [intervalEvent, intersect, Set.mem_setOf_eq, Rat.cast_max, Rat.cast_min,
    max_le_iff, le_min_iff, Set.mem_inter_iff]
  tauto

/-- Intersecting a finite interval description distributes over its union. -/
theorem event_map_intersect (head : ℚ × ℚ) (tail : List (ℚ × ℚ)) :
    event (tail.map (intersect head)) = intervalEvent head ∩ event tail := by
  induction tail with
  | nil => simp [event]
  | cons other tail ih =>
    simp only [List.map_cons, event, intervalEvent_intersect, ih, Set.inter_union_distrib_left]

/-- The clipped rational length is the original unit-interval measure. -/
theorem intervalMass_eq_volume (bounds : ℚ × ℚ) :
    (volume : Measure (Set.Icc (0 : ℝ) 1)).real (intervalEvent bounds) =
      (intervalMass bounds : ℝ) := by
  have himage : Subtype.val '' intervalEvent bounds =
      Set.Icc (max 0 (bounds.1 : ℝ)) (min 1 (bounds.2 : ℝ)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨max_le y.property.1 hy.1, le_min y.property.2 hy.2⟩
    · rintro ⟨hl, hu⟩
      exact ⟨⟨x, (le_max_left _ _).trans hl, hu.trans (min_le_left _ _)⟩,
        ⟨(le_max_right _ _).trans hl, hu.trans (min_le_right _ _)⟩, rfl⟩
  rw [Measure.real, unitInterval.volume_apply, himage, Real.volume_Icc,
    ENNReal.toReal_ofReal']
  simp [intervalMass, Rat.cast_max, Rat.cast_min, max_comm]

/-- The executable inclusion-exclusion result is exactly the original
non-atomic probability; neither disjointness nor ordered endpoints are inputs. -/
theorem probability_eq_volume (intervals : List (ℚ × ℚ)) :
    (volume : Measure (Set.Icc (0 : ℝ) 1)).real (event intervals) =
      (probability intervals : ℝ) := by
  induction intervals using probability.induct with
  | case1 => simp [event, probability]
  | case2 head tail ihTail ihInter =>
    simp only [List.attach_map_val] at ihInter
    have h := measureReal_union_add_inter (μ := (volume : Measure (Set.Icc (0 : ℝ) 1)))
      (s := intervalEvent head) (event_measurable tail)
    rw [← event_map_intersect, ihInter, intervalMass_eq_volume, ihTail] at h
    simp only [event, probability, Rat.cast_sub, Rat.cast_add]
    linarith

/-- Exact nonnegative probability in the original extended-real measure carrier. -/
theorem volume_event (intervals : List (ℚ × ℚ)) :
    (volume : Measure (Set.Icc (0 : ℝ) 1)) (event intervals) =
      ENNReal.ofReal (probability intervals : ℝ) := by
  rw [← probability_eq_volume, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The computed signed inclusion-exclusion expression is nonnegative. -/
theorem probability_nonneg (intervals : List (ℚ × ℚ)) :
    0 ≤ probability intervals := by
  have h : (0 : ℝ) ≤ (probability intervals : ℝ) := by
    rw [← probability_eq_volume]
    exact measureReal_nonneg
  exact_mod_cast h

/-- The computed event probability is at most one. -/
theorem probability_le_one (intervals : List (ℚ × ℚ)) :
    probability intervals ≤ 1 := by
  have h : (probability intervals : ℝ) ≤ 1 := by
    rw [← probability_eq_volume]
    exact measureReal_le_one
  exact_mod_cast h

/-- A coordinate-one cylinder described by rational intervals of the observed
unit action. Its descriptor is finite even though the path law is non-atomic. -/
def cylinder (intervals : List (ℚ × ℚ)) : Set (ℕ → AnalyticArena.State) :=
  (fun path => historyUnitAction (path 1)) ⁻¹' event intervals

/-- The represented cylinder is measurable. -/
theorem cylinder_measurable (intervals : List (ℚ × ℚ)) :
    MeasurableSet (cylinder intervals) :=
  (event_measurable intervals).preimage
    (historyUnitAction_measurable.comp (measurable_pi_apply 1))

/-- The rational algorithm computes the probability under the existing
complete non-atomic state-path law, with no supplied probability certificate. -/
theorem statePathMeasure_cylinder (intervals : List (ℚ × ℚ)) :
    statePathMeasure (cylinder intervals) =
      ENNReal.ofReal (probability intervals : ℝ) := by
  let root := ObservedChanceMeasurableUncountableBoundary.rootHistory
  calc
    _ = profile.compiledPolicy.stateCoordinateMeasure analyticTerminalSet_measurable
        root 1 (historyUnitAction ⁻¹' event intervals) := by
      rw [MeasurableKernelArena.EventHistoryActionPolicy.stateCoordinateMeasure]
      exact (Measure.map_apply (measurable_pi_apply 1)
        ((event_measurable intervals).preimage historyUnitAction_measurable)).symm
    _ = ((profile.compiledPolicy.stateCoordinateMeasure analyticTerminalSet_measurable
        root 1).map historyUnitAction) (event intervals) :=
      (Measure.map_apply historyUnitAction_measurable (event_measurable intervals)).symm
    _ = (volume : Measure (Set.Icc (0 : ℝ) 1)) (event intervals) := by
      rw [stateCoordinateMeasure_one_map_historyUnitAction]
    _ = _ := volume_event intervals

/-- Empty, overlapping, repeated, disjoint, clipped, reversed, singleton, and
full-cover descriptors all retain their set-union semantics. -/
theorem probability_regression :
    probability [] = 0 ∧
    probability [(0, 1/2), (1/4, 3/4)] = 3/4 ∧
    probability [(0, 1/2), (0, 1/2)] = 1/2 ∧
    probability [(0, 1/4), (3/4, 1)] = 1/2 ∧
    probability [(-2, 1/3), (2, 4)] = 1/3 ∧
    probability [(3/4, 1/4)] = 0 ∧
    probability [(1/2, 1/2)] = 0 ∧
    probability [(-1, 2)] = 1 ∧
    probability [(0, 1/2), (1/2, 1)] = 1 := by norm_num [probability, intervalMass, intersect]

#eval show IO Unit from do
  let descriptions : List (List (ℚ × ℚ)) :=
    [[], [(0, 1/2), (1/4, 3/4)], [(0, 1/2), (0, 1/2)],
      [(0, 1/4), (3/4, 1)], [(-2, 1/3), (2, 4)], [(3/4, 1/4)],
      [(1/2, 1/2)], [(-1, 2)], [(0, 1/2), (1/2, 1)]]
  unless descriptions.map probability == [0, 3/4, 1/2, 1/2, 1/3, 0, 0, 1, 1] do
    throw (IO.userError "rational interval union probability regression")

/-- The existing abstract information law kills terminal mass and uses the
computed non-atomic interval probability at the root information value. -/
def abstractProbability (information : Bool) (intervals : List (ℚ × ℚ)) : ℚ :=
  if information then 0 else probability intervals

/-- The executable query agrees with the original information-indexed measure,
including its zero-mass terminal branch. -/
theorem abstractProbability_eq (information : Bool) (intervals : List (ℚ × ℚ)) :
    abstractMeasure information (event intervals) =
      ENNReal.ofReal (abstractProbability information intervals : ℝ) := by
  cases information <;> simp [abstractProbability, abstractMeasure, volume_event]

end RationalIntervals

end Examples.ObservedNonAtomicKernelBoundary
