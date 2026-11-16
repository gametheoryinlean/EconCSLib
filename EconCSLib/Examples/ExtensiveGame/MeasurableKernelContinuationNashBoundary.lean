/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Observed

/-!
# Root Nash versus absolute-prefix continuation optimality

This finite one-player game has a root action that immediately earns the
maximal payoff and an off-path action that enters a second decision node.
The baseline profile chooses the maximal root action, but chooses the bad
action at the second node. A certified replacement strategy chooses the good
action at both nodes.

The regression proves:

* the baseline is Nash at the empty initial history, against every admitted
  measurable unilateral deviation;
* at the canonical absolute-prefix continuation from the off-path second
  history, the certified replacement raises expected payoff from zero to one;
* consequently the baseline is not measurable-kernel subgame perfect.

Every carrier is finite, every transition is deterministic, and every
relevant path terminates after one future step. The strict gap is therefore a
game-theoretic refinement gap, not a measurability, conditioning, or
nontermination artifact.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.MeasurableKernelContinuationNashBoundary

open ExtensiveGame
open MeasurableKernelArena

/-! ## Finite off-path decision game -/

/-- Root, off-path second decision, and two payoff-labelled terminal states.
-/
inductive Node
  | root
  | second
  | terminalBad
  | terminalGood
  deriving DecidableEq

/-- Both decision nodes admit Boolean actions; terminal nodes admit none. -/
def nodeAction : Node → Type
  | .root => Bool
  | .second => Bool
  | .terminalBad => Empty
  | .terminalGood => Empty

/-- At the root, `true` terminates well while `false` enters the off-path
decision. At the second node, the Boolean action selects the terminal payoff.
-/
def nodeNext : (state : Node) → nodeAction state → Node
  | .root, false => .second
  | .root, true => .terminalGood
  | .second, false => .terminalBad
  | .second, true => .terminalGood
  | .terminalBad, action => nomatch action
  | .terminalGood, action => nomatch action

/-- The unique player controls both decision nodes. -/
def nodeMover : Node → Option Unit
  | .root => some ()
  | .second => some ()
  | .terminalBad => none
  | .terminalGood => none

/-- Payoff is one exactly at the good terminal state. -/
def nodePayoff : Node → Unit → ℝ
  | .root, _ => 0
  | .second, _ => 0
  | .terminalBad, _ => 0
  | .terminalGood, _ => 1

/-- Underlying one-player finite extensive game. -/
def base : ExtensiveGame Unit ℝ where
  State := Node
  Action := nodeAction
  next := nodeNext
  init := .root
  mover := nodeMover
  payoff := nodePayoff

abbrev BaseHistory :=
  base.toArena.HistoryFrom base.init

local instance baseHistoryMeasurable :
    MeasurableSpace BaseHistory :=
  ⊤

/-- Empty root history. -/
def rootHistory : BaseHistory :=
  Arena.HistoryFrom.nil base.toArena base.init

/-- Off-path history reached by the root action `false`. -/
def secondHistory : BaseHistory :=
  ⟨.second, rootHistory.2.snoc false⟩

/-- Good terminal history reached directly from the root. -/
def rootGoodHistory : BaseHistory :=
  ⟨.terminalGood, rootHistory.2.snoc true⟩

/-- Bad terminal history reached from the second decision. -/
def secondBadHistory : BaseHistory :=
  ⟨.terminalBad, secondHistory.2.snoc false⟩

/-- Good terminal history reached from the second decision. -/
def secondGoodHistory : BaseHistory :=
  ⟨.terminalGood, secondHistory.2.snoc true⟩

/-- A complete history ending at the root is the empty history. -/
theorem eq_rootHistory_of_endpoint_root
    (history : BaseHistory)
    (hroot : history.1 = .root) :
    history = rootHistory := by
  rcases history with ⟨state, path⟩
  cases path with
  | nil => rfl
  | @snoc previous path action =>
      cases previous with
      | root =>
          cases action <;> contradiction
      | second =>
          cases action <;> contradiction
      | terminalBad =>
          exact Empty.elim action
      | terminalGood =>
          exact Empty.elim action

/-- A complete history ending at the second decision is the unique
root-`false` history. -/
theorem eq_secondHistory_of_endpoint_second
    (history : BaseHistory)
    (hsecond : history.1 = .second) :
    history = secondHistory := by
  rcases history with ⟨state, path⟩
  cases path with
  | nil => contradiction
  | @snoc previous path action =>
      cases previous with
      | root =>
          have hprevious :
              (⟨.root, path⟩ : BaseHistory) =
                rootHistory :=
            eq_rootHistory_of_endpoint_root
              ⟨.root, path⟩ rfl
          cases action with
          | false =>
              cases hprevious
              rfl
          | true =>
              contradiction
      | second =>
          cases action <;> contradiction
      | terminalBad =>
          exact Empty.elim action
      | terminalGood =>
          exact Empty.elim action

/-! ## Observed measurable history presentation -/

/-- Perfect-information observation layer retaining the complete base
history. Every complete history is declared a subgame root. -/
def observed : ObservedGame Unit ℝ :=
  ObservedGame.historyInformation base
    (ObservedGame.CompleteInformation.PublicObservationPresentation.trivial
      base)

/-- Explicit all-history continuation-root presentation for this analysis. -/
def observedRoots : observed.RootPresentation where
  IsRoot := fun _history => True
  init_isRoot := trivial

/-- The external presentation exposes every history as a root. -/
example (history : BaseHistory) :
    observedRoots.IsRoot history :=
  trivial

abbrev History := ObservedGame.CompleteHistory observed

/-- Exact discrete measurable model of the finite complete-history system. -/
noncomputable def historyModel :
    observed.MeasurableHistoryModel :=
  ObservedGame.MeasurableHistoryModel.discrete observed

local instance historyMeasurable : MeasurableSpace History :=
  ⊤

local instance historyMeasurableSingletonClass :
    MeasurableSingletonClass History where
  measurableSet_singleton :=
    historyModel.singleton_measurable

noncomputable abbrev AnalyticArena := historyModel.toArena

local instance actionBundleMeasurableSingletonClass :
    MeasurableSingletonClass AnalyticArena.ActionBundle where
  measurableSet_singleton := by
    intro _
    exact MeasurableSpace.measurableSet_top

/-- Common analytic information is the latest complete history. -/
def eventInformation :
    AnalyticArena.EventInformation where
  Information := fun _ => History
  informationMeasurable := fun _ =>
    ⊤
  informationAt := fun time events =>
    (events ⟨time, Finset.mem_Iic.mpr le_rfl⟩).1
  informationAt_measurable := by
    intro time
    exact measurable_latestEventState time

/-- Identity realization on concrete dependent history/action bundles. -/
noncomputable def realizationKernel (time : ℕ) :
    Kernel
      (AnalyticArena.EventPrefix time ×
        AnalyticArena.ActionBundle)
      AnalyticArena.ActionBundle :=
  Kernel.deterministic
    (fun input => input.2)
    measurable_snd

@[simp]
theorem realizationKernel_apply
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (action : AnalyticArena.ActionBundle) :
    realizationKernel time (events, action) =
      Measure.dirac action := by
  rw [realizationKernel, Kernel.deterministic_apply]

instance realizationKernel_isFinite
    (time : ℕ) :
    IsFiniteKernel (realizationKernel time) :=
  ⟨⟨1, ENNReal.one_lt_top, fun input => by
      rw [realizationKernel_apply]
      simp⟩⟩

instance realizationKernel_isSFinite
    (time : ℕ) :
    IsSFiniteKernel (realizationKernel time) := by
  exact
    ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel

/-- Concrete action bundles serve directly as abstract actions. -/
noncomputable def realization :
    EventInformation.ActionRealization eventInformation where
  AbstractAction := fun _ => AnalyticArena.ActionBundle
  abstractActionMeasurable := fun _ =>
    historyModel.historyActionMeasurable
  kernel := realizationKernel
  kernel_isSFinite := by
    intro time
    exact realizationKernel_isSFinite time

/-- Measurable presentation with no reachable chance-controlled history. -/
noncomputable def presentation :
    observed.MeasurableKernelPresentation historyModel where
  information := eventInformation
  realization := realization
  playerInformation := fun _ input => input.2
  player_informationAt := by
    intro _ _ i _ _hnonterminal
    cases i
    rfl
  chanceKernel := fun _ => 0
  chanceKernel_isSFinite := by
    intro _
    infer_instance

/-! ## Role classification and profile assembly -/

/-- Terminal complete histories. -/
def terminalInformationSet : Set History :=
  {history | base.isTerminal history.1}

/-- Player-controlled complete histories. -/
def playerInformationSet : Set History :=
  {history | ¬ base.isTerminal history.1}

private def terminalDecision (node : Node) :
    Decidable (base.isTerminal node) := by
  change Decidable (IsEmpty (nodeAction node))
  cases node with
  | root => exact isFalse (fun h => h.false false)
  | second => exact isFalse (fun h => h.false false)
  | terminalBad => exact isTrue ⟨fun action => nomatch action⟩
  | terminalGood => exact isTrue ⟨fun action => nomatch action⟩

/-- Exact measurable role classification. -/
def roles :
    presentation.InformationRoles where
  playerTagMeasurable := ⊤
  playerTagDecidableEq := inferInstance
  playerTagSingleton_measurable := by
    intro _
    exact MeasurableSpace.measurableSet_top
  terminalInformationSet := fun _ => terminalInformationSet
  terminalInformationDecidable := fun _ information => by
    change Decidable (information ∈ terminalInformationSet)
    letI := terminalDecision information.1
    unfold terminalInformationSet
    infer_instance
  terminalInformationSet_measurable := by
    intro _
    exact MeasurableSpace.measurableSet_top
  playerInformationSet := fun _ => playerInformationSet
  playerInformationDecidable := fun _ information => by
    change Decidable (information ∈ playerInformationSet)
    letI := terminalDecision information.1
    unfold playerInformationSet
    infer_instance
  playerInformationSet_measurable := by
    intro _
    exact MeasurableSpace.measurableSet_top
  playerTag := fun _ _ => some ()
  playerTag_measurable := by
    intro _
    exact measurable_const
  terminal_at := by
    intro _ _ hterminal
    exact hterminal
  player_at := by
    intro _ _ i hnonterminal _
    cases i
    exact ⟨hnonterminal, hnonterminal, rfl⟩
  chance_at := by
    intro time events hnonterminal hmover
    cases hstate : (latestEventState time events).1 with
    | root =>
        change nodeMover _ = none at hmover
        rw [hstate] at hmover
        contradiction
    | second =>
        change nodeMover _ = none at hmover
        rw [hstate] at hmover
        contradiction
    | terminalBad =>
        exact
          (hnonterminal (by
            rw [hstate]
            change IsEmpty Empty
            exact ⟨Empty.elim⟩)).elim
    | terminalGood =>
        exact
          (hnonterminal (by
            rw [hstate]
            change IsEmpty Empty
            exact ⟨Empty.elim⟩)).elim

/-- No represented nonterminal history is chance controlled. -/
theorem no_nonterminal_chance
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ base.isTerminal (latestEventState time events).1)
    (hmover :
      base.mover (latestEventState time events).1 = none) :
    False := by
  cases hstate : (latestEventState time events).1 with
  | root =>
      change nodeMover _ = none at hmover
      rw [hstate] at hmover
      contradiction
  | second =>
      change nodeMover _ = none at hmover
      rw [hstate] at hmover
      contradiction
  | terminalBad =>
      exact
        hnonterminal (by
          rw [hstate]
          change IsEmpty Empty
          exact ⟨Empty.elim⟩)
  | terminalGood =>
      exact
        hnonterminal (by
          rw [hstate]
          change IsEmpty Empty
          exact ⟨Empty.elim⟩)

/-- Profile assembly with an unreachable zero chance branch. -/
def assembly :
    presentation.ProfileAssembly where
  toInformationRoles := roles
  chanceAbstractKernel := fun _ => 0
  chanceAbstractKernel_isSFinite := by
    intro _
    infer_instance
  chance_isProbability := by
    intro time events hnonterminal hmover
    exact
      (no_nonterminal_chance
        time events hnonterminal hmover).elim
  chance_realization_isProbability := by
    intro time events hnonterminal hmover
    exact
      (no_nonterminal_chance
        time events hnonterminal hmover).elim
  chance_realization_legal := by
    intro time events hnonterminal hmover
    exact
      (no_nonterminal_chance
        time events hnonterminal hmover).elim
  chance_realizedKernel := by
    intro time events hnonterminal hmover
    exact
      (no_nonterminal_chance
        time events hnonterminal hmover).elim

/-! ## Baseline and improving strategies -/

/-- Concrete legal bundle at the root. -/
def rootBundle (action : Bool) :
    AnalyticArena.ActionBundle :=
  ⟨rootHistory, action⟩

/-- Concrete legal bundle at the off-path second history. -/
def secondBundle (action : Bool) :
    AnalyticArena.ActionBundle :=
  ⟨secondHistory, action⟩

/-- Baseline choice: `true` at the root and `false` at the second node. -/
def baselineBundle (history : History) :
    AnalyticArena.ActionBundle :=
  match history.1 with
  | .root => rootBundle true
  | .second => secondBundle false
  | .terminalBad => rootBundle true
  | .terminalGood => rootBundle true

/-- Improving replacement: choose `true` at either decision node. -/
def goodBundle (history : History) :
    AnalyticArena.ActionBundle :=
  match history.1 with
  | .root => rootBundle true
  | .second => secondBundle true
  | .terminalBad => rootBundle true
  | .terminalGood => rootBundle true

theorem baselineBundle_mem_actionFiber
    (history : History)
    (hnonterminal : ¬ base.isTerminal history.1) :
    baselineBundle history ∈
      AnalyticArena.actionFiber history := by
  change (baselineBundle history).1 = history
  cases hstate : history.1 with
  | root =>
      have hhistory :
          history = rootHistory :=
        eq_rootHistory_of_endpoint_root history hstate
      subst history
      rfl
  | second =>
      have hhistory :
          history = secondHistory :=
        eq_secondHistory_of_endpoint_second history hstate
      subst history
      rfl
  | terminalBad =>
      exact
        (hnonterminal (by
          rw [hstate]
          change IsEmpty Empty
          exact ⟨Empty.elim⟩)).elim
  | terminalGood =>
      exact
        (hnonterminal (by
          rw [hstate]
          change IsEmpty Empty
          exact ⟨Empty.elim⟩)).elim

theorem goodBundle_mem_actionFiber
    (history : History)
    (hnonterminal : ¬ base.isTerminal history.1) :
    goodBundle history ∈
      AnalyticArena.actionFiber history := by
  change (goodBundle history).1 = history
  cases hstate : history.1 with
  | root =>
      have hhistory :
          history = rootHistory :=
        eq_rootHistory_of_endpoint_root history hstate
      subst history
      rfl
  | second =>
      have hhistory :
          history = secondHistory :=
        eq_secondHistory_of_endpoint_second history hstate
      subst history
      rfl
  | terminalBad =>
      exact
        (hnonterminal (by
          rw [hstate]
          change IsEmpty Empty
          exact ⟨Empty.elim⟩)).elim
  | terminalGood =>
      exact
        (hnonterminal (by
          rw [hstate]
          change IsEmpty Empty
          exact ⟨Empty.elim⟩)).elim

theorem baselineBundle_measurable :
    @Measurable
      History AnalyticArena.ActionBundle
      historyModel.historyMeasurable
      historyModel.historyActionMeasurable
      baselineBundle := by
  change
    @Measurable
      History AnalyticArena.ActionBundle
      ⊤ ⊤ baselineBundle
  exact fun _ _ => MeasurableSpace.measurableSet_top

theorem goodBundle_measurable :
    @Measurable
      History AnalyticArena.ActionBundle
      historyModel.historyMeasurable
      historyModel.historyActionMeasurable
      goodBundle := by
  change
    @Measurable
      History AnalyticArena.ActionBundle
      ⊤ ⊤ goodBundle
  exact fun _ _ => MeasurableSpace.measurableSet_top

/-- Joint baseline player profile. -/
noncomputable def baselineProfile :
    assembly.PlayerKernelProfile where
  kernel := fun _ =>
    Kernel.deterministic
      (fun input =>
        baselineBundle input.information)
      (baselineBundle_measurable.comp
        (assembly.playerInput_information_measurable _))
  kernel_isSFinite := by
    intro _
    infer_instance
  isProbability := by
    intro time events i _ _
    cases i
    rw [Kernel.deterministic_apply]
    infer_instance
  realization_isProbability := by
    intro time events i _ _
    cases i
    change
      ∀ᵐ action
          ∂Measure.dirac
            (baselineBundle
              (latestEventState time events)),
        IsProbabilityMeasure
          (realizationKernel time (events, action))
    exact Filter.Eventually.of_forall fun action => by
      rw [realizationKernel_apply]
      infer_instance
  realization_legal := by
    intro time events i hnonterminal _
    cases i
    change
      ∀ᵐ stateAction
          ∂(Measure.dirac
              (baselineBundle
                (latestEventState time events))).bind
            (Kernel.sectR
              (realizationKernel time) events),
        stateAction ∈
          AnalyticArena.actionFiber
            (latestEventState time events)
    apply
      MeasurableKernelArena.EventInformation.RealizedActionPolicy.ae_bind_mem_actionFiber_of_ae_mass_one
        (Measure.dirac
          (baselineBundle
            (latestEventState time events)))
        (Kernel.sectR (realizationKernel time) events)
        (latestEventState time events)
    · exact Filter.Eventually.of_forall fun action => by
        rw [Kernel.sectR_apply, realizationKernel_apply]
        infer_instance
    · simpa only [
        ae_dirac_eq,
        Filter.eventually_pure,
        Kernel.sectR_apply,
        realizationKernel_apply] using
          Measure.dirac_apply_of_mem
            (baselineBundle_mem_actionFiber
              (latestEventState time events)
              hnonterminal)

@[simp]
theorem baselineProfile_kernel
    (time : ℕ)
    (input : assembly.PlayerInput time) :
    baselineProfile.kernel time input =
      Measure.dirac
        (baselineBundle input.information) := by
  rw [baselineProfile, Kernel.deterministic_apply]
  rfl

/-- Certified replacement strategy choosing the good action at either player
history. -/
noncomputable def goodStrategy :
    assembly.PlayerStrategy () where
  kernel := fun _ =>
    Kernel.deterministic goodBundle
      goodBundle_measurable
  kernel_isSFinite := by
    intro _
    infer_instance
  isProbability := by
    intro time events _ _
    rw [Kernel.deterministic_apply]
    infer_instance
  realization_isProbability := by
    intro time events _ _
    change
      ∀ᵐ action
          ∂Measure.dirac
            (goodBundle
              (latestEventState time events)),
        IsProbabilityMeasure
          (realizationKernel time (events, action))
    exact Filter.Eventually.of_forall fun action => by
      rw [realizationKernel_apply]
      infer_instance
  realization_legal := by
    intro time events hnonterminal _
    change
      ∀ᵐ stateAction
          ∂(Measure.dirac
              (goodBundle
                (latestEventState time events))).bind
            (Kernel.sectR
              (realizationKernel time) events),
        stateAction ∈
          AnalyticArena.actionFiber
            (latestEventState time events)
    apply
      MeasurableKernelArena.EventInformation.RealizedActionPolicy.ae_bind_mem_actionFiber_of_ae_mass_one
        (Measure.dirac
          (goodBundle
            (latestEventState time events)))
        (Kernel.sectR (realizationKernel time) events)
        (latestEventState time events)
    · exact Filter.Eventually.of_forall fun action => by
        rw [Kernel.sectR_apply, realizationKernel_apply]
        infer_instance
    · simpa only [
        ae_dirac_eq,
        Filter.eventually_pure,
        Kernel.sectR_apply,
        realizationKernel_apply] using
          Measure.dirac_apply_of_mem
            (goodBundle_mem_actionFiber
              (latestEventState time events)
              hnonterminal)

@[simp]
theorem goodStrategy_kernel
    (time : ℕ)
    (history : History) :
    goodStrategy.kernel time history =
      Measure.dirac (goodBundle history) := by
  rw [goodStrategy, Kernel.deterministic_apply]
  rfl

/-- Constructive unilateral replacement by the good strategy. -/
noncomputable def deviatedProfile :
    assembly.PlayerKernelProfile :=
  ObservedGame.MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate
    (assembly := assembly)
    baselineProfile () goodStrategy

/-- Assembled baseline kernel profile. -/
noncomputable def assembledBaseline :
    presentation.KernelBehavioralProfile :=
  assembly.toKernelBehavioralProfile baselineProfile

/-- Assembled unilateral deviation. -/
noncomputable def assembledDeviation :
    presentation.KernelBehavioralProfile :=
  assembly.toKernelBehavioralProfile deviatedProfile

/-! ## Exact compiled laws -/

/-- The assembled baseline realizes its selected concrete bundle exactly at
every represented player prefix. -/
theorem assembledBaseline_compiled_kernel_of_player
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ base.isTerminal
        (latestEventState time events).1)
    (hmover :
      base.mover
          (latestEventState time events).1 =
        some ()) :
    assembledBaseline.compiledPolicy.kernel time events =
      Measure.dirac
        (baselineBundle
          (latestEventState time events)) := by
  rw [
    ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.compiledPolicy_kernel,
    EventInformation.RealizedActionPolicy.realizedKernel_apply]
  change
    (assembly.abstractKernel baselineProfile time
        (latestEventState time events)).bind
        (fun action =>
          realizationKernel time (events, action)) =
      Measure.dirac
        (baselineBundle
          (latestEventState time events))
  have habstract :=
    assembly.abstractKernel_apply_player
      baselineProfile time events ()
      hnonterminal hmover
  change
    assembly.abstractKernel baselineProfile time
        (latestEventState time events) =
      baselineProfile.kernel time
        ⟨some (), latestEventState time events⟩
    at habstract
  rw [habstract, baselineProfile_kernel]
  change
    (realizationKernel time).sectR events ∘ₘ
        Measure.dirac
          (baselineBundle
            (latestEventState time events)) =
      Measure.dirac
        (baselineBundle
          (latestEventState time events))
  rw [
    Measure.dirac_bind
      ((realizationKernel time).sectR events).measurable]
  exact
    realizationKernel_apply time events
      (baselineBundle
        (latestEventState time events))

/-- The assembled replacement realizes the good bundle exactly at every
represented player prefix. -/
theorem assembledDeviation_compiled_kernel_of_player
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ base.isTerminal
        (latestEventState time events).1)
    (hmover :
      base.mover
          (latestEventState time events).1 =
        some ()) :
    assembledDeviation.compiledPolicy.kernel time events =
      Measure.dirac
        (goodBundle
          (latestEventState time events)) := by
  rw [
    ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.compiledPolicy_kernel,
    EventInformation.RealizedActionPolicy.realizedKernel_apply]
  change
    (assembly.abstractKernel deviatedProfile time
        (latestEventState time events)).bind
        (fun action =>
          realizationKernel time (events, action)) =
      Measure.dirac
        (goodBundle
          (latestEventState time events))
  have habstract :=
    assembly.abstractKernel_apply_player
      deviatedProfile time events ()
      hnonterminal hmover
  change
    assembly.abstractKernel deviatedProfile time
        (latestEventState time events) =
      deviatedProfile.kernel time
        ⟨some (), latestEventState time events⟩
    at habstract
  rw [habstract]
  unfold deviatedProfile
  rw [
    ObservedGame.MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate_kernel_same,
    goodStrategy_kernel]
  change
    (realizationKernel time).sectR events ∘ₘ
        Measure.dirac
          (goodBundle
            (latestEventState time events)) =
      Measure.dirac
        (goodBundle
          (latestEventState time events))
  rw [
    Measure.dirac_bind
      ((realizationKernel time).sectR events).measurable]
  exact
    realizationKernel_apply time events
      (goodBundle
        (latestEventState time events))

/-- The canonical second-history prefix is nonterminal. -/
theorem secondContinuation_nonterminal :
    ¬ base.isTerminal
      (latestEventState
        (ObservedGame.MeasurableHistoryModel.canonicalContinuationStart
          (G := observed)
          secondHistory)
        (historyModel.canonicalContinuationPrefix
          secondHistory)).1 := by
  rw [
    historyModel.latestEventState_canonicalContinuationPrefix]
  change ¬ IsEmpty Bool
  intro hempty
  exact hempty.false false

/-- The canonical second-history prefix is controlled by the unique player.
-/
theorem secondContinuation_mover :
    base.mover
        (latestEventState
          (ObservedGame.MeasurableHistoryModel.canonicalContinuationStart
            (G := observed)
            secondHistory)
          (historyModel.canonicalContinuationPrefix
            secondHistory)).1 =
      some () := by
  rw [
    historyModel.latestEventState_canonicalContinuationPrefix]
  rfl

/-- The baseline selects `false` on the complete canonical off-path prefix at
absolute time one. -/
theorem assembledBaseline_compiled_kernel_secondContinuation :
    assembledBaseline.compiledPolicy.kernel
        (ObservedGame.MeasurableHistoryModel.canonicalContinuationStart
          (G := observed)
          secondHistory)
        (historyModel.canonicalContinuationPrefix
          secondHistory) =
      Measure.dirac (secondBundle false) := by
  rw [
    assembledBaseline_compiled_kernel_of_player
      (ObservedGame.MeasurableHistoryModel.canonicalContinuationStart
        (G := observed)
        secondHistory)
      (historyModel.canonicalContinuationPrefix
        secondHistory)
      secondContinuation_nonterminal
      secondContinuation_mover,
    historyModel.latestEventState_canonicalContinuationPrefix]
  rfl

/-- The replacement selects `true` on the same complete canonical off-path
prefix. -/
theorem assembledDeviation_compiled_kernel_secondContinuation :
    assembledDeviation.compiledPolicy.kernel
        (ObservedGame.MeasurableHistoryModel.canonicalContinuationStart
          (G := observed)
          secondHistory)
        (historyModel.canonicalContinuationPrefix
          secondHistory) =
      Measure.dirac (secondBundle true) := by
  rw [
    assembledDeviation_compiled_kernel_of_player
      (ObservedGame.MeasurableHistoryModel.canonicalContinuationStart
        (G := observed)
        secondHistory)
      (historyModel.canonicalContinuationPrefix
        secondHistory)
      secondContinuation_nonterminal
      secondContinuation_mover,
    historyModel.latestEventState_canonicalContinuationPrefix]
  rfl

/-! ## Exact continuation coordinate laws -/

@[simp]
theorem transition_root_true :
    AnalyticArena.transition (rootBundle true) =
      Measure.dirac rootGoodHistory := by
  change
    AnalyticArena.nextMeasure rootHistory true =
      Measure.dirac rootGoodHistory
  rw [ObservedGame.MeasurableHistoryModel.toArena_nextMeasure]
  rfl

@[simp]
theorem transition_second_false :
    AnalyticArena.transition (secondBundle false) =
      Measure.dirac secondBadHistory := by
  change
    AnalyticArena.nextMeasure secondHistory false =
      Measure.dirac secondBadHistory
  rw [ObservedGame.MeasurableHistoryModel.toArena_nextMeasure]
  rfl

@[simp]
theorem transition_second_true :
    AnalyticArena.transition (secondBundle true) =
      Measure.dirac secondGoodHistory := by
  change
    AnalyticArena.nextMeasure secondHistory true =
      Measure.dirac secondGoodHistory
  rw [ObservedGame.MeasurableHistoryModel.toArena_nextMeasure]
  rfl

/-- The baseline's first future state from the initial history is the good
terminal history. -/
theorem assembledBaseline_continuationCoordinate_one_root :
    (assembledBaseline.continuationStatePathMeasure
        rootHistory).map
        (fun path => path 1) =
      Measure.dirac rootGoodHistory := by
  rw [
    assembledBaseline.continuationStatePathMeasure_coordinate_one_of_nonterminal
      rootHistory]
  · have hkernel :=
      assembledBaseline_compiled_kernel_of_player
        (ObservedGame.MeasurableHistoryModel.canonicalContinuationStart
          (G := observed)
          rootHistory)
        (historyModel.canonicalContinuationPrefix
          rootHistory)
        (by
          rw [
            historyModel.latestEventState_canonicalContinuationPrefix]
          change ¬ IsEmpty Bool
          intro hempty
          exact hempty.false false)
        (by
          rw [
            historyModel.latestEventState_canonicalContinuationPrefix]
          rfl)
    rw [hkernel]
    rw [historyModel.latestEventState_canonicalContinuationPrefix]
    change
      AnalyticArena.transition ∘ₘ
          Measure.dirac (rootBundle true) =
        Measure.dirac rootGoodHistory
    rw [Measure.dirac_bind AnalyticArena.transition.measurable]
    exact transition_root_true
  · change ¬ IsEmpty Bool
    intro hempty
    exact hempty.false false

/-- The off-path second history has probability zero at future coordinate one
under the baseline initial continuation. -/
theorem assembledBaseline_secondHistory_probability_zero :
    ((assembledBaseline.continuationStatePathMeasure
        rootHistory).map
        (fun path => path 1))
        ({secondHistory} : Set History) =
      0 := by
  rw [
    assembledBaseline_continuationCoordinate_one_root]
  have hne :
      rootGoodHistory ≠ secondHistory := by
    intro hequal
    have hendpoint := congrArg Sigma.fst hequal
    exact Node.noConfusion hendpoint
  apply
    (dirac_eq_zero_iff_not_mem
      (measurableSet_singleton secondHistory)).2
  simpa only [Set.mem_singleton_iff] using hne

/-- The baseline's first future state from the canonical off-path
continuation is the bad terminal history. -/
theorem assembledBaseline_continuationCoordinate_one_second :
    (assembledBaseline.continuationStatePathMeasure
        secondHistory).map
        (fun path => path 1) =
      Measure.dirac secondBadHistory := by
  rw [
    assembledBaseline.continuationStatePathMeasure_coordinate_one_of_nonterminal
      secondHistory]
  · rw [
      assembledBaseline_compiled_kernel_secondContinuation]
    rw [Measure.dirac_bind AnalyticArena.transition.measurable]
    exact transition_second_false
  · change ¬ IsEmpty Bool
    intro hempty
    exact hempty.false false

/-- The replacement's first future state from the same canonical off-path
continuation is the good terminal history. -/
theorem assembledDeviation_continuationCoordinate_one_second :
    (assembledDeviation.continuationStatePathMeasure
        secondHistory).map
        (fun path => path 1) =
      Measure.dirac secondGoodHistory := by
  rw [
    assembledDeviation.continuationStatePathMeasure_coordinate_one_of_nonterminal
      secondHistory]
  · rw [
      assembledDeviation_compiled_kernel_secondContinuation]
    rw [Measure.dirac_bind AnalyticArena.transition.measurable]
    exact transition_second_true
  · change ¬ IsEmpty Bool
    intro hempty
    exact hempty.false false

/-! ## Bounded payoff and strict equilibrium refinement -/

/-- Coordinate-one base payoff as a bounded measurable path utility. -/
def evaluation :
    ObservedGame.MeasurableHistoryModel.BoundedPathUtility
      historyModel where
  utility := fun _ path =>
    base.payoff (path 1).1 ()
  utility_measurable := by
    intro _
    have hpayoff :
        @Measurable
          History ℝ
          historyModel.historyMeasurable
          inferInstance
          (fun history =>
            base.payoff history.1 ()) := by
      change
        @Measurable History ℝ ⊤ inferInstance
          (fun history =>
            base.payoff history.1 ())
      exact Measurable.of_discrete
    exact hpayoff.comp (measurable_pi_apply 1)
  bound := 1
  norm_utility_le := by
    intro i path
    cases i
    change
      ‖nodePayoff (path 1).1 ()‖ ≤ (1 : ℝ)
    cases (path 1).1 <;> simp [nodePayoff]

/-- Continuation expected utility is the payoff integral against future state
coordinate one. -/
theorem continuationExpectedUtility_eq_integral_coordinate_one
    (profile : presentation.KernelBehavioralProfile)
    (root : History) :
    evaluation.continuationExpectedUtility
        profile root () =
      ∫ history,
        base.payoff history.1 ()
        ∂(profile.continuationStatePathMeasure root).map
          (fun path => path 1) := by
  unfold
    ObservedGame.MeasurableHistoryModel.BoundedPathUtility.continuationExpectedUtility
    evaluation
  symm
  exact
    integral_map
      (measurable_pi_apply 1).aemeasurable
      (by
        have hpayoff :
            @Measurable
              History ℝ
              historyModel.historyMeasurable
              inferInstance
              (fun history =>
                base.payoff history.1 ()) := by
          change
            @Measurable History ℝ ⊤ inferInstance
              (fun history =>
                base.payoff history.1 ())
          exact Measurable.of_discrete
        exact hpayoff.aestronglyMeasurable)

/-- The baseline earns the maximal payoff at the initial continuation. -/
theorem assembledBaseline_continuationExpectedUtility_root :
    evaluation.continuationExpectedUtility
        assembledBaseline rootHistory () =
      1 := by
  rw [
    continuationExpectedUtility_eq_integral_coordinate_one,
    assembledBaseline_continuationCoordinate_one_root]
  calc
    (∫ history,
      base.payoff history.1 ()
      ∂Measure.dirac rootGoodHistory) =
        base.payoff rootGoodHistory.1 () := by
      exact
        @integral_dirac
          History ℝ _ _ _
          historyModel.historyMeasurable
          historyMeasurableSingletonClass
          (fun history =>
            base.payoff history.1 ())
          rootGoodHistory
    _ = 1 := rfl

/-- The baseline earns zero in the off-path absolute-prefix continuation. -/
theorem assembledBaseline_continuationExpectedUtility_second :
    evaluation.continuationExpectedUtility
        assembledBaseline secondHistory () =
      0 := by
  rw [
    continuationExpectedUtility_eq_integral_coordinate_one,
    assembledBaseline_continuationCoordinate_one_second]
  calc
    (∫ history,
      base.payoff history.1 ()
      ∂Measure.dirac secondBadHistory) =
        base.payoff secondBadHistory.1 () := by
      exact
        @integral_dirac
          History ℝ _ _ _
          historyModel.historyMeasurable
          historyMeasurableSingletonClass
          (fun history =>
            base.payoff history.1 ())
          secondBadHistory
    _ = 0 := rfl

/-- The certified replacement earns one in that same off-path continuation.
-/
theorem assembledDeviation_continuationExpectedUtility_second :
    evaluation.continuationExpectedUtility
        assembledDeviation secondHistory () =
      1 := by
  rw [
    continuationExpectedUtility_eq_integral_coordinate_one,
    assembledDeviation_continuationCoordinate_one_second]
  calc
    (∫ history,
      base.payoff history.1 ()
      ∂Measure.dirac secondGoodHistory) =
        base.payoff secondGoodHistory.1 () := by
      exact
        @integral_dirac
          History ℝ _ _ _
          historyModel.historyMeasurable
          historyMeasurableSingletonClass
          (fun history =>
            base.payoff history.1 ())
          secondGoodHistory
    _ = 1 := rfl

/-- The baseline is Nash at the initial history against every certified
measurable unilateral deviation: it already attains the uniform payoff bound.
-/
theorem baseline_isNashAtContinuation_root :
    evaluation.IsNashAtContinuation
        assembly rootHistory baselineProfile := by
  apply
    evaluation.isNashAtContinuation_of_expectedUtility_eq_bound
      assembly rootHistory baselineProfile
  intro who
  cases who
  change
    evaluation.continuationExpectedUtility
        assembledBaseline rootHistory () =
      (evaluation.bound : ℝ)
  rw [
    assembledBaseline_continuationExpectedUtility_root]
  rfl

/-- The baseline is not continuation Nash at the off-path second history. -/
theorem baseline_not_isNashAtContinuation_second :
    ¬ evaluation.IsNashAtContinuation
        assembly secondHistory baselineProfile := by
  intro hnash
  have himprovement := hnash () goodStrategy
  change
    evaluation.continuationExpectedUtility
        assembledDeviation secondHistory () ≤
      evaluation.continuationExpectedUtility
        assembledBaseline secondHistory ()
    at himprovement
  rw [
    assembledDeviation_continuationExpectedUtility_second,
    assembledBaseline_continuationExpectedUtility_second]
    at himprovement
  norm_num at himprovement

/-- Initial-root Nash does not imply measurable-kernel subgame perfection. -/
theorem baseline_not_isNashOnAllContinuations :
    ¬ evaluation.IsNashOnPresentation
        assembly observedRoots baselineProfile := by
  intro hspe
  exact
    baseline_not_isNashAtContinuation_second
      (hspe secondHistory trivial)

/-- Strict refinement witness: the same baseline is initial-root Nash and
fails absolute-prefix measurable-kernel subgame perfection. -/
theorem root_nash_and_not_subgamePerfect :
    evaluation.IsNashAtContinuation
        assembly rootHistory baselineProfile ∧
      ¬ evaluation.IsNashOnPresentation
        assembly observedRoots baselineProfile :=
  ⟨baseline_isNashAtContinuation_root,
   baseline_not_isNashOnAllContinuations⟩

end Examples.MeasurableKernelContinuationNashBoundary
