/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.ProfileAssembly
import EconCSLib.Math.Probability.PMF.ToMeasure
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Strict two-player regression for measurable profile assembly

This finite perfect-information game has two genuinely reachable decision
histories: player `false` moves at the root and player `true` moves after the
unique first action. Both concrete action fibers are singletons.

The common information carrier is the uncountable product of complete
histories with a real auxiliary coordinate; represented information uses
coordinate zero. The abstract action carrier is the unit interval. The
baseline profile uses a Dirac law for both players, while a replacement
strategy for player `true` uses unit-interval volume. The measurable profile
assembler constructs the deviation by branching on the tagged player
singleton.

The regression proves that:

* both player-controlled histories are inhabited;
* the replacement law is genuinely non-atomic and has no PMF representation;
* player `false`'s tagged kernel is unchanged;
* player `true`'s tagged kernel is changed;
* the assembled profiles satisfy the generic unilateral-deviation relation;
* splitting and reassembling an existing profile preserves its compiled event
  policy exactly.

The concrete realization deliberately forgets the abstract draw because each
legal fiber is a singleton. Thus this file tests player-indexed measurable
assembly rather than repeating the earlier non-atomic concrete-law boundary.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Examples.ObservedKernelProfileAssemblyBoundary

open ExtensiveGame
open MeasurableKernelArena

/-! ## A two-stage perfect-information game -/

/-- Root, second-player, and terminal states. -/
inductive Node
  | first
  | second
  | terminal
  deriving DecidableEq

/-- Both decision nodes have one concrete action; the terminal node has none. -/
def nodeAction : Node → Type
  | .first => Unit
  | .second => Unit
  | .terminal => Empty

/-- The unique first action reaches player two, and the unique second action
terminates. -/
def nodeNext : (state : Node) → nodeAction state → Node
  | .first, _ => .second
  | .second, _ => .terminal
  | .terminal, action => nomatch action

/-- Player `false` controls the root and player `true` controls the second
decision node. -/
def nodeMover : Node → Option Bool
  | .first => some false
  | .second => some true
  | .terminal => none

/-- Underlying two-player sequential game. -/
def base : ExtensiveGame Bool Unit where
  State := Node
  Action := nodeAction
  next := nodeNext
  init := .first
  mover := nodeMover
  payoff := fun _ _ => ()

abbrev History := base.toArena.HistoryFrom base.init

local instance historyMeasurable : MeasurableSpace History := ⊤

/-- Empty root history. -/
def rootHistory : History :=
  Arena.HistoryFrom.nil base.toArena base.init

/-- The unique complete history at the second decision node. -/
def secondHistory : History :=
  ⟨.second, rootHistory.2.snoc ()⟩

/-- The unique terminal complete history. -/
def terminalHistory : History :=
  ⟨.terminal, secondHistory.2.snoc ()⟩

/-- Any complete history ending at the root is the empty root history. -/
theorem eq_rootHistory_of_endpoint_first
    (history : History)
    (hfirst : history.1 = .first) :
    history = rootHistory := by
  rcases history with ⟨state, path⟩
  cases path with
  | nil => rfl
  | @snoc previousState path previousAction =>
      cases previousState with
      | first => contradiction
      | second => contradiction
      | terminal => exact Empty.elim previousAction

/-- Any complete history ending at the second node is the unique one-action
history. -/
theorem eq_secondHistory_of_endpoint_second
    (history : History)
    (hsecond : history.1 = .second) :
    history = secondHistory := by
  rcases history with ⟨state, path⟩
  cases path with
  | nil => contradiction
  | @snoc previousState path previousAction =>
      cases previousState with
      | first =>
          have hprevious :
              (⟨.first, path⟩ : History) = rootHistory :=
            eq_rootHistory_of_endpoint_first
              ⟨.first, path⟩ rfl
          cases hprevious
          cases previousAction
          rfl
      | second => contradiction
      | terminal => exact Empty.elim previousAction

/-- Perfect-information observation layer retaining the complete history. -/
def observed : ObservedGame Bool Unit :=
  ObservedGame.historyInformation base
    (ObservedGame.CompleteInformation.PublicObservationPresentation.trivial
      base)

/-- The smart-constructor migration preserves the former history-valued
private information, trivial public observation, and direct base-action
fibers definitionally. -/
example (i : Bool) (history : History)
    (hmover : base.mover history.1 = some i)
    (hnonterminal : ¬ base.isTerminal history.1) :
    observed.observe i history = history ∧
      observed.publicObserve history = () ∧
      observed.infoAt history i hmover
          (base.toArena.isDecision_of_not_isTerminal
            _ hnonterminal) = history := by
  simp [observed]

/-- The established discrete measurable history model is exact here because
all structural carriers are finite. -/
noncomputable def historyModel :
    observed.MeasurableHistoryModel :=
  ObservedGame.MeasurableHistoryModel.discrete observed

noncomputable abbrev AnalyticArena := historyModel.toArena

/-! ## History-valued information and singleton-fiber realization -/

/-- Analytic information is the latest complete history together with a real
auxiliary coordinate. Represented prefixes use coordinate zero, while the
full carrier remains uncountable. -/
def eventInformation :
    AnalyticArena.EventInformation where
  Information := fun _ => History × ℝ
  informationMeasurable := fun _ =>
    (⊤ : MeasurableSpace History).prod inferInstance
  informationAt := fun time events =>
    (latestEventState time events, 0)
  informationAt_measurable := by
    intro time
    exact
      Measurable.prod
        (measurable_latestEventState time)
        measurable_const

/-- The legal root bundle. -/
def rootBundle : AnalyticArena.ActionBundle :=
  ⟨rootHistory, ()⟩

/-- The legal second-player bundle. -/
def secondBundle : AnalyticArena.ActionBundle :=
  ⟨secondHistory, ()⟩

/-- Inputs whose latest history is the root. -/
def rootDomain (time : ℕ) :
    Set
      (AnalyticArena.EventPrefix time × Set.Icc (0 : ℝ) 1) :=
  {input | latestEventState time input.1 = rootHistory}

/-- Inputs whose latest history is the second-player history. -/
def secondDomain (time : ℕ) :
    Set
      (AnalyticArena.EventPrefix time × Set.Icc (0 : ℝ) 1) :=
  {input | latestEventState time input.1 = secondHistory}

theorem rootDomain_measurable (time : ℕ) :
    MeasurableSet (rootDomain time) := by
  exact
    ((measurable_latestEventState time).comp measurable_fst)
      (historyModel.singleton_measurable rootHistory)

theorem secondDomain_measurable (time : ℕ) :
    MeasurableSet (secondDomain time) := by
  exact
    ((measurable_latestEventState time).comp measurable_fst)
      (historyModel.singleton_measurable secondHistory)

/-- Realize every abstract draw at a player node as the unique legal concrete
action, and return zero mass at terminal histories. -/
noncomputable def realizationKernel (time : ℕ) :
    Kernel
      (AnalyticArena.EventPrefix time × Set.Icc (0 : ℝ) 1)
      AnalyticArena.ActionBundle := by
  classical
  exact
    Kernel.piecewise
      (rootDomain_measurable time)
      (Kernel.deterministic (fun _ => rootBundle) measurable_const)
      (Kernel.piecewise
        (secondDomain_measurable time)
        (Kernel.deterministic (fun _ => secondBundle) measurable_const)
        0)

@[simp]
theorem realizationKernel_apply_first
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (action : Set.Icc (0 : ℝ) 1)
    (hfirst : (latestEventState time events).1 = .first) :
    realizationKernel time (events, action) =
      Measure.dirac rootBundle := by
  classical
  rw [realizationKernel, Kernel.piecewise_apply]
  have hroot :
      latestEventState time events = rootHistory :=
    eq_rootHistory_of_endpoint_first
      (latestEventState time events) hfirst
  have hdomain :
      (events, action) ∈ rootDomain time :=
    hroot
  rw [if_pos hdomain, Kernel.deterministic_apply]

@[simp]
theorem realizationKernel_apply_second
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (action : Set.Icc (0 : ℝ) 1)
    (hsecond : (latestEventState time events).1 = .second) :
    realizationKernel time (events, action) =
      Measure.dirac secondBundle := by
  classical
  rw [realizationKernel, Kernel.piecewise_apply]
  have hhistory :
      latestEventState time events = secondHistory :=
    eq_secondHistory_of_endpoint_second
      (latestEventState time events) hsecond
  have hnotRoot :
      latestEventState time events ≠ rootHistory := by
    intro heq
    rw [heq] at hsecond
    change Node.first = Node.second at hsecond
    exact Node.noConfusion hsecond
  have hnotRootDomain :
      (events, action) ∉ rootDomain time :=
    hnotRoot
  have hsecondDomain :
      (events, action) ∈ secondDomain time :=
    hhistory
  rw [
    if_neg hnotRootDomain,
    Kernel.piecewise_apply,
    if_pos hsecondDomain,
    Kernel.deterministic_apply]

/-- Fixed unit-interval action realization. -/
noncomputable def realization :
    EventInformation.ActionRealization eventInformation where
  AbstractAction := fun _ => Set.Icc (0 : ℝ) 1
  abstractActionMeasurable := fun _ => inferInstance
  kernel := realizationKernel
  kernel_isSFinite := by
    intro time
    unfold realizationKernel
    infer_instance

/-- Structural presentation; nonterminal chance nodes do not exist. -/
noncomputable def presentation :
    observed.MeasurableKernelPresentation historyModel where
  information := eventInformation
  realization := realization
  playerInformation := fun _ input => (input.2, 0)
  player_informationAt := by
    intro _time _events _i _hmover _hnonterminal
    rfl
  chanceKernel := fun _ => 0
  chanceKernel_isSFinite := by
    intro _
    infer_instance

/-! ## Measurable role classification and profile assembly -/

/-- Histories at terminal nodes. -/
def terminalHistorySet : Set History :=
  {history | base.isTerminal history.1}

/-- Histories controlled by a player. -/
def playerHistorySet : Set History :=
  {history | ¬ base.isTerminal history.1}

theorem historySet_measurable (set : Set History) :
    @MeasurableSet History ⊤ set :=
  MeasurableSpace.measurableSet_top

/-- Terminal region of the uncountable common information carrier. -/
def terminalInformationSet : Set (History × ℝ) :=
  terminalHistorySet ×ˢ Set.univ

/-- Player-controlled region of the uncountable common information carrier. -/
def playerInformationSet : Set (History × ℝ) :=
  playerHistorySet ×ˢ Set.univ

theorem terminalInformationSet_measurable :
    MeasurableSet terminalInformationSet :=
  (historySet_measurable terminalHistorySet).prod
    MeasurableSet.univ

theorem playerInformationSet_measurable :
    MeasurableSet playerInformationSet :=
  (historySet_measurable playerHistorySet).prod
    MeasurableSet.univ

private def terminalDecision (node : Node) :
    Decidable (base.isTerminal node) := by
  change Decidable (IsEmpty (nodeAction node))
  cases node with
  | first => exact isFalse (fun h => h.false ())
  | second => exact isFalse (fun h => h.false ())
  | terminal => exact isTrue ⟨fun action => nomatch action⟩

/-- Exact measurable role data on history-valued information. -/
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
    letI := terminalDecision information.1.1
    change Decidable (base.isTerminal information.1.1 ∧ True)
    infer_instance
  terminalInformationSet_measurable := by
    intro _
    exact terminalInformationSet_measurable
  playerInformationSet := fun _ => playerInformationSet
  playerInformationDecidable := fun _ information => by
    change Decidable (information ∈ playerInformationSet)
    letI := terminalDecision information.1.1
    change Decidable (¬ base.isTerminal information.1.1 ∧ True)
    infer_instance
  playerInformationSet_measurable := by
    intro _
    exact playerInformationSet_measurable
  playerTag := fun _ information =>
    base.mover information.1.1
  playerTag_measurable := by
    intro _
    have hmover :
        @Measurable
          History (Option Bool) ⊤ ⊤
          (fun history => base.mover history.1) :=
      fun _ _ => MeasurableSpace.measurableSet_top
    exact hmover.comp measurable_fst
  terminal_at := by
    intro _ _ hterminal
    exact ⟨hterminal, Set.mem_univ _⟩
  player_at := by
    intro _ _ i hnonterminal hmover
    exact
      ⟨by
        intro hterminal
        exact hnonterminal hterminal.1,
       ⟨hnonterminal, Set.mem_univ _⟩,
       hmover⟩
  chance_at := by
    intro _time events hnonterminal hmover
    cases hstate : (latestEventState _time events).1 with
    | first =>
        change nodeMover _ = none at hmover
        rw [hstate] at hmover
        contradiction
    | second =>
        change nodeMover _ = none at hmover
        rw [hstate] at hmover
        contradiction
    | terminal =>
        exact
          (hnonterminal (by
            rw [hstate]
            change IsEmpty Empty
            exact ⟨Empty.elim⟩)).elim

/-- No represented nonterminal history is a chance history. -/
theorem no_nonterminal_chance
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ base.isTerminal (latestEventState time events).1)
    (hmover :
      base.mover (latestEventState time events).1 = none) :
    False := by
  cases hstate : (latestEventState time events).1 with
  | first =>
      change nodeMover _ = none at hmover
      rw [hstate] at hmover
      contradiction
  | second =>
      change nodeMover _ = none at hmover
      rw [hstate] at hmover
      contradiction
  | terminal =>
      exact
        hnonterminal (by
          rw [hstate]
          change IsEmpty Empty
          exact ⟨Empty.elim⟩)

/-- Profile assembly with unreachable zero chance law. -/
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

/-! ## Baseline and non-atomic replacement laws -/

/-- The left endpoint of the unit interval. -/
def zeroAction : Set.Icc (0 : ℝ) 1 :=
  ⟨0, by constructor <;> norm_num⟩

/-- Baseline law for every tagged player input. -/
noncomputable def baselineKernel (time : ℕ) :
    Kernel
      (assembly.PlayerInput time)
      (Set.Icc (0 : ℝ) 1) :=
  Kernel.deterministic (fun _ => zeroAction) measurable_const

@[simp]
theorem baselineKernel_apply
    (time : ℕ)
    (input : assembly.PlayerInput time) :
    baselineKernel time input =
      Measure.dirac zeroAction := by
  rw [baselineKernel, Kernel.deterministic_apply]

/-- Both represented player nodes have normalized deterministic
realizations for every abstract draw. -/
theorem realization_isProbability_at_player
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (i : Bool)
    (_hnonterminal :
      ¬ base.isTerminal (latestEventState time events).1)
    (hmover :
      base.mover (latestEventState time events).1 = some i) :
    ∀ᵐ action ∂(Measure.dirac zeroAction),
      IsProbabilityMeasure
        (realizationKernel time (events, action)) := by
  exact Filter.Eventually.of_forall fun action => by
    cases hstate : (latestEventState time events).1 with
    | first =>
        rw [realizationKernel_apply_first time events action hstate]
        infer_instance
    | second =>
        rw [realizationKernel_apply_second time events action hstate]
        infer_instance
    | terminal =>
        change nodeMover _ = some i at hmover
        rw [hstate] at hmover
        contradiction

/-- Both represented player nodes realize inside their current dependent
action fibers. -/
theorem realization_legal_at_player
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (i : Bool)
    (_hnonterminal :
      ¬ base.isTerminal (latestEventState time events).1)
    (hmover :
      base.mover (latestEventState time events).1 = some i) :
    ∀ᵐ action ∂(Measure.dirac zeroAction),
      realizationKernel time (events, action)
          (AnalyticArena.actionFiber
            (latestEventState time events)) =
        1 := by
  exact Filter.Eventually.of_forall fun action => by
    cases hstate : (latestEventState time events).1 with
    | first =>
        rw [realizationKernel_apply_first time events action hstate]
        apply Measure.dirac_apply_of_mem
        change rootHistory = latestEventState time events
        exact
          (eq_rootHistory_of_endpoint_first
            (latestEventState time events) hstate).symm
    | second =>
        rw [realizationKernel_apply_second time events action hstate]
        apply Measure.dirac_apply_of_mem
        change secondHistory = latestEventState time events
        exact
          (eq_secondHistory_of_endpoint_second
            (latestEventState time events) hstate).symm
    | terminal =>
        change nodeMover _ = some i at hmover
        rw [hstate] at hmover
        contradiction

/-- Baseline player-kernel profile. -/
noncomputable def baselineProfile :
    assembly.PlayerKernelProfile where
  kernel := baselineKernel
  kernel_isSFinite := by
    intro time
    change IsSFiniteKernel (baselineKernel time)
    unfold baselineKernel
    infer_instance
  isProbability := by
    intro time events i _hnonterminal _hmover
    change
      IsProbabilityMeasure
        (baselineKernel time
          ⟨some i, (latestEventState time events, 0)⟩)
    rw [baselineKernel_apply]
    infer_instance
  realization_isProbability := by
    intro time events i hnonterminal hmover
    change
      ∀ᵐ action
          ∂baselineKernel time
            ⟨some i, (latestEventState time events, 0)⟩,
        IsProbabilityMeasure
          (realizationKernel time (events, action))
    rw [baselineKernel_apply]
    exact
      realization_isProbability_at_player
        time events i hnonterminal hmover
  realization_legal := by
    intro time events i hnonterminal hmover
    change
      ∀ᵐ stateAction
          ∂(baselineKernel time
              ⟨some i,
                (latestEventState time events, 0)⟩).bind
            (Kernel.sectR
              (realizationKernel time) events),
        stateAction ∈
          AnalyticArena.actionFiber
            (latestEventState time events)
    letI : IsProbabilityMeasure
        (baselineKernel time
          ⟨some i, (latestEventState time events, 0)⟩) := by
      rw [baselineKernel_apply]
      infer_instance
    apply
      MeasurableKernelArena.EventInformation.RealizedActionPolicy.ae_bind_mem_actionFiber_of_ae_mass_one
        (baselineKernel time
          ⟨some i, (latestEventState time events, 0)⟩)
        (Kernel.sectR (realizationKernel time) events)
        (latestEventState time events)
    rw [baselineKernel_apply]
    · exact
        realization_isProbability_at_player
          time events i hnonterminal hmover
    · exact
      realization_legal_at_player
        time events i hnonterminal hmover

@[simp]
theorem baselineProfile_kernel
    (time : ℕ)
    (input : assembly.PlayerInput time) :
    baselineProfile.kernel time input =
      Measure.dirac zeroAction := by
  change baselineKernel time input = Measure.dirac zeroAction
  exact baselineKernel_apply time input

/-- Player `true` replaces the baseline Dirac law by unit-interval volume. -/
noncomputable def secondPlayerStrategy :
    assembly.PlayerStrategy true where
  kernel := fun _ =>
    Kernel.const (History × ℝ)
      (volume : Measure (Set.Icc (0 : ℝ) 1))
  kernel_isSFinite := by
    intro time
    change
      IsSFiniteKernel
        (Kernel.const (History × ℝ)
          (volume : Measure (Set.Icc (0 : ℝ) 1)))
    letI :
        IsMarkovKernel
          (Kernel.const (History × ℝ)
            (volume : Measure (Set.Icc (0 : ℝ) 1))) := by
      infer_instance
    infer_instance
  isProbability := by
    intro _ _ _ _
    change IsProbabilityMeasure
      (volume : Measure (Set.Icc (0 : ℝ) 1))
    infer_instance
  realization_isProbability := by
    intro time events hnonterminal hmover
    change
      ∀ᵐ action ∂(volume : Measure (Set.Icc (0 : ℝ) 1)),
        IsProbabilityMeasure
          (realizationKernel time (events, action))
    exact Filter.Eventually.of_forall fun action => by
      have hsecond :
          (latestEventState time events).1 = .second := by
        cases hstate : (latestEventState time events).1 with
        | first =>
            change nodeMover _ = some true at hmover
            rw [hstate] at hmover
            contradiction
        | second => rfl
        | terminal =>
            exact
              (hnonterminal (by
                rw [hstate]
                change IsEmpty Empty
                exact ⟨Empty.elim⟩)).elim
      rw [realizationKernel_apply_second time events action hsecond]
      infer_instance
  realization_legal := by
    intro time events hnonterminal hmover
    change
      ∀ᵐ stateAction
          ∂(volume : Measure (Set.Icc (0 : ℝ) 1)).bind
            (Kernel.sectR
              (realizationKernel time) events),
        stateAction ∈
          AnalyticArena.actionFiber
            (latestEventState time events)
    apply
      MeasurableKernelArena.EventInformation.RealizedActionPolicy.ae_bind_mem_actionFiber_of_ae_mass_one
        (volume : Measure (Set.Icc (0 : ℝ) 1))
        (Kernel.sectR (realizationKernel time) events)
        (latestEventState time events)
    · exact Filter.Eventually.of_forall fun action => by
        have hsecond :
            (latestEventState time events).1 = .second := by
          cases hstate : (latestEventState time events).1 with
          | first =>
              change nodeMover _ = some true at hmover
              rw [hstate] at hmover
              contradiction
          | second => rfl
          | terminal =>
              exact
                (hnonterminal (by
                  rw [hstate]
                  change IsEmpty Empty
                  exact ⟨Empty.elim⟩)).elim
        rw [Kernel.sectR_apply]
        rw [realizationKernel_apply_second
          time events action hsecond]
        infer_instance
    · exact Filter.Eventually.of_forall fun action => by
        have hsecond :
            (latestEventState time events).1 = .second := by
          cases hstate : (latestEventState time events).1 with
          | first =>
              change nodeMover _ = some true at hmover
              rw [hstate] at hmover
              contradiction
          | second => rfl
          | terminal =>
              exact
                (hnonterminal (by
                  rw [hstate]
                  change IsEmpty Empty
                  exact ⟨Empty.elim⟩)).elim
        rw [Kernel.sectR_apply]
        rw [realizationKernel_apply_second
          time events action hsecond]
        apply Measure.dirac_apply_of_mem
        change secondHistory = latestEventState time events
        exact
          (eq_secondHistory_of_endpoint_second
            (latestEventState time events) hsecond).symm

@[simp]
theorem secondPlayerStrategy_kernel
    (time : ℕ)
    (information : History × ℝ) :
    secondPlayerStrategy.kernel time information =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  change
    Kernel.const (History × ℝ)
        (volume : Measure (Set.Icc (0 : ℝ) 1))
        information =
      (volume : Measure (Set.Icc (0 : ℝ) 1))
  exact Kernel.const_apply _ _

/-- Constructive tagged deviation of player `true`. -/
noncomputable def deviatedProfile :
    assembly.PlayerKernelProfile :=
  ObservedGame.MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate
    (assembly := assembly)
    baselineProfile true secondPlayerStrategy

/-! ## Strict witnesses and regression theorems -/

/-- Inhabited root event prefix. -/
def rootPrefix : AnalyticArena.EventPrefix 0 :=
  fun _ => (rootHistory, Sum.inl ())

/-- Inhabited second-player event prefix. -/
def secondPrefix : AnalyticArena.EventPrefix 0 :=
  fun _ => (secondHistory, Sum.inl ())

@[simp]
theorem latestEventState_rootPrefix :
    latestEventState 0 rootPrefix = rootHistory :=
  rfl

@[simp]
theorem latestEventState_secondPrefix :
    latestEventState 0 secondPrefix = secondHistory :=
  rfl

/-- The first player genuinely controls the inhabited root prefix. -/
theorem root_mover :
    base.mover (latestEventState 0 rootPrefix).1 =
      some false :=
  rfl

/-- The second player genuinely controls the inhabited one-action prefix. -/
theorem second_mover :
    base.mover (latestEventState 0 secondPrefix).1 =
      some true :=
  rfl

/-- The common analytic information carrier is genuinely uncountable. -/
theorem information_not_countable :
    ¬ Countable (History × ℝ) := by
  intro hcountable
  letI : Countable (History × ℝ) :=
    hcountable
  have hinjective :
      Function.Injective
        (fun coordinate : ℝ => (rootHistory, coordinate)) := by
    intro first second heq
    exact congrArg Prod.snd heq
  exact
    (not_countable (α := ℝ))
      hinjective.countable

/-- Unit-interval volume is not the measure of any PMF. -/
theorem no_PMF_unitInterval_volume :
    ¬ ∃ p : PMF (Set.Icc (0 : ℝ) 1),
      p.toMeasure =
        (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  rintro ⟨p, hp⟩
  have hsupportOne :
      p.toMeasure p.support = 1 :=
    (p.toMeasure_apply_eq_one_iff
      p.support_countable.measurableSet).mpr Set.Subset.rfl
  have hsupportZero :
      (volume : Measure (Set.Icc (0 : ℝ) 1)) p.support = 0 :=
    p.support_countable.measure_zero _
  rw [hp, hsupportZero] at hsupportOne
  exact zero_ne_one hsupportOne

/-- The exact measure used by the deviating player is genuinely non-atomic. -/
theorem unitInterval_volume_nonAtomic :
    NoAtoms (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  infer_instance

/-- The deviating player's represented law has no PMF representation. -/
theorem no_PMF_secondPlayerStrategy :
    ¬ ∃ p : PMF (Set.Icc (0 : ℝ) 1),
      p.toMeasure =
        secondPlayerStrategy.kernel
          0 (secondHistory, 0) := by
  rw [secondPlayerStrategy_kernel]
  exact no_PMF_unitInterval_volume

/-- Player `false`'s tagged law is unchanged by player `true`'s deviation. -/
theorem first_player_kernel_unchanged :
    deviatedProfile.kernel 0
        ⟨some false, (rootHistory, 0)⟩ =
      baselineProfile.kernel 0
        ⟨some false, (rootHistory, 0)⟩ := by
  exact
    ObservedGame.MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate_kernel_of_ne
      (assembly := assembly)
      baselineProfile true secondPlayerStrategy 0 (rootHistory, 0)
      (by decide)

/-- The deviating player's tagged law is unit-interval volume. -/
theorem second_player_kernel_eq_volume :
    deviatedProfile.kernel 0
        ⟨some true, (secondHistory, 0)⟩ =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  rw [deviatedProfile]
  rw [
    ObservedGame.MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate_kernel_same]
  exact secondPlayerStrategy_kernel 0 (secondHistory, 0)

/-- The deviating player's tagged law differs from the baseline Dirac law. -/
theorem second_player_kernel_changed :
    deviatedProfile.kernel 0
        ⟨some true, (secondHistory, 0)⟩ ≠
      baselineProfile.kernel 0
        ⟨some true, (secondHistory, 0)⟩ := by
  rw [
    second_player_kernel_eq_volume,
    baselineProfile_kernel]
  intro heq
  have hsingleton :=
    congrArg
      (fun measure : Measure (Set.Icc (0 : ℝ) 1) =>
        measure {zeroAction})
      heq
  simp at hsingleton

/-- The assembled complete profiles satisfy the generic unilateral-deviation
relation. -/
theorem assembled_isUnilateralDeviation :
    (assembly.toKernelBehavioralProfile baselineProfile).IsUnilateralDeviation
      true
      (assembly.toKernelBehavioralProfile deviatedProfile) := by
  exact
    assembly.toKernelBehavioralProfile_deviate
      baselineProfile true secondPlayerStrategy

/-- Generic split/reassembly is exact at the compiled event-policy level. -/
theorem split_reassembly_compiledPolicy_exact :
    (assembly.toKernelBehavioralProfile
        (ObservedGame.MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.ofKernelBehavioralProfile
          (assembly := assembly)
          (assembly.toKernelBehavioralProfile baselineProfile))).compiledPolicy =
      (assembly.toKernelBehavioralProfile baselineProfile).compiledPolicy :=
  assembly.toKernelBehavioralProfile_ofKernelBehavioralProfile_compiledPolicy
    (assembly.toKernelBehavioralProfile baselineProfile)

end Examples.ObservedKernelProfileAssemblyBoundary
