/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# An uncountable reachable observed-EFG presentation

This regression crosses the actual boundary of the automatic
countable-discrete constructor.

At the unique decision node the player chooses an arbitrary real number.
Every real action creates a distinct terminal complete history.  Hence both
the reachable complete-history carrier and its total legal history/action
carrier are genuinely uncountable.

The complete histories use the finite-sum Borel code `Unit ⊕ ℝ`, while legal
history/action bundles are coded by Borel `ℝ`.  Their
measurable spaces are transported along explicit equivalences.  History
append, terminality, projection, information, realization, and every
profile's abstract finite-law kernel are then proved measurable.

The resulting `MeasurablePresentation` has:

* one fixed player information state;
* the Borel abstract action space `ℝ`;
* a measurable deterministic realization into the current dependent action
  fiber;
* exact compilation of every behavioral finite law, not only one selected
  profile;
* a complete joint event-path and state-path law.

This remains a finite-action-law EFG: behavioral strategies are
`FiniteLaw ℝ`.
The example does not claim non-atomic behavioral randomization.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.ObservedChanceMeasurableUncountableBoundary

open ExtensiveGame
open MeasurableKernelArena

local macro "finiteLawMeasure(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0)

private theorem finiteLawMeasure_isProbability
    {α : Type*} [MeasurableSpace α] (law : FiniteLaw α) :
    IsProbabilityMeasure finiteLawMeasure(law) := by
  constructor
  change finiteLawMeasure(law) Set.univ = 1
  have hzero : ((0 : ℚ≥0) : ENNReal) = 0 := by
    change (((0 : ℚ≥0) : NNReal) : ENNReal) = 0
    simp
  have hadd (p q : ℚ≥0) :
      ((p + q : ℚ≥0) : ENNReal) =
        (p : ENNReal) + (q : ENNReal) := by
    change (((p + q : ℚ≥0) : NNReal) : ENNReal) =
      ((p : NNReal) : ENNReal) + ((q : NNReal) : ENNReal)
    simp
  have hsum :
      finiteLawMeasure(law) Set.univ =
        ((FiniteLaw.totalWeight law.atoms : ℚ≥0) : ENNReal) := by
    induction law.atoms with
    | nil => simp [FiniteLaw.totalWeight, hzero]
    | cons atom atoms ih =>
        simp [FiniteLaw.totalWeight, ih, hadd]
  rw [hsum, FiniteLaw.totalWeight_atoms]
  change (((1 : ℚ≥0) : NNReal) : ENNReal) = 1
  norm_num

private theorem measure_bind_add
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (left right : Measure α) (next : α → Measure β)
    (hmeasurable : Measurable next) :
    (left + right).bind next =
      left.bind next + right.bind next := by
  ext event hevent
  simp [Measure.bind_apply, hevent, hmeasurable.aemeasurable,
    MeasureTheory.lintegral_add_measure]

/-- A root decision followed by a terminal node. -/
inductive Node
  | root
  | terminal

/-- Every real number is a legal root action. -/
def nodeAction : Node → Type
  | .root => ℝ
  | .terminal => Empty

/-- Every root action terminates. -/
def nodeNext : (state : Node) → nodeAction state → Node
  | .root, _ => .terminal
  | .terminal, action => nomatch action

/-- The sole player controls the root. -/
def nodeMover : Node → Option Unit
  | .root => some ()
  | .terminal => none

/-- Underlying one-step real-action game. -/
def base : ExtensiveGame Unit Unit where
  State := Node
  Action := nodeAction
  next := nodeNext
  init := .root
  mover := nodeMover
  payoff := fun _ _ => ()

/-- The one original information state at every player-controlled history. -/
def informationAt
    (history : base.toArena.HistoryFrom base.init)
    (i : Unit)
    (_hmover : base.mover history.1 = some i)
    (_hdecision : base.toArena.IsDecision history.1) :
    Unit := ()

/-- At the root, abstract real actions are exactly concrete real actions. -/
def actionEquiv
    (history : base.toArena.HistoryFrom base.init)
    (i : Unit)
    (hmover : base.mover history.1 = some i)
    (_hdecision : base.toArena.IsDecision history.1) :
    ℝ ≃ base.Action history.1 := by
  cases i
  cases hstate : history.1 with
  | root =>
      change ℝ ≃ ℝ
      exact Equiv.refl ℝ
  | terminal =>
      change nodeMover history.1 = some () at hmover
      rw [hstate] at hmover
      exact (Option.some_ne_none () hmover.symm).elim

/-- Observed real-action game with one information state. -/
def observed : ObservedGame Unit Unit where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => ()
  infoAt := informationAt
  infoAt_observe := fun _ _ _ _ => rfl
  InfoAction := fun _ _ => ℝ
  actionEquiv := actionEquiv

/-- The example has no chance-controlled node. -/
def game : ObservedChanceGame Unit Unit where
  observed := observed
  chanceKernel := by
    intro history hchance
    cases hstate : history.1 with
    | root =>
        have hmover := hchance.1
        change nodeMover history.1 = none at hmover
        rw [hstate] at hmover
        exact (Option.some_ne_none () hmover).elim
    | terminal =>
        apply (hchance.2 ?_).elim
        rw [hstate]
        exact ⟨Empty.elim⟩

abbrev History :=
  ObservedChanceGame.CompleteHistory game

abbrev HistoryAction :=
  ObservedChanceGame.HistoryActionBundle game

/-- Empty root history. -/
def rootHistory : History :=
  Arena.HistoryFrom.nil base.toArena base.init

theorem rootHistory_mover :
    game.observed.base.mover rootHistory.1 = some () :=
  rfl

theorem rootHistory_nonterminal :
    ¬ game.observed.base.isTerminal rootHistory.1 :=
  fun hterminal => by
    change IsEmpty ℝ at hterminal
    exact hterminal.false 0

theorem rootHistory_decision :
    game.observed.base.toArena.IsDecision rootHistory.1 :=
  game.observed.base.toArena.isDecision_of_not_isTerminal _
    rootHistory_nonterminal

/-- The unique represented information coordinate in this one-decision
game. -/
def rootInformation : game.observed.RepresentedInfo () :=
  game.observed.representedInfoAt rootHistory () rootHistory_mover
    rootHistory_decision

/-- Terminal history generated by one real action. -/
def terminalHistory (action : ℝ) : History :=
  ⟨.terminal, rootHistory.2.snoc action⟩

/-- Code an empty history by `inl` and a one-action history by its real
action. -/
def historyCode : History → Unit ⊕ ℝ
  | ⟨_, .nil⟩ => .inl ()
  | ⟨_, .snoc history action⟩ =>
      match history with
      | .nil => .inr action

/-- Decode the finite-sum Borel history code. -/
def historyDecode : Unit ⊕ ℝ → History
  | .inl _ => rootHistory
  | .inr action => terminalHistory action

@[simp]
theorem historyCode_root :
    historyCode rootHistory = .inl () :=
  rfl

@[simp]
theorem historyCode_terminal (action : ℝ) :
    historyCode (terminalHistory action) = .inr action :=
  rfl

@[simp]
theorem historyDecode_code (history : History) :
    historyDecode (historyCode history) = history := by
  rcases history with ⟨state, path⟩
  cases path with
  | nil =>
      rfl
  | snoc path action =>
      cases path with
      | nil =>
          rfl
      | @snoc state path previousAction =>
          cases state with
          | root =>
              exact Empty.elim action
          | terminal =>
              exact Empty.elim previousAction

@[simp]
theorem historyCode_decode (code : Unit ⊕ ℝ) :
    historyCode (historyDecode code) = code := by
  cases code with
  | inl value =>
      cases value
      rfl
  | inr action =>
      rfl

/-- Complete histories are equivalent to `Unit ⊕ ℝ`. -/
def historyEquiv : History ≃ (Unit ⊕ ℝ) where
  toFun := historyCode
  invFun := historyDecode
  left_inv := historyDecode_code
  right_inv := historyCode_decode

/-- A legal history/action bundle is completely determined by its real root
action. -/
def historyActionCode
    (historyAction : HistoryAction) : ℝ := by
  rcases historyAction with ⟨⟨state, path⟩, action⟩
  cases path with
  | nil =>
      exact action
  | @snoc previousState path previousAction =>
      cases previousState with
      | root =>
          exact Empty.elim action
      | terminal =>
          exact Empty.elim previousAction

/-- Decode a real action as a legal bundle at the root history. -/
def historyActionDecode (action : ℝ) : HistoryAction :=
  ⟨rootHistory, action⟩

@[simp]
theorem historyActionCode_decode (action : ℝ) :
    historyActionCode (historyActionDecode action) = action :=
  rfl

@[simp]
theorem historyActionDecode_code (historyAction : HistoryAction) :
    historyActionDecode (historyActionCode historyAction) =
      historyAction := by
  rcases historyAction with ⟨⟨state, path⟩, action⟩
  cases path with
  | nil =>
      rfl
  | @snoc previousState path previousAction =>
      cases previousState with
      | root =>
          exact Empty.elim action
      | terminal =>
          exact Empty.elim previousAction

/-- Legal history/action bundles are equivalent to `ℝ`. -/
def historyActionEquiv : HistoryAction ≃ ℝ where
  toFun := historyActionCode
  invFun := historyActionDecode
  left_inv := historyActionDecode_code
  right_inv := historyActionCode_decode

/-- Finite-sum Borel measurable structure transported from `Unit ⊕ ℝ`. -/
@[reducible] def historyMeasurable : MeasurableSpace History :=
  (inferInstance : MeasurableSpace (Unit ⊕ ℝ)).comap historyEquiv

/-- Borel measurable structure transported from `ℝ`. -/
@[reducible] def historyActionMeasurable : MeasurableSpace HistoryAction :=
  (inferInstance : MeasurableSpace ℝ).comap historyActionEquiv

local instance : MeasurableSpace History :=
  historyMeasurable

local instance : MeasurableSpace HistoryAction :=
  historyActionMeasurable

/-- The history coding equivalence is measurable in both directions. -/
def historyMeasurableEquiv : History ≃ᵐ (Unit ⊕ ℝ) where
  toEquiv := historyEquiv
  measurable_toFun := comap_measurable historyEquiv
  measurable_invFun := by
    change
      @Measurable
        (Unit ⊕ ℝ) History
        inferInstance historyMeasurable
        historyEquiv.symm
    unfold historyMeasurable
    rw [measurable_comap_iff]
    simpa only [Function.comp_apply, historyCode_decode] using
      (measurable_id :
        Measurable (fun code : Unit ⊕ ℝ => code))

/-- The legal-bundle coding equivalence is measurable in both directions. -/
def historyActionMeasurableEquiv : HistoryAction ≃ᵐ ℝ where
  toEquiv := historyActionEquiv
  measurable_toFun := comap_measurable historyActionEquiv
  measurable_invFun := by
    change
      @Measurable
        ℝ HistoryAction
        inferInstance historyActionMeasurable
        historyActionEquiv.symm
    unfold historyActionMeasurable
    rw [measurable_comap_iff]
    simpa only [Function.comp_apply, historyActionCode_decode] using
      (measurable_id : Measurable (fun action : ℝ => action))

local instance historyActionMeasurableSingletonClass :
    MeasurableSingletonClass HistoryAction where
  measurableSet_singleton historyAction := by
    refine
      ⟨({historyActionEquiv historyAction} : Set ℝ),
        measurableSet_singleton _, ?_⟩
    ext candidate
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact historyActionEquiv.injective.eq_iff

/-- A complete history ending at the root is the empty history. -/
theorem eq_rootHistory_of_endpoint_root
    (history : History)
    (hroot : history.1 = .root) :
    history = rootHistory := by
  apply historyEquiv.injective
  change historyCode history = historyCode rootHistory
  cases hcode : historyCode history with
  | inl value =>
      cases value
      rfl
  | inr action =>
      have hhistory :
          history = terminalHistory action := by
        calc
          history = historyDecode (historyCode history) :=
            (historyDecode_code history).symm
          _ = terminalHistory action := by rw [hcode]; rfl
      have hendpoint := congrArg Sigma.fst hhistory
      rw [hroot] at hendpoint
      contradiction

/-- The state projection is measurable for the transported structures. -/
theorem stateProjection_measurable :
    Measurable (Sigma.fst : HistoryAction → History) := by
  change
    @Measurable
      HistoryAction History
      historyActionMeasurable historyMeasurable
      Sigma.fst
  unfold historyMeasurable
  rw [measurable_comap_iff]
  have heq :
      historyEquiv ∘ (Sigma.fst : HistoryAction → History) =
        fun _ => Sum.inl () := by
    funext historyAction
    rcases historyAction with ⟨history, action⟩
    have hroot : history.1 = .root := by
      cases hstate : history.1 with
      | root => rfl
      | terminal =>
          change nodeAction history.1 at action
          rw [hstate] at action
          exact Empty.elim action
    have hhistory :
        history = rootHistory :=
      eq_rootHistory_of_endpoint_root history hroot
    exact congrArg historyEquiv hhistory
  rw [heq]
  exact measurable_const

/-- Appending the real root action is measurable. -/
theorem appendHistory_measurable :
    Measurable (ObservedChanceGame.appendHistory game) := by
  change
    @Measurable
      HistoryAction History
      historyActionMeasurable historyMeasurable
      (ObservedChanceGame.appendHistory game)
  unfold historyMeasurable
  rw [measurable_comap_iff]
  have heq :
      historyEquiv ∘ ObservedChanceGame.appendHistory game =
        Sum.inr ∘ historyActionEquiv := by
    funext historyAction
    rcases historyAction with ⟨⟨state, path⟩, action⟩
    cases path with
    | nil =>
        rfl
    | @snoc previousState path previousAction =>
        cases previousState with
        | root =>
            exact Empty.elim action
        | terminal =>
            exact Empty.elim previousAction
  rw [heq]
  exact measurable_inr.comp historyActionMeasurableEquiv.measurable

/-- Terminal histories form the measurable `inr` branch of the history code. -/
theorem terminalSet_measurable :
    MeasurableSet
      {history : History |
        game.observed.base.isTerminal history.1} := by
  refine
    ⟨Set.range (Sum.inr : ℝ → Unit ⊕ ℝ),
      measurableSet_range_inr, ?_⟩
  ext history
  change
    historyCode history ∈ Set.range (Sum.inr : ℝ → Unit ⊕ ℝ) ↔
      game.observed.base.isTerminal history.1
  cases hcode : historyCode history with
  | inl value =>
      have hhistory :
          history = rootHistory := by
        calc
          history = historyDecode (historyCode history) :=
            (historyDecode_code history).symm
          _ = rootHistory := by rw [hcode]; cases value; rfl
      rw [hhistory]
      constructor
      · rintro ⟨action, hfalse⟩
        contradiction
      · intro hterminal
        change IsEmpty ℝ at hterminal
        exact (hterminal.false 0).elim
  | inr action =>
      have hhistory :
          history = terminalHistory action := by
        calc
          history = historyDecode (historyCode history) :=
            (historyDecode_code history).symm
          _ = terminalHistory action := by rw [hcode]; rfl
      rw [hhistory]
      constructor
      · intro _hmembership
        change IsEmpty Empty
        exact ⟨Empty.elim⟩
      · intro _hterminal
        exact ⟨action, rfl⟩

/-- Every complete-history singleton is measurable. -/
theorem singleton_measurable (history : History) :
    MeasurableSet ({history} : Set History) := by
  have hcodeSingleton :
      MeasurableSet
        ({historyEquiv history} : Set (Unit ⊕ ℝ)) := by
    cases hcode : historyEquiv history with
    | inl value =>
        have heq :
            ({Sum.inl value} : Set (Unit ⊕ ℝ)) =
              Sum.inl '' ({value} : Set Unit) := by
          ext candidate
          simp
        rw [heq]
        exact (measurableSet_singleton value).inl_image
    | inr action =>
        have heq :
            ({Sum.inr action} : Set (Unit ⊕ ℝ)) =
              Sum.inr '' ({action} : Set ℝ) := by
          ext candidate
          simp
        rw [heq]
        exact (measurableSet_singleton action).inr_image
  refine
    ⟨({historyEquiv history} : Set (Unit ⊕ ℝ)),
      hcodeSingleton, ?_⟩
  ext candidate
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  exact historyEquiv.injective.eq_iff

/-- Explicit uncountable measurable complete-history model. -/
noncomputable def measurableHistoryModel :
    ObservedChanceGame.MeasurableHistoryModel game where
  historyMeasurable := historyMeasurable
  historyActionMeasurable := historyActionMeasurable
  stateProjection_measurable := stateProjection_measurable
  appendHistory_measurable := appendHistory_measurable
  transition :=
    Kernel.deterministic
      (ObservedChanceGame.appendHistory game)
      appendHistory_measurable
  transition_isMarkov := by
    infer_instance
  transition_apply := by
    intro historyAction
    rw [Kernel.deterministic_apply]
  terminalSet_measurable := terminalSet_measurable
  singleton_measurable := singleton_measurable

noncomputable abbrev AnalyticArena :=
  measurableHistoryModel.toArena

/-- Complete histories are genuinely uncountable. -/
theorem history_not_countable :
    ¬ Countable History := by
  intro hcountable
  letI : Countable History := hcountable
  have hinjective :
      Function.Injective terminalHistory := by
    intro first second heq
    have := congrArg historyCode heq
    simpa using this
  exact (not_countable (α := ℝ)) hinjective.countable

/-- The total legal history/action carrier is genuinely uncountable. -/
theorem historyAction_not_countable :
    ¬ Countable HistoryAction := by
  intro hcountable
  letI : Countable HistoryAction := hcountable
  have hinjective :
      Function.Injective historyActionDecode := by
    intro first second heq
    have := congrArg historyActionCode heq
    simpa using this
  exact
    (not_countable (α := ℝ))
      hinjective.countable

/-- Analytic information distinguishes the root decision from terminal
histories. -/
def historyInformation (history : History) : Bool :=
  match historyCode history with
  | .inl _ => false
  | .inr _ => true

@[simp]
theorem historyInformation_root :
    historyInformation rootHistory = false :=
  rfl

@[simp]
theorem historyInformation_terminal (action : ℝ) :
    historyInformation (terminalHistory action) = true :=
  rfl

theorem historyInformation_eq_false_of_endpoint_root
    (history : History)
    (hroot : history.1 = .root) :
    historyInformation history = false := by
  rw [eq_rootHistory_of_endpoint_root history hroot]
  rfl

theorem endpoint_root_of_historyInformation_eq_false
    (history : History)
    (hinformation : historyInformation history = false) :
    history.1 = .root := by
  cases hcode : historyCode history with
  | inl value =>
      have hhistory :
          history = rootHistory := by
        calc
          history = historyDecode (historyCode history) :=
            (historyDecode_code history).symm
          _ = rootHistory := by rw [hcode]; cases value; rfl
      rw [hhistory]
      rfl
  | inr action =>
      unfold historyInformation at hinformation
      rw [hcode] at hinformation
      contradiction

theorem historyInformation_measurable :
    Measurable historyInformation := by
  have heq :
      historyInformation =
        (fun code : Unit ⊕ ℝ =>
          Sum.elim (fun _ => false) (fun _ => true) code) ∘
          historyEquiv := by
    funext history
    unfold historyInformation
    change
      (match historyCode history with
        | .inl _ => false
        | .inr _ => true) =
      Sum.elim (fun _ => false) (fun _ => true)
        (historyCode history)
    cases historyCode history <;> rfl
  rw [heq]
  exact
    (measurable_fun_sum measurable_const measurable_const).comp
      historyMeasurableEquiv.measurable

/-- Fixed measurable root/terminal event information. -/
def eventInformation :
    AnalyticArena.EventInformation where
  Information := fun _ => Bool
  informationMeasurable := fun _ => inferInstance
  informationAt := fun time events =>
    historyInformation (latestEventState time events)
  informationAt_measurable := by
    intro time
    exact
      historyInformation_measurable.comp
        (measurable_latestEventState time)

/-- Every legal bundle necessarily lies over the root history. -/
@[simp]
theorem historyActionDecode_fst (action : ℝ) :
    (historyActionDecode action).1 = rootHistory :=
  rfl

/-- Inputs whose latest history is nonterminal. -/
def realizationDomain (time : ℕ) :
    Set (AnalyticArena.EventPrefix time × ℝ) :=
  {input |
    historyInformation
      (latestEventState time input.1) = false}

theorem realizationDomain_measurable (time : ℕ) :
    MeasurableSet (realizationDomain time) := by
  have hmeasurable :
      Measurable
        (fun input : AnalyticArena.EventPrefix time × ℝ =>
          historyInformation
            (latestEventState time input.1)) :=
    historyInformation_measurable.comp
      ((measurable_latestEventState time).comp measurable_fst)
  exact hmeasurable (measurableSet_singleton false)

/-- Fixed realization kernel: at a root prefix, realize the selected real
action in the root's concrete action fiber; at a terminal prefix, return zero
mass. -/
noncomputable def realizationKernel (time : ℕ) :
    Kernel
      (AnalyticArena.EventPrefix time × ℝ)
      AnalyticArena.ActionBundle := by
  classical
  exact
    Kernel.piecewise
      (realizationDomain_measurable time)
      (Kernel.deterministic
        (fun input => historyActionDecode input.2)
        (historyActionMeasurableEquiv.symm.measurable.comp measurable_snd))
      0

@[simp]
theorem realizationKernel_apply_nonterminal
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (action : ℝ)
    (hnonterminal :
      ¬ game.observed.base.isTerminal
        (latestEventState time events).1) :
    realizationKernel time (events, action) =
      Measure.dirac (historyActionDecode action) := by
  classical
  rw [realizationKernel, Kernel.piecewise_apply]
  have hroot :
      (latestEventState time events).1 = .root := by
    cases hstate : (latestEventState time events).1 with
    | root => rfl
    | terminal =>
        apply (hnonterminal ?_).elim
        rw [hstate]
        exact ⟨Empty.elim⟩
  have hdomain :
      (events, action) ∈ realizationDomain time := by
    exact
      historyInformation_eq_false_of_endpoint_root
        (latestEventState time events) hroot
  rw [
    if_pos hdomain,
    Kernel.deterministic_apply]
  rfl

@[simp]
theorem realizationKernel_apply_terminal
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (action : ℝ)
    (hterminal :
      game.observed.base.isTerminal
        (latestEventState time events).1) :
    realizationKernel time (events, action) = 0 := by
  classical
  rw [realizationKernel, Kernel.piecewise_apply]
  have hnotDomain :
      (events, action) ∉ realizationDomain time := by
    intro hdomain
    have hroot :
        (latestEventState time events).1 = .root :=
      endpoint_root_of_historyInformation_eq_false
        (latestEventState time events) hdomain
    rw [hroot] at hterminal
    change IsEmpty ℝ at hterminal
    exact hterminal.false 0
  rw [if_neg hnotDomain]
  rfl

/-- Fixed Borel real-action realization data. -/
noncomputable def realization :
    EventInformation.ActionRealization eventInformation where
  AbstractAction := fun _ => ℝ
  abstractActionMeasurable := fun _ => inferInstance
  kernel := realizationKernel
  kernel_isSFinite := by
    intro time
    unfold realizationKernel
    infer_instance

/-- The original behavioral law, exposed with its definitionally intended
real carrier. -/
def profileLaw
    (profile : game.observed.BehavioralProfile) :
    FiniteLaw ℝ := by
  change FiniteLaw (game.observed.InfoAction () rootInformation.1)
  exact profile () rootInformation

/-- Abstract law at root information; terminal information carries zero mass. -/
noncomputable def abstractMeasure
  (profile : game.observed.BehavioralProfile) :
    Bool → Measure ℝ
  | false => finiteLawMeasure(profileLaw profile)
  | true => 0

/-- Measurable abstract kernel for every original behavioral profile. -/
noncomputable def abstractKernel
    (profile : game.observed.BehavioralProfile) :
    Kernel Bool ℝ :=
  Kernel.ofFunOfCountable (abstractMeasure profile)

@[simp]
theorem abstractKernel_false
    (profile : game.observed.BehavioralProfile) :
    abstractKernel profile false =
      finiteLawMeasure(profileLaw profile) :=
  rfl

@[simp]
theorem abstractKernel_true
    (profile : game.observed.BehavioralProfile) :
    abstractKernel profile true = 0 :=
  rfl

/-- Every abstract kernel is finite. -/
theorem abstractKernel_isFinite
    (profile : game.observed.BehavioralProfile) :
    IsFiniteKernel (abstractKernel profile) := by
  refine ⟨⟨1, ENNReal.one_lt_top, ?_⟩⟩
  intro information
  cases information
  · rw [abstractKernel_false]
    haveI :
        IsProbabilityMeasure finiteLawMeasure(profileLaw profile) :=
      finiteLawMeasure_isProbability _
    exact le_of_eq measure_univ
  · rw [abstractKernel_true]
    simp

/-- Realized policy for an arbitrary original behavioral profile. -/
noncomputable def policy
    (profile : game.observed.BehavioralProfile) :
    EventInformation.RealizedActionPolicy realization where
  abstractKernel := fun _ => abstractKernel profile
  abstractKernel_isSFinite := by
    intro time
    change IsSFiniteKernel (abstractKernel profile)
    letI : IsFiniteKernel (abstractKernel profile) :=
      abstractKernel_isFinite profile
    infer_instance
  terminal_zero := by
    intro time events hterminal
    change
      IsEmpty
        (nodeAction (latestEventState time events).1) at hterminal
    change
      abstractKernel profile
        (historyInformation (latestEventState time events)) = 0
    have hterminalState :
        (latestEventState time events).1 = .terminal := by
      cases hstate : (latestEventState time events).1 with
      | root =>
          rw [hstate] at hterminal
          change IsEmpty ℝ at hterminal
          exact
            (hterminal.false (0 : ℝ)).elim
      | terminal => rfl
    have hcode :
        ∃ action,
          historyCode (latestEventState time events) =
            Sum.inr action := by
      cases hcode :
          historyCode (latestEventState time events) with
      | inl value =>
          have hroot :=
            endpoint_root_of_historyInformation_eq_false
              (latestEventState time events) (by
                unfold historyInformation
                rw [hcode])
          rw [hroot] at hterminalState
          contradiction
      | inr action =>
          exact ⟨action, rfl⟩
    rcases hcode with ⟨action, hcode⟩
    rw [historyInformation, hcode, abstractKernel_true]
  nonterminal_isProbability := by
    intro time events hnonterminal
    change
      ¬ IsEmpty
        (nodeAction (latestEventState time events).1) at hnonterminal
    change
      IsProbabilityMeasure
        (abstractKernel profile
          (historyInformation (latestEventState time events)))
    have hroot :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          have hempty :
              IsEmpty
                (nodeAction
                  (latestEventState time events).1) := by
            rw [hstate]
            exact ⟨Empty.elim⟩
          exact
            (hnonterminal hempty).elim
    rw [
      historyInformation_eq_false_of_endpoint_root
        (latestEventState time events) hroot,
      abstractKernel_false]
    exact finiteLawMeasure_isProbability _
  realization_isProbability := by
    intro time events hnonterminal
    change
      ¬ game.observed.base.isTerminal
        (latestEventState time events).1 at hnonterminal
    change
      ∀ᵐ action
          ∂abstractKernel profile
            (historyInformation (latestEventState time events)),
        IsProbabilityMeasure
          (realizationKernel time (events, action))
    exact Filter.Eventually.of_forall fun action => by
      rw [
        realizationKernel_apply_nonterminal
          time events action hnonterminal]
      constructor
      exact Measure.dirac_apply_of_mem (Set.mem_univ _)
  realization_legal := by
    intro time events hnonterminal
    change
      ¬ game.observed.base.isTerminal
        (latestEventState time events).1 at hnonterminal
    have hroot :
        latestEventState time events = rootHistory := by
      apply eq_rootHistory_of_endpoint_root
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          exact
            (hnonterminal (by
              rw [hstate]
              change IsEmpty Empty
              exact ⟨Empty.elim⟩)).elim
    change
      ∀ᵐ stateAction
          ∂(abstractKernel profile
              (historyInformation
                (latestEventState time events))).bind
            (Kernel.sectR
              (realizationKernel time) events),
        stateAction ∈
          AnalyticArena.actionFiber
            (latestEventState time events)
    letI : IsProbabilityMeasure
        (abstractKernel profile
          (historyInformation
            (latestEventState time events))) := by
      rw [hroot, historyInformation_root, abstractKernel_false]
      exact finiteLawMeasure_isProbability _
    apply
      MeasurableKernelArena.EventInformation.RealizedActionPolicy.ae_bind_mem_actionFiber_of_ae_mass_one
        (abstractKernel profile
          (historyInformation
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
        change (historyActionDecode action).1 =
          latestEventState time events
        rw [historyActionDecode_fst, hroot]

/-- Binding a root behavioral finite law through realization is exactly its concrete
root history/action-bundle law. -/
theorem bind_realization
    (profile : game.observed.BehavioralProfile)
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ game.observed.base.isTerminal
        (latestEventState time events).1) :
    finiteLawMeasure(profileLaw profile).bind
        (fun action => realizationKernel time (events, action)) =
      finiteLawMeasure(
        (profileLaw profile).map historyActionDecode) := by
  have hkernel :
      Measurable fun action : ℝ =>
        realizationKernel time (events, action) :=
    (realizationKernel time).measurable.comp
      (measurable_const.prodMk measurable_id)
  rw [FiniteLaw.map_atoms]
  induction (profileLaw profile).atoms with
  | nil =>
      simp only [List.map_nil, List.foldr_nil]
      exact Measure.bind_zero_left _
  | cons atom atoms ih =>
      rcases atom with ⟨action, weight⟩
      simp only [List.map_cons, List.foldr_cons]
      rw [measure_bind_add _ _ _ hkernel,
        Measure.bind_smul, Measure.dirac_bind hkernel,
        realizationKernel_apply_nonterminal
          time events action hnonterminal,
        ih]
      rfl

/-- At the unique root information state, the original concrete behavioral
law is the exposed real-valued profile law. -/
theorem actionLawAt_root
    (profile : game.observed.BehavioralProfile)
    (hmover :
      game.observed.base.mover rootHistory.1 = some ())
    (hnonterminal :
      ¬ game.observed.base.isTerminal rootHistory.1) :
    profile.actionLawAt game.observed rootHistory () hmover
        hnonterminal =
      profileLaw profile := by
  let hdecision :=
    game.observed.base.toArena.isDecision_of_not_isTerminal
      rootHistory.1 hnonterminal
  unfold
    ObservedGame.BehavioralProfile.actionLawAt
    ObservedGame.BehavioralStrategy.actionLawAt
    ControlledObservedGame.BehavioralStrategy.actionLawAt
    profileLaw
  change
    (profile ()
      (game.observed.representedInfoAt rootHistory () hmover
        hdecision)).map
        (game.observed.actionEquiv rootHistory () hmover
          hdecision) =
      profile () rootInformation
  have hinformation :
      game.observed.representedInfoAt rootHistory () hmover hdecision =
        rootInformation := Subtype.ext rfl
  rw [hinformation]
  have hequiv :
      game.observed.actionEquiv rootHistory () hmover
          hdecision =
        Equiv.refl ℝ := by
    rfl
  rw [hequiv]
  exact FiniteLaw.map_id _

/-- Packaging a root abstract action through the original dependent
`actionEquiv` is exactly the Borel legal-bundle decoding. -/
theorem package_player_action
    (history : History)
    (hmover :
      game.observed.base.mover history.1 = some ())
    (hnonterminal :
      ¬ game.observed.base.isTerminal history.1)
    (action : ℝ) :
    (⟨history,
      game.observed.actionEquiv history () hmover
        (game.observed.base.toArena.isDecision_of_not_isTerminal
          _ hnonterminal)
        action⟩ :
      HistoryAction) =
        historyActionDecode action := by
  have hrootEndpoint : history.1 = .root := by
    cases hstate : history.1 with
    | root => rfl
    | terminal =>
        change nodeMover history.1 = some () at hmover
        rw [hstate] at hmover
        exact (Option.some_ne_none () hmover.symm).elim
  have hroot :
      history = rootHistory :=
    eq_rootHistory_of_endpoint_root history hrootEndpoint
  subst history
  rfl

/-- The original player action law, after packaging in the current dependent
fiber, is exactly the real profile law mapped through legal-bundle decoding. -/
theorem packaged_actionLawAt
    (profile : game.observed.BehavioralProfile)
    (history : History)
    (hmover :
      game.observed.base.mover history.1 = some ())
    (hnonterminal :
      ¬ game.observed.base.isTerminal history.1) :
    (profile.actionLawAt game.observed history () hmover
      hnonterminal).map
        (fun action =>
          (⟨history, action⟩ : HistoryAction)) =
      (profileLaw profile).map historyActionDecode := by
  unfold
    ObservedGame.BehavioralProfile.actionLawAt
    ObservedGame.BehavioralStrategy.actionLawAt
    ControlledObservedGame.BehavioralStrategy.actionLawAt
  let hdecision :=
    game.observed.base.toArena.isDecision_of_not_isTerminal
      history.1 hnonterminal
  have hinformation :
      game.observed.representedInfoAt history () hmover hdecision =
        rootInformation := Subtype.ext rfl
  change
    (((profile ()
      (game.observed.representedInfoAt history () hmover
        hdecision)).map
      (game.observed.actionEquiv history () hmover hdecision)).map
      (fun action => (⟨history, action⟩ : HistoryAction))) = _
  rw [hinformation, FiniteLaw.map_comp]
  change
    (profileLaw profile).map
        ((fun action => (⟨history, action⟩ : HistoryAction)) ∘
          game.observed.actionEquiv history () hmover
            hdecision) =
      _
  congr 1
  funext action
  exact package_player_action history hmover hnonterminal action

/-- Explicit measurable presentation for every behavioral profile. -/
noncomputable def presentation :
    ObservedChanceGame.MeasurablePresentation
      game measurableHistoryModel where
  information := eventInformation
  realization := realization
  toPolicy := policy
  chanceKernel := fun _ => 0
  chanceKernel_isSFinite := fun _ => inferInstance
  chanceKernel_eq := by
    intro profile time events hnonterminal hmover
    have hfalse : False := by
      change
        nodeMover (latestEventState time events).1 = none at hmover
      change
        ¬ IsEmpty
          (nodeAction (latestEventState time events).1) at hnonterminal
      cases hstate : (latestEventState time events).1 with
      | root =>
          rw [hstate] at hmover
          exact Option.some_ne_none () hmover
      | terminal =>
        apply hnonterminal
        rw [hstate]
        change IsEmpty Empty
        exact ⟨Empty.elim⟩
    exact hfalse.elim

  playerInformation := fun _ _ => false
  player_informationAt := by
    intro time events i hmover _hnonterminal
    cases i
    have hroot :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          change nodeMover (latestEventState time events).1 = some () at hmover
          rw [hstate] at hmover
          exact (Option.some_ne_none () hmover.symm).elim
    change
      historyInformation (latestEventState time events) = false
    exact
      historyInformation_eq_false_of_endpoint_root
        (latestEventState time events) hroot
  player_realizedKernel := by
    intro profile time events hnonterminal i hmover
    cases i
    rw [EventInformation.RealizedActionPolicy.realizedKernel_apply]
    change
      (abstractKernel profile
        (historyInformation (latestEventState time events))).bind
          (fun action => realizationKernel time (events, action)) =
        _
    have hroot :
        (latestEventState time events).1 = .root := by
      cases hstate : (latestEventState time events).1 with
      | root => rfl
      | terminal =>
          change nodeMover (latestEventState time events).1 = some () at hmover
          rw [hstate] at hmover
          exact (Option.some_ne_none () hmover.symm).elim
    rw [
      historyInformation_eq_false_of_endpoint_root
        (latestEventState time events) hroot,
      abstractKernel_false]
    have hpackaged :=
      packaged_actionLawAt
        profile (latestEventState time events) hmover
          hnonterminal
    exact
      (bind_realization profile time events hnonterminal).trans
        (congrArg
          (fun law : FiniteLaw HistoryAction =>
            finiteLawMeasure(law))
          hpackaged.symm)
  chance_realizedKernel := by
    intro profile time events hnonterminal hmover
    have hfalse : False := by
      change
        nodeMover (latestEventState time events).1 = none at hmover
      change
        ¬ IsEmpty
          (nodeAction (latestEventState time events).1) at hnonterminal
      cases hstate : (latestEventState time events).1 with
      | root =>
          rw [hstate] at hmover
          exact Option.some_ne_none () hmover
      | terminal =>
        apply hnonterminal
        rw [hstate]
        change IsEmpty Empty
        exact ⟨Empty.elim⟩
    exact hfalse.elim

/-- Exact concrete player kernel for every profile and event prefix. -/
theorem compiled_player_kernel_exact
    (profile : game.observed.BehavioralProfile)
    (time : ℕ)
    (events : AnalyticArena.EventPrefix time)
    (hnonterminal :
      ¬ game.observed.base.isTerminal
        (latestEventState time events).1)
    (hmover :
      game.observed.base.mover
          (latestEventState time events).1 =
        some ()) :
    (presentation.compiledPolicy profile).kernel time events =
      finiteLawMeasure(
        (profile.actionLawAt game.observed
            (latestEventState time events)
            () hmover hnonterminal).map
          (fun action =>
            (⟨latestEventState time events, action⟩ :
              AnalyticArena.ActionBundle))) :=
  presentation.compiledPolicy_kernel_of_mover
    profile time events hnonterminal () hmover

/-- The generalized presentation supplies the complete joint event-path law. -/
noncomputable def eventPathLaw
    (profile : game.observed.BehavioralProfile) :
    Measure (ℕ → AnalyticArena.PathEvent) :=
  presentation.eventPathMeasure profile rootHistory

/-- The generalized presentation supplies the complete state-path law. -/
noncomputable def statePathLaw
    (profile : game.observed.BehavioralProfile) :
    Measure (ℕ → AnalyticArena.State) :=
  presentation.statePathMeasure profile rootHistory

end Examples.ObservedChanceMeasurableUncountableBoundary
