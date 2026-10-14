/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution
import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# EconCSLib.Examples.ExtensiveGame.RootScopedKuhn

Finite guarding example **N-2** for the root-scoped boundary of constructive
mixed-to-behavioral realization.

The one-player game has two decisions. The information state at the second
decision remembers the first action, so the game has perfect recall. A fair
coin selects either the always-false or always-true complete pure plan; the
resulting mixed plan therefore correlates choices across information states.

The existing Kuhn construction behavioralizes this plan relative to an
explicitly selected continuation root. The named theorems below prove both
sides of the semantic boundary:

* exact bounded payoff-law realization and deviation coverage at every
  separately selected root; and
* a universally quantified impossibility theorem: no single behavioral
  profile realizes both the initial-root law at fuel `2` and the freshly
  resampled post-`false` continuation law at fuel `1`.

The negative theorem rules out the incorrect root-independent global lift. It
does not challenge either root-scoped construction, finite Kuhn rootwise-Nash
transfer, or the usual realization equivalence at one selected root. Mixed and
behavioral strategies also remain different strategy objects even where their
induced laws agree.
-/

namespace Examples.RootScopedKuhn

open ExtensiveGame

/-- Finite stages of the two-decision perfect-recall game. -/
inductive Stage
  | start
  | after (first : Bool)
  | done (first second : Bool)
  deriving DecidableEq

instance : Fintype Stage where
  elems := {.start, .after false, .after true,
    .done false false, .done false true,
    .done true false, .done true true}
  complete := by
    intro stage
    cases stage with
    | start => simp
    | after first => cases first <;> simp
    | done first second => cases first <;> cases second <;> simp

/-- Both decision stages offer a Boolean action; completed stages are
terminal. -/
def stageAction : Stage → Type
  | .start => Bool
  | .after _ => Bool
  | .done _ _ => PEmpty

/-- The first action is retained in the intermediate state and both actions
are retained at the terminal state. -/
def stageNext : (stage : Stage) → stageAction stage → Stage
  | .start, first => .after first
  | .after first, second => .done first second
  | .done _ _, action => nomatch action

/-- The sole player controls both decision stages. -/
def stageMover : Stage → Option Unit
  | .start => some ()
  | .after _ => some ()
  | .done _ _ => none

/-- Terminal payoffs record both actions, making complete bounded laws
observable. -/
def payoff : Stage → Unit → Bool × Bool
  | .done first second, _ => (first, second)
  | _, _ => (false, false)

/-- Base deterministic extensive game for the root-scoped Kuhn regression. -/
def base : ExtensiveGame Unit (Bool × Bool) where
  State := Stage
  Action := stageAction
  next := stageNext
  init := .start
  mover := stageMover
  payoff := payoff

/-- Perfect-recall decision information: the second information state records
the first action. -/
inductive DecisionInfo
  | first
  | second (firstAction : Bool)
  deriving DecidableEq

instance : Fintype DecisionInfo where
  elems := {.first, .second false, .second true}
  complete := by
    intro information
    cases information <;> simp

/-- The observation associated with each game stage. -/
def observe : Stage → Option DecisionInfo
  | .start => some .first
  | .after first => some (.second first)
  | .done _ _ => none

/-- Extract decision information from a player-controlled stage. -/
def infoAtState :
    (stage : Stage) → stageMover stage = some () → DecisionInfo
  | .start, _ => .first
  | .after first, _ => .second first
  | .done _ _, h => absurd h (by simp [stageMover])

/-- Boolean abstract actions coincide with concrete legal actions at both
decision stages. -/
def actionEquiv :
    (stage : Stage) → stageMover stage = some () →
      (Bool ≃ stageAction stage)
  | .start, _ => Equiv.refl Bool
  | .after _, _ => Equiv.refl Bool
  | .done _ _, h => absurd h (by simp [stageMover])

private theorem infoAtState_observe (stage : Stage)
    (hmover : stageMover stage = some ()) :
    some (infoAtState stage hmover) = observe stage := by
  cases stage <;>
    simp [infoAtState, observe, stageMover] at hmover ⊢

/-- The finite observed game whose second decision remembers the first
action. -/
def observed : ObservedGame Unit (Bool × Bool) where
  base := base
  Observation := fun _ => Option DecisionInfo
  PublicObservation := Option DecisionInfo
  observe := fun _ history => observe history.1
  publicObserve := fun history => observe history.1
  publicOf := fun _ observation => observation
  observe_public := fun _ _ => rfl
  InfoState := fun _ => DecisionInfo
  infoObserve := fun _ information => some information
  infoAt := fun history _ hmover _ =>
    infoAtState history.1 hmover
  infoAt_observe := by
    intro history i hmover hnonterminal
    cases i
    exact infoAtState_observe history.1 hmover
  InfoAction := fun _ _ => Bool
  actionEquiv := fun history _ hmover _ =>
    actionEquiv history.1 hmover

/-- The represented strategy coordinate at the initial decision. -/
private def firstInformation : observed.RepresentedInfo () :=
  observed.representedInfoAt
    ⟨Stage.start, Arena.History.nil⟩ () rfl ⟨false⟩

private theorem ownDecisionHistory_at_mover
    (history :
      observed.base.toArena.HistoryFrom
        observed.base.init)
    (hmover :
      observed.base.mover history.1 = some ()) :
    observed.ownDecisionHistory () history =
      match history.1 with
      | .start => []
      | .after first =>
          [⟨firstInformation, first⟩]
      | .done _ _ => [] := by
  rcases history with ⟨finish, path⟩
  induction path with
  | nil => rfl
  | @snoc previous path action ih =>
      cases previous with
      | start =>
          have hpath := ih rfl
          change
            observed.ownDecisionHistory () ⟨Stage.start, path⟩ =
              [] at hpath
          rw [observed.ownDecisionHistory_snoc_of_mover
            () path action rfl, hpath]
          rfl
      | after first =>
          simp [observed, base, stageNext, stageMover] at hmover
      | done first second => exact nomatch action

/-- The concrete finite game has perfect recall: equal second-stage
information states remember the same first action. -/
theorem observed_perfectRecall :
    observed.PerfectRecall := by
  intro i
  cases i
  intro first second hfirst hfirst_nonterminal
    hsecond hsecond_nonterminal hsame
  change
    observed.ownDecisionHistory () first =
      observed.ownDecisionHistory () second
  rw [ownDecisionHistory_at_mover first hfirst,
    ownDecisionHistory_at_mover second hsecond]
  rcases first with ⟨firstState, firstPath⟩
  rcases second with ⟨secondState, secondPath⟩
  cases firstState with
  | start =>
      cases secondState with
      | start => rfl
      | after action =>
          simp [ObservedGame.toControlledObservedGame,
            observed, infoAtState] at hsame
      | done _ _ =>
          simp [observed, base, stageMover] at hsecond
  | after firstAction =>
      cases secondState with
      | start =>
          simp [ObservedGame.toControlledObservedGame,
            observed, infoAtState] at hsame
      | after secondAction =>
          have haction : firstAction = secondAction := by
            simpa [ObservedGame.toControlledObservedGame,
              observed, infoAtState] using
              congrArg
                (fun information =>
                  match information with
                  | DecisionInfo.first => false
                  | DecisionInfo.second action => action)
                hsame
          subst secondAction
          rfl
      | done _ _ =>
          simp [observed, base, stageMover] at hsecond
  | done _ _ =>
      simp [observed, base, stageMover] at hfirst

/-- The hypotheses required by the constructive finite Kuhn API hold for the
concrete game. -/
def hypotheses :
    observed.FiniteKuhnHypotheses where
  recallCertificate := {
    remembered := fun _player information =>
      match information.1 with
      | .first => []
      | .second firstAction => [⟨firstInformation, firstAction⟩]
    remembered_infoAt := by
      intro player history hmover _hdecision
      cases player
      rcases history with ⟨state, path⟩
      cases state with
      | start =>
          simpa [ControlledDecisionGame.representedInfoAt,
            observed, infoAtState] using
            (ownDecisionHistory_at_mover
              ⟨Stage.start, path⟩ hmover).symm
      | after firstAction =>
          simpa [ControlledDecisionGame.representedInfoAt,
            observed, infoAtState] using
            (ownDecisionHistory_at_mover
              ⟨Stage.after firstAction, path⟩ hmover).symm
      | done firstAction secondAction =>
          simp [observed, base, stageMover] at hmover }
  finiteDecisionPresentation := by
    intro player
    cases player
    let secondInformation (firstAction : Bool) :
        observed.RepresentedInfo () :=
      observed.representedInfoAt
        ⟨Stage.after firstAction,
          (Arena.History.nil :
            observed.base.toArena.History Stage.start Stage.start).snoc
              firstAction⟩
        () rfl ⟨false⟩
    let representedInformationEquiv :
        observed.RepresentedInfo () ≃ DecisionInfo :=
      { toFun := fun information => information.1
        invFun := fun information =>
          match information with
          | .first => firstInformation
          | .second firstAction => secondInformation firstAction
        left_inv := by
          rintro ⟨information, witness⟩
          apply Subtype.ext
          cases information with
          | first => rfl
          | second firstAction => cases firstAction <;> rfl
        right_inv := by
          intro information
          cases information with
          | first => rfl
          | second firstAction => cases firstAction <;> rfl }
    let decisionInformationEquiv : DecisionInfo ≃ Fin 1 ⊕ Fin 2 :=
      { toFun := fun information =>
          match information with
          | .first => Sum.inl 0
          | .second firstAction =>
              Sum.inr (finTwoEquiv.symm firstAction)
        invFun := fun index =>
          match index with
          | .inl _ => .first
          | .inr secondIndex => .second (finTwoEquiv secondIndex)
        left_inv := by
          intro information
          cases information with
          | first => rfl
          | second firstAction => simp
        right_inv := by
          intro index
          cases index with
          | inl firstIndex =>
              apply congrArg Sum.inl
              exact Subsingleton.elim _ _
          | inr secondIndex => simp }
    let informationEquiv : observed.RepresentedInfo () ≃ Fin 3 :=
      representedInformationEquiv.trans
        (decisionInformationEquiv.trans finSumFinEquiv)
    exact
      ⟨⟨3, informationEquiv⟩,
        fun _information => by
          change DecidableEq Bool
          infer_instance⟩

/-- The concrete game contains no chance-controlled decision stage. -/
theorem base_noChance : observed.base.NoChanceOnHistories := by
  intro history hnonterminal
  rcases history with ⟨state, _path⟩
  cases state with
  | start => exact ⟨(), rfl⟩
  | after first => exact ⟨(), rfl⟩
  | done first second =>
      exact
        (hnonterminal
          ⟨fun action => nomatch action⟩).elim

/-- View the deterministic example through the normalized chance-EFG API. -/
def chanceGame :
    ObservedChanceGame Unit (Bool × Bool) :=
  ObservedChanceGame.ofNoChance
    observed base_noChance

instance :
    (state : chanceGame.observed.base.State) →
      Decidable
        (chanceGame.observed.base.isTerminal state)
  | .start => isFalse (by
      intro h
      exact h.false false)
  | .after _ => isFalse (by
      intro h
      exact h.false false)
  | .done _ _ =>
      isTrue ⟨fun action => nomatch action⟩

/-- The initial continuation root. -/
def initialRoot :
    observed.base.toArena.HistoryFrom
      observed.base.init :=
  ⟨Stage.start, Arena.History.nil⟩

/-- The typed concrete action choosing `false` at the initial decision. -/
def chooseFalse :
    observed.base.Action Stage.start :=
  false

/-- A concrete second-stage continuation after choosing `false` first. -/
def afterFalseRoot :
    observed.base.toArena.HistoryFrom
      observed.base.init :=
  ⟨Stage.after false,
    Arena.History.nil.snoc chooseFalse⟩

/-- Fair Boolean law used to select a complete correlated plan. -/
def fairCoin : FiniteLaw Bool where
  atoms := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

/-- A complete pure plan choosing the same Boolean action at every information
state. -/
def constantPlan (choice : Bool) :
    observed.PureStrategy () :=
  fun _ => choice

/-- A mixed strategy supported on the always-false and always-true plans.
Choices at distinct information states are therefore perfectly correlated. -/
def correlatedStrategy :
    observed.MixedStrategy () :=
  fairCoin.map constantPlan

/-- The one-player mixed profile carrying the correlated complete-plan law. -/
def correlatedProfile :
    observed.MixedProfile :=
  fun _ => correlatedStrategy

/-! ### Explicit bounded-law calculations -/

private def payoffOutcome (first second : Bool) :
    Option (Unit → Bool × Bool) :=
  some (fun _ => (first, second))

private abbrev afterRoot (first : Bool) :
    observed.base.toArena.HistoryFrom observed.base.init :=
  ⟨.after first,
    Arena.History.nil.snoc
      (show observed.base.Action .start from first)⟩

private theorem afterStage_not_terminal (first : Bool) :
    ¬ chanceGame.observed.base.isTerminal (.after first) := by
  intro h
  exact h.false false

private theorem afterRoot_not_terminal (first : Bool) :
    ¬ chanceGame.observed.base.isTerminal (afterRoot first).1 :=
  afterStage_not_terminal first

/-- The represented strategy coordinate at the second decision after
`first`. -/
private def secondInformation (first : Bool) :
    observed.RepresentedInfo () :=
  observed.representedInfoAt
    (afterRoot first) () rfl ⟨false⟩

private theorem done_terminal (first second : Bool) :
    base.isTerminal (.done first second) :=
  ⟨fun action => nomatch action⟩

private abbrev terminalRoot (first second : Bool) :
    observed.base.toArena.HistoryFrom observed.base.init :=
  ⟨.done first second,
    (afterRoot first).2.snoc
      (show observed.base.Action (.after first) from second)⟩

private theorem stoppedPayoff_terminalRoot (first second : Bool) :
    chanceGame.stoppedPayoffAtHistory (terminalRoot first second) =
      payoffOutcome first second := by
  unfold ObservedChanceGame.stoppedPayoffAtHistory
  have hterminal :
      chanceGame.observed.base.isTerminal
        (terminalRoot first second).1 :=
    done_terminal first second
  rw [if_pos hterminal]
  rfl

private theorem actionLaw_afterRoot
    (behavioral : observed.BehavioralProfile)
    (first : Bool) :
    ObservedGame.BehavioralStrategy.actionLawAt
        observed (behavioral ()) (afterRoot first) rfl
        (afterRoot_not_terminal first) =
      behavioral () (secondInformation first) := by
  unfold ObservedGame.BehavioralStrategy.actionLawAt
  change
    (behavioral () (secondInformation first)).map id =
      behavioral () (secondInformation first)
  exact FiniteLaw.map_id _

private theorem chanceActionLaw_afterRoot
    (behavioral : observed.BehavioralProfile)
    (first : Bool) :
    ObservedGame.BehavioralStrategy.actionLawAt
        chanceGame.observed (behavioral ())
        (afterRoot first) rfl
        (afterRoot_not_terminal first) =
      behavioral () (secondInformation first) :=
  actionLaw_afterRoot behavioral first

private theorem behavioralLaw_afterRoot
    (behavioral : observed.BehavioralProfile)
    (first : Bool) :
    chanceGame.behavioralStoppedPayoffLawFrom
        behavioral (afterRoot first) 1 =
      (behavioral () (secondInformation first)).map
        (fun second => payoffOutcome first second) := by
  unfold ObservedChanceGame.behavioralStoppedPayoffLawFrom
  rw [Arena.stochasticHistoryLawFrom]
  simp only [afterStage_not_terminal, ↓reduceDIte]
  rw [ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover
    _ _ _ (afterRoot_not_terminal first) () rfl]
  unfold ObservedGame.BehavioralProfile.actionLawAt
  rw [chanceActionLaw_afterRoot]
  rw [FiniteLaw.map_bind]
  change
    (behavioral () (secondInformation first)).bind
        (fun second =>
          (FiniteLaw.pure (terminalRoot first second)).map
            chanceGame.stoppedPayoffAtHistory) =
      _
  have hinner :
      (fun second =>
        (FiniteLaw.pure (terminalRoot first second)).map
          chanceGame.stoppedPayoffAtHistory) =
        (FiniteLaw.pure ∘
          fun second => payoffOutcome first second) := by
    funext second
    calc
      (FiniteLaw.pure (terminalRoot first second)).map
          chanceGame.stoppedPayoffAtHistory =
        FiniteLaw.pure
          (chanceGame.stoppedPayoffAtHistory
            (terminalRoot first second)) :=
        FiniteLaw.pure_map _ _
      _ = FiniteLaw.pure (payoffOutcome first second) :=
        congrArg FiniteLaw.pure
          (stoppedPayoff_terminalRoot first second)
  change
    (behavioral () (secondInformation first)).bind
        (fun second =>
          (FiniteLaw.pure (terminalRoot first second)).map
            chanceGame.stoppedPayoffAtHistory) =
      _
  calc
    _ =
        (behavioral () (secondInformation first)).bind
          (FiniteLaw.pure ∘
            fun second => payoffOutcome first second) :=
      congrArg
        (fun continuation =>
          (behavioral () (secondInformation first)).bind continuation)
        hinner
    _ = _ :=
      (FiniteLaw.map_eq_bind_pure_comp
        (fun second => payoffOutcome first second)
        (behavioral () (secondInformation first))).symm

private theorem afterFalseRoot_eq :
    afterFalseRoot = afterRoot false :=
  rfl

private theorem initial_not_terminal :
    ¬ chanceGame.observed.base.isTerminal initialRoot.1 := by
  intro h
  exact h.false false

private theorem actionLaw_initial
    (behavioral : observed.BehavioralProfile) :
    ObservedGame.BehavioralStrategy.actionLawAt
        chanceGame.observed (behavioral ())
        initialRoot rfl initial_not_terminal =
      behavioral () firstInformation := by
  unfold ObservedGame.BehavioralStrategy.actionLawAt
  change
    (behavioral () firstInformation).map id =
      behavioral () firstInformation
  exact FiniteLaw.map_id _

private theorem behavioralLaw_initial
    (behavioral : observed.BehavioralProfile) :
    chanceGame.behavioralStoppedPayoffLawFrom
        behavioral initialRoot 2 =
      (behavioral () firstInformation).bind fun first =>
        (behavioral () (secondInformation first)).map
          (fun second => payoffOutcome first second) := by
  unfold ObservedChanceGame.behavioralStoppedPayoffLawFrom
  rw [Arena.stochasticHistoryLawFrom]
  simp only [initial_not_terminal, ↓reduceDIte]
  rw [ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover
    _ _ _ initial_not_terminal () rfl]
  unfold ObservedGame.BehavioralProfile.actionLawAt
  rw [actionLaw_initial]
  rw [FiniteLaw.map_bind]
  have hinner :
      (fun first =>
        (chanceGame.observed.base.toArena.stochasticHistoryLawFrom
          (ObservedChanceGame.BehavioralProfile.toHistoryPolicy
            chanceGame behavioral)
          (afterRoot first) 1).map
            chanceGame.stoppedPayoffAtHistory) =
        (fun first =>
          (behavioral () (secondInformation first)).map
            (fun second => payoffOutcome first second)) := by
    funext first
    change
      chanceGame.behavioralStoppedPayoffLawFrom
          behavioral (afterRoot first) 1 =
        _
    exact behavioralLaw_afterRoot behavioral first
  change
    (behavioral () firstInformation).bind
        (fun first =>
          (chanceGame.observed.base.toArena.stochasticHistoryLawFrom
            (ObservedChanceGame.BehavioralProfile.toHistoryPolicy
              chanceGame behavioral)
            (afterRoot first) 1).map
              chanceGame.stoppedPayoffAtHistory) =
      _
  exact congrArg
    (fun continuation =>
      (behavioral () firstInformation).bind continuation)
    hinner

private theorem payoffOutcome_injective (first : Bool) :
    Function.Injective (payoffOutcome first) := by
  intro left right h
  have hsecond :=
    congrArg
      (fun outcome =>
        Option.map (fun value => (value ()).2) outcome)
      h
  simpa [payoffOutcome] using hsecond

private theorem payoffOutcome_ne_of_first_ne
    {first other : Bool} (hne : first ≠ other)
    (second otherSecond : Bool) :
    payoffOutcome first second ≠
      payoffOutcome other otherSecond := by
  intro h
  have hfirst :=
    congrArg
      (fun outcome =>
        Option.map (fun value => (value ()).1) outcome)
      h
  exact hne (by simpa [payoffOutcome] using hfirst)

private theorem FiniteLaw.mass_map_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (law : FiniteLaw α) (f : α → β)
    (hf : Function.Injective f) (outcome : α) :
    (law.map f).mass (f outcome) = law.mass outcome := by
  unfold FiniteLaw.mass FiniteLaw.eventMass
  rw [FiniteLaw.map_atoms, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro atom _
  simp [hf.eq_iff]

private theorem FiniteLaw.mass_bind_bool
    {α : Type*} [DecidableEq α]
    (law : FiniteLaw Bool) (next : Bool → FiniteLaw α)
    (outcome : α) :
    (law.bind next).mass outcome =
      law.mass false * (next false).mass outcome +
        law.mass true * (next true).mass outcome := by
  rw [FiniteLaw.mass_bind]
  unfold FiniteLaw.mass FiniteLaw.eventMass
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨choice, weight⟩
      cases choice <;>
        simp only [List.map_cons, List.sum_cons, Bool.false_eq_true,
          Bool.true_eq_false, decide_false, decide_true, if_false, if_true]
      · rw [ih]
        ring
      · rw [ih]
        ring

private theorem FiniteLaw.Equivalent.mass
    {α : Type*} [DecidableEq α]
    {left right : FiniteLaw α} (h : left.Equivalent right)
    (outcome : α) :
    left.mass outcome = right.mass outcome := by
  exact h.eventMass (fun candidate => decide (candidate = outcome))

private theorem behavioralLaw_initial_apply_false
    (behavioral : observed.BehavioralProfile)
    (second : Bool) :
    (chanceGame.behavioralStoppedPayoffLawFrom
        behavioral initialRoot 2).mass (payoffOutcome false second) =
      (show FiniteLaw Bool from
        behavioral () firstInformation).mass false *
        (show FiniteLaw Bool from
          behavioral () (secondInformation false)).mass second := by
  rw [behavioralLaw_initial]
  change
    ((show FiniteLaw Bool from
      behavioral () firstInformation).bind fun first : Bool =>
        (show FiniteLaw Bool from
          behavioral () (secondInformation first)).map
            (payoffOutcome first)).mass (payoffOutcome false second) = _
  rw [FiniteLaw.mass_bind_bool]
  have hfalse :
      ((behavioral () (secondInformation false)).map
          (payoffOutcome false)).mass (payoffOutcome false second) =
        (show FiniteLaw Bool from
          behavioral () (secondInformation false)).mass second :=
    FiniteLaw.mass_map_of_injective
      (show FiniteLaw Bool from
        behavioral () (secondInformation false))
      (payoffOutcome false)
      (payoffOutcome_injective false)
      second
  rw [hfalse]
  have htrue :
      ((show FiniteLaw Bool from
        behavioral () (secondInformation true)).map
          (payoffOutcome true)).mass (payoffOutcome false second) = 0 := by
    unfold FiniteLaw.mass FiniteLaw.eventMass
    rw [FiniteLaw.map_atoms, List.map_map]
    apply List.sum_eq_zero
    intro weight hweight
    rw [List.mem_map] at hweight
    obtain ⟨atom, _, rfl⟩ := hweight
    rcases atom with ⟨choice, atomWeight⟩
    simp only [Function.comp_apply]
    simp [payoffOutcome_ne_of_first_ne
      (by decide : true ≠ false) choice second]
  rw [htrue, mul_zero, add_zero]

private theorem behavioralLaw_afterFalse_apply
    (behavioral : observed.BehavioralProfile)
    (second : Bool) :
    (chanceGame.behavioralStoppedPayoffLawFrom
        behavioral afterFalseRoot 1).mass (payoffOutcome false second) =
      (show FiniteLaw Bool from
        behavioral () (secondInformation false)).mass second := by
  rw [afterFalseRoot_eq, behavioralLaw_afterRoot]
  change
    ((show FiniteLaw Bool from
      behavioral () (secondInformation false)).map
        (payoffOutcome false)).mass (payoffOutcome false second) = _
  exact
    FiniteLaw.mass_map_of_injective
      (show FiniteLaw Bool from
        behavioral () (secondInformation false))
      (payoffOutcome false)
      (payoffOutcome_injective false)
      second

private def singletonProfileEquiv :
    observed.PureStrategy () ≃ observed.PureProfile where
  toFun := fun strategy _ => strategy
  invFun := fun profile => profile ()
  left_inv := fun _ => rfl
  right_inv := by
    intro profile
    funext i
    cases i
    rfl

private theorem correlatedProfile_pureProfileLaw :
    (correlatedProfile.pureProfileLaw observed).Equivalent
      (correlatedStrategy.map singletonProfileEquiv) := by
  have hmarginal :=
    (FiniteLaw.fintypePi_map_apply correlatedProfile ()).map
      singletonProfileEquiv
  rw [FiniteLaw.map_comp] at hmarginal
  have hidentity :
      (singletonProfileEquiv ∘ fun profile : observed.PureProfile =>
        profile ()) = id := by
    funext profile
    funext i
    cases i
    rfl
  have hlaw :
      (FiniteLaw.fintypePi correlatedProfile).map
          (singletonProfileEquiv ∘
            fun profile : observed.PureProfile => profile ()) =
        FiniteLaw.fintypePi correlatedProfile := by
    rw [hidentity, FiniteLaw.map_id]
  have hresult :
      (FiniteLaw.fintypePi correlatedProfile).Equivalent
        (correlatedStrategy.map singletonProfileEquiv) :=
    (FiniteLaw.Equivalent.of_eq hlaw.symm).trans hmarginal
  exact hresult

private theorem correlatedProfile_pureProfileLaw_chance :
    (correlatedProfile.pureProfileLaw chanceGame.observed).Equivalent
      (correlatedStrategy.map singletonProfileEquiv) :=
  correlatedProfile_pureProfileLaw

private theorem constantProfile_behavioralLaw_initial (choice : Bool) :
    chanceGame.behavioralStoppedPayoffLawFrom
        ((singletonProfileEquiv
          (constantPlan choice)).toBehavioral observed)
        initialRoot 2 =
      FiniteLaw.pure (payoffOutcome choice choice) := by
  rw [behavioralLaw_initial]
  simp [singletonProfileEquiv,
    ObservedGame.PureProfile.toBehavioral,
    ObservedGame.PureStrategy.toBehavioral,
    constantPlan, FiniteLaw.pure_bind]
  exact FiniteLaw.pure_map _ _

private theorem constantProfile_behavioralLaw_afterFalse (choice : Bool) :
    chanceGame.behavioralStoppedPayoffLawFrom
        ((singletonProfileEquiv
          (constantPlan choice)).toBehavioral observed)
        afterFalseRoot 1 =
      FiniteLaw.pure (payoffOutcome false choice) := by
  rw [afterFalseRoot_eq, behavioralLaw_afterRoot]
  simp [singletonProfileEquiv,
    ObservedGame.PureProfile.toBehavioral,
    ObservedGame.PureStrategy.toBehavioral,
    constantPlan]
  exact FiniteLaw.pure_map _ _

private theorem mixedLaw_initial :
    (chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile initialRoot 2).Equivalent
      (fairCoin.map (fun choice => payoffOutcome choice choice)) := by
  unfold ObservedChanceGame.mixedStoppedPayoffLawFrom
  let continuation :=
    fun pureProfile : observed.PureProfile =>
      chanceGame.behavioralStoppedPayoffLawFrom
        (pureProfile.toBehavioral chanceGame.observed)
        initialRoot 2
  apply (correlatedProfile_pureProfileLaw_chance.bind fun _ =>
    FiniteLaw.Equivalent.refl _).trans
  apply FiniteLaw.Equivalent.of_eq
  calc
    (correlatedStrategy.map singletonProfileEquiv).bind continuation =
        correlatedStrategy.bind
          (continuation ∘ singletonProfileEquiv) :=
      FiniteLaw.bind_map correlatedStrategy singletonProfileEquiv continuation
    _ =
        (fairCoin.map constantPlan).bind
          (continuation ∘ singletonProfileEquiv) := rfl
    _ =
        fairCoin.bind
          ((continuation ∘ singletonProfileEquiv) ∘ constantPlan) :=
      FiniteLaw.bind_map fairCoin constantPlan
        (continuation ∘ singletonProfileEquiv)
    _ =
        fairCoin.bind
          (FiniteLaw.pure ∘
            fun choice => payoffOutcome choice choice) := by
      apply congrArg (FiniteLaw.bind fairCoin)
      funext choice
      exact constantProfile_behavioralLaw_initial choice
    _ = _ :=
      (FiniteLaw.map_eq_bind_pure_comp
        (fun choice => payoffOutcome choice choice) fairCoin).symm

private theorem mixedLaw_afterFalse :
    (chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile afterFalseRoot 1).Equivalent
      (fairCoin.map (payoffOutcome false)) := by
  unfold ObservedChanceGame.mixedStoppedPayoffLawFrom
  let continuation :=
    fun pureProfile : observed.PureProfile =>
      chanceGame.behavioralStoppedPayoffLawFrom
        (pureProfile.toBehavioral chanceGame.observed)
        afterFalseRoot 1
  apply (correlatedProfile_pureProfileLaw_chance.bind fun _ =>
    FiniteLaw.Equivalent.refl _).trans
  apply FiniteLaw.Equivalent.of_eq
  calc
    (correlatedStrategy.map singletonProfileEquiv).bind continuation =
        correlatedStrategy.bind
          (continuation ∘ singletonProfileEquiv) :=
      FiniteLaw.bind_map correlatedStrategy singletonProfileEquiv continuation
    _ =
        (fairCoin.map constantPlan).bind
          (continuation ∘ singletonProfileEquiv) := rfl
    _ =
        fairCoin.bind
          ((continuation ∘ singletonProfileEquiv) ∘ constantPlan) :=
      FiniteLaw.bind_map fairCoin constantPlan
        (continuation ∘ singletonProfileEquiv)
    _ =
        fairCoin.bind
          (FiniteLaw.pure ∘ payoffOutcome false) := by
      apply congrArg (FiniteLaw.bind fairCoin)
      funext choice
      exact constantProfile_behavioralLaw_afterFalse choice
    _ = _ :=
      (FiniteLaw.map_eq_bind_pure_comp
        (payoffOutcome false) fairCoin).symm

private theorem diagonalPayoffOutcome_injective :
    Function.Injective
      (fun choice => payoffOutcome choice choice) := by
  intro left right h
  have hfirst :=
    congrArg
      (fun outcome =>
        Option.map (fun value => (value ()).1) outcome)
      h
  simpa [payoffOutcome] using hfirst

private theorem mixedLaw_initial_falseFalse :
    (chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile initialRoot 2).mass
        (payoffOutcome false false) =
      (1 / 2 : ℚ≥0) := by
  rw [FiniteLaw.Equivalent.mass mixedLaw_initial]
  rw [FiniteLaw.mass_map_of_injective fairCoin
    (fun choice => payoffOutcome choice choice)
    diagonalPayoffOutcome_injective false]
  norm_num [fairCoin, FiniteLaw.mass, FiniteLaw.eventMass]

private theorem mixedLaw_initial_falseTrue :
    (chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile initialRoot 2).mass
        (payoffOutcome false true) =
      0 := by
  rw [FiniteLaw.Equivalent.mass mixedLaw_initial]
  have hfalse :
      payoffOutcome false true ≠
        payoffOutcome false false :=
    fun h =>
      Bool.noConfusion
        (payoffOutcome_injective false h)
  have htrue :
      payoffOutcome false true ≠
        payoffOutcome true true :=
    payoffOutcome_ne_of_first_ne Bool.false_ne_true _ _
  unfold FiniteLaw.mass FiniteLaw.eventMass
  rw [FiniteLaw.map_atoms, List.map_map]
  norm_num [fairCoin, Ne.symm hfalse, Ne.symm htrue]

private theorem mixedLaw_afterFalse_apply (second : Bool) :
    (chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile afterFalseRoot 1).mass
        (payoffOutcome false second) =
      (1 / 2 : ℚ≥0) := by
  rw [FiniteLaw.Equivalent.mass mixedLaw_afterFalse]
  rw [FiniteLaw.mass_map_of_injective fairCoin
    (payoffOutcome false) (payoffOutcome_injective false) second]
  cases second <;>
    norm_num [fairCoin, FiniteLaw.mass, FiniteLaw.eventMass]

/-! ### Root-independent separation -/

/-- A behavioral profile realizes the correlated mixed plan at one selected
continuation when their bounded optional-payoff laws are semantically
equivalent. -/
def RealizesAt
    (current :
      observed.base.toArena.HistoryFrom observed.base.init)
    (fuel : ℕ)
    (behavioral : observed.BehavioralProfile) : Prop :=
  (chanceGame.behavioralStoppedPayoffLawFrom
      behavioral current fuel).Equivalent
    (chanceGame.mixedStoppedPayoffLawFrom
      correlatedProfile current fuel)

/-- **N-2, universal separation.** No single root-independent behavioral
profile realizes both the initial-root law and the freshly resampled
post-`false` continuation law of the correlated mixed plan.

This theorem quantifies over every behavioral profile; it is not inferred from
two canonical root-scoped constructions being unequal. The continuation law
forces equal mass on its two second actions, which would make the initial
behavioral masses of `(false, false)` and `(false, true)` agree. The mixed plan
assigns those terminal outcomes masses `1/2` and `0`, respectively.

The result rules out only the erroneous continuation-wide promotion. The
positive theorem `correlatedPlan_realizedAtSelectedRoot` below still realizes
the plan exactly at each root selected separately. -/
theorem no_rootIndependent_behavioralProfile :
    ∀ behavioral : observed.BehavioralProfile,
      ¬ (RealizesAt initialRoot 2 behavioral ∧
        RealizesAt afterFalseRoot 1 behavioral) := by
  intro behavioral hrealizes
  rcases hrealizes with ⟨hinitial, hcontinuation⟩
  have hcontinuationFalse :=
    FiniteLaw.Equivalent.mass hcontinuation
      (payoffOutcome false false)
  have hcontinuationTrue :=
    FiniteLaw.Equivalent.mass hcontinuation
      (payoffOutcome false true)
  rw [behavioralLaw_afterFalse_apply,
    mixedLaw_afterFalse_apply] at hcontinuationFalse
  rw [behavioralLaw_afterFalse_apply,
    mixedLaw_afterFalse_apply] at hcontinuationTrue
  have hsecond :
      (show FiniteLaw Bool from
        behavioral () (secondInformation false)).mass false =
        (show FiniteLaw Bool from
          behavioral () (secondInformation false)).mass true :=
    hcontinuationFalse.trans hcontinuationTrue.symm
  have hinitialFalse :=
    FiniteLaw.Equivalent.mass hinitial
      (payoffOutcome false false)
  have hinitialTrue :=
    FiniteLaw.Equivalent.mass hinitial
      (payoffOutcome false true)
  rw [behavioralLaw_initial_apply_false,
    mixedLaw_initial_falseFalse] at hinitialFalse
  rw [behavioralLaw_initial_apply_false,
    mixedLaw_initial_falseTrue] at hinitialTrue
  have hhalfZero : (1 / 2 : ℚ≥0) = 0 :=
    hinitialFalse.symm.trans <|
      (congrArg
        (fun probability =>
          (show FiniteLaw Bool from
            behavioral () firstInformation).mass false * probability)
        hsecond).trans hinitialTrue
  exact (by norm_num : (1 / 2 : ℚ≥0) ≠ 0) hhalfZero

/-- **N-2.** At every explicitly selected continuation root, the existing
root-scoped behavioralization of the correlated mixed plan has exactly the
same bounded payoff law from that root.

The repeated `current` in both the construction and the law is the guarded
semantic boundary: this theorem supplies no root-independent
behavioralization. -/
theorem correlatedPlan_realizedAtSelectedRoot
    (current :
      observed.base.toArena.HistoryFrom
        observed.base.init)
    (offPath : observed.BehavioralProfile)
    (fuel : ℕ) :
    (chanceGame.mixedStoppedPayoffLawFrom
        correlatedProfile current fuel).Equivalent
      (chanceGame.behavioralStoppedPayoffLawFrom
        (hypotheses.mixedToBehavioralProfileAt
          observed current correlatedProfile offPath)
        current fuel) := by
  letI (i : Unit)
      (information : chanceGame.observed.RepresentedInfo i) :
      DecidableEq
        (chanceGame.observed.InfoAction i information.1) :=
    (hypotheses.finiteDecisionPresentation i).2 information
  exact
    chanceGame.mixedToBehavioral_stoppedPayoffLawFrom
      hypotheses.recallCertificate
      correlatedProfile offPath current fuel

/-- Root-scoped finite-Kuhn realization, including semantic deviation
coverage, at a selected continuation. -/
theorem realizationAt
    (current :
      observed.base.toArena.HistoryFrom
        observed.base.init)
    (offPath : observed.BehavioralProfile)
    (fuel : ℕ)
    (profile : observed.MixedProfile) :
    (chanceGame.behavioralStoppedPayoffLawFrom
        (hypotheses.mixedToBehavioralProfileAt
          observed current profile offPath)
        current fuel).Equivalent
      (chanceGame.mixedStoppedPayoffLawFrom
        profile current fuel) ∧
    ∀ (i : Unit) (target : observed.BehavioralStrategy i),
      ∃ source : observed.MixedStrategy i,
        (chanceGame.behavioralStoppedPayoffLawFrom
            (Function.update
              (hypotheses.mixedToBehavioralProfileAt
                observed current profile offPath)
              i target)
            current fuel).Equivalent
          (chanceGame.mixedStoppedPayoffLawFrom
            (Function.update profile i source)
            current fuel) :=
  chanceGame.finiteKuhnMixedBehavioralRealizationAt
    hypotheses current offPath fuel profile

/-- **N-2 deviation guard.** Every unilateral behavioral deviation at the
selected root has an exactly matching mixed-plan deviation law at that same
root. This exercises the coverage field needed for two-way root Nash transfer
without constructing a continuation-wide behavioralization. -/
theorem correlatedPlan_deviationCoveredAtSelectedRoot
    (current :
      observed.base.toArena.HistoryFrom
        observed.base.init)
    (offPath : observed.BehavioralProfile)
    (fuel : ℕ)
    (target : observed.BehavioralStrategy ()) :
    ∃ source : observed.MixedStrategy (),
      (chanceGame.behavioralStoppedPayoffLawFrom
          (Function.update
            (hypotheses.mixedToBehavioralProfileAt
              observed current correlatedProfile offPath)
            () target)
          current fuel).Equivalent
        (chanceGame.mixedStoppedPayoffLawFrom
          (Function.update
            correlatedProfile () source)
          current fuel) := by
  exact (realizationAt current offPath fuel correlatedProfile).2 () target

end Examples.RootScopedKuhn
