/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Realized

/-!
# Presentation.Chance.Countable — effective countable presentation boundary

This module separates two notions that the former automatic constructor mixed:

* finite and countable operational data must be supplied through executable
  decisions or encodings; and
* measurable spaces, measures, kernels, and complete analytic presentations
  are caller-supplied certified mathematical data.

A bare `Countable` proof is deliberately not converted to an `Encodable`
instance, a measurable space, or a kernel. The tagged information/action
carriers below remain useful for effective models, but clients that enumerate
them must provide actual `Encodable` data. Terminality is decided by the
state-indexed executable instance used by the finite execution layer.

`realizedAction` is partial: a tagged action whose information tag does not
match the current history returns `none`. In particular, the library no
longer invents a legal fallback action for an off-tag input. Analytic
realization and abstract-action kernels are instead projected from an explicit
`AnalyticPresentation`; their measurability, normalization, legality, and
compilation laws are owned by that supplied certificate.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedChanceGame

universe uN uU

variable {N : Type uN} {U : Type uU}

/-- Total carrier of original player-information points. -/
abbrev PlayerInformationPoint (G : ObservedChanceGame N U) :=
  Σ i : N, G.observed.InfoState i

/-- An original player-information point is reachable when a player-controlled
complete history maps to it. -/
def IsReachablePlayerInformation
    (G : ObservedChanceGame N U)
    (information : PlayerInformationPoint G) : Prop :=
  ∃ (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hmover :
      G.observed.base.mover history.1 = some information.1)
    (hdecision :
      G.observed.base.toArena.IsDecision history.1),
    G.observed.infoAt history information.1 hmover hdecision =
      information.2

/-- Proof-carrying carrier of reachable original player-information points. -/
abbrev ReachablePlayerInformation (G : ObservedChanceGame N U) :=
  {information : PlayerInformationPoint G //
    IsReachablePlayerInformation G information}

/-- The represented behavioral-strategy coordinate carried by a reachable
player-information point. -/
def ReachablePlayerInformation.representedInfo
    {G : ObservedChanceGame N U}
    (information : ReachablePlayerInformation G) :
    G.observed.RepresentedInfo information.1.1 := by
  refine ⟨information.1.2, ?_⟩
  rcases information.2 with
    ⟨history, hmover, hdecision, hinformation⟩
  exact ⟨{
    history := history
    mover := hmover
    decision := hdecision
    infoAt_eq := hinformation
  }⟩

/-- A player-controlled complete history together with its mover. -/
abbrev PlayerHistory (G : ObservedChanceGame N U) :=
  Σ history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init,
    {i : N //
      G.observed.base.mover history.1 = some i ∧
        ¬ G.observed.base.isTerminal history.1}

/-- The reachable player-information point represented at a concrete
player-controlled history. -/
def reachablePlayerInformationAt
    (G : ObservedChanceGame N U)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i)
    (hnonterminal : ¬ G.observed.base.isTerminal history.1) :
    ReachablePlayerInformation G :=
  let hdecision :=
    G.observed.base.toArena.isDecision_of_not_isTerminal
      history.1 hnonterminal
  ⟨⟨i, G.observed.infoAt history i hmover hdecision⟩,
    ⟨history, hmover, hdecision, rfl⟩⟩

/-- Disjoint information tags for effective countable presentations. -/
inductive CountableInformation (G : ObservedChanceGame N U)
  | terminal
  | player (information : ReachablePlayerInformation G)
  | chance
      (history :
        G.observed.base.toArena.HistoryFrom G.observed.base.init)
      (hchance : G.observed.base.isChanceState history.1)

namespace CountableInformation

/-- Abstract action type associated to one effective information tag. -/
def Action
    {G : ObservedChanceGame N U} :
    CountableInformation G → Type _
  | .terminal => Empty
  | .player information =>
      G.observed.InfoAction information.1.1 information.1.2
  | .chance history _hchance =>
      G.observed.base.Action history.1

end CountableInformation

/-- Common tagged abstract-action carrier. Countable clients should supply
an actual `Encodable` instance for this carrier rather than ask the library to
extract one from a `Countable` proof. -/
abbrev CountableAction (G : ObservedChanceGame N U) :=
  Σ information : CountableInformation G, information.Action

/-- Total carrier of original dependent player-information actions. -/
abbrev PlayerInformationAction (G : ObservedChanceGame N U) :=
  Σ information : PlayerInformationPoint G,
    G.observed.InfoAction information.1 information.2

/-- Total carrier of complete-history/local-action pairs. -/
abbrev CompleteHistoryAction (G : ObservedChanceGame N U) :=
  Σ history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init,
    G.observed.base.Action history.1

/-- Concrete bundles inherit measurable singletons from the explicit discrete
space of the supplied analytic history arena. This is a proof, not a selected
measurable-space structure. -/
instance instMeasurableSingletonClassAnalyticHistoryActionBundle
    (G : ObservedChanceGame N U) :
    MeasurableSingletonClass (AnalyticHistoryArena G).ActionBundle where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

/-- The optional incoming action preserves measurable singletons on path
events. No countability-to-measurable-space conversion is used. -/
instance instMeasurableSingletonClassAnalyticHistoryPathEvent
    (G : ObservedChanceGame N U) :
    MeasurableSingletonClass (AnalyticHistoryArena G).PathEvent where
  measurableSet_singleton event := by
    have hoptional :
        MeasurableSet
          ({event.2} :
            Set (Unit ⊕ (AnalyticHistoryArena G).ActionBundle)) := by
      cases event.2 with
      | inl value =>
          have heq :
              ({Sum.inl value} :
                  Set (Unit ⊕ (AnalyticHistoryArena G).ActionBundle)) =
                Sum.inl '' ({value} : Set Unit) := by
            ext value
            simp
          rw [heq]
          exact MeasurableSet.inl_image (measurableSet_singleton value)
      | inr actionBundle =>
          have heq :
              ({Sum.inr actionBundle} :
                  Set (Unit ⊕ (AnalyticHistoryArena G).ActionBundle)) =
                Sum.inr ''
                  ({actionBundle} :
                    Set (AnalyticHistoryArena G).ActionBundle) := by
            ext value
            simp
          rw [heq]
          exact MeasurableSet.inr_image (measurableSet_singleton actionBundle)
    have hevent :
        ({event.1} : Set (AnalyticHistoryArena G).State) ×ˢ
            ({event.2} :
              Set (Unit ⊕ (AnalyticHistoryArena G).ActionBundle)) =
          ({event} : Set (AnalyticHistoryArena G).PathEvent) :=
      Set.singleton_prod_singleton
    rw [← hevent]
    exact (measurableSet_singleton event.1).prod hoptional

namespace CountablePresentation

variable (G : ObservedChanceGame N U)

/-- Executably classify one complete history as terminal, player-controlled,
or chance-controlled. The state-indexed terminal decision is runtime data. -/
def informationAtHistory
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    CountableInformation G :=
  if hterminal : G.observed.base.isTerminal history.1 then
    .terminal
  else
    match hmover : G.observed.base.mover history.1 with
    | some i =>
        .player
          (reachablePlayerInformationAt G history i hmover hterminal)
    | none =>
        .chance history ⟨hmover, hterminal⟩

@[simp]
theorem informationAtHistory_of_terminal
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hterminal : G.observed.base.isTerminal history.1) :
    informationAtHistory G history = .terminal := by
  simp [informationAtHistory, hterminal]

@[simp]
theorem informationAtHistory_of_terminal_of_no_mover
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hterminal : G.observed.base.isTerminal history.1)
    (_hmover : G.observed.base.mover history.1 = none) :
    informationAtHistory G history = .terminal :=
  informationAtHistory_of_terminal G history hterminal

@[simp]
theorem informationAtHistory_of_mover
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i)
    (hnonterminal : ¬ G.observed.base.isTerminal history.1) :
    informationAtHistory G history =
      .player
        (reachablePlayerInformationAt G history i hmover
          hnonterminal) := by
  unfold informationAtHistory
  rw [dif_neg hnonterminal]
  split
  · rename_i j hj
    have hji : j = i :=
      Option.some.inj (hj.symm.trans hmover)
    subst j
    have hmoverProof : hj = hmover := Subsingleton.elim _ _
    cases hmoverProof
    rfl
  · rename_i hnone
    rw [hmover] at hnone
    contradiction

@[simp]
theorem informationAtHistory_of_chance
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal : ¬ G.observed.base.isTerminal history.1)
    (hmover : G.observed.base.mover history.1 = none) :
    informationAtHistory G history =
      .chance history ⟨hmover, hnonterminal⟩ := by
  unfold informationAtHistory
  rw [dif_neg hnonterminal]
  split
  · rename_i i hi
    rw [hmover] at hi
    contradiction
  · rename_i hnone
    have hmoverProof : hnone = hmover := Subsingleton.elim _ _
    cases hmoverProof
    rfl

/-- Canonical injection of an original player action into the tagged carrier. -/
def playerAction
    (information : ReachablePlayerInformation G)
    (action :
      G.observed.InfoAction information.1.1 information.1.2) :
    CountableAction G :=
  ⟨.player information, action⟩

/-- Canonical injection of a local chance action into the tagged carrier. -/
def chanceAction
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hchance : G.observed.base.isChanceState history.1)
    (action : G.observed.base.Action history.1) :
    CountableAction G :=
  ⟨.chance history hchance, action⟩

/-- Executably realize a tagged action at a nonterminal prefix.

A matching player/chance tag returns the legal local bundle. A mismatched tag
returns `none`; no fallback action is selected. -/
def realizedAction
    [DecidableEq (CountableInformation G)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        history.1)
    (taggedAction : CountableAction G) :
    Option (CompleteHistoryAction G) :=
  let hdecision :=
    G.observed.base.toArena.isDecision_of_not_isTerminal
      history.1 hnonterminal
  match hmover : G.observed.base.mover history.1 with
  | some i =>
      if htag :
          taggedAction.1 =
            CountableInformation.player
              (reachablePlayerInformationAt G history i hmover
                hnonterminal) then
        some
          ⟨history,
            G.observed.actionEquiv history i hmover hdecision
              (cast
                (congrArg CountableInformation.Action htag)
                taggedAction.2)⟩
      else
        none
  | none =>
      if htag :
          taggedAction.1 =
            CountableInformation.chance history
              ⟨hmover, hnonterminal⟩ then
        some
          ⟨history,
            cast
              (congrArg CountableInformation.Action htag)
              taggedAction.2⟩
      else
        none

/-- Successful partial realization retains the complete current history. -/
theorem realizedAction_fst
    [DecidableEq (CountableInformation G)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        history.1)
    (taggedAction : CountableAction G)
    (bundle : CompleteHistoryAction G)
    (hsuccess :
      realizedAction G history hnonterminal taggedAction = some bundle) :
    bundle.1 = history := by
  unfold realizedAction at hsuccess
  dsimp at hsuccess
  split at hsuccess <;> split at hsuccess <;> cases hsuccess <;> rfl

/-- A matching player tag is realized by the original history-local action
equivalence, with explicit successful `Option` output. -/
theorem realizedAction_player
    [DecidableEq (CountableInformation G)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        history.1)
    (i : N)
    (hmover :
      G.observed.base.mover
          history.1 =
        some i)
    (action :
      G.observed.InfoAction i
        (G.observed.infoAt
          history
          i hmover
            (G.observed.base.toArena.isDecision_of_not_isTerminal _
              hnonterminal))) :
    realizedAction G history hnonterminal
        (playerAction G
          (reachablePlayerInformationAt G
            history
            i hmover hnonterminal)
          action) =
      some
        ⟨history,
          G.observed.actionEquiv
            history
            i hmover
              (G.observed.base.toArena.isDecision_of_not_isTerminal _
                hnonterminal)
            action⟩ := by
  unfold realizedAction
  dsimp
  split
  · rename_i j hj
    have hji : j = i :=
      Option.some.inj (hj.symm.trans hmover)
    subst j
    have hproof : hj = hmover := Subsingleton.elim _ _
    cases hproof
    unfold playerAction
    dsimp only
    split
    · rename_i htag
      have htagProof : htag = rfl := Subsingleton.elim _ _
      cases htagProof
      rfl
    · rename_i htag
      exact (htag rfl).elim
  · rename_i hnone
    rw [hmover] at hnone
    contradiction

/-- A matching chance tag is realized by the identical local chance action. -/
theorem realizedAction_chance
    [DecidableEq (CountableInformation G)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        history.1)
    (hmover :
      G.observed.base.mover
          history.1 =
        none)
    (action :
      G.observed.base.Action
        history.1) :
    realizedAction G history hnonterminal
        (chanceAction G
          history
          ⟨hmover, hnonterminal⟩ action) =
      some
        ⟨history,
          action⟩ := by
  unfold realizedAction
  dsimp
  split
  · rename_i i hi
    rw [hmover] at hi
    contradiction
  · rename_i hnone
    have hproof : hnone = hmover := Subsingleton.elim _ _
    cases hproof
    unfold chanceAction
    dsimp only
    split
    · rename_i htag
      have htagProof : htag = rfl := Subsingleton.elim _ _
      cases htagProof
      rfl
    · rename_i htag
      exact (htag rfl).elim

/-- Reachable original player information maps to its player tag; unreachable
information returns `none`. The reachability decision is explicit executable
input and is not synthesized from classical logic. -/
def informationOfPlayerInformation
    (reachable :
      (information : PlayerInformationPoint G) →
        Decidable (IsReachablePlayerInformation G information))
    (information : PlayerInformationPoint G) :
    Option (CountableInformation G) :=
  letI := reachable information
  dite (IsReachablePlayerInformation G information)
    (fun hreachable => some (.player ⟨information, hreachable⟩))
    (fun _ => none)

/-- At a represented player history, partial lookup succeeds with precisely
the canonical reachable tag. -/
@[simp]
theorem informationOfPlayerInformation_at
    (reachable :
      (information : PlayerInformationPoint G) →
        Decidable (IsReachablePlayerInformation G information))
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i)
    (hnonterminal : ¬ G.observed.base.isTerminal history.1) :
    informationOfPlayerInformation G reachable
        ⟨i, G.observed.infoAt history i hmover
          (G.observed.base.toArena.isDecision_of_not_isTerminal _
            hnonterminal)⟩ =
      some (.player
        (reachablePlayerInformationAt G history i hmover
          hnonterminal)) := by
  unfold informationOfPlayerInformation
  split
  · congr 2
  · rename_i hunreachable
    exact
      (hunreachable
        ⟨history, hmover,
          G.observed.base.toArena.isDecision_of_not_isTerminal _
            hnonterminal,
          rfl⟩).elim

end CountablePresentation

end ExtensiveGame.ObservedChanceGame
