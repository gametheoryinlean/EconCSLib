/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.DependentFiber
import EconCSLib.GameTheory.ExtensiveGame.Observed.Game
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Structural

Information-refinement data, dependent action maps, identity, and composition.
-/

namespace ExtensiveGame.ObservedGame

universe uV

variable {N U : Type*}

/-- Evaluating a dependent function after changing its index agrees with
transporting the value at the original index. -/
theorem dependent_apply_eq_cast
    {α : Type*} {fiber : α → Type*}
    (function : (index : α) → fiber index)
    {source target : α}
    (hindex : source = target) :
    function target =
      cast (congrArg fiber hindex) (function source) := by
  subst target
  rfl

/-- An information refinement from a coarse observed EFG `G` to a finer
observed EFG `H`.

The history dynamics are still related by a strict Arena isomorphism. Private
observations, public observations, and decision information instead have
forgetful maps from fine to coarse. Coarse abstract actions can be realized at
every fine information state above the corresponding coarse state. -/
structure InformationRefinement
    (G H : ObservedGame N U) where
  /-- Strict isomorphism of the complete-history dynamics. -/
  historyIso : G.base.unfold.toArena.Iso H.base.unfold.toArena
  /-- The empty histories correspond. -/
  map_init :
    historyIso.stateEquiv
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      Arena.HistoryFrom.nil H.base.toArena H.base.init
  /-- Strategic movers agree at corresponding histories. -/
  map_mover :
    ∀ history : G.base.toArena.HistoryFrom G.base.init,
      H.base.mover (historyIso.stateEquiv history).1 =
        G.base.mover history.1
  /-- Terminal payoff vectors agree at corresponding histories. -/
  map_payoff :
    ∀ history : G.base.toArena.HistoryFrom G.base.init,
      G.base.isTerminal history.1 →
      H.base.payoff (historyIso.stateEquiv history).1 =
        G.base.payoff history.1
  /-- Forget a fine private observation to its coarse observation. -/
  forgetObservation :
    (i : N) → H.Observation i → G.Observation i
  /-- Observation forgetting commutes with corresponding histories. -/
  forget_observe :
    ∀ (i : N)
      (history : G.base.toArena.HistoryFrom G.base.init),
      forgetObservation i
          (H.observe i (historyIso.stateEquiv history)) =
        G.observe i history
  /-- Forget a fine public observation to its coarse public observation. -/
  forgetPublic :
    H.PublicObservation → G.PublicObservation
  /-- Public-observation forgetting commutes with corresponding histories. -/
  forget_publicObserve :
    ∀ history : G.base.toArena.HistoryFrom G.base.init,
      forgetPublic
          (H.publicObserve (historyIso.stateEquiv history)) =
        G.publicObserve history
  /-- Fine private-to-public projection commutes with forgetting. -/
  forget_publicOf :
    ∀ (i : N) (observation : H.Observation i),
      forgetPublic (H.publicOf i observation) =
        G.publicOf i (forgetObservation i observation)
  /-- Forget a fine decision information state to a coarse one. -/
  forgetInfo :
    (i : N) → H.InfoState i → G.InfoState i
  /-- The represented private observation commutes with information
  forgetting. -/
  forget_infoObserve :
    ∀ (i : N) (information : H.InfoState i),
      forgetObservation i (H.infoObserve i information) =
        G.infoObserve i (forgetInfo i information)
  /-- Coarse actions are equivalent to fine actions at every fine information
  state lying over the corresponding coarse state. -/
  infoActionEquiv :
    ∀ (i : N) (information : H.InfoState i),
      G.InfoAction i (forgetInfo i information) ≃
        H.InfoAction i information
  /-- Information forgetting at a corresponding player history returns the
  source information state. -/
  map_infoAt :
    ∀ (history : G.base.toArena.HistoryFrom G.base.init) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (hsource_nonterminal : G.base.toArena.IsDecision history.1)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i)
      (htarget_nonterminal :
        H.base.toArena.IsDecision (historyIso.stateEquiv history).1),
      G.infoAt history i hsource hsource_nonterminal =
        forgetInfo i
          (H.infoAt (historyIso.stateEquiv history) i htarget
            htarget_nonterminal)
  /-- Lifting and realizing every coarse abstract action agrees with the
  strict map of the concrete source action. -/
  map_infoActionAt :
    ∀ (history : G.base.toArena.HistoryFrom G.base.init) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (hsource_nonterminal : G.base.toArena.IsDecision history.1)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i)
      (htarget_nonterminal :
        H.base.toArena.IsDecision (historyIso.stateEquiv history).1)
      (action :
        G.InfoAction i
          (G.infoAt history i hsource hsource_nonterminal)),
      H.actionEquiv (historyIso.stateEquiv history) i htarget
          htarget_nonterminal
          (infoActionEquiv i
            (H.infoAt
              (historyIso.stateEquiv history) i htarget
              htarget_nonterminal)
            (cast
              (congrArg (G.InfoAction i)
                (map_infoAt history i hsource
                  hsource_nonterminal htarget
                  htarget_nonterminal))
              action)) =
        historyIso.actionEquiv history
          (G.actionEquiv history i hsource
            hsource_nonterminal action)
namespace InformationRefinement

variable {G H : ObservedGame N U}

/-- Forget only payoff compatibility from a legacy information refinement.

The resulting certificate lives entirely on the payoff-free projections and
retains the strict history, observation, information, action, and root
comparison data. -/
def toControlled
    (r : G.InformationRefinement H) :
    G.toControlledObservedGame.InformationRefinement
      H.toControlledObservedGame where
  historyIso := r.historyIso
  map_init := r.map_init
  map_mover := r.map_mover
  forgetObservation := r.forgetObservation
  forget_observe := r.forget_observe
  forgetPublic := r.forgetPublic
  forget_publicObserve := r.forget_publicObserve
  forget_publicOf := r.forget_publicOf
  forgetInfo := r.forgetInfo
  forget_infoObserve := r.forget_infoObserve
  infoActionEquiv := r.infoActionEquiv
  map_infoAt := r.map_infoAt
  map_infoActionAt := r.map_infoActionAt

/-- Directional compatibility of separately supplied continuation-root
presentations with an information refinement.

The property is external because root selection is analysis metadata, not
part of the refinement's dynamics/information comparison. -/
def MapsRootPresentations
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation) : Prop :=
  ∀ history : G.base.toArena.HistoryFrom G.base.init,
    sourceRoots.IsRoot history →
      targetRoots.IsRoot (r.historyIso.stateEquiv history)

/-- Exact correspondence of two external root presentations along an
information refinement.

This stronger certificate is needed only for results that cover every target
root as well as every source root. One-way Nash reflection uses
`MapsRootPresentations`; two-way transfer additionally needs this iff. -/
def PreservesRootPresentations
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation) : Prop :=
  ∀ history : G.base.toArena.HistoryFrom G.base.init,
    sourceRoots.IsRoot history ↔
      targetRoots.IsRoot (r.historyIso.stateEquiv history)

/-- Information refinements are determined by their structural maps and
dependent action equivalences; all coherence fields are propositions. -/
@[ext]
theorem ext (r s : G.InformationRefinement H)
    (hhistory : r.historyIso = s.historyIso)
    (hobservation : r.forgetObservation = s.forgetObservation)
    (hpublic : r.forgetPublic = s.forgetPublic)
    (hinfo : r.forgetInfo = s.forgetInfo)
    (haction : HEq r.infoActionEquiv s.infoActionEquiv) :
    r = s := by
  cases r
  cases s
  cases hhistory
  cases hobservation
  cases hpublic
  cases hinfo
  cases haction
  rfl

/-- The coarse-to-fine information-action equivalence at corresponding
player histories, with the forgetful index transport encapsulated. -/
def infoActionEquivAt
    (r : G.InformationRefinement H)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover
          (r.historyIso.stateEquiv history).1 =
        some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (r.historyIso.stateEquiv history).1) :
    G.InfoAction i
        (G.infoAt history i hsource hsource_nonterminal) ≃
      H.InfoAction i
        (H.infoAt
          (r.historyIso.stateEquiv history)
          i htarget htarget_nonterminal) :=
  Equiv.fiberEquivOverAt
    (r.forgetInfo i)
    (r.infoActionEquiv i)
    (G.infoAt history i hsource hsource_nonterminal)
    (H.infoAt
      (r.historyIso.stateEquiv history) i htarget
      htarget_nonterminal)
    (r.map_infoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal)

@[simp]
theorem infoActionEquivAt_apply
    (r : G.InformationRefinement H)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover
          (r.historyIso.stateEquiv history).1 =
        some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (r.historyIso.stateEquiv history).1)
    (action :
      G.InfoAction i
        (G.infoAt history i hsource hsource_nonterminal)) :
    r.infoActionEquivAt history i hsource hsource_nonterminal
        htarget htarget_nonterminal action =
      r.infoActionEquiv i
        (H.infoAt
          (r.historyIso.stateEquiv history) i htarget
          htarget_nonterminal)
        (cast
          (congrArg (G.InfoAction i)
            (r.map_infoAt history i hsource hsource_nonterminal
              htarget htarget_nonterminal))
          action) :=
  rfl

/-- Realization of the cast-stable refinement action equivalence commutes with
the strict history-action equivalence. -/
theorem map_infoActionEquivAt
    (r : G.InformationRefinement H)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover
          (r.historyIso.stateEquiv history).1 =
        some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (r.historyIso.stateEquiv history).1)
    (action :
      G.InfoAction i
        (G.infoAt history i hsource hsource_nonterminal)) :
    H.actionEquiv (r.historyIso.stateEquiv history) i htarget
        htarget_nonterminal
        (r.infoActionEquivAt history i hsource hsource_nonterminal
          htarget htarget_nonterminal action) =
      r.historyIso.actionEquiv history
        (G.actionEquiv history i hsource hsource_nonterminal action) :=
  r.map_infoActionAt history i hsource hsource_nonterminal
    htarget htarget_nonterminal action

/-- Identity information refinement. -/
def refl (G : ObservedGame N U) :
    G.InformationRefinement G where
  historyIso :=
    Arena.Iso.refl G.base.unfold.toArena
  map_init := rfl
  map_mover := by
    intro history
    rfl
  map_payoff := by
    intro history _
    rfl
  forgetObservation := fun _ observation => observation
  forget_observe := by
    intro i history
    rfl
  forgetPublic := id
  forget_publicObserve := by
    intro history
    rfl
  forget_publicOf := by
    intro i observation
    rfl
  forgetInfo := fun _ information => information
  forget_infoObserve := by
    intro i information
    rfl
  infoActionEquiv := fun _ _ => Equiv.refl _
  map_infoAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal
    congr
  map_infoActionAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal action
    rfl

/-- Identity refinements leave local information actions unchanged. -/
@[simp]
theorem refl_infoActionEquivAt
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource htarget : G.base.mover history.1 = some i)
    (hsource_nonterminal htarget_nonterminal :
      G.base.toArena.IsDecision history.1)
    (action :
      G.InfoAction i
        (G.infoAt history i hsource hsource_nonterminal)) :
    (refl G).infoActionEquivAt
        history i hsource hsource_nonterminal
        htarget htarget_nonterminal action =
      action := by
  rfl

/-- The decision-information equality used by composition of information
refinements. -/
def transInfoAt {K : ObservedGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (hmiddle :
      H.base.mover
          (r.historyIso.stateEquiv history).1 =
        some i)
    (hmiddle_nonterminal :
      H.base.toArena.IsDecision
        (r.historyIso.stateEquiv history).1)
    (htarget :
      K.base.mover
          (s.historyIso.stateEquiv
            (r.historyIso.stateEquiv history)).1 =
        some i)
    (htarget_nonterminal :
      K.base.toArena.IsDecision
        (s.historyIso.stateEquiv
          (r.historyIso.stateEquiv history)).1) :
    G.infoAt history i hsource hsource_nonterminal =
      r.forgetInfo i
        (s.forgetInfo i
          (K.infoAt
            (s.historyIso.stateEquiv
              (r.historyIso.stateEquiv history))
            i htarget htarget_nonterminal)) :=
  (r.map_infoAt history i hsource hsource_nonterminal
    hmiddle hmiddle_nonterminal).trans
    (congrArg (r.forgetInfo i)
      (s.map_infoAt
        (r.historyIso.stateEquiv history)
        i hmiddle hmiddle_nonterminal htarget
        htarget_nonterminal))

/-- Compose information refinements.

The resulting map forgets information twice and lifts coarse actions through
both indexed action equivalences. -/
def trans {K : ObservedGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K) :
    G.InformationRefinement K where
  historyIso := r.historyIso.trans s.historyIso
  map_init := by
    calc
      s.historyIso.stateEquiv
          (r.historyIso.stateEquiv
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)) =
        s.historyIso.stateEquiv
          (Arena.HistoryFrom.nil
            H.base.toArena H.base.init) :=
              congrArg s.historyIso.stateEquiv
                r.map_init
      _ = Arena.HistoryFrom.nil
          K.base.toArena K.base.init :=
            s.map_init
  map_mover := by
    intro history
    change
      K.base.mover
          (s.historyIso.stateEquiv
            (r.historyIso.stateEquiv history)).1 =
        G.base.mover history.1
    rw [s.map_mover, r.map_mover]
  map_payoff := by
    intro history hterminal
    have hmiddleTerminal :
        H.base.isTerminal
          (r.historyIso.stateEquiv history).1 :=
      (r.historyIso.isTerminal_iff history).mp hterminal
    change
      K.base.payoff
          (s.historyIso.stateEquiv
            (r.historyIso.stateEquiv history)).1 =
        G.base.payoff history.1
    rw [s.map_payoff _ hmiddleTerminal,
      r.map_payoff history hterminal]
  forgetObservation := fun i observation =>
    r.forgetObservation i
      (s.forgetObservation i observation)
  forget_observe := by
    intro i history
    change
      r.forgetObservation i
          (s.forgetObservation i
            (K.observe i
              (s.historyIso.stateEquiv
                (r.historyIso.stateEquiv history)))) =
        G.observe i history
    rw [s.forget_observe, r.forget_observe]
  forgetPublic := fun observation =>
    r.forgetPublic (s.forgetPublic observation)
  forget_publicObserve := by
    intro history
    change
      r.forgetPublic
          (s.forgetPublic
            (K.publicObserve
              (s.historyIso.stateEquiv
                (r.historyIso.stateEquiv history)))) =
        G.publicObserve history
    rw [s.forget_publicObserve,
      r.forget_publicObserve]
  forget_publicOf := by
    intro i observation
    change
      r.forgetPublic
          (s.forgetPublic
            (K.publicOf i observation)) =
        G.publicOf i
          (r.forgetObservation i
            (s.forgetObservation i observation))
    rw [s.forget_publicOf, r.forget_publicOf]
  forgetInfo := fun i information =>
    r.forgetInfo i (s.forgetInfo i information)
  forget_infoObserve := by
    intro i information
    change
      r.forgetObservation i
          (s.forgetObservation i
            (K.infoObserve i information)) =
        G.infoObserve i
          (r.forgetInfo i
            (s.forgetInfo i information))
    rw [s.forget_infoObserve,
      r.forget_infoObserve]
  infoActionEquiv := fun i information =>
    (r.infoActionEquiv i
      (s.forgetInfo i information)).trans
        (s.infoActionEquiv i information)
  map_infoAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal
    let hmiddle :
        H.base.mover
            (r.historyIso.stateEquiv history).1 =
          some i := by
      rw [r.map_mover history]
      exact hsource
    let hmiddle_nonterminal :
        H.base.toArena.IsDecision
          (r.historyIso.stateEquiv history).1 :=
      (r.historyIso.isDecision_iff history).mp
        hsource_nonterminal
    exact
      r.transInfoAt s history i
        hsource hsource_nonterminal
        hmiddle hmiddle_nonterminal
        htarget htarget_nonterminal
  map_infoActionAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal action
    let middleHistory :=
      r.historyIso.stateEquiv history
    let hmiddle :
        H.base.mover middleHistory.1 = some i := by
      rw [r.map_mover history]
      exact hsource
    let hmiddle_nonterminal :
        H.base.toArena.IsDecision middleHistory.1 :=
      (r.historyIso.isDecision_iff history).mp
        hsource_nonterminal
    let sourceInformation :=
      G.infoAt history i hsource hsource_nonterminal
    let middleInformation :=
      H.infoAt middleHistory i hmiddle hmiddle_nonterminal
    let targetInformation :=
      K.infoAt
        (s.historyIso.stateEquiv middleHistory)
        i htarget htarget_nonterminal
    have hFirst :
      sourceInformation =
          r.forgetInfo i middleInformation :=
      r.map_infoAt history i hsource hsource_nonterminal
        hmiddle hmiddle_nonterminal
    have hSecond :
      middleInformation =
          s.forgetInfo i targetInformation :=
      s.map_infoAt middleHistory i hmiddle hmiddle_nonterminal
        htarget htarget_nonterminal
    let middleAction :=
      r.infoActionEquiv i middleInformation
        (cast
          (congrArg (G.InfoAction i) hFirst)
          action)
    let targetAction :=
      s.infoActionEquiv i targetInformation
        (cast
          (congrArg (H.InfoAction i) hSecond)
          middleAction)
    have hcast :
        s.infoActionEquiv i targetInformation
            (r.infoActionEquiv i
              (s.forgetInfo i targetInformation)
              (cast
                (congrArg (G.InfoAction i)
                  (r.transInfoAt s history i
                    hsource hsource_nonterminal
                    hmiddle hmiddle_nonterminal
                    htarget htarget_nonterminal))
                action)) =
          targetAction := by
      exact
        Equiv.fiberEquivOverAt_trans_apply
          (W := G.InfoAction i)
          (Z := H.InfoAction i)
          (V := K.InfoAction i)
          (r.forgetInfo i)
          (s.forgetInfo i)
          (r.infoActionEquiv i)
          (s.infoActionEquiv i)
          sourceInformation middleInformation
          targetInformation
          hFirst hSecond action
    change
      K.actionEquiv
          (s.historyIso.stateEquiv middleHistory)
          i htarget htarget_nonterminal
          (s.infoActionEquiv i targetInformation
            (r.infoActionEquiv i
              (s.forgetInfo i targetInformation)
              (cast
                (congrArg (G.InfoAction i)
                  (r.transInfoAt s history i
                    hsource hsource_nonterminal
                    hmiddle hmiddle_nonterminal
                    htarget htarget_nonterminal))
                action))) =
        s.historyIso.actionEquiv middleHistory
          (r.historyIso.actionEquiv history
            (G.actionEquiv
              history i hsource hsource_nonterminal action))
    rw [hcast]
    calc
      K.actionEquiv
          (s.historyIso.stateEquiv middleHistory)
          i htarget htarget_nonterminal targetAction =
        s.historyIso.actionEquiv middleHistory
          (H.actionEquiv middleHistory i hmiddle
            hmiddle_nonterminal middleAction) := by
              exact
                s.map_infoActionAt middleHistory i
                  hmiddle hmiddle_nonterminal
                  htarget htarget_nonterminal middleAction
      _ = s.historyIso.actionEquiv middleHistory
          (r.historyIso.actionEquiv history
            (G.actionEquiv
              history i hsource hsource_nonterminal action)) := by
              exact
                congrArg
                  (s.historyIso.actionEquiv
                    middleHistory)
                  (r.map_infoActionAt
                    history i hsource hsource_nonterminal
                    hmiddle hmiddle_nonterminal action)

/-- The cast-stable refinement action equivalence is functorial under
composition. -/
theorem trans_infoActionEquivAt {K : ObservedGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (hmiddle :
      H.base.mover
          (r.historyIso.stateEquiv history).1 =
        some i)
    (hmiddle_nonterminal :
      H.base.toArena.IsDecision
        (r.historyIso.stateEquiv history).1)
    (htarget :
      K.base.mover
          (s.historyIso.stateEquiv
            (r.historyIso.stateEquiv history)).1 =
        some i)
    (htarget_nonterminal :
      K.base.toArena.IsDecision
        (s.historyIso.stateEquiv
          (r.historyIso.stateEquiv history)).1)
    (action :
      G.InfoAction i
        (G.infoAt history i hsource hsource_nonterminal)) :
    (r.trans s).infoActionEquivAt
        history i hsource hsource_nonterminal
        htarget htarget_nonterminal action =
      s.infoActionEquivAt
        (r.historyIso.stateEquiv history)
        i hmiddle hmiddle_nonterminal
        htarget htarget_nonterminal
        (r.infoActionEquivAt
          history i hsource hsource_nonterminal
          hmiddle hmiddle_nonterminal action) := by
  simpa [infoActionEquivAt, trans, transInfoAt] using
    Equiv.fiberEquivOverAt_trans_apply
      (r.forgetInfo i)
      (s.forgetInfo i)
      (r.infoActionEquiv i)
      (s.infoActionEquiv i)
      (G.infoAt history i hsource hsource_nonterminal)
      (H.infoAt
        (r.historyIso.stateEquiv history) i hmiddle
        hmiddle_nonterminal)
      (K.infoAt
        (s.historyIso.stateEquiv
          (r.historyIso.stateEquiv history))
        i htarget htarget_nonterminal)
      (r.map_infoAt history i hsource hsource_nonterminal
        hmiddle hmiddle_nonterminal)
      (s.map_infoAt
        (r.historyIso.stateEquiv history)
        i hmiddle hmiddle_nonterminal
        htarget htarget_nonterminal)
      action

/-- Identity is a left unit for information-refinement composition. -/
@[simp]
theorem refl_trans (r : G.InformationRefinement H) :
    (refl G).trans r = r := by
  apply InformationRefinement.ext
  · exact Arena.Iso.refl_trans r.historyIso
  · funext i observation
    rfl
  · funext observation
    rfl
  · funext i information
    rfl
  · apply heq_of_eq
    funext i information
    apply Equiv.ext
    intro action
    rfl

/-- Identity is a right unit for information-refinement composition. -/
@[simp]
theorem trans_refl (r : G.InformationRefinement H) :
    r.trans (refl H) = r := by
  apply InformationRefinement.ext
  · exact Arena.Iso.trans_refl r.historyIso
  · funext i observation
    rfl
  · funext observation
    rfl
  · funext i information
    rfl
  · apply heq_of_eq
    funext i information
    apply Equiv.ext
    intro action
    rfl

/-- Composition of information refinements is associative. -/
theorem trans_assoc {K L : ObservedGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K)
    (t : K.InformationRefinement L) :
    (r.trans s).trans t = r.trans (s.trans t) := by
  apply InformationRefinement.ext
  · exact Arena.Iso.trans_assoc
      r.historyIso s.historyIso t.historyIso
  · funext i observation
    rfl
  · funext observation
    rfl
  · funext i information
    rfl
  · apply heq_of_eq
    funext i information
    apply Equiv.ext
    intro action
    rfl


end InformationRefinement

end ExtensiveGame.ObservedGame
