/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Structural

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Inverse

Inverse strict observed-EFG isomorphisms and dependent cast laws.
-/

namespace ExtensiveGame.ObservedGame

universe uV

variable {N U : Type*}

namespace Iso

variable {G H : ObservedGame N U}

/-- The inverse dependent information-action equivalence at a target
information state. -/
def inverseInfoActionEquiv (e : G.Iso H) (i : N)
    (targetInformation : H.InfoState i) :
    H.InfoAction i targetInformation ≃
      G.InfoAction i ((e.infoStateEquiv i).symm targetInformation) :=
  (Equiv.cast
      (congrArg (H.InfoAction i)
        ((e.infoStateEquiv i).apply_symm_apply targetInformation))).symm.trans
    (e.infoActionEquiv i
      ((e.infoStateEquiv i).symm targetInformation)).symm

/-- Reverse the decision-information square at the image of a source
history. -/
theorem inverseInfoAt (e : G.Iso H)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv history).1) :
    (e.infoStateEquiv i).symm
        (H.infoAt
          (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal) =
      G.infoAt history i hsource hsource_nonterminal := by
  apply (e.infoStateEquiv i).injective
  simpa using
    (e.map_infoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal).symm

private theorem cast_inverseFiber
    {α β : Type*} {W : α → Type*} {Z : β → Type*}
    (base : α ≃ β)
    (fiber : ∀ source, W source ≃ Z (base source))
    (source sourceBack : α) (target : β)
    (hforward : base source = target)
    (hright : base sourceBack = target)
    (hleft : sourceBack = source)
    (value : Z target) :
    cast (congrArg W hleft)
        ((fiber sourceBack).symm
          (cast (congrArg Z hright).symm value)) =
      (fiber source).symm
        (cast (congrArg Z hforward).symm value) := by
  subst sourceBack
  rfl

private theorem cast_inverseInfoActionEquiv
    (e : G.Iso H) (i : N)
    (sourceInformation : G.InfoState i)
    (targetInformation : H.InfoState i)
    (hforward :
      e.infoStateEquiv i sourceInformation =
        targetInformation)
    (hback :
      (e.infoStateEquiv i).symm targetInformation =
        sourceInformation)
    (action : H.InfoAction i targetInformation) :
    cast
        (congrArg (G.InfoAction i) hback)
        (e.inverseInfoActionEquiv i targetInformation action) =
      (e.infoActionEquiv i sourceInformation).symm
        (cast
          (congrArg (H.InfoAction i) hforward).symm
          action) := by
  exact
    cast_inverseFiber
      (e.infoStateEquiv i) (e.infoActionEquiv i)
      sourceInformation
      ((e.infoStateEquiv i).symm targetInformation)
      targetInformation hforward
      ((e.infoStateEquiv i).apply_symm_apply targetInformation)
      hback action

private theorem cast_inverseHistoryActionEquiv
    {A B : Arena} (e : A.Iso B)
    (source : A.State) (target : B.State)
    (hforward : e.stateEquiv source = target)
    (hback : e.stateEquiv.symm target = source)
    (action : B.Action target) :
    cast (congrArg A.Action hback)
        (e.inverseActionEquiv target action) =
      (e.actionEquiv source).symm
        (cast (congrArg B.Action hforward).symm action) := by
  exact
    cast_inverseFiber e.stateEquiv e.actionEquiv
      source (e.stateEquiv.symm target) target
      hforward (e.stateEquiv.apply_symm_apply target)
      hback action

private theorem actionEquiv_heq_of_history_eq
    (G : ObservedGame N U) (i : N)
    {first second :
      G.base.toArena.HistoryFrom G.base.init}
    (hhistory : first = second)
    (hfirst : G.base.mover first.1 = some i)
    (hfirst_nonterminal : G.base.toArena.IsDecision first.1)
    (hsecond : G.base.mover second.1 = some i)
    (hsecond_nonterminal : G.base.toArena.IsDecision second.1)
    (firstAction :
      G.InfoAction i
        (G.infoAt first i hfirst hfirst_nonterminal))
    (secondAction :
      G.InfoAction i
        (G.infoAt second i hsecond hsecond_nonterminal))
    (haction : firstAction ≍ secondAction) :
    G.actionEquiv first i hfirst hfirst_nonterminal
        firstAction ≍
      G.actionEquiv second i hsecond hsecond_nonterminal
        secondAction := by
  subst second
  have hmover : hsecond = hfirst :=
    Subsingleton.elim _ _
  cases hmover
  have hnonterminal : hsecond_nonterminal = hfirst_nonterminal :=
    Subsingleton.elim _ _
  cases hnonterminal
  cases haction
  rfl

private theorem inverse_infoActionAt
    (e : G.Iso H)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv history).1)
    (action :
      H.InfoAction i
        (H.infoAt
          (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal)) :
    G.actionEquiv history i hsource hsource_nonterminal
        (cast
          (congrArg (G.InfoAction i)
            (e.inverseInfoAt history i hsource
              hsource_nonterminal htarget htarget_nonterminal))
          (e.inverseInfoActionEquiv i
            (H.infoAt
              (e.historyIso.stateEquiv history) i htarget
              htarget_nonterminal)
            action)) =
      cast
        (congrArg G.base.unfold.Action
          (e.historyIso.stateEquiv.symm_apply_apply history))
        (e.historyIso.inverseActionEquiv
            (e.historyIso.stateEquiv history)
          (H.actionEquiv
            (e.historyIso.stateEquiv history) i htarget
            htarget_nonterminal action)) := by
  have hinfo :
      e.infoStateEquiv i
          (G.infoAt history i hsource hsource_nonterminal) =
        H.infoAt
          (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal :=
    e.map_infoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal
  rw [cast_inverseInfoActionEquiv e i
    (G.infoAt history i hsource hsource_nonterminal)
    (H.infoAt
      (e.historyIso.stateEquiv history) i htarget
      htarget_nonterminal)
    hinfo
    (e.inverseInfoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal)]
  rw [cast_inverseHistoryActionEquiv e.historyIso
    history (e.historyIso.stateEquiv history)
    rfl (e.historyIso.stateEquiv.symm_apply_apply history)]
  apply (e.historyIso.actionEquiv history).injective
  simpa using
      (e.map_infoActionAt history i hsource hsource_nonterminal
        htarget htarget_nonterminal
        ((e.infoActionEquiv i
          (G.infoAt history i hsource hsource_nonterminal)).symm
            (cast
              (congrArg (H.InfoAction i) hinfo).symm
              action))).symm

/-- Reverse a strict structural isomorphism of observed EFGs. -/
def symm (e : G.Iso H) : H.Iso G where
  historyIso := e.historyIso.symm
  map_init := by
    change
      e.historyIso.stateEquiv.symm
          (Arena.HistoryFrom.nil H.base.toArena H.base.init) =
        Arena.HistoryFrom.nil G.base.toArena G.base.init
    apply e.historyIso.stateEquiv.injective
    rw [e.historyIso.stateEquiv.apply_symm_apply, e.map_init]
  map_mover := by
    intro history
    simpa using
      (e.map_mover
        (e.historyIso.stateEquiv.symm history)).symm
  map_payoff := by
    intro history hterminal
    have hsourceTerminal :
        G.base.isTerminal
          (e.historyIso.stateEquiv.symm history).1 := by
      apply
        (e.historyIso.isTerminal_iff
          (e.historyIso.stateEquiv.symm history)).mpr
      simpa using hterminal
    simpa using
      (e.map_payoff
        (e.historyIso.stateEquiv.symm history)
        hsourceTerminal).symm
  observationEquiv := fun i => (e.observationEquiv i).symm
  map_observe := by
    intro i history
    apply (e.observationEquiv i).injective
    simpa using
      (e.map_observe i
        (e.historyIso.stateEquiv.symm history)).symm
  publicEquiv := e.publicEquiv.symm
  map_publicObserve := by
    intro history
    apply e.publicEquiv.injective
    simpa using
      (e.map_publicObserve
        (e.historyIso.stateEquiv.symm history)).symm
  map_publicOf := by
    intro i observation
    apply e.publicEquiv.injective
    simpa using
      (e.map_publicOf i
        ((e.observationEquiv i).symm observation)).symm
  infoStateEquiv := fun i => (e.infoStateEquiv i).symm
  map_infoObserve := by
    intro i information
    apply (e.observationEquiv i).injective
    simpa using
      (e.map_infoObserve i
        ((e.infoStateEquiv i).symm information)).symm
  infoActionEquiv := e.inverseInfoActionEquiv
  map_infoAt := by
    intro history
    obtain ⟨sourceHistory, rfl⟩ :=
      e.historyIso.stateEquiv.surjective history
    intro i hsource hsource_nonterminal
      htarget htarget_nonterminal
    have htarget' :
        G.base.mover sourceHistory.1 = some i := by
      simpa [Arena.Iso.symm] using htarget
    have htarget_nonterminal' :
        G.base.toArena.IsDecision sourceHistory.1 := by
      simpa [Arena.Iso.symm] using htarget_nonterminal
    simpa [Arena.Iso.symm] using
      e.inverseInfoAt sourceHistory i
        htarget' htarget_nonterminal'
        hsource hsource_nonterminal
  map_infoActionAt := by
    intro history
    obtain ⟨sourceHistory, rfl⟩ :=
      e.historyIso.stateEquiv.surjective history
    intro i hsource hsource_nonterminal
      htarget htarget_nonterminal action
    have htarget' :
        G.base.mover sourceHistory.1 = some i := by
      simpa [Arena.Iso.symm] using htarget
    have htarget_nonterminal' :
        G.base.toArena.IsDecision sourceHistory.1 := by
      simpa [Arena.Iso.symm] using htarget_nonterminal
    have hcore :=
      e.inverse_infoActionAt
        sourceHistory i htarget' htarget_nonterminal'
        hsource hsource_nonterminal action
    apply eq_of_heq
    refine HEq.trans ?_ ((heq_iff_eq.mpr hcore).trans ?_)
    · apply actionEquiv_heq_of_history_eq G i
        (e.historyIso.stateEquiv.symm_apply_apply sourceHistory)
        htarget htarget_nonterminal
        htarget' htarget_nonterminal'
      exact
        (cast_heq _ _).trans
          (cast_heq _ _).symm
    · exact cast_heq _ _

end Iso

end ExtensiveGame.ObservedGame
