/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall

/-!
# Recall preservation under controlled morphisms

Transport of personal decisions, own-decision histories, private/public signal
histories, and classic/private/public recall through strict payoff-free
`ControlledObservedGame.Iso`s. This leaf depends only on the structural morphism
core and recall infrastructure; it has no subgame, finite-EFG, or structural
history-length dependency.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*}

namespace Iso

variable {G H : ControlledObservedGame N}

/-! ## Recall preservation -/

/-- A strict payoff-free isomorphism maps a packaged personal decision
through its information-state and information-action equivalences. -/
def personalDecisionEquiv (e : G.Iso H) (i : N) :
    G.PersonalDecision i ≃ H.PersonalDecision i :=
  (e.representedInfoEquiv i).sigmaCongr fun information =>
    e.infoActionEquiv i information.1

private theorem sigma_mk_cast_eq
    {α : Type*} {fiber : α → Type*}
    {first second : α} (hindex : first = second)
    (value : fiber first) :
    (⟨second, cast (congrArg fiber hindex) value⟩ :
        Σ index, fiber index) =
      ⟨first, value⟩ := by
  subst second
  rfl

/-- Mapping one concrete player decision agrees with mapping its packaged
information/action record. -/
theorem map_personalDecisionAt
    (e : G.Iso H) (i : N)
    (history : G.base.History)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (action : G.base.Action history.1) :
    H.personalDecisionAt i
        (e.historyIso.stateEquiv history) htarget
        (e.historyIso.actionEquiv history action) =
      e.personalDecisionEquiv i
        (G.personalDecisionAt i history hsource action) := by
  let hsource_nonterminal : G.base.toArena.IsDecision history.1 :=
    ⟨action⟩
  let htarget_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv history).1 :=
    ⟨e.historyIso.actionEquiv history action⟩
  let sourceInformation :=
    G.infoAt history i hsource hsource_nonterminal
  let sourceAction :=
    (G.actionEquiv history i hsource
      hsource_nonterminal).symm action
  let sourceCoordinate :=
    G.representedInfoAt history i hsource hsource_nonterminal
  let targetCoordinate :=
    H.representedInfoAt (e.historyIso.stateEquiv history) i
      htarget htarget_nonterminal
  have hinfo :
      e.infoStateEquiv i sourceInformation =
        H.infoAt (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal :=
    e.map_infoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal
  let mappedAction :=
    e.infoActionEquiv i sourceInformation sourceAction
  let mappedCoordinateAction :
      H.InfoAction i (e.representedInfoEquiv i sourceCoordinate).1 := by
    simpa [sourceCoordinate, sourceInformation,
      ControlledObservedGame.Iso.representedInfoEquiv] using mappedAction
  let transportedAction :=
    cast (congrArg (H.InfoAction i) hinfo) mappedAction
  have haction :
      (H.actionEquiv
          (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal).symm
          (e.historyIso.actionEquiv history action) =
        transportedAction := by
    apply
      (H.actionEquiv
        (e.historyIso.stateEquiv history) i htarget
        htarget_nonterminal).injective
    rw [(H.actionEquiv
      (e.historyIso.stateEquiv history) i htarget
      htarget_nonterminal).apply_symm_apply]
    simpa [sourceAction, sourceInformation, mappedAction,
      transportedAction] using
      (e.map_infoActionAt history i hsource hsource_nonterminal
        htarget htarget_nonterminal sourceAction).symm
  have hcoordinate :
      e.representedInfoEquiv i sourceCoordinate = targetCoordinate :=
    Subtype.ext hinfo
  change
    (⟨targetCoordinate,
      (H.actionEquiv
        (e.historyIso.stateEquiv history) i htarget
        htarget_nonterminal).symm
        (e.historyIso.actionEquiv history action)⟩ :
      H.PersonalDecision i) =
    e.personalDecisionEquiv i
      (⟨sourceCoordinate, sourceAction⟩ :
        G.PersonalDecision i)
  rw [haction]
  apply Sigma.ext hcoordinate.symm
  simp [personalDecisionEquiv, sourceCoordinate, targetCoordinate,
    sourceInformation, mappedAction,
    transportedAction]
  exact cast_heq _ _

/-- Strict history mapping sends a player's remembered decision sequence to
the pointwise-mapped source sequence. -/
theorem map_ownDecisionHistory [DecidableEq N]
    (e : G.Iso H) (i : N)
    (history : G.base.History) :
    H.ownDecisionHistory i
        (e.historyIso.stateEquiv history) =
      (G.ownDecisionHistory i history).map
        (e.personalDecisionEquiv i) := by
  obtain ⟨state, path⟩ := history
  induction path with
  | nil =>
      change
        H.ownDecisionHistory i
            (e.historyIso.stateEquiv
              (Arena.HistoryFrom.nil
                G.base.toArena G.base.init)) =
          (G.ownDecisionHistory i
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)).map
            (e.personalDecisionEquiv i)
      rw [e.map_init]
      rw [H.ownDecisionHistory_nil, G.ownDecisionHistory_nil]
      rfl
  | @snoc state path action ih =>
      let previous : G.base.History := ⟨state, path⟩
      change
        H.ownDecisionHistory i
            (e.historyIso.stateEquiv
              (G.base.unfold.toArena.next previous action)) =
          (G.ownDecisionHistory i
            (G.base.unfold.toArena.next previous action)).map
              (e.personalDecisionEquiv i)
      rw [e.historyIso.map_next previous action]
      change
        H.ownDecisionHistory i
            ⟨H.base.next
                (e.historyIso.stateEquiv previous).1
                (e.historyIso.actionEquiv previous action),
              (e.historyIso.stateEquiv previous).2.snoc
                (e.historyIso.actionEquiv previous action)⟩ =
          (G.ownDecisionHistory i
            ⟨G.base.next state action, path.snoc action⟩).map
              (e.personalDecisionEquiv i)
      by_cases hsource : G.base.mover state = some i
      · have htarget :
            H.base.mover
                (e.historyIso.stateEquiv previous).1 =
              some i := by
          rw [e.map_mover previous]
          exact hsource
        rw [H.ownDecisionHistory_snoc_of_mover
          i (e.historyIso.stateEquiv previous).2
          (e.historyIso.actionEquiv previous action)
          htarget]
        rw [G.ownDecisionHistory_snoc_of_mover
          i path action hsource]
        have ih' :
            H.ownDecisionHistory i
                ⟨(e.historyIso.stateEquiv previous).1,
                  (e.historyIso.stateEquiv previous).2⟩ =
              (G.ownDecisionHistory i ⟨state, path⟩).map
                (e.personalDecisionEquiv i) := by
          simpa [previous] using ih
        rw [List.map_append, ih', List.map_singleton]
        congr 1
        simpa [previous] using
          congrArg (fun decision => [decision])
            (e.map_personalDecisionAt
              i previous hsource htarget action)
      · have htarget :
            H.base.mover
                (e.historyIso.stateEquiv previous).1 ≠
              some i := by
          rw [e.map_mover previous]
          exact hsource
        rw [H.ownDecisionHistory_snoc_of_not_mover
          i (e.historyIso.stateEquiv previous).2
          (e.historyIso.actionEquiv previous action)
          htarget]
        rw [G.ownDecisionHistory_snoc_of_not_mover
          i path action hsource]
        exact ih

private theorem infoAt_eq_of_history_eq
    (K : ControlledObservedGame N) (i : N)
    {first second : K.base.History}
    (hhistory : first = second)
    (hfirst : K.base.mover first.1 = some i)
    (hfirst_nonterminal : K.base.toArena.IsDecision first.1)
    (hsecond : K.base.mover second.1 = some i)
    (hsecond_nonterminal : K.base.toArena.IsDecision second.1) :
    K.infoAt first i hfirst hfirst_nonterminal =
      K.infoAt second i hsecond hsecond_nonterminal := by
  subst second
  rfl

/-- Strict payoff-free observed-game isomorphisms preserve and reflect
classic perfect recall for one player. -/
theorem hasPerfectRecall_iff [DecidableEq N]
    (e : G.Iso H) (i : N) :
    G.HasPerfectRecall i ↔ H.HasPerfectRecall i := by
  constructor
  · intro hrecall targetFirst targetSecond
      htargetFirst htargetFirst_nonterminal
      htargetSecond htargetSecond_nonterminal hsame
    let sourceFirst :=
      e.historyIso.stateEquiv.symm targetFirst
    let sourceSecond :=
      e.historyIso.stateEquiv.symm targetSecond
    have hmapFirst :
        e.historyIso.stateEquiv sourceFirst = targetFirst :=
      e.historyIso.stateEquiv.apply_symm_apply targetFirst
    have hmapSecond :
        e.historyIso.stateEquiv sourceSecond = targetSecond :=
      e.historyIso.stateEquiv.apply_symm_apply targetSecond
    have hsourceFirst :
        G.base.mover sourceFirst.1 = some i := by
      have hmapped :
          H.base.mover
              (e.historyIso.stateEquiv sourceFirst).1 =
            some i := by
        simpa [hmapFirst] using htargetFirst
      rw [e.map_mover sourceFirst] at hmapped
      exact hmapped
    have hsourceSecond :
        G.base.mover sourceSecond.1 = some i := by
      have hmapped :
          H.base.mover
              (e.historyIso.stateEquiv sourceSecond).1 =
            some i := by
        simpa [hmapSecond] using htargetSecond
      rw [e.map_mover sourceSecond] at hmapped
      exact hmapped
    have hmappedFirst_nonterminal :
        H.base.toArena.IsDecision
          (e.historyIso.stateEquiv sourceFirst).1 := by
      simpa [hmapFirst] using htargetFirst_nonterminal
    have hmappedSecond_nonterminal :
        H.base.toArena.IsDecision
          (e.historyIso.stateEquiv sourceSecond).1 := by
      simpa [hmapSecond] using htargetSecond_nonterminal
    have hsourceFirst_nonterminal :
        G.base.toArena.IsDecision sourceFirst.1 :=
      (e.historyIso.isDecision_iff sourceFirst).mpr
        hmappedFirst_nonterminal
    have hsourceSecond_nonterminal :
        G.base.toArena.IsDecision sourceSecond.1 :=
      (e.historyIso.isDecision_iff sourceSecond).mpr
        hmappedSecond_nonterminal
    have hsourceInfo :
        G.infoAt sourceFirst i hsourceFirst
            hsourceFirst_nonterminal =
          G.infoAt sourceSecond i hsourceSecond
            hsourceSecond_nonterminal := by
      have hmappedFirst :
          H.base.mover
              (e.historyIso.stateEquiv sourceFirst).1 =
            some i := by
        rw [e.map_mover sourceFirst]
        exact hsourceFirst
      have hmappedSecond :
          H.base.mover
              (e.historyIso.stateEquiv sourceSecond).1 =
            some i := by
        rw [e.map_mover sourceSecond]
        exact hsourceSecond
      have hfirstInfo :
          H.infoAt
              (e.historyIso.stateEquiv sourceFirst)
              i hmappedFirst hmappedFirst_nonterminal =
            H.infoAt targetFirst i htargetFirst
              htargetFirst_nonterminal :=
        infoAt_eq_of_history_eq H i hmapFirst
          hmappedFirst hmappedFirst_nonterminal
          htargetFirst htargetFirst_nonterminal
      have hsecondInfo :
          H.infoAt
              (e.historyIso.stateEquiv sourceSecond)
              i hmappedSecond hmappedSecond_nonterminal =
            H.infoAt targetSecond i htargetSecond
              htargetSecond_nonterminal :=
        infoAt_eq_of_history_eq H i hmapSecond
          hmappedSecond hmappedSecond_nonterminal
          htargetSecond htargetSecond_nonterminal
      apply (e.infoStateEquiv i).injective
      calc
        e.infoStateEquiv i
            (G.infoAt sourceFirst i hsourceFirst
              hsourceFirst_nonterminal) =
          H.infoAt
            (e.historyIso.stateEquiv sourceFirst)
            i hmappedFirst hmappedFirst_nonterminal :=
            e.map_infoAt sourceFirst i
              hsourceFirst hsourceFirst_nonterminal
              hmappedFirst hmappedFirst_nonterminal
        _ = H.infoAt targetFirst i htargetFirst
            htargetFirst_nonterminal := hfirstInfo
        _ = H.infoAt targetSecond i htargetSecond
            htargetSecond_nonterminal := hsame
        _ = H.infoAt
            (e.historyIso.stateEquiv sourceSecond)
            i hmappedSecond hmappedSecond_nonterminal :=
              hsecondInfo.symm
        _ = e.infoStateEquiv i
            (G.infoAt sourceSecond i hsourceSecond
              hsourceSecond_nonterminal) :=
              (e.map_infoAt sourceSecond i
                hsourceSecond hsourceSecond_nonterminal
                hmappedSecond hmappedSecond_nonterminal).symm
    have hsourceHistory :=
      hrecall sourceFirst sourceSecond
        hsourceFirst hsourceFirst_nonterminal
        hsourceSecond hsourceSecond_nonterminal hsourceInfo
    have hfirstMap :=
      e.map_ownDecisionHistory i sourceFirst
    have hsecondMap :=
      e.map_ownDecisionHistory i sourceSecond
    rw [hsourceHistory] at hfirstMap
    calc
      H.ownDecisionHistory i targetFirst =
          H.ownDecisionHistory i
            (e.historyIso.stateEquiv sourceFirst) := by
              rw [hmapFirst]
      _ = (G.ownDecisionHistory i sourceSecond).map
          (e.personalDecisionEquiv i) := hfirstMap
      _ = H.ownDecisionHistory i
          (e.historyIso.stateEquiv sourceSecond) :=
            hsecondMap.symm
      _ = H.ownDecisionHistory i targetSecond := by
            rw [hmapSecond]
  · intro hrecall sourceFirst sourceSecond
      hsourceFirst hsourceFirst_nonterminal
      hsourceSecond hsourceSecond_nonterminal hsame
    have htargetFirst :
        H.base.mover
            (e.historyIso.stateEquiv sourceFirst).1 =
          some i := by
      rw [e.map_mover sourceFirst]
      exact hsourceFirst
    have htargetSecond :
        H.base.mover
            (e.historyIso.stateEquiv sourceSecond).1 =
          some i := by
      rw [e.map_mover sourceSecond]
      exact hsourceSecond
    have htargetFirst_nonterminal :
        H.base.toArena.IsDecision
          (e.historyIso.stateEquiv sourceFirst).1 :=
      (e.historyIso.isDecision_iff sourceFirst).mp
        hsourceFirst_nonterminal
    have htargetSecond_nonterminal :
        H.base.toArena.IsDecision
          (e.historyIso.stateEquiv sourceSecond).1 :=
      (e.historyIso.isDecision_iff sourceSecond).mp
        hsourceSecond_nonterminal
    have htargetInfo :
        H.infoAt
            (e.historyIso.stateEquiv sourceFirst)
            i htargetFirst htargetFirst_nonterminal =
          H.infoAt
            (e.historyIso.stateEquiv sourceSecond)
            i htargetSecond htargetSecond_nonterminal := by
      rw [← e.map_infoAt sourceFirst i
        hsourceFirst hsourceFirst_nonterminal
        htargetFirst htargetFirst_nonterminal]
      rw [← e.map_infoAt sourceSecond i
        hsourceSecond hsourceSecond_nonterminal
        htargetSecond htargetSecond_nonterminal]
      exact congrArg (e.infoStateEquiv i) hsame
    have htargetHistory :=
      hrecall
        (e.historyIso.stateEquiv sourceFirst)
        (e.historyIso.stateEquiv sourceSecond)
        htargetFirst htargetFirst_nonterminal
        htargetSecond htargetSecond_nonterminal htargetInfo
    rw [e.map_ownDecisionHistory i sourceFirst,
      e.map_ownDecisionHistory i sourceSecond] at htargetHistory
    exact
      (e.personalDecisionEquiv i).injective.list_map
        htargetHistory

/-- Strict payoff-free observed-game isomorphisms preserve and reflect
classic perfect recall for every player. -/
theorem perfectRecall_iff [DecidableEq N]
    (e : G.Iso H) :
    G.PerfectRecall ↔ H.PerfectRecall := by
  constructor <;> intro hrecall i
  · exact (e.hasPerfectRecall_iff i).mp (hrecall i)
  · exact (e.hasPerfectRecall_iff i).mpr (hrecall i)

/-- Strict history mapping sends a private-signal history to the pointwise
mapped source signal history. -/
theorem map_signalHistory
    (e : G.Iso H) (i : N)
    (history : G.base.History) :
    H.signalHistory i (e.historyIso.stateEquiv history) =
      (G.signalHistory i history).map
        (e.observationEquiv i) := by
  obtain ⟨state, path⟩ := history
  induction path with
  | nil =>
      change
        H.signalHistory i
            (e.historyIso.stateEquiv
              (Arena.HistoryFrom.nil
                G.base.toArena G.base.init)) =
          (G.signalHistory i
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)).map
            (e.observationEquiv i)
      rw [e.map_init]
      simp only [ControlledObservedGame.signalHistory]
      have hobserve :=
        (e.map_observe i
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init)).symm
      rw [e.map_init] at hobserve
      exact congrArg (fun observation => [observation]) hobserve
  | @snoc state path action ih =>
      let previous : G.base.History := ⟨state, path⟩
      change
        H.signalHistory i
            (e.historyIso.stateEquiv
              (G.base.unfold.toArena.next previous action)) =
          (G.signalHistory i
            (G.base.unfold.toArena.next previous action)).map
              (e.observationEquiv i)
      rw [e.historyIso.map_next previous action]
      change
        H.signalHistoryPath i
            ((e.historyIso.stateEquiv previous).2.snoc
              (e.historyIso.actionEquiv previous action)) =
          (G.signalHistoryPath i (path.snoc action)).map
            (e.observationEquiv i)
      simp only [ControlledObservedGame.signalHistoryPath,
        List.map_append, List.map_singleton]
      have ih' :
          H.signalHistoryPath i
              (e.historyIso.stateEquiv previous).2 =
            (G.signalHistoryPath i path).map
              (e.observationEquiv i) := by
        simpa [ControlledObservedGame.signalHistory,
          previous] using ih
      rw [ih']
      congr 1
      have hobserve :=
        (e.map_observe i
          (G.base.unfold.toArena.next previous action)).symm
      rw [e.historyIso.map_next previous action] at hobserve
      simpa [previous] using
        congrArg (fun observation => [observation]) hobserve

/-- Strict history mapping sends a public-signal history to the pointwise
mapped source public-signal history. -/
theorem map_publicSignalHistory
    (e : G.Iso H)
    (history : G.base.History) :
    H.publicSignalHistory (e.historyIso.stateEquiv history) =
      (G.publicSignalHistory history).map e.publicEquiv := by
  obtain ⟨state, path⟩ := history
  induction path with
  | nil =>
      change
        H.publicSignalHistory
            (e.historyIso.stateEquiv
              (Arena.HistoryFrom.nil
                G.base.toArena G.base.init)) =
          (G.publicSignalHistory
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)).map e.publicEquiv
      rw [e.map_init]
      simp only [ControlledObservedGame.publicSignalHistory]
      have hobserve :=
        (e.map_publicObserve
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init)).symm
      rw [e.map_init] at hobserve
      exact congrArg (fun observation => [observation]) hobserve
  | @snoc state path action ih =>
      let previous : G.base.History := ⟨state, path⟩
      change
        H.publicSignalHistory
            (e.historyIso.stateEquiv
              (G.base.unfold.toArena.next previous action)) =
          (G.publicSignalHistory
            (G.base.unfold.toArena.next previous action)).map
              e.publicEquiv
      rw [e.historyIso.map_next previous action]
      change
        H.publicSignalHistoryPath
            ((e.historyIso.stateEquiv previous).2.snoc
              (e.historyIso.actionEquiv previous action)) =
          (G.publicSignalHistoryPath (path.snoc action)).map
            e.publicEquiv
      simp only [ControlledObservedGame.publicSignalHistoryPath,
        List.map_append, List.map_singleton]
      have ih' :
          H.publicSignalHistoryPath
              (e.historyIso.stateEquiv previous).2 =
            (G.publicSignalHistoryPath path).map
              e.publicEquiv := by
        simpa [ControlledObservedGame.publicSignalHistory,
          previous] using ih
      rw [ih']
      congr 1
      have hobserve :=
        (e.map_publicObserve
          (G.base.unfold.toArena.next previous action)).symm
      rw [e.historyIso.map_next previous action] at hobserve
      simpa [previous] using
        congrArg (fun observation => [observation]) hobserve

/-- A strict payoff-free observed-game isomorphism transports private-signal
perfect recall in its forward direction. -/
theorem hasEventClockSignalPerfectRecall_of
    (e : G.Iso H) (i : N)
    (hrecall : G.HasEventClockSignalPerfectRecall i) :
    H.HasEventClockSignalPerfectRecall i := by
  intro targetFirst targetSecond
    htargetFirst htargetFirst_nonterminal
    htargetSecond htargetSecond_nonterminal hsame
  let sourceFirst :=
    e.historyIso.stateEquiv.symm targetFirst
  let sourceSecond :=
    e.historyIso.stateEquiv.symm targetSecond
  have hmapFirst :
      e.historyIso.stateEquiv sourceFirst = targetFirst :=
    e.historyIso.stateEquiv.apply_symm_apply targetFirst
  have hmapSecond :
      e.historyIso.stateEquiv sourceSecond = targetSecond :=
    e.historyIso.stateEquiv.apply_symm_apply targetSecond
  have hsourceFirst :
      G.base.mover sourceFirst.1 = some i := by
    have hmapped :
        H.base.mover
            (e.historyIso.stateEquiv sourceFirst).1 =
          some i := by
      simpa [hmapFirst] using htargetFirst
    rw [e.map_mover sourceFirst] at hmapped
    exact hmapped
  have hsourceSecond :
      G.base.mover sourceSecond.1 = some i := by
    have hmapped :
        H.base.mover
            (e.historyIso.stateEquiv sourceSecond).1 =
          some i := by
      simpa [hmapSecond] using htargetSecond
    rw [e.map_mover sourceSecond] at hmapped
    exact hmapped
  have hmappedFirst_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv sourceFirst).1 := by
    simpa [hmapFirst] using htargetFirst_nonterminal
  have hmappedSecond_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv sourceSecond).1 := by
    simpa [hmapSecond] using htargetSecond_nonterminal
  have hsourceFirst_nonterminal :
      G.base.toArena.IsDecision sourceFirst.1 :=
    (e.historyIso.isDecision_iff sourceFirst).mpr
      hmappedFirst_nonterminal
  have hsourceSecond_nonterminal :
      G.base.toArena.IsDecision sourceSecond.1 :=
    (e.historyIso.isDecision_iff sourceSecond).mpr
      hmappedSecond_nonterminal
  have hmappedFirst :
      H.base.mover
          (e.historyIso.stateEquiv sourceFirst).1 =
        some i := by
    rw [e.map_mover sourceFirst]
    exact hsourceFirst
  have hmappedSecond :
      H.base.mover
          (e.historyIso.stateEquiv sourceSecond).1 =
        some i := by
    rw [e.map_mover sourceSecond]
    exact hsourceSecond
  have hsourceInfo :
      G.infoAt sourceFirst i hsourceFirst
          hsourceFirst_nonterminal =
        G.infoAt sourceSecond i hsourceSecond
          hsourceSecond_nonterminal := by
    apply (e.infoStateEquiv i).injective
    calc
      e.infoStateEquiv i
          (G.infoAt sourceFirst i hsourceFirst
            hsourceFirst_nonterminal) =
        H.infoAt
          (e.historyIso.stateEquiv sourceFirst)
          i hmappedFirst hmappedFirst_nonterminal :=
          e.map_infoAt sourceFirst i hsourceFirst
            hsourceFirst_nonterminal hmappedFirst
            hmappedFirst_nonterminal
      _ = H.infoAt targetFirst i htargetFirst
          htargetFirst_nonterminal :=
        infoAt_eq_of_history_eq H i hmapFirst
          hmappedFirst hmappedFirst_nonterminal
          htargetFirst htargetFirst_nonterminal
      _ = H.infoAt targetSecond i htargetSecond
          htargetSecond_nonterminal := hsame
      _ = H.infoAt
          (e.historyIso.stateEquiv sourceSecond)
          i hmappedSecond hmappedSecond_nonterminal :=
        (infoAt_eq_of_history_eq H i hmapSecond
          hmappedSecond hmappedSecond_nonterminal
          htargetSecond htargetSecond_nonterminal).symm
      _ = e.infoStateEquiv i
          (G.infoAt sourceSecond i hsourceSecond
            hsourceSecond_nonterminal) :=
        (e.map_infoAt sourceSecond i
          hsourceSecond hsourceSecond_nonterminal
          hmappedSecond hmappedSecond_nonterminal).symm
  have hsourceSignals :=
    hrecall sourceFirst sourceSecond
      hsourceFirst hsourceFirst_nonterminal
      hsourceSecond hsourceSecond_nonterminal hsourceInfo
  calc
    H.signalHistory i targetFirst =
        H.signalHistory i
          (e.historyIso.stateEquiv sourceFirst) := by
            rw [hmapFirst]
    _ = (G.signalHistory i sourceFirst).map
        (e.observationEquiv i) :=
          e.map_signalHistory i sourceFirst
    _ = (G.signalHistory i sourceSecond).map
        (e.observationEquiv i) := congrArg
          (List.map (e.observationEquiv i)) hsourceSignals
    _ = H.signalHistory i
        (e.historyIso.stateEquiv sourceSecond) :=
          (e.map_signalHistory i sourceSecond).symm
    _ = H.signalHistory i targetSecond := by
          rw [hmapSecond]

/-- Strict payoff-free observed-game isomorphisms preserve and reflect
private-signal perfect recall for one player. -/
theorem hasEventClockSignalPerfectRecall_iff
    (e : G.Iso H) (i : N) :
    G.HasEventClockSignalPerfectRecall i ↔
      H.HasEventClockSignalPerfectRecall i := by
  constructor
  · exact e.hasEventClockSignalPerfectRecall_of i
  · intro hrecall
    exact e.symm.hasEventClockSignalPerfectRecall_of i hrecall

/-- Strict payoff-free observed-game isomorphisms preserve and reflect
private-signal perfect recall for every player. -/
theorem eventClockSignalPerfectRecall_iff
    (e : G.Iso H) :
    G.EventClockSignalPerfectRecall ↔
      H.EventClockSignalPerfectRecall := by
  constructor <;> intro hrecall i
  · exact (e.hasEventClockSignalPerfectRecall_iff i).mp (hrecall i)
  · exact (e.hasEventClockSignalPerfectRecall_iff i).mpr (hrecall i)

/-- A strict payoff-free observed-game isomorphism transports public-signal
perfect recall in its forward direction. -/
theorem hasEventClockPublicPerfectRecall_of
    (e : G.Iso H)
    (hrecall : G.HasEventClockPublicPerfectRecall) :
    H.HasEventClockPublicPerfectRecall := by
  intro targetFirst targetSecond hsame
  let sourceFirst :=
    e.historyIso.stateEquiv.symm targetFirst
  let sourceSecond :=
    e.historyIso.stateEquiv.symm targetSecond
  have hmapFirst :
      e.historyIso.stateEquiv sourceFirst = targetFirst :=
    e.historyIso.stateEquiv.apply_symm_apply targetFirst
  have hmapSecond :
      e.historyIso.stateEquiv sourceSecond = targetSecond :=
    e.historyIso.stateEquiv.apply_symm_apply targetSecond
  have hsourcePublic :
      G.publicObserve sourceFirst =
        G.publicObserve sourceSecond := by
    apply e.publicEquiv.injective
    calc
      e.publicEquiv (G.publicObserve sourceFirst) =
          H.publicObserve
            (e.historyIso.stateEquiv sourceFirst) :=
        e.map_publicObserve sourceFirst
      _ = H.publicObserve targetFirst := by rw [hmapFirst]
      _ = H.publicObserve targetSecond := hsame
      _ = H.publicObserve
          (e.historyIso.stateEquiv sourceSecond) := by
            rw [hmapSecond]
      _ = e.publicEquiv (G.publicObserve sourceSecond) :=
        (e.map_publicObserve sourceSecond).symm
  have hsourceSignals :=
    hrecall sourceFirst sourceSecond hsourcePublic
  calc
    H.publicSignalHistory targetFirst =
        H.publicSignalHistory
          (e.historyIso.stateEquiv sourceFirst) := by
            rw [hmapFirst]
    _ = (G.publicSignalHistory sourceFirst).map e.publicEquiv :=
      e.map_publicSignalHistory sourceFirst
    _ = (G.publicSignalHistory sourceSecond).map e.publicEquiv :=
      congrArg (List.map e.publicEquiv) hsourceSignals
    _ = H.publicSignalHistory
        (e.historyIso.stateEquiv sourceSecond) :=
      (e.map_publicSignalHistory sourceSecond).symm
    _ = H.publicSignalHistory targetSecond := by
          rw [hmapSecond]

/-- Strict payoff-free observed-game isomorphisms preserve and reflect
public-signal perfect recall. -/
theorem hasEventClockPublicPerfectRecall_iff
    (e : G.Iso H) :
    G.HasEventClockPublicPerfectRecall ↔
      H.HasEventClockPublicPerfectRecall := by
  constructor
  · exact e.hasEventClockPublicPerfectRecall_of
  · intro hrecall
    exact e.symm.hasEventClockPublicPerfectRecall_of hrecall


end Iso

end ExtensiveGame.ControlledObservedGame
