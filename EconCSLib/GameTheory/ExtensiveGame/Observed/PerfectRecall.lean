/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Morphism
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Recall

/-!
# Payoff-aware compatibility for perfect recall

Classic recall, no absent-mindedness, remembered-decision extraction, and
recall certificates are implemented once on `ControlledObservedGame`.
This module retains the historical `ObservedGame` API as definitional
payoff-forgetting adapters and delegates strict-isomorphism preservation to
`ControlledObservedGame.Iso`.

The classic condition follows [MFoGT, Def. 6.3.3]: equal current information
must determine the same ordered sequence of the player's earlier information
states and own actions. `RecallCertificate` is EconCSLib's factorized
history-indexed representation of that condition, not an additional
literature theorem.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} {G H : ObservedGame N U}

/-- Compatibility spelling for one remembered information/action decision. -/
abbrev PersonalDecision (G : ObservedGame N U) (i : N) :=
  G.toControlledObservedGame.PersonalDecision i

/-- Package the decision represented by a concrete action. -/
abbrev personalDecisionAt (G : ObservedGame N U) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover history.1 = some i)
    (action : G.base.Action history.1) :
    G.PersonalDecision i :=
  G.toControlledObservedGame.personalDecisionAt
    i history hmover action

/-- Realizing and repackaging an observed information action recovers the
original information/action pair. -/
@[simp]
theorem personalDecisionAt_actionEquiv
    (G : ObservedGame N U) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover history.1 = some i)
    (hdecision : G.base.toArena.IsDecision history.1)
    (action :
      G.InfoAction i (G.infoAt history i hmover hdecision)) :
    G.personalDecisionAt i history hmover
        (G.actionEquiv history i hmover hdecision action) =
      ⟨G.representedInfoAt history i hmover hdecision, action⟩ :=
  ControlledObservedGame.personalDecisionAt_actionEquiv
    G.toControlledObservedGame i history hmover hdecision action

/-- Compatibility spelling for the path-recursive remembered-decision
extractor. -/
abbrev ownDecisionHistoryPath [DecidableEq N]
    (G : ObservedGame N U) (i : N) :
    {state : G.base.State} →
      G.base.toArena.History G.base.init state →
        List (G.PersonalDecision i) :=
  G.toControlledObservedGame.ownDecisionHistoryPath i

/-- Ordered sequence of player `i`'s previous information/action decisions. -/
abbrev ownDecisionHistory [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    List (G.PersonalDecision i) :=
  G.toControlledObservedGame.ownDecisionHistory i history

/-- Compatibility spelling for a concrete remembered-decision occurrence. -/
abbrev PersonalDecisionOccurrence
    (G : ObservedGame N U) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (decision : G.PersonalDecision i) :=
  G.toControlledObservedGame.PersonalDecisionOccurrence
    i history decision

/-- Every remembered decision has an occurrence in the underlying history. -/
theorem exists_personalDecisionOccurrence_of_mem
    [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (decision : G.PersonalDecision i)
    (hmem : decision ∈ G.ownDecisionHistory i history) :
    Nonempty
      (G.PersonalDecisionOccurrence i history decision) :=
  ControlledObservedGame.exists_personalDecisionOccurrence_of_mem
    G.toControlledObservedGame i history decision hmem

@[simp]
theorem ownDecisionHistory_nil [DecidableEq N]
    (G : ObservedGame N U) (i : N) :
    G.ownDecisionHistory i
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) = [] :=
  G.toControlledObservedGame.ownDecisionHistory_nil i

@[simp]
theorem ownDecisionHistory_snoc_of_mover [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state)
    (hmover : G.base.mover state = some i) :
    G.ownDecisionHistory i
        ⟨G.base.next state action, path.snoc action⟩ =
      G.ownDecisionHistory i ⟨state, path⟩ ++
        [G.personalDecisionAt i ⟨state, path⟩ hmover action] :=
  ControlledObservedGame.ownDecisionHistory_snoc_of_mover
    G.toControlledObservedGame i path action hmover

@[simp]
theorem ownDecisionHistory_snoc_of_not_mover [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state)
    (hmover : G.base.mover state ≠ some i) :
    G.ownDecisionHistory i
        ⟨G.base.next state action, path.snoc action⟩ =
      G.ownDecisionHistory i ⟨state, path⟩ :=
  ControlledObservedGame.ownDecisionHistory_snoc_of_not_mover
    G.toControlledObservedGame i path action hmover

/-- Appending a suffix cannot shorten remembered own decisions. -/
theorem ownDecisionHistory_length_le_append
    [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    {middle finish : G.base.State}
    (basePath : G.base.toArena.History G.base.init middle)
    (suffix : G.base.toArena.History middle finish) :
    (G.ownDecisionHistory i ⟨middle, basePath⟩).length ≤
      (G.ownDecisionHistory i
        ⟨finish, basePath.append suffix⟩).length :=
  ControlledObservedGame.ownDecisionHistory_length_le_append
    G.toControlledObservedGame i basePath suffix

/-- A continuation preserves the earlier remembered-decision list as a
prefix. -/
theorem ownDecisionHistory_prefix_append
    [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    {middle finish : G.base.State}
    (basePath : G.base.toArena.History G.base.init middle)
    (suffix : G.base.toArena.History middle finish) :
    G.ownDecisionHistory i ⟨middle, basePath⟩ <+:
      G.ownDecisionHistory i
        ⟨finish, basePath.append suffix⟩ :=
  ControlledObservedGame.ownDecisionHistory_prefix_append
    G.toControlledObservedGame i basePath suffix

/-- Compatibility spelling for classic perfect recall of one player. -/
abbrev HasPerfectRecall [DecidableEq N]
    (G : ObservedGame N U) (i : N) : Prop :=
  G.toControlledObservedGame.HasPerfectRecall i

/-- Compatibility spelling for singleton decision information. -/
abbrev HasSingletonInformation
    (G : ObservedGame N U) (i : N) : Prop :=
  G.toControlledObservedGame.HasSingletonInformation i

/-- Singleton decision information implies perfect recall. -/
theorem HasSingletonInformation.hasPerfectRecall
    [DecidableEq N] {i : N}
    (hinformation : G.HasSingletonInformation i) :
    G.HasPerfectRecall i :=
  ControlledObservedGame.HasSingletonInformation.hasPerfectRecall
    hinformation

/-- Every player has singleton decision information. -/
abbrev PerfectInformation (G : ObservedGame N U) : Prop :=
  G.toControlledObservedGame.PerfectInformation

/-- Every player has classic perfect recall. -/
abbrev PerfectRecall [DecidableEq N]
    (G : ObservedGame N U) : Prop :=
  G.toControlledObservedGame.PerfectRecall

/-- Compatibility spelling for no absent-mindedness of one player. -/
abbrev HasNoAbsentMindedness
    (G : ObservedGame N U) (i : N) : Prop :=
  G.toControlledObservedGame.HasNoAbsentMindedness i

/-- An earlier remembered information state differs from the current one
under no absent-mindedness. -/
theorem HasNoAbsentMindedness.info_ne_of_mem_ownDecisionHistory
    [DecidableEq N] {i : N}
    (hnoAbsent : G.HasNoAbsentMindedness i)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover history.1 = some i)
    (hdecision : G.base.toArena.IsDecision history.1)
    (decision : G.PersonalDecision i)
    (hmem : decision ∈ G.ownDecisionHistory i history) :
    decision.1 ≠ G.representedInfoAt history i hmover hdecision :=
  ControlledObservedGame.HasNoAbsentMindedness.info_ne_of_mem_ownDecisionHistory
    hnoAbsent history hmover hdecision decision hmem

/-- No player is absent-minded. -/
abbrev NoAbsentMindedness (G : ObservedGame N U) : Prop :=
  G.toControlledObservedGame.NoAbsentMindedness

/-- Perfect recall rules out absent-mindedness. -/
theorem HasPerfectRecall.hasNoAbsentMindedness
    [DecidableEq N] {i : N}
    (hrecall : G.HasPerfectRecall i) :
    G.HasNoAbsentMindedness i :=
  ControlledObservedGame.HasPerfectRecall.hasNoAbsentMindedness
    hrecall

/-- Playerwise perfect recall implies global no absent-mindedness. -/
theorem PerfectRecall.noAbsentMindedness
    [DecidableEq N]
    (hrecall : G.PerfectRecall) :
    G.NoAbsentMindedness :=
  fun i => (hrecall i).hasNoAbsentMindedness

/-- Perfect information implies perfect recall. -/
theorem PerfectInformation.perfectRecall
    [DecidableEq N]
    (hinformation : G.PerfectInformation) :
    G.PerfectRecall :=
  fun i => (hinformation i).hasPerfectRecall

/-- Compatibility spelling for a payoff-free recall factorization
certificate. -/
abbrev RecallCertificate [DecidableEq N]
    (G : ObservedGame N U) :=
  G.toControlledObservedGame.RecallCertificate

namespace RecallCertificate

/-- The compatibility certificate agrees with the legacy observed-game
information and decision-history spellings. -/
theorem remembered_infoAt [DecidableEq N]
    (certificate : G.RecallCertificate)
    (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover history.1 = some i)
    (hdecision : G.base.toArena.IsDecision history.1) :
    certificate.remembered i
        (G.representedInfoAt history i hmover hdecision) =
      G.ownDecisionHistory i history :=
  ControlledObservedGame.RecallCertificate.remembered_infoAt
    certificate i history hmover hdecision

/-- A factorization certificate proves perfect recall. -/
theorem perfectRecall [DecidableEq N]
    (certificate : G.RecallCertificate) :
    G.PerfectRecall :=
  ControlledObservedGame.RecallCertificate.perfectRecall certificate

end RecallCertificate

/-- Perfect recall is equivalent to existence of a recall certificate. -/
theorem recallCertificate_nonempty_iff_perfectRecall
    [DecidableEq N]
    (G : ObservedGame N U) :
    Nonempty G.RecallCertificate ↔ G.PerfectRecall :=
  ControlledObservedGame.recallCertificate_nonempty_iff_perfectRecall
    G.toControlledObservedGame

namespace Iso

/-- Strictly map a remembered personal decision. -/
def personalDecisionEquiv (e : G.Iso H) (i : N) :
    G.PersonalDecision i ≃ H.PersonalDecision i :=
  e.toControlledIso.personalDecisionEquiv i

/-- Mapping a concrete decision agrees with mapping its packaged record. -/
theorem map_personalDecisionAt
    (e : G.Iso H) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (action : G.base.Action history.1) :
    H.personalDecisionAt i
        (e.historyIso.stateEquiv history) htarget
        (e.historyIso.actionEquiv history action) =
      e.personalDecisionEquiv i
        (G.personalDecisionAt i history hsource action) :=
  e.toControlledIso.map_personalDecisionAt
    i history hsource htarget action

/-- Strict history mapping acts pointwise on remembered decisions. -/
theorem map_ownDecisionHistory [DecidableEq N]
    (e : G.Iso H) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    H.ownDecisionHistory i
        (e.historyIso.stateEquiv history) =
      (G.ownDecisionHistory i history).map
        (e.personalDecisionEquiv i) :=
  e.toControlledIso.map_ownDecisionHistory i history

/-- Strict isomorphisms preserve and reflect one-player perfect recall. -/
theorem hasPerfectRecall_iff [DecidableEq N]
    (e : G.Iso H) (i : N) :
    G.HasPerfectRecall i ↔ H.HasPerfectRecall i :=
  e.toControlledIso.hasPerfectRecall_iff i

/-- Strict isomorphisms preserve and reflect global perfect recall. -/
theorem perfectRecall_iff [DecidableEq N]
    (e : G.Iso H) :
    G.PerfectRecall ↔ H.PerfectRecall :=
  e.toControlledIso.perfectRecall_iff

/-- Strict isomorphisms preserve and reflect existence of recall
certificates. -/
theorem recallCertificate_nonempty_iff
    [DecidableEq N]
    (e : G.Iso H) :
    Nonempty G.RecallCertificate ↔
      Nonempty H.RecallCertificate := by
  rw [G.recallCertificate_nonempty_iff_perfectRecall,
    H.recallCertificate_nonempty_iff_perfectRecall]
  exact e.perfectRecall_iff

end Iso

end ExtensiveGame.ObservedGame
