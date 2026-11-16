/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Subgame

/-!
# Lawful-subgame preservation under controlled morphisms

Transport of occurrence-sensitive continuations, lawful roots, selected lawful
subgame systems, and complete standard-subgame systems through strict payoff-free
`ControlledObservedGame.Iso`s. This leaf depends on the structural morphism core
and the controlled subgame infrastructure, but not on recall.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*}

namespace Iso

variable {G H : ControlledObservedGame N}

/-! ## Lawful-subgame preservation -/

/-- Strict arena morphisms preserve reachability. -/
private theorem mapReachable
    {A B : Arena} (f : A.Hom B)
    {source target : A.State}
    (hreachable : Arena.Reachable A source target) :
    Arena.Reachable B (f.state source) (f.state target) := by
  induction hreachable with
  | refl =>
      exact Arena.Reachable.refl _
  | @step source next action hreach ih =>
      refine Arena.Reachable.step (f.action source action) ?_
      rw [← f.map_next source action]
      exact ih

/-- Strict payoff-free isomorphisms preserve and reflect the
occurrence-sensitive continuation relation. -/
theorem map_isContinuationOf
    (e : G.Iso H)
    (root current : G.base.History) :
    G.IsContinuationOf root current ↔
      H.IsContinuationOf
        (e.historyIso.stateEquiv root)
        (e.historyIso.stateEquiv current) := by
  constructor
  · exact mapReachable e.historyIso.toHom
  · intro htarget
    have hsource :=
      mapReachable e.historyIso.symm.toHom htarget
    change
      Arena.Reachable G.base.unfold.toArena
        (e.historyIso.stateEquiv.symm
          (e.historyIso.stateEquiv root))
        (e.historyIso.stateEquiv.symm
          (e.historyIso.stateEquiv current))
      at hsource
    change Arena.Reachable G.base.unfold.toArena root current
    simpa only [Equiv.symm_apply_apply] using hsource

/-- Transport structural lawfulness of one target root through a strict
payoff-free isomorphism. -/
def mapLawfulSubgameRoot
    (e : G.Iso H)
    (root : H.base.History)
    (hlawful :
      G.IsLawfulSubgameRoot
        (e.historyIso.stateEquiv.symm root)) :
    H.IsLawfulSubgameRoot root where
  root_information_singleton := by
    intro hproper i hmover hnonterminal other hother
      hother_nonterminal hinfo
    let f := e.symm
    have hsourceProper :
        f.historyIso.stateEquiv root ≠
          Arena.HistoryFrom.nil
            G.base.toArena G.base.init := by
      intro hsourceInit
      apply hproper
      apply f.historyIso.stateEquiv.injective
      exact hsourceInit.trans f.map_init.symm
    have hrootMover :
        G.base.mover
            (f.historyIso.stateEquiv root).1 =
          some i := by
      rw [f.map_mover root, hmover]
    have hrootNonterminal :
        G.base.toArena.IsDecision
          (f.historyIso.stateEquiv root).1 :=
      (f.historyIso.isDecision_iff root).mp hnonterminal
    have hotherMover :
        G.base.mover
            (f.historyIso.stateEquiv other).1 =
          some i := by
      rw [f.map_mover other, hother]
    have hotherNonterminal :
        G.base.toArena.IsDecision
          (f.historyIso.stateEquiv other).1 :=
      (f.historyIso.isDecision_iff other).mp hother_nonterminal
    have hsourceInfo :
        G.infoAt
            (f.historyIso.stateEquiv root)
            i hrootMover hrootNonterminal =
          G.infoAt
            (f.historyIso.stateEquiv other)
            i hotherMover hotherNonterminal := by
      rw [← f.map_infoAt root i hmover hnonterminal
          hrootMover hrootNonterminal,
        ← f.map_infoAt other i hother hother_nonterminal
          hotherMover hotherNonterminal,
        hinfo]
    have hsourceEq :=
      hlawful.root_information_singleton
        hsourceProper i hrootMover hrootNonterminal
        (f.historyIso.stateEquiv other)
        hotherMover hotherNonterminal hsourceInfo
    exact f.historyIso.stateEquiv.injective hsourceEq
  information_closed := by
    intro current hcurrent i hmover hnonterminal other hother
      hother_nonterminal hinfo
    let f := e.symm
    have hcurrentSource :
        G.IsContinuationOf
          (f.historyIso.stateEquiv root)
          (f.historyIso.stateEquiv current) :=
      (f.map_isContinuationOf root current).mp hcurrent
    have hcurrentMover :
        G.base.mover
            (f.historyIso.stateEquiv current).1 =
          some i := by
      rw [f.map_mover current, hmover]
    have hcurrentNonterminal :
        G.base.toArena.IsDecision
          (f.historyIso.stateEquiv current).1 :=
      (f.historyIso.isDecision_iff current).mp hnonterminal
    have hotherMover :
        G.base.mover
            (f.historyIso.stateEquiv other).1 =
          some i := by
      rw [f.map_mover other, hother]
    have hotherNonterminal :
        G.base.toArena.IsDecision
          (f.historyIso.stateEquiv other).1 :=
      (f.historyIso.isDecision_iff other).mp hother_nonterminal
    have hsourceInfo :
        G.infoAt
            (f.historyIso.stateEquiv current)
            i hcurrentMover hcurrentNonterminal =
          G.infoAt
            (f.historyIso.stateEquiv other)
            i hotherMover hotherNonterminal := by
      rw [← f.map_infoAt current i hmover hnonterminal
          hcurrentMover hcurrentNonterminal,
        ← f.map_infoAt other i hother hother_nonterminal
          hotherMover hotherNonterminal,
        hinfo]
    have hotherSource :=
      hlawful.information_closed
        (f.historyIso.stateEquiv current)
        hcurrentSource i hcurrentMover hcurrentNonterminal
        (f.historyIso.stateEquiv other)
        hotherMover hotherNonterminal hsourceInfo
    exact (f.map_isContinuationOf root other).mpr hotherSource

/-- Transport a payoff-free lawful subgame system through a strict
isomorphism. -/
def mapSubgameSystem
    (e : G.Iso H) (system : G.SubgameSystem) :
    H.SubgameSystem where
  IsRoot target :=
    system.IsRoot (e.historyIso.stateEquiv.symm target)
  init_isRoot := by
    rw [← e.map_init, Equiv.symm_apply_apply]
    exact system.init_isRoot
  lawful := by
    intro target hroot
    exact
      e.mapLawfulSubgameRoot target
        (system.isLawful hroot)

/-- Transport a complete payoff-free standard-subgame system through a
strict isomorphism. -/
def mapCompleteSubgameSystem
    (e : G.Iso H)
    (system : G.CompleteSubgameSystem) :
    H.CompleteSubgameSystem where
  toSubgameSystem :=
    e.mapSubgameSystem system.toSubgameSystem
  complete := by
    intro target htarget
    let source :=
      e.historyIso.stateEquiv.symm target
    have hsource :
        G.IsLawfulSubgameRoot source := by
      apply e.symm.mapLawfulSubgameRoot source
      change
        H.IsLawfulSubgameRoot
          (e.historyIso.stateEquiv source)
      rw [show
        e.historyIso.stateEquiv source = target by
          exact
            e.historyIso.stateEquiv.apply_symm_apply target]
      exact htarget
    exact system.complete source hsource


end Iso

end ExtensiveGame.ControlledObservedGame
