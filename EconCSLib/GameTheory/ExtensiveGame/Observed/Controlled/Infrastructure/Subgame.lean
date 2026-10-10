/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# Payoff-free lawful subgames

Occurrence-sensitive continuations, lawful subgame roots, selected subgame
systems, and complete subgame systems for `ControlledObservedGame`. Root
presentation remains an external choice, distinct from structural lawfulness.
Bijective player relabeling preserves and reflects root lawfulness and
transports both selected and complete systems without changing histories.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N M : Type*} {G : ControlledObservedGame N}

/-! ## Payoff-free lawful subgames -/

/-- `current` is an occurrence-sensitive continuation of `root`. -/
def IsContinuationOf
    (G : ControlledObservedGame N)
    (root current : G.base.History) : Prop :=
  Arena.Reachable G.base.unfold.toArena root current

/-- Every complete history is its own continuation. -/
theorem IsContinuationOf.refl
    (G : ControlledObservedGame N)
    (root : G.base.History) :
    G.IsContinuationOf root root :=
  by
    change Arena.Reachable G.base.unfold.toArena root root
    exact @Arena.Reachable.refl G.base.unfold.toArena root

/-- Information-set conditions making one complete history a lawful standard
subgame root. The definition is entirely payoff-free. -/
structure IsLawfulSubgameRoot
    (G : ControlledObservedGame N)
    (root : G.base.History) : Prop where
  /-- A proper player-controlled root has singleton decision information. -/
  root_information_singleton :
    root ≠ Arena.HistoryFrom.nil G.base.toArena G.base.init →
      ∀ (i : N) (hmover : G.base.mover root.1 = some i)
      (hdecision : G.base.toArena.IsDecision root.1)
      (other : G.base.History)
      (hother : G.base.mover other.1 = some i)
      (hother_decision : G.base.toArena.IsDecision other.1),
      G.infoAt root i hmover hdecision =
          G.infoAt other i hother hother_decision →
        other = root
  /-- Every information set encountered after entry stays wholly inside the
  continuation. -/
  information_closed :
    ∀ current, G.IsContinuationOf root current →
      ∀ (i : N) (hmover : G.base.mover current.1 = some i)
        (hdecision : G.base.toArena.IsDecision current.1)
        (other : G.base.History)
        (hother : G.base.mover other.1 = some i)
        (hother_decision : G.base.toArena.IsDecision other.1),
        G.infoAt current i hmover hdecision =
            G.infoAt other i hother hother_decision →
          G.IsContinuationOf root other

/-- Bijective player relabeling preserves and reflects structural subgame
lawfulness.

The proof transports mover witnesses through the player equivalence. Arena
histories and continuation reachability are unchanged, while the dependent
information-state equalities are converted using the equivalence inverse and
proof irrelevance. -/
theorem isLawfulSubgameRoot_relabelPlayers_iff
    (G : ControlledObservedGame N)
    (e : M ≃ N) (root : G.base.History) :
    (G.relabelPlayers e).IsLawfulSubgameRoot root ↔
      G.IsLawfulSubgameRoot root := by
  constructor
  · intro h
    constructor
    · intro hproper i hmover hnonterminal other hother
        hother_nonterminal hinfo
      have hmover' :
          (G.relabelPlayers e).base.mover root.1 =
            some (e.symm i) := by
        simp [hmover]
      have hother' :
          (G.relabelPlayers e).base.mover other.1 =
            some (e.symm i) := by
        simp [hother]
      apply h.root_information_singleton hproper
        (e.symm i) hmover' hnonterminal other hother'
        hother_nonterminal
      change
        G.infoAt root (e (e.symm i)) _ _ =
          G.infoAt other (e (e.symm i)) _ _
      convert hinfo using 1
      · exact congrArg G.InfoState (e.apply_symm_apply i)
      · congr
        · exact e.apply_symm_apply i
        · apply proof_irrel_heq
      · congr
        · exact e.apply_symm_apply i
        · apply proof_irrel_heq
    · intro current hcurrent i hmover hnonterminal other hother
        hother_nonterminal hinfo
      have hmover' :
          (G.relabelPlayers e).base.mover current.1 =
            some (e.symm i) := by
        simp [hmover]
      have hother' :
          (G.relabelPlayers e).base.mover other.1 =
            some (e.symm i) := by
        simp [hother]
      apply h.information_closed current hcurrent
        (e.symm i) hmover' hnonterminal other hother'
        hother_nonterminal
      change
        G.infoAt current (e (e.symm i)) _ _ =
          G.infoAt other (e (e.symm i)) _ _
      convert hinfo using 1
      · exact congrArg G.InfoState (e.apply_symm_apply i)
      · congr
        · exact e.apply_symm_apply i
        · apply proof_irrel_heq
      · congr
        · exact e.apply_symm_apply i
        · apply proof_irrel_heq
  · intro h
    constructor
    · intro hproper i hmover hnonterminal other hother
        hother_nonterminal hinfo
      have hmover' : G.base.mover root.1 = some (e i) := by
        have mapped := congrArg (Option.map e) hmover
        simpa using mapped
      have hother' : G.base.mover other.1 = some (e i) := by
        have mapped := congrArg (Option.map e) hother
        simpa using mapped
      apply h.root_information_singleton hproper
        (e i) hmover' hnonterminal other hother'
        hother_nonterminal
      simpa using hinfo
    · intro current hcurrent i hmover hnonterminal other hother
        hother_nonterminal hinfo
      have hmover' : G.base.mover current.1 = some (e i) := by
        have mapped := congrArg (Option.map e) hmover
        simpa using mapped
      have hother' : G.base.mover other.1 = some (e i) := by
        have mapped := congrArg (Option.map e) hother
        simpa using mapped
      apply h.information_closed current hcurrent
        (e i) hmover' hnonterminal other hother'
        hother_nonterminal
      simpa using hinfo

/-- An explicit selection of payoff-free lawful subgame roots. -/
structure SubgameSystem (G : ControlledObservedGame N) where
  /-- Selected roots. -/
  IsRoot : G.base.History → Prop
  /-- The whole-game root is selected. -/
  init_isRoot :
    IsRoot (Arena.HistoryFrom.nil G.base.toArena G.base.init)
  /-- Every selected root is structurally lawful. -/
  lawful :
    ∀ root, IsRoot root → G.IsLawfulSubgameRoot root

namespace SubgameSystem

/-- Extract structural lawfulness of a selected root. -/
def isLawful (system : G.SubgameSystem)
    {root : G.base.History}
    (hroot : system.IsRoot root) :
    G.IsLawfulSubgameRoot root :=
  system.lawful root hroot

/-- Transport a selected lawful system through a bijective player rename. -/
def relabelPlayers
    (system : G.SubgameSystem)
    (e : M ≃ N) :
    (G.relabelPlayers e).SubgameSystem where
  IsRoot := system.IsRoot
  init_isRoot := system.init_isRoot
  lawful := by
    intro root hroot
    exact
      (isLawfulSubgameRoot_relabelPlayers_iff G e root).2
        (system.isLawful hroot)

/-- Visibility of every lawful-system root in an external root
presentation. -/
def IsVisibleIn (system : G.SubgameSystem)
    (roots : G.ContinuationRootPresentation) : Prop :=
  ∀ root, system.IsRoot root → roots.IsRoot root

/-- Derived accessor for the proper-root singleton condition. -/
theorem root_information_singleton
    (system : G.SubgameSystem)
    (root : G.base.History)
    (hroot : system.IsRoot root)
    (hproper :
      root ≠ Arena.HistoryFrom.nil G.base.toArena G.base.init) :
    ∀ (i : N) (hmover : G.base.mover root.1 = some i)
      (hdecision : G.base.toArena.IsDecision root.1)
      (other : G.base.History)
      (hother : G.base.mover other.1 = some i)
      (hother_decision : G.base.toArena.IsDecision other.1),
      G.infoAt root i hmover hdecision =
          G.infoAt other i hother hother_decision →
        other = root :=
  (system.isLawful hroot).root_information_singleton hproper

/-- Derived accessor for continuation information-set closure. -/
theorem information_closed
    (system : G.SubgameSystem)
    (root : G.base.History)
    (hroot : system.IsRoot root) :
    ∀ current, G.IsContinuationOf root current →
      ∀ (i : N) (hmover : G.base.mover current.1 = some i)
        (hdecision : G.base.toArena.IsDecision current.1)
        (other : G.base.History)
        (hother : G.base.mover other.1 = some i)
        (hother_decision : G.base.toArena.IsDecision other.1),
        G.infoAt current i hmover hdecision =
            G.infoAt other i hother hother_decision →
          G.IsContinuationOf root other :=
  (system.isLawful hroot).information_closed

end SubgameSystem

/-- The initial complete history is always a lawful payoff-free subgame
root. -/
theorem init_isLawfulSubgameRoot
    (G : ControlledObservedGame N) :
    G.IsLawfulSubgameRoot
      (Arena.HistoryFrom.nil G.base.toArena G.base.init) where
  root_information_singleton := by
    intro hproper
    exact (hproper rfl).elim
  information_closed := by
    intro _current _hcurrent i _hmover _hnonterminal
      other _hother _hother_nonterminal _hsame
    exact other.2.reachableInUnfolding G.base.toArena G.base.init

/-- The smallest payoff-free lawful subgame system selects only the initial
history. -/
def SubgameSystem.initialOnly
    (G : ControlledObservedGame N) :
    G.SubgameSystem where
  IsRoot := fun root =>
    root = Arena.HistoryFrom.nil G.base.toArena G.base.init
  init_isRoot := rfl
  lawful := by
    intro root hroot
    subst root
    exact G.init_isLawfulSubgameRoot

@[simp]
theorem SubgameSystem.initialOnly_isRoot_iff
    (G : ControlledObservedGame N)
    (root : G.base.History) :
    (SubgameSystem.initialOnly G).IsRoot root ↔
      root = Arena.HistoryFrom.nil G.base.toArena G.base.init :=
  Iff.rfl

/-- A complete payoff-free standard-subgame system selects every
structurally lawful root. -/
structure CompleteSubgameSystem
    (G : ControlledObservedGame N)
    extends G.SubgameSystem where
  /-- Converse coverage of every structurally lawful root. -/
  complete :
    ∀ root, G.IsLawfulSubgameRoot root →
      toSubgameSystem.IsRoot root

namespace CompleteSubgameSystem

/-- A complete system selects exactly the structurally lawful roots. -/
theorem isRoot_iff_isLawful
    (system : G.CompleteSubgameSystem)
    (root : G.base.History) :
    system.toSubgameSystem.IsRoot root ↔
      G.IsLawfulSubgameRoot root :=
  ⟨system.toSubgameSystem.isLawful, system.complete root⟩

/-- Transport a complete lawful system through a bijective player rename. -/
def relabelPlayers
    (system : G.CompleteSubgameSystem)
    (e : M ≃ N) :
    (G.relabelPlayers e).CompleteSubgameSystem where
  toSubgameSystem :=
    system.toSubgameSystem.relabelPlayers e
  complete := by
    intro root hroot
    exact
      system.complete root
        ((isLawfulSubgameRoot_relabelPlayers_iff G e root).1 hroot)

/-- Canonical complete payoff-free standard-subgame system. -/
def canonical
    (G : ControlledObservedGame N) :
    G.CompleteSubgameSystem where
  IsRoot := G.IsLawfulSubgameRoot
  init_isRoot := G.init_isLawfulSubgameRoot
  lawful := fun _root hroot => hroot
  complete := fun _root hroot => hroot

end CompleteSubgameSystem

end ExtensiveGame.ControlledObservedGame
