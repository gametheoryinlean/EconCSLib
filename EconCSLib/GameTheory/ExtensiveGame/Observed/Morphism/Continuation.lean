/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Operational

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Continuation

Bounded continuation forms and pure Nash transfer on
presentation-designated continuations through strict isomorphisms.
Subgame perfection on an explicit lawful system and complete standard SPE are
exposed separately.
-/

namespace ExtensiveGame.ObservedGame

universe uV

variable {N U : Type*}

/-! ### Continuation game forms and equilibrium layers -/

/-- The deterministic bounded continuation game form at an accumulated
history.

The outcome is optional because the general Arena layer permits infinite play:
`none` means that the supplied fuel ended before a terminal history was
reached. -/
def continuationGameForm
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) :
    GameForm N where
  Strategy := G.PureStrategy
  Outcome := Option (N → U)
  outcome profile :=
    G.stoppedPayoffFrom profile hNoChance current fuel

/-- Pure Nash equilibrium on every presentation-designated continuation for
bounded no-chance semantics.

The same complete contingent profile is required to be Nash in the
continuation game at every designated root. This predicate does not itself
assert that those roots form the standard subgames. The outcome utility is
explicit so callers decide how a fuel-exhausted `none` result is interpreted.
For finite games, choose a fuel bound known to reach a terminal node for every
profile and deviation. -/
def IsPureNashOnRootsAtFuel
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (roots : G.RootPresentation)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ) : Prop :=
  ∀ current : G.base.toArena.HistoryFrom G.base.init,
    roots.IsRoot current →
      (G.continuationGameForm hNoChance current fuel).IsNash
        utility profile

/-- Bounded pure subgame perfection on an explicit, possibly conservative,
lawful subgame system. -/
def IsPureSubgamePerfectOnAtFuel
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ) : Prop :=
  ∀ current : G.base.toArena.HistoryFrom G.base.init,
    system.IsRoot current →
      (G.continuationGameForm hNoChance current fuel).IsNash
        utility profile

/-- Bounded standard pure SPE on the complete system of all structurally
lawful subgame roots. -/
def IsPureStandardSubgamePerfectAtFuel
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ) : Prop :=
  G.IsPureSubgamePerfectOnAtFuel hNoChance
    system.toSubgameSystem utility profile fuel

namespace Iso

variable {G H : ObservedGame N U}

/-- Every strict observed-EFG isomorphism induces a strict game-form
isomorphism between corresponding bounded continuation games. -/
def continuationGameFormIso
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) :
    (G.continuationGameForm hNoChanceG current fuel).Iso
      (H.continuationGameForm hNoChanceH
        (e.historyIso.stateEquiv current) fuel) where
  strategyEquiv := e.strategyEquiv
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro profile
    exact
      (e.map_stoppedPayoffFrom profile hNoChanceG hNoChanceH
        current fuel).symm

/-- The continuation game-form isomorphism is compatible with the same
outcome-utility interpretation on both representations. -/
theorem continuationGameFormIso_utilityCompatible
    {V : Type uV}
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (utility : Option (N → U) → N → V)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) :
    GameForm.Iso.UtilityCompatible
      (e.continuationGameFormIso hNoChanceG hNoChanceH current fuel)
      utility utility := by
  intro outcome i
  rfl

/-- A strict structural observed-EFG isomorphism preserves bounded pure Nash
on explicitly corresponding root presentations in both directions.

This theorem uses all three pieces that plain strategic equivalence lacks:
profile/deviation equivalence, exact payoff preservation at every
continuation, and an iff correspondence of presentation-designated roots. -/
theorem isPureNashOnRootsAtFuel_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ) :
    G.IsPureNashOnRootsAtFuel hNoChanceG sourceRoots utility profile fuel ↔
      H.IsPureNashOnRootsAtFuel hNoChanceH targetRoots utility
        (e.mapProfile profile) fuel := by
  constructor
  · intro hspe targetRoot htargetRoot
    let sourceRoot :=
      e.historyIso.stateEquiv.symm targetRoot
    have hmap :
        e.historyIso.stateEquiv sourceRoot = targetRoot :=
      e.historyIso.stateEquiv.apply_symm_apply targetRoot
    have hsourceRoot : sourceRoots.IsRoot sourceRoot := by
      apply (hroots sourceRoot).mpr
      simpa [hmap] using htargetRoot
    have hsourceNash := hspe sourceRoot hsourceRoot
    have hmapped :=
      GameForm.Iso.isNash_iff
        (e.continuationGameFormIso hNoChanceG hNoChanceH sourceRoot fuel)
        (e.continuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot fuel)
        profile |>.mp hsourceNash
    change
      (H.continuationGameForm hNoChanceH
        (e.historyIso.stateEquiv sourceRoot) fuel).IsNash
          utility (e.mapProfile profile) at hmapped
    rw [hmap] at hmapped
    exact hmapped
  · intro hspe sourceRoot hsourceRoot
    have htargetRoot :
        targetRoots.IsRoot (e.historyIso.stateEquiv sourceRoot) :=
      (hroots sourceRoot).mp hsourceRoot
    have htargetNash :=
      hspe (e.historyIso.stateEquiv sourceRoot) htargetRoot
    exact
      GameForm.Iso.isNash_iff
        (e.continuationGameFormIso hNoChanceG hNoChanceH sourceRoot fuel)
        (e.continuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot fuel)
        profile |>.mpr htargetNash

end Iso

end ExtensiveGame.ObservedGame
