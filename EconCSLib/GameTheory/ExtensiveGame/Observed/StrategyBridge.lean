/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.IndexedContinuation
import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.StrategyBridge

Uniform public navigation for pure, behavioral, and mixed strategy semantics.

The underlying strategy spaces and hypotheses are intentionally different.
This module does not identify them. Instead, `BoundedDesignatedNashBridge` packages the
one operation downstream clients use uniformly: map a profile and transfer the
corresponding bounded designated-continuation Nash predicate.

The `pureSemantics`, `behavioralSemantics`, and `mixedSemantics` adapters also
package every natural-number execution bound into the same arbitrary-index
continuation interface. Their `atIndex` views are definitionally the existing
continuation families, so no semantic theorem is duplicated.
-/

namespace ExtensiveGame

universe uV

/-- Uniform interface for a profile map that preserves and reflects one
bounded designated-continuation Nash predicate. -/
structure BoundedDesignatedNashBridge
    (SourceProfile TargetProfile : Type*)
    (SourceProperty : SourceProfile → Prop)
    (TargetProperty : TargetProfile → Prop) where
  /-- Map a source profile to its target representation. -/
  mapProfile : SourceProfile → TargetProfile
  /-- The mapped profile has the target designated-root Nash property exactly
  when the source profile has the source property. -/
  isNash_iff :
    ∀ profile,
      SourceProperty profile ↔
        TargetProperty (mapProfile profile)

namespace ObservedStrategyBridge

variable {N U : Type*}

/-! ### Strategy-mode adapters -/

/-- All natural-number bounded pure continuation semantics as one indexed
continuation family. -/
def pureSemantics
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (roots : G.RootPresentation)
    (hNoChance : G.base.NoChanceOnHistories) :
    IndexedContinuationGameForm N where
  Strategy := G.PureStrategy
  Horizon := ℕ
  Root := G.base.toArena.HistoryFrom G.base.init
  IsDeclaredRoot := roots.IsRoot
  Outcome := Option (N → U)
  outcome := fun fuel current profile =>
    G.stoppedPayoffFrom profile hNoChance current fuel

/-- Fixing a pure-semantics index recovers the established continuation
family definitionally. -/
theorem pureSemantics_atIndex
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (roots : G.RootPresentation)
    (hNoChance : G.base.NoChanceOnHistories) (fuel : ℕ) :
    (pureSemantics G roots hNoChance).atIndex fuel =
      G.pureContinuationFamilyOnRoots roots hNoChance fuel :=
  rfl

/-- All natural-number bounded behavioral continuation semantics as one
indexed continuation family. -/
def behavioralSemantics
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation) :
    IndexedContinuationGameForm N where
  Strategy := G.observed.BehavioralStrategy
  Horizon := ℕ
  Root :=
    G.observed.base.toArena.HistoryFrom
      G.observed.base.init
  IsDeclaredRoot := roots.IsRoot
  Outcome := FiniteLaw (Option (N → U))
  outcome := fun fuel current profile =>
    G.behavioralStoppedPayoffLawFrom profile current fuel

/-- Fixing a behavioral-semantics index recovers the established continuation
family definitionally. -/
theorem behavioralSemantics_atIndex
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    (behavioralSemantics G roots).atIndex fuel =
      G.behavioralContinuationFamilyOnRoots roots fuel :=
  rfl

/-- All natural-number bounded mixed continuation semantics as one indexed
continuation family. -/
def mixedSemantics
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation) :
    IndexedContinuationGameForm N where
  Strategy := G.observed.MixedStrategy
  Horizon := ℕ
  Root :=
    G.observed.base.toArena.HistoryFrom
      G.observed.base.init
  IsDeclaredRoot := roots.IsRoot
  Outcome := FiniteLaw (Option (N → U))
  outcome := fun fuel current profile =>
    G.mixedStoppedPayoffLawFrom profile current fuel

/-- Fixing a mixed-semantics index recovers the established continuation
family definitionally. -/
theorem mixedSemantics_atIndex
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    (mixedSemantics G roots).atIndex fuel =
      G.mixedContinuationFamilyOnRoots roots fuel :=
  rfl

/-! ### Strict representation adapters over every bound -/

/-- A strict observed-game isomorphism acts uniformly on the complete indexed
pure semantics, rather than requiring a new relation at each fuel. -/
def pureIso
    {G H : ObservedGame N U}
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories) :
    (pureSemantics G sourceRoots hNoChanceG).Iso
      (pureSemantics H targetRoots hNoChanceH) where
  horizonEquiv := Equiv.refl ℕ
  rootEquiv := e.historyIso.stateEquiv
  strategyEquiv := e.strategyEquiv
  outcomeEquiv := Equiv.refl _
  map_declaredRoot := hroots
  map_outcome := by
    intro fuel current profile
    exact
      (e.map_stoppedPayoffFrom
        profile hNoChanceG hNoChanceH current fuel).symm

/-- A strict chance-game isomorphism acts uniformly on the complete indexed
behavioral semantics. -/
def behavioralIso
    {G H : ObservedChanceGame N U}
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      e.observedIso.PreservesRootPresentations
        sourceRoots targetRoots) :
    (behavioralSemantics G sourceRoots).Iso
      (behavioralSemantics H targetRoots) where
  horizonEquiv := Equiv.refl ℕ
  rootEquiv := e.observedIso.historyIso.stateEquiv
  strategyEquiv := e.observedIso.behavioralStrategyEquiv
  outcomeEquiv := Equiv.refl _
  map_declaredRoot := hroots
  map_outcome := by
    intro fuel current profile
    exact
      (e.map_behavioralStoppedPayoffLawFrom
        profile current fuel).symm

/-- A strict chance-game isomorphism acts uniformly on the complete indexed
mixed semantics. -/
def mixedIso
    {G H : ObservedChanceGame N U}
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      e.observedIso.PreservesRootPresentations
        sourceRoots targetRoots) :
    (mixedSemantics G sourceRoots).Iso
      (mixedSemantics H targetRoots) where
  horizonEquiv := Equiv.refl ℕ
  rootEquiv := e.observedIso.historyIso.stateEquiv
  strategyEquiv := e.observedIso.mixedStrategyEquiv
  outcomeEquiv := Equiv.refl _
  map_declaredRoot := hroots
  map_outcome := by
    intro fuel current profile
    exact
      (e.map_mixedStoppedPayoffLawFrom
        profile current fuel).symm

/-! ### Uniform bounded designated-root Nash bridges -/

/-- Strict structural relabeling as a uniform pure-strategy
designated-root Nash bridge. -/
def pure
    {G H : ObservedGame N U}
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (utility : Option (N → U) → N → V)
    (fuel : ℕ) :
    BoundedDesignatedNashBridge
      G.PureProfile H.PureProfile
      (fun profile =>
        G.IsPureNashOnRootsAtFuel
          hNoChanceG sourceRoots utility profile fuel)
      (fun profile =>
        H.IsPureNashOnRootsAtFuel
          hNoChanceH targetRoots utility profile fuel) where
  mapProfile := e.mapProfile
  isNash_iff := fun profile =>
    e.isPureNashOnRootsAtFuel_iff
      hNoChanceG hNoChanceH sourceRoots targetRoots hroots
      utility profile fuel

/-- Strict chance-aware relabeling as a uniform behavioral-strategy
designated-root Nash bridge. -/
def behavioral
    {G H : ObservedChanceGame N U}
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      e.observedIso.PreservesRootPresentations
        sourceRoots targetRoots)
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (fuel : ℕ) :
    BoundedDesignatedNashBridge
      G.observed.BehavioralProfile
      H.observed.BehavioralProfile
      (fun profile =>
        G.IsBehavioralNashOnRootsAtFuel
          sourceRoots utility profile fuel)
      (fun profile =>
        H.IsBehavioralNashOnRootsAtFuel
          targetRoots utility profile fuel) where
  mapProfile := e.observedIso.mapBehavioralProfile
  isNash_iff := fun profile =>
    e.isBehavioralNashOnRootsAtFuel_iff
      sourceRoots targetRoots hroots utility profile fuel

/-- Strict chance-aware relabeling as a uniform mixed-strategy designated-root
Nash bridge. -/
def mixed
    {G H : ObservedChanceGame N U}
    {V : Type uV}
    [Fintype N] [LinearOrder N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      e.observedIso.PreservesRootPresentations
        sourceRoots targetRoots)
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (fuel : ℕ) :
    BoundedDesignatedNashBridge
      G.observed.MixedProfile
      H.observed.MixedProfile
      (fun profile =>
        G.IsMixedNashOnRootsAtFuel
          sourceRoots utility profile fuel)
      (fun profile =>
        H.IsMixedNashOnRootsAtFuel
          targetRoots utility profile fuel) where
  mapProfile := e.observedIso.mapMixedProfile
  isNash_iff := fun profile =>
    e.isMixedNashOnRootsAtFuel_iff
      sourceRoots targetRoots hroots utility profile fuel

/-- Constructive finite Kuhn equivalence as the same uniform designated-root
Nash bridge.

The map samples every behavioral information-state action independently into
a complete mixed contingent plan. The inverse realization remains
root-scoped, exactly as required by the finite Kuhn theorem. -/
def kuhn
    (G : ObservedChanceGame N U)
    {V : Type uV}
    [Fintype N] [LinearOrder N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i)
    (fuel : ℕ) :
    BoundedDesignatedNashBridge
      G.observed.BehavioralProfile
      G.observed.MixedProfile
      (fun profile =>
        G.IsBehavioralNashOnRootsAtFuel
          roots utility profile fuel)
      (fun profile =>
        G.IsMixedNashOnRootsAtFuel
          roots utility profile fuel) where
  mapProfile := h.behavioralToMixedProfile
  isNash_iff := fun profile =>
    G.isBehavioralNashOnRootsAtFuel_iff_mixed
      h roots utility hutility profile fuel

end ObservedStrategyBridge

end ExtensiveGame
