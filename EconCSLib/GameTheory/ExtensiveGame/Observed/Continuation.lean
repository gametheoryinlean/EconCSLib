/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.Continuation.Iso
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation

Compile observed extensive games into representation-neutral continuation
semantics.

The structural observed-EFG layer remembers complete histories, observations,
public states, decision information, chance kernels, and
presentation-designated continuation roots. The `ContinuationGameForm` layer
remembers only the strategic data needed to state Nash optimality on
caller-declared roots: one shared complete strategy space, a root predicate,
and the outcome generated from every root. It cannot certify standard
subgames without a representation-aware adapter.

This module connects the two layers for:

* bounded no-chance pure continuation semantics;
* bounded chance-aware behavioral continuation semantics;
* strict observed-EFG isomorphisms;
* one-way information refinements.

The adapters expose why equilibrium proofs need not be repeated for every EFG
representation. Exact history/payoff naturality supplies the evaluator square;
root preservation supplies the declared-root map; the generic
`ContinuationGameForm` theorems then transfer Nash on
presentation-designated continuations. Information refinements reflect Nash
on presentation-designated continuations by default and become two-way
exactly when their strategy lift is surjective. Strict isomorphisms supply
both surjectivities automatically.

## Public-entry policy

Downstream strict-isomorphism clients should use the canonical relation-local
theorems `ObservedGame.Iso.isPureNashOnRootsAtFuel_iff` and
`ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff`. The
private route regressions in this module check that compilation to
`ContinuationGameForm` recovers the canonical result, but they are not a
second public entry point.

## Main definitions

* `ObservedGame.pureContinuationFamilyOnRoots`.
* `ObservedChanceGame.behavioralContinuationFamily`.
* `ObservedGame.Iso.pureContinuationFamilyIso`.
* `ObservedGame.InformationRefinement.pureContinuationFamilyHom`.
* `ObservedGame.InformationRefinement.pureContinuationFamilySimulation`.
* `ObservedChanceGame.Iso.behavioralContinuationFamilyIso`.
* `ObservedChanceGame.InformationRefinement.behavioralContinuationFamilyHom`.
* `ObservedChanceGame.InformationRefinement.behavioralContinuationFamilySimulation`.

## Main results

* `isPureNashOnRootsAtFuel_iff_continuationFamily`.
* `isBehavioralNashOnRootsAtFuel_iff_continuationFamily`.
* the strict-iso adapters inherit generic two-way Nash on presentation-designated continuations transfer;
* the refinement adapters inherit generic Nash on presentation-designated continuations reflection and conditional
  two-way transfer;
* private route regressions verify the continuation-family derivations without
  adding competing downstream entry points.
-/

namespace ExtensiveGame

universe uV

/-! ### Bounded pure continuation semantics -/

namespace ObservedGame

variable {N U : Type*}

/-- The bounded pure continuation family on a separately supplied root
presentation. -/
def pureContinuationFamilyOnRoots
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (roots : G.RootPresentation)
    (hNoChance : G.base.NoChanceOnHistories)
    (fuel : ℕ) :
    ContinuationGameForm N where
  Strategy := G.PureStrategy
  Root := G.base.toArena.HistoryFrom G.base.init
  IsDeclaredRoot := roots.IsRoot
  Outcome := Option (N → U)
  outcome := fun current profile =>
    G.stoppedPayoffFrom profile hNoChance current fuel

/-- Fixing a root in the pure continuation family recovers the existing
bounded continuation game form definitionally. -/
theorem pureContinuationFamilyOnRoots_toGameForm
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (roots : G.RootPresentation)
    (hNoChance : G.base.NoChanceOnHistories)
    (fuel : ℕ)
    (current :
      G.base.toArena.HistoryFrom G.base.init) :
    (G.pureContinuationFamilyOnRoots
      roots hNoChance fuel).toGameForm current =
      G.continuationGameForm
        hNoChance current fuel :=
  rfl

/-- The existing bounded pure Nash on presentation-designated continuations predicate is exactly the
representation-neutral continuation-family predicate. -/
theorem isPureNashOnRootsAtFuel_iff_continuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (roots : G.RootPresentation)
    (hNoChance : G.base.NoChanceOnHistories)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ) :
    G.IsPureNashOnRootsAtFuel
        hNoChance roots utility profile fuel ↔
      (G.pureContinuationFamilyOnRoots
        roots hNoChance fuel).IsNashOnRoots
          (fun _ => utility) profile :=
  Iff.rfl

namespace Iso

variable {G H : ObservedGame N U}

/-- A strict observed-EFG isomorphism induces an isomorphism of the complete
bounded pure continuation families, not merely separate isomorphisms at
individual roots. -/
def pureContinuationFamilyIso
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
    (fuel : ℕ) :
    (G.pureContinuationFamilyOnRoots
      sourceRoots hNoChanceG fuel).Iso
      (H.pureContinuationFamilyOnRoots
        targetRoots hNoChanceH fuel) where
  rootEquiv :=
    e.historyIso.stateEquiv
  strategyEquiv :=
    e.strategyEquiv
  outcomeEquiv :=
    Equiv.refl _
  map_declaredRoot := hroots
  map_outcome := by
    intro current profile
    exact
      (e.map_stoppedPayoffFrom
        profile hNoChanceG hNoChanceH
        current fuel).symm

/-- The pure continuation-family isomorphism preserves a common
root-independent outcome utility. -/
theorem pureContinuationFamilyIso_utilityCompatible
    {V : Type uV}
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
    (e.pureContinuationFamilyIso
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
      ).toHom.UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro root outcome i
  rfl

/-- Route-regression theorem: strict observed-EFG pure Nash on presentation-designated continuations transfer is an
instance of the representation-neutral continuation-family theorem.

Downstream code should use
`ObservedGame.Iso.isPureNashOnRootsAtFuel_iff`; this independently proved
variant is retained to test coherence of the continuation adapter. -/
private theorem isPureNashOnRootsAtFuel_iff_viaContinuationFamily
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
    (profile : G.PureProfile)
    (fuel : ℕ) :
    G.IsPureNashOnRootsAtFuel
        hNoChanceG sourceRoots utility profile fuel ↔
      H.IsPureNashOnRootsAtFuel
        hNoChanceH targetRoots utility
        (e.mapProfile profile) fuel := by
  change
    (G.pureContinuationFamilyOnRoots
      sourceRoots hNoChanceG fuel).IsNashOnRoots
        (fun _ => utility) profile ↔
      (H.pureContinuationFamilyOnRoots
        targetRoots hNoChanceH fuel).IsNashOnRoots
          (fun _ => utility)
          ((e.pureContinuationFamilyIso
            sourceRoots targetRoots hroots
            hNoChanceG hNoChanceH fuel
            ).mapProfile profile)
  exact
    (e.pureContinuationFamilyIso
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
      ).isNashOnRoots_iff
        (e.pureContinuationFamilyIso_utilityCompatible
          sourceRoots targetRoots hroots
          hNoChanceG hNoChanceH utility fuel)
        profile

end Iso

namespace InformationRefinement

variable {G H : ObservedGame N U}

/-- An observed information refinement induces one semantic morphism between
the complete bounded pure continuation families. -/
def pureContinuationFamilyHom
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (fuel : ℕ) :
    (G.pureContinuationFamilyOnRoots
      sourceRoots hNoChanceG fuel).Hom
      (H.pureContinuationFamilyOnRoots
        targetRoots hNoChanceH fuel) where
  rootMap :=
    r.historyIso.stateEquiv
  strategyMap :=
    r.mapStrategy
  outcomeMap :=
    id
  map_declaredRoot := fun current => (hroots current).mp
  map_outcome := by
    intro current profile
    exact
      (r.map_stoppedPayoffFrom
        profile hNoChanceG hNoChanceH
        current fuel).symm

/-- A pure refinement morphism preserves a common root-independent utility. -/
theorem pureContinuationFamilyHom_utilityCompatible
    {V : Type uV}
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (utility : Option (N → U) → N → V)
    (fuel : ℕ) :
    (r.pureContinuationFamilyHom
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
      ).UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro root outcome i
  rfl

/-- History equivalence and exact designated-root correspondence make every
pure refinement morphism surjective on declared continuation roots. -/
theorem pureContinuationFamilyHom_declaredRootSurjective
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (fuel : ℕ) :
    (r.pureContinuationFamilyHom
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
      ).DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  let sourceRoot :=
    r.historyIso.stateEquiv.symm
      targetRoot
  refine
    ⟨sourceRoot, ?_, ?_⟩
  · exact
      (hroots sourceRoot).mpr
        (by
          simpa [sourceRoot] using
            htargetRoot)
  · exact
      r.historyIso.stateEquiv.apply_symm_apply
        targetRoot

/-- Exact designated-root correspondence makes the pure refinement morphism
reflect declared-root membership along its root map. -/
theorem pureContinuationFamilyHom_declaredRootReflecting
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (fuel : ℕ) :
    (r.pureContinuationFamilyHom
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
      ).DeclaredRootReflecting := by
  intro sourceRoot htargetRoot
  exact
    (hroots sourceRoot).mpr
      htargetRoot

/-- The functional pure refinement adapter, regarded uniformly as a
relational-root continuation simulation.

This form composes directly with weak/stuttering compiler simulations. -/
def pureContinuationFamilySimulation
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (fuel : ℕ) :
    (G.pureContinuationFamilyOnRoots
      sourceRoots hNoChanceG fuel).Simulation
      (H.pureContinuationFamilyOnRoots
        targetRoots hNoChanceH fuel) :=
  (r.pureContinuationFamilyHom
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
    ).toSimulation
      (r.pureContinuationFamilyHom_declaredRootReflecting
        sourceRoots targetRoots hroots
        hNoChanceG hNoChanceH fuel)

/-- The pure refinement graph simulation covers all admissible source roots. -/
theorem pureContinuationFamilySimulation_sourceRootTotal
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (fuel : ℕ) :
    (r.pureContinuationFamilySimulation
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
      ).SourceRootTotal :=
  (r.pureContinuationFamilyHom
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
    ).toSimulation_sourceRootTotal _

/-- The pure refinement graph simulation covers all admissible target roots. -/
theorem pureContinuationFamilySimulation_targetRootTotal
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (fuel : ℕ) :
    (r.pureContinuationFamilySimulation
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
      ).TargetRootTotal :=
  (r.pureContinuationFamilyHom
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
    ).toSimulation_targetRootTotal _
      (r.pureContinuationFamilyHom_declaredRootSurjective
        sourceRoots targetRoots hroots
        hNoChanceG hNoChanceH fuel)

/-- The pure continuation-family morphism is strategy-surjective precisely
under the refinement's explicit deviation-lifting hypothesis. -/
theorem pureContinuationFamilyHom_strategySurjective
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (fuel : ℕ)
    (hsurjective : r.StrategySurjective) :
    (r.pureContinuationFamilyHom
      sourceRoots targetRoots hroots
      hNoChanceG hNoChanceH fuel
      ).StrategySurjective := by
  intro i targetStrategy
  exact hsurjective i targetStrategy

end InformationRefinement

end ObservedGame

/-! ### Bounded behavioral continuation semantics -/

namespace ObservedChanceGame

variable {N U : Type*}

/-- The bounded behavioral continuation family on a separately supplied root
presentation. -/
def behavioralContinuationFamilyOnRoots
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    ContinuationGameForm N where
  Strategy := G.observed.BehavioralStrategy
  Root :=
    G.observed.base.toArena.HistoryFrom
      G.observed.base.init
  IsDeclaredRoot := roots.IsRoot
  Outcome := FiniteLaw (Option (N → U))
  outcome := fun current profile =>
    G.behavioralStoppedPayoffLawFrom profile current fuel

/-- Fixing a root in the behavioral continuation family recovers the existing
bounded behavioral continuation game form definitionally. -/
theorem behavioralContinuationFamilyOnRoots_toGameForm
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (fuel : ℕ)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init) :
    (G.behavioralContinuationFamilyOnRoots
      roots fuel).toGameForm current =
      G.behavioralContinuationGameForm
        current fuel :=
  rfl

/-- The existing bounded behavioral Nash on presentation-designated continuations predicate is exactly the
representation-neutral continuation-family predicate. -/
theorem isBehavioralNashOnRootsAtFuel_iff_continuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    G.IsBehavioralNashOnRootsAtFuel
        roots utility profile fuel ↔
      (G.behavioralContinuationFamilyOnRoots
        roots fuel).IsNashOnRoots
          (fun _ => utility) profile :=
  Iff.rfl

namespace Iso

variable {G H : ObservedChanceGame N U}

/-- A strict observed chance-EFG isomorphism induces an isomorphism of the
complete bounded behavioral continuation families. -/
def behavioralContinuationFamilyIso
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      e.observedIso.PreservesRootPresentations
        sourceRoots targetRoots)
    (fuel : ℕ) :
    (G.behavioralContinuationFamilyOnRoots
      sourceRoots fuel).Iso
      (H.behavioralContinuationFamilyOnRoots
        targetRoots fuel) where
  rootEquiv :=
    e.observedIso.historyIso.stateEquiv
  strategyEquiv :=
    e.observedIso.behavioralStrategyEquiv
  outcomeEquiv :=
    Equiv.refl _
  map_declaredRoot := hroots
  map_outcome := by
    intro current profile
    exact
      (e.map_behavioralStoppedPayoffLawFrom
        profile current fuel).symm

/-- The behavioral continuation-family isomorphism preserves a common
root-independent functional on payoff laws. -/
theorem behavioralContinuationFamilyIso_utilityCompatible
    {V : Type uV}
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      e.observedIso.PreservesRootPresentations
        sourceRoots targetRoots)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (fuel : ℕ) :
    (e.behavioralContinuationFamilyIso
      sourceRoots targetRoots hroots fuel).toHom.UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro root outcome i
  rfl

end Iso

namespace InformationRefinement

variable {G H : ObservedChanceGame N U}

/-- A chance-aware information refinement induces one semantic morphism
between the complete bounded behavioral continuation families. -/
def behavioralContinuationFamilyHom
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.PreservesRootPresentations
        sourceRoots targetRoots)
    (fuel : ℕ) :
    (G.behavioralContinuationFamilyOnRoots
      sourceRoots fuel).Hom
      (H.behavioralContinuationFamilyOnRoots
        targetRoots fuel) where
  rootMap :=
    r.observedRefinement.historyIso.stateEquiv
  strategyMap :=
    r.observedRefinement.mapBehavioralStrategy
  outcomeMap :=
    id
  map_declaredRoot :=
    fun current => (hroots current).mp
  map_outcome := by
    intro current profile
    exact
      (r.map_behavioralStoppedPayoffLawFrom
        profile current fuel).symm

/-- A behavioral refinement morphism preserves a common root-independent
functional on payoff laws. -/
theorem behavioralContinuationFamilyHom_utilityCompatible
    {V : Type uV}
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.PreservesRootPresentations
        sourceRoots targetRoots)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilyHom
      sourceRoots targetRoots hroots fuel).UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro root outcome i
  rfl

/-- Every behavioral refinement morphism is surjective on admissible
continuation roots because the strict history dynamics are equivalent. -/
theorem behavioralContinuationFamilyHom_declaredRootSurjective
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.PreservesRootPresentations
        sourceRoots targetRoots)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilyHom
      sourceRoots targetRoots hroots fuel).DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  let sourceRoot :=
    r.observedRefinement.historyIso.stateEquiv.symm
      targetRoot
  refine
    ⟨sourceRoot, ?_, ?_⟩
  · exact
      (hroots sourceRoot).mpr
        (by
          simpa [sourceRoot] using
            htargetRoot)
  · exact
      r.observedRefinement.historyIso.stateEquiv.apply_symm_apply
        targetRoot

/-- Exact designated-root correspondence makes the behavioral refinement
morphism reflect declared-root membership along its root map. -/
theorem behavioralContinuationFamilyHom_declaredRootReflecting
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.PreservesRootPresentations
        sourceRoots targetRoots)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilyHom
      sourceRoots targetRoots hroots fuel).DeclaredRootReflecting := by
  intro sourceRoot htargetRoot
  exact
    (hroots sourceRoot).mpr htargetRoot

/-- The functional behavioral refinement adapter, regarded uniformly as a
relational-root continuation simulation.

This is the semantic form used to compose an information refinement after a
weak/stuttering compiler bridge. -/
def behavioralContinuationFamilySimulation
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.PreservesRootPresentations
        sourceRoots targetRoots)
    (fuel : ℕ) :
    (G.behavioralContinuationFamilyOnRoots
      sourceRoots fuel).Simulation
      (H.behavioralContinuationFamilyOnRoots
        targetRoots fuel) :=
  (r.behavioralContinuationFamilyHom
      sourceRoots targetRoots hroots fuel).toSimulation
        (r.behavioralContinuationFamilyHom_declaredRootReflecting
          sourceRoots targetRoots hroots fuel)

/-- The behavioral refinement graph simulation covers every admissible source
root. -/
theorem behavioralContinuationFamilySimulation_sourceRootTotal
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.PreservesRootPresentations
        sourceRoots targetRoots)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilySimulation
      sourceRoots targetRoots hroots fuel).SourceRootTotal :=
  (r.behavioralContinuationFamilyHom
      sourceRoots targetRoots hroots fuel).toSimulation_sourceRootTotal _

/-- The behavioral refinement graph simulation covers every admissible target
root. -/
theorem behavioralContinuationFamilySimulation_targetRootTotal
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.PreservesRootPresentations
        sourceRoots targetRoots)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilySimulation
      sourceRoots targetRoots hroots fuel).TargetRootTotal :=
  (r.behavioralContinuationFamilyHom
      sourceRoots targetRoots hroots fuel).toSimulation_targetRootTotal _
        (r.behavioralContinuationFamilyHom_declaredRootSurjective
          sourceRoots targetRoots hroots fuel)

/-- Behavioral strategy lifting is surjective exactly under the explicit
deviation-lifting hypothesis of the information refinement. -/
theorem behavioralContinuationFamilyHom_strategySurjective
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.PreservesRootPresentations
        sourceRoots targetRoots)
    (fuel : ℕ)
    (hsurjective :
      r.observedRefinement.BehavioralStrategySurjective) :
    (r.behavioralContinuationFamilyHom
      sourceRoots targetRoots hroots fuel).StrategySurjective := by
  intro i targetStrategy
  exact hsurjective i targetStrategy

end InformationRefinement

end ObservedChanceGame

end ExtensiveGame
