/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.Continuation.Core

/-!
# EconCSLib.GameTheory.GameForm.Continuation.Simulation

A relational continuation simulation compares every related pair of roots
using one global strategy map and one outcome map. Start with `Simulation`,
then its composition and root-coverage predicates, and finally the
Nash-on-declared-roots transfer theorems.

Keeping the correspondence relational lets weak operational simulations use
their actual related roots without choosing a preferred representative. Root
coverage and deviation coverage are explicit premises of the transfer result.
-/

universe uN uS uR uO uV

namespace ContinuationGameForm

variable {N : Type uN}

/-! ### Relational-root simulations -/

/-- A continuation-family simulation whose root correspondence is relational.

Weak/stuttering operational simulations generally do not provide a preferred
target history for each source macro state.  Requiring a root function would
therefore introduce an arbitrary choice.  `Simulation` keeps the same global
strategy and outcome maps as `Hom`, but evaluates their commuting square at
every related pair of continuation roots.

Admissible-root preservation is an iff on related roots.  Existence of related
roots in either direction is kept as a separate property because different
theorem-transfer directions require different coverage assumptions. -/
structure Simulation (G H : ContinuationGameForm N) where
  /-- Relation between source and target continuation roots. -/
  RootRel : G.Root → H.Root → Prop
  /-- Map each player's complete source strategy. -/
  strategyMap :
    (i : N) → G.Strategy i → H.Strategy i
  /-- Map source continuation outcomes. -/
  outcomeMap : G.Outcome → H.Outcome
  /-- Related roots agree on subgame admissibility. -/
  map_declaredRoot :
    ∀ (sourceRoot : G.Root) (targetRoot : H.Root),
      RootRel sourceRoot targetRoot →
        (G.IsDeclaredRoot sourceRoot ↔
          H.IsDeclaredRoot targetRoot)
  /-- Evaluation commutes at every related root pair. -/
  map_outcome :
    ∀ (sourceRoot : G.Root) (targetRoot : H.Root),
      RootRel sourceRoot targetRoot →
      ∀ profile : G.Profile,
        outcomeMap
            (G.outcome sourceRoot profile) =
          H.outcome targetRoot
            (fun i => strategyMap i (profile i))

namespace Simulation

variable {G H K : ContinuationGameForm N}

/-- Continuation simulations are equal when their root relations and
strategy/outcome maps agree. -/
@[ext]
theorem ext (S T : G.Simulation H)
    (hrel :
      ∀ sourceRoot targetRoot,
        S.RootRel sourceRoot targetRoot ↔
          T.RootRel sourceRoot targetRoot)
    (hstrategy : S.strategyMap = T.strategyMap)
    (houtcome : S.outcomeMap = T.outcomeMap) :
    S = T := by
  have hrelEq : S.RootRel = T.RootRel := by
    funext sourceRoot targetRoot
    exact propext (hrel sourceRoot targetRoot)
  cases S
  cases T
  cases hrelEq
  cases hstrategy
  cases houtcome
  rfl

/-- Map one shared complete profile through a simulation. -/
def mapProfile
    (S : G.Simulation H) (profile : G.Profile) :
    H.Profile :=
  fun i => S.strategyMap i (profile i)

@[simp]
theorem mapProfile_apply
    (S : G.Simulation H) (profile : G.Profile)
    (i : N) :
    S.mapProfile profile i =
      S.strategyMap i (profile i) :=
  rfl

/-- Every admissible source root has a related target root. -/
def SourceRootTotal (S : G.Simulation H) : Prop :=
  ∀ sourceRoot : G.Root,
    G.IsDeclaredRoot sourceRoot →
      ∃ targetRoot : H.Root,
        S.RootRel sourceRoot targetRoot

/-- Every admissible target root has a related source root. -/
def TargetRootTotal (S : G.Simulation H) : Prop :=
  ∀ targetRoot : H.Root,
    H.IsDeclaredRoot targetRoot →
      ∃ sourceRoot : G.Root,
        S.RootRel sourceRoot targetRoot

/-- Every target player strategy is represented by a source strategy. -/
def StrategySurjective
    (S : G.Simulation H) : Prop :=
  ∀ i : N,
    Function.Surjective (S.strategyMap i)

/-- Root-dependent utility interpretations agree at related roots and mapped
outcomes. -/
def UtilityCompatible
    {V : Type uV}
    (S : G.Simulation H)
    (sourceUtility :
      G.Root → G.Outcome → N → V)
    (targetUtility :
      H.Root → H.Outcome → N → V) : Prop :=
  ∀ (sourceRoot : G.Root)
    (targetRoot : H.Root),
    S.RootRel sourceRoot targetRoot →
    ∀ (outcome : G.Outcome) (i : N),
      targetUtility targetRoot
          (S.outcomeMap outcome) i =
        sourceUtility sourceRoot outcome i

/-- A related pair of roots induces an ordinary game-form morphism. -/
def atHom
    (S : G.Simulation H)
    (sourceRoot : G.Root)
    (targetRoot : H.Root)
    (hrelated :
      S.RootRel sourceRoot targetRoot) :
    (G.toGameForm sourceRoot).Hom
      (H.toGameForm targetRoot) where
  strategyMap := S.strategyMap
  outcomeMap := S.outcomeMap
  map_outcome :=
    S.map_outcome
      sourceRoot targetRoot hrelated

/-- Relational utility compatibility restricts to every related one-root
game-form morphism. -/
theorem atHom_utilityCompatible
    {V : Type uV}
    (S : G.Simulation H)
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (hutility :
      S.UtilityCompatible
        sourceUtility targetUtility)
    (sourceRoot : G.Root)
    (targetRoot : H.Root)
    (hrelated :
      S.RootRel sourceRoot targetRoot) :
    GameForm.Hom.UtilityCompatible
      (S.atHom sourceRoot targetRoot hrelated)
      (sourceUtility sourceRoot)
      (targetUtility targetRoot) := by
  intro outcome i
  exact
    hutility sourceRoot targetRoot
      hrelated outcome i

/-- Global strategy surjectivity restricts to every related one-root
morphism. -/
theorem atHom_strategySurjective
    (S : G.Simulation H)
    (hsurjective : S.StrategySurjective)
    (sourceRoot : G.Root)
    (targetRoot : H.Root)
    (hrelated :
      S.RootRel sourceRoot targetRoot) :
    (S.atHom sourceRoot targetRoot
      hrelated).StrategySurjective := by
  intro i targetStrategy
  exact hsurjective i targetStrategy

/-- Identity relational simulation. -/
def refl (G : ContinuationGameForm N) :
    G.Simulation G where
  RootRel := (· = ·)
  strategyMap := fun _ strategy => strategy
  outcomeMap := id
  map_declaredRoot := by
    intro sourceRoot targetRoot hroot
    subst targetRoot
    rfl
  map_outcome := by
    intro sourceRoot targetRoot hroot
    subst targetRoot
    intro profile
    rfl

/-- The identity simulation covers admissible roots in both directions. -/
theorem refl_sourceRootTotal
    (G : ContinuationGameForm N) :
    (refl G).SourceRootTotal := by
  intro sourceRoot hsourceRoot
  exact ⟨sourceRoot, rfl⟩

/-- The identity simulation covers admissible target roots. -/
theorem refl_targetRootTotal
    (G : ContinuationGameForm N) :
    (refl G).TargetRootTotal := by
  intro targetRoot htargetRoot
  exact ⟨targetRoot, rfl⟩

/-- Compose relational-root continuation simulations. -/
def trans
    (S : G.Simulation H)
    (T : H.Simulation K) :
    G.Simulation K where
  RootRel := fun sourceRoot targetRoot =>
    ∃ middleRoot : H.Root,
      S.RootRel sourceRoot middleRoot ∧
        T.RootRel middleRoot targetRoot
  strategyMap := fun i strategy =>
    T.strategyMap i (S.strategyMap i strategy)
  outcomeMap :=
    T.outcomeMap ∘ S.outcomeMap
  map_declaredRoot := by
    intro sourceRoot targetRoot hrelated
    obtain
        ⟨middleRoot, hsourceMiddle,
          hmiddleTarget⟩ :=
      hrelated
    exact
      (S.map_declaredRoot
        sourceRoot middleRoot
        hsourceMiddle).trans
        (T.map_declaredRoot
          middleRoot targetRoot
          hmiddleTarget)
  map_outcome := by
    intro sourceRoot targetRoot hrelated
      profile
    obtain
        ⟨middleRoot, hsourceMiddle,
          hmiddleTarget⟩ :=
      hrelated
    change
      T.outcomeMap
          (S.outcomeMap
            (G.outcome sourceRoot profile)) =
        K.outcome targetRoot
          (T.mapProfile (S.mapProfile profile))
    rw [S.map_outcome
      sourceRoot middleRoot hsourceMiddle]
    rw [T.map_outcome
      middleRoot targetRoot hmiddleTarget]
    rfl

/-- Mapping a profile through the identity simulation is a no-op. -/
@[simp]
theorem refl_mapProfile
    (G : ContinuationGameForm N) (profile : G.Profile) :
    (refl G).mapProfile profile = profile :=
  rfl

/-- Profile mapping is functorial under simulation composition. -/
@[simp]
theorem trans_mapProfile
    (S : G.Simulation H) (T : H.Simulation K)
    (profile : G.Profile) :
    (S.trans T).mapProfile profile =
      T.mapProfile (S.mapProfile profile) :=
  rfl

/-- The identity simulation is a left unit for relational composition. -/
@[simp]
theorem refl_trans (S : G.Simulation H) :
    (refl G).trans S = S := by
  apply Simulation.ext
  · intro sourceRoot targetRoot
    constructor
    · rintro ⟨middleRoot, rfl, hrelated⟩
      exact hrelated
    · intro hrelated
      exact ⟨sourceRoot, rfl, hrelated⟩
  · rfl
  · rfl

/-- The identity simulation is a right unit for relational composition. -/
@[simp]
theorem trans_refl (S : G.Simulation H) :
    S.trans (refl H) = S := by
  apply Simulation.ext
  · intro sourceRoot targetRoot
    constructor
    · rintro ⟨middleRoot, hrelated, rfl⟩
      exact hrelated
    · intro hrelated
      exact ⟨targetRoot, hrelated, rfl⟩
  · rfl
  · rfl

/-- Relational composition of continuation simulations is associative. -/
theorem trans_assoc {L : ContinuationGameForm N}
    (S : G.Simulation H) (T : H.Simulation K)
    (R : K.Simulation L) :
    (S.trans T).trans R = S.trans (T.trans R) := by
  apply Simulation.ext
  · intro sourceRoot targetRoot
    constructor
    · rintro ⟨rightRoot, ⟨middleRoot, hsource, hmiddle⟩, hright⟩
      exact ⟨middleRoot, hsource, rightRoot, hmiddle, hright⟩
    · rintro ⟨middleRoot, hsource, rightRoot, hmiddle, hright⟩
      exact ⟨rightRoot, ⟨middleRoot, hsource, hmiddle⟩, hright⟩
  · rfl
  · rfl

/-- Source-root coverage composes relationally. -/
theorem SourceRootTotal.trans
    {S : G.Simulation H}
    {T : H.Simulation K}
    (hS : S.SourceRootTotal)
    (hT : T.SourceRootTotal) :
    (S.trans T).SourceRootTotal := by
  intro sourceRoot hsourceRoot
  obtain ⟨middleRoot, hsourceMiddle⟩ :=
    hS sourceRoot hsourceRoot
  have hmiddleRoot :
      H.IsDeclaredRoot middleRoot :=
    (S.map_declaredRoot
      sourceRoot middleRoot
      hsourceMiddle).mp hsourceRoot
  obtain ⟨targetRoot, hmiddleTarget⟩ :=
    hT middleRoot hmiddleRoot
  exact
    ⟨targetRoot, middleRoot,
      hsourceMiddle, hmiddleTarget⟩

/-- Target-root coverage composes relationally. -/
theorem TargetRootTotal.trans
    {S : G.Simulation H}
    {T : H.Simulation K}
    (hS : S.TargetRootTotal)
    (hT : T.TargetRootTotal) :
    (S.trans T).TargetRootTotal := by
  intro targetRoot htargetRoot
  obtain ⟨middleRoot, hmiddleTarget⟩ :=
    hT targetRoot htargetRoot
  have hmiddleRoot :
      H.IsDeclaredRoot middleRoot :=
    (T.map_declaredRoot
      middleRoot targetRoot
      hmiddleTarget).mpr htargetRoot
  obtain ⟨sourceRoot, hsourceMiddle⟩ :=
    hS middleRoot hmiddleRoot
  exact
    ⟨sourceRoot, middleRoot,
      hsourceMiddle, hmiddleTarget⟩

/-- Strategy-surjective relational simulations compose. -/
theorem StrategySurjective.trans
    {S : G.Simulation H}
    {T : H.Simulation K}
    (hS : S.StrategySurjective)
    (hT : T.StrategySurjective) :
    (S.trans T).StrategySurjective := by
  intro i targetStrategy
  obtain ⟨middleStrategy, hmiddle⟩ :=
    hT i targetStrategy
  obtain ⟨sourceStrategy, hsource⟩ :=
    hS i middleStrategy
  refine ⟨sourceStrategy, ?_⟩
  change
    T.strategyMap i
        (S.strategyMap i sourceStrategy) =
      targetStrategy
  rw [hsource, hmiddle]

/-- Utility compatibility composes along relational roots. -/
theorem UtilityCompatible.trans
    {V : Type uV}
    {S : G.Simulation H}
    {T : H.Simulation K}
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {middleUtility :
      H.Root → H.Outcome → N → V}
    {targetUtility :
      K.Root → K.Outcome → N → V}
    (hS :
      S.UtilityCompatible
        sourceUtility middleUtility)
    (hT :
      T.UtilityCompatible
        middleUtility targetUtility) :
    (S.trans T).UtilityCompatible
      sourceUtility targetUtility := by
  intro sourceRoot targetRoot hrelated
    outcome i
  obtain
      ⟨middleRoot, hsourceMiddle,
        hmiddleTarget⟩ :=
    hrelated
  change
    targetUtility targetRoot
        (T.outcomeMap
          (S.outcomeMap outcome)) i =
      sourceUtility sourceRoot outcome i
  rw [hT middleRoot targetRoot
    hmiddleTarget
    (S.outcomeMap outcome) i]
  exact
    hS sourceRoot middleRoot
      hsourceMiddle outcome i

end Simulation

/-! ### Functional morphisms as graph simulations -/

namespace Hom

variable {G H : ContinuationGameForm N}

/-- Regard a continuation morphism that reflects admissible roots as a
relational-root simulation on the graph of its root map.

This conversion is the bridge between functional representation changes
(strict isomorphisms and information refinements) and genuinely relational
weak/stuttering compiler semantics. -/
def toSimulation
    (f : G.Hom H)
    (hreflect : f.DeclaredRootReflecting) :
    G.Simulation H where
  RootRel := fun sourceRoot targetRoot =>
    f.rootMap sourceRoot = targetRoot
  strategyMap := f.strategyMap
  outcomeMap := f.outcomeMap
  map_declaredRoot := by
    intro sourceRoot targetRoot hroot
    subst targetRoot
    constructor
    · exact f.map_declaredRoot sourceRoot
    · exact hreflect sourceRoot
  map_outcome := by
    intro sourceRoot targetRoot hroot profile
    subst targetRoot
    exact f.map_outcome sourceRoot profile

/-- The graph simulation maps profiles exactly as the original morphism. -/
@[simp]
theorem toSimulation_mapProfile
    (f : G.Hom H)
    (hreflect : f.DeclaredRootReflecting)
    (profile : G.Profile) :
    (f.toSimulation hreflect).mapProfile profile =
      f.mapProfile profile :=
  rfl

/-- Every admissible source root is covered by the graph simulation. -/
theorem toSimulation_sourceRootTotal
    (f : G.Hom H)
    (hreflect : f.DeclaredRootReflecting) :
    (f.toSimulation hreflect).SourceRootTotal := by
  intro sourceRoot hsourceRoot
  exact ⟨f.rootMap sourceRoot, rfl⟩

/-- Admissible-root surjectivity gives target-root coverage of the graph
simulation. -/
theorem toSimulation_targetRootTotal
    (f : G.Hom H)
    (hreflect : f.DeclaredRootReflecting)
    (hroot : f.DeclaredRootSurjective) :
    (f.toSimulation hreflect).TargetRootTotal := by
  intro targetRoot htargetRoot
  obtain
      ⟨sourceRoot, hsourceRoot, hmap⟩ :=
    hroot targetRoot htargetRoot
  exact ⟨sourceRoot, hmap⟩

/-- Strategy-surjectivity is unchanged by passage to the graph simulation. -/
theorem toSimulation_strategySurjective
    (f : G.Hom H)
    (hreflect : f.DeclaredRootReflecting)
    (hstrategy : f.StrategySurjective) :
    (f.toSimulation hreflect).StrategySurjective :=
  hstrategy

/-- Utility compatibility is unchanged by passage to the graph simulation. -/
theorem toSimulation_utilityCompatible
    {V : Type uV}
    (f : G.Hom H)
    (hreflect : f.DeclaredRootReflecting)
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (hutility :
      f.UtilityCompatible
        sourceUtility targetUtility) :
    (f.toSimulation hreflect).UtilityCompatible
      sourceUtility targetUtility := by
  intro sourceRoot targetRoot hroot
    outcome i
  subst targetRoot
  exact hutility sourceRoot outcome i

end Hom

/-! ### Generic Nash-on-declared-roots transfer through relational simulations -/

/-- Target Nash-on-declared-roots reflects to the source through a root-relational simulation
that covers every admissible source root. -/
theorem IsNashOnRoots.comapSimulation
    {V : Type uV} [DecidableEq N] [Preorder V]
    {G H : ContinuationGameForm N}
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (S : G.Simulation H)
    (hutility :
      S.UtilityCompatible
        sourceUtility targetUtility)
    (hsource : S.SourceRootTotal)
    {profile : G.Profile}
    (hNash :
      H.IsNashOnRoots targetUtility
        (S.mapProfile profile)) :
    G.IsNashOnRoots sourceUtility profile := by
  intro sourceRoot hsourceRoot
  obtain ⟨targetRoot, hrelated⟩ :=
    hsource sourceRoot hsourceRoot
  have htargetRoot :
      H.IsDeclaredRoot targetRoot :=
    (S.map_declaredRoot
      sourceRoot targetRoot hrelated).mp
        hsourceRoot
  exact
    (hNash targetRoot htargetRoot).comap
      (S.atHom
        sourceRoot targetRoot hrelated)
      (S.atHom_utilityCompatible
        hutility sourceRoot targetRoot
        hrelated)

/-- Source Nash-on-declared-roots maps to the target through a strategy-surjective simulation
that covers every admissible target root. -/
theorem IsNashOnRoots.mapSimulation_of_surjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    {G H : ContinuationGameForm N}
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (S : G.Simulation H)
    (hutility :
      S.UtilityCompatible
        sourceUtility targetUtility)
    (hstrategy : S.StrategySurjective)
    (htarget : S.TargetRootTotal)
    {profile : G.Profile}
    (hNash :
      G.IsNashOnRoots sourceUtility profile) :
    H.IsNashOnRoots targetUtility
      (S.mapProfile profile) := by
  intro targetRoot htargetRoot
  obtain ⟨sourceRoot, hrelated⟩ :=
    htarget targetRoot htargetRoot
  have hsourceRoot :
      G.IsDeclaredRoot sourceRoot :=
    (S.map_declaredRoot
      sourceRoot targetRoot hrelated).mpr
        htargetRoot
  exact
    (hNash sourceRoot hsourceRoot
      ).map_of_strategySurjective
        (S.atHom
          sourceRoot targetRoot hrelated)
        (S.atHom_utilityCompatible
          hutility sourceRoot targetRoot
          hrelated)
        (S.atHom_strategySurjective
          hstrategy sourceRoot targetRoot
          hrelated)

/-- A root-relational simulation preserves Nash-on-declared-roots in both directions when it
covers admissible roots on both sides and lifts every target strategy. -/
theorem Simulation.isNashOnRoots_iff_of_total
    {V : Type uV} [DecidableEq N] [Preorder V]
    {G H : ContinuationGameForm N}
    (S : G.Simulation H)
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (hutility :
      S.UtilityCompatible
        sourceUtility targetUtility)
    (hstrategy : S.StrategySurjective)
    (hsource : S.SourceRootTotal)
    (htarget : S.TargetRootTotal)
    (profile : G.Profile) :
    G.IsNashOnRoots sourceUtility profile ↔
      H.IsNashOnRoots targetUtility
        (S.mapProfile profile) := by
  constructor
  · exact fun hNash =>
      hNash.mapSimulation_of_surjective
        S hutility hstrategy htarget
  · exact fun hNash =>
      hNash.comapSimulation
        S hutility hsource


end ContinuationGameForm
