/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.Basic

/-!
# EconCSLib.GameTheory.GameForm.Continuation.Core

A continuation family shares complete strategies across caller-declared roots.
Read `ContinuationGameForm` and `IsNashOnRoots` first, then `Hom` and its
rootwise `GameForm` view. The transfer theorems state root coverage and
unilateral-deviation coverage where each direction needs them.

The root predicate carries the caller's interpretation. A representation-aware
client must identify lawful subgames before using these results as standard
subgame-perfect equilibrium theorems.
-/

universe uN uS uR uO uV

/-- A representation-neutral family of continuation game forms.

All roots share the same complete contingent strategy spaces and outcome type.
Only the evaluator changes with the continuation root. -/
structure ContinuationGameForm (N : Type uN) where
  /-- Complete contingent strategy space of each player. -/
  Strategy : N → Type uS
  /-- Candidate continuation roots. -/
  Root : Type uR
  /-- Caller-declared roots at which Nash optimality is tested.

  This representation-neutral layer cannot inspect histories or information
  sets and therefore cannot certify that the predicate describes standard
  proper subgames. -/
  IsDeclaredRoot : Root → Prop
  /-- Representation-neutral continuation outcome type. -/
  Outcome : Type uO
  /-- Evaluate a complete profile from a continuation root. -/
  outcome : Root → (∀ i, Strategy i) → Outcome

namespace ContinuationGameForm

variable {N : Type uN}

/-- The shared complete-profile type of a continuation family. -/
abbrev Profile (G : ContinuationGameForm N) :=
  ∀ i, G.Strategy i

/-- The ordinary game form obtained by fixing a continuation root. -/
def toGameForm (G : ContinuationGameForm N) (root : G.Root) :
    GameForm N where
  Strategy := G.Strategy
  Outcome := G.Outcome
  outcome := G.outcome root

/-- Nash equilibrium at every caller-declared root in a continuation family.

Utilities may depend on the root as well as the outcome.  Ordinary
root-independent terminal utilities are represented by a constant function in
the first argument.  Standard SPE is obtained only when a representation-aware
client supplies a lawfully certified proper-subgame root predicate. -/
def IsNashOnRoots
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ContinuationGameForm N)
    (utility : G.Root → G.Outcome → N → V)
    (profile : G.Profile) : Prop :=
  ∀ root : G.Root,
    G.IsDeclaredRoot root →
      (G.toGameForm root).IsNash
        (utility root) profile

/-! ### Morphisms -/

/-- A semantic morphism between continuation families.

The strategy map is global rather than root-dependent: a single mapped
complete profile must be used at every target continuation. -/
structure Hom (G H : ContinuationGameForm N) where
  /-- Map source continuation roots to target roots. -/
  rootMap : G.Root → H.Root
  /-- Map each player's complete source strategy. -/
  strategyMap : (i : N) → G.Strategy i → H.Strategy i
  /-- Map source continuation outcomes. -/
  outcomeMap : G.Outcome → H.Outcome
  /-- Every admissible source root maps to an admissible target root. -/
  map_declaredRoot :
    ∀ root : G.Root,
      G.IsDeclaredRoot root →
        H.IsDeclaredRoot (rootMap root)
  /-- Evaluation commutes at every continuation root. -/
  map_outcome :
    ∀ (root : G.Root) (profile : G.Profile),
      outcomeMap (G.outcome root profile) =
        H.outcome (rootMap root)
          (fun i => strategyMap i (profile i))

namespace Hom

variable {G H K : ContinuationGameForm N}

/-- Continuation morphisms are equal when their root, strategy, and outcome
maps are equal. -/
@[ext]
theorem ext (f g : G.Hom H)
    (hroot : f.rootMap = g.rootMap)
    (hstrategy : f.strategyMap = g.strategyMap)
    (houtcome : f.outcomeMap = g.outcomeMap) :
    f = g := by
  cases f
  cases g
  cases hroot
  cases hstrategy
  cases houtcome
  rfl

/-- Map one shared complete profile between continuation families. -/
def mapProfile (f : G.Hom H) (profile : G.Profile) :
    H.Profile :=
  fun i => f.strategyMap i (profile i)

@[simp]
theorem mapProfile_apply
    (f : G.Hom H) (profile : G.Profile) (i : N) :
    f.mapProfile profile i =
      f.strategyMap i (profile i) :=
  rfl

/-- The game-form morphism induced at one source continuation root. -/
def atHom (f : G.Hom H) (root : G.Root) :
    (G.toGameForm root).Hom
      (H.toGameForm (f.rootMap root)) where
  strategyMap := f.strategyMap
  outcomeMap := f.outcomeMap
  map_outcome := f.map_outcome root

/-- The induced one-root morphism uses the global profile map. -/
@[simp]
theorem atHom_mapProfile
    (f : G.Hom H) (root : G.Root)
    (profile : G.Profile) :
    (f.atHom root).mapProfile profile =
      f.mapProfile profile :=
  rfl

/-- Identity semantic morphism. -/
def refl (G : ContinuationGameForm N) : G.Hom G where
  rootMap := id
  strategyMap := fun _ strategy => strategy
  outcomeMap := id
  map_declaredRoot := by
    intro root hroot
    exact hroot
  map_outcome := by
    intro root profile
    rfl

/-- Compose semantic morphisms between continuation families. -/
def trans (f : G.Hom H) (g : H.Hom K) : G.Hom K where
  rootMap := g.rootMap ∘ f.rootMap
  strategyMap := fun i strategy =>
    g.strategyMap i (f.strategyMap i strategy)
  outcomeMap := g.outcomeMap ∘ f.outcomeMap
  map_declaredRoot := by
    intro root hroot
    exact
      g.map_declaredRoot (f.rootMap root)
        (f.map_declaredRoot root hroot)
  map_outcome := by
    intro root profile
    change
      g.outcomeMap
          (f.outcomeMap (G.outcome root profile)) =
        K.outcome
          (g.rootMap (f.rootMap root))
          (g.mapProfile (f.mapProfile profile))
    rw [f.map_outcome, g.map_outcome]
    rfl

/-- Mapping a profile through the identity continuation morphism is a no-op. -/
@[simp]
theorem refl_mapProfile
    (G : ContinuationGameForm N) (profile : G.Profile) :
    (refl G).mapProfile profile = profile :=
  rfl

/-- Profile mapping is functorial under morphism composition. -/
@[simp]
theorem trans_mapProfile
    (f : G.Hom H) (g : H.Hom K)
    (profile : G.Profile) :
    (f.trans g).mapProfile profile =
      g.mapProfile (f.mapProfile profile) :=
  rfl

/-- The identity continuation morphism is a left unit for composition. -/
@[simp]
theorem refl_trans (f : G.Hom H) :
    (refl G).trans f = f := by
  ext <;> rfl

/-- The identity continuation morphism is a right unit for composition. -/
@[simp]
theorem trans_refl (f : G.Hom H) :
    f.trans (refl H) = f := by
  ext <;> rfl

/-- Composition of continuation morphisms is associative. -/
theorem trans_assoc {L : ContinuationGameForm N}
    (f : G.Hom H) (g : H.Hom K) (h : K.Hom L) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext <;> rfl

/-- Root-dependent utilities commute with a continuation morphism. -/
def UtilityCompatible
    {V : Type uV}
    (f : G.Hom H)
    (sourceUtility :
      G.Root → G.Outcome → N → V)
    (targetUtility :
      H.Root → H.Outcome → N → V) : Prop :=
  ∀ (root : G.Root) (outcome : G.Outcome) (i : N),
    targetUtility
        (f.rootMap root) (f.outcomeMap outcome) i =
      sourceUtility root outcome i

/-- Every target player strategy is represented by a source strategy. -/
def StrategySurjective (f : G.Hom H) : Prop :=
  ∀ i : N,
    Function.Surjective (f.strategyMap i)

/-- At every admissible source continuation, every unilateral target
deviation from the mapped profile is represented by a source deviation with
exactly the same mapped outcome. -/
def OutcomeDeviationCompleteAt [DecidableEq N]
    (f : G.Hom H) (profile : G.Profile) : Prop :=
  ∀ (root : G.Root),
    G.IsDeclaredRoot root →
      (f.atHom root).OutcomeDeviationCompleteAt
        profile

/-- Rootwise semantic deviation completeness at every source profile. -/
def OutcomeDeviationComplete [DecidableEq N]
    (f : G.Hom H) : Prop :=
  ∀ profile : G.Profile,
    f.OutcomeDeviationCompleteAt profile

/-- Every admissible target root is the image of an admissible source root. -/
def DeclaredRootSurjective (f : G.Hom H) : Prop :=
  ∀ targetRoot : H.Root,
    H.IsDeclaredRoot targetRoot →
      ∃ sourceRoot : G.Root,
        G.IsDeclaredRoot sourceRoot ∧
          f.rootMap sourceRoot = targetRoot

/-- Admissible target roots in the image reflect to admissible source roots.

Together with `Hom.map_declaredRoot`, this says that admissibility is exact
along the graph of `rootMap`.  It is the additional condition needed to regard
a functional continuation morphism as a relational-root simulation. -/
def DeclaredRootReflecting (f : G.Hom H) : Prop :=
  ∀ sourceRoot : G.Root,
    H.IsDeclaredRoot (f.rootMap sourceRoot) →
      G.IsDeclaredRoot sourceRoot

/-- Utility compatibility restricts to every induced one-root game-form
morphism. -/
theorem atHom_utilityCompatible
    {V : Type uV}
    (f : G.Hom H)
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (hutility :
      f.UtilityCompatible sourceUtility targetUtility)
    (root : G.Root) :
    GameForm.Hom.UtilityCompatible
      (f.atHom root)
      (sourceUtility root)
      (targetUtility (f.rootMap root)) := by
  intro outcome i
  exact hutility root outcome i

/-- Global strategy lifting gives strategy lifting at every continuation. -/
theorem atHom_strategySurjective
    (f : G.Hom H)
    (hsurjective : f.StrategySurjective)
    (root : G.Root) :
    (f.atHom root).StrategySurjective := by
  intro i targetStrategy
  exact hsurjective i targetStrategy

/-- Literal strategy surjectivity implies rootwise semantic deviation
completeness at every profile. -/
theorem StrategySurjective.outcomeDeviationCompleteAt
    [DecidableEq N]
    {f : G.Hom H}
    (hsurjective : f.StrategySurjective)
    (profile : G.Profile) :
    f.OutcomeDeviationCompleteAt profile := by
  intro root hroot
  exact
    (f.atHom_strategySurjective
      hsurjective root).outcomeDeviationCompleteAt
      profile

/-- Literal strategy surjectivity implies global rootwise semantic deviation
completeness. -/
theorem StrategySurjective.outcomeDeviationComplete
    [DecidableEq N]
    {f : G.Hom H}
    (hsurjective : f.StrategySurjective) :
    f.OutcomeDeviationComplete :=
  fun profile =>
    hsurjective.outcomeDeviationCompleteAt profile

/-- Strategy-surjective continuation morphisms compose. -/
theorem StrategySurjective.trans
    {f : G.Hom H} {g : H.Hom K}
    (hf : f.StrategySurjective)
    (hg : g.StrategySurjective) :
    (f.trans g).StrategySurjective := by
  intro i targetStrategy
  obtain ⟨middleStrategy, hmiddle⟩ :=
    hg i targetStrategy
  obtain ⟨sourceStrategy, hsource⟩ :=
    hf i middleStrategy
  refine ⟨sourceStrategy, ?_⟩
  change
    g.strategyMap i
        (f.strategyMap i sourceStrategy) =
      targetStrategy
  rw [hsource, hmiddle]

/-- Rootwise semantic deviation completeness composes. -/
theorem OutcomeDeviationCompleteAt.trans
    [DecidableEq N]
    {f : G.Hom H} {g : H.Hom K}
    {profile : G.Profile}
    (hf : f.OutcomeDeviationCompleteAt profile)
    (hg :
      g.OutcomeDeviationCompleteAt
        (f.mapProfile profile)) :
    (f.trans g).OutcomeDeviationCompleteAt profile := by
  intro root hroot
  change
    ((f.atHom root).trans
      (g.atHom (f.rootMap root))
      ).OutcomeDeviationCompleteAt profile
  exact
    (hf root hroot).trans
      (hg (f.rootMap root)
        (f.map_declaredRoot root hroot))

/-- Globally rootwise deviation-complete continuation morphisms compose. -/
theorem OutcomeDeviationComplete.trans
    [DecidableEq N]
    {f : G.Hom H} {g : H.Hom K}
    (hf : f.OutcomeDeviationComplete)
    (hg : g.OutcomeDeviationComplete) :
    (f.trans g).OutcomeDeviationComplete := by
  intro profile
  exact
    (hf profile).trans
      (hg (f.mapProfile profile))

/-- Admissible-root-surjective continuation morphisms compose. -/
theorem DeclaredRootSurjective.trans
    {f : G.Hom H} {g : H.Hom K}
    (hf : f.DeclaredRootSurjective)
    (hg : g.DeclaredRootSurjective) :
    (f.trans g).DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  obtain
      ⟨middleRoot, hmiddleRoot, hmiddleMap⟩ :=
    hg targetRoot htargetRoot
  obtain
      ⟨sourceRoot, hsourceRoot, hsourceMap⟩ :=
    hf middleRoot hmiddleRoot
  refine
    ⟨sourceRoot, hsourceRoot, ?_⟩
  change
    g.rootMap (f.rootMap sourceRoot) =
      targetRoot
  rw [hsourceMap, hmiddleMap]

/-- Subgame-root reflection composes along continuation morphisms. -/
theorem DeclaredRootReflecting.trans
    {f : G.Hom H} {g : H.Hom K}
    (hf : f.DeclaredRootReflecting)
    (hg : g.DeclaredRootReflecting) :
    (f.trans g).DeclaredRootReflecting := by
  intro sourceRoot htargetRoot
  exact
    hf sourceRoot
      (hg (f.rootMap sourceRoot)
        htargetRoot)

/-- Utility-compatible continuation morphisms compose. -/
theorem UtilityCompatible.trans
    {V : Type uV}
    {f : G.Hom H} {g : H.Hom K}
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {middleUtility :
      H.Root → H.Outcome → N → V}
    {targetUtility :
      K.Root → K.Outcome → N → V}
    (hf :
      f.UtilityCompatible
        sourceUtility middleUtility)
    (hg :
      g.UtilityCompatible
        middleUtility targetUtility) :
    (f.trans g).UtilityCompatible
      sourceUtility targetUtility := by
  intro root outcome i
  change
    targetUtility
        (g.rootMap (f.rootMap root))
        (g.outcomeMap (f.outcomeMap outcome)) i =
      sourceUtility root outcome i
  rw [hg, hf]

end Hom

/-! ### Generic Nash-on-declared-roots transfer -/

/-- Nash-on-declared-roots of a mapped target profile reflects through every utility-compatible
continuation morphism.

No surjectivity is required: every source root and source deviation is tested
through its image in the target. -/
theorem IsNashOnRoots.comap
    {V : Type uV} [DecidableEq N] [Preorder V]
    {G H : ContinuationGameForm N}
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (f : G.Hom H)
    (hutility :
      f.UtilityCompatible
        sourceUtility targetUtility)
    {profile : G.Profile}
    (hNash :
      H.IsNashOnRoots targetUtility
        (f.mapProfile profile)) :
    G.IsNashOnRoots sourceUtility profile := by
  intro sourceRoot hsourceRoot
  have htargetNash :=
    hNash
      (f.rootMap sourceRoot)
      (f.map_declaredRoot
        sourceRoot hsourceRoot)
  exact
    htargetNash.comap
      (f.atHom sourceRoot)
      (f.atHom_utilityCompatible
        hutility sourceRoot)

/-- A source Nash-on-declared-roots maps forward when every target root lifts and every target
unilateral deviation at the corresponding source continuation is realized by
a source deviation with the same mapped outcome.

This replaces literal strategy surjectivity by the weaker, semantic condition
needed for realization-equivalent EFG strategy models. -/
theorem IsNashOnRoots.map_of_outcomeDeviationCompleteAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    {G H : ContinuationGameForm N}
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (f : G.Hom H)
    (hutility :
      f.UtilityCompatible
        sourceUtility targetUtility)
    {profile : G.Profile}
    (hdeviation :
      f.OutcomeDeviationCompleteAt profile)
    (hroot : f.DeclaredRootSurjective)
    (hNash :
      G.IsNashOnRoots sourceUtility profile) :
    H.IsNashOnRoots targetUtility
      (f.mapProfile profile) := by
  intro targetRoot htargetRoot
  obtain
      ⟨sourceRoot, hsourceRoot, hmapRoot⟩ :=
    hroot targetRoot htargetRoot
  subst targetRoot
  exact
    (hNash sourceRoot hsourceRoot
      ).map_of_outcomeDeviationCompleteAt
        (f.atHom sourceRoot)
        (f.atHom_utilityCompatible
          hutility sourceRoot)
        (hdeviation sourceRoot hsourceRoot)

/-- A source Nash-on-declared-roots maps forward when every target unilateral deviation and every
admissible target root lift to the source. -/
theorem IsNashOnRoots.map_of_surjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    {G H : ContinuationGameForm N}
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (f : G.Hom H)
    (hutility :
      f.UtilityCompatible
        sourceUtility targetUtility)
    (hstrategy : f.StrategySurjective)
    (hroot : f.DeclaredRootSurjective)
    {profile : G.Profile}
    (hNash :
      G.IsNashOnRoots sourceUtility profile) :
    H.IsNashOnRoots targetUtility
      (f.mapProfile profile) := by
  exact
    hNash.map_of_outcomeDeviationCompleteAt
      f hutility
      (hstrategy.outcomeDeviationCompleteAt
        profile)
      hroot

/-- Exact two-way Nash-on-declared-roots transfer under semantic deviation completeness at the
source profile and admissible-root coverage. -/
theorem Hom.isNashOnRoots_iff_of_outcomeDeviationCompleteAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    {G H : ContinuationGameForm N}
    (f : G.Hom H)
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (hutility :
      f.UtilityCompatible
        sourceUtility targetUtility)
    (hroot : f.DeclaredRootSurjective)
    (profile : G.Profile)
    (hdeviation :
      f.OutcomeDeviationCompleteAt profile) :
    G.IsNashOnRoots sourceUtility profile ↔
      H.IsNashOnRoots targetUtility
        (f.mapProfile profile) := by
  constructor
  · exact fun hNash =>
      hNash.map_of_outcomeDeviationCompleteAt
        f hutility hdeviation hroot
  · exact fun hNash =>
      hNash.comap f hutility

/-- A utility-compatible continuation morphism preserves Nash-on-declared-roots in both
directions exactly when the required strategy and admissible-root lifting data
are supplied. -/
theorem Hom.isNashOnRoots_iff_of_surjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    {G H : ContinuationGameForm N}
    (f : G.Hom H)
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (hutility :
      f.UtilityCompatible
        sourceUtility targetUtility)
    (hstrategy : f.StrategySurjective)
    (hroot : f.DeclaredRootSurjective)
    (profile : G.Profile) :
    G.IsNashOnRoots sourceUtility profile ↔
      H.IsNashOnRoots targetUtility
        (f.mapProfile profile) := by
  constructor
  · exact fun hNash =>
      hNash.map_of_surjective
        f hutility hstrategy hroot
  · exact fun hNash =>
      hNash.comap f hutility


end ContinuationGameForm
