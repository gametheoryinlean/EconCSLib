/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.Continuation.Iso

/-!
# EconCSLib.GameTheory.GameForm.IndexedContinuation

Horizon- and semantics-parametric continuation game forms.

`ContinuationGameForm` deliberately abstracts from histories and probability,
but a concrete evaluator is often additionally indexed by a horizon,
approximation level, discount parameter, or an explicit unbounded-semantics
marker. `IndexedContinuationGameForm` packages that index without fixing it to
`Nat`, and without fixing outcomes to `PMF`.

Fixing an index produces the existing `ContinuationGameForm`, so all generic
Nash and Nash-on-declared-roots transfer theorems are reused rather than duplicated. The index
may be `Nat` for bounded execution, `Unit` for a total/unbounded evaluator,
`WithTop Nat` for finite and limiting semantics, or any application-specific
type. The outcome may likewise be deterministic, a discrete PMF, a measure,
or another semantic object supplied by the client.
-/

universe uN uS uH uR uO uV

/-- A continuation-game family indexed by an arbitrary semantic horizon. -/
structure IndexedContinuationGameForm (N : Type uN) where
  /-- Complete contingent strategy space of each player. -/
  Strategy : N → Type uS
  /-- Index selecting a horizon or another semantic evaluator. -/
  Horizon : Type uH
  /-- Candidate continuation roots. -/
  Root : Type uR
  /-- Caller-declared roots at which Nash optimality is tested.  Lawfulness as
  standard proper subgames is a responsibility of the representation-aware
  client. -/
  IsDeclaredRoot : Root → Prop
  /-- Representation-neutral outcome type. -/
  Outcome : Type uO
  /-- Evaluate a profile at an index and continuation root. -/
  outcome : Horizon → Root → (∀ i, Strategy i) → Outcome

namespace IndexedContinuationGameForm

variable {N : Type uN}

/-- Complete profiles shared by every index and continuation root. -/
abbrev Profile (G : IndexedContinuationGameForm N) :=
  ∀ i, G.Strategy i

/-- Fix one semantic index and recover an ordinary continuation family. -/
def atIndex (G : IndexedContinuationGameForm N) (horizon : G.Horizon) :
    ContinuationGameForm N where
  Strategy := G.Strategy
  Root := G.Root
  IsDeclaredRoot := G.IsDeclaredRoot
  Outcome := G.Outcome
  outcome := G.outcome horizon

@[simp]
theorem atIndex_outcome
    (G : IndexedContinuationGameForm N)
    (horizon : G.Horizon) (root : G.Root) (profile : G.Profile) :
    (G.atIndex horizon).outcome root profile =
      G.outcome horizon root profile :=
  rfl

/-- Nash-on-declared-roots at one arbitrary semantic index. -/
def IsNashOnRootsAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : IndexedContinuationGameForm N)
    (utility : G.Root → G.Outcome → N → V)
    (horizon : G.Horizon) (profile : G.Profile) : Prop :=
  (G.atIndex horizon).IsNashOnRoots utility profile

/-- Nash-on-declared-roots simultaneously at every semantic index. -/
def IsNashOnRoots
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : IndexedContinuationGameForm N)
    (utility : G.Horizon → G.Root → G.Outcome → N → V)
    (profile : G.Profile) : Prop :=
  ∀ horizon, G.IsNashOnRootsAt (utility horizon) horizon profile

/-- A semantic morphism that acts uniformly at every source index. -/
structure Hom (G H : IndexedContinuationGameForm N) where
  /-- Map source semantic indices to target indices. -/
  horizonMap : G.Horizon → H.Horizon
  /-- Map source continuation roots to target roots. -/
  rootMap : G.Root → H.Root
  /-- Map each player's source strategies. -/
  strategyMap : (i : N) → G.Strategy i → H.Strategy i
  /-- Map source outcomes. -/
  outcomeMap : G.Outcome → H.Outcome
  /-- Admissible roots map to admissible roots. -/
  map_declaredRoot :
    ∀ root, G.IsDeclaredRoot root → H.IsDeclaredRoot (rootMap root)
  /-- Evaluation commutes at every index and root. -/
  map_outcome :
    ∀ (horizon : G.Horizon) (root : G.Root) (profile : G.Profile),
      outcomeMap (G.outcome horizon root profile) =
        H.outcome (horizonMap horizon) (rootMap root)
          (fun i => strategyMap i (profile i))

namespace Hom

variable {G H K : IndexedContinuationGameForm N}

/-- Indexed morphisms are determined by their four data maps. -/
@[ext]
theorem ext (f g : G.Hom H)
    (hhorizon : f.horizonMap = g.horizonMap)
    (hroot : f.rootMap = g.rootMap)
    (hstrategy : f.strategyMap = g.strategyMap)
    (houtcome : f.outcomeMap = g.outcomeMap) :
    f = g := by
  cases f
  cases g
  cases hhorizon
  cases hroot
  cases hstrategy
  cases houtcome
  rfl

/-- Map a profile once, uniformly across all indices and roots. -/
def mapProfile (f : G.Hom H) (profile : G.Profile) : H.Profile :=
  fun i => f.strategyMap i (profile i)

@[simp]
theorem mapProfile_apply
    (f : G.Hom H) (profile : G.Profile) (i : N) :
    f.mapProfile profile i = f.strategyMap i (profile i) :=
  rfl

/-- Identity indexed-continuation morphism. -/
def refl (G : IndexedContinuationGameForm N) : G.Hom G where
  horizonMap := id
  rootMap := id
  strategyMap := fun _ strategy => strategy
  outcomeMap := id
  map_declaredRoot := fun _ hroot => hroot
  map_outcome := by intros; rfl

/-- Compose indexed-continuation morphisms. -/
def trans (f : G.Hom H) (g : H.Hom K) : G.Hom K where
  horizonMap := g.horizonMap ∘ f.horizonMap
  rootMap := g.rootMap ∘ f.rootMap
  strategyMap := fun i strategy => g.strategyMap i (f.strategyMap i strategy)
  outcomeMap := g.outcomeMap ∘ f.outcomeMap
  map_declaredRoot := fun root hroot =>
    g.map_declaredRoot _ (f.map_declaredRoot root hroot)
  map_outcome := by
    intro horizon root profile
    calc
      g.outcomeMap (f.outcomeMap (G.outcome horizon root profile)) =
          g.outcomeMap
            (H.outcome (f.horizonMap horizon) (f.rootMap root)
              (f.mapProfile profile)) :=
        congrArg g.outcomeMap (f.map_outcome horizon root profile)
      _ =
          K.outcome
            (g.horizonMap (f.horizonMap horizon))
            (g.rootMap (f.rootMap root))
            (g.mapProfile (f.mapProfile profile)) :=
        g.map_outcome
          (f.horizonMap horizon) (f.rootMap root)
          (f.mapProfile profile)

@[simp]
theorem refl_mapProfile
    (G : IndexedContinuationGameForm N) (profile : G.Profile) :
    (refl G).mapProfile profile = profile :=
  rfl

@[simp]
theorem trans_mapProfile
    (f : G.Hom H) (g : H.Hom K) (profile : G.Profile) :
    (f.trans g).mapProfile profile =
      g.mapProfile (f.mapProfile profile) :=
  rfl

@[simp]
theorem refl_trans (f : G.Hom H) :
    (refl G).trans f = f := by
  ext <;> rfl

@[simp]
theorem trans_refl (f : G.Hom H) :
    f.trans (refl H) = f := by
  ext <;> rfl

theorem trans_assoc
    {L : IndexedContinuationGameForm N}
    (f : G.Hom H) (g : H.Hom K) (h : K.Hom L) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext <;> rfl

/-- Fixing an index turns an indexed morphism into the existing continuation
morphism. -/
def atHom (f : G.Hom H) (horizon : G.Horizon) :
    (G.atIndex horizon).Hom
      (H.atIndex (f.horizonMap horizon)) where
  rootMap := f.rootMap
  strategyMap := f.strategyMap
  outcomeMap := f.outcomeMap
  map_declaredRoot := f.map_declaredRoot
  map_outcome := f.map_outcome horizon

@[simp]
theorem atHom_mapProfile
    (f : G.Hom H) (horizon : G.Horizon) (profile : G.Profile) :
    (f.atHom horizon).mapProfile profile = f.mapProfile profile :=
  rfl

/-- Every target strategy has a source representative. -/
def StrategySurjective (f : G.Hom H) : Prop :=
  ∀ i, Function.Surjective (f.strategyMap i)

/-- Every target semantic index has a source representative. -/
def HorizonSurjective (f : G.Hom H) : Prop :=
  Function.Surjective f.horizonMap

/-- Every admissible target root has an admissible source preimage. -/
def DeclaredRootSurjective (f : G.Hom H) : Prop :=
  ∀ targetRoot, H.IsDeclaredRoot targetRoot →
    ∃ sourceRoot, G.IsDeclaredRoot sourceRoot ∧
      f.rootMap sourceRoot = targetRoot

/-- Utilities commute with all index, root, and outcome maps. -/
def UtilityCompatible
    {V : Type uV} (f : G.Hom H)
    (sourceUtility : G.Horizon → G.Root → G.Outcome → N → V)
    (targetUtility : H.Horizon → H.Root → H.Outcome → N → V) : Prop :=
  ∀ horizon root outcome i,
    targetUtility (f.horizonMap horizon) (f.rootMap root)
        (f.outcomeMap outcome) i =
      sourceUtility horizon root outcome i

/-- Indexed utility compatibility specializes to each fixed-index morphism. -/
theorem atHom_utilityCompatible
    {V : Type uV} (f : G.Hom H)
    {sourceUtility : G.Horizon → G.Root → G.Outcome → N → V}
    {targetUtility : H.Horizon → H.Root → H.Outcome → N → V}
    (hutility : f.UtilityCompatible sourceUtility targetUtility)
    (horizon : G.Horizon) :
    (f.atHom horizon).UtilityCompatible
      (sourceUtility horizon)
      (targetUtility (f.horizonMap horizon)) :=
  fun root outcome i => hutility horizon root outcome i

/-- Exact Nash-on-declared-roots transfer at any index follows from the existing continuation
theorem and uniform strategy/root coverage. -/
theorem isNashOnRootsAt_iff_of_surjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    (f : G.Hom H)
    {sourceUtility : G.Horizon → G.Root → G.Outcome → N → V}
    {targetUtility : H.Horizon → H.Root → H.Outcome → N → V}
    (hutility : f.UtilityCompatible sourceUtility targetUtility)
    (hstrategy : f.StrategySurjective)
    (hroot : f.DeclaredRootSurjective)
    (horizon : G.Horizon) (profile : G.Profile) :
    G.IsNashOnRootsAt (sourceUtility horizon) horizon profile ↔
      H.IsNashOnRootsAt
        (targetUtility (f.horizonMap horizon))
      (f.horizonMap horizon) (f.mapProfile profile) := by
  exact
    (f.atHom horizon).isNashOnRoots_iff_of_surjective
      (f.atHom_utilityCompatible hutility horizon)
      hstrategy hroot profile

/-- Uniform index, strategy, and root coverage gives exact Nash-on-declared-roots transfer over
the complete indexed family. -/
theorem isNashOnRoots_iff_of_surjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    (f : G.Hom H)
    {sourceUtility : G.Horizon → G.Root → G.Outcome → N → V}
    {targetUtility : H.Horizon → H.Root → H.Outcome → N → V}
    (hutility : f.UtilityCompatible sourceUtility targetUtility)
    (hhorizon : f.HorizonSurjective)
    (hstrategy : f.StrategySurjective)
    (hroot : f.DeclaredRootSurjective)
    (profile : G.Profile) :
    G.IsNashOnRoots sourceUtility profile ↔
      H.IsNashOnRoots targetUtility (f.mapProfile profile) := by
  constructor
  · intro hsource targetHorizon
    obtain ⟨sourceHorizon, rfl⟩ :=
      hhorizon targetHorizon
    exact
      (f.isNashOnRootsAt_iff_of_surjective
        hutility hstrategy hroot sourceHorizon profile).mp
        (hsource sourceHorizon)
  · intro htarget sourceHorizon
    exact
      (f.isNashOnRootsAt_iff_of_surjective
        hutility hstrategy hroot sourceHorizon profile).mpr
        (htarget (f.horizonMap sourceHorizon))

end Hom

/-- An invertible indexed continuation semantics. -/
structure Iso (G H : IndexedContinuationGameForm N) where
  horizonEquiv : G.Horizon ≃ H.Horizon
  rootEquiv : G.Root ≃ H.Root
  strategyEquiv : (i : N) → G.Strategy i ≃ H.Strategy i
  outcomeEquiv : G.Outcome ≃ H.Outcome
  map_declaredRoot :
    ∀ root, G.IsDeclaredRoot root ↔ H.IsDeclaredRoot (rootEquiv root)
  map_outcome :
    ∀ (horizon : G.Horizon) (root : G.Root) (profile : G.Profile),
      outcomeEquiv (G.outcome horizon root profile) =
        H.outcome (horizonEquiv horizon) (rootEquiv root)
          (fun i => strategyEquiv i (profile i))

namespace Iso

variable {G H K : IndexedContinuationGameForm N}

/-- Indexed isomorphisms are determined by their four equivalences. -/
@[ext]
theorem ext (e f : G.Iso H)
    (hhorizon : e.horizonEquiv = f.horizonEquiv)
    (hroot : e.rootEquiv = f.rootEquiv)
    (hstrategy : e.strategyEquiv = f.strategyEquiv)
    (houtcome : e.outcomeEquiv = f.outcomeEquiv) :
    e = f := by
  cases e
  cases f
  cases hhorizon
  cases hroot
  cases hstrategy
  cases houtcome
  rfl

/-- Identity indexed-continuation isomorphism. -/
def refl (G : IndexedContinuationGameForm N) : G.Iso G where
  horizonEquiv := Equiv.refl _
  rootEquiv := Equiv.refl _
  strategyEquiv := fun _ => Equiv.refl _
  outcomeEquiv := Equiv.refl _
  map_declaredRoot := fun _ => Iff.rfl
  map_outcome := by intros; rfl

/-- Compose indexed-continuation isomorphisms. -/
def trans (e : G.Iso H) (f : H.Iso K) : G.Iso K where
  horizonEquiv := e.horizonEquiv.trans f.horizonEquiv
  rootEquiv := e.rootEquiv.trans f.rootEquiv
  strategyEquiv := fun i =>
    (e.strategyEquiv i).trans (f.strategyEquiv i)
  outcomeEquiv := e.outcomeEquiv.trans f.outcomeEquiv
  map_declaredRoot := fun root =>
    (e.map_declaredRoot root).trans
      (f.map_declaredRoot (e.rootEquiv root))
  map_outcome := by
    intro horizon root profile
    change
      f.outcomeEquiv
          (e.outcomeEquiv
            (G.outcome horizon root profile)) =
        K.outcome
          (f.horizonEquiv (e.horizonEquiv horizon))
          (f.rootEquiv (e.rootEquiv root))
          (fun i =>
            f.strategyEquiv i
              (e.strategyEquiv i (profile i)))
    rw [e.map_outcome, f.map_outcome]

/-- Forget invertibility and retain the indexed morphism. -/
def toHom (e : G.Iso H) : G.Hom H where
  horizonMap := e.horizonEquiv
  rootMap := e.rootEquiv
  strategyMap := fun i => e.strategyEquiv i
  outcomeMap := e.outcomeEquiv
  map_declaredRoot := fun root => (e.map_declaredRoot root).mp
  map_outcome := e.map_outcome

/-- Fixing an index turns an indexed isomorphism into the existing
continuation isomorphism. -/
def atIso (e : G.Iso H) (horizon : G.Horizon) :
    (G.atIndex horizon).Iso
      (H.atIndex (e.horizonEquiv horizon)) where
  rootEquiv := e.rootEquiv
  strategyEquiv := e.strategyEquiv
  outcomeEquiv := e.outcomeEquiv
  map_declaredRoot := e.map_declaredRoot
  map_outcome := e.map_outcome horizon

/-- Map a profile through an indexed isomorphism. -/
def mapProfile (e : G.Iso H) (profile : G.Profile) : H.Profile :=
  e.toHom.mapProfile profile

/-- Indexed isomorphisms are strategy-surjective. -/
theorem toHom_strategySurjective (e : G.Iso H) :
    e.toHom.StrategySurjective :=
  fun i => (e.strategyEquiv i).surjective

/-- Indexed isomorphisms cover every target semantic index. -/
theorem toHom_horizonSurjective (e : G.Iso H) :
    e.toHom.HorizonSurjective :=
  e.horizonEquiv.surjective

/-- Indexed isomorphisms cover every admissible target root. -/
theorem toHom_declaredRootSurjective (e : G.Iso H) :
    e.toHom.DeclaredRootSurjective := by
  intro targetRoot htarget
  let sourceRoot := e.rootEquiv.symm targetRoot
  refine ⟨sourceRoot, ?_, e.rootEquiv.apply_symm_apply targetRoot⟩
  exact
    (e.map_declaredRoot sourceRoot).mpr
      (by simpa [sourceRoot] using htarget)

/-- An indexed isomorphism preserves Nash-on-declared-roots at every selected source index. -/
theorem isNashOnRootsAt_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    (e : G.Iso H)
    {sourceUtility : G.Horizon → G.Root → G.Outcome → N → V}
    {targetUtility : H.Horizon → H.Root → H.Outcome → N → V}
    (hutility : e.toHom.UtilityCompatible sourceUtility targetUtility)
    (horizon : G.Horizon) (profile : G.Profile) :
    G.IsNashOnRootsAt (sourceUtility horizon) horizon profile ↔
      H.IsNashOnRootsAt
        (targetUtility (e.horizonEquiv horizon))
        (e.horizonEquiv horizon) (e.mapProfile profile) :=
  e.toHom.isNashOnRootsAt_iff_of_surjective
    hutility e.toHom_strategySurjective
    e.toHom_declaredRootSurjective horizon profile

/-- An indexed isomorphism preserves Nash-on-declared-roots simultaneously over all semantic
indices. -/
theorem isNashOnRoots_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    (e : G.Iso H)
    {sourceUtility : G.Horizon → G.Root → G.Outcome → N → V}
    {targetUtility : H.Horizon → H.Root → H.Outcome → N → V}
    (hutility : e.toHom.UtilityCompatible sourceUtility targetUtility)
    (profile : G.Profile) :
    G.IsNashOnRoots sourceUtility profile ↔
      H.IsNashOnRoots targetUtility (e.mapProfile profile) :=
  e.toHom.isNashOnRoots_iff_of_surjective
    hutility e.toHom_horizonSurjective
    e.toHom_strategySurjective
    e.toHom_declaredRootSurjective profile

end Iso

end IndexedContinuationGameForm
