/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.Continuation.Simulation

/-!
# EconCSLib.GameTheory.GameForm.Continuation.Iso

An isomorphism supplies equivalences of roots, player strategies, and
outcomes that commute with continuation evaluation. Read `Iso`, its `toHom`
view and inverse, then the composition laws and two-way transfer of
`IsNashOnRoots`.

The equivalence transports the declared-root predicate; it does not certify
that those roots form a lawful subgame system.
-/

universe uN uS uR uO uV

namespace ContinuationGameForm

variable {N : Type uN}

/-! ### Isomorphisms -/

/-- An isomorphism of representation-neutral continuation semantics. -/
structure Iso (G H : ContinuationGameForm N) where
  /-- Equivalence of continuation roots. -/
  rootEquiv : G.Root ≃ H.Root
  /-- Equivalence of every player's complete strategy space. -/
  strategyEquiv :
    (i : N) → G.Strategy i ≃ H.Strategy i
  /-- Equivalence of continuation outcomes. -/
  outcomeEquiv : G.Outcome ≃ H.Outcome
  /-- Caller-declared roots correspond exactly. -/
  map_declaredRoot :
    ∀ root : G.Root,
      G.IsDeclaredRoot root ↔
        H.IsDeclaredRoot (rootEquiv root)
  /-- Evaluation commutes at every root. -/
  map_outcome :
    ∀ (root : G.Root) (profile : G.Profile),
      outcomeEquiv (G.outcome root profile) =
        H.outcome (rootEquiv root)
          (fun i => strategyEquiv i (profile i))

namespace Iso

variable {G H K : ContinuationGameForm N}

/-- Continuation isomorphisms are equal when their root, strategy, and
outcome equivalences are equal. -/
@[ext]
theorem ext (e f : G.Iso H)
    (hroot : e.rootEquiv = f.rootEquiv)
    (hstrategy : e.strategyEquiv = f.strategyEquiv)
    (houtcome : e.outcomeEquiv = f.outcomeEquiv) :
    e = f := by
  cases e
  cases f
  cases hroot
  cases hstrategy
  cases houtcome
  rfl

/-- Forget invertibility and retain a continuation morphism. -/
def toHom (e : G.Iso H) : G.Hom H where
  rootMap := e.rootEquiv
  strategyMap := fun i => e.strategyEquiv i
  outcomeMap := e.outcomeEquiv
  map_declaredRoot := by
    intro root hroot
    exact (e.map_declaredRoot root).mp hroot
  map_outcome := e.map_outcome

/-- Forget invertibility and retain the graph relational simulation. -/
def toSimulation (e : G.Iso H) :
    G.Simulation H :=
  e.toHom.toSimulation fun root hroot =>
    (e.map_declaredRoot root).mpr hroot

/-- The graph simulation induced by an isomorphism covers every admissible
source root. -/
theorem toSimulation_sourceRootTotal
    (e : G.Iso H) :
    e.toSimulation.SourceRootTotal :=
  e.toHom.toSimulation_sourceRootTotal _

/-- The graph simulation induced by an isomorphism covers every admissible
target root. -/
theorem toSimulation_targetRootTotal
    (e : G.Iso H) :
    e.toSimulation.TargetRootTotal := by
  intro targetRoot htargetRoot
  let sourceRoot :=
    e.rootEquiv.symm targetRoot
  refine ⟨sourceRoot, ?_⟩
  exact e.rootEquiv.apply_symm_apply targetRoot

/-- The graph simulation induced by an isomorphism is strategy-surjective. -/
theorem toSimulation_strategySurjective
    (e : G.Iso H) :
    e.toSimulation.StrategySurjective := by
  intro i targetStrategy
  exact
    ⟨(e.strategyEquiv i).symm targetStrategy,
      (e.strategyEquiv i).apply_symm_apply
        targetStrategy⟩

/-- Map one complete profile along a continuation isomorphism. -/
def mapProfile (e : G.Iso H) (profile : G.Profile) :
    H.Profile :=
  e.toHom.mapProfile profile

/-- Identity continuation isomorphism. -/
def refl (G : ContinuationGameForm N) : G.Iso G where
  rootEquiv := Equiv.refl _
  strategyEquiv := fun _ => Equiv.refl _
  outcomeEquiv := Equiv.refl _
  map_declaredRoot := by
    intro root
    rfl
  map_outcome := by
    intro root profile
    rfl

/-- Reverse a continuation isomorphism. -/
def symm (e : G.Iso H) : H.Iso G where
  rootEquiv := e.rootEquiv.symm
  strategyEquiv := fun i =>
    (e.strategyEquiv i).symm
  outcomeEquiv := e.outcomeEquiv.symm
  map_declaredRoot := by
    intro root
    simpa using
      (e.map_declaredRoot
        (e.rootEquiv.symm root)).symm
  map_outcome := by
    intro root profile
    apply e.outcomeEquiv.injective
    rw [e.map_outcome]
    simp

/-- Compose continuation isomorphisms. -/
def trans (e : G.Iso H) (f : H.Iso K) :
    G.Iso K where
  rootEquiv := e.rootEquiv.trans f.rootEquiv
  strategyEquiv := fun i =>
    (e.strategyEquiv i).trans
      (f.strategyEquiv i)
  outcomeEquiv :=
    e.outcomeEquiv.trans f.outcomeEquiv
  map_declaredRoot := by
    intro root
    exact
      (e.map_declaredRoot root).trans
        (f.map_declaredRoot
          (e.rootEquiv root))
  map_outcome := by
    intro root profile
    change
      f.outcomeEquiv
          (e.outcomeEquiv
            (G.outcome root profile)) =
        K.outcome
          (f.rootEquiv (e.rootEquiv root))
          (fun i =>
            f.strategyEquiv i
              (e.strategyEquiv i (profile i)))
    rw [e.map_outcome, f.map_outcome]

/-- Mapping a profile through the identity continuation isomorphism is a
no-op. -/
@[simp]
theorem refl_mapProfile
    (G : ContinuationGameForm N) (profile : G.Profile) :
    (refl G).mapProfile profile = profile :=
  rfl

/-- Profile mapping is functorial under continuation-isomorphism
composition. -/
@[simp]
theorem trans_mapProfile
    (e : G.Iso H) (f : H.Iso K) (profile : G.Profile) :
    (e.trans f).mapProfile profile =
      f.mapProfile (e.mapProfile profile) :=
  rfl

/-- The identity continuation isomorphism is a left unit for composition. -/
@[simp]
theorem refl_trans (e : G.Iso H) :
    (refl G).trans e = e := by
  apply Iso.ext
  · apply Equiv.ext
    intro root
    rfl
  · funext i
    apply Equiv.ext
    intro strategy
    rfl
  · apply Equiv.ext
    intro outcome
    rfl

/-- The identity continuation isomorphism is a right unit for composition. -/
@[simp]
theorem trans_refl (e : G.Iso H) :
    e.trans (refl H) = e := by
  apply Iso.ext
  · apply Equiv.ext
    intro root
    rfl
  · funext i
    apply Equiv.ext
    intro strategy
    rfl
  · apply Equiv.ext
    intro outcome
    rfl

/-- Composition of continuation isomorphisms is associative. -/
theorem trans_assoc {L : ContinuationGameForm N}
    (e : G.Iso H) (f : H.Iso K) (g : K.Iso L) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  apply Iso.ext
  · apply Equiv.ext
    intro root
    rfl
  · funext i
    apply Equiv.ext
    intro strategy
    rfl
  · apply Equiv.ext
    intro outcome
    rfl

/-- The underlying morphism of an isomorphism is strategy-surjective. -/
theorem toHom_strategySurjective
    (e : G.Iso H) :
    e.toHom.StrategySurjective := by
  intro i targetStrategy
  exact
    ⟨(e.strategyEquiv i).symm targetStrategy,
      (e.strategyEquiv i).apply_symm_apply
        targetStrategy⟩

/-- The underlying morphism of an isomorphism is surjective on
caller-declared roots. -/
theorem toHom_declaredRootSurjective
    (e : G.Iso H) :
    e.toHom.DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  let sourceRoot :=
    e.rootEquiv.symm targetRoot
  refine
    ⟨sourceRoot, ?_, ?_⟩
  · exact
      (e.map_declaredRoot sourceRoot).mpr
        (by
          simpa [sourceRoot] using
            htargetRoot)
  · exact
      e.rootEquiv.apply_symm_apply
        targetRoot

/-- Continuation isomorphisms preserve Nash-on-declared-roots in both directions for compatible
root-dependent utility interpretations. -/
theorem isNashOnRoots_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    (e : G.Iso H)
    {sourceUtility :
      G.Root → G.Outcome → N → V}
    {targetUtility :
      H.Root → H.Outcome → N → V}
    (hutility :
      e.toHom.UtilityCompatible
        sourceUtility targetUtility)
    (profile : G.Profile) :
    G.IsNashOnRoots sourceUtility profile ↔
      H.IsNashOnRoots targetUtility
        (e.mapProfile profile) := by
  exact
    e.toHom.isNashOnRoots_iff_of_surjective
      hutility
      e.toHom_strategySurjective
      e.toHom_declaredRootSurjective
      profile

end Iso

end ContinuationGameForm
