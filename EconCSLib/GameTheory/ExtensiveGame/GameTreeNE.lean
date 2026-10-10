/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE

/-!
# EconCSLib.GameTheory.ExtensiveGame.GameTreeNE

Nash equilibrium for the historical structural endpoint-policy layer.

An NE only requires optimality at the root (the entire game), allowing
"incredible threats" off the equilibrium path.
`IsGlobalEndpointSubgamePerfectOn` checks all subtree *values* of a fixed
root, but equal values at distinct occurrences remain merged. Canonical
occurrence-sensitive NE/SPE uses `toOccurrenceObservedGame`.

## Main definitions

* `GameTree.IsNashEquilibrium` — no unilateral deviation improves the
  root-game outcome.
* `GameTree.IsNashAt` — root-scoped alias for `IsNashEquilibrium`.
* `GameTree.IsGlobalEndpointSubgamePerfectOn` — root-scoped structural
  endpoint-policy optimality.
* `GameTree.HasOnlyRootSubgames` — every subgame of a fixed tree is the root.

## Main results

* `IsGlobalEndpointSubgamePerfect.toNE` — global endpoint optimality implies
  NE.
* `IsGlobalEndpointSubgamePerfect.toGlobalEndpointSubgamePerfectOn` — the
  global predicate implies its root-scoped version.
* `isGlobalEndpointSubgamePerfectOn_iff_forall_subtree_isNashAt` — structural
  endpoint optimality on a root is exactly Nash equilibrium at every subtree
  value.
* `IsNashAt.toGlobalEndpointSubgamePerfectOn_of_hasOnlyRootSubgames` — if a tree has no
  proper subtree values, every root Nash equilibrium is structurally
  endpoint-optimal on that tree.
-/

namespace GameTree

variable {N U : Type*} [TotalPreorder U]

/-- **Nash equilibrium**: no single player can improve their outcome at the
    root game by unilateral deviation.

    Weaker than `IsGlobalEndpointSubgamePerfect`, which demands optimality at every subtree. -/
def IsNashEquilibrium (σ : Strategy N U) (g : GameTree N U) : Prop :=
  ∀ (i : N) (σ' : Strategy N U),
    IVariant i σ σ' → outcome σ' g i ≤ outcome σ g i

/-- Root-scoped Nash equilibrium predicate for a fixed `GameTree` root.

This is definitionally the existing `IsNashEquilibrium`, with the requested
root-first API name for users who want to state equilibrium at a particular
subgame rather than quantify over every subtree. -/
abbrev IsNashAt (σ : Strategy N U) (g : GameTree N U) : Prop :=
  IsNashEquilibrium σ g

/-- Root-scoped structural endpoint optimality on the subtree values of a
fixed root.

`IsGlobalEndpointSubgamePerfect σ` is global over every `GameTree N U`.  This predicate
restricts the same no-profitable-deviation condition to subgames that occur
inside the chosen root `g`. Equal subtree values at different occurrences are
still identified, so this is not the canonical occurrence-sensitive standard
EFG predicate. -/
def IsGlobalEndpointSubgamePerfectOn (σ : Strategy N U) (g : GameTree N U) : Prop :=
  ∀ (s : GameTree N U), Subtree s g →
    ∀ (i : N) (σ' : Strategy N U),
      IVariant i σ σ' → outcome σ' s i ≤ outcome σ s i

/-- A fixed `GameTree` has no proper subgames when every subtree is the root
    itself. This is the pure finite-tree analogue of having no nontrivial
    subgames. -/
def HasOnlyRootSubgames (g : GameTree N U) : Prop :=
  ∀ s : GameTree N U, Subtree s g → s = g

/-- Root-scoped structural endpoint optimality is equivalent to Nash
equilibrium at every subtree value of the root. -/
theorem isGlobalEndpointSubgamePerfectOn_iff_forall_subtree_isNashAt
    {σ : Strategy N U} {g : GameTree N U} :
    IsGlobalEndpointSubgamePerfectOn σ g ↔ ∀ s : GameTree N U, Subtree s g → IsNashAt σ s :=
  Iff.rfl

/-- Global structural endpoint optimality implies Nash equilibrium at any
fixed root game. -/
theorem IsGlobalEndpointSubgamePerfect.toNE {σ : Strategy N U} (hspe : IsGlobalEndpointSubgamePerfect σ)
    (g : GameTree N U) : IsNashEquilibrium σ g :=
  fun i σ' hiv => hspe g i σ' hiv

/-- Global structural endpoint optimality restricts to every fixed root. -/
theorem IsGlobalEndpointSubgamePerfect.toGlobalEndpointSubgamePerfectOn {σ : Strategy N U}
    (hspe : IsGlobalEndpointSubgamePerfect σ) (g : GameTree N U) :
    IsGlobalEndpointSubgamePerfectOn σ g :=
  fun s _ i σ' hiv => hspe s i σ' hiv

/-- Root-scoped structural endpoint optimality implies Nash equilibrium at
the same root. -/
theorem IsGlobalEndpointSubgamePerfectOn.toNashAt {σ : Strategy N U} {g : GameTree N U}
    (hspe : IsGlobalEndpointSubgamePerfectOn σ g) : IsNashAt σ g :=
  fun i σ' hiv => hspe g (Subtree.self g) i σ' hiv

/-- If a tree has no proper subtree value, root Nash equilibrium already
implies structural endpoint optimality on that tree. -/
theorem IsNashAt.toGlobalEndpointSubgamePerfectOn_of_hasOnlyRootSubgames
    {σ : Strategy N U} {g : GameTree N U}
    (hnash : IsNashAt σ g) (hsubgames : HasOnlyRootSubgames g) :
    IsGlobalEndpointSubgamePerfectOn σ g := by
  intro s hsg i σ' hiv
  have hs : s = g := hsubgames s hsg
  subst hs
  exact hnash i σ' hiv

/-- **Kuhn's theorem, NE form**: every finite perfect-information game
    without chance has a pure-strategy Nash equilibrium. -/
theorem Kuhn_exists_NE [DecidableLE U] (g : GameTree N U) :
    ∃ σ : Strategy N U, IsNashEquilibrium σ g := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_globalEndpointSPE (N := N) (U := U)
  exact ⟨σ, hspe.toNE g⟩

/-- Every finite tree has a pure strategy that is globally endpoint-optimal on
all subtree values of the selected root. -/
theorem Kuhn_exists_globalEndpointSPE_on [DecidableLE U] (g : GameTree N U) :
    ∃ σ : Strategy N U, IsGlobalEndpointSubgamePerfectOn σ g := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_globalEndpointSPE (N := N) (U := U)
  exact ⟨σ, hspe.toGlobalEndpointSubgamePerfectOn g⟩

end GameTree
