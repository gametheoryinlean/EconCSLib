/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE

/-!
# EconCSLib.GameTheory.ExtensiveGame.GameTreeNE

Nash equilibrium on `GameTree`, a weaker concept than subgame-perfect equilibrium.

An NE only requires optimality at the root (the entire game), allowing
"incredible threats" off the equilibrium path. Every SPE is an NE, but
not vice-versa — this is the classical distinction [MSZ §7.1].

## Main definitions

* `GameTree.IsNashEquilibrium` — no unilateral deviation improves the
  root-game outcome.
* `GameTree.IsNashAt` — root-scoped alias for `IsNashEquilibrium`.
* `GameTree.IsSubgamePerfectOn` — root-scoped subgame-perfect predicate.
* `GameTree.HasOnlyRootSubgames` — every subgame of a fixed tree is the root.

## Main results

* `IsSubgamePerfect.toNE` — SPE implies NE (as a corollary of Kuhn).
* `IsSubgamePerfect.toSubgamePerfectOn` — global SPE implies root-scoped SPE.
* `isSubgamePerfectOn_iff_forall_subtree_isNashAt` — subgame perfection on a
  root is exactly Nash equilibrium at every subtree.
* `IsNashAt.toSubgamePerfectOn_of_hasOnlyRootSubgames` — if a tree has no
  proper subgames, every root Nash equilibrium is subgame-perfect on that tree
  (MSZ Theorem 7.4, pure finite-tree form).
-/

namespace GameTree

variable {N U : Type*} [TotalPreorder U]

/-- **Nash equilibrium**: no single player can improve their outcome at the
    root game by unilateral deviation.

    Weaker than `IsSubgamePerfect`, which demands optimality at every subtree. -/
def IsNashEquilibrium (σ : Strategy N U) (g : GameTree N U) : Prop :=
  ∀ (i : N) (σ' : Strategy N U),
    IVariant i σ σ' → outcome σ' g i ≤ outcome σ g i

/-- Root-scoped Nash equilibrium predicate for a fixed `GameTree` root.

This is definitionally the existing `IsNashEquilibrium`, with the requested
root-first API name for users who want to state equilibrium at a particular
subgame rather than quantify over every subtree. -/
abbrev IsNashAt (σ : Strategy N U) (g : GameTree N U) : Prop :=
  IsNashEquilibrium σ g

/-- Root-scoped subgame perfection on the subtrees of a fixed root.

`IsSubgamePerfect σ` is global over every `GameTree N U`.  This predicate
restricts the same no-profitable-deviation condition to subgames that occur
inside the chosen root `g`. -/
def IsSubgamePerfectOn (σ : Strategy N U) (g : GameTree N U) : Prop :=
  ∀ (s : GameTree N U), Subtree s g →
    ∀ (i : N) (σ' : Strategy N U),
      IVariant i σ σ' → outcome σ' s i ≤ outcome σ s i

/-- A fixed `GameTree` has no proper subgames when every subtree is the root
    itself. This is the pure finite-tree analogue of having no nontrivial
    subgames. -/
def HasOnlyRootSubgames (g : GameTree N U) : Prop :=
  ∀ s : GameTree N U, Subtree s g → s = g

/-- Root-scoped subgame perfection is equivalent to Nash equilibrium at every
    subtree of the root. This is the pure finite-tree form of MSZ Definition 7.2. -/
theorem isSubgamePerfectOn_iff_forall_subtree_isNashAt
    {σ : Strategy N U} {g : GameTree N U} :
    IsSubgamePerfectOn σ g ↔ ∀ s : GameTree N U, Subtree s g → IsNashAt σ s :=
  Iff.rfl

/-- **SPE ⇒ NE**: every subgame-perfect equilibrium is a Nash equilibrium
    (at any fixed root game). -/
theorem IsSubgamePerfect.toNE {σ : Strategy N U} (hspe : IsSubgamePerfect σ)
    (g : GameTree N U) : IsNashEquilibrium σ g :=
  fun i σ' hiv => hspe g i σ' hiv

/-- A global subgame-perfect equilibrium is subgame-perfect on every fixed root. -/
theorem IsSubgamePerfect.toSubgamePerfectOn {σ : Strategy N U}
    (hspe : IsSubgamePerfect σ) (g : GameTree N U) :
    IsSubgamePerfectOn σ g :=
  fun s _ i σ' hiv => hspe s i σ' hiv

/-- Root-scoped subgame perfection implies Nash equilibrium at the same root. -/
theorem IsSubgamePerfectOn.toNashAt {σ : Strategy N U} {g : GameTree N U}
    (hspe : IsSubgamePerfectOn σ g) : IsNashAt σ g :=
  fun i σ' hiv => hspe g (Subtree.self g) i σ' hiv

/-- If a tree has no proper subgames, root Nash equilibrium already implies
    subgame perfection on that tree. This is the pure finite-tree form of
    MSZ Theorem 7.4. -/
theorem IsNashAt.toSubgamePerfectOn_of_hasOnlyRootSubgames
    {σ : Strategy N U} {g : GameTree N U}
    (hnash : IsNashAt σ g) (hsubgames : HasOnlyRootSubgames g) :
    IsSubgamePerfectOn σ g := by
  intro s hsg i σ' hiv
  have hs : s = g := hsubgames s hsg
  subst hs
  exact hnash i σ' hiv

/-- **Kuhn's theorem, NE form**: every finite perfect-information game
    without chance has a pure-strategy Nash equilibrium. -/
theorem Kuhn_exists_NE [DecidableLE U] (g : GameTree N U) :
    ∃ σ : Strategy N U, IsNashEquilibrium σ g := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE (N := N) (U := U)
  exact ⟨σ, hspe.toNE g⟩

/-- **Kuhn's theorem, root-scoped SPE form**: every finite perfect-information
    game without chance has a pure strategy that is subgame-perfect on that
    root. -/
theorem Kuhn_exists_SPE_on [DecidableLE U] (g : GameTree N U) :
    ∃ σ : Strategy N U, IsSubgamePerfectOn σ g := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE (N := N) (U := U)
  exact ⟨σ, hspe.toSubgamePerfectOn g⟩

end GameTree
