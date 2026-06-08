/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE

/-!
# ExtensiveGame.GameTreeNE

Nash equilibrium on `GameTree`, a weaker concept than subgame-perfect equilibrium.

An NE only requires optimality at the root (the entire game), allowing
"incredible threats" off the equilibrium path. Every SPE is an NE, but
not vice-versa — this is the classical distinction [MSZ §7.1].

## Main definitions

* `GameTree.IsNashEquilibrium` — no unilateral deviation improves the
  root-game outcome.
* `GameTree.IsNashAt` — root-scoped alias for `IsNashEquilibrium`.
* `GameTree.IsSubgamePerfectOn` — root-scoped subgame-perfect predicate.
* `GameTree.ProperSubgame` — a subtree strictly below a fixed root.
* `GameTree.HasOnlyRootSubgames` — every subgame of a fixed tree is the root.

## Main results

* `IsSubgamePerfect.toNE` — SPE implies NE (as a corollary of Kuhn).
* `IsSubgamePerfect.toNashAt` — the same implication with the root-scoped name.
* `IsSubgamePerfect.of_forall_isNashAt` — build global SPE from Nash
  equilibrium at every root.
* `isSubgamePerfect_iff_forall_isNashAt` — global SPE is Nash equilibrium at
  every root.
* `IsSubgamePerfect.toSubgamePerfectOn` — global SPE implies root-scoped SPE.
* `IsSubgamePerfect.of_forall_isSubgamePerfectOn` — build global SPE from
  root-scoped SPE at every root.
* `isSubgamePerfect_iff_forall_isSubgamePerfectOn` — global SPE is equivalent
  to root-scoped SPE at every root.
* `isSubgamePerfectOn_iff_forall_subtree_isNashAt` — subgame perfection on a
  root is exactly Nash equilibrium at every subtree.
* `IsNashAt.toSubgamePerfectOn_of_forall_subtree_isNashAt` — build
  root-scoped SPE from Nash equilibrium at every subtree.
* `isNashAt_Leaf` / `isSubgamePerfectOn_Leaf` — leaves are automatically
  Nash and subgame-perfect for every strategy.
* `IsSubgamePerfectOn.of_subtree` — root-scoped SPE restricts to every subtree.
* `IsSubgamePerfectOn.of_forall_subtree_isSubgamePerfectOn` — build
  root-scoped SPE from root-scoped SPE on every subtree.
* `isSubgamePerfectOn_iff_forall_subtree_isSubgamePerfectOn` — root-scoped SPE
  is equivalent to root-scoped SPE on every subtree.
* `IsSubgamePerfectOn.toNashAt_of_subtree` — root-scoped SPE gives Nash
  equilibrium at every subtree.
* `IsSubgamePerfectOn.of_properSubgame` / `toNashAt_of_properSubgame` —
  proper-subgame versions of the restriction facts.
* `IsSubgamePerfectOn.toNashAt_and_forall_properSubgame_isNashAt` /
  `toNashAt_and_forall_properSubgame_isSubgamePerfectOn` — bundled
  root/proper-subgame consequences.
* `IsNashAt.toSubgamePerfectOn_of_forall_properSubgame_isNashAt` — build
  root-scoped SPE from root Nash plus Nash equilibrium at every proper subgame.
* `isSubgamePerfectOn_iff_isNashAt_and_forall_properSubgame_isNashAt` —
  root-scoped SPE as root Nash plus Nash equilibrium at every proper subgame.
* `isSubgamePerfectOn_iff_isNashAt_and_forall_properSubgame_isSubgamePerfectOn` —
  root-scoped SPE as root Nash plus root-scoped SPE on every proper subgame.
* `IsSubgamePerfectOn.forall_subtree_isSubgamePerfectOn` /
  `forall_subtree_isNashAt` — bundled subtree consequences.
* `IsSubgamePerfectOn.head` / `tail_mem` / `child_mem` — convenience
  restrictions to direct children of a node.
* `IsSubgamePerfectOn.child` / `toNashAt_child` — the same restrictions through
  the public `children` list API.
* `isSubgamePerfectOn_Node_iff` — recursive decomposition into root Nash and
  root-scoped SPE on each direct child.
* `IsSubgamePerfectOn.toNashAt_and_head_tail` — bundled node decomposition into
  root Nash plus head/tail SPE.
* `IsNashAt.toSubgamePerfectOn_Node` — build root-scoped SPE at a node from
  root Nash plus root-scoped SPE on each direct child.
* `isSubgamePerfectOn_Node_iff_children` — the same recursive decomposition
  through `children`.
* `IsNashAt.toSubgamePerfectOn_of_hasOnlyRootSubgames` — if a tree has no
  proper subgames, every root Nash equilibrium is subgame-perfect on that tree
  (MSZ Theorem 7.4, pure finite-tree form).
* `isSubgamePerfectOn_iff_isNashAt_of_no_properSubgame` — the proper-subgame
  formulation of the no-nontrivial-subgames case.
* `optStrategy_isSubgamePerfectOn` / `optStrategy_isNashAt` — the canonical
  backward-induction strategy is root-scoped SPE, hence Nash, at every root.
* `Kuhn_exists_SPE_on_subtrees` / `Kuhn_exists_NE_on_subtrees` — one pure
  strategy witnesses subgame perfection, respectively Nash equilibrium, on
  every subtree of a fixed finite root.
* `Kuhn_exists_SPE_on_subtree` / `Kuhn_exists_NE_on_subtree` — fixed-subtree
  existence wrappers for applying Kuhn's theorem to a named subgame.
* `Kuhn_exists_NE_and_SPE_on_properSubgames` — one pure strategy is root Nash
  and subgame-perfect on every proper subgame of a fixed finite root.
-/

namespace GameTree

variable {ι U : Type*} [TotalPreorder U]

/-- **Nash equilibrium**: no single player can improve their outcome at the
    root game by unilateral deviation.

    Weaker than `IsSubgamePerfect`, which demands optimality at every subtree. -/
def IsNashEquilibrium (σ : Strategy ι U) (g : GameTree ι U) : Prop :=
  ∀ (i : ι) (σ' : Strategy ι U),
    IVariant i σ σ' → outcome σ' g i ≤ outcome σ g i

/-- Root-scoped Nash equilibrium predicate for a fixed `GameTree` root.

This is definitionally the existing `IsNashEquilibrium`, with the requested
root-first API name for users who want to state equilibrium at a particular
subgame rather than quantify over every subtree. -/
abbrev IsNashAt (σ : Strategy ι U) (g : GameTree ι U) : Prop :=
  IsNashEquilibrium σ g

/-- Root-scoped subgame perfection on the subtrees of a fixed root.

`IsSubgamePerfect σ` is global over every `GameTree ι U`.  This predicate
restricts the same no-profitable-deviation condition to subgames that occur
inside the chosen root `g`. -/
def IsSubgamePerfectOn (σ : Strategy ι U) (g : GameTree ι U) : Prop :=
  ∀ (s : GameTree ι U), Subtree s g →
    ∀ (i : ι) (σ' : Strategy ι U),
      IVariant i σ σ' → outcome σ' s i ≤ outcome σ s i

/-- Root-scoped subgame perfection is equivalent to Nash equilibrium at every
    subtree of the root. This is the pure finite-tree form of MSZ Definition 7.2. -/
theorem isSubgamePerfectOn_iff_forall_subtree_isNashAt
    {σ : Strategy ι U} {g : GameTree ι U} :
    IsSubgamePerfectOn σ g ↔ ∀ s : GameTree ι U, Subtree s g → IsNashAt σ s :=
  Iff.rfl

/-- Nash equilibrium at every subtree of a root gives root-scoped subgame
    perfection on that root. This is the constructor form of
    `isSubgamePerfectOn_iff_forall_subtree_isNashAt`. -/
theorem IsNashAt.toSubgamePerfectOn_of_forall_subtree_isNashAt
    {σ : Strategy ι U} {g : GameTree ι U}
    (hsubtrees : ∀ s : GameTree ι U, Subtree s g → IsNashAt σ s) :
    IsSubgamePerfectOn σ g :=
  hsubtrees

/-- Every strategy is Nash at a terminal leaf: no player has a decision left
    that could change the terminal payoff. -/
theorem isNashAt_Leaf (σ : Strategy ι U) (p : ι → U) :
    IsNashAt σ (Leaf p) := by
  intro i σ' _hiv
  simp

/-- Every strategy is root-scoped subgame-perfect on a terminal leaf. -/
theorem isSubgamePerfectOn_Leaf (σ : Strategy ι U) (p : ι → U) :
    IsSubgamePerfectOn σ (Leaf p) := by
  intro s hsub
  cases hsub
  exact isNashAt_Leaf σ p

/-- On a terminal leaf, root-scoped subgame perfection is equivalent to root
    Nash equilibrium. The forward implication holds for every root; the reverse
    direction uses that a leaf has no proper subtrees. -/
theorem isSubgamePerfectOn_Leaf_iff {σ : Strategy ι U} {p : ι → U} :
    IsSubgamePerfectOn σ (Leaf p) ↔ IsNashAt σ (Leaf p) := by
  constructor
  · intro hspe
    exact hspe (Leaf p) (Subtree.self (Leaf p))
  · intro _hnash
    exact isSubgamePerfectOn_Leaf σ p

/-- Every terminal leaf has a root-scoped Nash equilibrium. -/
theorem exists_isNashAt_Leaf (p : ι → U) :
    ∃ σ : Strategy ι U, IsNashAt σ (Leaf p) := by
  exact ⟨optStrategy, isNashAt_Leaf optStrategy p⟩

/-- Every terminal leaf has a root-scoped subgame-perfect equilibrium. -/
theorem exists_isSubgamePerfectOn_Leaf (p : ι → U) :
    ∃ σ : Strategy ι U, IsSubgamePerfectOn σ (Leaf p) := by
  exact ⟨optStrategy, isSubgamePerfectOn_Leaf optStrategy p⟩

/-- On a terminal leaf, existence of root-scoped subgame perfection is
    equivalent to existence of root Nash equilibrium. -/
theorem exists_isSubgamePerfectOn_Leaf_iff_exists_isNashAt (p : ι → U) :
    (∃ σ : Strategy ι U, IsSubgamePerfectOn σ (Leaf p)) ↔
      ∃ σ : Strategy ι U, IsNashAt σ (Leaf p) := by
  constructor
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, isSubgamePerfectOn_Leaf_iff.mp hspe⟩
  · rintro ⟨σ, _hnash⟩
    exact ⟨σ, isSubgamePerfectOn_Leaf σ p⟩

/-- **SPE ⇒ NE**: every subgame-perfect equilibrium is a Nash equilibrium
    (at any fixed root game). -/
theorem IsSubgamePerfect.toNE {σ : Strategy ι U} (hspe : IsSubgamePerfect σ)
    (g : GameTree ι U) : IsNashEquilibrium σ g :=
  fun i σ' hiv => hspe g i σ' hiv

/-- **SPE ⇒ root-scoped Nash** at any fixed root game. -/
theorem IsSubgamePerfect.toNashAt {σ : Strategy ι U} (hspe : IsSubgamePerfect σ)
    (g : GameTree ι U) : IsNashAt σ g :=
  hspe.toNE g

/-- Nash equilibrium at every root gives global subgame perfection. -/
theorem IsSubgamePerfect.of_forall_isNashAt {σ : Strategy ι U}
    (hnash : ∀ g : GameTree ι U, IsNashAt σ g) :
    IsSubgamePerfect σ :=
  hnash

/-- Global subgame perfection is equivalent to Nash equilibrium at every root. -/
theorem isSubgamePerfect_iff_forall_isNashAt {σ : Strategy ι U} :
    IsSubgamePerfect σ ↔ ∀ g : GameTree ι U, IsNashAt σ g := by
  constructor
  · intro hspe g
    exact hspe.toNashAt g
  · intro hnash
    exact IsSubgamePerfect.of_forall_isNashAt hnash

/-- A global subgame-perfect equilibrium is subgame-perfect on every fixed root. -/
theorem IsSubgamePerfect.toSubgamePerfectOn {σ : Strategy ι U}
    (hspe : IsSubgamePerfect σ) (g : GameTree ι U) :
    IsSubgamePerfectOn σ g :=
  fun s _ i σ' hiv => hspe s i σ' hiv

/-- Root-scoped subgame perfection at every root gives global subgame
    perfection. -/
theorem IsSubgamePerfect.of_forall_isSubgamePerfectOn {σ : Strategy ι U}
    (hroots : ∀ g : GameTree ι U, IsSubgamePerfectOn σ g) :
    IsSubgamePerfect σ := by
  intro g i σ' hiv
  exact hroots g g (Subtree.self g) i σ' hiv

/-- Global subgame perfection is equivalent to root-scoped subgame perfection
    at every possible root. -/
theorem isSubgamePerfect_iff_forall_isSubgamePerfectOn {σ : Strategy ι U} :
    IsSubgamePerfect σ ↔ ∀ g : GameTree ι U, IsSubgamePerfectOn σ g := by
  constructor
  · intro hspe g
    exact hspe.toSubgamePerfectOn g
  · intro hroots g i σ' hiv
    exact IsSubgamePerfect.of_forall_isSubgamePerfectOn hroots g i σ' hiv

/-- Existence of one strategy that is Nash at every root is equivalent to
    existence of a global subgame-perfect strategy. -/
theorem exists_forall_isNashAt_iff_exists_isSubgamePerfect :
    (∃ σ : Strategy ι U, ∀ g : GameTree ι U, IsNashAt σ g) ↔
      ∃ σ : Strategy ι U, IsSubgamePerfect σ := by
  constructor
  · rintro ⟨σ, hnash⟩
    exact ⟨σ, IsSubgamePerfect.of_forall_isNashAt hnash⟩
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, fun g => hspe.toNashAt g⟩

/-- Existence of one strategy that is root-scoped subgame-perfect at every root
    is equivalent to existence of a global subgame-perfect strategy. -/
theorem exists_forall_isSubgamePerfectOn_iff_exists_isSubgamePerfect :
    (∃ σ : Strategy ι U, ∀ g : GameTree ι U, IsSubgamePerfectOn σ g) ↔
      ∃ σ : Strategy ι U, IsSubgamePerfect σ := by
  constructor
  · rintro ⟨σ, hroots⟩
    exact ⟨σ, IsSubgamePerfect.of_forall_isSubgamePerfectOn hroots⟩
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, fun g => hspe.toSubgamePerfectOn g⟩

/-- Root-scoped subgame perfection implies Nash equilibrium at the same root. -/
theorem IsSubgamePerfectOn.toNashAt {σ : Strategy ι U} {g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) : IsNashAt σ g :=
  fun i σ' hiv => hspe g (Subtree.self g) i σ' hiv

/-- Root-scoped subgame perfection restricts to every subtree of the root.
    This is the subgame-perfect side of the pure finite-tree form of
    MSZ Theorem 7.5. -/
theorem IsSubgamePerfectOn.of_subtree {σ : Strategy ι U} {s g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) (hsub : Subtree s g) :
    IsSubgamePerfectOn σ s := by
  intro r hrs i σ' hiv
  exact hspe r (Subtree.trans hrs hsub) i σ' hiv

/-- If a strategy is root-scoped subgame-perfect on every subtree of a root,
    then it is root-scoped subgame-perfect on that root. -/
theorem IsSubgamePerfectOn.of_forall_subtree_isSubgamePerfectOn
    {σ : Strategy ι U} {g : GameTree ι U}
    (hsubtrees :
      ∀ s : GameTree ι U, Subtree s g → IsSubgamePerfectOn σ s) :
    IsSubgamePerfectOn σ g :=
  hsubtrees g (Subtree.self g)

/-- Root-scoped subgame perfection on a root is equivalent to root-scoped
    subgame perfection on every subtree of that root. -/
theorem isSubgamePerfectOn_iff_forall_subtree_isSubgamePerfectOn
    {σ : Strategy ι U} {g : GameTree ι U} :
    IsSubgamePerfectOn σ g ↔
      ∀ s : GameTree ι U, Subtree s g → IsSubgamePerfectOn σ s := by
  constructor
  · intro hspe s hsub
    exact hspe.of_subtree hsub
  · intro hsubtrees
    exact IsSubgamePerfectOn.of_forall_subtree_isSubgamePerfectOn hsubtrees

/-- Root-scoped subgame perfection gives Nash equilibrium at every subtree.
    This is the Nash-equilibrium side of the pure finite-tree form of
    MSZ Theorem 7.5. -/
theorem IsSubgamePerfectOn.toNashAt_of_subtree
    {σ : Strategy ι U} {s g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) (hsub : Subtree s g) :
    IsNashAt σ s :=
  (hspe.of_subtree hsub).toNashAt

/-- Root-scoped subgame perfection restricts to every proper subgame of the
    root. -/
theorem IsSubgamePerfectOn.of_properSubgame
    {σ : Strategy ι U} {s g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) (hproper : ProperSubgame s g) :
    IsSubgamePerfectOn σ s :=
  hspe.of_subtree hproper.toSubtree

/-- Root-scoped subgame perfection gives Nash equilibrium at every proper
    subgame. -/
theorem IsSubgamePerfectOn.toNashAt_of_properSubgame
    {σ : Strategy ι U} {s g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) (hproper : ProperSubgame s g) :
    IsNashAt σ s :=
  hspe.toNashAt_of_subtree hproper.toSubtree

/-- A root-scoped subgame-perfect strategy is root-scoped subgame-perfect on
    every subtree of the root. -/
theorem IsSubgamePerfectOn.forall_subtree_isSubgamePerfectOn
    {σ : Strategy ι U} {g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) :
    ∀ s : GameTree ι U, Subtree s g → IsSubgamePerfectOn σ s :=
  fun _ hsub => hspe.of_subtree hsub

/-- A root-scoped subgame-perfect strategy is Nash at every subtree of the root. -/
theorem IsSubgamePerfectOn.forall_subtree_isNashAt
    {σ : Strategy ι U} {g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) :
    ∀ s : GameTree ι U, Subtree s g → IsNashAt σ s :=
  fun _ hsub => hspe.toNashAt_of_subtree hsub

/-- Root-scoped subgame perfection gives root Nash equilibrium together with
    Nash equilibrium at every subtree of the root. -/
theorem IsSubgamePerfectOn.toNashAt_and_forall_subtree_isNashAt
    {σ : Strategy ι U} {g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) :
    IsNashAt σ g ∧
      ∀ s : GameTree ι U, Subtree s g → IsNashAt σ s :=
  ⟨hspe.toNashAt, hspe.forall_subtree_isNashAt⟩

/-- A root-scoped subgame-perfect strategy is root-scoped subgame-perfect on
    every proper subgame of the root. -/
theorem IsSubgamePerfectOn.forall_properSubgame_isSubgamePerfectOn
    {σ : Strategy ι U} {g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) :
    ∀ s : GameTree ι U, ProperSubgame s g → IsSubgamePerfectOn σ s :=
  fun _ hproper => hspe.of_properSubgame hproper

/-- Root-scoped subgame perfection gives root Nash equilibrium together with
    root-scoped subgame perfection on every subtree of the root. -/
theorem IsSubgamePerfectOn.toNashAt_and_forall_subtree_isSubgamePerfectOn
    {σ : Strategy ι U} {g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) :
    IsNashAt σ g ∧
      ∀ s : GameTree ι U, Subtree s g → IsSubgamePerfectOn σ s :=
  ⟨hspe.toNashAt, hspe.forall_subtree_isSubgamePerfectOn⟩

/-- A root-scoped subgame-perfect strategy is Nash at every proper subgame of
    the root. -/
theorem IsSubgamePerfectOn.forall_properSubgame_isNashAt
    {σ : Strategy ι U} {g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) :
    ∀ s : GameTree ι U, ProperSubgame s g → IsNashAt σ s :=
  fun _ hproper => hspe.toNashAt_of_properSubgame hproper

/-- Root-scoped subgame perfection gives root Nash equilibrium together with
    Nash equilibrium at every proper subgame. -/
theorem IsSubgamePerfectOn.toNashAt_and_forall_properSubgame_isNashAt
    {σ : Strategy ι U} {g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) :
    IsNashAt σ g ∧
      ∀ s : GameTree ι U, ProperSubgame s g → IsNashAt σ s :=
  ⟨hspe.toNashAt, hspe.forall_properSubgame_isNashAt⟩

/-- Root-scoped subgame perfection gives root Nash equilibrium together with
    root-scoped subgame perfection on every proper subgame. -/
theorem IsSubgamePerfectOn.toNashAt_and_forall_properSubgame_isSubgamePerfectOn
    {σ : Strategy ι U} {g : GameTree ι U}
    (hspe : IsSubgamePerfectOn σ g) :
    IsNashAt σ g ∧
      ∀ s : GameTree ι U, ProperSubgame s g → IsSubgamePerfectOn σ s :=
  ⟨hspe.toNashAt, hspe.forall_properSubgame_isSubgamePerfectOn⟩

/-- Root Nash equilibrium together with Nash equilibrium at every proper
    subgame gives root-scoped subgame perfection. -/
theorem IsNashAt.toSubgamePerfectOn_of_forall_properSubgame_isNashAt
    {σ : Strategy ι U} {g : GameTree ι U}
    (hnash : IsNashAt σ g)
    (hproper : ∀ s : GameTree ι U, ProperSubgame s g → IsNashAt σ s) :
    IsSubgamePerfectOn σ g := by
  intro s hsub
  rcases hsub.eq_or_properSubgame with rfl | hs
  · exact hnash
  · exact hproper s hs

/-- Root Nash equilibrium together with root-scoped subgame perfection on every
    proper subgame gives root-scoped subgame perfection. -/
theorem IsNashAt.toSubgamePerfectOn_of_forall_properSubgame_isSubgamePerfectOn
    {σ : Strategy ι U} {g : GameTree ι U}
    (hnash : IsNashAt σ g)
    (hproper :
      ∀ s : GameTree ι U, ProperSubgame s g → IsSubgamePerfectOn σ s) :
    IsSubgamePerfectOn σ g := by
  exact hnash.toSubgamePerfectOn_of_forall_properSubgame_isNashAt
    (fun s hs => (hproper s hs).toNashAt)

/-- Root-scoped subgame perfection is equivalent to Nash equilibrium at the
    root together with Nash equilibrium at every proper subgame. This is the
    proper-subgame formulation of the pure finite-tree form of MSZ Definition
    7.2. -/
theorem isSubgamePerfectOn_iff_isNashAt_and_forall_properSubgame_isNashAt
    {σ : Strategy ι U} {g : GameTree ι U} :
    IsSubgamePerfectOn σ g ↔
      IsNashAt σ g ∧
        ∀ s : GameTree ι U, ProperSubgame s g → IsNashAt σ s := by
  constructor
  · intro hspe
    exact hspe.toNashAt_and_forall_properSubgame_isNashAt
  · rintro ⟨hnash, hproper⟩
    exact hnash.toSubgamePerfectOn_of_forall_properSubgame_isNashAt hproper

/-- Root-scoped subgame perfection is equivalent to Nash equilibrium at the
    root together with root-scoped subgame perfection on every proper subgame. -/
theorem isSubgamePerfectOn_iff_isNashAt_and_forall_properSubgame_isSubgamePerfectOn
    {σ : Strategy ι U} {g : GameTree ι U} :
    IsSubgamePerfectOn σ g ↔
      IsNashAt σ g ∧
        ∀ s : GameTree ι U, ProperSubgame s g → IsSubgamePerfectOn σ s := by
  constructor
  · intro hspe
    exact hspe.toNashAt_and_forall_properSubgame_isSubgamePerfectOn
  · rintro ⟨hnash, hproper⟩
    exact hnash.toSubgamePerfectOn_of_forall_properSubgame_isSubgamePerfectOn
      hproper

/-- Existence of one strategy that is Nash at every subtree of a root is
    equivalent to existence of a root-scoped subgame-perfect strategy. -/
theorem exists_forall_subtree_isNashAt_iff_exists_isSubgamePerfectOn
    (g : GameTree ι U) :
    (∃ σ : Strategy ι U, ∀ s : GameTree ι U, Subtree s g → IsNashAt σ s) ↔
      ∃ σ : Strategy ι U, IsSubgamePerfectOn σ g := by
  constructor
  · rintro ⟨σ, hnash⟩
    exact ⟨σ, IsNashAt.toSubgamePerfectOn_of_forall_subtree_isNashAt hnash⟩
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, hspe.forall_subtree_isNashAt⟩

/-- Existence of one strategy that is root-scoped subgame-perfect on every
    subtree is equivalent to existence of a root-scoped subgame-perfect
    strategy at the root. -/
theorem exists_forall_subtree_isSubgamePerfectOn_iff_exists_isSubgamePerfectOn
    (g : GameTree ι U) :
    (∃ σ : Strategy ι U,
      ∀ s : GameTree ι U, Subtree s g → IsSubgamePerfectOn σ s) ↔
      ∃ σ : Strategy ι U, IsSubgamePerfectOn σ g := by
  constructor
  · rintro ⟨σ, hsubtrees⟩
    exact ⟨σ, IsSubgamePerfectOn.of_forall_subtree_isSubgamePerfectOn hsubtrees⟩
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, hspe.forall_subtree_isSubgamePerfectOn⟩

/-- Existence of one root Nash equilibrium that is also Nash at every proper
    subgame is equivalent to existence of a root-scoped subgame-perfect
    strategy. -/
theorem exists_isNashAt_and_forall_properSubgame_isNashAt_iff_exists_isSubgamePerfectOn
    (g : GameTree ι U) :
    (∃ σ : Strategy ι U,
      IsNashAt σ g ∧
        ∀ s : GameTree ι U, ProperSubgame s g → IsNashAt σ s) ↔
      ∃ σ : Strategy ι U, IsSubgamePerfectOn σ g := by
  constructor
  · rintro ⟨σ, hnash, hproper⟩
    exact ⟨σ, hnash.toSubgamePerfectOn_of_forall_properSubgame_isNashAt hproper⟩
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, hspe.toNashAt, hspe.forall_properSubgame_isNashAt⟩

/-- Existence of one root Nash equilibrium whose proper subgames are
    root-scoped subgame-perfect is equivalent to existence of a root-scoped
    subgame-perfect strategy. -/
theorem exists_isNashAt_and_forall_properSubgame_isSubgamePerfectOn_iff_exists_isSubgamePerfectOn
    (g : GameTree ι U) :
    (∃ σ : Strategy ι U,
      IsNashAt σ g ∧
        ∀ s : GameTree ι U, ProperSubgame s g → IsSubgamePerfectOn σ s) ↔
      ∃ σ : Strategy ι U, IsSubgamePerfectOn σ g := by
  constructor
  · rintro ⟨σ, hnash, hproper⟩
    exact ⟨σ, hnash.toSubgamePerfectOn_of_forall_properSubgame_isSubgamePerfectOn hproper⟩
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, hspe.toNashAt, hspe.forall_properSubgame_isSubgamePerfectOn⟩

/-- Root-scoped subgame perfection at a node restricts to its head child. -/
theorem IsSubgamePerfectOn.head
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hspe : IsSubgamePerfectOn σ (Node m h t)) :
    IsSubgamePerfectOn σ h :=
  hspe.of_subtree (Subtree.head m h t)

/-- Root-scoped subgame perfection at a node restricts to every tail child. -/
theorem IsSubgamePerfectOn.tail_mem
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    {c : GameTree ι U} (hspe : IsSubgamePerfectOn σ (Node m h t))
    (hmem : c ∈ t) :
    IsSubgamePerfectOn σ c :=
  hspe.of_subtree (Subtree.tail_mem m h t hmem)

/-- Root-scoped subgame perfection at a node restricts to every direct child. -/
theorem IsSubgamePerfectOn.child_mem
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    {c : GameTree ι U} (hspe : IsSubgamePerfectOn σ (Node m h t))
    (hmem : c ∈ h :: t) :
    IsSubgamePerfectOn σ c :=
  hspe.of_subtree (Subtree.child_mem m h t hmem)

/-- Root-scoped subgame perfection at a node restricts to every child in the
    public `children` list. -/
theorem IsSubgamePerfectOn.child
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    {c : GameTree ι U} (hspe : IsSubgamePerfectOn σ (Node m h t))
    (hmem : c ∈ children (Node m h t)) :
    IsSubgamePerfectOn σ c :=
  hspe.of_subtree (Subtree.child m h t hmem)

/-- Root-scoped subgame perfection at a node gives Nash equilibrium at its
    head child. -/
theorem IsSubgamePerfectOn.toNashAt_head
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hspe : IsSubgamePerfectOn σ (Node m h t)) :
    IsNashAt σ h :=
  hspe.head.toNashAt

/-- Root-scoped subgame perfection at a node gives Nash equilibrium at every
    tail child. -/
theorem IsSubgamePerfectOn.toNashAt_tail_mem
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    {c : GameTree ι U} (hspe : IsSubgamePerfectOn σ (Node m h t))
    (hmem : c ∈ t) :
    IsNashAt σ c :=
  (hspe.tail_mem hmem).toNashAt

/-- Root-scoped subgame perfection at a node gives Nash equilibrium at every
    direct child. -/
theorem IsSubgamePerfectOn.toNashAt_child_mem
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    {c : GameTree ι U} (hspe : IsSubgamePerfectOn σ (Node m h t))
    (hmem : c ∈ h :: t) :
    IsNashAt σ c :=
  (hspe.child_mem hmem).toNashAt

/-- Root-scoped subgame perfection at a node gives Nash equilibrium at every
    child in the public `children` list. -/
theorem IsSubgamePerfectOn.toNashAt_child
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    {c : GameTree ι U} (hspe : IsSubgamePerfectOn σ (Node m h t))
    (hmem : c ∈ children (Node m h t)) :
    IsNashAt σ c :=
  (hspe.child hmem).toNashAt

/-- Root-scoped subgame perfection can be checked recursively at a nonterminal
    node: Nash equilibrium at the node itself, plus root-scoped subgame
    perfection on every direct child. -/
theorem isSubgamePerfectOn_Node_iff
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)} :
    IsSubgamePerfectOn σ (Node m h t) ↔
      IsNashAt σ (Node m h t) ∧
        IsSubgamePerfectOn σ h ∧
          ∀ c ∈ t, IsSubgamePerfectOn σ c := by
  constructor
  · intro hspe
    exact ⟨hspe.toNashAt,
      hspe.of_subtree (Subtree.head m h t),
      fun c hmem => hspe.of_subtree (Subtree.tail_mem m h t hmem)⟩
  · rintro ⟨hnash, hhead, htail⟩
    intro s hsub
    cases hsub with
    | refl =>
        exact hnash
    | inHead m h t hs =>
        exact hhead.toNashAt_of_subtree hs
    | inTail m h t hmem hs =>
        exact (htail _ hmem).toNashAt_of_subtree hs

/-- Root-scoped subgame perfection at a nonterminal node gives root Nash
    equilibrium together with root-scoped subgame perfection on the head child
    and every tail child. -/
theorem IsSubgamePerfectOn.toNashAt_and_head_tail
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hspe : IsSubgamePerfectOn σ (Node m h t)) :
    IsNashAt σ (Node m h t) ∧
      IsSubgamePerfectOn σ h ∧
        ∀ c ∈ t, IsSubgamePerfectOn σ c :=
  (isSubgamePerfectOn_Node_iff).mp hspe

/-- Root Nash equilibrium at a node, together with root-scoped subgame
    perfection on each direct child, gives root-scoped subgame perfection at
    the node. -/
theorem IsNashAt.toSubgamePerfectOn_Node
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hnash : IsNashAt σ (Node m h t))
    (hhead : IsSubgamePerfectOn σ h)
    (htail : ∀ c ∈ t, IsSubgamePerfectOn σ c) :
    IsSubgamePerfectOn σ (Node m h t) :=
  (isSubgamePerfectOn_Node_iff).mpr ⟨hnash, hhead, htail⟩

/-- Root-scoped subgame perfection at a nonterminal node is equivalent to root
    Nash equilibrium plus root-scoped subgame perfection on every child in the
    public `children` list. -/
theorem isSubgamePerfectOn_Node_iff_children
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)} :
    IsSubgamePerfectOn σ (Node m h t) ↔
      IsNashAt σ (Node m h t) ∧
        ∀ c ∈ children (Node m h t), IsSubgamePerfectOn σ c := by
  rw [isSubgamePerfectOn_Node_iff]
  constructor
  · rintro ⟨hnash, hhead, htail⟩
    refine ⟨hnash, ?_⟩
    intro c hmem
    rcases List.mem_cons.mp (by simpa [children] using hmem) with rfl | hmem'
    · exact hhead
    · exact htail c hmem'
  · rintro ⟨hnash, hchildren⟩
    refine ⟨hnash, ?_, ?_⟩
    · exact hchildren h (by simp [children])
    · intro c hmem
      exact hchildren c (by simp [children, hmem])

/-- Root-scoped subgame perfection at a nonterminal node gives root Nash
    equilibrium together with root-scoped subgame perfection on every child in
    the public `children` list. -/
theorem IsSubgamePerfectOn.toNashAt_and_children
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hspe : IsSubgamePerfectOn σ (Node m h t)) :
    IsNashAt σ (Node m h t) ∧
      ∀ c ∈ children (Node m h t), IsSubgamePerfectOn σ c :=
  (isSubgamePerfectOn_Node_iff_children).mp hspe

/-- Root Nash equilibrium at a node, together with root-scoped subgame
    perfection on every child in the public `children` list, gives root-scoped
    subgame perfection at the node. -/
theorem IsNashAt.toSubgamePerfectOn_Node_of_children
    {σ : Strategy ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)}
    (hnash : IsNashAt σ (Node m h t))
    (hchildren : ∀ c ∈ children (Node m h t), IsSubgamePerfectOn σ c) :
    IsSubgamePerfectOn σ (Node m h t) :=
  (isSubgamePerfectOn_Node_iff_children).mpr ⟨hnash, hchildren⟩

/-- Existence of one strategy satisfying the head/tail recursive SPE check at
    a node is equivalent to existence of a root-scoped SPE at that node. -/
theorem exists_isNashAt_and_child_isSubgamePerfectOn_iff_exists_isSubgamePerfectOn_Node
    (m : ι) (h : GameTree ι U) (t : List (GameTree ι U)) :
    (∃ σ : Strategy ι U,
      IsNashAt σ (Node m h t) ∧
        IsSubgamePerfectOn σ h ∧
          ∀ c ∈ t, IsSubgamePerfectOn σ c) ↔
      ∃ σ : Strategy ι U, IsSubgamePerfectOn σ (Node m h t) := by
  constructor
  · rintro ⟨σ, hnash, hhead, htail⟩
    exact ⟨σ, hnash.toSubgamePerfectOn_Node hhead htail⟩
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, hspe.toNashAt_and_head_tail⟩

/-- Existence of one strategy satisfying the children-list recursive SPE check
    at a node is equivalent to existence of a root-scoped SPE at that node. -/
theorem exists_isNashAt_and_children_isSubgamePerfectOn_iff_exists_isSubgamePerfectOn_Node
    (m : ι) (h : GameTree ι U) (t : List (GameTree ι U)) :
    (∃ σ : Strategy ι U,
      IsNashAt σ (Node m h t) ∧
        ∀ c ∈ children (Node m h t), IsSubgamePerfectOn σ c) ↔
      ∃ σ : Strategy ι U, IsSubgamePerfectOn σ (Node m h t) := by
  constructor
  · rintro ⟨σ, hnash, hchildren⟩
    exact ⟨σ, hnash.toSubgamePerfectOn_Node_of_children hchildren⟩
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, hspe.toNashAt_and_children⟩

/-- If a tree has no proper subgames, root Nash equilibrium already implies
    subgame perfection on that tree. This is the pure finite-tree form of
    MSZ Theorem 7.4. -/
theorem IsNashAt.toSubgamePerfectOn_of_hasOnlyRootSubgames
    {σ : Strategy ι U} {g : GameTree ι U}
    (hnash : IsNashAt σ g) (hsubgames : HasOnlyRootSubgames g) :
    IsSubgamePerfectOn σ g := by
  intro s hsg i σ' hiv
  have hs : s = g := hsubgames s hsg
  subst hs
  exact hnash i σ' hiv

/-- On a tree with no proper subgames, root-scoped subgame perfection is
    equivalent to root Nash equilibrium. This is the iff form of the pure
    finite-tree version of MSZ Theorem 7.4. -/
theorem isSubgamePerfectOn_iff_isNashAt_of_hasOnlyRootSubgames
    {σ : Strategy ι U} {g : GameTree ι U} (hsubgames : HasOnlyRootSubgames g) :
    IsSubgamePerfectOn σ g ↔ IsNashAt σ g := by
  constructor
  · intro hspe
    exact hspe.toNashAt
  · intro hnash
    exact hnash.toSubgamePerfectOn_of_hasOnlyRootSubgames hsubgames

/-- If the root has no proper subgame, then root Nash equilibrium and
    root-scoped subgame perfection coincide. This is the pure finite-tree form
    of MSZ Theorem 7.4. -/
theorem isSubgamePerfectOn_iff_isNashAt_of_no_properSubgame
    {σ : Strategy ι U} {g : GameTree ι U}
    (hnoProper : ¬ ∃ s : GameTree ι U, ProperSubgame s g) :
    IsSubgamePerfectOn σ g ↔ IsNashAt σ g :=
  isSubgamePerfectOn_iff_isNashAt_of_hasOnlyRootSubgames
    ((hasOnlyRootSubgames_iff_no_properSubgame g).mpr hnoProper)

/-- On a tree with no proper subgames, existence of root-scoped subgame
    perfection is equivalent to existence of root Nash equilibrium. -/
theorem exists_isSubgamePerfectOn_iff_exists_isNashAt_of_hasOnlyRootSubgames
    (g : GameTree ι U) (hsubgames : HasOnlyRootSubgames g) :
    (∃ σ : Strategy ι U, IsSubgamePerfectOn σ g) ↔
      ∃ σ : Strategy ι U, IsNashAt σ g := by
  constructor
  · rintro ⟨σ, hspe⟩
    exact ⟨σ, hspe.toNashAt⟩
  · rintro ⟨σ, hnash⟩
    exact ⟨σ, hnash.toSubgamePerfectOn_of_hasOnlyRootSubgames hsubgames⟩

/-- If the root has no proper subgame, existence of root-scoped subgame
    perfection is equivalent to existence of root Nash equilibrium. -/
theorem exists_isSubgamePerfectOn_iff_exists_isNashAt_of_no_properSubgame
    (g : GameTree ι U)
    (hnoProper : ¬ ∃ s : GameTree ι U, ProperSubgame s g) :
    (∃ σ : Strategy ι U, IsSubgamePerfectOn σ g) ↔
      ∃ σ : Strategy ι U, IsNashAt σ g :=
  exists_isSubgamePerfectOn_iff_exists_isNashAt_of_hasOnlyRootSubgames g
    ((hasOnlyRootSubgames_iff_no_properSubgame g).mpr hnoProper)

/-- The canonical backward-induction strategy is root-scoped subgame-perfect
    at every finite perfect-information root. -/
theorem optStrategy_isSubgamePerfectOn (g : GameTree ι U) :
    IsSubgamePerfectOn (optStrategy : Strategy ι U) g :=
  optStrategy_isSubgamePerfect.toSubgamePerfectOn g

/-- The canonical backward-induction strategy is Nash at every finite
    perfect-information root. -/
theorem optStrategy_isNashAt (g : GameTree ι U) :
    IsNashAt (optStrategy : Strategy ι U) g :=
  optStrategy_isSubgamePerfect.toNashAt g

/-- The canonical backward-induction strategy is root-scoped subgame-perfect
    on every subtree of a fixed finite perfect-information root. -/
theorem optStrategy_isSubgamePerfectOn_subtree {s g : GameTree ι U}
    (hsub : Subtree s g) :
    IsSubgamePerfectOn (optStrategy : Strategy ι U) s :=
  (optStrategy_isSubgamePerfectOn g).of_subtree hsub

/-- The canonical backward-induction strategy is Nash at every subtree of a
    fixed finite perfect-information root. -/
theorem optStrategy_isNashAt_subtree {s g : GameTree ι U}
    (hsub : Subtree s g) :
    IsNashAt (optStrategy : Strategy ι U) s :=
  (optStrategy_isSubgamePerfectOn g).toNashAt_of_subtree hsub

/-- The canonical backward-induction strategy is root-scoped subgame-perfect
    on every proper subgame of a fixed finite perfect-information root. -/
theorem optStrategy_isSubgamePerfectOn_properSubgame {s g : GameTree ι U}
    (hproper : ProperSubgame s g) :
    IsSubgamePerfectOn (optStrategy : Strategy ι U) s :=
  (optStrategy_isSubgamePerfectOn g).of_properSubgame hproper

/-- The canonical backward-induction strategy is Nash at every proper subgame
    of a fixed finite perfect-information root. -/
theorem optStrategy_isNashAt_properSubgame {s g : GameTree ι U}
    (hproper : ProperSubgame s g) :
    IsNashAt (optStrategy : Strategy ι U) s :=
  (optStrategy_isSubgamePerfectOn g).toNashAt_of_properSubgame hproper

/-- **Kuhn's theorem, NE form**: every finite perfect-information game
    without chance has a pure-strategy Nash equilibrium. -/
theorem Kuhn_exists_NE (g : GameTree ι U) :
    ∃ σ : Strategy ι U, IsNashEquilibrium σ g := by
  exact ⟨optStrategy, optStrategy_isNashAt g⟩

/-- **Kuhn's theorem, root-scoped SPE form**: every finite perfect-information
    game without chance has a pure strategy that is subgame-perfect on that
    root. -/
theorem Kuhn_exists_SPE_on (g : GameTree ι U) :
    ∃ σ : Strategy ι U, IsSubgamePerfectOn σ g := by
  exact ⟨optStrategy, optStrategy_isSubgamePerfectOn g⟩

/-- **Kuhn's theorem, all-roots SPE-on form**: one pure strategy is
    root-scoped subgame-perfect at every finite perfect-information root. -/
theorem Kuhn_exists_SPE_on_all_roots :
    ∃ σ : Strategy ι U, ∀ g : GameTree ι U, IsSubgamePerfectOn σ g := by
  exact ⟨optStrategy, optStrategy_isSubgamePerfectOn⟩

/-- **Kuhn's theorem, all-roots NE form**: one pure strategy is Nash at every
    finite perfect-information root. -/
theorem Kuhn_exists_NE_on_all_roots :
    ∃ σ : Strategy ι U, ∀ g : GameTree ι U, IsNashAt σ g := by
  exact ⟨optStrategy, optStrategy_isNashAt⟩

/-- **Kuhn's theorem, subtree SPE form**: every finite perfect-information game
    without chance has a pure strategy that is subgame-perfect on every subtree
    of a fixed root. -/
theorem Kuhn_exists_SPE_on_subtrees (g : GameTree ι U) :
    ∃ σ : Strategy ι U,
      ∀ s : GameTree ι U, Subtree s g → IsSubgamePerfectOn σ s := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE_on g
  exact ⟨σ, hspe.forall_subtree_isSubgamePerfectOn⟩

/-- **Kuhn's theorem, subtree Nash form**: every finite perfect-information game
    without chance has a pure strategy that is Nash at every subtree of a fixed
    root. -/
theorem Kuhn_exists_NE_on_subtrees (g : GameTree ι U) :
    ∃ σ : Strategy ι U,
      ∀ s : GameTree ι U, Subtree s g → IsNashAt σ s := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE_on g
  exact ⟨σ, hspe.forall_subtree_isNashAt⟩

/-- **Kuhn's theorem, fixed-subtree SPE form**: every subtree of a finite
    perfect-information game has a pure strategy that is subgame-perfect at
    that subtree root. -/
theorem Kuhn_exists_SPE_on_subtree {s g : GameTree ι U} (_hsub : Subtree s g) :
    ∃ σ : Strategy ι U, IsSubgamePerfectOn σ s :=
  Kuhn_exists_SPE_on s

/-- **Kuhn's theorem, fixed-subtree Nash form**: every subtree of a finite
    perfect-information game has a pure-strategy Nash equilibrium at that
    subtree root. -/
theorem Kuhn_exists_NE_on_subtree {s g : GameTree ι U} (_hsub : Subtree s g) :
    ∃ σ : Strategy ι U, IsNashAt σ s := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE_on_subtree _hsub
  exact ⟨σ, hspe.toNashAt⟩

/-- **Kuhn's theorem, proper-subgame SPE form**: every finite
    perfect-information game has a pure strategy that is subgame-perfect on
    every proper subgame of a fixed root. -/
theorem Kuhn_exists_SPE_on_properSubgames (g : GameTree ι U) :
    ∃ σ : Strategy ι U,
      ∀ s : GameTree ι U, ProperSubgame s g → IsSubgamePerfectOn σ s := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE_on g
  exact ⟨σ, hspe.forall_properSubgame_isSubgamePerfectOn⟩

/-- **Kuhn's theorem, proper-subgame Nash form**: every finite
    perfect-information game has a pure strategy that is Nash at every proper
    subgame of a fixed root. -/
theorem Kuhn_exists_NE_on_properSubgames (g : GameTree ι U) :
    ∃ σ : Strategy ι U,
      ∀ s : GameTree ι U, ProperSubgame s g → IsNashAt σ s := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE_on g
  exact ⟨σ, hspe.forall_properSubgame_isNashAt⟩

/-- **Kuhn's theorem, fixed proper-subgame SPE form**: every proper subgame of
    a finite perfect-information game has a pure strategy that is
    subgame-perfect at that subgame root. -/
theorem Kuhn_exists_SPE_on_properSubgame {s g : GameTree ι U}
    (hproper : ProperSubgame s g) :
    ∃ σ : Strategy ι U, IsSubgamePerfectOn σ s :=
  Kuhn_exists_SPE_on_subtree hproper.toSubtree

/-- **Kuhn's theorem, fixed proper-subgame Nash form**: every proper subgame of
    a finite perfect-information game has a pure-strategy Nash equilibrium at
    that subgame root. -/
theorem Kuhn_exists_NE_on_properSubgame {s g : GameTree ι U}
    (hproper : ProperSubgame s g) :
    ∃ σ : Strategy ι U, IsNashAt σ s :=
  Kuhn_exists_NE_on_subtree hproper.toSubtree

/-- **Kuhn's theorem, root/proper-subgame Nash form**: every finite
    perfect-information game has one pure strategy that is Nash at the root and
    Nash at every proper subgame. -/
theorem Kuhn_exists_NE_and_NE_on_properSubgames (g : GameTree ι U) :
    ∃ σ : Strategy ι U,
      IsNashAt σ g ∧
        ∀ s : GameTree ι U, ProperSubgame s g → IsNashAt σ s := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE_on g
  exact ⟨σ, hspe.toNashAt_and_forall_properSubgame_isNashAt⟩

/-- **Kuhn's theorem, root Nash/proper-subgame SPE form**: every finite
    perfect-information game has one pure strategy that is Nash at the root and
    subgame-perfect on every proper subgame. -/
theorem Kuhn_exists_NE_and_SPE_on_properSubgames (g : GameTree ι U) :
    ∃ σ : Strategy ι U,
      IsNashAt σ g ∧
        ∀ s : GameTree ι U, ProperSubgame s g → IsSubgamePerfectOn σ s := by
  obtain ⟨σ, hspe⟩ := Kuhn_exists_SPE_on g
  exact ⟨σ, hspe.toNashAt_and_forall_properSubgame_isSubgamePerfectOn⟩

end GameTree
