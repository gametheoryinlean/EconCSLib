/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Zermelo
import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm

/-!
# Examples.SimpleGameTree

A sample 2-player zero-sum perfect-info game expressed in the
`GameTree` framework, used to smoke-test `value`, `Kuhn_exists_SPE`,
root-scoped Nash equilibrium, and the Zermelo-style zero-sum API.

The game (adapted from `ZerosumFiniteGame.lean`):

```
         [B]
        /    \
      [A]    (3)
     /   \
   (10) (-10)
```

* Player B (index 1) moves first, picks left (to A's subgame) or right (payoff 3).
* Player A (index 0) moves in the subgame, picks left (10) or right (-10).

Values represent payoff to Player 0 (A). In the zero-sum reading,
Player 1 (B) gets the negation.

Backward induction:
* A's subgame: A picks max{10, -10} = 10.
* B's full game: B picks min{10, 3} = 3.

So `value g 0 = 3`.
-/

namespace Examples.SimpleGameTree

open GameTree

/-- Two players: 0 = A (maximizer), 1 = B (minimizer). -/
abbrev Player := Fin 2

/-- Leaf payoff vector — Player 0 gets `v`, Player 1 gets `-v` (zero-sum). -/
def zeroSumLeaf (v : ℚ) : Player → ℚ
  | ⟨0, _⟩ => v
  | ⟨1, _⟩ => -v

/-- The sample game tree (see module docstring). -/
def sample : GameTree Player ℚ :=
  Node (1 : Player)                                                         -- B's turn
    (Node (0 : Player)                                                      -- A's subgame
      (Leaf (zeroSumLeaf 10))
      (List.cons (Leaf (zeroSumLeaf (-10))) List.nil))
    (List.cons (Leaf (zeroSumLeaf 3)) List.nil)

/-- Player A's proper subgame inside `sample`. -/
def sampleLeftSubgame : GameTree Player ℚ :=
  Node (0 : Player)
    (Leaf (zeroSumLeaf 10))
    (List.cons (Leaf (zeroSumLeaf (-10))) List.nil)

-- Sanity: the game is well-typed. (Deeper `#eval` checks are blocked by
-- the noncomputable `value` relying on classical choice.)
example : GameTree Player ℚ := sample

/-- The zero-sum predicate holds on the sample game. -/
theorem sample_zero_sum : IsZeroSum sample := by
  simp [sample, IsZeroSum, zeroSumLeaf]

/-- **Existence of an SPE** for the sample game (via `Kuhn_exists_SPE`). -/
example : ∃ σ : Strategy Player ℚ, IsSubgamePerfect σ := Kuhn_exists_SPE

/-- Zermelo-style pure SPE existence for the zero-sum sample. -/
theorem sample_zermelo_spe : ∃ σ : Strategy Player ℚ, IsSubgamePerfect σ :=
  zermelo_exists_pure_SPE sample sample_zero_sum

/-- Zermelo-style pure root Nash existence for the zero-sum sample. -/
theorem sample_zermelo_ne :
    ∃ σ : Strategy Player ℚ, GameTree.IsNashEquilibrium σ sample :=
  zermelo_exists_pure_NE sample sample_zero_sum

/-- A one-leaf game has only its root as a subgame. -/
theorem leaf_hasOnlyRootSubgames (p : Player → ℚ) :
    HasOnlyRootSubgames (Leaf p : GameTree Player ℚ) :=
  hasOnlyRootSubgames_Leaf p

/-- On a game with no proper subgames, root Nash already gives the corresponding
    root-scoped subgame-perfect condition. This instantiates the pure finite-tree
    form of MSZ Theorem 7.4 on a one-leaf game. -/
theorem leaf_nash_to_spe_on (p : Player → ℚ) {σ : Strategy Player ℚ}
    (hnash : GameTree.IsNashAt σ (Leaf p)) :
    IsSubgamePerfectOn σ (Leaf p) :=
  hnash.toSubgamePerfectOn_of_hasOnlyRootSubgames (leaf_hasOnlyRootSubgames p)

/-- The backward-induction value of the sample remains zero-sum. -/
theorem sample_value_zero_sum : (value sample) 0 + (value sample) 1 = 0 :=
  value_zero_sum sample sample_zero_sum

/-- The backward-induction strategy is subgame-perfect on the sample root. -/
theorem sample_optStrategy_spe_on :
    IsSubgamePerfectOn (optStrategy : Strategy Player ℚ) sample :=
  optStrategy_isSubgamePerfectOn sample

/-- The global SPE predicate is equivalent to root-scoped SPE at every root. -/
theorem sample_optStrategy_global_spe_iff_roots :
    IsSubgamePerfect (optStrategy : Strategy Player ℚ) ↔
      ∀ g : GameTree Player ℚ,
        IsSubgamePerfectOn (optStrategy : Strategy Player ℚ) g :=
  isSubgamePerfect_iff_forall_isSubgamePerfectOn

/-- The global backward-induction SPE is Nash at the sample root. -/
theorem sample_optStrategy_nash_at :
    IsNashAt (optStrategy : Strategy Player ℚ) sample :=
  optStrategy_isNashAt sample

/-- The left child is Player A's proper subgame in the sample tree. -/
theorem sample_left_subgame :
    Subtree sampleLeftSubgame sample := by
  unfold sample
  change Subtree sampleLeftSubgame
    (Node (1 : Player) sampleLeftSubgame
      (List.cons (Leaf (zeroSumLeaf 3)) List.nil))
  exact Subtree.head (1 : Player)
    sampleLeftSubgame
    (List.cons (Leaf (zeroSumLeaf 3)) List.nil)

/-- The left child is a nontrivial subgame, not just a reflexive subtree. -/
theorem sample_left_properSubgame :
    ProperSubgame sampleLeftSubgame sample := by
  unfold sample
  change ProperSubgame sampleLeftSubgame
    (Node (1 : Player) sampleLeftSubgame
      (List.cons (Leaf (zeroSumLeaf 3)) List.nil))
  exact ProperSubgame.head (1 : Player)
    sampleLeftSubgame
    (List.cons (Leaf (zeroSumLeaf 3)) List.nil)

/-- Root-scoped SPE on the sample restricts to Player A's proper subgame. -/
theorem sample_optStrategy_spe_on_left_subgame :
    IsSubgamePerfectOn (optStrategy : Strategy Player ℚ) sampleLeftSubgame :=
  optStrategy_isSubgamePerfectOn_properSubgame sample_left_properSubgame

/-- Root-scoped SPE on the sample gives Nash equilibrium at Player A's
    proper subgame. -/
theorem sample_optStrategy_nash_at_left_subgame :
    IsNashAt (optStrategy : Strategy Player ℚ) sampleLeftSubgame :=
  optStrategy_isNashAt_properSubgame sample_left_properSubgame

/-- The direct-child convenience theorem gives the same SPE restriction to
    Player A's subgame. -/
theorem sample_optStrategy_spe_on_head :
    IsSubgamePerfectOn (optStrategy : Strategy Player ℚ) sampleLeftSubgame := by
  simpa [sample, sampleLeftSubgame] using
    (sample_optStrategy_spe_on.head
      (m := (1 : Player))
      (h := sampleLeftSubgame)
      (t := List.cons (Leaf (zeroSumLeaf 3)) List.nil))

/-- The direct-child convenience theorem also gives Nash equilibrium at
    Player A's subgame. -/
theorem sample_optStrategy_nash_at_head :
    IsNashAt (optStrategy : Strategy Player ℚ) sampleLeftSubgame := by
  simpa [sample, sampleLeftSubgame] using
    (sample_optStrategy_spe_on.toNashAt_head
      (m := (1 : Player))
      (h := sampleLeftSubgame)
      (t := List.cons (Leaf (zeroSumLeaf 3)) List.nil))

/-- Kuhn's theorem gives one pure strategy that is subgame-perfect on every
    subtree of the sample root. -/
theorem sample_has_spe_on_every_subtree :
    ∃ σ : Strategy Player ℚ,
      ∀ s : GameTree Player ℚ, Subtree s sample → IsSubgamePerfectOn σ s :=
  Kuhn_exists_SPE_on_subtrees sample

/-- The same pure strategy can be viewed as Nash at every subtree of the sample
    root. This is the pure finite-tree subtree-Nash consequence of SPE. -/
theorem sample_has_nash_at_every_subtree :
    ∃ σ : Strategy Player ℚ,
      ∀ s : GameTree Player ℚ, Subtree s sample → IsNashAt σ s :=
  Kuhn_exists_NE_on_subtrees sample

/-- The recursive node characterization splits subgame perfection on `sample`
    into root Nash, SPE on Player A's subgame, and SPE on the right leaf. -/
theorem sample_optStrategy_spe_on_decomposes :
    IsNashAt (optStrategy : Strategy Player ℚ) sample ∧
      IsSubgamePerfectOn (optStrategy : Strategy Player ℚ) sampleLeftSubgame ∧
        ∀ c ∈ List.cons (Leaf (zeroSumLeaf 3)) List.nil,
          IsSubgamePerfectOn (optStrategy : Strategy Player ℚ) c := by
  simpa [sample, sampleLeftSubgame] using
    (isSubgamePerfectOn_Node_iff
      (σ := (optStrategy : Strategy Player ℚ))
      (m := (1 : Player))
      (h := sampleLeftSubgame)
      (t := List.cons (Leaf (zeroSumLeaf 3)) List.nil)).mp
        sample_optStrategy_spe_on

/-- The right terminal branch is automatically Nash for every strategy. -/
theorem sample_right_leaf_nash_at (σ : Strategy Player ℚ) :
    IsNashAt σ (Leaf (zeroSumLeaf 3)) :=
  isNashAt_Leaf σ (zeroSumLeaf 3)

/-- The extracted strategic-form game has a pure Nash equilibrium, and this is
    exactly the root-scoped Nash predicate on the original tree. -/
theorem sample_strategic_form_has_nash :
    ∃ σ : (toStrategicGame sample).Profile,
      IsNashEquilibrium (toStrategicGame sample) σ ∧
        IsNashAt (profileStrategy σ) sample := by
  have hprofile : profileStrategy (fun _ => optStrategy : (toStrategicGame sample).Profile) =
      (optStrategy : Strategy Player ℚ) := rfl
  refine ⟨fun _ => optStrategy, ?_, ?_⟩
  · exact (toStrategicGame_nash_iff_isNashAt sample (fun _ => optStrategy)).mpr
      (by simpa [hprofile] using optStrategy_isSubgamePerfect.toNE sample)
  · simpa [hprofile] using optStrategy_isSubgamePerfect.toNE sample

end Examples.SimpleGameTree
