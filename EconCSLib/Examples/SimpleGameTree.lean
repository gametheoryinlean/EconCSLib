/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Zermelo
import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm

/-!
# EconCSLib.Examples.SimpleGameTree

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

-- Sanity: the game is well-typed.
example : GameTree Player ℚ := sample

-- `value` is computable (backward induction over the decidable order `≤` on `ℚ`),
-- so the value evaluates and is machine-checkable on this concrete game.
#eval value₀ sample          -- 3  (B picks min{10, 3} = 3)
#eval value sample 0         -- 3
#eval value sample 1         -- -3

/-- The player-0 value of the sample is `3`, checked by computation. -/
example : value₀ sample = 3 := by decide

/-- The zero-sum predicate holds on the sample game. -/
theorem sample_zero_sum : IsZeroSum sample := by
  simp [sample, IsZeroSum, zeroSumLeaf]

/-- **Existence of an SPE** for the sample game (via `Kuhn_exists_SPE`). -/
example : ∃ σ : Strategy Player ℚ, IsSubgamePerfect σ := Kuhn_exists_SPE

/-- Pure root-scoped SPE existence for the sample (Kuhn's theorem; no zero-sum
    hypothesis required). -/
theorem sample_zermelo_spe : ∃ σ : Strategy Player ℚ, IsSubgamePerfectOn σ sample :=
  zermelo_exists_pure_SPE sample

/-- Pure root Nash existence for the sample (Kuhn's theorem). -/
theorem sample_zermelo_ne :
    ∃ σ : Strategy Player ℚ, GameTree.IsNashEquilibrium σ sample :=
  zermelo_exists_pure_NE sample

/-- **Zermelo determinacy on the sample**: `optStrategy` is a saddle with value
    `value₀ sample` — player 0 secures it, player 1 caps it. This is the result
    that genuinely uses the zero-sum hypothesis `sample_zero_sum`. -/
theorem sample_zermelo_determinacy :
    (∀ σ' : Strategy Player ℚ, IVariant (1 : Player) optStrategy σ' →
        value₀ sample ≤ outcome σ' sample 0) ∧
    (∀ σ' : Strategy Player ℚ, IVariant (0 : Player) optStrategy σ' →
        outcome σ' sample 0 ≤ value₀ sample) :=
  zermelo_determinacy sample sample_zero_sum

/-- A one-leaf game has only its root as a subgame. -/
theorem leaf_hasOnlyRootSubgames (p : Player → ℚ) :
    HasOnlyRootSubgames (Leaf p : GameTree Player ℚ) := by
  intro s hsub
  cases hsub
  rfl

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
  optStrategy_isSubgamePerfect.toSubgamePerfectOn sample

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
