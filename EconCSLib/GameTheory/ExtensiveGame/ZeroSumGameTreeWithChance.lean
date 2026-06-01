/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.GameTheory.ExtensiveGame.ZeroSumGameTreeWithChance

**2-player zero-sum extensive game with rational chance (Nature) nodes.**

This module sits strictly between the chance-free `Zermelo.lean` and the
fully general `StochasticGameTree.lean` (which requires vNM utility theory).
Because payoffs and probabilities are both in `ℚ`, rational arithmetic suffices
for chance averaging — no vNM theorem is needed.

Ported from `math-xmum/gametheory` (finitegame branch),
`GameTheory/ZerosumFiniteGame.lean`, with EconCSLib-style docstrings and
targeted imports (no `import Mathlib`).

## Design

```
inductive GameTree
  | Leaf  (val : ℚ)                          -- terminal payoff for player A
  | Pnode (p : Player) (L R : GameTree)       -- player decision node (binary)
  | Nnode (p : Set.Icc (0:ℚ) 1) (L R : GameTree)  -- chance node (prob p → L)
```

`value : GameTree → ℚ` computes the backward-induction value for player A:
* Leaf  → the leaf payoff.
* Player A node → max of children's values.
* Player B node → min of children's values.
* Nature node   → probability-weighted average of children's values.

`DStrategy : Strategy` is A's canonical optimal (dominant) strategy:
always choose the child with the higher `value`.

`value_prop` is the soundness theorem: for every B-strategy `SB`,
`t.value ≤ t.outcome DStrategy SB`.

## Main definitions

* `ZeroSumChance.Player` — two players: `A` (maximizer) and `B` (minimizer).
* `ZeroSumChance.Select` — binary selection: `l` (left) or `r` (right).
* `ZeroSumChance.GameTree` — inductive binary game tree with Nature.
* `ZeroSumChance.GameTree.value` — backward-induction value (computable).
* `ZeroSumChance.GameTree.DStrategy` — dominant strategy for A.
* `ZeroSumChance.GameTree.outcome` — outcome under a strategy pair.
* `ZeroSumChance.GameTree.value_prop` — `t.value ≤ t.outcome DStrategy SB`.

## References

* Ported from `math-xmum/gametheory` finitegame branch, `ZerosumFiniteGame.lean`.
* [MSZ] Maschler, Solan, Zamir, *Game Theory*, §3.6 (Zermelo / finite games).

## Related modules

* `EconCSLib.GameTheory.ExtensiveGame.Zermelo` — the chance-free variant.
* `EconCSLib.GameTheory.ExtensiveGame.StochasticGameTree` — n-player general utility (needs vNM).
-/

namespace ZeroSumChance

/-! ### Players and binary selection -/

/-- The two players in a zero-sum game: A is the maximizer, B is the minimizer. -/
inductive Player
  | A : Player  -- Alice, maximizer
  | B : Player  -- Bob, minimizer
  deriving Repr, DecidableEq

/-- A binary choice: `l` = left branch, `r` = right branch. -/
inductive Select
  | l : Select  -- left
  | r : Select  -- right
  deriving Repr, DecidableEq

/-! ### Game tree -/

/-- A finite binary game tree for a 2-player zero-sum game with Nature.

    * `Leaf val`          — terminal node; `val` is A's payoff (B gets `-val`).
    * `Pnode p L R`       — player `p`'s decision node; player chooses L or R.
    * `Nnode prob L R`    — Nature's chance node; Nature picks L with probability
                            `prob ∈ [0,1]` and R with probability `1 - prob`. -/
inductive GameTree : Type
  | Leaf  (val : ℚ)                                           : GameTree
  | Pnode (p : Player) (L R : GameTree)                       : GameTree
  | Nnode (prob : Set.Icc (0 : ℚ) 1) (L R : GameTree)        : GameTree
  deriving Repr, DecidableEq

instance : Inhabited GameTree := ⟨.Leaf 0⟩

namespace GameTree

/-! ### Structural size -/

/-- Structural size of a game tree (used internally for well-founded reasoning). -/
def size : GameTree → ℕ
  | Leaf _      => 1
  | Pnode _ L R => L.size + R.size
  | Nnode _ L R => L.size + R.size

/-- Every game tree has positive size. -/
lemma size_pos (t : GameTree) : 1 ≤ t.size := by
  induction t with
  | Leaf _      => simp [size]
  | Pnode _ L R => simp [size]; linarith
  | Nnode _ L R => simp [size]; linarith

/-! ### Strategies and value -/

/-- A pure strategy is a function that, given a player's decision node, selects
    one of the two branches. `Strategy ≝ GameTree → GameTree → Select`. -/
abbrev Strategy := GameTree → GameTree → Select

/-- The backward-induction value of the game tree for player A.

    * A-node: A maximizes, so we take the max of both children's values.
    * B-node: B minimizes, so we take the min of both children's values.
    * Nature node: probability-weighted average (rational arithmetic). -/
def value : GameTree → ℚ
  | Leaf r      => r
  | Pnode p L R => match p with
    | .A => max L.value R.value
    | .B => min L.value R.value
  | Nnode prob L R => prob * L.value + (1 - prob) * R.value

/-- **A's dominant strategy**: at each A-node, move to whichever child has the
    higher value; ties go left. -/
def DStrategy : Strategy :=
  fun L R => if L.value < R.value then .r else .l

/-! ### Outcome under a strategy pair -/

/-- The realized payoff for player A when A plays `SA` and B plays `SB`.

    Nature's moves are resolved by their fixed probabilities. -/
def outcome (SA SB : Strategy) : GameTree → ℚ
  | Leaf r      => r
  | Pnode p L R => match p with
    | .A => match SA L R with
      | .l => outcome SA SB L
      | .r => outcome SA SB R
    | .B => match SB L R with
      | .l => outcome SA SB L
      | .r => outcome SA SB R
  | Nnode prob L R => prob * outcome SA SB L + (1 - prob) * outcome SA SB R

/-! ### Main theorem -/

/-- **Soundness of `DStrategy`**: the backward-induction value is a lower bound
    on the outcome A achieves by following `DStrategy`, regardless of how B plays.

    Formally: for every B-strategy `SB` and game tree `t`,
    `t.value ≤ t.outcome DStrategy SB`. -/
theorem value_prop (SB : Strategy) {t : GameTree} : t.value ≤ t.outcome DStrategy SB := by
  induction t with
  | Leaf r =>
    simp [outcome, value]
  | Pnode p L R HL HR =>
    match p with
    | Player.A =>
      rw [value, outcome, DStrategy]
      split_ifs with h
      · -- DStrategy picked R (L.value < R.value); goal: max L.value R.value ≤ outcome … R
        exact (max_le (le_of_lt h |>.trans HR) HR)
      · -- DStrategy picked L (¬ L.value < R.value, i.e. R.value ≤ L.value)
        -- goal: max L.value R.value ≤ outcome … L
        exact (max_le HL (not_lt.mp h |>.trans HL))
    | Player.B =>
      rw [value, outcome]
      cases SB L R
      · -- B chose L
        exact min_le_left L.value R.value |>.trans HL
      · -- B chose R
        exact min_le_right L.value R.value |>.trans HR
  | Nnode prob L R HL HR =>
    rw [outcome, value]
    have hpL : (prob : ℚ) * L.value ≤ prob * outcome DStrategy SB L :=
      mul_le_mul_of_nonneg_left HL prob.2.1
    have hpR : (1 - prob) * R.value ≤ (1 - prob) * outcome DStrategy SB R :=
      mul_le_mul_of_nonneg_left HR (by linarith [prob.2.2])
    linarith

end GameTree

/-! ### Notation helpers -/

/-- Coerce a rational `a` to the unit-interval subtype, defaulting to `⟨0, …⟩` if
    `a ∉ [0, 1]`. -/
def PUInterval (a : ℚ) : Set.Icc (0 : ℚ) 1 :=
  if h : 0 ≤ a ∧ a ≤ 1 then ⟨a, h⟩ else ⟨0, le_refl _, zero_le_one⟩

notation:100 "[L " v:101 "]"               => GameTree.Leaf v
notation:100 "[N " p:100 ", " L:100 ", " R:100 "]" => GameTree.Nnode (PUInterval p) L R
notation:100 "[A " L:100 ", " R:100 "]"   => GameTree.Pnode Player.A L R
notation:100 "[B " L:100 ", " R:100 "]"   => GameTree.Pnode Player.B L R

/-! ### Quick smoke test -/

section Example

/-- A small example: B node with an A subgame on the left and a leaf on the right. -/
private def T : GameTree := [B [A [L 10], [L (-10)]] , [L 3]]

/-- T with a 50/50 Nature node at the root. -/
private def T' : GameTree := [N (1/2 : ℚ), T, T]

#eval T.value   -- expected: 3
#eval T'.value  -- expected: 3

end Example

end ZeroSumChance
