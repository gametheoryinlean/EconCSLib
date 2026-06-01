/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic

/-!
# EconCSLib.GameTheory.ExtensiveGame.StochasticGameTree

Finite perfect-information game trees with explicit chance nodes.

This module intentionally keeps stochastic trees separate from the existing
no-chance `GameTree` type.  Chance nodes carry rational weights on a nonempty
finite successor list; the local probability-sum condition is a predicate rather
than a constructor field, so the recursive data type stays lightweight.

## Main definitions

* `StochasticGameTree` — terminal, player, and chance nodes.
* `StochasticGameTree.ChanceProbabilitiesSumToOne` — local probability check.
* `StochasticGameTree.Strategy` — pure contingent plans at player nodes.
* `StochasticGameTree.expectedPayoffWithFuel` — executable fuel-bounded
  expected-payoff evaluator.
* `StochasticGameTree.expectedPayoff` — expected payoff using tree-size fuel.
* `StochasticGameTree.ofGameTree` — embed ordinary no-chance trees.
-/

inductive StochasticGameTree (N : Type*) : Type _
  | Leaf (payoff : N → ℚ) : StochasticGameTree N
  | Player (mover : N) (head : StochasticGameTree N) (tail : List (StochasticGameTree N)) :
      StochasticGameTree N
  | Chance (headProb : ℚ) (head : StochasticGameTree N)
      (tail : List (ℚ × StochasticGameTree N)) : StochasticGameTree N

namespace StochasticGameTree

variable {N : Type*}

/-- A pure strategy chooses a child at every player-controlled node. -/
def Strategy (N : Type*) : Type _ :=
  (m : N) → (h : StochasticGameTree N) → (t : List (StochasticGameTree N)) →
    { c : StochasticGameTree N // c ∈ h :: t }

/-- The trivial head-selecting strategy, useful for examples that have no
    strategically relevant player choice. -/
def headStrategy : Strategy N :=
  fun _ h _ => ⟨h, List.mem_cons_self⟩

/-- Embed an ordinary no-chance `GameTree` into the stochastic tree layer. -/
def ofGameTree : GameTree N ℚ → StochasticGameTree N
  | GameTree.Leaf p => StochasticGameTree.Leaf p
  | GameTree.Node m h t => StochasticGameTree.Player m (ofGameTree h) (t.map ofGameTree)

/-- Local probability mass check at a chance node. -/
def ChanceProbabilitiesSumToOne (headProb : ℚ) (tail : List (ℚ × StochasticGameTree N)) :
    Prop :=
  headProb + (tail.map Prod.fst).sum = 1

/-- Fuel-bounded expected payoff under a pure strategy.  If fuel runs out, the
    default payoff is zero; `expectedPayoff` below supplies tree-size fuel. -/
noncomputable def expectedPayoffWithFuel (fuel : ℕ) (σ : Strategy N)
    (g : StochasticGameTree N) (i : N) : ℚ :=
  match fuel with
  | 0 => 0
  | n + 1 =>
      match g with
      | Leaf p => p i
      | Player m h t => expectedPayoffWithFuel n σ (σ m h t).val i
      | Chance p h t =>
          p * expectedPayoffWithFuel n σ h i +
            (t.map (fun child => child.1 * expectedPayoffWithFuel n σ child.2 i)).sum

/-- Expected payoff with enough fuel for every branch of the finite tree. -/
noncomputable def expectedPayoff (σ : Strategy N) (g : StochasticGameTree N) (i : N) :
    ℚ :=
  expectedPayoffWithFuel (sizeOf g) σ g i

/-- A one-step fair coin game for examples and CI regression checks. -/
def fairCoinGame : StochasticGameTree (Fin 2) :=
  StochasticGameTree.Chance (1 / 2)
    (StochasticGameTree.Leaf (fun i => if i = 0 then 1 else 0))
    (List.cons
      (1 / 2, StochasticGameTree.Leaf (fun i => if i = 0 then 0 else 1))
      List.nil)

theorem fairCoin_probs_sum_to_one :
    ChanceProbabilitiesSumToOne (1 / 2)
      (List.cons
        (1 / 2, StochasticGameTree.Leaf (fun i : Fin 2 => if i = 0 then 0 else 1))
        List.nil) := by
  norm_num [ChanceProbabilitiesSumToOne]

theorem fairCoin_expected_player0 :
    expectedPayoff (headStrategy : Strategy (Fin 2)) fairCoinGame 0 = 1 / 2 := by
  norm_num [expectedPayoff, expectedPayoffWithFuel, fairCoinGame, headStrategy]

end StochasticGameTree
