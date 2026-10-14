/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTree
import EconCSLib.Math.Probability.FiniteLaw
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega

/-!
# EconCSLib.GameTheory.ExtensiveGame.StochasticGameTree

Finite perfect-information game trees with normalized chance nodes.

This module intentionally keeps stochastic trees separate from the existing
no-chance `GameTree` type. A chance node contains a `FiniteLaw` on the finite
nonempty type of child occurrences. Nonnegativity and total mass one are
therefore construction invariants rather than optional side conditions.

Operational player choices are indexed by the path of child indices from the
root. Equal subtree values at different occurrences can consequently receive
different choices.

## Main definitions

* `StochasticGameTree` — terminal, player, and chance nodes.
* `StochasticGameTree.Policy` — occurrence-sensitive pure contingent choices.
* `StochasticGameTree.expectedPayoffWithFuel` — executable fuel-bounded
  expected-payoff evaluator.
* `StochasticGameTree.expectedPayoffAtFuel` — root evaluator at an explicit
  finite horizon.
* `StochasticGameTree.ofGameTree` — embed ordinary no-chance trees.

The occurrence-sensitive compiler and its exact bounded-law theorems live in
`Compiler/StochasticGameTreeObserved.lean`.
-/

inductive StochasticGameTree (N : Type*) : Type _
  | Leaf (payoff : N → ℝ) : StochasticGameTree N
  | Player (mover : N) (arity : ℕ)
      (child : Fin (arity + 1) → StochasticGameTree N) :
      StochasticGameTree N
  | Chance (arity : ℕ)
      (child : Fin (arity + 1) → StochasticGameTree N)
      (law : FiniteLaw (Fin (arity + 1))) :
      StochasticGameTree N

namespace StochasticGameTree

variable {N : Type*}

/-- Turn a nonempty head-and-tail family into a function on its finite child
occurrence type. -/
def childrenOfList (head : StochasticGameTree N)
    (tail : List (StochasticGameTree N)) :
    Fin (tail.length + 1) → StochasticGameTree N
  | ⟨0, _⟩ => head
  | ⟨index + 1, hindex⟩ =>
      tail.get ⟨index, by omega⟩

/-- An occurrence-sensitive pure policy.

The first argument is the path of child indices from the root to the current
player node. It prevents equal subtree values at different occurrences from
being silently identified. -/
def Policy (N : Type*) : Type _ :=
  (path : List ℕ) → (mover : N) →
    (arity : ℕ) →
    (child : Fin (arity + 1) → StochasticGameTree N) →
      Fin (arity + 1)

/-- The head-selecting policy, useful when player choices are irrelevant. -/
def headPolicy : Policy N :=
  fun _path _mover arity _child =>
    ⟨0, Nat.zero_lt_succ arity⟩

mutual
  private def compileGameTree : GameTree N ℝ → StochasticGameTree N
    | GameTree.Leaf payoff => StochasticGameTree.Leaf payoff
    | GameTree.Node mover head tail =>
        let compiledHead := compileGameTree head
        let compiledTail := compileGameTreeList tail
        StochasticGameTree.Player mover compiledTail.length
          (childrenOfList compiledHead compiledTail)

  private def compileGameTreeList : List (GameTree N ℝ) →
      List (StochasticGameTree N)
    | [] => []
    | head :: tail => compileGameTree head :: compileGameTreeList tail
end

/-- Embed an ordinary no-chance real-payoff `GameTree` into the stochastic
tree layer. -/
def ofGameTree (tree : GameTree N ℝ) : StochasticGameTree N :=
  compileGameTree tree

/-- Fuel-bounded expected payoff under an occurrence-sensitive pure policy.

If fuel runs out, the default payoff is zero. At chance nodes this is the
finite expectation under the constructor's normalized law; callers choose
the horizon explicitly through `expectedPayoffAtFuel`. -/
def expectedPayoffWithFuel (fuel : ℕ) (policy : Policy N)
    (path : List ℕ) (g : StochasticGameTree N) (i : N) : ℝ :=
  match fuel with
  | 0 => 0
  | n + 1 =>
      match g with
      | Leaf p => p i
      | Player mover arity child =>
          let choice := policy path mover arity child
          expectedPayoffWithFuel n policy
            (path ++ [choice.1]) (child choice) i
      | Chance _ child law =>
          (law.atoms.map fun atom =>
            (atom.2 : ℝ) *
              expectedPayoffWithFuel n policy
                (path ++ [atom.1.1]) (child atom.1) i).sum

/-- Expected payoff from the root at an explicit finite horizon.

The horizon specifies the truncation, including zero payoff when fuel is
exhausted at a leaf. Since each child function has a finite enumerable domain,
structural recursion can compute a sufficient horizon by taking the maximum
over all children, with fuel one at leaves. An arbitrary supplied horizon need
not reach every leaf. The total-evaluation prototype and its correspondence
proof are in the opt-in `Examples/ExtensiveGame/StochasticTreeCompilation`. -/
def expectedPayoffAtFuel (fuel : ℕ) (policy : Policy N)
    (g : StochasticGameTree N) (i : N) : ℝ :=
  expectedPayoffWithFuel fuel policy [] g i

end StochasticGameTree
