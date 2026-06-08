/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Linarith

/-!
# ExtensiveGame.Zermelo

**Zermelo-style finite game results** as two-player zero-sum consequences of
backward induction and Kuhn's theorem.

Zermelo (1913) established determinacy for finite perfect-information
two-player win/loss/draw games (Chess, in his original paper).
Here we frame it as the special case of Kuhn's theorem where:

* `ι = Fin 2` — exactly two players,
* payoffs are in `ℚ` (any `[LinearOrderedField U]` would do),
* the game is **zero-sum**: `payoff leaf 0 + payoff leaf 1 = 0` at every leaf.

## Main definitions

* `GameTree.IsZeroSum` — the zero-sum predicate on a `GameTree (Fin 2) ℚ`
* `GameTree.value₀` — the value of the game for Player 0.

## Main results

* `IsZeroSum.of_subtree` / `IsZeroSum.of_properSubgame` — zero-sumness is
  inherited by subgames.
* `zermelo_exists_pure_SPE` — every finite 2-player zero-sum perfect-info game
  has a pure-strategy subgame-perfect equilibrium.
* `zermelo_exists_pure_SPE_on` — the root-scoped SPE version.
* `zermelo_exists_pure_NE` — the same game has a pure-strategy Nash equilibrium
  at the root.
* `zermelo_exists_pure_NE_on_subtrees` — one pure strategy is Nash on every
  subtree of the root.
* `zermelo_exists_pure_SPE_on_subtree` /
  `zermelo_exists_pure_NE_on_subtree` — fixed-subtree versions.
* `zermelo_exists_pure_SPE_on_properSubgames` /
  `zermelo_exists_pure_NE_on_properSubgames` — proper-subgame versions.
* `value_zero_sum` — backward induction preserves the zero-sum value invariant.
* `value_one_eq_neg_value₀` — player 1's backward-induction value is the
  negative of player 0's value.
* `value₀_Node_zero_isMax` / `value₀_Node_one_isMin` — the local max/min
  behavior of the zero-sum value at player-0 and player-1 nodes.
* `outcome_optStrategy_zero_sum` — the backward-induction strategy reaches a
  zero-sum terminal outcome.
* `value₀_eq_optStrategy_outcome` — `optStrategy` realizes the player-0 value.

## References

* [Zermelo 1913] *Über eine Anwendung der Mengenlehre auf die Theorie des
  Schachspiels*, Proceedings of the Fifth International Congress of Mathematicians
* [MSZ] Maschler, Solan, Zamir, *Game Theory*, §3.6
-/

namespace GameTree

/-! ### Zero-sum condition -/

/-- A 2-player `GameTree` valued in `ℚ` is **zero-sum** if at every leaf
    the two players' payoffs sum to zero. -/
def IsZeroSum : GameTree (Fin 2) ℚ → Prop
  | Leaf p => p 0 + p 1 = 0
  | Node _ h t => IsZeroSum h ∧ ∀ c ∈ t, IsZeroSum c

/-- The head child of a zero-sum node is zero-sum. -/
theorem IsZeroSum.head {m : Fin 2} {h : GameTree (Fin 2) ℚ}
    {t : List (GameTree (Fin 2) ℚ)} (hzs : IsZeroSum (Node m h t)) :
    IsZeroSum h := by
  have hzs' : IsZeroSum h ∧ ∀ c ∈ t, IsZeroSum c := by
    simpa [IsZeroSum] using hzs
  exact hzs'.1

/-- Every tail child of a zero-sum node is zero-sum. -/
theorem IsZeroSum.tail_mem {m : Fin 2} {h : GameTree (Fin 2) ℚ}
    {t : List (GameTree (Fin 2) ℚ)} {c : GameTree (Fin 2) ℚ}
    (hzs : IsZeroSum (Node m h t)) (hmem : c ∈ t) :
    IsZeroSum c := by
  have hzs' : IsZeroSum h ∧ ∀ c ∈ t, IsZeroSum c := by
    simpa [IsZeroSum] using hzs
  exact hzs'.2 c hmem

/-- Every child of a zero-sum node is zero-sum. -/
theorem IsZeroSum.child_mem {m : Fin 2} {h : GameTree (Fin 2) ℚ}
    {t : List (GameTree (Fin 2) ℚ)} {c : GameTree (Fin 2) ℚ}
    (hzs : IsZeroSum (Node m h t)) (hmem : c ∈ h :: t) :
    IsZeroSum c := by
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact IsZeroSum.head hzs
  · exact IsZeroSum.tail_mem hzs hmem'

/-- Zero-sumness is inherited by subgames. -/
theorem IsZeroSum.of_subtree {s g : GameTree (Fin 2) ℚ}
    (hzs : IsZeroSum g) (hsub : Subtree s g) : IsZeroSum s := by
  induction hsub with
  | refl => exact hzs
  | inHead m h t _ ih => exact ih (IsZeroSum.head hzs)
  | inTail m h t hmem _ ih => exact ih (IsZeroSum.tail_mem hzs hmem)

/-- Zero-sumness is inherited by proper subgames. -/
theorem IsZeroSum.of_properSubgame {s g : GameTree (Fin 2) ℚ}
    (hzs : IsZeroSum g) (hproper : ProperSubgame s g) : IsZeroSum s :=
  hzs.of_subtree hproper.toSubtree

/-! ### Existence theorem -/

/-- **Zermelo's theorem** (existence form): every finite two-player zero-sum
    perfect-information game admits a pure-strategy subgame-perfect equilibrium.

    This is the specialization of Kuhn's theorem (`Kuhn_exists_SPE`) to the
    2-player zero-sum setting on rationals. The zero-sum hypothesis is part of
    the Zermelo-style statement; existence itself follows from Kuhn's theorem. -/
theorem zermelo_exists_pure_SPE (g : GameTree (Fin 2) ℚ) (_hzs : IsZeroSum g) :
    ∃ σ : Strategy (Fin 2) ℚ, IsSubgamePerfect σ :=
  Kuhn_exists_SPE

/-- Every finite two-player zero-sum perfect-information game admits a
    root-scoped pure-strategy subgame-perfect equilibrium. -/
theorem zermelo_exists_pure_SPE_on (g : GameTree (Fin 2) ℚ) (_hzs : IsZeroSum g) :
    ∃ σ : Strategy (Fin 2) ℚ, IsSubgamePerfectOn σ g :=
  Kuhn_exists_SPE_on g

/-- Every finite two-player zero-sum perfect-information game admits a
    pure-strategy Nash equilibrium at the root. -/
theorem zermelo_exists_pure_NE (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    ∃ σ : Strategy (Fin 2) ℚ, IsNashEquilibrium σ g := by
  obtain ⟨σ, hspe⟩ := zermelo_exists_pure_SPE g hzs
  exact ⟨σ, hspe.toNE g⟩

/-- Every finite two-player zero-sum perfect-information game admits one pure
    strategy that is subgame-perfect on every subtree of the root. -/
theorem zermelo_exists_pure_SPE_on_subtrees
    (g : GameTree (Fin 2) ℚ) (_hzs : IsZeroSum g) :
    ∃ σ : Strategy (Fin 2) ℚ,
      ∀ s : GameTree (Fin 2) ℚ, Subtree s g → IsSubgamePerfectOn σ s :=
  Kuhn_exists_SPE_on_subtrees g

/-- Every finite two-player zero-sum perfect-information game admits one pure
    strategy that is Nash on every subtree of the root. -/
theorem zermelo_exists_pure_NE_on_subtrees
    (g : GameTree (Fin 2) ℚ) (_hzs : IsZeroSum g) :
    ∃ σ : Strategy (Fin 2) ℚ,
      ∀ s : GameTree (Fin 2) ℚ, Subtree s g → IsNashAt σ s :=
  Kuhn_exists_NE_on_subtrees g

/-- Every zero-sum subtree admits a root-scoped pure-strategy
    subgame-perfect equilibrium. -/
theorem zermelo_exists_pure_SPE_on_subtree
    {s g : GameTree (Fin 2) ℚ} (hzs : IsZeroSum g) (hsub : Subtree s g) :
    ∃ σ : Strategy (Fin 2) ℚ, IsSubgamePerfectOn σ s :=
  zermelo_exists_pure_SPE_on s (hzs.of_subtree hsub)

/-- Every zero-sum subtree admits a pure-strategy Nash equilibrium at its
    root. -/
theorem zermelo_exists_pure_NE_on_subtree
    {s g : GameTree (Fin 2) ℚ} (hzs : IsZeroSum g) (hsub : Subtree s g) :
    ∃ σ : Strategy (Fin 2) ℚ, IsNashAt σ s := by
  obtain ⟨σ, hspe⟩ := zermelo_exists_pure_SPE_on_subtree hzs hsub
  exact ⟨σ, hspe.toNashAt⟩

/-- Every finite two-player zero-sum perfect-information game admits one pure
    strategy that is subgame-perfect on every proper subgame of the root. -/
theorem zermelo_exists_pure_SPE_on_properSubgames
    (g : GameTree (Fin 2) ℚ) (_hzs : IsZeroSum g) :
    ∃ σ : Strategy (Fin 2) ℚ,
      ∀ s : GameTree (Fin 2) ℚ, ProperSubgame s g → IsSubgamePerfectOn σ s :=
  Kuhn_exists_SPE_on_properSubgames g

/-- Every finite two-player zero-sum perfect-information game admits one pure
    strategy that is Nash on every proper subgame of the root. -/
theorem zermelo_exists_pure_NE_on_properSubgames
    (g : GameTree (Fin 2) ℚ) (_hzs : IsZeroSum g) :
    ∃ σ : Strategy (Fin 2) ℚ,
      ∀ s : GameTree (Fin 2) ℚ, ProperSubgame s g → IsNashAt σ s :=
  Kuhn_exists_NE_on_properSubgames g

/-- Every proper zero-sum subgame admits a root-scoped pure-strategy
    subgame-perfect equilibrium. -/
theorem zermelo_exists_pure_SPE_on_properSubgame
    {s g : GameTree (Fin 2) ℚ} (hzs : IsZeroSum g)
    (hproper : ProperSubgame s g) :
    ∃ σ : Strategy (Fin 2) ℚ, IsSubgamePerfectOn σ s :=
  zermelo_exists_pure_SPE_on_subtree hzs hproper.toSubtree

/-- Every proper zero-sum subgame admits a pure-strategy Nash equilibrium at
    its root. -/
theorem zermelo_exists_pure_NE_on_properSubgame
    {s g : GameTree (Fin 2) ℚ} (hzs : IsZeroSum g)
    (hproper : ProperSubgame s g) :
    ∃ σ : Strategy (Fin 2) ℚ, IsNashAt σ s :=
  zermelo_exists_pure_NE_on_subtree hzs hproper.toSubtree

/-- Every finite two-player zero-sum perfect-information game admits one pure
    strategy that is Nash at the root and Nash on every proper subgame. -/
theorem zermelo_exists_pure_NE_and_NE_on_properSubgames
    (g : GameTree (Fin 2) ℚ) (_hzs : IsZeroSum g) :
    ∃ σ : Strategy (Fin 2) ℚ,
      IsNashAt σ g ∧
        ∀ s : GameTree (Fin 2) ℚ, ProperSubgame s g → IsNashAt σ s :=
  Kuhn_exists_NE_and_NE_on_properSubgames g

/-- Every finite two-player zero-sum perfect-information game admits one pure
    strategy that is Nash at the root and subgame-perfect on every proper
    subgame. -/
theorem zermelo_exists_pure_NE_and_SPE_on_properSubgames
    (g : GameTree (Fin 2) ℚ) (_hzs : IsZeroSum g) :
    ∃ σ : Strategy (Fin 2) ℚ,
      IsNashAt σ g ∧
        ∀ s : GameTree (Fin 2) ℚ, ProperSubgame s g → IsSubgamePerfectOn σ s :=
  Kuhn_exists_NE_and_SPE_on_properSubgames g

/-! ### Backward-induction value in zero-sum games -/

/-- **Minimax value** for player 0 in a two-player zero-sum game.

    Under zero-sum, this fully determines both players' values
    (player 1's value = `-value₀`). -/
noncomputable def value₀ (g : GameTree (Fin 2) ℚ) : ℚ :=
  (value g) 0

/-- At a zero-sum leaf, `value₀` equals player 0's payoff and
    `-value₀` equals player 1's. -/
theorem value₀_Leaf (p : Fin 2 → ℚ) (_h : IsZeroSum (Leaf p)) :
    value₀ (Leaf p) = p 0 := by
  unfold value₀
  simp

/-- Backward induction preserves the zero-sum invariant: if every terminal
    payoff vector is zero-sum, then the selected backward-induction value
    vector is zero-sum as well. -/
theorem value_zero_sum (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    (value g) 0 + (value g) 1 = 0 := by
  revert hzs
  induction g using GameTree.strong_induction with
  | base p =>
      intro hzs
      simpa [IsZeroSum] using hzs
  | step m h t ih =>
      intro hzs
      obtain ⟨c, hmem, hvalue⟩ := value_Node_eq_some_child_value m h t
      rw [hvalue]
      exact ih c hmem (IsZeroSum.child_mem hzs hmem)

/-- In a zero-sum game, player 1's backward-induction value is determined by
    player 0's value. -/
theorem value_one_eq_neg_value₀ (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    (value g) 1 = -value₀ g := by
  unfold value₀
  have h := value_zero_sum g hzs
  linarith

/-! ### Local max-min structure -/

/-- At any decision node, the backward-induction `value₀` is realized by
    one of the node's children. -/
theorem value₀_Node_eq_some_child (m : Fin 2) (h : GameTree (Fin 2) ℚ)
    (t : List (GameTree (Fin 2) ℚ)) :
    ∃ c ∈ h :: t, value₀ (Node m h t) = value₀ c := by
  obtain ⟨c, hmem, hvalue⟩ := value_Node_eq_some_child_value m h t
  refine ⟨c, hmem, ?_⟩
  unfold value₀
  exact congrArg (fun v : Fin 2 → ℚ => v 0) hvalue

/-- At a player-0 node, `value₀` is at least the `value₀` of every child. -/
theorem value₀_Node_zero_ge_child (h : GameTree (Fin 2) ℚ)
    (t : List (GameTree (Fin 2) ℚ)) (c : GameTree (Fin 2) ℚ)
    (hmem : c ∈ h :: t) :
    value₀ c ≤ value₀ (Node (0 : Fin 2) h t) := by
  unfold value₀
  exact value_Node_ge (0 : Fin 2) h t c hmem

/-- At a zero-sum player-1 node, `value₀` is no greater than the `value₀`
    of every child. Equivalently, player 1's local maximization of their own
    value is player 0's local minimization. -/
theorem value₀_Node_one_le_child (h : GameTree (Fin 2) ℚ)
    (t : List (GameTree (Fin 2) ℚ)) (hzs : IsZeroSum (Node (1 : Fin 2) h t))
    (c : GameTree (Fin 2) ℚ) (hmem : c ∈ h :: t) :
    value₀ (Node (1 : Fin 2) h t) ≤ value₀ c := by
  have hge : (value c) 1 ≤ (value (Node (1 : Fin 2) h t)) 1 :=
    value_Node_ge (1 : Fin 2) h t c hmem
  rw [value_one_eq_neg_value₀ c (IsZeroSum.child_mem hzs hmem),
    value_one_eq_neg_value₀ (Node (1 : Fin 2) h t) hzs] at hge
  exact neg_le_neg_iff.mp hge

/-- At a player-0 node, some child realizes the node's `value₀`, and that
    value is at least every child's `value₀`. -/
theorem value₀_Node_zero_isMax (h : GameTree (Fin 2) ℚ)
    (t : List (GameTree (Fin 2) ℚ)) :
    ∃ c ∈ h :: t,
      value₀ (Node (0 : Fin 2) h t) = value₀ c ∧
      ∀ d ∈ h :: t, value₀ d ≤ value₀ c := by
  obtain ⟨c, hmem, hvalue⟩ := value₀_Node_eq_some_child (0 : Fin 2) h t
  refine ⟨c, hmem, hvalue, ?_⟩
  intro d hdmem
  rw [← hvalue]
  exact value₀_Node_zero_ge_child h t d hdmem

/-- At a zero-sum player-1 node, some child realizes the node's `value₀`, and
    that value is no greater than every child's `value₀`. -/
theorem value₀_Node_one_isMin (h : GameTree (Fin 2) ℚ)
    (t : List (GameTree (Fin 2) ℚ)) (hzs : IsZeroSum (Node (1 : Fin 2) h t)) :
    ∃ c ∈ h :: t,
      value₀ (Node (1 : Fin 2) h t) = value₀ c ∧
      ∀ d ∈ h :: t, value₀ c ≤ value₀ d := by
  obtain ⟨c, hmem, hvalue⟩ := value₀_Node_eq_some_child (1 : Fin 2) h t
  refine ⟨c, hmem, hvalue, ?_⟩
  intro d hdmem
  rw [← hvalue]
  exact value₀_Node_one_le_child h t hzs d hdmem

/-! ### Backward-induction outcome in zero-sum games -/

/-- The terminal outcome reached by the backward-induction strategy is
    zero-sum whenever the game tree is zero-sum. -/
theorem outcome_optStrategy_zero_sum (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    outcome (optStrategy : Strategy (Fin 2) ℚ) g 0 +
      outcome (optStrategy : Strategy (Fin 2) ℚ) g 1 = 0 := by
  rw [outcome_optStrategy_eq_value]
  exact value_zero_sum g hzs

/-- In a zero-sum game, the backward-induction outcome for player 1 is the
    negative of player 0's backward-induction value. -/
theorem outcome_optStrategy_one_eq_neg_value₀
    (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    outcome (optStrategy : Strategy (Fin 2) ℚ) g 1 = -value₀ g := by
  rw [outcome_optStrategy_eq_value]
  exact value_one_eq_neg_value₀ g hzs

/-! ### Value realization -/

/-- The backward-induction strategy realizes `value₀` for player 0. -/
theorem value₀_eq_optStrategy_outcome (g : GameTree (Fin 2) ℚ) :
    value₀ g = outcome (optStrategy : Strategy (Fin 2) ℚ) g 0 := by
  unfold value₀
  rw [outcome_optStrategy_eq_value]

/-- A real value theorem for finite zero-sum perfect-information trees:
    the backward-induction strategy realizes player 0's value, and the value
    vector is zero-sum. -/
theorem value₀_minimax_prop (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    value₀ g = outcome (optStrategy : Strategy (Fin 2) ℚ) g 0 ∧
      (value g) 1 = -value₀ g :=
  ⟨value₀_eq_optStrategy_outcome g, value_one_eq_neg_value₀ g hzs⟩

end GameTree
