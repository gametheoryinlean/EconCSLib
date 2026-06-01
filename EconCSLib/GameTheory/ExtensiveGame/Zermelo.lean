/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.GameTheory.ExtensiveGame.Zermelo

**Zermelo-style finite game results** as two-player zero-sum consequences of
backward induction and Kuhn's theorem.

Zermelo (1913) established determinacy for finite perfect-information
two-player win/loss/draw games (Chess, in his original paper).
Here we frame it as the special case of Kuhn's theorem where:

* `N = Fin 2` — exactly two players,
* payoffs are in `ℚ` (any `[LinearOrderedField U]` would do),
* the game is **zero-sum**: `payoff leaf 0 + payoff leaf 1 = 0` at every leaf.

## Main definitions

* `GameTree.IsZeroSum` — the zero-sum predicate on a `GameTree (Fin 2) ℚ`
* `GameTree.value₀` — the value of the game for Player 0.

## Main results

* `zermelo_determinacy` — **determinacy / saddle value**: in a finite two-player
  zero-sum perfect-information game, `optStrategy` is a saddle point with value
  `value₀ g`. Player 0, by playing `optStrategy`, secures at least `value₀ g`
  against every opponent play; player 1, by playing `optStrategy`, holds player 0
  to at most `value₀ g`. This is the genuine Zermelo content (the value is
  determined and both players have a pure optimal strategy).
* `IsZeroSum.of_subtree` — zero-sumness is inherited by every subgame.
* `outcome_zero_sum` — every strategy's terminal outcome is zero-sum in a
  zero-sum tree.
* `value_zero_sum` — backward induction preserves the zero-sum value invariant.
* `value_one_eq_neg_value₀` — player 1's backward-induction value is the
  negative of player 0's value.
* `value₀_Node_zero_isMax` / `value₀_Node_one_isMin` — the local max/min
  behavior of the zero-sum value at player-0 and player-1 nodes.
* `value₀_eq_outcome_and_zeroSum` — `optStrategy` realizes the player-0 value and
  the value vector is zero-sum (packaging lemma; the saddle statement is
  `zermelo_determinacy`).
* `zermelo_exists_pure_SPE` / `zermelo_exists_pure_NE` — the `Fin 2` / `ℚ`
  instances of Kuhn's existence theorem. **Existence needs no zero-sum
  hypothesis**; the zero-sum refinement is `zermelo_determinacy`.

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

/-! ### Existence (instances of Kuhn's theorem)

Existence of a pure SPE / Nash equilibrium is **Kuhn's theorem**; it holds for
any finite perfect-information game and does **not** use the zero-sum
hypothesis. These two declarations are just the `Fin 2` / `ℚ` instances, kept as
named entry points. The genuinely zero-sum result — that the game has a
determined value realized by a saddle point — is `zermelo_determinacy` below. -/

/-- Pure root-scoped subgame-perfect existence for a finite two-player game on
    `ℚ`: the `Fin 2` / `ℚ` instance of `Kuhn_exists_SPE_on`. Zero-sum is **not**
    needed for existence; see `zermelo_determinacy` for the zero-sum refinement. -/
theorem zermelo_exists_pure_SPE (g : GameTree (Fin 2) ℚ) :
    ∃ σ : Strategy (Fin 2) ℚ, IsSubgamePerfectOn σ g :=
  Kuhn_exists_SPE_on g

/-- Pure root Nash existence for a finite two-player game on `ℚ`: the `Fin 2` /
    `ℚ` instance of `Kuhn_exists_NE`. Zero-sum is **not** needed. -/
theorem zermelo_exists_pure_NE (g : GameTree (Fin 2) ℚ) :
    ∃ σ : Strategy (Fin 2) ℚ, IsNashEquilibrium σ g :=
  Kuhn_exists_NE g

/-! ### Backward-induction value in zero-sum games -/

/-- **Minimax value** for player 0 in a two-player zero-sum game.

    Under zero-sum, this fully determines both players' values
    (player 1's value = `-value₀`). -/
def value₀ (g : GameTree (Fin 2) ℚ) : ℚ :=
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

/-- In a zero-sum tree, the terminal outcome of **any** strategy is zero-sum:
    following any strategy ends at some leaf, and every leaf of a zero-sum tree
    is zero-sum. This is the strategy-level analogue of `value_zero_sum`. -/
theorem outcome_zero_sum (σ : Strategy (Fin 2) ℚ) (g : GameTree (Fin 2) ℚ)
    (hzs : IsZeroSum g) :
    outcome σ g 0 + outcome σ g 1 = 0 := by
  revert hzs
  induction g using GameTree.strong_induction with
  | base p =>
      intro hzs
      simpa [outcome_Leaf, IsZeroSum] using hzs
  | step m h t ih =>
      intro hzs
      rw [outcome_Node]
      have hmem : (σ m h t).val ∈ h :: t := (σ m h t).property
      exact ih _ hmem (IsZeroSum.child_mem hzs hmem)

/-- The terminal outcome reached by the backward-induction strategy is
    zero-sum whenever the game tree is zero-sum. -/
theorem outcome_optStrategy_zero_sum (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    outcome (optStrategy : Strategy (Fin 2) ℚ) g 0 +
      outcome (optStrategy : Strategy (Fin 2) ℚ) g 1 = 0 :=
  outcome_zero_sum optStrategy g hzs

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

/-- Packaging lemma: the backward-induction strategy realizes player 0's value,
    and the value vector is zero-sum. This is *not* the minimax statement — it
    has no quantification over opponent strategies. The genuine saddle / security
    statement is `zermelo_determinacy`. -/
theorem value₀_eq_outcome_and_zeroSum (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    value₀ g = outcome (optStrategy : Strategy (Fin 2) ℚ) g 0 ∧
      (value g) 1 = -value₀ g :=
  ⟨value₀_eq_optStrategy_outcome g, value_one_eq_neg_value₀ g hzs⟩

/-! ### Determinacy (the saddle value)

The genuine Zermelo content. Combining subgame perfection of `optStrategy`
(`optStrategy_isSubgamePerfect`) with the zero-sum invariant gives a saddle
point: `value₀ g` is simultaneously what player 0 can secure and what player 1
can hold player 0 to. -/

/-- **Player 0's security.** If player 0 plays `optStrategy` (so the deviating
    profile `σ'` is a `1`-variant, leaving player 0's choices fixed), then player
    0's payoff is at least `value₀ g` against *every* play of player 1.

    Proof: subgame perfection at player 1 caps `outcome σ' g 1 ≤ value g 1 =
    -value₀ g`; the zero-sum identity `outcome σ' g 0 = -outcome σ' g 1` then
    forces `outcome σ' g 0 ≥ value₀ g`. -/
theorem value₀_le_outcome_of_iVariant_one (g : GameTree (Fin 2) ℚ)
    (hzs : IsZeroSum g) {σ' : Strategy (Fin 2) ℚ}
    (hiv : IVariant (1 : Fin 2) optStrategy σ') :
    value₀ g ≤ outcome σ' g 0 := by
  have h1 := optStrategy_isSubgamePerfect g (1 : Fin 2) σ' hiv
  rw [outcome_optStrategy_eq_value, value_one_eq_neg_value₀ g hzs] at h1
  have hsum := outcome_zero_sum σ' g hzs
  linarith

/-- **Player 1's security.** If player 1 plays `optStrategy` (so `σ'` is a
    `0`-variant, leaving player 1's choices fixed), then player 0's payoff is at
    most `value₀ g` against *every* play of player 0. Immediate from subgame
    perfection at player 0; no zero-sum hypothesis is needed for this direction. -/
theorem outcome_le_value₀_of_iVariant_zero (g : GameTree (Fin 2) ℚ)
    {σ' : Strategy (Fin 2) ℚ} (hiv : IVariant (0 : Fin 2) optStrategy σ') :
    outcome σ' g 0 ≤ value₀ g := by
  have h0 := optStrategy_isSubgamePerfect g (0 : Fin 2) σ' hiv
  rw [outcome_optStrategy_eq_value] at h0
  simpa [value₀] using h0

/-- **Zermelo's theorem (determinacy / saddle value).** In a finite two-player
    zero-sum perfect-information game, `optStrategy` is a saddle point with value
    `value₀ g`:

    * playing `optStrategy`, player 0 *secures* at least `value₀ g` against every
      opponent play (`1`-variant);
    * playing `optStrategy`, player 1 *holds* player 0 to at most `value₀ g`
      against every opponent play (`0`-variant).

    Hence the game is determined and `value₀ g` is its value, attained by the
    pure backward-induction strategy on both sides. -/
theorem zermelo_determinacy (g : GameTree (Fin 2) ℚ) (hzs : IsZeroSum g) :
    (∀ σ' : Strategy (Fin 2) ℚ, IVariant (1 : Fin 2) optStrategy σ' →
        value₀ g ≤ outcome σ' g 0) ∧
    (∀ σ' : Strategy (Fin 2) ℚ, IVariant (0 : Fin 2) optStrategy σ' →
        outcome σ' g 0 ≤ value₀ g) :=
  ⟨fun _ hiv => value₀_le_outcome_of_iVariant_one g hzs hiv,
   fun _ hiv => outcome_le_value₀_of_iVariant_zero g hiv⟩

end GameTree
