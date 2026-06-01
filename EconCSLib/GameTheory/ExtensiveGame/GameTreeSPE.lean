/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.BackwardInduction

/-!
# EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE

Strategies, outcomes, and **Kuhn's theorem** on `GameTree N U`:
every finite perfect-information game without chance has a
subgame-perfect equilibrium, obtainable via backward induction.

## Minimal assumptions

Only `[TotalPreorder U]` — preorder + totality, no antisymmetry,
no decidability. See `ExtensiveGame/BackwardInduction.lean`.

## Main definitions

* `GameTree.Strategy` — a strategy is a subtype-bundled child-selector
  at every possible `(mover, head, tail)`.
* `GameTree.outcome` — the terminal payoff reached when following a strategy.
* `GameTree.optStrategy` — the canonical backward-induction strategy (picks
  a child whose value attains the backward-induction max for the node's mover).
* `GameTree.IVariant` — two strategies differ only at nodes whose mover is `i`.
* `GameTree.IsSubgamePerfect` — no unilateral deviation of any player at any
  subgame improves their payoff.

## Main results

* `outcome_optStrategy_eq_value` — outcome of `optStrategy` is the BI value.
* `optStrategy_isSubgamePerfect` — the backward-induction strategy `optStrategy`
  is a subgame-perfect equilibrium (the substantive theorem).
* `Kuhn_exists_SPE` — existence form: every finite perfect-information game has
  an SPE.

## A note on the name "Kuhn"

"Kuhn's theorem" here means the **backward-induction / SPE-existence** theorem
(Kuhn 1953). It is distinct from the *other* result also called Kuhn's theorem —
the equivalence of mixed and behavioral strategies under perfect recall — whose
infrastructure lives in `ExtensiveGame/BehaviorStrategy.lean` (tracked under
EG-L2). Do not conflate the two.

## References

* [MSZ, Ch. 3] Maschler, Solan, Zamir, *Game Theory* (Cambridge, 2013) —
  backward induction on finite perfect-information games.
* Kuhn, H. W. (1953), "Extensive Games and the Problem of Information," in
  *Contributions to the Theory of Games, Vol. II*.
-/

namespace GameTree

variable {N U : Type*} [TotalPreorder U]

/-! ### Strategies -/

/-- A pure strategy for the entire game tree: at every possible node context
    `(mover, head, tail)`, specify one child (bundled with its membership proof).

    Note: a single `Strategy` covers all players. Player-`i` "strategies"
    are conceptualized as the restriction to nodes where `mover = i`. -/
def Strategy (N U : Type*) : Type _ :=
  (m : N) → (h : GameTree N U) → (t : List (GameTree N U)) →
    { c : GameTree N U // c ∈ h :: t }

/-- The outcome (terminal payoff vector) of playing strategy `σ` starting
    from game tree `g`. Walks down the tree, using `σ` to pick a child at
    each `Node`, until a `Leaf` is reached. -/
noncomputable def outcome (σ : Strategy N U) : GameTree N U → (N → U)
  | Leaf p => p
  | Node m h t => outcome σ (σ m h t).val
termination_by g => g.size
decreasing_by
  have hmem := (σ m h t).property
  exact size_mem_children_lt m h t (by simpa [children] using hmem)

omit [TotalPreorder U] in
@[simp]
theorem outcome_Leaf (σ : Strategy N U) (p : N → U) :
    outcome σ (Leaf p) = p := by
  rw [outcome]

omit [TotalPreorder U] in
@[simp]
theorem outcome_Node (σ : Strategy N U) (m : N) (h : GameTree N U)
    (t : List (GameTree N U)) :
    outcome σ (Node m h t) = outcome σ (σ m h t).val := by
  rw [outcome]

/-! ### Backward-induction strategy -/

/-- The canonical backward-induction strategy: at each node, pick a child
    whose backward-induction value equals the node's value (i.e., a child
    attaining the argmax for the mover).

    Noncomputable — uses classical choice via `value_Node_eq_some_child_value`. -/
noncomputable def optStrategy [DecidableLE U] : Strategy N U := fun m h t =>
  ⟨(value_Node_eq_some_child_value m h t).choose,
   (value_Node_eq_some_child_value m h t).choose_spec.1⟩

/-- At a node, the `optStrategy` picks a child whose value equals the node's value. -/
theorem value_optStrategy_eq [DecidableLE U] (m : N) (h : GameTree N U)
    (t : List (GameTree N U)) :
    value (optStrategy m h t).val = value (Node m h t) :=
  ((value_Node_eq_some_child_value m h t).choose_spec.2).symm

/-! ### Strategy deviation -/

/-- Two strategies are `i`-variants if they agree on all nodes NOT owned by `i`.
    I.e., `σ'` is obtained from `σ` by changing only player `i`'s choices. -/
def IVariant (i : N) (σ σ' : Strategy N U) : Prop :=
  ∀ (m : N) (h : GameTree N U) (t : List (GameTree N U)),
    m ≠ i → σ m h t = σ' m h t

omit [TotalPreorder U] in
/-- `IVariant` is reflexive: any strategy is an `i`-variant of itself. -/
theorem IVariant.refl (i : N) (σ : Strategy N U) : IVariant i σ σ :=
  fun _ _ _ _ => rfl

/-! ### Subgame-perfect equilibrium -/

/-- A strategy is **subgame-perfect** (SPE) if, at every subtree, no player
    can strictly improve their payoff by a unilateral deviation — i.e., by
    switching to any `i`-variant strategy. -/
def IsSubgamePerfect (σ : Strategy N U) : Prop :=
  ∀ (g : GameTree N U) (i : N) (σ' : Strategy N U),
    IVariant i σ σ' → outcome σ' g i ≤ outcome σ g i

/-! ### Kuhn's theorem (main result) -/

/-- **Key lemma**: the outcome of the backward-induction strategy equals
    the backward-induction value vector at every game tree.

    This is the bridge between `value` (defined via argmax) and `outcome`
    (defined via tree traversal). -/
theorem outcome_optStrategy_eq_value [DecidableLE U] (g : GameTree N U) :
    outcome (optStrategy : Strategy N U) g = value g := by
  induction g using GameTree.strong_induction with
  | base p => simp [outcome_Leaf, value_Leaf]
  | step m h t ih =>
      -- outcome optStrategy (Node m h t) = outcome optStrategy (optStrategy m h t).val
      -- By IH on the chosen child: = value (optStrategy m h t).val
      -- By value_optStrategy_eq:   = value (Node m h t)
      rw [outcome_Node]
      have hmem : (optStrategy m h t).val ∈ h :: t := (optStrategy m h t).property
      rw [ih _ hmem]
      exact value_optStrategy_eq m h t

/-- **Optimality of `optStrategy`**: for every subtree `g`, every player `i`,
    and every `i`-variant deviation `σ'`, the deviating outcome is no better
    than `optStrategy`'s outcome at coordinate `i`. This is the SPE property
    spelled out before bundling into existence form. -/
theorem optStrategy_isSubgamePerfect [DecidableLE U] :
    IsSubgamePerfect (optStrategy : Strategy N U) := by
  intro g i σ' hiv
  induction g using GameTree.strong_induction with
  | base p =>
      -- Both outcomes equal `p`; `≤` holds by reflexivity.
      simp [outcome_Leaf]
  | step m h t ih =>
      -- Two subcases depending on whether the mover is the deviating player.
      rw [outcome_Node, outcome_Node]
      by_cases hmi : m = i
      · -- Mover = deviating player. σ' can pick any child c'; optStrategy picks argmax.
        -- Use IH on c' to compare σ' vs optStrategy there, then value_Node_ge.
        have hmem' : (σ' m h t).val ∈ h :: t := (σ' m h t).property
        -- IH on c' gives: outcome σ' c' i ≤ outcome optStrategy c' i
        have h_ih := ih _ hmem'
        -- Bridge: outcome optStrategy c' = value c'
        rw [outcome_optStrategy_eq_value] at h_ih
        -- value c' i ≤ value (Node m h t) i by value_Node_ge
        have h_max : (value (σ' m h t).val) i ≤ (value (Node m h t)) i := by
          subst hmi
          exact value_Node_ge m h t _ hmem'
        -- Right side: outcome optStrategy (optStrategy m h t).val i = value (Node m h t) i
        have h_rhs : outcome optStrategy (optStrategy m h t).val i =
                       (value (Node m h t)) i := by
          rw [outcome_optStrategy_eq_value]
          exact congrArg (· i) (value_optStrategy_eq m h t)
        calc outcome σ' (σ' m h t).val i
            ≤ (value (σ' m h t).val) i := h_ih
          _ ≤ (value (Node m h t)) i := h_max
          _ = outcome optStrategy (optStrategy m h t).val i := h_rhs.symm
      · -- Mover ≠ deviating player: σ' and optStrategy pick the same child.
        have hsame : σ' m h t = optStrategy m h t := (hiv m h t hmi).symm
        rw [hsame]
        -- Apply IH on the shared child
        have hmem : (optStrategy m h t).val ∈ h :: t := (optStrategy m h t).property
        exact ih _ hmem

/-- **Kuhn's theorem** (existence form): every finite perfect-information
    game without chance admits a subgame-perfect equilibrium.

    The backward-induction strategy `optStrategy` is such an SPE. -/
theorem Kuhn_exists_SPE [DecidableLE U] : ∃ σ : Strategy N U, IsSubgamePerfect σ :=
  ⟨optStrategy, optStrategy_isSubgamePerfect⟩

end GameTree
