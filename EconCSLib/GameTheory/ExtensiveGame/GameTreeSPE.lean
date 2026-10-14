/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.BackwardInduction

/-!
# EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE

Structural endpoint policies, outcomes, and backward induction on
`GameTree N U`.

The historical `Strategy` is one global child selector indexed by a node's
structural value `(mover, head, tail)`.  It is not bound to a root and cannot
distinguish two equal subtree values reached at different history
occurrences.  Consequently this module calls its predicate
`IsGlobalEndpointSubgamePerfect`: it is a stronger global structural
endpoint-policy theorem, not the canonical strategy space of a root-bound
perfect-information EFG.

The canonical occurrence-sensitive theorem is
`GameTree.Kuhn_exists_occurrencePureSPE` in
`Compiler.GameTreeOccurrenceObserved`.

## Minimal assumptions

The structural notions use only `[TotalPreorder U]`.  The executable
backward-induction selector additionally uses `[DecidableLE U]`; no classical
choice is used. See `ExtensiveGame/BackwardInduction.lean`.

## Main definitions

* `GameTree.Strategy` — a global structural endpoint policy: a
  subtype-bundled child-selector at every possible `(mover, head, tail)`.
* `GameTree.outcome` — the terminal payoff reached when following a strategy.
* `GameTree.optStrategy` — the canonical backward-induction strategy (picks
  a child whose value attains the backward-induction max for the node's mover).
* `GameTree.IVariant` — two strategies differ only at nodes whose mover is `i`.
* `GameTree.IsGlobalEndpointSubgamePerfect` — no structural endpoint-policy
  deviation improves at any tree value.

## Main results

* `outcome_optStrategy_eq_value` — outcome of `optStrategy` is the BI value.
* `optStrategy_isGlobalEndpointSubgamePerfect` — the backward-induction
  endpoint policy is globally optimal against structural endpoint deviations.
* `Kuhn_exists_globalEndpointSPE` — existence form for that historical layer.

## A note on the name "Kuhn"

The historical name refers to the backward-induction route underlying finite
SPE existence. The theorem exported by this module alone is the structural
endpoint-policy result; its canonical standard-SPE realization is proved by
the occurrence compiler. This is distinct from the *other* result also called
Kuhn's theorem—the equivalence of mixed and behavioral strategies under
perfect recall—whose infrastructure lives in the observed-game layer.

## References

* [MSZ, Ch. 3] Maschler, Solan, Zamir, *Game Theory* (Cambridge, 2013) —
  backward induction on finite perfect-information games.
* Kuhn, H. W. (1953), "Extensive Games and the Problem of Information," in
  *Contributions to the Theory of Games, Vol. II*.
-/

namespace GameTree

variable {N U : Type*} [TotalPreorder U]

/-! ### Strategies -/

/-- A global structural endpoint policy: at every possible node context
    `(mover, head, tail)`, specify one child (bundled with its membership proof).

    Note: a single `Strategy` covers all players. Player-`i` "strategies"
    are conceptualized as the restriction to nodes where `mover = i`.
    Equal subtree values at distinct history occurrences are intentionally
    identified. -/
def Strategy (N U : Type*) : Type _ :=
  (m : N) → (h : GameTree N U) → (t : List (GameTree N U)) →
    { c : GameTree N U // c ∈ h :: t }

/-- The outcome (terminal payoff vector) of playing strategy `σ` starting
    from game tree `g`. Walks down the tree, using `σ` to pick a child at
    each `Node`, until a `Leaf` is reached. -/
def outcome (σ : Strategy N U) : GameTree N U → (N → U)
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

/-- Applying `value` after selecting the best child is the same finite fold as
selecting the best already-computed child value. -/
private theorem value_argMaxOn_child
    [DecidableLE U] (m : N) (h : GameTree N U)
    (t : List (GameTree N U)) :
    value (List.argMaxOn (fun child => (value child) m) h t) =
      List.argMaxOn (fun childValue => childValue m)
        (value h) (t.map value) := by
  simp only [List.argMaxOn]
  induction t generalizing h with
  | nil =>
      rfl
  | cons child tail ih =>
      simp only [List.foldl_cons, List.map_cons]
      by_cases hle : (value h) m ≤ (value child) m
      · simp only [hle, if_true]
        exact ih child
      · simp only [hle, if_false]
        exact ih h

/-- The canonical executable backward-induction strategy: at each node, pick
the child maximizing the mover's coordinate.  The child and its membership
proof are produced by the same finite `argMaxOn` fold used by `value`; no
existence theorem or classical choice is involved. -/
def optStrategy [DecidableLE U] : Strategy N U := fun m h t =>
  ⟨List.argMaxOn (fun child => (value child) m) h t,
    List.argMaxOn_mem (fun child => (value child) m) h t⟩

/-- At a node, the `optStrategy` picks a child whose value equals the node's value. -/
theorem value_optStrategy_eq [DecidableLE U] (m : N) (h : GameTree N U)
    (t : List (GameTree N U)) :
    value (optStrategy m h t).val = value (Node m h t) :=
  by
    change
      value (List.argMaxOn (fun child => (value child) m) h t) =
        value (Node m h t)
    rw [value_Node, valueList_eq_map, value_argMaxOn_child]

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

/-- Historical global endpoint-policy optimality: at every tree value, no
player can improve by switching to an `i`-variant global endpoint policy.

This is not the root-bound occurrence-sensitive standard EFG predicate; use
`ObservedGame.IsPureStandardSubgamePerfect` through
`GameTree.toOccurrenceObservedGame` for that semantics. -/
def IsGlobalEndpointSubgamePerfect (σ : Strategy N U) : Prop :=
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
than `optStrategy`'s outcome at coordinate `i`. This is the global structural
endpoint-policy property spelled out before bundling into existence form. -/
theorem optStrategy_isGlobalEndpointSubgamePerfect [DecidableLE U] :
    IsGlobalEndpointSubgamePerfect (optStrategy : Strategy N U) := by
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

/-- Existence theorem for global structural endpoint policies.  For canonical
root-bound occurrence-sensitive SPE use `Kuhn_exists_occurrencePureSPE`. -/
theorem Kuhn_exists_globalEndpointSPE [DecidableLE U] :
    ∃ σ : Strategy N U,
      IsGlobalEndpointSubgamePerfect σ :=
  ⟨optStrategy, optStrategy_isGlobalEndpointSubgamePerfect⟩

end GameTree
