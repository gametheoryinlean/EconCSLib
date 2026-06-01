/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Argmax
import EconCSLib.GameTheory.ExtensiveGame.GameTree

/-!
# EconCSLib.GameTheory.ExtensiveGame.BackwardInduction

Backward induction on `GameTree N U`, producing a value function
`value : GameTree N U → (N → U)` together with the optimality lemmas
used by `ExtensiveGame.SPE` to prove Kuhn's theorem.

## Minimal assumptions

The payoff type `U` carries `[TotalPreorder U]` (reflexivity + transitivity +
totality; **no antisymmetry**) plus `[DecidableLE U]` so the argmax — and hence
`value` — is **computable**. `ℚ` (the Zermelo / examples track) supplies both.

## Main definitions

* `GameTree.value` — the backward-induction value vector (computable).
* `GameTree.valueList` — mutually recursive helper: value on a list of trees.

## Main results

* `value_Leaf` — value of a leaf is its payoff
* `value_Node` — value of a node equals the argmax-chosen child's value
* `value_Node_ge` — the mover's coordinate dominates every child's
* `value_Node_eq_some_child_value` — a node's value is the value of some child
-/

namespace GameTree

variable {N U : Type*} [TotalPreorder U] [DecidableLE U]

mutual
  /-- Value of a game tree: a payoff vector. At a `Node`, the mover selects
      a child maximizing their own coordinate (argmax over the total preorder).

      **Computable** — with a decidable comparison `[DecidableLE U]` the argmax
      is a left fold, so `value` runs (`#eval`/`decide`) on concrete games. -/
  def value : GameTree N U → (N → U)
    | Leaf p => p
    | Node m h t =>
        let hv := value h
        let tv := valueList t
        List.argMaxOn (fun v => v m) hv tv
  /-- Pointwise image of `value` over a list of game trees.
      Structurally recursive on the list. -/
  def valueList : List (GameTree N U) → List (N → U)
    | [] => []
    | x :: xs => value x :: valueList xs
end

@[simp]
theorem value_Leaf (p : N → U) : value (Leaf p : GameTree N U) = p := rfl

@[simp]
theorem value_Node (m : N) (h : GameTree N U) (t : List (GameTree N U)) :
    value (Node m h t) =
      List.argMaxOn (fun v => v m) (value h) (valueList t) := rfl

@[simp]
theorem valueList_nil : valueList ([] : List (GameTree N U)) = [] := rfl

@[simp]
theorem valueList_cons (x : GameTree N U) (xs : List (GameTree N U)) :
    valueList (x :: xs) = value x :: valueList xs := rfl

/-- `valueList l` is exactly `l.map value`. Useful for rewriting. -/
theorem valueList_eq_map (l : List (GameTree N U)) :
    valueList l = l.map value := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [valueList, ih]

/-- Membership in `valueList` via membership in the source list. -/
theorem mem_valueList_iff {v : N → U} {l : List (GameTree N U)} :
    v ∈ valueList l ↔ ∃ c ∈ l, value c = v := by
  rw [valueList_eq_map]
  simp [List.mem_map, eq_comm]

/-- **Key optimality lemma**: at a `Node m h t`, the mover `m`'s coordinate
    of the backward-induction value dominates every child's. -/
theorem value_Node_ge (m : N) (h : GameTree N U) (t : List (GameTree N U))
    (c : GameTree N U) (hmem : c ∈ h :: t) :
    (value c) m ≤ (value (Node m h t)) m := by
  rw [value_Node]
  -- The argmax is chosen from (value h :: valueList t) w.r.t. `(·) m`.
  -- We need: `value c m ≤ argMaxOn (·m) (value h) (valueList t) m`.
  -- Since `c ∈ h :: t`, `value c ∈ value h :: valueList t`.
  have hcv : value c ∈ value h :: valueList t := by
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact List.mem_cons_self
    · refine List.mem_cons.mpr (Or.inr ?_)
      rw [valueList_eq_map]
      exact List.mem_map_of_mem hmem'
  exact List.argMaxOn_ge (fun v => v m) (value h) (valueList t) (value c) hcv

/-- The value at a node is itself the value of some child (the argmax).
    Specifically, `argMaxOn ... ∈ value h :: valueList t`, so it equals
    `value c` for some `c ∈ h :: t`. -/
theorem value_Node_eq_some_child_value (m : N) (h : GameTree N U)
    (t : List (GameTree N U)) :
    ∃ c ∈ h :: t, value (Node m h t) = value c := by
  rw [value_Node]
  have hmem := List.argMaxOn_mem (fun v => v m) (value h) (valueList t)
  rcases List.mem_cons.mp hmem with heq | hmem'
  · exact ⟨h, List.mem_cons_self, heq⟩
  · rw [mem_valueList_iff] at hmem'
    obtain ⟨c, hc_mem, hc_eq⟩ := hmem'
    refine ⟨c, List.mem_cons.mpr (Or.inr hc_mem), ?_⟩
    exact hc_eq.symm

end GameTree
