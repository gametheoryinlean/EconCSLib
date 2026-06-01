/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Preference
import Mathlib.Data.List.Basic

/-!
# EconCSLib.GameTheory.ExtensiveGame.GameTree

Finite extensive-form games of **perfect information, without chance**,
encoded as a generic inductive type.

## Design

```
inductive GameTree (N U : Type*)
  | Leaf (payoff : N → U)
  | Node (mover : N) (head : GameTree N U) (tail : List (GameTree N U))
```

* **N** — the player set (need not be finite or decidable).
* **U** — the payoff type (will acquire `[TotalPreorder U]` at theorem sites,
  not in the type definition — Bourbaki discipline).
* **Finite** via inductive structure.
* **Non-empty children at each `Node`** via the `head : GameTree` + `tail : List ...`
  split — `head` provides a witness, `tail` the rest.
* **No `Nature` / chance constructor**: chance is deferred to a future
  `StochasticGameTree` module (see project memory 2026-04-20).

## Main definitions

* `GameTree` — the inductive type itself
* `GameTree.size` — structural size (well-founded recursion helper)
* `GameTree.children` — the full child list `head :: tail` at a `Node`
* `GameTree.mapChildren` — apply a function to every child of a `Node`

## References

* [MSZ, Ch. 3] Maschler, Solan, Zamir, *Game Theory* (Cambridge, 2013) —
  extensive games (backward induction; Kuhn 1953)
-/

/-- A finite extensive-form game of perfect information, without chance.

    * `Leaf payoff` — a terminal state with a payoff vector `N → U`.
    * `Node mover head tail` — a decision node owned by `mover`,
      with non-empty children `head :: tail`.

    Finiteness is built into the inductive type; non-emptiness of
    children is built into the `Node` constructor via `head + tail`. -/
inductive GameTree (N : Type*) (U : Type*) : Type _
  | Leaf (payoff : N → U) : GameTree N U
  | Node (mover : N) (head : GameTree N U) (tail : List (GameTree N U)) :
      GameTree N U

namespace GameTree

variable {N U : Type*}

/-- The full child list at a `Node`, as a guaranteed non-empty list. -/
@[simp]
def children : GameTree N U → List (GameTree N U)
  | Leaf _ => []
  | Node _ h t => h :: t

/-- Children of a `Node` are never empty. -/
theorem children_node_ne_nil (m : N) (h : GameTree N U) (t : List (GameTree N U)) :
    children (Node m h t) ≠ [] := by
  simp [children]

/-- Structural size, used for well-founded recursion. -/
def size : GameTree N U → ℕ
  | Leaf _ => 1
  | Node _ h t => 1 + h.size + (t.map size).sum

/-- Size is always positive. -/
theorem size_pos (g : GameTree N U) : 0 < g.size := by
  cases g with
  | Leaf _ => simp [size]
  | Node _ _ _ => simp [size]; omega

/-- The head of a `Node`'s children is structurally smaller. -/
theorem size_head_lt (m : N) (h : GameTree N U) (t : List (GameTree N U)) :
    h.size < (Node m h t).size := by
  simp [size]
  have : 0 ≤ (t.map size).sum := Nat.zero_le _
  omega

/-- Any tail child is structurally smaller. -/
theorem size_mem_tail_lt (m : N) (h : GameTree N U) (t : List (GameTree N U))
    {c : GameTree N U} (hmem : c ∈ t) :
    c.size < (Node m h t).size := by
  simp only [size]
  have hsum : c.size ≤ (t.map size).sum := by
    induction t with
    | nil => cases hmem
    | cons x xs ih =>
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · simp [List.sum_cons]
        · simp [List.sum_cons]
          have := ih hmem'
          omega
  have : 0 < h.size := size_pos h
  omega

/-- Any child (head or in tail) is structurally smaller than the node. -/
theorem size_mem_children_lt (m : N) (h : GameTree N U) (t : List (GameTree N U))
    {c : GameTree N U} (hmem : c ∈ children (Node m h t)) :
    c.size < (Node m h t).size := by
  simp [children, List.mem_cons] at hmem
  rcases hmem with rfl | hmem'
  · exact size_head_lt m c t
  · exact size_mem_tail_lt m h t hmem'

/-! ### Subtree relation

`Subtree s g` means the tree `s` occurs somewhere inside `g` (reflexively, or
as the head / a tail element, recursively). Useful for stating subgame-perfect
properties quantified over all reachable subgames. -/

/-- `Subtree s g` — `s` occurs as a subtree of `g`. -/
inductive Subtree : GameTree N U → GameTree N U → Prop
  | refl (g : GameTree N U) : Subtree g g
  | inHead (s : GameTree N U) (m : N) (h : GameTree N U) (t : List (GameTree N U))
      (hs : Subtree s h) : Subtree s (Node m h t)
  | inTail (s : GameTree N U) (m : N) (h : GameTree N U) (t : List (GameTree N U))
      {c : GameTree N U} (hmem : c ∈ t) (hs : Subtree s c) :
      Subtree s (Node m h t)

/-- Every tree is a subtree of itself. -/
theorem Subtree.self (g : GameTree N U) : Subtree g g := Subtree.refl g

/-- The head of a `Node` is a subtree of the node. -/
theorem Subtree.head (m : N) (h : GameTree N U) (t : List (GameTree N U)) :
    Subtree h (Node m h t) :=
  Subtree.inHead h m h t (Subtree.refl h)

/-- Any tail member of a `Node` is a subtree of the node. -/
theorem Subtree.tail_mem (m : N) (h : GameTree N U) (t : List (GameTree N U))
    {c : GameTree N U} (hmem : c ∈ t) : Subtree c (Node m h t) :=
  Subtree.inTail c m h t hmem (Subtree.refl c)

/-- Any child (head or tail) is a subtree. -/
theorem Subtree.child_mem (m : N) (h : GameTree N U) (t : List (GameTree N U))
    {c : GameTree N U} (hmem : c ∈ h :: t) : Subtree c (Node m h t) := by
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact Subtree.head m c t
  · exact Subtree.tail_mem m h t hmem'

/-- The subtree relation is transitive. In game-theoretic terms, a subgame of
    a subgame is also a subgame of the original game. -/
theorem Subtree.trans {r s g : GameTree N U} (hrs : Subtree r s) (hsg : Subtree s g) :
    Subtree r g := by
  induction hsg with
  | refl => exact hrs
  | inHead m h t _ ih => exact Subtree.inHead r m h t ih
  | inTail m h t hmem _ ih => exact Subtree.inTail r m h t hmem ih

/-! ### Strong induction on size

A size-based strong induction principle: to prove `motive g`, assume
`motive c` for every child `c ∈ h :: t` of a `Node`. Stronger than the
default inductive recursor (which only gives IH on the head), and
precisely what backward-induction proofs need. -/

/-- **Strong induction**: to prove `motive g`, it suffices to handle `Leaf`
    and, for each `Node`, to prove the motive given the motive for every
    child (head or tail). -/
theorem strong_induction {motive : GameTree N U → Prop}
    (base : ∀ p, motive (Leaf p))
    (step : ∀ (m : N) (h : GameTree N U) (t : List (GameTree N U)),
              (∀ c ∈ h :: t, motive c) → motive (Node m h t))
    (g : GameTree N U) : motive g := by
  -- Well-founded recursion on `size`.
  suffices h : ∀ (n : ℕ) (g : GameTree N U), g.size ≤ n → motive g from
    h g.size g (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro g hg
      exact absurd hg (Nat.not_le_of_lt (size_pos g))
  | succ k ih =>
      intro g hg
      cases g with
      | Leaf p => exact base p
      | Node m h t =>
          apply step m h t
          intro c hmem
          apply ih c
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · have := size_head_lt m c t
            omega
          · have := size_mem_tail_lt m h t hmem'
            omega

end GameTree
