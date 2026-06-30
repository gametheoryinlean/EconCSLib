/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Preference
import Mathlib.Data.List.Basic

/-!
# ExtensiveGame.GameTree

Finite extensive-form games of **perfect information, without chance**,
encoded as a generic inductive type.

## Design

```
inductive GameTree (ι U : Type*)
  | Leaf (payoff : ι → U)
  | Node (mover : ι) (head : GameTree ι U) (tail : List (GameTree ι U))
```

* **ι** — the player set (need not be finite or decidable).
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
* `GameTree.Subtree` — the reflexive subtree relation
* `GameTree.ProperSubgame` — a subtree strictly below a fixed root
* `GameTree.HasOnlyRootSubgames` — the root is the only subtree
* `GameTree.mapChildren` — apply a function to every child of a `Node`

## References

* [MSZ] Maschler, Solan, Zamir, *Game Theory*, Chapter 3 (extensive games),
  Theorem 3.13 (Kuhn)
-/

/-- A finite extensive-form game of perfect information, without chance.

    * `Leaf payoff` — a terminal state with a payoff vector `ι → U`.
    * `Node mover head tail` — a decision node owned by `mover`,
      with non-empty children `head :: tail`.

    Finiteness is built into the inductive type; non-emptiness of
    children is built into the `Node` constructor via `head + tail`. -/
inductive GameTree (ι : Type*) (U : Type*) : Type _
  | Leaf (payoff : ι → U) : GameTree ι U
  | Node (mover : ι) (head : GameTree ι U) (tail : List (GameTree ι U)) :
      GameTree ι U

namespace GameTree

variable {ι U : Type*}

/-- The full child list at a `Node`, as a guaranteed non-empty list. -/
@[simp]
def children : GameTree ι U → List (GameTree ι U)
  | Leaf _ => []
  | Node _ h t => h :: t

/-- Children of a `Node` are never empty. -/
theorem children_node_ne_nil (m : ι) (h : GameTree ι U) (t : List (GameTree ι U)) :
    children (Node m h t) ≠ [] := by
  simp [children]

/-- Structural size, used for well-founded recursion. -/
def size : GameTree ι U → ℕ
  | Leaf _ => 1
  | Node _ h t => 1 + h.size + (t.map size).sum

/-- Size is always positive. -/
theorem size_pos (g : GameTree ι U) : 0 < g.size := by
  cases g with
  | Leaf _ => simp [size]
  | Node _ _ _ => simp [size]; omega

/-- The head of a `Node`'s children is structurally smaller. -/
theorem size_head_lt (m : ι) (h : GameTree ι U) (t : List (GameTree ι U)) :
    h.size < (Node m h t).size := by
  simp [size]
  have : 0 ≤ (t.map size).sum := Nat.zero_le _
  omega

/-- Any tail child is structurally smaller. -/
theorem size_mem_tail_lt (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
    {c : GameTree ι U} (hmem : c ∈ t) :
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
theorem size_mem_children_lt (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
    {c : GameTree ι U} (hmem : c ∈ children (Node m h t)) :
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
inductive Subtree : GameTree ι U → GameTree ι U → Prop
  | refl (g : GameTree ι U) : Subtree g g
  | inHead (s : GameTree ι U) (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
      (hs : Subtree s h) : Subtree s (Node m h t)
  | inTail (s : GameTree ι U) (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
      {c : GameTree ι U} (hmem : c ∈ t) (hs : Subtree s c) :
      Subtree s (Node m h t)

/-- Every tree is a subtree of itself. -/
theorem Subtree.self (g : GameTree ι U) : Subtree g g := Subtree.refl g

/-- The head of a `Node` is a subtree of the node. -/
theorem Subtree.head (m : ι) (h : GameTree ι U) (t : List (GameTree ι U)) :
    Subtree h (Node m h t) :=
  Subtree.inHead h m h t (Subtree.refl h)

/-- Any tail member of a `Node` is a subtree of the node. -/
theorem Subtree.tail_mem (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
    {c : GameTree ι U} (hmem : c ∈ t) : Subtree c (Node m h t) :=
  Subtree.inTail c m h t hmem (Subtree.refl c)

/-- Any child (head or tail) is a subtree. -/
theorem Subtree.child_mem (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
    {c : GameTree ι U} (hmem : c ∈ h :: t) : Subtree c (Node m h t) := by
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact Subtree.head m c t
  · exact Subtree.tail_mem m h t hmem'

/-- Any child in the public `children` list is a subtree. -/
theorem Subtree.child (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
    {c : GameTree ι U} (hmem : c ∈ children (Node m h t)) :
    Subtree c (Node m h t) :=
  Subtree.child_mem m h t (by simpa [children] using hmem)

/-- The subtree relation is transitive. In game-theoretic terms, a subgame of
    a subgame is also a subgame of the original game. -/
theorem Subtree.trans {r s g : GameTree ι U} (hrs : Subtree r s) (hsg : Subtree s g) :
    Subtree r g := by
  induction hsg with
  | refl => exact hrs
  | inHead m h t _ ih => exact Subtree.inHead r m h t ih
  | inTail m h t hmem _ ih => exact Subtree.inTail r m h t hmem ih

/-- A subtree is no larger than the tree containing it. -/
theorem Subtree.size_le {s g : GameTree ι U} (hsub : Subtree s g) :
    s.size ≤ g.size := by
  induction hsub with
  | refl => exact Nat.le_refl _
  | inHead m h t _ ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (size_head_lt m h t))
  | inTail m h t hmem _ ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (size_mem_tail_lt m h t hmem))

/-! ### Proper subgames -/

/-- A proper subgame is a subtree strictly below the chosen root. -/
def ProperSubgame (s g : GameTree ι U) : Prop :=
  Subtree s g ∧ s ≠ g

/-- A proper subgame is, in particular, a subtree. -/
theorem ProperSubgame.toSubtree {s g : GameTree ι U} (hproper : ProperSubgame s g) :
    Subtree s g :=
  hproper.1

/-- A proper subgame is not the whole root tree. -/
theorem ProperSubgame.ne {s g : GameTree ι U} (hproper : ProperSubgame s g) :
    s ≠ g :=
  hproper.2

/-- Every subtree is either the root itself or a proper subgame. -/
theorem Subtree.eq_or_properSubgame {s g : GameTree ι U} (hsub : Subtree s g) :
    s = g ∨ ProperSubgame s g := by
  by_cases hroot : s = g
  · exact Or.inl hroot
  · exact Or.inr ⟨hsub, hroot⟩

/-- Subtree membership splits into the root case and the proper-subgame case. -/
theorem subtree_iff_eq_or_properSubgame {s g : GameTree ι U} :
    Subtree s g ↔ s = g ∨ ProperSubgame s g := by
  constructor
  · intro hsub
    exact hsub.eq_or_properSubgame
  · intro hcases
    rcases hcases with hroot | hproper
    · rw [hroot]
      exact Subtree.self g
    · exact hproper.toSubtree

/-- No tree is a proper subgame of itself. -/
theorem not_properSubgame_self (g : GameTree ι U) :
    ¬ ProperSubgame g g := by
  intro hproper
  exact hproper.ne rfl

/-- Proper subgames are structurally smaller than their root. -/
theorem ProperSubgame.size_lt {s g : GameTree ι U} (hproper : ProperSubgame s g) :
    s.size < g.size := by
  rcases hproper with ⟨hsub, hne⟩
  induction hsub with
  | refl =>
      exact False.elim (hne rfl)
  | inHead m h t hs _ih =>
      exact Nat.lt_of_le_of_lt hs.size_le (size_head_lt m h t)
  | inTail m h t hmem hs _ih =>
      exact Nat.lt_of_le_of_lt hs.size_le (size_mem_tail_lt m h t hmem)

/-- A proper subgame of a subtree is a proper subgame of the larger root. -/
theorem ProperSubgame.trans_subtree {r s g : GameTree ι U}
    (hr : ProperSubgame r s) (hs : Subtree s g) :
    ProperSubgame r g := by
  refine ⟨Subtree.trans hr.toSubtree hs, ?_⟩
  intro hrg
  have hsize : r.size < s.size := hr.size_lt
  have hle : s.size ≤ g.size := hs.size_le
  subst hrg
  exact Nat.lt_irrefl r.size (Nat.lt_of_lt_of_le hsize hle)

/-- The proper-subgame relation is transitive. -/
theorem ProperSubgame.trans {r s g : GameTree ι U}
    (hr : ProperSubgame r s) (hs : ProperSubgame s g) :
    ProperSubgame r g :=
  hr.trans_subtree hs.toSubtree

/-- A subtree of a proper subgame is a proper subgame of the larger root. -/
theorem Subtree.trans_properSubgame {r s g : GameTree ι U}
    (hr : Subtree r s) (hs : ProperSubgame s g) :
    ProperSubgame r g := by
  refine ⟨Subtree.trans hr hs.toSubtree, ?_⟩
  intro hrg
  have hle : r.size ≤ s.size := hr.size_le
  have hsize : s.size < g.size := hs.size_lt
  subst hrg
  exact Nat.lt_irrefl r.size (Nat.lt_of_le_of_lt hle hsize)

/-- The head child of a node is a proper subgame of that node. -/
theorem ProperSubgame.head (m : ι) (h : GameTree ι U) (t : List (GameTree ι U)) :
    ProperSubgame h (Node m h t) := by
  refine ⟨Subtree.head m h t, ?_⟩
  intro h_eq
  have h_lt : h.size < (Node m h t).size := size_head_lt m h t
  have h_size : (Node m h t).size = h.size := (congrArg size h_eq).symm
  simp [h_size] at h_lt

/-- Every tail child of a node is a proper subgame of that node. -/
theorem ProperSubgame.tail_mem (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
    {c : GameTree ι U} (hmem : c ∈ t) :
    ProperSubgame c (Node m h t) := by
  refine ⟨Subtree.tail_mem m h t hmem, ?_⟩
  intro h_eq
  have h_lt : c.size < (Node m h t).size := size_mem_tail_lt m h t hmem
  have h_size : (Node m h t).size = c.size := (congrArg size h_eq).symm
  simp [h_size] at h_lt

/-- Every direct child of a node is a proper subgame of that node. -/
theorem ProperSubgame.child_mem (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
    {c : GameTree ι U} (hmem : c ∈ h :: t) :
    ProperSubgame c (Node m h t) := by
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact ProperSubgame.head m c t
  · exact ProperSubgame.tail_mem m h t hmem'

/-- Every child in the public `children` list is a proper subgame of the node. -/
theorem ProperSubgame.child (m : ι) (h : GameTree ι U) (t : List (GameTree ι U))
    {c : GameTree ι U} (hmem : c ∈ children (Node m h t)) :
    ProperSubgame c (Node m h t) :=
  ProperSubgame.child_mem m h t (by simpa [children] using hmem)

/-- The proper subgames of a nonterminal node are exactly the subtrees of its
    direct children. -/
theorem properSubgame_Node_iff_exists_child_subtree
    {s : GameTree ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)} :
    ProperSubgame s (Node m h t) ↔
      ∃ c : GameTree ι U, c ∈ children (Node m h t) ∧ Subtree s c := by
  constructor
  · intro hproper
    cases hproper.toSubtree with
    | refl =>
        exact False.elim (hproper.ne rfl)
    | inHead m h t hs =>
        exact ⟨h, by simp [children], hs⟩
    | inTail m h t hmem hs =>
        exact ⟨_, by simp [children, hmem], hs⟩
  · rintro ⟨c, hmem, hs⟩
    exact hs.trans_properSubgame (ProperSubgame.child m h t hmem)

/-- The head/tail form of `properSubgame_Node_iff_exists_child_subtree`. -/
theorem properSubgame_Node_iff_subtree_head_or_tail
    {s : GameTree ι U} {m : ι} {h : GameTree ι U} {t : List (GameTree ι U)} :
    ProperSubgame s (Node m h t) ↔
      Subtree s h ∨ ∃ c : GameTree ι U, c ∈ t ∧ Subtree s c := by
  rw [properSubgame_Node_iff_exists_child_subtree]
  constructor
  · rintro ⟨c, hmem, hs⟩
    rcases List.mem_cons.mp (by simpa [children] using hmem) with rfl | hmem'
    · exact Or.inl hs
    · exact Or.inr ⟨c, hmem', hs⟩
  · rintro (hs | ⟨c, hmem, hs⟩)
    · exact ⟨h, by simp [children], hs⟩
    · exact ⟨c, by simp [children, hmem], hs⟩

/-- A fixed `GameTree` has no proper subgames when every subtree is the root
    itself. This is the pure finite-tree analogue of having no nontrivial
    subgames. -/
def HasOnlyRootSubgames (g : GameTree ι U) : Prop :=
  ∀ s : GameTree ι U, Subtree s g → s = g

/-- Having only the root subgame is equivalent to having no proper subgames. -/
theorem hasOnlyRootSubgames_iff_no_properSubgame (g : GameTree ι U) :
    HasOnlyRootSubgames g ↔ ¬ ∃ s : GameTree ι U, ProperSubgame s g := by
  constructor
  · intro hroot hproper
    rcases hproper with ⟨s, hsub, hne⟩
    exact hne (hroot s hsub)
  · intro hno s hsub
    by_contra hne
    exact hno ⟨s, hsub, hne⟩

/-- A terminal leaf has no proper subgames. -/
theorem hasOnlyRootSubgames_Leaf (p : ι → U) :
    HasOnlyRootSubgames (Leaf p : GameTree ι U) := by
  intro s hsub
  cases hsub
  rfl

/-- Every nonterminal node has a proper subgame. -/
theorem not_hasOnlyRootSubgames_Node (m : ι) (h : GameTree ι U)
    (t : List (GameTree ι U)) :
    ¬ HasOnlyRootSubgames (Node m h t) := by
  intro hroot
  have hproper : ProperSubgame h (Node m h t) := ProperSubgame.head m h t
  exact hproper.ne (hroot h hproper.toSubtree)

/-- A tree has only its root as a subgame if and only if it is terminal. -/
theorem hasOnlyRootSubgames_iff_exists_leaf (g : GameTree ι U) :
    HasOnlyRootSubgames g ↔ ∃ p : ι → U, g = Leaf p := by
  constructor
  · intro hroot
    cases g with
    | Leaf p => exact ⟨p, rfl⟩
    | Node m h t =>
        exact False.elim (not_hasOnlyRootSubgames_Node m h t hroot)
  · rintro ⟨p, rfl⟩
    exact hasOnlyRootSubgames_Leaf p

/-! ### Strong induction on size

A size-based strong induction principle: to prove `motive g`, assume
`motive c` for every child `c ∈ h :: t` of a `Node`. Stronger than the
default inductive recursor (which only gives IH on the head), and
precisely what backward-induction proofs need. -/

/-- **Strong induction**: to prove `motive g`, it suffices to handle `Leaf`
    and, for each `Node`, to prove the motive given the motive for every
    child (head or tail). -/
theorem strong_induction {motive : GameTree ι U → Prop}
    (base : ∀ p, motive (Leaf p))
    (step : ∀ (m : ι) (h : GameTree ι U) (t : List (GameTree ι U)),
              (∀ c ∈ h :: t, motive c) → motive (Node m h t))
    (g : GameTree ι U) : motive g := by
  -- Well-founded recursion on `size`.
  suffices h : ∀ (n : ℕ) (g : GameTree ι U), g.size ≤ n → motive g from
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
