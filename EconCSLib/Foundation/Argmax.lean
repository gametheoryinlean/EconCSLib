/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Preference
import Mathlib.Data.List.Basic

/-!
# EconCSLib.Foundation.Argmax

Argmax helpers for total preorders on non-empty lists.

## Why a bespoke version

Mathlib's `List.argmax` / `Finset.argmax` require `[LinearOrder]`
(antisymmetry). The backward-induction proof in
`ExtensiveGame.BackwardInduction` only needs `[TotalPreorder]` (no
antisymmetry). This file closes that gap with a **computable** argmax: a left
fold that keeps the running maximizer, needing only a decidable comparison
`[DecidableLE]` for the fold and `[TotalPreorder]` for correctness.

## Main definitions

* `List.exists_argMax_on` — some element of `head :: tail` maximizes `f`
  (pure existence, `[TotalPreorder]` only)
* `List.argMaxOn` — chosen such element, computed by a fold
  (`[TotalPreorder]` + `[DecidableLE]`)
* `List.argMaxOn_mem` — the chosen element is in the list
* `List.argMaxOn_ge` — every element's `f`-image is `≤` the chosen one's
-/

namespace List

variable {X Y : Type*}

/-- **Existence of an argmax** on a non-empty list under a total preorder.
    Since the preorder may lack antisymmetry, ties are allowed — we only
    claim existence of *some* maximizer, not uniqueness. -/
theorem exists_argMax_on [TotalPreorder Y] (f : X → Y)
    (head : X) (tail : List X) :
    ∃ m, m ∈ head :: tail ∧ ∀ x ∈ head :: tail, f x ≤ f m := by
  induction tail generalizing head with
  | nil =>
      refine ⟨head, List.mem_singleton.mpr rfl, ?_⟩
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact le_refl _
  | cons y ys ih =>
      obtain ⟨m', hm'_mem, hm'_max⟩ := ih y
      rcases TotalPreorder.le_total (f m') (f head) with hle | hle
      · refine ⟨head, List.mem_cons_self, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx_in
        · exact le_refl _
        · exact le_trans (hm'_max x hx_in) hle
      · refine ⟨m', ?_, ?_⟩
        · exact List.mem_cons.mpr (Or.inr hm'_mem)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx_in
          · exact hle
          · exact hm'_max x hx_in

/-- `foldl_max_ge`: every element's `f`-image is `≤` that of the running
    maximizer kept by the left fold. The induction generalizes the accumulator. -/
private theorem foldl_max_ge [TotalPreorder Y] [DecidableLE Y] (f : X → Y) :
    ∀ (l : List X) (acc : X), ∀ x ∈ acc :: l,
      f x ≤ f (l.foldl (fun a z => if f a ≤ f z then z else a) acc) := by
  intro l
  induction l with
  | nil =>
      intro acc x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact le_refl _
  | cons y ys ih =>
      intro acc x hx
      rw [List.foldl_cons]
      by_cases h : f acc ≤ f y
      · rw [if_pos h]
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact le_trans h (ih y y List.mem_cons_self)
        · exact ih y x hx'
      · rw [if_neg h]
        have hy : f y ≤ f acc := by
          rcases TotalPreorder.le_total (f y) (f acc) with hle | hle
          · exact hle
          · exact absurd hle h
        rcases List.mem_cons.mp hx with heq | hx'
        · rw [heq]; exact ih acc acc List.mem_cons_self
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · exact le_trans hy (ih acc acc List.mem_cons_self)
          · exact ih acc x (List.mem_cons.mpr (Or.inr hx''))

/-- `foldl_max_mem`: the running maximizer kept by the left fold lies in the
    candidate list `acc :: l`. -/
private theorem foldl_max_mem [LE Y] [DecidableLE Y] (f : X → Y) :
    ∀ (l : List X) (acc : X),
      l.foldl (fun a z => if f a ≤ f z then z else a) acc ∈ acc :: l := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons y ys ih =>
      intro acc
      rw [List.foldl_cons]
      by_cases h : f acc ≤ f y
      · rw [if_pos h]
        exact List.mem_cons_of_mem acc (ih y)
      · rw [if_neg h]
        rcases List.mem_cons.mp (ih acc) with hr | hr
        · rw [hr]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem acc (List.mem_cons_of_mem y hr)

/-- A chosen maximizer of `f` on the non-empty list `head :: tail`, **computed**
    by a left fold that keeps the running maximizer (ties keep the later element).
    Computable: the fold needs only a decidable comparison `[DecidableLE Y]`;
    correctness (`argMaxOn_mem` / `argMaxOn_ge`) needs the total preorder. -/
def argMaxOn [TotalPreorder Y] [DecidableLE Y] (f : X → Y)
    (head : X) (tail : List X) : X :=
  tail.foldl (fun a z => if f a ≤ f z then z else a) head

/-- The chosen maximizer is a member of the list. -/
theorem argMaxOn_mem [TotalPreorder Y] [DecidableLE Y] (f : X → Y)
    (head : X) (tail : List X) :
    argMaxOn f head tail ∈ head :: tail :=
  foldl_max_mem f tail head

/-- Soundness: every element's `f`-image is `≤` the chosen maximizer's. -/
theorem argMaxOn_ge [TotalPreorder Y] [DecidableLE Y] (f : X → Y)
    (head : X) (tail : List X) :
    ∀ x ∈ head :: tail, f x ≤ f (argMaxOn f head tail) :=
  foldl_max_ge f tail head

/-- The argmax achieves at least the head's value. -/
theorem le_argMaxOn_head [TotalPreorder Y] [DecidableLE Y] (f : X → Y)
    (head : X) (tail : List X) :
    f head ≤ f (argMaxOn f head tail) :=
  argMaxOn_ge f head tail head List.mem_cons_self

end List
