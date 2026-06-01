/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.RoundRobin

The **choice round-robin** algorithm and its EF1 correctness proof, stated on the
canonical bundled `AdditiveInstance` interface.

## Main definitions

* `bestGood` — argmax helper: an element of `s` maximizing an agent's item weight
* `roundRobinAux` — recursive core: agents take turns picking their best remaining good
* `roundRobinAllocation` — the complete round-robin allocation for an additive instance
* `roundRobinRule` — a feasible-allocation rule induced by round-robin

## Main results

* `roundRobinAllocation_isAllocation` — the output is a valid partition of `I.allGoods`
* `roundRobinAllocation_isEF1` — the output satisfies EF1 for nonnegative weights
* `roundRobinRule_isEF1` — rule-style EF1 correctness

## Algorithm

Agents are ordered `0, 1, ..., n-1, 0, 1, ...` (cycling mod `n`). In each step the
current agent picks their highest-weight remaining good. The implementation recurses on
`remaining.card` with accumulator `A : Allocation (Fin n) G`.

## EF1 proof outline

Fix distinct agents `i, j : Fin n`.

**Case `i.val < j.val`** (i picks before j in every round):
When `i` picks their `r`-th good `i_r` in round `r`, agent `j`'s round-`r` good `j_r` is
still in the pool (j hasn't picked yet that round). Since `i` picks optimally,
`v_i(i_r) ≥ v_i(j_r)`. Summing over rounds: `v_i(A_i) ≥ v_i(A_j)` — agent `i` does not
envy `j` at all (stronger than EF1). Any good in `A_j` is therefore a valid EF1 witness
(use monotonicity: removing a good can only decrease value).

**Case `j.val < i.val`** (j picks before i in every round):
When `i` picks their `r`-th good `i_r` in round `r`, agent `j`'s *next* good `j_{r+1}` is
still in the pool (j picks in round r+1, after i picks in round r). So `v_i(i_r) ≥ v_i(j_{r+1})`.
Telescoping over `r = 0, …, |A_j| − 2`:
  `v_i(A_i) ≥ Σ_r v_i(j_{r+1}) = v_i(A_j) − v_i(j_0)`,
i.e., `v_i(A_j \ {j_0}) ≤ v_i(A_i)`, where `j_0` is `j`'s **first** picked good (EF1 witness).

## Proof technique

All proofs use strong induction on `remaining.card` via `Finset.strongInductionOn`,
with case splits on `turn = i`, `turn = j`, `turn ≠ i ∧ turn ≠ j` handled via
`Function.update_apply`.

The EF1 correctness proofs use two-part invariants maintained across rounds:

* `roundRobin_noEnvy_of_earlier` maintains `v_i(A j) ≤ v_i(A i)` (no-envy) plus a
  headroom condition `v_i(A j) + w_i(g) ≤ v_i(A i)` for all remaining `g`, active when
  agent `i` has picked in the current cycle but `j` has not yet (`i.val < turn.val ≤ j.val`).

* `roundRobin_ef1_of_later` maintains a two-phase invariant: Phase 1 (before `j`'s first
  pick) and Phase 2 (after `j` picks witness `g0`: `v_i(A j \ {g0}) ≤ v_i(A i)` with
  conditional headroom guarded by `i.val < turn.val ∨ turn.val ≤ j.val`).

## References

* Lipton et al., "On Approximately Fair Allocations of Indivisible Goods" (EC 2004)
* Nisan et al., *Algorithmic Game Theory*, Chapter 11
-/

open Finset BigOperators

namespace SocialChoice
namespace FairDivision
namespace Indivisible

variable {n : ℕ} {G : Type*}

/-! ### Raw implementation layer

The public algorithm below is stated on `AdditiveInstance`. The recursive proof
machinery is parameterized by the raw induced valuation to keep the induction
lemmas independent of bundled-record projection noise. -/

/-! ### Best-item selection -/

/-- `rawBestGood w i s hs` is a good in `s` that maximises `w.weight i` over `s`.

    Defined noncomputably via `Classical.choose` on `Finset.exists_max_image`. Its
    key properties are `rawBestGood_mem` (membership) and `rawBestGood_le` (maximality). -/
private noncomputable def rawBestGood
    (w : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) : G :=
  Classical.choose (Finset.exists_max_image s (w.weight i) hs)

/-- `rawBestGood` lies in the candidate set `s`. -/
private lemma rawBestGood_mem
    (w : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) :
    rawBestGood w i s hs ∈ s :=
  (Classical.choose_spec (Finset.exists_max_image s (w.weight i) hs)).1

/-- Every element of `s` is no more valuable (to agent `i`) than `rawBestGood`. -/
private lemma rawBestGood_le
    (w : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) {g : G} (hg : g ∈ s) :
    w.weight i g ≤ w.weight i (rawBestGood w i s hs) :=
  (Classical.choose_spec (Finset.exists_max_image s (w.weight i) hs)).2 g hg

variable [NeZero n]

/-! ### Round-robin algorithm -/

/-- Recursive core of the choice round-robin.

    `rawRoundRobinAux w turn remaining A` distributes `remaining` one good at a time:
    `turn` picks the `rawBestGood` from `remaining`, it is added to `A turn`, and
    control passes to agent `(turn + 1) % n`. Terminates when `remaining = ∅`.

    Use `rawRoundRobinAlloc` (which starts with `turn = 0` and `A = fun _ => ∅`)
    rather than calling this directly. -/
private noncomputable def rawRoundRobinAux [DecidableEq G]
    (w : AdditiveValuation (Fin n) G)
    (turn : Fin n) (remaining : Finset G) (A : Allocation (Fin n) G) :
    Allocation (Fin n) G :=
  if h : remaining.Nonempty then
    let g := rawBestGood w turn remaining h
    rawRoundRobinAux w
      ⟨(turn.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      (remaining.erase g)
      (Function.update A turn (insert g (A turn)))
  else A
  termination_by remaining.card
  decreasing_by exact Finset.card_erase_lt_of_mem (rawBestGood_mem w turn remaining h)

/-- The complete choice round-robin allocation of `allGoods` among `n` agents.

    Agent 0 picks first. The `r`-th agent to pick is agent `r % n`. -/
private noncomputable def rawRoundRobinAlloc [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G) : Allocation (Fin n) G :=
  rawRoundRobinAux w ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅)

/-! ### Unfolding lemmas -/

/-- `rawRoundRobinAux` with no remaining goods is the identity on the accumulator. -/
@[simp]
private lemma roundRobinAux_empty [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n) (A : Allocation (Fin n) G) :
    rawRoundRobinAux w turn ∅ A = A := by
  rw [rawRoundRobinAux.eq_1]; simp [Finset.not_nonempty_empty]

/-- One unfolding step of `rawRoundRobinAux` when `remaining` is nonempty. -/
private lemma roundRobinAux_step [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n)
    (remaining : Finset G) (A : Allocation (Fin n) G) (h : remaining.Nonempty) :
    rawRoundRobinAux w turn remaining A =
      rawRoundRobinAux w
        ⟨(turn.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
        (remaining.erase (rawBestGood w turn remaining h))
        (Function.update A turn (insert (rawBestGood w turn remaining h) (A turn))) := by
  rw [rawRoundRobinAux.eq_1]; exact dif_pos h

/-! ### Partition properties -/

/-- Goods in the accumulator are never removed: `A i ⊆ (rawRoundRobinAux ... A) i`. -/
private lemma roundRobinAux_mono [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n)
    (remaining : Finset G) (A : Allocation (Fin n) G) (i : Fin n) :
    A i ⊆ (rawRoundRobinAux w turn remaining A) i := by
  induction remaining using Finset.strongInductionOn generalizing turn A
  rename_i s ih
  by_cases hne : s.Nonempty
  · rw [roundRobinAux_step w turn s A hne]
    apply Finset.Subset.trans _ (ih _ (Finset.erase_ssubset (rawBestGood_mem w turn s hne)) _ _)
    simp only [Function.update_apply]
    split_ifs with h
    · subst h; exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, roundRobinAux_empty]

/-- `rawRoundRobinAux` preserves bundle disjointness, provided `remaining` and `A` are disjoint. -/
private lemma roundRobinAux_disjoint [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n)
    (remaining : Finset G) (A : Allocation (Fin n) G)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (A i) (A j))
    (hrem : ∀ g ∈ remaining, ∀ i : Fin n, g ∉ A i) :
    ∀ i j : Fin n, i ≠ j →
      Disjoint ((rawRoundRobinAux w turn remaining A) i)
               ((rawRoundRobinAux w turn remaining A) j) := by
  induction remaining using Finset.strongInductionOn generalizing turn A
  rename_i s ih
  by_cases hne : s.Nonempty
  · rw [roundRobinAux_step w turn s A hne]
    apply ih _ (Finset.erase_ssubset (rawBestGood_mem w turn s hne))
    · intro p q hpq
      simp only [Function.update_apply]
      by_cases hp : p = turn <;> by_cases hq : q = turn
      · exact absurd (hp.trans hq.symm) hpq
      · rw [if_pos hp, if_neg hq]
        rw [Finset.disjoint_left]
        intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact fun hxq => hrem _ (rawBestGood_mem w turn s hne) q hxq
        · exact Finset.disjoint_left.mp (hdisj turn q (hp ▸ hpq)) hx
      · rw [if_neg hp, if_pos hq]
        rw [Finset.disjoint_left]
        intro x hx
        simp only [Finset.mem_insert]
        rintro (rfl | hxins)
        · exact hrem _ (rawBestGood_mem w turn s hne) p hx
        · exact Finset.disjoint_left.mp (hdisj p turn (hq ▸ hpq)) hx hxins
      · rw [if_neg hp, if_neg hq]
        exact hdisj p q hpq
    · intro g' hg' i
      simp only [Function.update_apply]
      by_cases hi : i = turn
      · rw [if_pos hi]
        simp only [Finset.mem_insert]
        rintro (rfl | hins)
        · exact (Finset.mem_erase.mp hg').1 rfl
        · exact hrem g' (Finset.erase_subset _ _ hg') turn (hi ▸ hins)
      · rw [if_neg hi]
        exact hrem g' (Finset.erase_subset _ _ hg') i
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, roundRobinAux_empty]
    exact hdisj

/-- After `rawRoundRobinAux`, the union of all bundles equals `remaining ∪ ⋃_i A i`. -/
private lemma roundRobinAux_biUnion [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n)
    (remaining : Finset G) (A : Allocation (Fin n) G)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (A i) (A j))
    (hrem : ∀ g ∈ remaining, ∀ i : Fin n, g ∉ A i) :
    Finset.univ.biUnion (rawRoundRobinAux w turn remaining A) =
      remaining ∪ Finset.univ.biUnion A := by
  induction remaining using Finset.strongInductionOn generalizing turn A
  rename_i s ih
  by_cases hne : s.Nonempty
  · rw [roundRobinAux_step w turn s A hne]
    set g := rawBestGood w turn s hne with hg_def
    have hgmem : g ∈ s := rawBestGood_mem w turn s hne
    have hdisj' : ∀ p q : Fin n, p ≠ q →
        Disjoint (Function.update A turn (insert g (A turn)) p)
                 (Function.update A turn (insert g (A turn)) q) := by
      intro p q hpq; simp only [Function.update_apply]
      by_cases hp : p = turn <;> by_cases hq : q = turn
      · exact absurd (hp.trans hq.symm) hpq
      · rw [if_pos hp, if_neg hq]; rw [Finset.disjoint_left]; intro x hx
        simp only [Finset.mem_insert] at hx; rcases hx with rfl | hx
        · exact fun hxq => hrem _ hgmem q hxq
        · exact Finset.disjoint_left.mp (hdisj turn q (hp ▸ hpq)) hx
      · rw [if_neg hp, if_pos hq]; rw [Finset.disjoint_left]; intro x hx
        simp only [Finset.mem_insert]; rintro (rfl | hxins)
        · exact hrem _ hgmem p hx
        · exact Finset.disjoint_left.mp (hdisj p turn (hq ▸ hpq)) hx hxins
      · rw [if_neg hp, if_neg hq]; exact hdisj p q hpq
    have hrem' : ∀ g' ∈ s.erase g, ∀ i : Fin n, g' ∉ Function.update A turn (insert g (A turn)) i := by
      intro g' hg' i; simp only [Function.update_apply]
      by_cases hi : i = turn
      · rw [if_pos hi]; simp only [Finset.mem_insert]; rintro (rfl | hins)
        · exact (Finset.mem_erase.mp hg').1 rfl
        · exact hrem g' (Finset.erase_subset _ _ hg') turn (hi ▸ hins)
      · rw [if_neg hi]; exact hrem g' (Finset.erase_subset _ _ hg') i
    rw [ih _ (Finset.erase_ssubset hgmem) _ _ hdisj' hrem']
    have hbij : Finset.univ.biUnion (Function.update A turn (insert g (A turn))) =
        {g} ∪ Finset.univ.biUnion A := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
                 Finset.mem_singleton, Function.update_apply]
      constructor
      · rintro ⟨i, hi⟩
        by_cases h : i = turn
        · simp only [h, if_true] at hi; simp only [Finset.mem_insert] at hi
          rcases hi with rfl | hmem; exact Or.inl rfl; exact Or.inr ⟨turn, h ▸ hmem⟩
        · simp only [h, if_false] at hi; exact Or.inr ⟨i, hi⟩
      · rintro (rfl | ⟨i, hi⟩)
        · exact ⟨turn, by simp [Finset.mem_insert]⟩
        · by_cases h : i = turn
          · exact ⟨turn, by simp [Finset.mem_insert, h ▸ hi]⟩
          · exact ⟨i, by simp [h, hi]⟩
    rw [hbij, ← Finset.union_assoc]
    congr 1
    rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hgmem]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, roundRobinAux_empty, Finset.empty_union]

/-- `rawRoundRobinAlloc` produces a complete partition of `allGoods`. -/
private theorem rawRoundRobinAlloc_isAllocation [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G) :
    IsAllocation allGoods (rawRoundRobinAlloc w allGoods) := by
  constructor
  · intro i j hij
    exact roundRobinAux_disjoint w ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅)
      (fun i j _ => Finset.disjoint_empty_left _)
      (fun g _hg i hi => absurd hi (Finset.notMem_empty g))
      i j hij
  · have hb := roundRobinAux_biUnion w ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅)
      (fun i j _ => Finset.disjoint_empty_left _)
      (fun g _hg i hi => absurd hi (Finset.notMem_empty g))
    change allGoods = Finset.univ.biUnion (rawRoundRobinAux w ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅))
    rw [hb]
    simp

/-! ### EF1 correctness -/

/-- **Key lemma — no envy when picking earlier** (`i.val < j.val`).

    Since agent `i` picks before `j` in every round, when `i` picks `i_r` in round `r`,
    agent `j`'s round-`r` good `j_r` is still available. By `rawBestGood_le`:
    `w.weight i i_r ≥ w.weight i j_r`. Summing over all rounds:
    `v_i(A_i) ≥ v_i(A_j)` — agent `i` never envies agent `j` at all. -/
private lemma roundRobin_noEnvy_of_earlier
    [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G)
    (hnn : ∀ (i : Fin n) (g : G), 0 ≤ w.weight i g)
    (i j : Fin n) (hij : i.val < j.val) :
    w.toValuation.val i ((rawRoundRobinAlloc w allGoods) j) ≤
    w.toValuation.val i ((rawRoundRobinAlloc w allGoods) i) := by
  -- Strengthen to an invariant on `rawRoundRobinAux`:
  --   hinvI:  v_i(A_j) ≤ v_i(A_i)
  --   hinvII: when i already picked this round but j hasn't yet,
  --           every remaining good g satisfies v_i(A_j) + w_i(g) ≤ v_i(A_i)
  suffices h : ∀ (turn : Fin n) (remaining : Finset G) (A : Allocation (Fin n) G),
      (∀ p q : Fin n, p ≠ q → Disjoint (A p) (A q)) →
      (∀ g ∈ remaining, ∀ k : Fin n, g ∉ A k) →
      w.toValuation.val i (A j) ≤ w.toValuation.val i (A i) →
      (i.val < turn.val ∧ turn.val ≤ j.val →
        ∀ g ∈ remaining, w.toValuation.val i (A j) + w.weight i g ≤
            w.toValuation.val i (A i)) →
      w.toValuation.val i ((rawRoundRobinAux w turn remaining A) j) ≤
      w.toValuation.val i ((rawRoundRobinAux w turn remaining A) i) by
    unfold rawRoundRobinAlloc; apply h
    · intro p q _; exact Finset.disjoint_empty_left _
    · intro g _ k hk; exact absurd hk (Finset.notMem_empty g)
    · simp [AdditiveValuation.toValuation]
    · intro ⟨h1, _⟩; exact absurd h1 (Nat.not_lt_zero i.val)
  intro turn remaining
  induction remaining using Finset.strongInductionOn generalizing turn
  rename_i s ih
  intro A hdisj hrem hinvI hinvII
  by_cases hne : s.Nonempty
  swap
  · -- Base: s = ∅
    simp only [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, roundRobinAux_empty]; exact hinvI
  · -- Step: s nonempty
    rw [roundRobinAux_step w turn s A hne]
    set g := rawBestGood w turn s hne with hg_def
    have hgmem : g ∈ s := rawBestGood_mem w turn s hne
    have hg_not : ∀ k : Fin n, g ∉ A k := hrem g hgmem
    have hij_ne : (i : Fin n) ≠ j := Fin.ne_of_val_ne (Nat.ne_of_lt hij)
    apply ih (s.erase g) (Finset.erase_ssubset hgmem)
      ⟨(turn.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      (Function.update A turn (insert g (A turn)))
    -- Disjointness preserved
    · intro p q hpq; simp only [Function.update_apply]
      by_cases hp : p = turn <;> by_cases hq : q = turn
      · exact absurd (hp.trans hq.symm) hpq
      · rw [if_pos hp, if_neg hq, Finset.disjoint_left]
        intro x hx; simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact fun hxq => (hg_not q) hxq
        · exact Finset.disjoint_left.mp (hdisj turn q (hp ▸ hpq)) hx
      · rw [if_neg hp, if_pos hq, Finset.disjoint_left]
        intro x hx; simp only [Finset.mem_insert]
        rintro (rfl | hxins)
        · exact (hg_not p) hx
        · exact Finset.disjoint_left.mp (hdisj p turn (hq ▸ hpq)) hx hxins
      · rw [if_neg hp, if_neg hq]; exact hdisj p q hpq
    -- Remaining goods not in bundles
    · intro g' hg' k; simp only [Function.update_apply]
      by_cases hk : k = turn
      · rw [if_pos hk]; simp only [Finset.mem_insert]
        rintro (rfl | hins)
        · exact (Finset.mem_erase.mp hg').1 rfl
        · exact hrem g' (Finset.erase_subset _ _ hg') turn (hk ▸ hins)
      · rw [if_neg hk]; exact hrem g' (Finset.erase_subset _ _ hg') k
    -- hinvI': no-envy invariant maintained
    · by_cases hi : i = turn <;> by_cases hj : j = turn
      · exact absurd (hi.trans hj.symm) hij_ne
      · -- turn = i: i picks g; A'[j] = A j, A'[i] = insert g (A i)
        have h1 := Function.update_of_ne hj (insert g (A turn)) A
        have h2 : Function.update A turn (insert g (A turn)) i = insert g (A i) := by
          rw [hi]; exact Function.update_self turn _ A
        rw [h1, h2]; simp only [AdditiveValuation.toValuation]
        rw [Finset.sum_insert (hi ▸ hg_not turn)]
        exact le_trans hinvI (le_add_of_nonneg_left (hnn i g))
      · -- turn = j: j picks g; A'[j] = insert g (A j), A'[i] = A i
        have h1 : Function.update A turn (insert g (A turn)) j = insert g (A j) := by
          rw [hj]; exact Function.update_self turn _ A
        have h2 := Function.update_of_ne hi (insert g (A turn)) A
        rw [h1, h2]; simp only [AdditiveValuation.toValuation]
        rw [Finset.sum_insert (hj ▸ hg_not turn)]
        have := hinvII ⟨by rw [← hj]; exact hij, by rw [← hj]⟩ g hgmem
        simp only [AdditiveValuation.toValuation] at this; rw [add_comm]; exact this
      · -- turn ≠ i, turn ≠ j: bundles unchanged
        have h1 := Function.update_of_ne hj (insert g (A turn)) A
        have h2 := Function.update_of_ne hi (insert g (A turn)) A
        rw [h1, h2]; exact hinvI
    -- hinvII': headroom invariant maintained
    · intro ⟨hlt_turn', hle_turn'⟩ g' hg'
      simp only at hlt_turn' hle_turn'
      by_cases hi : i = turn <;> by_cases hj : j = turn
      · exact absurd (hi.trans hj.symm) hij_ne
      · -- turn = i: i picks g = rawBestGood w i s (since turn = i)
        have h1 := Function.update_of_ne hj (insert g (A turn)) A
        have h2 : Function.update A turn (insert g (A turn)) i = insert g (A i) := by
          rw [hi]; exact Function.update_self turn _ A
        rw [h1, h2]; simp only [AdditiveValuation.toValuation]
        rw [Finset.sum_insert (hi ▸ hg_not turn)]
        have hle : w.weight i g' ≤ w.weight i g := by
          rw [hg_def, ← hi]; exact rawBestGood_le w i s hne (Finset.erase_subset _ _ hg')
        have hab := add_le_add hinvI hle
        simp only [AdditiveValuation.toValuation] at hab
        rw [add_comm (w.weight i g)]; exact hab
      · -- turn = j: vacuous (turn' > j or wraps to 0)
        exfalso
        have hteq : turn.val = j.val := congrArg Fin.val hj.symm
        have hjn : j.val + 1 ≤ n := Nat.succ_le_of_lt j.isLt
        rcases Nat.eq_or_lt_of_le hjn with h | h
        · -- j.val + 1 = n, so (turn.val+1) % n = 0
          have : (turn.val + 1) % n = 0 := by rw [hteq, h, Nat.mod_self]
          omega
        · -- j.val + 1 < n, so (turn.val+1) % n = j.val + 1 > j.val
          have : (turn.val + 1) % n = j.val + 1 := by
            rw [hteq, Nat.mod_eq_of_lt h]
          omega
      · -- turn ≠ i, turn ≠ j: bundles unchanged, deduce old condition
        have h1 := Function.update_of_ne hj (insert g (A turn)) A
        have h2 := Function.update_of_ne hi (insert g (A turn)) A
        rw [h1, h2]
        have : turn.val + 1 ≤ n := Nat.succ_le_of_lt turn.isLt
        rcases Nat.eq_or_lt_of_le this with h | h
        · rw [h, Nat.mod_self] at hlt_turn'; omega
        · rw [Nat.mod_eq_of_lt h] at hlt_turn' hle_turn'
          have hi_lt : i.val < turn.val := by
            rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt_turn') with heq | hlt
            · exact absurd (Fin.ext_iff.mpr heq : i = turn) hi
            · exact hlt
          exact hinvII ⟨hi_lt, by omega⟩ g' (Finset.erase_subset _ _ hg')

/-- **Key lemma — EF1 witness when picking later** (`j.val < i.val`).

    Since agent `j` picks before `i` in every round, when `i` picks `i_r` in round `r`,
    agent `j`'s *next* good `j_{r+1}` (to be picked in round `r+1`) is still available.
    By `rawBestGood_le`: `w.weight i i_r ≥ w.weight i j_{r+1}`. Telescoping:
    `v_i(A_i) ≥ Σ_r v_i(j_{r+1}) = v_i(A_j) − v_i(j_0)`,
    where `j_0` is `j`'s first picked good. So `j_0` is the EF1 witness. -/
private lemma roundRobin_ef1_of_later
    [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G)
    (hnn : ∀ (i : Fin n) (g : G), 0 ≤ w.weight i g)
    (i j : Fin n) (hij : j.val < i.val)
    (hne : ((rawRoundRobinAlloc w allGoods) j).Nonempty) :
    ∃ g ∈ (rawRoundRobinAlloc w allGoods) j,
      w.toValuation.val i ((rawRoundRobinAlloc w allGoods) j \ {g}) ≤
      w.toValuation.val i ((rawRoundRobinAlloc w allGoods) i) := by
  -- Strengthen to a two-phase invariant on `rawRoundRobinAux`:
  --   Phase 1 (A j = ∅, turn ≤ j): j hasn't picked yet.
  --   Phase 2 (∃ g0 ∈ A j): j already picked g0; v_i(A_j \ {g0}) ≤ v_i(A_i),
  --     with headroom ∀ g ∈ remaining, v_i(A_j\{g0}) + w_i(g) ≤ v_i(A_i)
  --     available when i has already picked this cycle (guard: i < turn ∨ turn ≤ j).
  --   Guard analysis:
  --     turn = j: guard is true (j ≤ j), headroom available for j's pick.
  --     turn = i: guard is false, headroom vacuous input; i establishes headroom.
  --     turn between j+1..i-1: guard false, headroom vacuous (pass-through).
  --     turn between i+1..n-1 or 0..j-1: guard true, headroom maintained.
  suffices h : ∀ (turn : Fin n) (remaining : Finset G) (A : Allocation (Fin n) G),
      (∀ p q : Fin n, p ≠ q → Disjoint (A p) (A q)) →
      (∀ g ∈ remaining, ∀ k : Fin n, g ∉ A k) →
      ((A j = ∅ ∧ turn.val ≤ j.val) ∨
       (∃ g0 ∈ A j,
         w.toValuation.val i (A j \ {g0}) ≤ w.toValuation.val i (A i) ∧
         (i.val < turn.val ∨ turn.val ≤ j.val →
           ∀ g ∈ remaining,
             w.toValuation.val i (A j \ {g0}) + w.weight i g ≤
               w.toValuation.val i (A i)))) →
      (∃ g0 ∈ (rawRoundRobinAux w turn remaining A) j,
        w.toValuation.val i ((rawRoundRobinAux w turn remaining A) j \ {g0}) ≤
        w.toValuation.val i ((rawRoundRobinAux w turn remaining A) i)) ∨
      (rawRoundRobinAux w turn remaining A) j = ∅ by
    unfold rawRoundRobinAlloc
    rcases h ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅)
        (fun p q _ => Finset.disjoint_empty_left _)
        (fun g _ k hk => absurd hk (Finset.notMem_empty g))
        (Or.inl ⟨rfl, Nat.zero_le _⟩) with ⟨g0, hg0, hef1⟩ | hempty
    · exact ⟨g0, hg0, hef1⟩
    · exact absurd hempty (Finset.Nonempty.ne_empty hne)
  intro turn remaining
  induction remaining using Finset.strongInductionOn generalizing turn
  rename_i s ih
  intro A hdisj hrem hphase
  by_cases hne_s : s.Nonempty
  swap
  · -- Base: s = ∅
    simp only [Finset.not_nonempty_iff_eq_empty] at hne_s
    rw [hne_s, roundRobinAux_empty]
    rcases hphase with ⟨hempty, _⟩ | ⟨g0, hg0, hef1, _⟩
    · right; exact hempty
    · left; exact ⟨g0, hg0, hef1⟩
  · -- Step: s nonempty
    rw [roundRobinAux_step w turn s A hne_s]
    set g := rawBestGood w turn s hne_s with hg_def
    have hgmem : g ∈ s := rawBestGood_mem w turn s hne_s
    have hg_not : ∀ k : Fin n, g ∉ A k := hrem g hgmem
    have hij_ne : j ≠ i := Fin.ne_of_val_ne (Nat.ne_of_lt hij)
    -- Helper: compute (turn.val + 1) % n
    have htn : turn.val + 1 ≤ n := Nat.succ_le_of_lt turn.isLt
    apply ih (s.erase g) (Finset.erase_ssubset hgmem)
      ⟨(turn.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      (Function.update A turn (insert g (A turn)))
    -- Disjointness preserved
    · intro p q hpq; simp only [Function.update_apply]
      by_cases hp : p = turn <;> by_cases hq : q = turn
      · exact absurd (hp.trans hq.symm) hpq
      · rw [if_pos hp, if_neg hq, Finset.disjoint_left]
        intro x hx; simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact fun hxq => (hg_not q) hxq
        · exact Finset.disjoint_left.mp (hdisj turn q (hp ▸ hpq)) hx
      · rw [if_neg hp, if_pos hq, Finset.disjoint_left]
        intro x hx; simp only [Finset.mem_insert]
        rintro (rfl | hxins)
        · exact (hg_not p) hx
        · exact Finset.disjoint_left.mp (hdisj p turn (hq ▸ hpq)) hx hxins
      · rw [if_neg hp, if_neg hq]; exact hdisj p q hpq
    -- Remaining goods not in bundles
    · intro g' hg' k; simp only [Function.update_apply]
      by_cases hk : k = turn
      · rw [if_pos hk]; simp only [Finset.mem_insert]
        rintro (rfl | hins)
        · exact (Finset.mem_erase.mp hg').1 rfl
        · exact hrem g' (Finset.erase_subset _ _ hg') turn (hk ▸ hins)
      · rw [if_neg hk]; exact hrem g' (Finset.erase_subset _ _ hg') k
    -- Phase invariant maintained
    · rcases hphase with ⟨hempty, hturn_le⟩ | ⟨g0, hg0mem, hef1, hhead⟩
      · -- Phase 1: A[j] = ∅, turn.val ≤ j.val
        by_cases hj : j = turn
        · -- j = turn: j picks g, transitioning to Phase 2
          have h_Aj : Function.update A turn (insert g (A turn)) j = insert g (A j) := by
            rw [hj]; exact Function.update_self turn _ A
          have h_Ai : Function.update A turn (insert g (A turn)) i = A i :=
            Function.update_of_ne (fun h => hij_ne (hj.trans h.symm)) _ _
          right; refine ⟨g, ?_, ?_, ?_⟩
          · rw [h_Aj]; exact Finset.mem_insert_self g (A j)
          · -- v_i(insert g (A j) \ {g}) = v_i(∅) = 0 ≤ v_i(A i)
            rw [h_Aj, Finset.sdiff_singleton_eq_erase, Finset.erase_insert (by
              rw [hempty]; exact Finset.notMem_empty g)]
            rw [h_Ai, hempty]; simp only [AdditiveValuation.toValuation, Finset.sum_empty]
            exact Finset.sum_nonneg (fun x _ => hnn i x)
          · -- Headroom guard: i < turn' ∨ turn' ≤ j → ...
            -- turn' = (j+1) % n. Since j < i < n, j+1 ≤ i < n, so turn' = j+1.
            -- Guard: i < j+1 ∨ j+1 ≤ j. First: j+1 > i ↔ j ≥ i, contradicts j < i.
            -- Second: j+1 ≤ j is false. So guard is false. Headroom vacuous.
            intro hguard; exfalso
            have hjlt : j.val + 1 < n := Nat.lt_of_lt_of_le (Nat.succ_lt_succ hij) i.isLt
            have htv : (turn.val + 1) % n = j.val + 1 := by
              rw [congrArg Fin.val hj.symm, Nat.mod_eq_of_lt hjlt]
            simp only at hguard; rcases hguard with h | h <;> omega
        · -- turn ≠ j (turn.val < j.val): other agent picks, stay in Phase 1
          have hi : i ≠ turn := by
            intro h; rw [h] at hij; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hij hturn_le)
          left; constructor
          · rw [Function.update_of_ne hj]; exact hempty
          · have hturn_lt_j : turn.val < j.val :=
              Nat.lt_of_le_of_ne hturn_le (fun h => hj (Fin.ext_iff.mpr h.symm))
            rcases Nat.eq_or_lt_of_le htn with h | h
            · have : (turn.val + 1) % n = 0 := by rw [h, Nat.mod_self]
              simp only [this]; exact Nat.zero_le _
            · have : (turn.val + 1) % n = turn.val + 1 := Nat.mod_eq_of_lt h
              simp only [this]; omega
      · -- Phase 2: ∃ g0 ∈ A j, EF1 + conditional headroom
        by_cases hi : i = turn <;> by_cases hj : j = turn
        · exact absurd (hj.trans hi.symm) hij_ne
        · -- turn = i: i picks g = rawBestGood w i s; establish headroom
          have h_Aj : Function.update A turn (insert g (A turn)) j = A j :=
            Function.update_of_ne hj _ _
          have h_Ai : Function.update A turn (insert g (A turn)) i = insert g (A i) := by
            rw [hi]; exact Function.update_self turn _ A
          right; refine ⟨g0, ?_, ?_, ?_⟩
          · rw [h_Aj]; exact hg0mem
          · -- EF1: v_i(A j \ {g0}) ≤ v_i(insert g (A i))
            rw [h_Aj, h_Ai]; simp only [AdditiveValuation.toValuation]
            rw [Finset.sum_insert (hi ▸ hg_not turn)]
            exact le_trans hef1 (le_add_of_nonneg_left (hnn i g))
          · -- Headroom: i < turn' ∨ turn' ≤ j → ∀ g' ∈ s.erase g, ...
            -- turn' = (i+1) % n. Guard: i < (i+1)%n ∨ (i+1)%n ≤ j.
            -- If i+1 < n: turn' = i+1, first disjunct true.
            -- If i+1 = n: turn' = 0, second disjunct: 0 ≤ j, true (j : Fin n).
            -- Either way, guard is true, so we need to ESTABLISH headroom.
            intro _hguard g' hg'
            rw [h_Aj, h_Ai]; simp only [AdditiveValuation.toValuation]
            rw [Finset.sum_insert (hi ▸ hg_not turn)]
            -- g = rawBestGood w i s (since turn = i), so w_i(g') ≤ w_i(g)
            have hle : w.weight i g' ≤ w.weight i g := by
              rw [hg_def, ← hi]; exact rawBestGood_le w i s hne_s (Finset.erase_subset _ _ hg')
            have hab := add_le_add hef1 hle
            simp only [AdditiveValuation.toValuation] at hab
            rw [add_comm (w.weight i g)]; exact hab
        · -- turn = j: j picks g; use headroom to prove EF1
          have h_Aj : Function.update A turn (insert g (A turn)) j = insert g (A j) := by
            rw [hj]; exact Function.update_self turn _ A
          have h_Ai : Function.update A turn (insert g (A turn)) i = A i :=
            Function.update_of_ne hi _ _
          -- Guard for current turn is true: i < turn ∨ turn ≤ j.
          -- turn = j, so turn ≤ j (second disjunct). Guard is true.
          have hguard : i.val < turn.val ∨ turn.val ≤ j.val :=
            Or.inr (le_of_eq (congrArg Fin.val hj.symm))
          right; refine ⟨g0, ?_, ?_, ?_⟩
          · rw [h_Aj]; exact Finset.mem_insert_of_mem hg0mem
          · -- v_i(insert g (A j) \ {g0}) ≤ v_i(A i)
            have hg_ne_g0 : g ≠ g0 := fun h => hg_not j (h ▸ hg0mem)
            rw [h_Aj, h_Ai]
            have hsdiff : insert g (A j) \ {g0} = insert g (A j \ {g0}) := by
              ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨hx | hx, hne⟩
                · exact Or.inl hx
                · exact Or.inr ⟨hx, hne⟩
              · rintro (rfl | ⟨hx, hne⟩)
                · exact ⟨Or.inl rfl, hg_ne_g0⟩
                · exact ⟨Or.inr hx, hne⟩
            rw [hsdiff]; simp only [AdditiveValuation.toValuation]
            have hg_not_sdiff : g ∉ A j \ {g0} :=
              fun h => hg_not j (Finset.mem_sdiff.mp h).1
            rw [Finset.sum_insert hg_not_sdiff]
            have := hhead hguard g hgmem
            simp only [AdditiveValuation.toValuation] at this
            rw [add_comm]; exact this
          · -- New headroom guard: i < turn' ∨ turn' ≤ j → ...
            -- turn' = (j+1)%n. Since j < i < n, j+1 ≤ i, j+1 < n, turn' = j+1.
            -- Guard: i < j+1 (false since j < i) or j+1 ≤ j (false). Guard false, vacuous.
            intro hguard'; exfalso
            have hjlt : j.val + 1 < n := Nat.lt_of_lt_of_le (Nat.succ_lt_succ hij) i.isLt
            have htv : (turn.val + 1) % n = j.val + 1 := by
              rw [congrArg Fin.val hj.symm, Nat.mod_eq_of_lt hjlt]
            simp only at hguard'; rcases hguard' with h | h <;> omega
        · -- turn ≠ i, turn ≠ j: bundles unchanged, pass through
          have h_Aj : Function.update A turn (insert g (A turn)) j = A j :=
            Function.update_of_ne hj _ _
          have h_Ai : Function.update A turn (insert g (A turn)) i = A i :=
            Function.update_of_ne hi _ _
          right; refine ⟨g0, ?_, ?_, ?_⟩
          · rw [h_Aj]; exact hg0mem
          · rw [h_Aj, h_Ai]; exact hef1
          · -- Headroom: if guard was true for turn, it stays true for turn'
            -- (or was false and stays false)
            intro hguard' g' hg'
            rw [h_Aj, h_Ai]
            -- Deduce guard was true for turn from guard being true for turn'
            simp only at hguard'
            have hguard_old : i.val < turn.val ∨ turn.val ≤ j.val := by
              rcases Nat.eq_or_lt_of_le htn with h | h
              · -- turn+1 = n, turn' = 0
                rw [h, Nat.mod_self] at hguard'
                rcases hguard' with h' | h'
                · omega
                · left; omega
              · -- turn+1 < n, turn' = turn+1
                rw [Nat.mod_eq_of_lt h] at hguard'
                rcases hguard' with h' | h'
                · left; omega
                · right; omega
            exact hhead hguard_old g' (Finset.erase_subset _ _ hg')

/-- **Round-robin gives EF1** for additive valuations with nonneg weights.

    For `i.val < j.val`: `roundRobin_noEnvy_of_earlier` gives no envy; monotonicity
    (`toValuation_mono`) then makes any good from `A j` a valid EF1 witness.
    For `j.val < i.val`: `roundRobin_ef1_of_later` provides `j`'s first good as witness.

    [Lipton et al. 2004; AGT Ch.11] -/
private theorem rawRoundRobinAlloc_isEF1
    [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G)
    (hnn : ∀ (i : Fin n) (g : G), 0 ≤ w.weight i g) :
    IsEF1 w.toValuation (rawRoundRobinAlloc w allGoods) := by
  intro i j hij hne
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · -- Case i.val < j.val: agent i never envies j; any good from A j is a witness
    obtain ⟨g, hg⟩ := hne
    exact ⟨g, hg, le_trans
      (AdditiveValuation.toValuation_mono w hnn i Finset.sdiff_subset)
      (roundRobin_noEnvy_of_earlier w allGoods hnn i j hlt)⟩
  · -- Case j.val < i.val: j's first good is the EF1 witness
    exact roundRobin_ef1_of_later w allGoods hnn i j hgt hne

/-! ### Bundled additive-instance API -/

/-- `bestGood I i s hs` is a good in `s` maximizing agent `i`'s item weight. -/
noncomputable def bestGood [DecidableEq G]
    (I : AdditiveInstance (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) : G :=
  rawBestGood I.toAdditiveValuation i s hs

omit [NeZero n] in
/-- `bestGood` lies in the candidate set. -/
lemma bestGood_mem [DecidableEq G]
    (I : AdditiveInstance (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) :
    bestGood I i s hs ∈ s :=
  rawBestGood_mem I.toAdditiveValuation i s hs

omit [NeZero n] in
/-- Every candidate good has no larger weight than `bestGood`. -/
lemma bestGood_le [DecidableEq G]
    (I : AdditiveInstance (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) {g : G} (hg : g ∈ s) :
    I.weight i g ≤ I.weight i (bestGood I i s hs) :=
  rawBestGood_le I.toAdditiveValuation i s hs hg

/-- Recursive core of round-robin for bundled additive instances. -/
noncomputable def roundRobinAux [DecidableEq G]
    (I : AdditiveInstance (Fin n) G)
    (turn : Fin n) (remaining : Finset G) (A : Allocation (Fin n) G) :
    Allocation (Fin n) G :=
  rawRoundRobinAux I.toAdditiveValuation turn remaining A

/-- The complete choice round-robin allocation for a bundled additive instance. -/
noncomputable def roundRobinAllocation [DecidableEq G]
    (I : AdditiveInstance (Fin n) G) : Allocation (Fin n) G :=
  roundRobinAux I ⟨0, NeZero.pos n⟩ I.allGoods (fun _ => ∅)

/-- Round-robin as a feasible-allocation rule on bundled additive instances. -/
noncomputable def roundRobinRule [DecidableEq G]
    (I : AdditiveInstance (Fin n) G) :
    {A : Allocation (Fin n) G // I.feasible A} :=
  ⟨roundRobinAllocation I, by
    dsimp [roundRobinAllocation, roundRobinAux, AdditiveInstance.feasible]
    exact rawRoundRobinAlloc_isAllocation I.toAdditiveValuation I.allGoods⟩

/-- `roundRobinAllocation` produces a complete partition of the instance goods. -/
theorem roundRobinAllocation_isAllocation [DecidableEq G]
    (I : AdditiveInstance (Fin n) G) :
    IsAllocation I.allGoods (roundRobinAllocation I) :=
  (roundRobinRule I).2

/-- Round-robin gives EF1 for additive instances with nonnegative item weights. -/
theorem roundRobinAllocation_isEF1 [DecidableEq G]
    (I : AdditiveInstance (Fin n) G)
    (hnn : ∀ (i : Fin n) (g : G), 0 ≤ I.weight i g) :
    I.IsEF1 (roundRobinAllocation I) := by
  change IsEF1 I.toValuation (roundRobinAllocation I)
  dsimp [AdditiveInstance.toValuation, roundRobinAllocation, roundRobinAux]
  exact rawRoundRobinAlloc_isEF1 I.toAdditiveValuation I.allGoods hnn

/-- The bundled round-robin rule is EF1 under nonnegative item weights. -/
theorem roundRobinRule_isEF1 [DecidableEq G]
    (I : AdditiveInstance (Fin n) G)
    (hnn : ∀ (i : Fin n) (g : G), 0 ≤ I.weight i g) :
    I.IsEF1 (roundRobinRule I).1 :=
  roundRobinAllocation_isEF1 I hnn

end Indivisible
end FairDivision
end SocialChoice
