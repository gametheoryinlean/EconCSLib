/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Range
import Mathlib.Tactic

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle

The **envy-cycle elimination** algorithm and its EF1 correctness proof, stated on the
canonical bundled `AdditiveInstance` interface.

## Main definitions

* `envies v A i j` — agent `i` strictly envies agent `j`: `v_i(A_i) < v_i(A_j)`
* `isSource v A i` — `i` has in-degree 0 in the envy graph (no one envies `i`)
* `isEnvyCycle v A l` — `l` is a directed cycle in the envy graph
* `hasEnvyCycle v A` — the envy graph contains at least one directed cycle
* `rotateBundles A l` — rotate bundles around cycle `l`
* `eliminateAllCycles v A` — iterate rotation until no envy cycle remains
* `findSource v A h` — a source in the acyclic envy graph
* `envyCycleAllocation I` — full bundled algorithm: process `I.allGoods` in list order
* `envyCycleRule I` — the algorithm as a feasible-allocation rule

## Main results

* `rotateBundles_not_mem` — agents outside the cycle are unaffected by rotation
* `rotateBundles_isAllocation` — rotation preserves the partition property
* `rotateBundles_improves` — every agent in the cycle strictly improves after rotation
* `rotateBundles_nondecreasing` — no agent loses value under a rotation step
* `eliminateAllCycles_acyclic` — after elimination, the envy graph contains no cycle
* `eliminateAllCycles_isAllocation` — valid allocations are preserved by elimination
* `eliminateAllCycles_nondecreasing` — agent values do not decrease under elimination
* `eliminateAllCycles_eq_of_acyclic` — elimination is the identity on already-acyclic allocations
* `acyclic_has_source` — a finite acyclic directed graph always has a source
* `findSource_isSource` — the agent returned by `findSource` satisfies `isSource`
* `envyCycleAllocation_isAllocation` — output is a valid complete allocation
* `envyCycleAllocation_isEF1` — output satisfies EF1 for nonnegative additive weights
* `envyCycleRule_isEF1` — rule-style EF1 correctness

## Algorithm outline

Process a list of goods one at a time. The current partial allocation `A` is kept cycle-free
throughout (loop invariant). Each step is:

1. Let `A_dag = eliminateAllCycles v A`  (no-op if `A` is already acyclic).
2. Find a source `s` in the envy graph of `A_dag`  (exists because `A_dag` is a DAG; see
   `acyclic_has_source`).
3. Give the next good `g` to `s`: update `A_dag s ↦ insert g (A_dag s)`.
4. Eliminate any new envy cycles: `eliminateAllCycles v (Function.update A_dag s ...)`.

## Raw implementation layer

The public algorithm below is stated on `AdditiveInstance`. The list-processing core is
parameterized by the raw induced valuation to keep the induction lemmas independent of
bundled-record projection noise.

## EF1 invariant

After each complete step (add good + eliminate cycles), the partial allocation is
**envy-free (EF)** among all agents with nonempty bundles. This is maintained because:
- Before adding `g`, no agent envied the source `s` (source property of step 2).
- Adding `g` to `s` may introduce new envy towards `s`; these are resolved in step 4.
- Envy between non-source agents is unchanged by steps 2–4.

When the last good is allocated the allocation is EF among nonempty-bundle agents, which
implies EF1 globally (the guard `(A j).Nonempty` in `IsEF1` covers agents with `A j = ∅`).

## Termination of `eliminateAllCycles`

Termination is witnessed by the **Pareto domination count**: the number of allocations
`B` such that every agent weakly prefers `B` to the current allocation `A`. Each rotation
step strictly improves at least one agent (and weakly improves all), so this count strictly
decreases. Since `[Fintype N]` and `[Fintype G]` make the set of allocations finite, the
count is bounded and the loop terminates.

## References

* Lipton et al., "On Approximately Fair Allocations of Indivisible Goods" (EC 2004) [L+04]
* Nisan et al., *Algorithmic Game Theory*, Chapter 12
* Bouveret, Chevaleyre, Maudet — COMSOC Handbook, Ch. 12 [BCM]
-/

open Finset

namespace SocialChoice
namespace FairDivision
namespace Indivisible

open Classical in
attribute [local instance] Classical.dec

variable {N G : Type*}

/-! ### Envy relation -/

/-- Agent `i` **envies** agent `j` under valuation `v` and allocation `A`: they strictly
    prefer `j`'s bundle over their own.

    `envies v A i j ↔ v_i(A_i) < v_i(A_j)`.

    An allocation is envy-free (`IsEnvyFree`) iff no agent envies any other. [L+04] -/
def envies (v : Valuation N G) (A : Allocation N G) (i j : N) : Prop :=
  v.val i (A i) < v.val i (A j)

/-- An agent cannot envy themselves: `envies v A i i` is always false. -/
lemma envies_irrefl (v : Valuation N G) (A : Allocation N G) (i : N) :
    ¬ envies v A i i :=
  lt_irrefl _

/-- Envy implies distinct agents: if `i` envies `j` then `i ≠ j`. -/
lemma envies_ne (v : Valuation N G) (A : Allocation N G)
    {i j : N} (h : envies v A i j) : i ≠ j := by
  intro heq; subst heq; exact lt_irrefl _ h

/-! ### Sources in the envy graph -/

/-- Agent `i` is a **source** in the envy graph: no other agent envies `i`.

    Equivalently, `i` has in-degree 0 in the envy graph. Sources always exist in finite
    acyclic graphs (see `acyclic_has_source`). Giving a new good to a source is the key
    step in the algorithm: since no agent envied the source before, the source can only
    attract new envy from the added good — not from pre-existing bundles. -/
def isSource (v : Valuation N G) (A : Allocation N G) (i : N) : Prop :=
  ∀ j : N, ¬ envies v A j i

/-- In an envy-free allocation, every agent is a source. -/
lemma IsEnvyFree.isSource_all (v : Valuation N G) (A : Allocation N G)
    (hef : IsEnvyFree v A) (i : N) : isSource v A i := by
  intro j henv
  exact absurd (lt_of_lt_of_le henv (hef j i)) (lt_irrefl _)

/-! ### Envy cycles -/

/-- A list `l : List N` is a **directed envy cycle** under `v` and `A` if:
    - `l` is nonempty (`0 < l.length`),
    - all elements are distinct (`l.Nodup`), and
    - every consecutive pair (with wrap-around from last to first) is an envy edge.

    For `l = [i₀, i₁, ..., iₖ₋₁]`: agent `iⱼ` envies `i_{(j+1) mod k}` for all `j`.
    In particular `iₖ₋₁` envies `i₀`, closing the directed cycle. [L+04] -/
def isEnvyCycle (v : Valuation N G) (A : Allocation N G)
    (l : List N) : Prop :=
  0 < l.length ∧ l.Nodup ∧
  ∀ k : Fin l.length,
    envies v A (l.get k)
      (l.get ⟨(k.val + 1) % l.length,
        Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)⟩)

/-- The envy graph **has a cycle**: some nonempty list forms a directed envy cycle. -/
def hasEnvyCycle (v : Valuation N G) (A : Allocation N G) : Prop :=
  ∃ l : List N, isEnvyCycle v A l

/-- A directed envy cycle must have length at least 2. A singleton `[i]` would require
    `i` to envy itself, contradicting irreflexivity of `<`. -/
lemma isEnvyCycle_length_ge_two (v : Valuation N G) (A : Allocation N G)
    (l : List N) (hcyc : isEnvyCycle v A l) : 2 ≤ l.length := by
  obtain ⟨hlen, _, hedge⟩ := hcyc
  by_contra h
  push_neg at h
  -- `hlen` rules out length 0; `h` gives length < 2; so length = 1.
  have h1 : l.length = 1 := by omega
  -- At position 0, the successor is (0 + 1) % 1 = 0: the same position.
  have hself := hedge ⟨0, by omega⟩
  simp only [h1, Nat.mod_one] at hself
  exact lt_irrefl _ hself

/-- If `i` is a source, it cannot participate in any envy cycle. -/
lemma isSource_not_mem_envyCycle (v : Valuation N G) (A : Allocation N G)
    (i : N) (hs : isSource v A i) (l : List N) (hcyc : isEnvyCycle v A l) :
    i ∉ l := by
  obtain ⟨hlen, _, hedge⟩ := hcyc
  intro hi
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hi
  -- Predecessor index: the agent whose outgoing edge in the cycle targets j
  let pred : Fin l.length :=
    ⟨(j.val + l.length - 1) % l.length, Nat.mod_lt _ hlen⟩
  -- (pred.val + 1) % l.length = j.val, so the envy edge at pred targets j
  have hsucc : (pred.val + 1) % l.length = j.val := by
    simp only [pred]
    have hj_lt := j.isLt
    rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
    · -- j.val = 0: pred.val = l.length - 1, so pred.val + 1 = l.length ≡ 0
      simp only [hj0, Nat.zero_add]
      have hlt1 : l.length - 1 < l.length := Nat.sub_lt hlen (by omega)
      rw [Nat.mod_eq_of_lt hlt1, Nat.sub_add_cancel hlen, Nat.mod_self]
    · -- j.val > 0: pred.val = j.val - 1, so pred.val + 1 = j.val
      have heq : j.val + l.length - 1 = j.val - 1 + l.length := by omega
      rw [heq, Nat.add_mod_right]
      have hlt2 : j.val - 1 < l.length := Nat.lt_of_le_of_lt (Nat.pred_le _) hj_lt
      rw [Nat.mod_eq_of_lt hlt2, Nat.sub_add_cancel hjpos, Nat.mod_eq_of_lt hj_lt]
  -- The edge at pred: (l.get pred) envies (l.get j)
  have hedge_pred := hedge pred
  have hfin_eq : (⟨(pred.val + 1) % l.length,
        Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) pred.isLt)⟩ : Fin l.length) = j :=
    Fin.ext hsucc
  rw [hfin_eq, hj] at hedge_pred
  -- l.get pred envies i, contradicting isSource v A i
  exact hs (l.get pred) hedge_pred

/-! ### Bundle rotation -/

/-- Rotate bundles around a cycle `l = [i₀, i₁, ..., iₖ₋₁]`:
    agent `iⱼ` receives the bundle currently held by `i_{(j+1) mod k}`.
    Agents not in `l` are unaffected.

    Requires `[DecidableEq N]` for `Function.update`. Correctness lemmas assume `l.Nodup`
    (so each agent appears at most once and the rotation is well-defined).

    After rotation along an envy cycle, every participating agent receives a bundle they
    strictly preferred: `iⱼ` gets `A i_{j+1}` and `envies v A iⱼ i_{j+1}` guarantees
    `v_{iⱼ}(A iⱼ) < v_{iⱼ}(A i_{j+1})`. [L+04] -/
noncomputable def rotateBundles [DecidableEq N] (A : Allocation N G) (l : List N) :
    Allocation N G :=
  -- Build the successor list [i₁, i₂, ..., iₖ₋₁, i₀] by rotating `l` left by one.
  let successors : List N := l.tail ++ l.head?.toList
  -- For each (agent, successor) pair, redirect the agent's bundle to their successor's bundle.
  (l.zip successors).foldl (fun B p => Function.update B p.1 (A p.2)) A

/-! ### Lemmas about `rotateBundles` -/

section RotateBundles

variable [DecidableEq N] [DecidableEq G]

section
omit [DecidableEq G]

/-- Agents not in the cycle are unaffected by bundle rotation. -/
lemma rotateBundles_not_mem (A : Allocation N G) (l : List N) (i : N) (h : i ∉ l) :
    rotateBundles A l i = A i := by
  unfold rotateBundles
  -- Step 1: foldl of updates leaves index i unchanged when all pair.fst ≠ i
  suffices hfoldl : ∀ (ps : List (N × N)) (B : Allocation N G),
      (∀ p ∈ ps, p.1 ≠ i) →
      List.foldl (fun B p => Function.update B p.1 (A p.2)) B ps i = B i by
    apply hfoldl
    intro p hp
    suffices p.1 ∈ l from fun heq => h (heq ▸ this)
    -- Step 2: for any zip, the fst component comes from the first list
    suffices ∀ (l₁ l₂ : List N) (q : N × N), q ∈ l₁.zip l₂ → q.1 ∈ l₁ from this l _ p hp
    intro l₁
    induction l₁ with
    | nil => intro _ _ hq; simp at hq
    | cons x xs ih =>
        intro l₂ q hq
        cases l₂ with
        | nil => simp at hq
        | cons y ys =>
            rw [List.zip_cons_cons, List.mem_cons] at hq
            exact hq.elim (fun heq => heq ▸ List.mem_cons_self)
                          (fun hq' => List.mem_cons_of_mem _ (ih ys q hq'))
  -- Step 3: the foldl helper by induction
  intro ps
  induction ps with
  | nil => intros; rfl
  | cons q qs ih =>
      intro B hq
      simp only [List.foldl_cons]
      rw [ih (Function.update B q.1 (A q.2))
            (fun p hp => hq p (List.mem_cons_of_mem _ hp))]
      exact Function.update_of_ne (Ne.symm (hq q List.mem_cons_self)) (A q.2) B

/--
Each agent in the cycle receives their successor's bundle.
    Concretely, if `i = l.get k`, then `rotateBundles A l i = A (l.get k')` where
    `k' = (k.val + 1) % l.length`.
-/
lemma rotateBundles_mem (A : Allocation N G) (l : List N) (i : N) (h : i ∈ l) :
    ∃ k : Fin l.length, l.get k = i ∧
      ∃ k' : Fin l.length, (k'.val = (k.val + 1) % l.length) ∧
        rotateBundles A l i = A (l.get k') := by
  obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp h;
  obtain ⟨ k', hk' ⟩ : ∃ k' : Fin l.length, l.get k' = i ∧ ∀ j : Fin l.length, l.get j = i → j ≤ k' := by
    exact ⟨ Finset.max' ( Finset.univ.filter fun j => l.get j = i ) ⟨ k, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hk ⟩ ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( Finset.univ.filter fun j => l.get j = i ) ⟨ k, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hk ⟩ ⟩ ) |>.2, fun j hj => Finset.le_max' _ _ ( by aesop ) ⟩;
  refine' ⟨ k', hk'.1, ⟨ ⟨ ( k' + 1 ) % l.length, Nat.mod_lt _ ( Fin.pos k' ) ⟩, rfl, _ ⟩ ⟩ ; simp +decide [ rotateBundles ] ;
  -- By definition of `zip`, the last element in the list `l.zip (l.tail ++ l.head?.toList)` where the first component is `i` is at index `k'`.
  have h_last : List.getLast? (List.zip l (l.tail ++ l.head?.toList) |>.filter (fun p => p.1 = i)) = some (i, l.get ⟨(k'.val + 1) % l.length, Nat.mod_lt _ (Fin.pos k')⟩) := by
    have h_last : List.getLast? (List.map (fun j : Fin l.length => (l.get j, l.get ⟨(j.val + 1) % l.length, Nat.mod_lt _ (Fin.pos j)⟩)) (List.filter (fun j : Fin l.length => l.get j = i) (List.finRange l.length))) = some (i, l.get ⟨(k'.val + 1) % l.length, Nat.mod_lt _ (Fin.pos k')⟩) := by
      have h_last : List.getLast? (List.filter (fun j : Fin l.length => l.get j = i) (List.finRange l.length)) = some k' := by
        have h_sorted : List.Pairwise (· ≤ ·) (List.filter (fun j : Fin l.length => l.get j = i) (List.finRange l.length)) := by
          exact List.Pairwise.filter _ (List.pairwise_le_finRange l.length)
        have h_last : ∀ {l : List (Fin l.length)}, List.Pairwise (· ≤ ·) l → (∀ j ∈ l, j ≤ k') → k' ∈ l → List.getLast? l = some k' := by
          intros l hl_sorted hl_le_k' hl_mem_k'; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.getLast? ] ;
          cases l <;> simp_all +decide [ List.getLast ];
          cases hl_mem_k' <;> grind
        exact h_last h_sorted ( fun j hj => hk'.2 j <| by simpa using List.mem_filter.mp hj |>.2 ) <| List.mem_filter.mpr ⟨ List.mem_finRange _, by simpa using hk'.1 ⟩;
      grind +revert;
    have h_zip : List.zip l (l.tail ++ l.head?.toList) = List.map (fun j : Fin l.length => (l.get j, l.get ⟨(j.val + 1) % l.length, Nat.mod_lt _ (Fin.pos j)⟩)) (List.finRange l.length) := by
      refine' List.ext_get _ _ <;> simp +decide;
      · cases l <;> simp +decide;
      · intro n hn hn' hn''; rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide ;
        rcases n with ( _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        rw [ List.getElem_append ] ; simp +decide;
        split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        cases hn.eq_or_lt <;> first | linarith | aesop;
    rw [ h_zip, List.filter_map ] ; aesop;
  -- By definition of `foldl`, the result of folding the list `l.zip (l.tail ++ l.head?.toList)` with the function `fun B p => Function.update B p.1 (A p.2)` is the same as applying the function to the last element of the list.
  have h_foldl_last : ∀ {L : List (N × N)}, List.getLast? (List.filter (fun p => p.1 = i) L) = some (i, l.get ⟨(k'.val + 1) % l.length, Nat.mod_lt _ (Fin.pos k')⟩) → List.foldl (fun B p => Function.update B p.1 (A p.2)) A L i = A (l.get ⟨(k'.val + 1) % l.length, Nat.mod_lt _ (Fin.pos k')⟩) := by
    intros L hL; induction' L using List.reverseRecOn with L ih <;> simp_all +decide [ Function.update_apply ] ;
    grind +ring;
  exact h_foldl_last h_last

end

/--
Bundle rotation preserves the partition property.

    *Proof sketch*: the goods held by cycle participants are permuted cyclically. The
    disjointness and completeness properties of the partition are maintained because
    the multiset of bundles is merely rearranged — the same goods appear in the same
    total quantity, just redistributed among cycle agents.
-/
lemma rotateBundles_isAllocation [Fintype N]
    {allGoods : Finset G} {A : Allocation N G}
    (hA : IsAllocation allGoods A)
    (l : List N) (hnd : l.Nodup) :
    IsAllocation allGoods (rotateBundles A l) := by
  have h_disjoint : ∀ i j, i ≠ j → Disjoint (rotateBundles A l i) (rotateBundles A l j) := by
    intro i j hij;
    by_cases hi : i ∈ l <;> by_cases hj : j ∈ l <;> simp_all +decide [ rotateBundles_not_mem ];
    · obtain ⟨ k, hk₁, k', hk₂, _ ⟩ := rotateBundles_mem A l i hi
      obtain ⟨ m, hm₁, m', _, _ ⟩ := rotateBundles_mem A l j hj;
      by_cases hkm : k' = m' <;> simp_all +decide;
      · have := Nat.modEq_iff_dvd.mp hk₂.symm; simp_all +decide ;
        obtain ⟨ a, ha ⟩ := this; simp_all +decide [ sub_eq_iff_eq_add ] ;
        exact False.elim ( hij ( by rw [ ← hk₁, ← hm₁ ] ; exact congr_arg _ ( Fin.ext ( by nlinarith [ show a = 0 by nlinarith [ Fin.is_lt k, Fin.is_lt m ] ] ) ) ) );
      · have := hA.disjoint ( l[↑k'] ) ( l[↑m'] ) ; simp_all +decide [ Fin.ext_iff ] ;
        exact this ( by intro h; have := List.nodup_iff_injective_get.mp hnd h; aesop );
    · obtain ⟨ _, _, k', _, _ ⟩ := rotateBundles_mem A l i hi;
      have := hA.disjoint ( l.get k' ) j; aesop;
    · obtain ⟨ _, _, k', _, _ ⟩ := rotateBundles_mem A l j hj;
      have := hA.disjoint i ( l.get k' ) ; aesop;
    · exact hA.disjoint i j hij;
  refine' ⟨ h_disjoint, _ ⟩;
  refine' le_antisymm _ _;
  · intro g hg
    obtain ⟨i, hi⟩ : ∃ i, g ∈ A i := by
      exact hA.mem_biUnion g hg;
    by_cases hi' : i ∈ l <;> simp_all +decide [ Finset.mem_biUnion ];
    · obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hi';
      use l.get ⟨(k.val + l.length - 1) % l.length, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)⟩;
      have h_rotate : ∀ k : Fin l.length, rotateBundles A l (l.get k) = A (l.get ⟨(k.val + 1) % l.length, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)⟩) := by
        intro k
        obtain ⟨ k', hk' ⟩ := rotateBundles_mem A l (l.get k) (by
        exact List.get_mem l k);
        have := List.nodup_iff_injective_get.mp hnd hk'.1; aesop;
      convert hi using 1;
      convert h_rotate ⟨ ( k + l.length - 1 ) % l.length, Nat.mod_lt _ ( Nat.lt_of_le_of_lt ( Nat.zero_le k ) k.isLt ) ⟩ using 1;
      simp +decide [ ← hk, Nat.sub_add_cancel ( show 1 ≤ ( k : ℕ ) + l.length from by linarith [ Fin.is_lt k ] ), Nat.mod_eq_of_lt ];
    · exact ⟨ i, by rw [ rotateBundles_not_mem _ _ _ hi' ] ; exact hi ⟩;
  · have h_complete : ∀ i, rotateBundles A l i ⊆ allGoods := by
      intro i
      by_cases hi : i ∈ l;
      · obtain ⟨ k, hk ⟩ := rotateBundles_mem A l i hi;
        exact hk.2.choose_spec.2.symm ▸ hA.complete.symm ▸ Finset.subset_biUnion_of_mem _ ( Finset.mem_univ _ );
      · rw [ rotateBundles_not_mem _ _ _ hi ];
        exact hA.complete.symm ▸ Finset.subset_biUnion_of_mem _ ( Finset.mem_univ _ );
    exact Finset.biUnion_subset.mpr fun i _ => h_complete i

section
omit [DecidableEq G]

/-- After rotating along an envy cycle `l`, every agent in `l` strictly improves.

    *Proof*: agent `iⱼ` in the cycle satisfies `envies v A iⱼ i_{j+1}`, i.e.,
    `v_{iⱼ}(A iⱼ) < v_{iⱼ}(A i_{j+1})`. After rotation, `iⱼ` holds `A i_{j+1}`, so
    their new value strictly exceeds their old value. -/
lemma rotateBundles_improves
    (v : Valuation N G) (A : Allocation N G)
    (l : List N) (hcyc : isEnvyCycle v A l)
    (i : N) (hi : i ∈ l) :
    v.val i (A i) < v.val i (rotateBundles A l i) := by
  obtain ⟨ k, hk, k', hk', hk'' ⟩ := rotateBundles_mem A l i hi;
  grind +locals

end

section
omit [DecidableEq G]

/-- Bundle rotation does not decrease any agent's value. Cycle participants strictly
    improve (see `rotateBundles_improves`); non-participants are unchanged. -/
lemma rotateBundles_nondecreasing
    (v : Valuation N G) (A : Allocation N G)
    (l : List N) (hcyc : isEnvyCycle v A l)
    (i : N) :
    v.val i (A i) ≤ v.val i (rotateBundles A l i) := by
  by_cases hi : i ∈ l;
  · exact le_of_lt ( rotateBundles_improves v A l hcyc i hi );
  · rw [ rotateBundles_not_mem A l i hi ]

end

end RotateBundles

/-! ### Pareto domination count (termination measure) -/

/-- The number of allocations that weakly Pareto-dominate `A`: every agent weakly
    prefers `B`'s assignment over `A`'s. This count strictly decreases with each
    envy-cycle rotation, providing the termination measure for `eliminateAllCycles`. -/
noncomputable def paretoDomCount [Fintype N] [Fintype G]
    (v : Valuation N G) (A : Allocation N G) : ℕ :=
  (Finset.univ.filter (fun B : N → Finset G => ∀ i : N, v.val i (A i) ≤ v.val i (B i))).card

/--
The Pareto domination set of `A'` is a subset of that of `A` when `A'` weakly
    Pareto-dominates `A`.
-/
lemma paretoDomSet_subset [Fintype N] [Fintype G]
    (v : Valuation N G) (A A' : Allocation N G)
    (h : ∀ i : N, v.val i (A i) ≤ v.val i (A' i)) :
    Finset.univ.filter (fun B : N → Finset G => ∀ i : N, v.val i (A' i) ≤ v.val i (B i)) ⊆
    Finset.univ.filter (fun B : N → Finset G => ∀ i : N, v.val i (A i) ≤ v.val i (B i)) := by
  grind

/--
`A` belongs to its own Pareto domination set (by reflexivity).
-/
lemma self_mem_paretoDomSet [Fintype N] [Fintype G]
    (v : Valuation N G) (A : Allocation N G) :
    A ∈ Finset.univ.filter (fun B : N → Finset G => ∀ i : N, v.val i (A i) ≤ v.val i (B i)) := by
  classical
  refine Finset.mem_filter.mpr ⟨?_, fun _ => le_rfl⟩
  exact Finset.mem_univ (show N → Finset G from A)

/--
If `A'` strictly Pareto-improves over `A` (weakly for all, strictly for some agent),
    then `A` is NOT in the Pareto domination set of `A'`.
-/
lemma not_mem_paretoDomSet_of_strict [Fintype N] [Fintype G]
    (v : Valuation N G) (A A' : Allocation N G)
    (_hweak : ∀ i : N, v.val i (A i) ≤ v.val i (A' i))
    (hstrict : ∃ j : N, v.val j (A j) < v.val j (A' j)) :
    A ∉ Finset.univ.filter (fun B : N → Finset G => ∀ i : N, v.val i (A' i) ≤ v.val i (B i)) := by
  classical
  intro hmem
  obtain ⟨j, hj⟩ := hstrict
  have hle : v.val j (A' j) ≤ v.val j (A j) := (Finset.mem_filter.mp hmem).2 j
  exact (not_lt_of_ge hle) hj

/-- Rotation along an envy cycle strictly decreases the Pareto domination count. -/
lemma rotateBundles_paretoDomCount_lt [Fintype N] [Fintype G] [DecidableEq N]
    (v : Valuation N G) (A : Allocation N G)
    (l : List N) (hcyc : isEnvyCycle v A l) :
    paretoDomCount v (rotateBundles A l) < paretoDomCount v A := by
  unfold paretoDomCount
  apply Finset.card_lt_card
  constructor
  · exact paretoDomSet_subset v A (rotateBundles A l) (rotateBundles_nondecreasing v A l hcyc)
  · intro hsub
    have hmem := self_mem_paretoDomSet v A
    have hnmem := not_mem_paretoDomSet_of_strict v A (rotateBundles A l)
      (rotateBundles_nondecreasing v A l hcyc)
      ⟨l.get ⟨0, hcyc.1⟩, rotateBundles_improves v A l hcyc _ (List.get_mem l ⟨0, hcyc.1⟩)⟩
    exact hnmem (hsub hmem)

/-! ### Cycle elimination -/

/-- Repeatedly rotate envy cycles until none remain, producing a cycle-free allocation.

    `eliminateAllCycles v A` is an allocation reachable from `A` by a finite sequence of
    bundle rotations that contains no directed envy cycle.

    Termination is witnessed by the `paretoDomCount` measure: each rotation step strictly
    decreases the number of allocations that weakly Pareto-dominate the current allocation.
    Since this count is a natural number, the process terminates.

    **Key properties** (proved below):
    - `eliminateAllCycles_acyclic`: the output is cycle-free.
    - `eliminateAllCycles_isAllocation`: the partition property is preserved.
    - `eliminateAllCycles_nondecreasing`: no agent's value decreases.
    - `eliminateAllCycles_eq_of_acyclic`: the identity on already-acyclic inputs. -/
noncomputable def eliminateAllCycles [Fintype N] [Fintype G] [DecidableEq N]
    (v : Valuation N G) (A : Allocation N G) : Allocation N G :=
  @WellFounded.fix (Allocation N G) (fun _ => Allocation N G)
    (InvImage (· < ·) (paretoDomCount v))
    (InvImage.wf _ Nat.lt_wfRel.wf)
    (fun A rec =>
      if h : hasEnvyCycle v A then
        rec (rotateBundles A (Classical.choose h))
          (rotateBundles_paretoDomCount_lt v A _ (Classical.choose_spec h))
      else A)
    A

/-- Unfolding lemma for `eliminateAllCycles`: if a cycle exists, rotate and recurse;
    otherwise return the current allocation. -/
lemma eliminateAllCycles_unfold [Fintype N] [Fintype G] [DecidableEq N]
    (v : Valuation N G) (A : Allocation N G) :
    eliminateAllCycles v A =
      if h : hasEnvyCycle v A then
        eliminateAllCycles v (rotateBundles A (Classical.choose h))
      else A := by
  unfold eliminateAllCycles
  rw [WellFounded.fix_eq]

/-! ### Lemmas about `eliminateAllCycles` -/

section EliminateAllCycles

variable [Fintype N] [Fintype G] [DecidableEq N]

/--
After cycle elimination, the envy graph is acyclic. This is the defining correctness
    property of `eliminateAllCycles`. [L+04]
-/
lemma eliminateAllCycles_acyclic
    (v : Valuation N G) (A : Allocation N G) :
    ¬ hasEnvyCycle v (eliminateAllCycles v A) := by
  apply WellFounded.induction (InvImage.wf (paretoDomCount v) Nat.lt_wfRel.wf) A
  intro A ih
  rw [eliminateAllCycles_unfold]
  split
  · case isTrue h =>
    exact ih _ (rotateBundles_paretoDomCount_lt v A _ (Classical.choose_spec h))
  · case isFalse h => exact h

/--
Cycle elimination preserves the partition property. Each rotation step preserves
    `IsAllocation` by `rotateBundles_isAllocation`, and the composition of
    finitely many such steps preserves it inductively.
-/
lemma eliminateAllCycles_isAllocation [DecidableEq G]
    (v : Valuation N G) {allGoods : Finset G} {A : Allocation N G}
    (hA : IsAllocation allGoods A) :
    IsAllocation allGoods (eliminateAllCycles v A) := by
  -- By induction on the number of rotations, we can show that the eliminateAllCycles function preserves IsAllocation.
  have h_ind : ∀ A : Allocation N G, IsAllocation allGoods A → IsAllocation allGoods (eliminateAllCycles v A) := by
    intro A hA;
    induction' n : paretoDomCount v A using Nat.strong_induction_on with n ih generalizing A;
    by_cases h : hasEnvyCycle v A;
    · rw [ eliminateAllCycles_unfold ];
      have := Classical.choose_spec h;
      have := rotateBundles_isAllocation hA ( Classical.choose h ) this.2.1;
      have := rotateBundles_paretoDomCount_lt v A ( Classical.choose h ) ( Classical.choose_spec h ) ; aesop;
    · rw [ eliminateAllCycles_unfold ] ; aesop;
  exact h_ind A hA

/--
Cycle elimination does not decrease any agent's value (for additive nonneg valuations).

    Each rotation step strictly improves participating agents and leaves others unchanged,
    so the entire sequence of rotations is value-nondecreasing for every agent.
-/
lemma eliminateAllCycles_nondecreasing
    [DecidableEq G]
    (v : Valuation N G) (A : Allocation N G) (i : N) :
    v.val i (A i) ≤ v.val i (eliminateAllCycles v A i) := by
  by_contra! h_contra;
  -- By induction on the number of cycles, we can show that eliminateAllCycles is value-nondecreasing.
  have h_ind : ∀ A : Allocation N G, ∀ i : N, v.val i (A i) ≤ v.val i (eliminateAllCycles v A i) := by
    intro A i;
    induction' n : paretoDomCount v A using Nat.strong_induction_on with n ih generalizing A;
    rw [ eliminateAllCycles_unfold ];
    split_ifs with h;
    · refine' le_trans _ ( ih _ _ _ rfl );
      · exact rotateBundles_nondecreasing v A _ ( Classical.choose_spec h ) i;
      · exact n ▸ rotateBundles_paretoDomCount_lt v A _ ( Classical.choose_spec h );
    · rfl;
  exact (not_lt_of_ge (h_ind A i)) h_contra

/-- Cycle elimination is a fixed point on acyclic inputs: if `A` already has no envy
    cycle, then `eliminateAllCycles v A = A` (no rotation is performed). -/
lemma eliminateAllCycles_eq_of_acyclic
    (v : Valuation N G) (A : Allocation N G)
    (h : ¬ hasEnvyCycle v A) :
    eliminateAllCycles v A = A := by
  rw [eliminateAllCycles_unfold]
  simp [h]

end EliminateAllCycles

/-! ### Sources -/

/--
A finite directed graph with no directed cycle has at least one source (a node with
    in-degree 0).

    *Proof sketch*: start from any agent `i₀`. If `i₀` is a source, done. Otherwise pick
    any `i₁` that envies `i₀`. Repeat: if `i₁` is a source, done; else pick `i₂` envying
    `i₁`. Since `N` is finite, this walk must revisit some node, yielding a directed cycle —
    contradicting `hdag`. Hence the walk must terminate at a source.

    [BCM Ch.12; standard directed graph theory]
-/
lemma acyclic_has_source [Fintype N] [Nonempty N]
    (v : Valuation N G) (A : Allocation N G)
    (hdag : ¬ hasEnvyCycle v A) :
    ∃ i : N, isSource v A i := by
  -- Assume for contradiction that every agent is not a source.
  by_contra h_contra
  push_neg at h_contra;
  -- Since there are no sources, for every agent i, there exists an agent j such that j envies i.
  have h_envy : ∀ i, ∃ j, envies v A j i := by
    exact fun i => by simpa [ isSource ] using h_contra i;
  -- By repeatedly applying `h_envy`, we can construct an infinite sequence of agents where each agent envies the next.
  have h_seq : ∃ seq : ℕ → N, ∀ n, envies v A (seq (n + 1)) (seq n) := by
    exact ⟨ fun n => Nat.recOn n ( Classical.arbitrary N ) fun n ih => Classical.choose ( h_envy ih ), fun n => Classical.choose_spec ( h_envy _ ) ⟩;
  obtain ⟨seq, hseq⟩ := h_seq
  have h_distinct : ∃ m n : ℕ, m < n ∧ seq m = seq n := by
    by_contra h_no_cycle;
    exact absurd ( Set.infinite_range_of_injective ( fun m n hmn => le_antisymm ( not_lt.1 fun contra => h_no_cycle ⟨ n, m, contra, hmn.symm ⟩ ) ( not_lt.1 fun contra => h_no_cycle ⟨ m, n, contra, hmn ⟩ ) ) ) ( Set.not_infinite.mpr <| Set.toFinite _ )
  obtain ⟨m, n, hmn, h_eq⟩ := h_distinct
  have h_cycle : ∃ l : List N, isEnvyCycle v A l := by
    -- Let's choose the smallest $n$ such that $seq(m) = seq(n)$ for some $m < n$.
    obtain ⟨m, n, hmn, h_eq, h_min⟩ : ∃ m n : ℕ, m < n ∧ seq m = seq n ∧ ∀ k l : ℕ, k < l → l < n → seq k ≠ seq l := by
      have h_min : ∃ n, ∃ m < n, seq m = seq n ∧ ∀ k l, k < l → l < n → seq k ≠ seq l := by
        have h_min : ∃ n, ∃ m < n, seq m = seq n := by
          exact ⟨ n, m, hmn, h_eq ⟩;
        obtain ⟨n, hn⟩ : ∃ n, ∃ m < n, seq m = seq n ∧ ∀ k l, k < l → l < n → seq k ≠ seq l := by
          have h_min : ∃ n, ∃ m < n, seq m = seq n ∧ ∀ k l, k < l → l < n → seq k ≠ seq l := by
            have h_well_founded : WellFounded fun n m : ℕ => n < m := by
              exact wellFounded_lt
            have := h_well_founded.has_min { n | ∃ m < n, seq m = seq n } ⟨ _, h_min.choose_spec ⟩;
            obtain ⟨ n, hn₁, hn₂ ⟩ := this; exact ⟨ n, hn₁.choose, hn₁.choose_spec.1, hn₁.choose_spec.2, fun k l hkl hln h => hn₂ _ ⟨ k, hkl, h ⟩ hln ⟩ ;
          exact h_min;
        exact ⟨ n, hn ⟩;
      exact ⟨ _, _, h_min.choose_spec.choose_spec.1, h_min.choose_spec.choose_spec.2.1, h_min.choose_spec.choose_spec.2.2 ⟩;
    refine' ⟨ List.reverse ( List.map seq ( List.range' m ( n - m ) ) ), _, _, _ ⟩ <;> simp_all +decide;
    · rw [ List.nodup_map_iff_inj_on ];
      · grind;
      · grind;
    · intro k
      have h_k_lt : (k : ℕ) < n - m := by
        exact k.2.trans_le ( by simp +decide )
      have h_k_mod : (k + 1) % (n - m) = if k.val + 1 < n - m then k.val + 1 else 0 := by
        split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        rw [ Nat.mod_eq_zero_of_dvd ] ; exact ⟨ 1, by omega ⟩ ;
      simp_all +decide [ Nat.sub_sub, add_comm, add_left_comm, add_assoc ];
      split_ifs <;> simp_all +decide [ add_comm 1, add_assoc ];
      · convert hseq ( m + ( n - ( m + ( k + 2 ) ) ) ) using 1 ; ring_nf;
        exact congr_arg _ ( by omega );
      · grind +ring
  exact hdag h_cycle

/-- Given a proof that the envy graph of `A` is acyclic, returns a source agent.
    The specific agent chosen is unspecified beyond satisfying `isSource`. -/
noncomputable def findSource [Fintype N] [Nonempty N]
    (v : Valuation N G) (A : Allocation N G)
    (hdag : ¬ hasEnvyCycle v A) : N :=
  Classical.choose (acyclic_has_source v A hdag)

/-- The agent returned by `findSource` is indeed a source in the envy graph of `A`. -/
lemma findSource_isSource [Fintype N] [Nonempty N]
    (v : Valuation N G) (A : Allocation N G)
    (hdag : ¬ hasEnvyCycle v A) :
    isSource v A (findSource v A hdag) :=
  Classical.choose_spec (acyclic_has_source v A hdag)

/-! ### Envy-cycle elimination algorithm -/

/-- One step of the algorithm: given a cycle-free partial allocation `A`, add good `g`
    to the source agent, then eliminate all new envy cycles.

    The source is defined via `findSource`. The resulting allocation is again cycle-free
    by `eliminateAllCycles_acyclic`. -/
private noncomputable def envyCycleStep [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]
    (v : Valuation N G) (A : Allocation N G)
    (hdag : ¬ hasEnvyCycle v A) (g : G) : Allocation N G :=
  let s := findSource v A hdag
  eliminateAllCycles v (Function.update A s (insert g (A s)))

/-- After `envyCycleStep`, the resulting allocation is again acyclic.
    This is the loop invariant used by the raw list-processing allocator. -/
private lemma envyCycleStep_acyclic [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]
    (v : Valuation N G) (A : Allocation N G)
    (hdag : ¬ hasEnvyCycle v A) (g : G) :
    ¬ hasEnvyCycle v (envyCycleStep v A hdag g) := by
  exact eliminateAllCycles_acyclic v _

/-- The envy-cycle elimination algorithm: process goods in `goods` one at a time.

    Starting from the empty allocation `fun _ => ∅`, for each good `g` (in list order):
    1. Find a source `s` in the current cycle-free envy graph.
    2. Give `g` to `s`: update `A s ↦ insert g (A s)`.
    3. Eliminate any new envy cycles via `eliminateAllCycles`.

    The initial empty allocation is trivially cycle-free
    (see `rawEnvyCycleElimination_initial_acyclic`). The invariant `¬ hasEnvyCycle v A` is
    maintained at each step by `envyCycleStep_acyclic`.

    `goods : List G` fixes a processing order; the EF1 theorem below is independent of
    that order. The bundled API uses `I.allGoods.toList` as the canonical finite-set
    order. [L+04] -/
private noncomputable def rawEnvyCycleElimination
    [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]
    (v : Valuation N G) (goods : List G) : Allocation N G :=
  goods.foldl (fun (A : Allocation N G) (g : G) =>
    let A_dag : Allocation N G := eliminateAllCycles v A
    let s : N := findSource v A_dag (eliminateAllCycles_acyclic v A)
    eliminateAllCycles v (Function.update A_dag s (insert g (A_dag s)))
  ) (fun (_ : N) => (∅ : Finset G))

/-! ### Correctness theorems -/

section Correctness

variable [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]

section
omit [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]

/-
The empty allocation has no envy cycle: with all bundles empty, `v_i(∅)` is equal for
    all agents, so no strict envy is possible (for additive valuations where `v_i(∅) = 0`).
-/
private lemma rawEnvyCycleElimination_initial_acyclic
     (w : AdditiveValuation N G) :
    ¬ hasEnvyCycle w.toValuation (fun _ => (∅ : Finset G)) := by
  unfold hasEnvyCycle;
  simp +decide [ isEnvyCycle ];
  intro l hl hl'; use ⟨ 0, hl ⟩ ; simp +decide [ envies ] ;

end

/-
**Allocation correctness**: the output of `rawEnvyCycleElimination` is a valid complete
    allocation of `goods.toFinset`.

    Requires `goods.Nodup` to ensure each good appears exactly once, so the output
    partitions `goods.toFinset` exactly.
-/
private theorem rawEnvyCycleElimination_isAllocation
    (v : Valuation N G) (goods : List G) (hnd : goods.Nodup) :
    IsAllocation goods.toFinset (rawEnvyCycleElimination v goods) := by
  revert hnd;
  induction' goods using List.reverseRecOn with goods ih;
  · refine' fun _ => ⟨ _, _ ⟩ <;> simp +decide;
    · unfold rawEnvyCycleElimination; aesop;
    · ext; simp [rawEnvyCycleElimination];
  · intro hgoods;
    have := ‹goods.Nodup → IsAllocation goods.toFinset ( rawEnvyCycleElimination v goods ) › ( List.nodup_append.mp hgoods |>.1 );
    have := eliminateAllCycles_isAllocation v this;
    have := eliminateAllCycles_isAllocation v ( show IsAllocation ( goods.toFinset ∪ { ih } ) ( Function.update ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ( findSource v ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ( eliminateAllCycles_acyclic v ( rawEnvyCycleElimination v goods ) ) ) ( insert ih ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ( findSource v ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ( eliminateAllCycles_acyclic v ( rawEnvyCycleElimination v goods ) ) ) ) ) ) from ?_ );
    · unfold rawEnvyCycleElimination; aesop;
    · constructor;
      · intro i j hij; by_cases hi : i = findSource v ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ( eliminateAllCycles_acyclic v ( rawEnvyCycleElimination v goods ) ) <;> by_cases hj : j = findSource v ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ( eliminateAllCycles_acyclic v ( rawEnvyCycleElimination v goods ) ) <;> simp_all +decide [ Function.update_apply, Finset.disjoint_left ] ;
        · have := this.disjoint j ( findSource v ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ( eliminateAllCycles_acyclic v ( rawEnvyCycleElimination v goods ) ) ) ; simp_all +decide [ Finset.disjoint_left ] ;
          have := ‹IsAllocation goods.toFinset ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ›.complete; simp_all +decide [ Finset.ext_iff ] ;
          grind;
        · intro a ha; have := this.disjoint i ( findSource v ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ( eliminateAllCycles_acyclic v ( rawEnvyCycleElimination v goods ) ) ) hi; simp_all +decide [ Finset.disjoint_left ] ;
          have := ‹IsAllocation goods.toFinset ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ›.complete; simp_all +decide [ Finset.ext_iff ] ;
          grind;
        · exact fun x hx hx' => this.disjoint i j hij |> fun h => Finset.disjoint_left.mp h hx hx';
      · ext x;
        by_cases hx : x = ih <;> simp +decide [ hx ];
        · exact ⟨ findSource v ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ( eliminateAllCycles_acyclic v ( rawEnvyCycleElimination v goods ) ), by simp +decide ⟩;
        · have := this.2.symm; simp_all +decide [ Finset.ext_iff ] ;
          convert this x |> Iff.symm using 1;
          constructor <;> rintro ⟨ a, ha ⟩ <;> use a <;> by_cases ha' : a = findSource v ( eliminateAllCycles v ( rawEnvyCycleElimination v goods ) ) ( eliminateAllCycles_acyclic v ( rawEnvyCycleElimination v goods ) ) <;> simp_all +decide [ Function.update_apply ]

/-! ### Helper lemmas for EF1 -/

/-
Each agent's bundle after rotation is some agent's original bundle.
-/
section
omit [Fintype N] [Fintype G] [Nonempty N] [DecidableEq G]

private lemma rotateBundles_bundle_perm (A : Allocation N G) (l : List N) (j : N) :
    ∃ k : N, rotateBundles A l j = A k := by
  by_cases hj : j ∈ l;
  · -- By rotateBundles_mem, there exists a k such that rotateBundles A l j = A (l.get k').
    obtain ⟨k, hk⟩ := rotateBundles_mem A l j hj;
    aesop;
  · exact ⟨ j, rotateBundles_not_mem A l j hj ⟩

end

/-
Each agent's bundle after `eliminateAllCycles` is some agent's original bundle.
-/
section
omit [Nonempty N]

private lemma eliminateAllCycles_bundle_perm
    (v : Valuation N G) (A : Allocation N G) (j : N) :
    ∃ k : N, eliminateAllCycles v A j = A k := by
  by_contra h;
  -- By induction on the number of cycles, we can show that eliminateAllCycles v A j is indeed some agent's original bundle.
  have h_induction : ∀ n : ℕ, ∀ A : Allocation N G, paretoDomCount v A = n → ∀ j : N, ∃ k : N, eliminateAllCycles v A j = A k := by
    intro n A hn j
    induction' n using Nat.strong_induction_on with n ih generalizing A j;
    rw [eliminateAllCycles_unfold];
    split_ifs with h;
    · obtain ⟨ k, hk ⟩ := ih ( paretoDomCount v ( rotateBundles A ( Classical.choose h ) ) ) ( by linarith [ rotateBundles_paretoDomCount_lt v A ( Classical.choose h ) ( Classical.choose_spec h ) ] ) ( rotateBundles A ( Classical.choose h ) ) rfl j;
      obtain ⟨ k', hk' ⟩ := rotateBundles_bundle_perm A ( Classical.choose h ) k; use k'; aesop;
    · exact ⟨ j, rfl ⟩;
  exact h ( h_induction _ _ rfl _ )

end

/-
For additive nonneg valuations, removing any good from a bundle decreases its value.
-/
section
omit [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N]

private lemma additive_val_erase_le
    (w : AdditiveValuation N G) (hnn : ∀ i g, 0 ≤ w.weight i g)
    (i : N) (S : Finset G) (g : G) (_hg : g ∈ S) :
    w.toValuation.val i (S \ {g}) ≤ w.toValuation.val i S := by
  -- Since $S \setminus \{g\}$ is a subset of $S$, we can apply the monotonicity of the sum.
  have h_subset : S \ {g} ⊆ S := by
    exact Finset.sdiff_subset
  convert Finset.sum_le_sum_of_subset_of_nonneg h_subset fun x hx _ => hnn i x

end

/-
In a linear order, a source's bundle is weakly dominated by every agent's bundle.
-/
section
omit [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]

private lemma isSource_val_le (v : Valuation N G) (A : Allocation N G)
    (s : N) (hs : isSource v A s) (i : N) :
    v.val i (A s) ≤ v.val i (A i) := by
  contrapose! hs;
  exact fun h => h i hs

end

/-
Cycle elimination preserves EF1 for additive nonneg valuations.
    Each output bundle is some input bundle (by `eliminateAllCycles_bundle_perm`),
    and values only increase (by `eliminateAllCycles_nondecreasing`).
    If j's bundle came from a different agent k ≠ i, use EF1 of input at (i,k).
    If j's bundle came from agent i, use `additive_val_erase_le` + nondecreasing.
-/
section
omit [Nonempty N]

private lemma eliminateAllCycles_preserves_ef1

    (w : AdditiveValuation N G) (hnn : ∀ i g, 0 ≤ w.weight i g)
    (A : Allocation N G) (hef1 : IsEF1 w.toValuation A) :
    IsEF1 w.toValuation (eliminateAllCycles w.toValuation A) := by
  -- Let's denote the new allocation as A'.
  set A' : Allocation N G := eliminateAllCycles w.toValuation A;
  -- For any i ≠ j, if (A' j).Nonempty, then there exists k such that A' j = A k.
  have h_exists_k : ∀ i j : N, i ≠ j → (A' j).Nonempty → ∃ k : N, A' j = A k := by
    exact fun _ j _ _ => eliminateAllCycles_bundle_perm w.toValuation A j
  intro i j hij hA'j
  obtain ⟨k, hk⟩ := h_exists_k i j hij hA'j
  by_cases hk_eq_i : k = i;
  · simp_all +decide [ IsEF1 ];
    obtain ⟨g, hg⟩ : ∃ g ∈ A i, w.toValuation.val i (A i \ {g}) ≤ w.toValuation.val i (A i) := by
      exact ⟨ hA'j.choose, hA'j.choose_spec, additive_val_erase_le w hnn i _ _ hA'j.choose_spec ⟩;
    exact ⟨ g, hg.1, hg.2.trans ( eliminateAllCycles_nondecreasing _ _ _ ) ⟩;
  · have := hef1 i k ( Ne.symm hk_eq_i ) ?_ <;> simp_all +decide [ Finset.Nonempty ];
    exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.trans ( eliminateAllCycles_nondecreasing _ _ _ ) ⟩

end

/-
Adding a good to a source preserves EF1. The witness for envy towards s is g.
    Uses the source property (no agent envied s before), so v_i(A s) ≤ v_i(A i).
-/
section
omit [Fintype G]

private lemma update_source_ef1

    (w : AdditiveValuation N G) (hnn : ∀ i g, 0 ≤ w.weight i g)
    (A : Allocation N G) (hef1 : IsEF1 w.toValuation A)
    (hdag : ¬ hasEnvyCycle w.toValuation A) (g : G) :
    let s := findSource w.toValuation A hdag
    IsEF1 w.toValuation (Function.update A s (insert g (A s))) := by
  intro s i j hij hnonempty;
  by_cases hj : j = s <;> simp_all +decide [ Function.update_apply ];
  · -- Since $s$ is a source, we have $w.toValuation.val i (A s) \leq w.toValuation.val i (A i)$.
    have h_source : w.toValuation.val i (A s) ≤ w.toValuation.val i (A i) := by
      exact isSource_val_le _ _ _ ( findSource_isSource _ _ hdag ) _;
    by_cases hg : g ∈ A s <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
    exact Or.inl ( le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.erase_subset _ _ ) fun _ _ _ => hnn _ _ ) h_source );
  · by_cases hi : i = s <;> simp_all +decide [ IsEF1 ];
    obtain ⟨ g', hg', hg'' ⟩ := hef1 s j ( by tauto ) hnonempty;
    refine' ⟨ g', hg', le_trans hg'' _ ⟩;
    exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_insert _ _ ) fun _ _ _ => hnn _ _

end

/-
**EF1 correctness**: the raw output satisfies EF1 for additive nonneg valuations.

    *Proof strategy (induction on `goods.length`)*:
    - *Base case*: the empty allocation is trivially EF1.
    - *Inductive step*: assume the allocation after processing `goods.tail` is EF1 among
      agents with nonempty bundles. Adding the next good to a source agent `s` can only
      introduce envy towards `s`. Since no one envied `s` before (source property), any
      new envy `i → s` satisfies `v_i(A_s' \ {g}) = v_i(A_s) ≤ v_i(A_i)` (the old
      bundle was not envied), giving EF1 with witness `g`. Cycle elimination does not
      break EF1 (values only increase for cycle participants).

    The valuation codomain is fixed to `ℝ`; nonnegative weights are used for
    additive monotonicity. [L+04]
-/
private theorem rawEnvyCycleElimination_isEF1

    (w : AdditiveValuation N G)
    (hnn : ∀ i g, 0 ≤ w.weight i g)
    (goods : List G) (hnd : goods.Nodup) :
    IsEF1 w.toValuation (rawEnvyCycleElimination w.toValuation goods) := by
  induction' goods using List.reverseRecOn with goods g ih;
  · intro i j hij;
    unfold rawEnvyCycleElimination; aesop;
  · unfold rawEnvyCycleElimination;
    simp +zetaDelta at *;
    apply eliminateAllCycles_preserves_ef1;
    · exact hnn;
    · apply_rules [ update_source_ef1 ];
      convert eliminateAllCycles_preserves_ef1 w hnn _ _ using 1;
      convert ih ( List.nodup_append.mp hnd |>.1 ) using 1

end Correctness

/-! ### Bundled additive-instance API -/

/-- The complete envy-cycle-elimination allocation for a bundled additive instance. -/
noncomputable def envyCycleAllocation
    [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]
    (I : AdditiveInstance N G) : Allocation N G :=
  rawEnvyCycleElimination I.toAdditiveValuation.toValuation I.allGoods.toList

/-- Envy-cycle elimination as a feasible-allocation rule on bundled additive instances. -/
noncomputable def envyCycleRule
    [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]
    (I : AdditiveInstance N G) :
    {A : Allocation N G // I.feasible A} :=
  ⟨envyCycleAllocation I, by
    dsimp [envyCycleAllocation, AdditiveInstance.feasible]
    simpa [Finset.toList_toFinset] using
      rawEnvyCycleElimination_isAllocation I.toAdditiveValuation.toValuation
        I.allGoods.toList I.allGoods.nodup_toList⟩

/-- `envyCycleAllocation` produces a complete partition of the instance goods. -/
theorem envyCycleAllocation_isAllocation
    [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]
    (I : AdditiveInstance N G) :
    IsAllocation I.allGoods (envyCycleAllocation I) :=
  (envyCycleRule I).2

/-- Envy-cycle elimination gives EF1 for additive instances with nonnegative item weights. -/
theorem envyCycleAllocation_isEF1
    [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]
    (I : AdditiveInstance N G)
    (hnn : ∀ (i : N) (g : G), 0 ≤ I.weight i g) :
    I.IsEF1 (envyCycleAllocation I) := by
  change IsEF1 I.toValuation (envyCycleAllocation I)
  dsimp [AdditiveInstance.toValuation, envyCycleAllocation]
  exact rawEnvyCycleElimination_isEF1 I.toAdditiveValuation hnn
    I.allGoods.toList I.allGoods.nodup_toList

/-- The bundled envy-cycle-elimination rule is EF1 under nonnegative item weights. -/
theorem envyCycleRule_isEF1
    [Fintype N] [Fintype G] [Nonempty N] [DecidableEq N] [DecidableEq G]
    (I : AdditiveInstance N G)
    (hnn : ∀ (i : N) (g : G), 0 ≤ I.weight i g) :
    I.IsEF1 (envyCycleRule I).1 :=
  envyCycleAllocation_isEF1 I hnn

end Indivisible
end FairDivision
end SocialChoice
