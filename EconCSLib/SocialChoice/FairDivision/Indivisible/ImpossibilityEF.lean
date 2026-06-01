/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
import Mathlib.Tactic.FinCases

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.ImpossibilityEF

Envy-freeness is not always achievable for indivisible goods.

## Main result

* `ef_impossible_two_agents_one_good` — for 2 agents and 1 good that both want,
  every complete allocation is NOT envy-free.

## Proof sketch

Any complete allocation of a single good `{g}` between two agents assigns `{g}`
to exactly one agent and `∅` to the other. The agent receiving `∅` envies the other
whenever they value `g` more than nothing.

This is the canonical impossibility: EF always exists for divisible goods (via
cut-and-choose), but fails even for the simplest indivisible instance.

## References

* Nisan et al., *Algorithmic Game Theory*, Chapter 11
-/

open Finset

namespace SocialChoice
namespace FairDivision
namespace Indivisible

/-! ### Main impossibility theorem -/

/-- **EF Impossibility**: for indivisible goods, envy-free complete allocations
    need not exist.

    For 2 agents and 1 good `g` that both agents strictly prefer to nothing,
    every complete allocation is NOT envy-free.

    *Proof*: any complete allocation of `{g}` gives `g` to one agent (say agent `i`)
    and `∅` to the other (agent `j`). Then `v_j(A_i) = v_j({g}) > v_j(∅) = v_j(A_j)`,
    so agent `j` envies agent `i`.

    Contrast with `SocialChoice.FairDivision.Divisible.CutAndChoose`, where EF
    always exists for two agents with nonatomic divisible measures.
    [AGT Ch.11] -/
theorem ef_impossible_two_agents_one_good {G : Type*}
    [DecidableEq G]
    {g : G}
    (v : Valuation (Fin 2) G)
    (h0 : v.val 0 ∅ < v.val 0 {g})
    (h1 : v.val 1 ∅ < v.val 1 {g})
    {A : Allocation (Fin 2) G} (hA : IsAllocation {g} A) :
    ¬ IsEnvyFree v A := by
  intro hEF
  -- The good g must lie in some agent's bundle (completeness).
  have hg : g ∈ univ.biUnion A := by
    rw [← hA.complete]; exact mem_singleton_self g
  rw [mem_biUnion] at hg
  obtain ⟨i, _, hgi⟩ := hg
  -- Every agent's bundle is a subset of {g} (from completeness).
  have hsubset : ∀ j : Fin 2, A j ⊆ {g} := by
    intro j x hx
    have : x ∈ univ.biUnion A := mem_biUnion.mpr ⟨j, mem_univ j, hx⟩
    rwa [← hA.complete] at this
  -- Case split: which agent holds g?
  fin_cases i
  · -- Agent 0 holds g; agent 1 must get ∅.
    have h01 : A 1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxg := mem_singleton.mp (hsubset 1 hx)
      subst hxg
      exact (disjoint_left.mp (hA.disjoint 1 0 (by decide)) hx) hgi
    have h00 : A 0 = {g} :=
      Subset.antisymm (hsubset 0) (singleton_subset_iff.mpr hgi)
    -- IsEnvyFree says v.val 1 (A 0) ≤ v.val 1 (A 1), i.e., v 1 {g} ≤ v 1 ∅
    have hef := hEF 1 0
    rw [h00, h01] at hef
    -- But h1 says v 1 ∅ < v 1 {g}: contradiction
    exact absurd (lt_of_lt_of_le h1 hef) (lt_irrefl _)
  · -- Agent 1 holds g; agent 0 must get ∅.
    have h10 : A 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxg := mem_singleton.mp (hsubset 0 hx)
      subst hxg
      exact (disjoint_left.mp (hA.disjoint 0 1 (by decide)) hx) hgi
    have h11 : A 1 = {g} :=
      Subset.antisymm (hsubset 1) (singleton_subset_iff.mpr hgi)
    -- IsEnvyFree says v.val 0 (A 1) ≤ v.val 0 (A 0), i.e., v 0 {g} ≤ v 0 ∅
    have hef := hEF 0 1
    rw [h10, h11] at hef
    -- But h0 says v 0 ∅ < v 0 {g}: contradiction
    exact absurd (lt_of_lt_of_le h0 hef) (lt_irrefl _)

end Indivisible
end FairDivision
end SocialChoice
