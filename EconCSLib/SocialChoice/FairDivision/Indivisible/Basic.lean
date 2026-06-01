/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Basic

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.Basic

Foundational definitions for indivisible goods allocation.

## Main definitions

* `Allocation N G` — a function assigning each agent a bundle (Finset of goods)
* `IsAllocation` — predicate that an allocation partitions all goods

## Design

`Allocation` is a plain function type alias; the partition predicate `IsAllocation` is
kept separate so that algorithms can manipulate raw allocations before proving
correctness. `[Fintype N]` and `[DecidableEq G]` are required only by `IsAllocation`
(where `Finset.univ` and `Finset.biUnion` need them), not by the type alias itself.

## References

* Nisan et al., *Algorithmic Game Theory*, Chapter 11
-/

open Finset

namespace SocialChoice
namespace FairDivision
namespace Indivisible

/-! ### Allocation type -/

/-- An allocation assigns each agent `i : N` a bundle (a finite subset of goods `G`).

    This is a plain function type alias. The partition property is stated separately
    in `IsAllocation`, keeping structure and assumptions decoupled. -/
def Allocation (N G : Type*) := N → Finset G

/-! ### Complete allocation (partition) -/

/-- A complete allocation partitions all goods among agents.

    * `disjoint`: distinct agents receive disjoint bundles.
    * `complete`: every good in `allGoods` is allocated to some agent.

    `[Fintype N]` is required for `Finset.univ` in the completeness condition.
    `[DecidableEq G]` is required for `Finset.biUnion` and `Disjoint`.

    [AGT Ch.11] -/
structure IsAllocation {N G : Type*} [Fintype N] [DecidableEq G]
    (allGoods : Finset G) (A : Allocation N G) : Prop where
  /-- Distinct agents receive disjoint bundles. -/
  disjoint : ∀ i j : N, i ≠ j → Disjoint (A i) (A j)
  /-- Every good in `allGoods` is allocated to some agent. -/
  complete  : allGoods = Finset.univ.biUnion A

namespace IsAllocation

variable {N G : Type*} [Fintype N] [DecidableEq G]
variable {allGoods : Finset G} {A : Allocation N G}

/-- Every good in `allGoods` belongs to the bundle of some agent. -/
lemma mem_biUnion (h : IsAllocation allGoods A) (g : G) (hg : g ∈ allGoods) :
    ∃ i : N, g ∈ A i := by
  rw [h.complete] at hg
  simp [Finset.mem_biUnion] at hg
  exact hg

end IsAllocation

end Indivisible
end FairDivision
end SocialChoice
