/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Valuation
import EconCSLib.SocialChoice.FairDivision.Fairness

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness

Fairness predicates for indivisible goods allocation.

## Main definitions

* `IsEnvyFree` — envy-free: every agent weakly prefers their own bundle (EF)
* `IsEF1` — envy-free up to one good: envy vanishes after removing some item (EF1)
* `IsEFX` — envy-free up to any good: envy vanishes after removing any item (EFX)
* `IsProportional` — proportional: each agent values their bundle at ≥ 1/n of total (PROP)
* `IsEquitable` — equitable: all agents achieve the same utility from their bundle (EQ)
* `IsMaxminShare` — maximin share guarantee: each agent's bundle meets their MMS value

## Implication chain

`EFX → EF1` holds unconditionally (existential weakening). For *monotone* valuations,
`EF → EFX → EF1`. These definition-adjacent implications are proved in this file.
For additive valuations with complete allocations, `EF → PROP → MMS`; those additive
cross-notion results live in `SocialChoice.FairDivision.Indivisible.Implications`.

Note: EF1 does **not** imply PROP in general (counterexample: 2 agents, 3 equal-value
goods — give 1 good to agent A and 2 to agent B; A is EF1 but PROP fails).

## References

* Nisan et al., *Algorithmic Game Theory*, Chapters 11–12
* Lipton et al., "On Approximately Fair Allocations of Indivisible Goods" (EC 2004)
* Chaudhury, Garg, Mehlhorn — "EFX Allocations for Three Agents" (EC 2020)
* Bouveret, Chevaleyre, Maudet — "Fair Allocation of Indivisible Goods" (COMSOC Handbook, Ch. 12)
* Budish — "The Combinatorial Assignment Problem" (JPE 2011) [MMS]
-/

open Finset

namespace SocialChoice
namespace FairDivision
namespace Indivisible

variable {N G : Type*}

/-! ### Envy-freeness -/

/-- Envy-free (EF): every agent weakly prefers their own bundle over any other agent's bundle.

    `∀ i j, v_i(A_j) ≤ v_i(A_i)`.

    For indivisible goods, EF allocations need not exist (e.g., 2 agents, 1 good).
    See `IsEF1` for the standard relaxation. [AGT Ch.11] -/
abbrev IsEnvyFree (v : Valuation N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsEnvyFree v.val A

/-! ### EF1 -/

/-- Envy-free up to one good (EF1): for any envied bundle, removing *some* item
    from it eliminates the envy.

    `∀ i ≠ j, A_j nonempty → ∃ g ∈ A_j, v_i(A_j \ {g}) ≤ v_i(A_i)`.

    The `Nonempty` guard is needed because the existential is vacuous for `A j = ∅`
    (an agent cannot envy an empty bundle). EF1 always exists; see `RoundRobin.lean`.
    [AGT Ch.11; Lipton et al. 2004] -/
def IsEF1 [DecidableEq G] (v : Valuation N G) (A : Allocation N G) : Prop :=
  ∀ i j : N, i ≠ j → (A j).Nonempty →
    ∃ g ∈ A j, v.val i (A j \ {g}) ≤ v.val i (A i)

/-! ### EFX -/

/-- Envy-free up to any good (EFX): for any envied bundle, removing *any* item
    from it eliminates the envy.

    `∀ i ≠ j, ∀ g ∈ A_j, v_i(A_j \ {g}) ≤ v_i(A_i)`.

    Strictly stronger than EF1 (any witness vs. some witness). EFX exists for
    n = 2 (trivial) and n = 3 (Chaudhury-Garg-Mehlhorn 2020). Existence for n ≥ 4
    is the major open problem in fair division. [AGT Ch.11; EC 2020 arXiv:2005.06878] -/
def IsEFX [DecidableEq G] (v : Valuation N G) (A : Allocation N G) : Prop :=
  ∀ i j : N, i ≠ j →
    ∀ g ∈ A j, v.val i (A j \ {g}) ≤ v.val i (A i)

/-! ### Proportionality -/

/-- Proportional (PROP): each agent values their bundle at least 1/n of the total value.

    Stated as `v_i(allGoods) ≤ n * v_i(A_i)` to avoid division.

    For indivisible goods, proportional allocations need not exist (2 agents, 1 good).
    [AGT Ch.11] -/
abbrev IsProportional (n : ℕ)
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsProportional n allGoods v.val A

/-! ### Implication theorems -/

section Implications

variable [DecidableEq G]

/-- EFX implies EF1: the universal witness in EFX is in particular an existential
    witness for EF1. -/
theorem IsEFX.isEF1 (v : Valuation N G) (A : Allocation N G)
    (h : IsEFX v A) : IsEF1 v A := fun i j hij ⟨g, hg⟩ => ⟨g, hg, h i j hij g hg⟩

/-- EF implies EFX for *monotone* valuations (removing a good from a bundle
    cannot increase its value).

    Monotonicity is stated as an explicit hypothesis rather than a typeclass because
    abstract `Valuation` does not assume it. Additive valuations with nonneg weights
    satisfy this; see `AdditiveValuation.toValuation_mono`. -/
theorem IsEnvyFree.isEFX_of_mono (v : Valuation N G) (A : Allocation N G)
    (hmono : ∀ i S T, T ⊆ S → v.val i T ≤ v.val i S)
    (hef : IsEnvyFree v A) : IsEFX v A := by
  intro i j hij g hg
  calc v.val i (A j \ {g}) ≤ v.val i (A j) :=
        hmono i (A j) (A j \ {g}) (Finset.sdiff_subset)
    _ ≤ v.val i (A i) := hef i j

end Implications

/-! ### Equitability -/

/-- Equitable (EQ): all agents achieve the same utility from their own bundle.

    `∀ i j, v_i(A_i) = v_j(A_j)`.

    Equitability requires comparable utilities across agents — it is most meaningful when
    valuations are normalized so every agent assigns total value 1 to all goods combined.

    Equitability is incomparable with envy-freeness:
    - EF does not imply EQ: agents may have different utilities from their bundles even
      with no envy (e.g., agent 0 gets a good worth 10 to them, agent 1 gets a good worth
      7 to them; if neither envies the other, EF holds but EQ fails).
    - EQ does not imply EF: equal utilities do not prevent an agent from preferring the
      other's bundle (if agent 0 values both bundles at 5, they may still prefer agent 1's
      bundle by their own measure).

    For divisible goods (normalized valuations), equitable+EF allocations always exist
    (Alon 1987, n²−n cuts suffice). For indivisible goods, equitable allocations may not exist.

    [BCM Ch.12; Proc Ch.13] -/
abbrev IsEquitable (v : Valuation N G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsEquitable v.val A

/-! ### Maximin share -/

/-- Maximin share (MMS) guarantee: each agent's bundle is at least as valuable as their
    maximin share value — the best worst-piece they could guarantee by self-partitioning.

    Formally: for each agent `i`, for every complete allocation `B` of `allGoods`, some
    bundle in `B` has value ≤ `v_i(A_i)` (agent `i`'s bundle in `A`).

    This is equivalent to the standard MMS definition: `v_i(A_i) ≥ MMS_i` where
    `MMS_i = max_{B complete} min_j v_i(B_j)` (the maximum over all complete `n`-partitions
    of the minimum bundle value for agent `i`). The equivalence holds because
    `∀ B, ∃ j, v_i(B_j) ≤ v_i(A_i)` is the same as `∀ B, min_j v_i(B_j) ≤ v_i(A_i)`,
    i.e., `v_i(A_i) ≥ max_B min_j v_i(B_j)`. This formulation avoids `iSup`/`iInf` and
    is stated directly in the real-valued order.

    MMS is the weakest standard fairness guarantee in the hierarchy:
    `EF → EFX → EF1 → PROP → MMS` (for additive normalized valuations).

    Key results:
    - `IsProportional.isMaxminShare` (in `Implications`): PROP implies MMS.
    - MMS allocations almost always exist for additive preferences (Bouveret-Lemaître 2014).
    - MMS allocations need not always exist (Procaccia-Wang 2014 counterexample).
    - At least (3/4)-MMS is always achievable for additive preferences.

    `[Fintype N]` and `[DecidableEq G]` are required by `IsAllocation`.

    [BCM Ch.12; Budish 2011] -/
def IsMaxminShare [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  ∀ i : N, ∀ B : Allocation N G, IsAllocation allGoods B →
    ∃ j : N, v.val i (B j) ≤ v.val i (A i)

end Indivisible
end FairDivision
end SocialChoice
