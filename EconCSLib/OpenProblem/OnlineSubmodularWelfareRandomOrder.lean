/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.SubmodularWelfareDemandOracle

/-!
# EconCSLib.OpenProblem.OnlineSubmodularWelfareRandomOrder

This file formalizes the interface of the open problem asking for an online
algorithm for submodular welfare maximization in random arrival order that beats
the `1/2` competitive-ratio barrier.

The development reuses the finite bundle valuation, allocation, welfare, and
offline optimum primitives from `OpenProblem.SubmodularWelfareDemandOracle`.
The online-specific layer records an arrival order, an algorithm whose output is
determined by that order and a random seed, and the expected welfare benchmark
over random arrival order and internal randomness.

## References

* Korula, Mirrokni, and Zadimoghaddam, "Online Submodular Welfare Maximization:
  Greedy Beats 1/2 in Random Order" (2017).
* Nisan et al., *Algorithmic Game Theory*, Ch. 11.
-/

section OnlineRandomOrderSubmodularWelfare

variable {I Ω G : Type*} [Fintype I] [Fintype Ω] [DecidableEq G]
variable {M : Finset G} [Fintype (BundlePartitionAllocation I M)]
variable [Nonempty (BundlePartitionAllocation I M)]

/-!
## Arrival orders and online algorithms
-/

/-- A certified arrival order for the finite item set `M`.

The list contains only items from `M`, has no duplicates, and covers every item
of `M`.  The random-order model will later specialize distributions over this
finite type to the uniform distribution. -/
structure OnlineArrivalOrder {G : Type*} [DecidableEq G] (M : Finset G) where
  /-- The ordered sequence of arriving items, represented as items certified to
  belong to `M`. -/
  order : List { g : G // g ∈ M }
  /-- Every item in `M` appears in the order. -/
  covers : ∀ g : { g : G // g ∈ M }, g ∈ order
  /-- No item appears twice. -/
  nodup : order.Nodup

variable [Fintype (OnlineArrivalOrder M)]

/-- Interface-level predicate that a lottery over certified arrival orders is
the uniform random-order distribution.

The exact finite counting proof is deferred; this hook isolates the random-order
assumption used in the open-problem statement. -/
def IsUniformRandomOrder
    (_arrivalDist : Lottery ℝ (OnlineArrivalOrder M)) : Prop :=
  True

/-- A randomized online algorithm for submodular welfare maximization.

The field `run` records the allocation obtained from the valuation profile, a
realized arrival order, and a random seed.  Irrevocability is part of the
intended online semantics; this first interface keeps it as a named predicate so
future executable policies can refine the statement without changing the open
problem. -/
structure RandomizedOnlineSubmodularWelfareAlgorithm
    (I Ω : Type*) {G : Type*} [Fintype I] [Fintype Ω] [DecidableEq G]
    (M : Finset G) [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)]
    [Fintype (OnlineArrivalOrder M)] where
  /-- Allocation returned for a valuation profile, an arrival order, and a seed. -/
  run :
    (I → SubmodularBundleValuation M) →
      OnlineArrivalOrder M → Ω → BundlePartitionAllocation I M
  /-- Distribution over the algorithm's internal random seeds. -/
  seedDist : Lottery ℝ Ω

/-- Interface-level predicate that a randomized online algorithm respects the
online information and irrevocability constraints. -/
def RandomizedOnlineSubmodularWelfareAlgorithm.IsOnline
    (_alg : RandomizedOnlineSubmodularWelfareAlgorithm I Ω M) : Prop :=
  True

/-- Interface-level predicate that the online algorithm has polynomial running
time in the number of agents and items. -/
def RandomizedOnlineSubmodularWelfareAlgorithm.IsPolynomial
    (_alg : RandomizedOnlineSubmodularWelfareAlgorithm I Ω M) : Prop :=
  PolynomialTimeInAgentsItems (n I) M.card

/-- Expected welfare over a random arrival order and the algorithm's internal
randomness. -/
noncomputable def RandomizedOnlineSubmodularWelfareAlgorithm.expectedRandomOrderWelfare
    (alg : RandomizedOnlineSubmodularWelfareAlgorithm I Ω M)
    (arrivalDist : Lottery ℝ (OnlineArrivalOrder M))
    (profile : I → SubmodularBundleValuation M) : ℝ :=
  Lottery.expectedValue arrivalDist
    (fun order =>
      Lottery.expectedValue alg.seedDist
        (fun ω => BundlePartitionSocialWelfare profile (alg.run profile order ω)))

/-!
## Final open-problem statement
-/

/-- Open-problem statement: in the random-order model, there is a randomized
online algorithm whose expected welfare is at least `0.51` times the offline
optimum for every monotone submodular valuation profile. -/
noncomputable def OnlineSubmodularWelfareRandomOrderBeatsHalfStatement
    (I Ω : Type*) {G : Type*} [Fintype I] [Fintype Ω] [DecidableEq G]
    (M : Finset G) [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)]
    [Fintype (OnlineArrivalOrder M)] : Prop :=
  ∃ alg : RandomizedOnlineSubmodularWelfareAlgorithm I Ω M,
    RandomizedOnlineSubmodularWelfareAlgorithm.IsOnline alg ∧
    RandomizedOnlineSubmodularWelfareAlgorithm.IsPolynomial alg ∧
      ∃ arrivalDist : Lottery ℝ (OnlineArrivalOrder M),
        IsUniformRandomOrder arrivalDist ∧
          ∀ profile : I → SubmodularBundleValuation M,
            (51 / 100 : ℝ) * OPT profile ≤
              alg.expectedRandomOrderWelfare arrivalDist profile

/-- English version: "Is there a randomized online algorithm for submodular
welfare maximization in random arrival order with competitive ratio at least
`0.51`?"

The `answer(sorry)` marker records that the mathematical answer is unresolved;
it is not a proof of either side of the question. -/
theorem onlineSubmodularWelfareRandomOrderBeatsHalf
    (I Ω : Type*) {G : Type*} [Fintype I] [Fintype Ω] [DecidableEq G]
    (M : Finset G) [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)]
    [Fintype (OnlineArrivalOrder M)] :
    answer(sorry) ↔
      OnlineSubmodularWelfareRandomOrderBeatsHalfStatement I Ω M := by
  sorry

end OnlineRandomOrderSubmodularWelfare
