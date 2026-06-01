/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.VCG
import EconCSLib.Foundation.Utility.Lottery
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped BigOperators

/-!
# EconCSLib.OpenProblem.OpenProblem1

This file formalizes the interface of one open problem in algorithmic mechanism
design: randomized submodular welfare maximization with demand queries.

The development is intentionally interface-level. It defines bundle valuations,
value and demand oracles, disjoint bundle allocations, the induced social
welfare and optimum, a randomized algorithm interface, and a final proposition
stating the existence of a polynomial-time demand-oracle algorithm beating the
`1 - 1/e` barrier.

## References

* [Feige, U. and Vondrak, J., 2010. The submodular welfare problem with demand
  queries. Theory of Computing, 6(1), pp.247-290.]
* [Maschler, Solan, Zamir, *Game Theory*, Ch. 11-12]
-/

/-!
## Bundle valuations

Define a bundle valuation by specializing the allocation type from
`MechanismDesign.Auction.Transfer` to the finite powerset `P(M)`. A valuation satisfies:

1. `v(S) ≥ 0`;
2. `v(∅) = 0`;
3. monotonicity: `v(S) ≤ v(T)` for `S ⊆ T ⊆ M`;
4. submodularity: `v(S ∪ {j}) - v(S) ≥ v(T ∪ {j}) - v(T)` for
   `S ⊆ T ⊆ M` and `j ∉ T`.
-/

/-- The bundle-allocation type associated to a finite ground set `M`.

An allocation is a bundle `S : Finset G` equipped with a proof that `S ⊆ M`, i.e. an
element of the finite powerset `P(M)`. -/
abbrev BundleAllocation {G : Type*} (M : Finset G) : Type _ :=
  { S : Finset G // S ⊆ M }

/-- A nonnegative valuation on bundles from a finite ground set.

The value field is expressed using the multiple-parameter valuation type from
`MechanismDesign.Auction.Transfer`, specialized to the allocation type `P(M)` and real values. -/
structure BundleValuation {G : Type*} [DecidableEq G] (M : Finset G) where
  /-- The real-valued valuation function on feasible bundles. -/
  val : MultipleParameterMechanism.Valuation (BundleAllocation M) ℝ
  /-- Values are nonnegative. -/
  nonnegative : ∀ S : BundleAllocation M, 0 ≤ val S
  /-- The empty bundle has value zero. -/
  empty_value : val ⟨∅, by simp⟩ = 0

/-- A bundle valuation that is monotone with respect to bundle inclusion. -/
structure MonotoneBundleValuation {G : Type*} [DecidableEq G] (M : Finset G)
    extends BundleValuation M where
  /-- Monotonicity with respect to bundle inclusion. -/
  monotone : ∀ S T : BundleAllocation M, S.1 ⊆ T.1 → val S ≤ val T

/-- A monotone bundle valuation with diminishing marginal returns. -/
structure SubmodularBundleValuation {G : Type*} [DecidableEq G] (M : Finset G)
    extends MonotoneBundleValuation M where
  /-- Diminishing marginal returns for adding one item. -/
  submodular :
    ∀ (S T : BundleAllocation M) (j : G),
      S.1 ⊆ T.1 → (hjM : j ∈ M) → j ∉ T.1 →
        val ⟨S.1 ∪ {j}, by
          intro x hx
          rw [Finset.mem_union] at hx
          exact hx.elim (fun hxS => S.2 hxS) (by
            intro hxj
            rw [Finset.mem_singleton] at hxj
            simpa [hxj] using hjM)⟩ - val S ≥
        val ⟨T.1 ∪ {j}, by
          intro x hx
          rw [Finset.mem_union] at hx
          exact hx.elim (fun hxT => T.2 hxT) (by
            intro hxj
            rw [Finset.mem_singleton] at hxj
            simpa [hxj] using hjM)⟩ - val T

/-!
## Value and demand oracles

The value oracle returns `v(S)` for a certified submodular valuation. The demand
oracle takes prices `p : M → ℝ` and returns a feasible bundle maximizing
`v(S) - ∑ j ∈ S, p(j)`.
-/

/-- The value oracle associated to a submodular bundle valuation.

It is the specialization of `MultipleParameterMechanism.valueOfAllocation` to the
one-agent reported valuation profile containing `v.val`. -/
def ValueOracle {G : Type*} [DecidableEq G] {M : Finset G}
    (v : SubmodularBundleValuation M) (S : BundleAllocation M) : ℝ :=
  MultipleParameterMechanism.valueOfAllocation
    (I := Unit) (A := BundleAllocation M) (V := ℝ)
    S (fun _ => v.val) ()

/-- A price vector on the finite ground set `M`. -/
abbrev BundlePriceVector {G : Type*} (M : Finset G) : Type _ :=
  { j : G // j ∈ M } → ℝ

/-- Quasi-linear utility of a bundle at prices `p`. -/
def BundleDemandUtility {G : Type*} [DecidableEq G] {M : Finset G}
    (v : SubmodularBundleValuation M) (p : BundlePriceVector M)
    (S : BundleAllocation M) : ℝ :=
  ValueOracle v S - S.1.attach.sum (fun j => p ⟨j.1, S.2 j.2⟩)

/-- Bundles returned by the demand oracle for valuation `v` and price vector `p`.

An element is a feasible bundle together with the assertion that it maximizes
`val(S) - ∑ j ∈ S, p(j)` among all feasible bundles. -/
def DemandOracle {G : Type*} [DecidableEq G] {M : Finset G}
    (v : SubmodularBundleValuation M) (p : BundlePriceVector M) : Type _ :=
  { S : BundleAllocation M //
    ∀ T : BundleAllocation M, BundleDemandUtility v p T ≤ BundleDemandUtility v p S }

/-!
## Disjoint bundle allocations and social welfare
-/

/-- An allocation profile of disjoint bundles from the finite ground set `M`.

Each agent `i : I` receives a feasible bundle `S_i ⊆ M`, and different agents'
bundles are required to be disjoint. The profile need not exhaust all of `M`. -/
def BundlePartitionAllocation (I : Type*) {G : Type*} [DecidableEq G]
    (M : Finset G) : Type _ :=
  { S : I → BundleAllocation M //
    ∀ i j : I, i ≠ j → Disjoint (S i).1 (S j).1 }

/-- The number `n` of agents in a finite allocation index set. -/
abbrev n (I : Type*) [Fintype I] : ℕ :=
  Fintype.card I

/-- Agent `i`'s induced valuation on allocation profiles: evaluate only the
bundle assigned to `i`. -/
def BundlePartitionProfileValuation {I G : Type*} [DecidableEq G] {M : Finset G}
    (v : I → SubmodularBundleValuation M) (i : I) :
    MultipleParameterMechanism.Valuation (BundlePartitionAllocation I M) ℝ :=
  fun S => (v i).val (S.1 i)

/-- Social welfare of a disjoint bundle-allocation profile.

This is the specialization of `MultipleParameterMechanism.socialWelfare` to the
allocation domain `BundlePartitionAllocation I M`, where each agent's valuation
of a full allocation profile is its value for its own assigned bundle. -/
def BundlePartitionSocialWelfare {I G : Type*} [Fintype I] [DecidableEq G]
    {M : Finset G} [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)]
    (v : I → SubmodularBundleValuation M)
    (S : BundlePartitionAllocation I M) : ℝ :=
  MultipleParameterMechanism.socialWelfare
    (I := I) (A := BundlePartitionAllocation I M)
    (fun i => BundlePartitionProfileValuation v i) S

/-- A welfare-maximizing disjoint bundle allocation profile. -/
noncomputable def OptimalBundlePartitionAllocation {I G : Type*}
    [Fintype I] [DecidableEq G] {M : Finset G}
    [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)]
    (v : I → SubmodularBundleValuation M) :
    BundlePartitionAllocation I M :=
  MultipleParameterMechanism.efficientAllocation
    (I := I) (A := BundlePartitionAllocation I M)
    (fun i => BundlePartitionProfileValuation v i)

/-- The optimal social-welfare value for the disjoint bundle-allocation problem. -/
noncomputable def OPT {I G : Type*} [Fintype I] [DecidableEq G] {M : Finset G}
    [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)]
    (v : I → SubmodularBundleValuation M) : ℝ :=
  BundlePartitionSocialWelfare v (OptimalBundlePartitionAllocation v)

/-!
## Randomized algorithms
-/

/-- A value/demand oracle package for one agent.

The functions are the algorithmic interface. The field `valuation` is the
semantic object used to state correctness and welfare; `value_correct` ties the
reported value oracle to the already-defined `ValueOracle`, while
`demandOracle` reuses the already-defined `DemandOracle`, whose subtype
contains the demand-optimality certificate. -/
structure BundleOracle {G : Type*} [DecidableEq G] (M : Finset G) where
  /-- The underlying submodular valuation certified by this oracle package. -/
  valuation : SubmodularBundleValuation M
  /-- Value-query access to the certified valuation. -/
  valueOracle : BundleAllocation M → ℝ
  /-- Correctness of value-query answers. -/
  value_correct : ∀ S : BundleAllocation M, valueOracle S = ValueOracle valuation S
  /-- Demand-query access at every price vector. -/
  demandOracle : (p : BundlePriceVector M) → DemandOracle valuation p

/-- A profile for the submodular-welfare problem with demand queries.

The explicit input is an agent-indexed profile of value/demand oracle packages.
The underlying valuation profile used in welfare analysis is recovered from
those packages. -/
structure SubmodularWelfareMaximizationProfile (I : Type*) {G : Type*} [DecidableEq G]
    (M : Finset G) where
  /-- One certified oracle package for each agent. -/
  oracle : I → BundleOracle M

/-- A randomized executable algorithm for submodular welfare maximization.

The seed type `Ω` is separate from the allocation domain. Supplying a concrete
seed makes `run` deterministic and executable; `seedDist` specifies the
probability law used when taking expectations. -/
structure RandomizedSubmodularWelfareAlgorithm
    (I Ω : Type*) {G : Type*} [Fintype I] [Fintype Ω] [DecidableEq G]
    (M : Finset G) [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)] where
  /-- The allocation profile produced from a valuation/oracle profile and a random seed. -/
  run :
    SubmodularWelfareMaximizationProfile I M → Ω → BundlePartitionAllocation I M
  /-- The probability distribution over random seeds. -/
  seedDist : Lottery ℝ Ω

/-- Expected social welfare of the allocation output by a randomized
submodular-welfare algorithm. -/
noncomputable def expectedBundlePartitionSocialWelfare
    {I Ω G : Type*} [Fintype I] [Fintype Ω] [DecidableEq G]
    {M : Finset G} [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)]
    (A : RandomizedSubmodularWelfareAlgorithm I Ω M)
    (profile : SubmodularWelfareMaximizationProfile I M) : ℝ :=
  Lottery.expectedValue A.seedDist
    (fun ω => BundlePartitionSocialWelfare
      (fun i => (profile.oracle i).valuation) (A.run profile ω))

/-!
## Final open-problem statement
-/

/-- Named predicate for polynomial running time in the number of agents and
items. This is an interface-level placeholder until a concrete cost model is
chosen. -/
def PolynomialTimeInAgentsItems (_agents _items : ℕ) : Prop :=
  True

/-- Named predicate for polynomially many bundle-oracle queries in the number
of agents and items. This covers value and demand queries to `BundleOracle`
packages in this file. -/
def PolynomialBundleOracleQueryBound (_agents _items : ℕ) : Prop :=
  True

/-- Complexity specification for a randomized submodular-welfare algorithm:
polynomial time and polynomially many bundle-oracle queries in `n` agents and
`m` items. -/
def RandomizedSubmodularWelfareAlgorithm.IsPolynomial
    {I Ω G : Type*} [Fintype I] [Fintype Ω] [DecidableEq G]
    {M : Finset G} [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)]
    (_alg : RandomizedSubmodularWelfareAlgorithm I Ω M) : Prop :=
  PolynomialTimeInAgentsItems (n I) M.card ∧
    PolynomialBundleOracleQueryBound (n I) M.card

/-- Open problem: there exists a randomized demand-oracle SWM algorithm beating
the `1 - 1/e` barrier by `0.01` for the fixed agent, item, and seed domains. -/
noncomputable def ExistsDemandOracleSWMAlgorithmBeatingOneMinusInvE
    (I Ω : Type*) {G : Type*} [Fintype I] [Fintype Ω] [DecidableEq G]
    (M : Finset G) [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)] : Prop :=
  ∃ alg : RandomizedSubmodularWelfareAlgorithm I Ω M,
    alg.IsPolynomial ∧
      ∀ profile : SubmodularWelfareMaximizationProfile I M,
        (1 - 1 / Real.exp 1 + (1 / 100 : ℝ)) *
            OPT (fun i => (profile.oracle i).valuation) ≤
          expectedBundlePartitionSocialWelfare alg profile
