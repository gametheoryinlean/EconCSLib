/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.SubmodularWelfareDemandOracle

/-!
# EconCSLib.OpenProblem.SubadditiveProphetStaticPricing

This file formalizes the interface of the open problem asking whether static
item prices give a constant-factor prophet inequality for combinatorial auctions
with independent subadditive buyer valuations.

The statement is existential and does not encode computational tractability. It
reuses the bundle allocation and welfare vocabulary from
`OpenProblem.SubmodularWelfareDemandOracle`, adds subadditive valuations, finite
valuation priors, static item prices, tie-breaking rules, and the expected
welfare comparison against the offline optimum.

## References

* Feldman, Gravin, and Lucier, "Combinatorial Auctions via Posted Prices" (2014).
* Dütting, Feldman, Kesselheim, and Lucier, "Prophet Inequalities Made Easy"
  (2020).
* Correa and Cristi, "Prophet Inequalities for Subadditive Combinatorial
  Auctions" (2023).
-/

section SubadditiveProphetStaticPricing

variable {I G Sample : Type*} [Fintype I] [DecidableEq G] [Fintype Sample]
variable {M : Finset G} [Fintype (BundlePartitionAllocation I M)]
variable [Nonempty (BundlePartitionAllocation I M)]

/-!
## Subadditive valuations and welfare
-/

/-- A normalized nonnegative bundle valuation satisfying subadditivity. -/
structure SubadditiveBundleValuation {G : Type*} [DecidableEq G] (M : Finset G)
    extends BundleValuation M where
  /-- Subadditivity of the valuation over feasible bundles. -/
  subadditive : ∀ S T : BundleAllocation M,
    val ⟨S.1 ∪ T.1, by
      intro x hx
      rw [Finset.mem_union] at hx
      exact hx.elim (fun hxS => S.2 hxS) (fun hxT => T.2 hxT)⟩ ≤
        val S + val T

/-- Agent `i`'s induced valuation on subadditive allocation profiles. -/
def SubadditiveBundlePartitionProfileValuation
    (v : I → SubadditiveBundleValuation M) (i : I) :
    MultipleParameterMechanism.Valuation (BundlePartitionAllocation I M) ℝ :=
  fun S => (v i).val (S.1 i)

/-- Social welfare of a disjoint allocation profile under subadditive
valuations. -/
def SubadditiveBundlePartitionSocialWelfare
    (v : I → SubadditiveBundleValuation M)
    (S : BundlePartitionAllocation I M) : ℝ :=
  MultipleParameterMechanism.socialWelfare
    (I := I) (A := BundlePartitionAllocation I M)
    (fun i => SubadditiveBundlePartitionProfileValuation v i) S

/-- A welfare-maximizing disjoint allocation profile for subadditive
valuations. -/
noncomputable def OptimalSubadditiveBundlePartitionAllocation
    (v : I → SubadditiveBundleValuation M) :
    BundlePartitionAllocation I M :=
  MultipleParameterMechanism.efficientAllocation
    (I := I) (A := BundlePartitionAllocation I M)
    (fun i => SubadditiveBundlePartitionProfileValuation v i)

/-- The offline optimal welfare value for a subadditive valuation profile. -/
noncomputable def SubadditiveOPT
    (v : I → SubadditiveBundleValuation M) : ℝ :=
  SubadditiveBundlePartitionSocialWelfare v
    (OptimalSubadditiveBundlePartitionAllocation v)

/-!
## Static pricing instances
-/

/-- A finite prior over subadditive valuation profiles.

The sample type is explicit so expected values can use the library's finite
`Lottery` interface. The `independentPriors` field records the assumption that
the buyer valuations are independently sampled from their known marginals. -/
structure SubadditiveValuationPriorInstance
    (I Sample : Type*) {G : Type*} [DecidableEq G] [Fintype Sample]
    (M : Finset G) where
  /-- A valuation profile associated with each prior sample. -/
  valuationProfile : Sample → I → SubadditiveBundleValuation M
  /-- The finite prior distribution over valuation-profile samples. -/
  prior : Lottery ℝ Sample
  /-- Independence of the buyer-specific valuation priors. -/
  independentPriors : Prop

/-- Static item prices on the ground set `M`. -/
abbrev StaticItemPrices {G : Type*} (M : Finset G) : Type _ :=
  { g : G // g ∈ M } → ℝ

/-- Total posted price of a feasible bundle. -/
def PostedBundlePrice
    (p : StaticItemPrices M) (S : BundleAllocation M) : ℝ :=
  S.1.attach.sum (fun g => p ⟨g.1, S.2 g.2⟩)

/-- A tie-breaking rule for the sequential posted-price process.

The outcome field summarizes the allocation induced by buyers' utility-maximizing
choices at prices `p`. The consistency predicate is kept as a reusable hook so
later files can refine adversarial, lexicographic, or seller-favorable
tie-breaking without changing the prophet-inequality statement. -/
structure PostedPriceTieBreakingRule
    (I : Type*) {G : Type*} [DecidableEq G] (M : Finset G)
    [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)] where
  /-- Allocation produced for prices and a realized valuation profile. -/
  outcome :
    StaticItemPrices M →
      (I → SubadditiveBundleValuation M) → BundlePartitionAllocation I M
  /-- The outcome is consistent with buyers choosing utility-maximizing bundles
  among currently unsold items, under the selected tie-breaking model. -/
  demandConsistent : Prop

/-- Expected welfare of the static posted-price process under a tie-breaking
rule and a valuation prior. -/
noncomputable def ExpectedPostedPriceWelfare
    (Iprior : SubadditiveValuationPriorInstance I Sample M)
    (p : StaticItemPrices M)
    (tb : PostedPriceTieBreakingRule I M) : ℝ :=
  Lottery.expectedValue Iprior.prior
    (fun sample =>
      SubadditiveBundlePartitionSocialWelfare
        (Iprior.valuationProfile sample)
        (tb.outcome p (Iprior.valuationProfile sample)))

/-- Expected offline optimal welfare under the valuation prior. -/
noncomputable def ExpectedSubadditiveOfflineOPT
    (Iprior : SubadditiveValuationPriorInstance I Sample M) : ℝ :=
  Lottery.expectedValue Iprior.prior
    (fun sample => SubadditiveOPT (Iprior.valuationProfile sample))

/-!
## Final open-problem statement
-/

/-- Open-problem statement: there is a universal constant `C` such that every
independent-prior subadditive combinatorial-auction instance admits static item
prices whose expected welfare is at least `1 / C` times the expected offline
optimum, robustly over all demand-consistent tie-breaking rules. -/
noncomputable def SubadditiveProphetStaticPricingStatement
    (I : Type*) {G : Type*} [Fintype I] [DecidableEq G]
    (M : Finset G) [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)] : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Sample : Type*) [Fintype Sample],
      ∀ Iprior : SubadditiveValuationPriorInstance I Sample M,
        Iprior.independentPriors →
          ∃ p : StaticItemPrices M,
            ∀ tb : PostedPriceTieBreakingRule I M,
              tb.demandConsistent →
                (1 / C) * ExpectedSubadditiveOfflineOPT Iprior ≤
                  ExpectedPostedPriceWelfare Iprior p tb

/-- English version: "Do static item prices give a constant-factor prophet
inequality for combinatorial auctions with independent subadditive buyer
valuations?"

The `answer(sorry)` marker records that the mathematical answer is unresolved;
it is not a proof of either side of the question. -/
theorem subadditiveProphetStaticPricing
    (I : Type*) {G : Type*} [Fintype I] [DecidableEq G]
    (M : Finset G) [Fintype (BundlePartitionAllocation I M)]
    [Nonempty (BundlePartitionAllocation I M)] :
    answer(sorry) ↔ SubadditiveProphetStaticPricingStatement I M := by
  sorry

end SubadditiveProphetStaticPricing
