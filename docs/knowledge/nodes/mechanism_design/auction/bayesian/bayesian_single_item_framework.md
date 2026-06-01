---
id: mechanism_design.auction.bayesian.single_item_framework
title: Bayesian Single-Item Auction Framework
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.auction.basic.formats
  - mechanism_design.transfer.single_parameter_transfer_layer
  - mechanism_design.bayesian.bayesian_mechanisms
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.BayesianSingleItem
  declarations:
    - TypeCDF
    - ContinuousTypeProfile
    - OpponentProfile
    - OpponentTypeProfile
    - BayesianSingleItemAuction
    - BayesianSingleItemAuction.profileInsert
    - BayesianSingleItemAuction.toDirectBayesianMechanismWithTransfers
    - BayesianSingleItemAuction.RespectsSingleItemCapacity
    - BayesianSingleItemAuction.IsFeasible
    - BayesianSingleItemAuction.typeDensity
    - BayesianSingleItemAuction.typeMeasure
    - BayesianSingleItemAuction.jointDensity
    - BayesianSingleItemAuction.productPrior
    - BayesianSingleItemAuction.opponentProductPrior
    - BayesianSingleItemAuction.HasIndependentTypePriors
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - bayesian
  - single-item
  - ipv
  - cdf
---

# Bayesian Single-Item Auction Framework

This node bundles the data definitions used to model a sealed-bid
single-item auction in an incomplete-information environment as a direct
Bayesian mechanism with transfers
([[mechanism_design.bayesian.bayesian_mechanisms]]).

## Continuous private-value data

- `TypeCDF (ω : ℝ)` records a one-dimensional scalar type distribution on
  the support interval `[0, ω]`: a CDF `F : ℝ → ℝ` that is monotone on the
  support and continuously differentiable on the open interval `(0, ω)`,
  with normalisation `F(0) = 0` and `F(ω) = 1`.
- `ContinuousTypeProfile I` records a per-agent upper bound `ωᵢ` and CDF
  `Fᵢ : TypeCDF (ωᵢ)`. This is the data structure used to attach
  Myerson-style regularity assumptions to a Bayesian auction without
  forcing them into the abstract mechanism layer.

## Opponent profiles

- `OpponentTypeProfile I i` is the function space `{j // j ≠ i} → ℝ` of
  type reports for everyone except agent `i`.
- `profileInsert i z_i` glues an opponent profile `t₋ᵢ` together
  with agent `i`'s report `z_i` to recover a full report profile
  `(∀ _ : I, ℝ)`.

These objects support the *interim* viewpoint: fixing agent `i`'s report
and integrating over opponents' types.

## Auction structure

A `BayesianSingleItemAuction I` extends `SingleParameterMechanism I ℝ`
([[mechanism_design.transfer.single_parameter_transfer_layer]]) with
Bayesian environment data:

- `prior : Measure (∀ _ : I, ℝ)` — the common-knowledge prior on full
  type profiles, registered as a probability measure.
- `opponentPrior : (i : I) → Measure (OpponentTypeProfile I i)` — explicit
  per-agent opponent marginals, used to define interim expectations
  without committing to an independence assumption at the level of
  measures.
- `typeData : ContinuousTypeProfile I` — the per-agent CDFs and supports
  for Myerson-style analysis.

The reuse pattern is:

- `allocationRule t i : ℝ` — agent `i`'s winning probability at report
  profile `t`, inherited from the single-parameter mechanism.
- `paymentRule t i : ℝ` — agent `i`'s payment at report profile `t`.
- `toDirectBayesianMechanismWithTransfers` exposes the auction as a
  `DirectBayesianMechanismWithTransfers I (fun _ => ℝ) (I → ℝ) ℝ`, so
  Bayesian ex-ante / interim machinery from
  ([[mechanism_design.bayesian.bayesian_mechanisms]]) applies.

## Feasibility

For probabilistic single-item allocation, two constraints matter:

- `IsAllocFeasible` (inherited): every `allocationRule t i` lies in
  `[0, 1]`.
- `RespectsSingleItemCapacity`: for every report profile,
  $\sum_i x_i(t) \le 1$ — at most one item is allocated in expectation.
- `IsFeasible` is the conjunction.

## Density layer (assuming independence)

When the prior is independent across agents, `typeDensity i` returns the
derivative of `Fᵢ`, and `jointDensity t = ∏ᵢ fᵢ(tᵢ)` is the product
density. These are convenience helpers for density-based analysis; the
core mechanism layer does not require independence.

## Product priors

`productPrior` and `opponentProductPrior` build the full type prior and
opponent priors from the one-dimensional density-induced measures. The
predicate `HasIndependentTypePriors` records when the auction's stored priors
are exactly these product priors.

## Position in the library

The single-parameter Myerson payment identity
([[mechanism_design.myerson.payment_formula]]) and the ex-ante revelation
principle ([[mechanism_design.bayesian.ex_ante_revelation_principle]])
both apply to instances of this framework. Concrete IPV models such as
the symmetric first-price equilibrium and Myerson's optimal auction are
tracked separately ([[mechanism_design.auction.bayesian.symmetric_first_price_equilibrium]],
[[mechanism_design.myerson.optimal_auction]]).

## References

- [MFoGT, Chapter 12, Section 12.1] Maschler, Solan, and Zamir, *Game
  Theory*. IPV setting for single-object
  auctions.
- [Krishna, Chapters 2–3] Vijay Krishna, *Auction Theory*, 2nd ed.. Continuous-type private-value model
  with CDFs and densities.
- [AGT, Chapter 9, Section 9.5] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
  Single-parameter Bayesian mechanism design.
