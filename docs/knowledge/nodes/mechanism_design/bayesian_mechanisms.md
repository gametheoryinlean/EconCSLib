---
id: mechanism_design.bayesian.bayesian_mechanisms
title: Bayesian Mechanisms
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.bayesian
uses:
- mechanism_design.basic.direct_mechanism_interface
- mechanism_design.basic.induced_strategic_game
- mechanism_design.transfer.mechanisms_with_transfers
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBayesian
  declarations:
  - BayesianMechanism
  - BayesianMechanism.Strategy
  - BayesianMechanism.StrategyProfile
  - BayesianMechanism.IsMeasurableStrategyProfile
  - BayesianMechanism.inducedMessages
  - BayesianMechanism.toMechanism
  - DirectBayesianMechanism
  - DirectBayesianMechanism.truthfulStrategy
  - BayesianMechanismWithTransfers
  - BayesianMechanismWithTransfers.StrategyProfile
  - BayesianMechanismWithTransfers.inducedAllocation
  - BayesianMechanismWithTransfers.inducedPayments
  - BayesianMechanismWithTransfers.deviate
  - BayesianMechanismWithTransfers.toMechanismWithTransfers
  - BayesianMechanismWithTransfers.toBayesianMechanism
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- bayesian-mechanism
- incomplete-information
---

# Bayesian Mechanisms

Bayesian mechanisms record type spaces, message spaces, a common prior, and
type-contingent strategies. They induce messages from strategy profiles and can
be converted to direct or transfer mechanisms.

For mechanisms with transfers, the interface also records induced allocations,
induced payments, deviations, and the associated Bayesian mechanism obtained by
forgetting the allocation/payment decomposition.

## References

- [AGT, Chapter 9, Section 9.6, Def. 9.41] Nisan, Roughgarden, Tardos,
  and Vazirani, *Algorithmic Game Theory*. Bayesian mechanisms, type spaces,
  strategies, and expected utilities.
- [MFoGT, Chapter 7, Section 7.4] Maschler, Solan, and Zamir, *Game Theory*. Bayesian games and Bayesian equilibrium
  background.

## Used by auctions

[[mechanism_design.auction.bayesian.single_item_framework]] (single-item
Bayesian auction framework).

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_bayesian_interface` in `blueprint/src/content.tex`.
