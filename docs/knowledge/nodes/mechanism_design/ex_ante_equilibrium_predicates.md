---
id: mechanism_design.bayesian.ex_ante_equilibrium_predicates
title: Ex-Ante Equilibrium Predicates
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.bayesian
uses:
- mechanism_design.bayesian.bayesian_mechanisms
- mechanism_design.bayesian.ex_ante_expected_utility
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBayesian
  declarations:
  - BayesianMechanismWithTransfers.IntegrableExAnteUtility
  - BayesianMechanismWithTransfers.IsExAnteBayesianNashEquilibrium
  - DirectBayesianMechanismWithTransfers
  - DirectBayesianMechanismWithTransfers.truthfulStrategy
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- bayesian-mechanism
- bayesian-nash-equilibrium
---

# Ex-Ante Equilibrium Predicates

Bayesian mechanisms with transfers include integrability assumptions for
ex-ante expected utility and an ex-ante Bayesian Nash equilibrium predicate.

The direct Bayesian transfer mechanism interface also provides the truthful
strategy profile used in revelation-principle statements.

## References

- [AGT, Chapter 9, Section 9.6, Defs. 9.41-9.43] Nisan, Roughgarden,
  Tardos, and Vazirani, *Algorithmic Game Theory*. Ex-ante equilibrium predicates for
  Bayesian mechanisms.
- [MFoGT, Chapter 7, Section 7.4.1] Maschler, Solan, and Zamir, *Game
  Theory*. Strategies, interim expectations, and
  Bayesian Nash equilibrium.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_ex_ante_equilibrium` in `blueprint/src/content.tex`.
