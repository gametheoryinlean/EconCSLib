---
id: mechanism_design.bayesian.ex_ante_revelation_principle
title: Ex-Ante Revelation Principle Interface
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.bayesian
uses:
- mechanism_design.bayesian.ex_ante_equilibrium_predicates
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBayesian
  declarations:
  - BayesianMechanismWithTransfers.directRevelation
  - BayesianMechanismWithTransfers.ExAnteRevelationPrincipleConclusion
  - BayesianMechanismWithTransfers.exAnte_revelation_principle
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
- mechanism-design
- revelation-principle
- bayesian-nash-equilibrium
---

# Ex-Ante Revelation Principle Interface

Given an indirect Bayesian mechanism with transfers and an ex-ante Bayesian
Nash equilibrium strategy profile, the direct-revelation mechanism induced by
that profile satisfies the ex-ante revelation-principle conclusion.

## References

- [AGT, Chapter 9, Section 9.6, Prop. 9.44] Nisan, Roughgarden, Tardos,
  and Vazirani, *Algorithmic Game Theory*. Bayesian revelation principle for
  ex-ante incentive-compatible direct mechanisms.
- [MFoGT, Chapter 7, Section 7.4] Maschler, Solan, and Zamir, *Game Theory*. Bayesian-game equilibrium background for
  revelation-principle statements.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `thm:md_ex_ante_revelation_interface` in `blueprint/src/content.tex`.
