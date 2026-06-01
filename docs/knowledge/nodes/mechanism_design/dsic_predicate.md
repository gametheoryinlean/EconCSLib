---
id: mechanism_design.basic.dsic_predicate
title: DSIC Predicate
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.basic
uses:
- mechanism_design.basic.induced_strategic_game
- game_theory.strategic_game.weakly_dominant_strategy
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBasic
  declarations:
  - Mechanism.IsDSIC
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- dsic
- dominance
---

# DSIC Predicate

A direct mechanism is dominant-strategy incentive compatible when, for every true
type profile and every agent, truthful reporting is weakly dominant in the
strategic game induced by that type profile.

This definition treats DSIC as an instance of the library's strategic-game
dominance API. The mechanism layer supplies reports, outcomes, and utilities;
the strategic-game layer supplies the dominance comparison.

## References

- [AGT, Chapter 9, Def. 9.15] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Incentive compatibility, strategy-proofness, and truthfulness for direct
  mechanisms.
- [AGT, Chapter 9, Section 9.4] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
  Dominant-strategy implementation of mechanism-design objectives.

## Used by auctions

[[mechanism_design.auction.basic.first_price_no_dsic]] (first-price mechanism
is not DSIC), [[mechanism_design.auction.basic.second_price_dsic]]
(second-price mechanism is DSIC).

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_basic_interface` in `blueprint/src/content.tex`.
