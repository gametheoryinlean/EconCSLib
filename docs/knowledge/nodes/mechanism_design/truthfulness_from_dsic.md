---
id: mechanism_design.basic.truthfulness_from_dsic
title: Truthfulness From DSIC
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.basic
uses:
- mechanism_design.basic.dsic_predicate
- mechanism_design.basic.induced_strategic_game
- game_theory.strategic_game.nash_equilibrium
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBasic
  declarations:
  - Mechanism.IsDSIC.truthful_isNash
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
- mechanism-design
- dsic
- nash-equilibrium
---

# Truthfulness From DSIC

In a direct mechanism, if truthful reporting is dominant-strategy incentive
compatible, then the truthful reporting profile is a Nash equilibrium of the
induced strategic game.

## References

- [AGT, Chapter 9, Def. 9.15] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Truthfulness as dominant-strategy incentive compatibility.
- [AGT, Chapter 9, Prop. 9.25] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Truthful direct mechanisms obtained from equilibrium behavior in induced
  mechanisms.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `thm:md_basic_truthful` in `blueprint/src/content.tex`.
