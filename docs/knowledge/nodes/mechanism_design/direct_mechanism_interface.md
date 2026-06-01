---
id: mechanism_design.basic.direct_mechanism_interface
title: Direct Mechanism Interface
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.basic
uses:
- game_theory.strategic_game.strategic_game
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBasic
  declarations:
  - Mechanism
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- direct-mechanism
- dsic
---

# Direct Mechanism Interface

A direct mechanism for agents \(I\), report spaces \(T_i\), and outcomes \(O\)
maps reported types to an outcome. It induces a strategic game by taking reports
as strategies and evaluating outcomes through externally supplied utilities.

This node records the direct revelation structure itself. The induced strategic
game, DSIC predicate, and ex-post individual rationality predicate are separate
basic mechanism-design nodes because they add additional payoff or order
structure.

## References

- [AGT, Chapter 9, Def. 9.14] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Direct-revelation mechanisms and report spaces.
- [MFoGT, Chapter 1, Section 1.1.3] Maschler, Solan, and Zamir, *Game
  Theory*. Social-choice and mechanism-design
  context for outcome rules.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_basic_interface` in `blueprint/src/content.tex`.
