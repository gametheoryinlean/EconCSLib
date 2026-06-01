---
id: mechanism_design.basic.induced_strategic_game
title: Induced Strategic Game
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.basic
uses:
- mechanism_design.basic.direct_mechanism_interface
- game_theory.strategic_game.strategic_game
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBasic
  declarations:
  - Mechanism.toStrategicGame
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- strategic-game
---

# Induced Strategic Game

Given a direct mechanism \(M\), a utility function, and a true type profile, the
induced strategic game takes each agent's report space as the agent's strategy
space. The payoff of a report profile is the utility of the outcome selected by
the mechanism under the true type profile.

The induced game is the bridge that lets mechanism-design predicates reuse
normal-form equilibrium and dominance notions instead of duplicating them.

## References

- [AGT, Chapter 9, Section 9.4.1, Def. 9.24] Nisan, Roughgarden,
  Tardos, and Vazirani, *Algorithmic Game Theory*. Mechanisms induced as strategic
  games.
- [AGT, Chapter 9, Prop. 9.25] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  The revelation-principle argument connecting induced games and direct
  mechanisms.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_basic_interface` in `blueprint/src/content.tex`.
