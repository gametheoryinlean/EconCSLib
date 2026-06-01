---
id: game_theory.strategic_game.refinements.discontinuous_nash_existence
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Nash Existence In Better Reply Secure Games
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.refinements.better_reply_secure_game
  - game_theory.strategic_game.refinements.reny_solution_exists
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - discontinuous-game
  - nash-equilibrium
  - existence
---

# Nash Existence In Better Reply Secure Games

If a game is compact, quasi-concave, and better reply secure, then its Nash
equilibrium set is nonempty and compact.

## Proof Sketch

The set of Reny solutions is nonempty and compact. Better reply security turns
every Reny solution profile into a Nash equilibrium. Therefore Nash equilibria
exist, and compactness follows from compactness of the Reny solution set together
with the graph-closure formulation.

## References

- [MFoGT, Cor. 4.8.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Compact quasi-concave better reply secure games have nonempty compact Nash set.
