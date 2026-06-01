---
id: game_theory.extensive_game.imperfect_information.behavioral_equilibrium_exists
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Existence Of Behavioral Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.behavioral_equilibrium
  - game_theory.extensive_game.imperfect_information.perfect_recall_mixed_to_behavioral
  - game_theory.extensive_game.imperfect_information.isbell_behavioral_to_mixed
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - behavioral-strategy
  - nash-equilibrium
  - existence
---

# Existence Of Behavioral Equilibrium

For every finite extensive form game with perfect recall, any mixed equilibrium is
outcome equivalent to a behavioral equilibrium and conversely. In particular,
behavioral equilibria always exist.

## Proof Sketch

Nash's theorem gives a mixed equilibrium of the associated finite normal form.
Kuhn's perfect-recall theorem converts each player's mixed strategy to an
outcome-equivalent behavioral strategy. If the behavioral profile admitted a
profitable behavioral deviation, Isbell's theorem would convert that deviation into
an outcome-equivalent mixed deviation, contradicting mixed equilibrium. The reverse
direction is analogous.

## References

- [MFoGT, Thm. 6.3.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. In every finite perfect-recall extensive game, mixed and behavioral equilibria are outcome-equivalent and behavioral equilibria exist.
