---
id: game_theory.strategic_game.refinements.better_reply_secure_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Better Reply Secure Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.refinements.reny_solution
  - game_theory.strategic_game.nash_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - discontinuous-game
---

# Better Reply Secure Game

A game $G$ is better reply secure if for every Reny solution $(s,v)$, the profile
$s$ is a Nash equilibrium.

In this condition, Nash profiles and the strategy-profile components of Reny
solutions coincide.

## References

- [MFoGT, Def. 4.8.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Better reply security for discontinuous games.
