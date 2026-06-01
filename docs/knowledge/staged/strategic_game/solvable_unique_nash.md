---
id: game_theory.strategic_game.dominance.solvable_unique_nash
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Solvable Games Have A Unique Nash Equilibrium
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.dominance.dominance_solvable_game
  - game_theory.strategic_game.dominance.nash_is_rationalizable
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.IESDS
verification:
  statement: accepted
  proof: gap
  alignment: pending
tags:
  - strategic-game
  - rationalizability
  - nash-equilibrium
---

# Solvable Games Have A Unique Nash Equilibrium

If a strategic game is solvable, then it has a unique Nash equilibrium.

## Proof Sketch

Every Nash equilibrium is rationalizable. If $S^\infty$ is a singleton, all Nash
equilibria must equal that singleton profile. Thus there is at most one Nash
equilibrium. In the compact continuous setting of MFoGT, the solvable outcome is
also the unique fixed rationalizable prediction.

## References

- [MFoGT, Cor. 4.5.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. If the game is solvable, it has a unique Nash equilibrium.
