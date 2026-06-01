---
id: game_theory.strategic_game.potential.potential_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Potential Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.PotentialGame
  declarations:
    - IsExactPotential
    - IsOrdinalPotential
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - potential-game
---

# Potential Game

For a finite game, a function $P$ on mixed profiles is a potential if every pure
unilateral deviation has the same payoff difference and potential difference:
$$
  g_i(s_i,u_{-i})-g_i(t_i,u_{-i})
  =
  P(s_i,u_{-i})-P(t_i,u_{-i}).
$$

MFoGT also gives an evaluation-game version: a $C^1$ function $W$ is a
potential for $\Phi$ if, along each player's tangent space, the gradient of $W$
is a positive scalar multiple of the player's evaluation vector.

## References

- [MFoGT, Chapter 5, Definitions 5.2.7 and 5.2.8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite and evaluation-game potential functions.
