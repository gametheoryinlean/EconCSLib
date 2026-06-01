---
id: game_theory.strategic_game.dominance.nash_is_rationalizable
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Nash Equilibria Are Rationalizable
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.nash_equilibrium
  - game_theory.strategic_game.dominance.rationalizable_fixed_point
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.IESDS
  declarations:
    - StrategicGame.IsNashEquilibrium.survives
    - StrategicGame.IsNashEquilibrium.isRationalizable
verification:
  statement: accepted
  proof: gap
  alignment: aligned
tags:
  - strategic-game
  - nash-equilibrium
  - rationalizability
---

# Nash Equilibria Are Rationalizable

If $s$ is a Nash equilibrium, then $s$ is rationalizable.

## Proof Sketch

The singleton set $\{s\}$ satisfies
$$
  \{s\}\subseteq BR(\{s\})
$$
because every component of $s$ is a best response to the other components. Since
$S^\infty$ is the largest set $L$ with $L\subseteq BR(L)$, it contains $\{s\}$.

## References

- [MFoGT, Cor. 4.5.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every Nash equilibrium is rationalizable.
