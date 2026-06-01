---
id: game_theory.strategic_game.continuous.mixed_equilibrium_compact_continuous
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Mixed Equilibrium In Compact Continuous Games
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.core.mixed_extension
  - game_theory.strategic_game.continuous.compact_quasi_concave_nash_exists
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - continuous-game
  - mixed-strategy
  - existence
---

# Mixed Equilibrium In Compact Continuous Games

If $G$ is compact and continuous, then its set of mixed equilibria is a nonempty
compact subset of
$$
  \prod_{i\in I}\Delta(S_i).
$$

## Proof Sketch

The mixed strategy spaces $\Delta(S_i)$ are compact in the weak-star topology.
The expected payoff functions in the mixed extension are continuous and
multilinear, hence quasi-concave in each player's mixed strategy. Applying the
compact quasi-concave existence theorem to the mixed extension yields a nonempty
compact set of mixed equilibria.

## References

- [MFoGT, Thm. 4.7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every compact continuous game has a nonempty compact set of mixed equilibria.
