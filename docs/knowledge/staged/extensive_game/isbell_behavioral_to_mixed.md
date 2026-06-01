---
id: game_theory.extensive_game.imperfect_information.isbell_behavioral_to_mixed
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Isbell Behavioral-To-Mixed Equivalence
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.linear_extensive_game
  - game_theory.extensive_game.imperfect_information.mixed_behavioral_general_strategies
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - behavioral-strategy
  - mixed-strategy
---

# Isbell Behavioral-To-Mixed Equivalence

If an extensive game is linear for player $i$, then for every behavioral strategy
$\beta_i$ of player $i$ there exists a mixed strategy $\sigma_i$ such that, against
every general strategy of the other players, the induced probability distributions
on terminal nodes coincide.

## Proof Sketch

Given $\beta_i$, define a product distribution on pure strategies by multiplying
the probabilities assigned by $\beta_i$ at all information sets. Since each
information set can occur at most once along a play, the probability of any terminal
history factors through exactly the behavioral probabilities used on that history;
all unused information-set probabilities sum to one. Hence the mixed strategy and
behavioral strategy induce the same outcome distribution.

## References

- [MFoGT, Thm. 6.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. In a game linear for player i, every behavioral strategy is outcome equivalent to a mixed strategy.
