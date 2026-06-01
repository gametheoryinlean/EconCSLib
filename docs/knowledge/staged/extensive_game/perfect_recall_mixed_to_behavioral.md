---
id: game_theory.extensive_game.imperfect_information.perfect_recall_mixed_to_behavioral
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Kuhn Mixed-To-Behavioral Equivalence
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.perfect_recall
  - game_theory.extensive_game.imperfect_information.mixed_behavioral_general_strategies
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - perfect-recall
  - kuhn-theorem
  - behavioral-strategy
---

# Kuhn Mixed-To-Behavioral Equivalence

If an extensive game has perfect recall for player $i$, then for every mixed
strategy $\sigma_i$ there exists a behavioral strategy $\beta_i$ such that, against
every general strategy of the other players, the induced probability distributions
on terminal nodes coincide.

## Proof Sketch

For each information set reached with positive probability under $\sigma_i$, define
the behavioral probability of an action by conditioning $\sigma_i$ on pure
strategies that reach the information set and choose that action. Perfect recall
makes the probabilities along a reached history telescope: reaching the next
information set is determined by the previous remembered action. Thus the
behavioral strategy reproduces the same terminal probabilities as the original
mixed strategy.

## References

- [MFoGT, Thm. 6.3.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. With perfect recall, every mixed strategy is outcome equivalent to a behavioral strategy.
