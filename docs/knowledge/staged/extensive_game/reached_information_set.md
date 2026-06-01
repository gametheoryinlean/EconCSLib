---
id: game_theory.extensive_game.imperfect_information.reached_information_set
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Reached Information Set
kind: definition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.behavioral_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - information-set
  - behavioral-strategy
---

# Reached Information Set

An information set $Q$ is reached by a behavioral strategy profile $\beta$ if the
probability of reaching $Q$ under $\beta$ is positive. The set of reached
information sets is denoted $Rch(\beta)$.

When $Q\in Rch(\beta)$, Bayes' rule defines a conditional probability
$\nu_\beta(Q)$ on the nodes of $Q$.

## References

- [MFoGT, Def. 6.3.7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. An information set is reached by a behavioral strategy profile if it has positive probability.
