---
id: game_theory.extensive_game.imperfect_information.mixed_behavioral_general_strategies
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Mixed Behavioral And General Strategies
kind: definition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.imperfect_information_pure_strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - randomized-strategy
  - behavioral-strategy
---

# Mixed Behavioral And General Strategies

In an extensive game, player $i$ has three common randomized strategy spaces:

1. a mixed strategy is a probability distribution on pure strategies, denoted
   $\Sigma_i=\Delta(S_i)$;
2. a behavioral strategy chooses independently at each information set, assigning
   $\beta^i_k\in\Delta(A_i(P^i_k))$;
3. a general strategy is a probability distribution over behavioral strategies,
   denoted $G_i=\Delta(B_i)$.

These three randomization models need not induce the same distributions over
terminal outcomes unless additional recall conditions hold.

## References

- [MFoGT, Section 6.3.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Three kinds of randomized strategies in extensive form games.
