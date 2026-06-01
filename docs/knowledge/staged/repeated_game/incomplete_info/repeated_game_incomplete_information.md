---
id: game_theory.repeated_game.incomplete_info.repeated_game_incomplete_information
title: Repeated Game With Incomplete Information
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.incomplete_info
uses:
  - game_theory.strategic_game.bayesian.bayesian_game
  - game_theory.repeated_game.core.standard_repeated_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - repeated-game
  - incomplete-information
---

# Repeated Game With Incomplete Information

In the one-sided zero-sum model treated by MFoGT, a state $k$ is drawn from a
prior $p\in\Delta(K)$. Player 1 observes $k$, player 2 observes only the prior,
and the corresponding zero-sum stage game is repeated.

Actions are observed after each stage, so player 1's actions may both affect
payoffs and reveal information about the state.

## References

- [MFoGT, Chapter 8, Section 8.6.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Repeated zero-sum games with lack of information on one side.
