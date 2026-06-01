---
id: game_theory.extensive_game.imperfect_information.information_set
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Information Set
kind: definition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.imperfect_information_extensive_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - information-set
  - imperfect-information
---

# Information Set

For player $i$, information is represented by a partition
$$
  \{P^i_k\}_{k\in K_i}
$$
of player $i$'s decision nodes. A part $P^i_k$ is an information set. Nodes in the
same information set cannot be distinguished by player $i$ and must have the same
available physical actions.

## References

- [MFoGT, Section 6.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Information of player i is a partition of that player's decision nodes.
