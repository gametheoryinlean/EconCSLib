---
id: game_theory.repeated_game.core.standard_repeated_game
title: Standard Repeated Game
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.core
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - repeated-game
---

# Standard Repeated Game

A standard repeated game fixes a finite stage game
$G=(N,(A_i)_{i\in N},(g_i)_{i\in N})$. At every stage, players choose actions
simultaneously, the action profile is publicly observed, and the same stage game
is played again.

A history of length $t$ is an element of $H_t=A^t$, where
$A=\prod_i A_i$. A play is an infinite sequence in $A^\mathbb N$.

## References

- [MFoGT, Chapter 8, Sections 8.1 and 8.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Standard repeated games with complete information and perfect observation.
