---
id: game_theory.strategic_game.core.symmetric_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.core
title: Symmetric Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - symmetry
---

# Symmetric Game

A strategic game has a symmetry $\phi$ if $\phi$ is a permutation of the player
set, induces bijections $S_i\to S_{\phi(i)}$, and preserves payoffs:
$$
  g_{\phi(i)}(\phi(s))=g_i(s)
  \quad\text{for all } i\in I,\ s\in S.
$$
The same permutation acts on mixed profiles by transporting probability mass along
the induced bijections of strategy sets.

## References

- [MFoGT, Thm. 4.6.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Definition of a game symmetry used before the symmetric equilibrium theorem.
