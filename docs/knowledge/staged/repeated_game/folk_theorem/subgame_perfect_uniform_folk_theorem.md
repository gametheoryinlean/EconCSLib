---
id: game_theory.repeated_game.folk_theorem.subgame_perfect_uniform_folk_theorem
title: Subgame Perfect Uniform Folk Theorem
kind: theorem
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.folk_theorem
uses:
  - game_theory.repeated_game.folk_theorem.uniform_folk_theorem
  - game_theory.extensive_game.perfect_information.subgame_perfect_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - repeated-game
  - folk-theorem
  - subgame-perfect-equilibrium
---

# Subgame Perfect Uniform Folk Theorem

For standard repeated games, requiring subgame perfection does not change the
uniform folk-theorem payoff set:
$$
  E_\infty' = E_\infty = E.
$$

MFoGT obtains this by replacing eternal punishment with finite punishment
phases after which play restarts on the main path.

## References

- [MFoGT, Chapter 8, Thm. 8.5.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Perfect folk theorem for uniform equilibria.
