---
id: game_theory.strategic_game.equilibrium.strict_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.equilibrium
title: Strict Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.nash_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - nash-equilibrium
---

# Strict Equilibrium

A profile $s\in S$ is a strict equilibrium if
$$
  \{s\}=BR(s).
$$
Equivalently, every player's prescribed strategy is the unique best response to
the other players' prescribed strategies.

## References

- [MFoGT, Def. 4.5.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Strict equilibrium as singleton best-response image.
