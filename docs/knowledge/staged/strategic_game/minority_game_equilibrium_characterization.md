---
id: game_theory.strategic_game.continuous.minority_game_equilibrium_characterization
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Three-Player Minority Game Equilibria
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.equilibrium.mixed_nash_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - nash-equilibrium
  - minority-game
---

# Three-Player Minority Game Equilibria

In the symmetric three-player minority game, each player chooses one of two rooms
and receives payoff $1$ if alone and $0$ otherwise.

Represent a mixed profile by probabilities $p_i\in[0,1]$ of choosing the first
room. For player $i$, let $\{j,k\}$ be the other players. The profile is a Nash
equilibrium if and only if:

1. $p_i=1$ implies $p_j+p_k\le 1$;
2. $p_i=0$ implies $p_j+p_k\ge 1$;
3. $0<p_i<1$ implies $p_j+p_k=1$.

In particular, all non-unanimous pure profiles are Nash equilibria, and the
symmetric mixed profile $p_1=p_2=p_3=1/2$ is a Nash equilibrium.

## References

- [MFoGT, Section 4.12, Exercise 5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Symmetric three-player minority game with two rooms.
