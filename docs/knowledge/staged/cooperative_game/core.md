---
id: game_theory.cooperative_game.core
title: Core Of A Coalitional Game
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.core
uses:
  - game_theory.cooperative_game.imputation
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Core
  declarations:
    - CoalitionalGame.Core
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - core
  - stability
---

# Core Of A Coalitional Game

The **core** is the set of payoff vectors that no coalition can block.
For a TU game $(N,v)$, a payoff vector $x$ is in the core if:
$$
  \sum_{i \in N} x_i = v(N)
$$
and, for every coalition $S \subseteq N$,
$$
  \sum_{i \in S} x_i \ge v(S).
$$

The first condition allocates the worth of the grand coalition. The second
condition is coalitional rationality: every coalition receives at least the
worth it can secure on its own.

## Lean Status

The Lean predicate `CoalitionalGame.Core` uses the efficient payoff
condition plus the coalition-by-coalition inequality above.

## References

- [MSZ Ch.17, Def 17.2] Maschler, Solan, Zamir, *Game Theory*.
