---
id: game_theory.strategic_game.refinements.proper_vs_perfect_equilibrium_examples
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Proper And Perfect Equilibrium Examples
kind: example
status: staged
uses:
  - game_theory.strategic_game.refinements.proper_equilibrium
  - game_theory.strategic_game.dominance.dominated_strategy
verification:
  proof: not_applicable
tags:
  - strategic-game
  - equilibrium-refinement
  - example
---

# Proper And Perfect Equilibrium Examples

MFoGT gives two useful warning examples in Section 6.5.

First, proper equilibrium is a strict refinement of perfect equilibrium. In the
three-by-three game with rows $T,M,B$ and columns $l,m,r$:

- row $T$ has payoffs $(1,1)$, $(0,0)$, $(-1,-2)$;
- row $M$ has payoffs $(0,0)$, $(0,0)$, $(0,-2)$;
- row $B$ has payoffs $(-2,-1)$, $(-2,0)$, $(-2,-2)$.

the profile $(M,m)$ is perfect but not proper.

Second, proper equilibrium can still depend on strictly dominated strategies.
In the battle-of-the-sexes game with outside option,
with rows $T,M,B$ and columns $l,r$:

- row $T$ has payoffs $(2,4)$ and $(2,4)$;
- row $M$ has payoffs $(3,1)$ and $(0,0)$;
- row $B$ has payoffs $(0,0)$ and $(1,3)$.

the profile $(T,r)$ is proper in the full game. After deleting the strictly
dominated strategy $B$, however, it is no longer perfect and hence no longer
proper.

## References

- [MFoGT, Section 6.5, examples after Rem. 6.5.8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Examples separating proper and perfect equilibrium and showing dependence on dominated strategies.
