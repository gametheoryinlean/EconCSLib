---
id: game_theory.strategic_game.correlated.degenerate_correlated_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Degenerate Correlated Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.correlated.correlated_equilibrium
  - game_theory.strategic_game.nash_equilibrium
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.CorrelatedEq
  declarations:
    - StrategicGame.vertex_mem_correlatedEquilibriumDistributions_iff_isNashEquilibrium
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - correlated-equilibrium
  - nash-equilibrium
---

# Degenerate Correlated Equilibrium

A degenerate correlated equilibrium is a correlated device that puts probability
one on a single pure strategy profile.

For such a point-mass device, obedience is exactly the Nash condition for that
pure profile: no player can improve by deviating from the recommended action,
because the recommendation fully determines the profile.

## Proof Sketch

If the point-mass profile is Nash, every recommended action is already a best
response to the other components, so obedience holds. Conversely, obedience of
the point-mass device tests exactly the unilateral deviations from that profile,
which is the Nash condition.

The Lean theorem is distribution-level: it states that the standard-simplex
vertex at a pure profile belongs to the correlated-equilibrium distribution
set if and only if that profile is a pure Nash equilibrium.

## References

- [MSZ, Chapter 8, Def. 8.6 and Thm. 8.7] Maschler, Solan, and Zamir, *Game Theory*. Point-mass correlated equilibria correspond to pure Nash equilibria.
