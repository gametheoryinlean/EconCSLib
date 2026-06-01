---
id: game_theory.strategic_game.zero_sum.learning.no_internal_regret_correlated_convergence
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: No Internal Regret Converges To Correlated Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.internal_regret
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - learning
  - regret
  - correlated-equilibrium
  - convergence
---

# No Internal Regret Converges To Correlated Equilibrium

In repeated play of a finite strategic game, suppose every player follows a
procedure with no internal regret. Then the empirical distribution of realized
action profiles approaches the set of correlated-equilibrium distributions.

## Proof Sketch

For each player $i$ and each replacement pair $a_i\mapsto b_i$, the corresponding
internal-regret inequality can be written as
$$
  \sum_{a_{-i}} q(a_i,a_{-i})
  (g_i(b_i,a_{-i})-g_i(a_i,a_{-i}))\le 0,
$$
where $q$ is the empirical distribution. These are exactly the obedience
inequalities for a correlated equilibrium. Since there are finitely many such
linear inequalities, vanishing positive internal regret for all players forces
the empirical distributions toward their common feasible set.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. If each player has no internal regret, empirical distributions converge to the correlated-equilibrium set.
