---
id: game_theory.strategic_game.bayesian.bayesian_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Bayesian Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_strategy
  - game_theory.strategic_game.nash_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - bayesian-game
  - bayesian-equilibrium
---

# Bayesian Equilibrium

A Bayesian strategy profile $\sigma$ is a Bayesian equilibrium if no player can
improve expected payoff by replacing their type-contingent strategy while the
other players keep theirs fixed.

In ex-ante form, for every player $i$ and every alternative type-contingent
strategy $\tau_i:T_i\to\Delta(A_i)$,
$$
  \mathbb E_p[g_i(\sigma_i(t_i),\sigma_{-i}(t_{-i}),t)]
  \ge
  \mathbb E_p[g_i(\tau_i(t_i),\sigma_{-i}(t_{-i}),t)].
$$

When every type has positive prior probability, this is equivalent to the
interim condition that after each observed type $t_i$, the prescribed mixed
action is optimal against the conditional distribution of other players' types
and actions.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Bayesian equilibrium as the Nash-style equilibrium concept for Bayesian games.
