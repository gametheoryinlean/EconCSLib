---
id: game_theory.extensive_game.imperfect_information.weak_bayesian_perfect_equilibrium
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Weak Bayesian Perfect Equilibrium
kind: definition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.belief_system
  - game_theory.extensive_game.imperfect_information.reached_information_set
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - belief
  - refinement
---

# Weak Bayesian Perfect Equilibrium

A pair $(\beta,\mu)$ of a behavioral strategy profile and a belief system is weak
Bayesian perfect if:

1. at every information set $Q_i$, $\beta_i(Q_i)$ is a best response in the
   continuation game starting at $Q_i$ under belief $\mu(Q_i)$ and continuation
   play $\beta$;
2. on every reached information set $Q\in Rch(\beta)$, beliefs are Bayes-compatible:
   $$
     \mu(Q)=\nu_\beta(Q).
   $$

## References

- [MFoGT, Def. 6.4.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Weak Bayesian perfect equilibrium as sequential rationality plus Bayes compatibility on path.
