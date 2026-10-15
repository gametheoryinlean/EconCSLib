---
id: game_theory.strategic_game.bayesian.nonatomic_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Nonatomic Bayesian Equilibrium Distribution
kind: definition
status: staged
uses:
  - game_theory.strategic_game.bayesian.distributional_strategy
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.Continuous
  declarations:
    - StrategicGame.NonatomicBayesianGame
    - StrategicGame.NonatomicBayesianGame.actionDistribution
    - StrategicGame.NonatomicBayesianGame.bestResponseGraph
    - StrategicGame.NonatomicBayesianGame.IsDistributionalEquilibrium
    - StrategicGame.NonatomicBayesianGame.isDistributionalEquilibrium_iff_ae
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - bayesian-game
  - nonatomic-game
  - distributional-equilibrium
---

# Nonatomic Bayesian Equilibrium Distribution

Let $(T,\mu)$ be an atomless type space, let $S$ be an action space, and let
$F(t,s,\nu)$ be the payoff of type $t$ from action $s$ when the population
action distribution is $\nu$. A distributional equilibrium is a probability
measure $\lambda$ on $T\times S$ whose type marginal is $\mu$, whose action
marginal is $\nu$, and which satisfies
$$
  \lambda\{(t,s):s\in\operatorname*{argmax}_{a\in S}F(t,a,\nu)\}=1.
$$

This is the nonatomic continuation stated after the war-of-attrition example
in MFoGT Section 7.4.2. The Lean definition requires the agent law to be both
a probability measure and atomless, requires the joint distribution to be a
probability measure with the prescribed agent marginal, computes the
endogenous action marginal explicitly, and requires the best-response graph
to be measurable. The accompanying theorem proves equivalence between the
source's measure-one graph condition and the corresponding almost-everywhere
best-response inequalities.

## References

- [MFoGT, Section 7.4.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nonatomic-game continuation of the war-of-attrition discussion.
