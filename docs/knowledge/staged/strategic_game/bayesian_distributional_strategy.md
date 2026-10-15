---
id: game_theory.strategic_game.bayesian.distributional_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Distributional Strategy in a Bayesian Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_game
  - game_theory.strategic_game.bayesian.bayesian_strategy
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.Basic
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.Continuous
  declarations:
    - StrategicGame.BayesianGame.DistributionalStrategy
    - StrategicGame.BayesianGame.IsInducedByBehaviorStrategy
    - StrategicGame.BayesianGame.behaviorStrategyToDistributional
    - StrategicGame.BayesianGame.distributionalStrategyToBehavior
    - StrategicGame.BayesianGame.distributionalStrategyToBehavior_isInduced
    - StrategicGame.ContinuousBehaviorStrategy
    - StrategicGame.ContinuousBehaviorStrategy.RandomSeedStrategy
    - StrategicGame.ContinuousBehaviorStrategy.exists_randomSeedStrategy
    - StrategicGame.ContinuousDistributionalStrategy
    - StrategicGame.ContinuousDistributionalStrategy.ofBehavior_toBehavior
    - StrategicGame.ContinuousDistributionalStrategy.exists_behaviorStrategy
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - bayesian-game
  - distributional-strategy
  - conditional-probability
---

# Distributional Strategy in a Bayesian Game

A distributional strategy of player $i$ is a joint probability distribution
$\mu_i\in\Delta(T_i\times A_i)$ whose marginal on $T_i$ equals the type
marginal induced by the common prior:
$$
  \sum_{a_i\in A_i}\mu_i(t_i,a_i)=p_i(t_i).
$$

A behavioral strategy $\beta_i:T_i\to\Delta(A_i)$ induces the joint law
$$
  \mu_i(t_i,a_i)=p_i(t_i)\beta_i(a_i\mid t_i).
$$
Conversely, at a positive-probability type, dividing the joint mass by
$p_i(t_i)$ gives the conditional action distribution. In the finite model, a
null type has zero joint mass for every action, so choosing any behavioral
distribution there still gives the exact joint-law identity. The conditional
representative at a null type is non-unique, but the correspondence of joint
laws is exact for every type.

For measurable type spaces and standard Borel action spaces, a behavioral
strategy is a Markov kernel. Mathlib's kernel representation theorem supplies
a jointly measurable action map of type and an independent uniform
$[0,1]$ seed, and the Lean theorem proves equality of the induced kernels and
joint type-action laws. Conversely, a continuous distributional strategy is a
probability measure on the type-action product with the prescribed type
marginal. Standard-Borel disintegration produces a behavioral kernel whose
composition with the type prior recovers the original joint law exactly.

## References

- [MFoGT, Section 7.4.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Distributional strategies and their behavioral conditional probabilities.
- [Milgrom-Weber 1985] Paul R. Milgrom and Robert J. Weber, "Distributional Strategies for Games with Incomplete Information," *Mathematics of Operations Research* 10(4):619-632, <https://doi.org/10.1287/moor.10.4.619>.
