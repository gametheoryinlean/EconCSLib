---
id: game_theory.strategic_game.bayesian.bayesian_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Bayesian Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_game
  - game_theory.strategic_game.core.mixed_strategy
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.Basic
  declarations:
    - StrategicGame.BayesianGame.PureStrategy
    - StrategicGame.BayesianGame.BehaviorStrategy
    - StrategicGame.BayesianGame.MixedBayesianStrategy
    - StrategicGame.BayesianGame.mixedBayesianStrategyToBehavior
    - StrategicGame.BayesianGame.behaviorStrategyToMixedBayesian
    - StrategicGame.BayesianGame.mixedBayesianStrategyToBehavior_behaviorStrategyToMixedBayesian
    - StrategicGame.BayesianGame.mixedPlanActionDistribution_eq_piProduct_behavior
    - StrategicGame.BayesianGame.mixedPlanExpectedPayoff_eq_behavioralExpectedPayoff
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - bayesian-game
  - strategy
---

# Bayesian Strategy

In a Bayesian game, a pure strategy of player $i$ is a type-contingent action
plan
$$
  s_i:T_i\to A_i.
$$
It specifies what player $i$ will do after each type that player might observe.

A behavioral Bayesian strategy assigns to each type a distribution over
actions:
$$
  \sigma_i:T_i\to\Delta(A_i).
$$
A mixed Bayesian strategy is instead a probability distribution over the set
of pure type-contingent plans $A_i^{T_i}$. In the finite model these two
representations induce the same typewise action marginals, but they are not the
same definition. A Bayesian strategy profile is a tuple of strategies of the
chosen representation, one for each player.

Formally, typewise marginalization maps a mixed contingent plan to a behavioral
strategy. Conversely, the product coupling across types maps any behavioral
strategy to a mixed contingent plan, and its marginals are proved to recover
the original behavioral strategy. At the profile level, the formalization also
proves equality of the induced action distribution at every type profile and
equality of ex-ante payoffs. Thus the finite correspondence is realization
equivalence, not merely a map between two strategy spaces.

MSZ Equations (9.58)--(9.60) give the same pure, mixed, behavioral, and
conditional product-action representations, with the extra generality that
the available action set may depend on the player's type. The present Lean API
specializes those equations to a fixed action type for each player.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Strategies in Bayesian games are type-contingent plans.
- [MSZ, Chapter 9, Eqs. 9.58--9.60] Maschler, Solan, and Zamir, *Game Theory*. Pure, mixed, and behavioral strategies and the conditional product action law.
