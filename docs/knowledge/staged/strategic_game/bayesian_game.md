---
id: game_theory.strategic_game.bayesian.bayesian_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Bayesian Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.Basic
  declarations:
    - StrategicGame.PrimitiveBayesianGame
    - StrategicGame.PrimitiveBayesianGame.toReduced
    - StrategicGame.PrimitiveBayesianGame.toReduced_behavioralExpectedPayoff
    - StrategicGame.PrimitiveBayesianGame.toReduced_isBayesianEquilibrium
    - StrategicGame.BayesianGame
    - StrategicGame.BayesianGame.behavioralExpectedPayoff_eq_sum_typeMarginal_mul_conditionalInterim
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - bayesian-game
  - incomplete-information
---

# Bayesian Game

A finite reduced-form Bayesian game models incomplete information by giving
each player a type and allowing payoffs to depend on the full type profile.

The data consist of players $I$, finite action sets $(A_i)$, finite type sets
$(T_i)$, a common prior $p\in\Delta(T)$ on $T=\prod_i T_i$, and payoff functions
$$
  g_i:A\times T\to\mathbb R,
  \qquad A=\prod_i A_i.
$$
Player $i$ observes only their own type $t_i$ before choosing an action.

The common prior records the ex-ante probability of type profiles. Conditional
beliefs about other players' types are derived from the prior whenever the
observed type has positive probability.

MFoGT Section 7.4 first specifies a primitive state space, state-dependent
payoffs, and signal maps. `PrimitiveBayesianGame` formalizes that finite model;
`toReduced` pushes the state prior forward to type profiles and conditions
payoffs on the signal fibers. The formalized payoff-preservation theorem shows
that the primitive and reduced ex-ante formulations agree, and the
equilibrium-preservation theorem proves that the reduction does not change
Bayesian equilibria.

The Lean structure is an explicit finite specialization: the state, type,
action, and player spaces are finite. The general measure-space model used in
the source's continuous example is outside this declaration.

Relative to MSZ's Harsanyi model, this is the constant-action-family submodel:
the Lean action type is `Act i`, while that model permits an action set
$A_i(t_i)$ depending on player $i$'s type. The Lean structure also permits
zero-probability types; MSZ assumes every type marginal is positive.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Games with incomplete information, also called Bayesian games.
- [MSZ, Chapter 9, Def. 9.39 and Section 9.4] Maschler, Solan, and Zamir, *Game Theory*. Finite common-prior Harsanyi games, including type-dependent action sets and the full-type-support assumption.
