---
id: game_theory.strategic_game.bayesian.agent_normal_form
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Agent Normal Form Of A Bayesian Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_game
  - game_theory.strategic_game.bayesian.bayesian_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - bayesian-game
  - normal-form
---

# Agent Normal Form Of A Bayesian Game

The agent normal form of a finite Bayesian game replaces each player-type pair
$(i,t_i)$ by a separate agent. The action set of agent $(i,t_i)$ is $A_i$.

For a positive-probability type, the payoff of agent $(i,t_i)$ is the
conditional expected payoff of the original player $i$, conditional on
observing type $t_i$, when the other type agents use their prescribed actions.
For a zero-probability type, one must choose a convention such as the
unnormalized interim payoff (which is identically zero); an ordinary
conditional expectation is not defined there.

This construction turns the interim incentive constraints of a Bayesian
equilibrium into ordinary Nash best-response constraints in a finite
strategic-form game.

## Formalization status

The Lean declaration `BayesianGame.strategicForm` is not this
agent-form game: its players are the original players and its pure strategies
are complete type-contingent plans. No Lean declaration in this development constructs
the separate-player-per-type game defined by MSZ. Moreover, `BayesianGame`
uses a type-independent action family, whereas MSZ allows
$A_i(t_i)$ to vary with the type.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite Bayesian strategies and own-type-conditioned optimality; this section does not explicitly state the agent-normal-form construction.
- [MSZ, Chapter 9, Def. 9.50 and Thm. 9.51] Maschler, Solan, and Zamir, *Game Theory*. Agent-form construction and its Nash-equilibrium characterization of Bayesian equilibrium.
