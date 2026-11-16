---
id: game_theory.strategic_game.bayesian.bayesian_equilibrium_as_nash
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Bayesian Equilibrium As Nash Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_equilibrium
  - game_theory.strategic_game.bayesian.bayesian_strategy
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.Basic
  declarations:
    - StrategicGame.BayesianGame.strategicForm
    - StrategicGame.BayesianGame.IsMixedBayesianEquilibrium
    - StrategicGame.BayesianGame.isMixedBayesianEquilibrium_iff_behavioral
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - bayesian-game
  - bayesian-equilibrium
  - nash-equilibrium
---

# Bayesian Equilibrium As Nash Equilibrium

For a finite Bayesian game with a common prior, Bayesian equilibria correspond
to mixed Nash equilibria of its Harsanyi strategic form, in which each original
player's pure strategies are complete type-contingent action plans.

This strategic form must not be confused with MSZ's agent-form game. In the
Harsanyi strategic form each original player chooses an entire contingent
plan; in the agent form each player-type pair is a separate player choosing
only that type's action.

## Proof Sketch

A mixed strategy in the Harsanyi strategic form is a distribution over pure
type-contingent plans. Taking every typewise action marginal produces a
behavioral strategy. Conversely, independently coupling a player's behavioral
choices across counterfactual types realizes that behavioral strategy as a
mixed contingent plan. The formal payoff-equivalence theorem is stable under a
unilateral update, so the two Nash deviation inequalities are equivalent.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed and behavioral strategies and ex-ante Bayesian equilibrium; the explicit strategic-form equivalence is a proved finite consequence rather than a separately numbered theorem in this section.
- [MSZ, Chapter 9, Def. 9.46 and Thms. 9.51, 9.53] Maschler, Solan, and Zamir, *Game Theory*. Ex-ante Nash equilibrium, its full-support equivalence with interim Bayesian equilibrium, and the distinct agent-form result.
