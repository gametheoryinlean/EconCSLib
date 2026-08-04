---
id: game_theory.strategic_game.bayesian.finite_bayesian_equilibrium_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Finite Bayesian Equilibrium Exists
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_equilibrium_as_nash
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.BayesianGame.Basic
  declarations:
    - StrategicGame.BayesianGame.exists_isMixedBayesianEquilibrium
    - StrategicGame.BayesianGame.exists_isBayesianEquilibrium
    - StrategicGame.BayesianGame.exists_isInterimBayesianEquilibrium
    - StrategicGame.BayesianGame.exists_allConditionalInterimPureActionBestResponses_of_fullTypeSupport
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - bayesian-game
  - bayesian-equilibrium
  - existence
---

# Finite Bayesian Equilibrium Exists

Every finite Bayesian game with finite action sets, finite type sets, and a
common prior has an ex-ante behavioral equilibrium and an interim equilibrium
at every positive-probability type. Under full type support, there is a
behavioral profile satisfying every pure-action interim constraint in the
fixed-action-family specialization of the MSZ finite Bayesian-equilibrium
existence theorem cited below.

## Proof Sketch

Construct the finite Harsanyi strategic form whose pure strategies are
type-contingent plans. Nash's theorem gives a mixed equilibrium of that finite
game. Taking typewise action marginals gives a behavioral profile, and the
formal mixed-plan/behavioral equilibrium equivalence proves that it is a
Bayesian equilibrium. The theorem also handles the vacuous empty-player case.
The ex-ante/interim equivalence transfers this profile to the guarded interim
predicate; linearity in the acting type's mixed action reduces its constraints
to the pure-action inequalities used by MSZ. This does not formalize MSZ's
more general type-dependent action family $A_i(t_i)$.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite Bayesian-game framework; the section does not separately state the finite-existence theorem, which follows from finite Nash existence after a representation theorem.
- [MSZ, Chapter 9, Thms. 9.47 and 9.52] Maschler, Solan, and Zamir, *Game Theory*. Existence of behavioral ex-ante Nash and interim Bayesian equilibria in finite Harsanyi games.
