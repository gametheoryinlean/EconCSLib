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
  - game_theory.strategic_game.bayesian.agent_normal_form
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - bayesian-game
  - bayesian-equilibrium
  - nash-equilibrium
---

# Bayesian Equilibrium As Nash Equilibrium

For a finite Bayesian game with a common prior, Bayesian equilibria correspond
to Nash equilibria of the associated agent normal form.

## Proof Sketch

A Bayesian strategy profile assigns an action distribution to every player-type
pair, which is exactly a mixed profile in the agent normal form. A unilateral
deviation by one type-agent changes the original player's prescription only at
that type. Thus the agent's Nash best-response inequality is the interim
Bayesian incentive constraint for that type. Conversely, typewise interim
optimality for every player-type pair gives Nash optimality for every agent.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Bayesian equilibrium corresponds to Nash equilibrium in the associated strategic-form representation.
