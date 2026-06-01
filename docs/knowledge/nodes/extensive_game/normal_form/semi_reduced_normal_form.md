---
id: game_theory.extensive_game.normal_form.semi_reduced_normal_form
title: Semi-Reduced Normal Form
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.normal_form
uses:
  - game_theory.extensive_game.normal_form.normal_form_reduction
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm
  declarations:
    - GameTree.PlayerStrategy
    - GameTree.profileStrategy
    - GameTree.profileStrategy_deviate_variant
    - GameTree.profileStrategy_deviate_eq_of_variant
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - normal-form
---

# Semi-Reduced Normal Form

Two strategies $s_i,t_i$ of player $i$ are payoff-equivalent if for every
$s_{-i}$ and every player $j$,
$$
  g_j(s_i,s_{-i})=g_j(t_i,s_{-i}).
$$
The semi-reduced normal form identifies payoff-equivalent strategies. This removes
differences that occur only at positions excluded by the strategy itself.

## References

- [MFoGT, Section 6.2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Semi-reduced normal form identifies payoff-equivalent strategies.
