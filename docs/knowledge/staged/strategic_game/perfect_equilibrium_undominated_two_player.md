---
id: game_theory.strategic_game.refinements.perfect_equilibrium_undominated_two_player
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Perfect Equilibrium And Undominated Equilibrium
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.refinements.perfect_equilibrium
  - game_theory.strategic_game.dominance.dominated_strategy
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - equilibrium-refinement
  - dominance
---

# Perfect Equilibrium And Undominated Equilibrium

In a finite two-player normal-form game, a Nash equilibrium is perfect if and only
if it is undominated, meaning that no strategy in its support is weakly dominated.

For games with more than two players, the corresponding inclusion is strict:
perfect equilibrium is a stronger requirement than undominated equilibrium.

## References

- [MFoGT, Prop. 6.5.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. In two-player finite normal-form games, perfect equilibrium iff undominated; strict inclusion for more players.
