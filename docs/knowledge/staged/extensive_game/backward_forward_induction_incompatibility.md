---
id: game_theory.extensive_game.examples.backward_forward_induction_incompatibility
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.examples
title: Backward And Forward Induction Can Conflict
kind: example
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.forward_induction
  - game_theory.extensive_game.perfect_information.subgame_perfect_equilibrium
verification:
  proof: not_applicable
tags:
  - extensive-game
  - forward-induction
  - example
---

# Backward And Forward Induction Can Conflict

MFoGT Figure 6.21 adds an initial stage before the battle-of-the-sexes game with
outside option. The continuation subgame has the forward-induction outcome
$(T,L)$ with payoff $(3,1)$.

Backward induction then says player 2 should stop at the first stage and obtain
payoff $2$. But if player 2 continues, forward-induction reasoning interprets the
continuation as evidence that player 2 expects more than $2$, which changes the
beliefs used in the later subgame.

This illustrates why forward-induction refinements are usually applied only when
the rationality interpretation is coherent.

## References

- [MFoGT, Section 6.7 and Figure 6.21] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Example where backward-induction and forward-induction reasoning are incompatible.
