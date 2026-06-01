---
id: game_theory.extensive_game.imperfect_information.forward_induction
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Forward Induction
kind: definition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.sequential_equilibrium
  - game_theory.strategic_game.dominance.dominated_strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - forward-induction
  - refinement
---

# Forward Induction

Forward induction is a refinement principle for extensive form games. Unlike
backward induction, which evaluates future optimality at each information set,
forward induction also uses past play to restrict beliefs: when possible, a
deviation from the equilibrium path should be interpreted as a rational signal
rather than as a mere mistake.

In the battle-of-the-sexes game with outside option in MFoGT Figure 6.20, player
1 can stop and receive payoff $2$. If player 1 instead enters, player 2 should
infer, when possible, that player 1 expects more than $2$. Since one continuation
choice of player 1 is strictly dominated by stopping, the forward-induction
outcome selects the continuation equilibrium $(T,L)$ with payoff $(3,1)$.

## References

- [MFoGT, Section 6.7 and Figure 6.20] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Forward induction restricts off-path beliefs by interpreting deviations as rational when possible.
