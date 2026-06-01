---
id: game_theory.extensive_game.normal_form.agent_normal_form
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.normal_form
title: Agent Normal Form
kind: definition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.perfect_recall
  - game_theory.extensive_game.normal_form.normal_form_reduction
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - normal-form
  - refinement
---

# Agent Normal Form

For a perfect-recall extensive form game $\Gamma$, the agent normal form
$\Gamma^a$ replaces each information set $Q$ of $\Gamma$ by a distinct agent
$i(Q)$.

The agent at $Q$ has the same payoff function as the original player who moves at
$Q$. Thus a single original player is duplicated into a team of agents, one for
each information set, all with common interests.

Since each agent moves at most once, mixed and behavioral strategies coincide in
the agent normal form.

## References

- [MFoGT, Def. 6.6.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Agent normal form of a perfect-recall extensive form game.
