---
id: game_theory.strategic_game.dominance.dominated_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Dominated Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.Dominance
  declarations:
    - WeaklyDominates
    - StrictlyDominates
verification:
  definition: accepted
  proof: not_applicable
  alignment: pending
tags:
  - strategic-game
  - dominance
---

# Dominated Strategy

A strategy $m_i\in\Delta(S_i)$ is strictly dominated if there exists
$\sigma_i\in\Delta(S_i)$ such that
$$
  g_i(\sigma_i,t_{-i})>g_i(m_i,t_{-i})
  \quad\text{for all } t_{-i}\in S_{-i}.
$$
It is weakly dominated if there exists $\sigma_i$ such that the same inequalities
are weak for all $t_{-i}$ and strict for at least one $t_{-i}$.

For pure strategies, this specializes by identifying $s_i\in S_i$ with the Dirac
mass at $s_i$.

## Lean scope

Lean's `StrictlyDominates` / `WeaklyDominates` formalize domination between
**pure** strategies ($s,s' : G.\text{strategy}\,i$). The mixed-strategy
domination above — domination by some $\sigma_i\in\Delta(S_i)$ — is the more
general MFoGT notion, of which the Lean relations are the pure-strategy special
case. Mixed-strategy domination is not yet formalized, so this node stays
`pending` until the general notion is ported.

## References

- [MFoGT, Section 1.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Strictly dominated and weakly dominated pure strategies.
- [MFoGT, Definitions 4.3.2 and 4.3.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Strict and weak domination for mixed strategies in finite games.
