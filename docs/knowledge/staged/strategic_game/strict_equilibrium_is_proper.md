---
id: game_theory.strategic_game.refinements.strict_equilibrium_is_proper
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Strict Equilibrium Is Proper
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.equilibrium.strict_equilibrium
  - game_theory.strategic_game.refinements.proper_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - equilibrium-refinement
  - strict-equilibrium
---

# Strict Equilibrium Is Proper

Every strict equilibrium of a finite normal-form game is a proper equilibrium.

## Proof Sketch

If $s$ is strict, then for small perturbations of the opponents, each $s_i$
remains the unique best response of player $i$. Using proper equilibria of the
restricted game where each player is prevented from playing $s_i$, the profiles
$\sigma^\epsilon=(1-\epsilon)s+\epsilon\tau^\epsilon$ are $\epsilon$-proper and
converge to $s$.

## References

- [MFoGT, Rem. 6.5.8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every strict equilibrium is proper.
