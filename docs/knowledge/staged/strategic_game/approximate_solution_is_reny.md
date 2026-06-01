---
id: game_theory.strategic_game.refinements.approximate_solution_is_reny
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Approximate Solutions Are Reny Solutions
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.refinements.approximate_solution
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - approximate-equilibrium
  - discontinuous-game
---

# Approximate Solutions Are Reny Solutions

Every approximate solution is a Reny solution.

## Proof Sketch

Let $(s^n)$ be $\epsilon_n$-equilibria with $\epsilon_n\to 0$ and
$(s^n,g(s^n))\to(s,v)$. For every player $i$ and deviation $t_i$,
$$
  g_i(t_i,s^n_{-i})\le g_i(s^n)+\epsilon_n.
$$
Taking lower limits along $n$ gives the Reny inequality
$\underline g_i(t_i,s_{-i})\le v_i$.

## References

- [MFoGT, Prop. 4.8.10] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every approximate solution is a Reny solution.
