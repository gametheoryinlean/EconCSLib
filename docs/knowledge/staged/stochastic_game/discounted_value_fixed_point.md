---
id: game_theory.stochastic_game.value.discounted_value_fixed_point
title: Discounted Value Is the Unique Shapley Fixed Point
kind: theorem
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.value
uses:
  - game_theory.stochastic_game.value.discounted_value
  - game_theory.stochastic_game.value.shapley_operator_contraction
verification:
  statement: accepted
  proof: accepted
tags:
  - stochastic-game
  - zero-sum
  - shapley-operator
  - fixed-point
---

# Discounted Value Is the Unique Shapley Fixed Point

**Theorem (Shapley 1953).** For a finite-state, finite-action zero-sum
stochastic game with discount factor $\gamma \in (0, 1)$, the
discounted value function $v_\gamma : S \to \mathbb{R}$
([[game_theory.stochastic_game.value.discounted_value]]) is the **unique fixed
point** of the Shapley operator $T_\gamma$
([[game_theory.stochastic_game.value.shapley_operator]]):
$$
v_\gamma = T_\gamma(v_\gamma).
$$

Both players have stationary $\varepsilon$-optimal strategies, given at
each state $s$ by an $\varepsilon$-optimal pair of the one-shot matrix
game whose payoff entries are the operator's argument inside
$\operatorname{val}$.

## Proof

The Banach fixed-point theorem applied to $T_\gamma$ as a
$\gamma$-contraction
([[game_theory.stochastic_game.value.shapley_operator_contraction]]) on
$L^\infty(S) = \mathbb{R}^S$ (with $S$ finite) gives unique existence of
a fixed point $w^* = T_\gamma(w^*)$.

To identify $w^* = v_\gamma$:

1. **Upper bound** $w^*(s) \ge v_\gamma(s)$. Define a stationary
   strategy for player 1 by playing, at each state $s'$, a maximin
   strategy of the matrix game inside the $\operatorname{val}$ that
   defines $T_\gamma w^*(s') = w^*(s')$. Standard backward-induction
   estimates (using $w^*$ as the certifying continuation) give
   $\mathbb{E}_{\sigma_1, \sigma_2}[\Pi_\gamma | s_0 = s] \ge w^*(s)$
   for every player-2 strategy $\sigma_2$. Hence
   $\sup \inf \ge w^*(s)$, i.e. $v_\gamma(s) \ge w^*(s)$.

2. **Lower bound** $w^*(s) \le v_\gamma(s)$ is the symmetric argument
   from player 2's side using the inner $\operatorname{val}$'s minimax
   strategy.

Together $v_\gamma = w^*$, the unique fixed point. $\square$

## Computational consequence

The iteration $f_{n+1} = T_\gamma(f_n)$ converges to $v_\gamma$
geometrically at rate $\gamma$. This is **Shapley iteration** (a.k.a.
value iteration for zero-sum stochastic games), the analogue of MDP
value iteration.

## Refinement: stationary optimal strategies

The argument above gives stationary $\varepsilon$-optimal strategies.
For *exactly optimal* stationary strategies, use the matrix-game inner
$\operatorname{val}$ at each state and pick optimal strategies (not
just $\varepsilon$-optimal). Existence then drops to the optimal
strategy sets of finite matrix games, which are nonempty polytopes
([[math.minimax.optimal_strategy_sets_are_polytopes]]).

## References

- Shapley, L. S. (1953). "Stochastic Games". *PNAS* 39: 1095–1100. The original theorem.
- Filar, J. and Vrieze, K. (1997). *Competitive Markov Decision Processes.* Ch. 4. Modern presentation.
- [MFoGT Chapter 8, Thm. 8.6.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
