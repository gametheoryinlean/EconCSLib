---
id: game_theory.stochastic_game.value.shapley_operator
title: Shapley Operator
kind: definition
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.value
uses:
  - game_theory.stochastic_game.core.stochastic_game
  - game_theory.strategic_game.zero_sum.core.value
verification:
  definition: accepted
  proof: not_applicable
tags:
  - stochastic-game
  - zero-sum
  - shapley-operator
---

# Shapley Operator

For a finite-state, finite-action two-player zero-sum stochastic game
$\Gamma = (S, A_1, A_2, q, r)$ with discount factor $\gamma \in (0, 1)$,
the **Shapley operator** acts on bounded functions
$f : S \to \mathbb{R}$ by playing a one-shot zero-sum matrix game at
each state, with payoff entries that combine the current stage payoff
with a discounted continuation value:
$$
(T_\gamma f)(s) = \operatorname{val}_{A_1 \times A_2}\,
   \Bigl[(1 - \gamma)\, r(s, a_1, a_2)
   \; + \;\gamma\, \sum_{s'} q(s' \mid s, a_1, a_2)\, f(s')\Bigr].
$$

In words: at state $s$, the Shapley operator solves a matrix game whose
$(a_1, a_2)$-entry is the convex combination of (i) the stage payoff
weighted by $1-\gamma$, and (ii) the expected continuation value
$f(s')$ weighted by $\gamma$.

In Lean (when formalised): \`Shapley.operator γ Γ f : S → ℝ\`.

## Why it matters

- **Discounted value** $v_\gamma$ is the unique fixed point
  $v_\gamma = T_\gamma(v_\gamma)$
  ([[game_theory.stochastic_game.value.discounted_value_fixed_point]]).
- $T_\gamma$ is a **$\gamma$-contraction** in the supremum norm
  ([[game_theory.stochastic_game.value.shapley_operator_contraction]]), so Banach
  fixed-point theorem gives existence, uniqueness, and the iteration
  scheme $f_{n+1} = T_\gamma(f_n) \to v_\gamma$ at geometric rate.
- The argmin / argmax at each state yields **stationary optimal
  strategies** for both players.

## Generalises the Bellman operator

For a single-player game (MDP) the inner $\operatorname{val}$ collapses
to a single $\sup_{a_1}$ (or $\inf_{a_2}$), and $T_\gamma$ becomes the
familiar Bellman operator from reinforcement learning. The Shapley
operator is the *minimax* Bellman operator.

## Abstract value-operator framework

The general value-operator framework
([[game_theory.strategic_game.zero_sum.operators.value_operator_general]]) abstracts the Shapley
operator into "any nonexpansive value-style operator on bounded
functions". Nonexpansiveness lemmas
([[game_theory.strategic_game.zero_sum.operators.value_operator_nonexpansive_general]]) and
monotone-limit results
([[game_theory.strategic_game.zero_sum.continuous.monotone_decreasing_values_limit]]) all apply
to $T_\gamma$ as a special case.

## References

- Shapley, L. S. (1953). "Stochastic Games". *PNAS* 39: 1095–1100.
- Filar, J. and Vrieze, K. (1997). *Competitive Markov Decision Processes.* Ch. 4.
- [MFoGT Chapter 8, §8.6.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
