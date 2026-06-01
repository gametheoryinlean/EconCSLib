---
id: game_theory.stochastic_game.value.discounted_value
title: Discounted Value of a Zero-Sum Stochastic Game
kind: definition
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.value
uses:
  - game_theory.stochastic_game.core.history
  - game_theory.strategic_game.zero_sum.core.value
verification:
  definition: accepted
  proof: not_applicable
tags:
  - stochastic-game
  - zero-sum
  - discounted-value
---

# Discounted Value of a Zero-Sum Stochastic Game

For a two-player zero-sum stochastic game
([[game_theory.stochastic_game.core.stochastic_game]]) with discount factor
$\gamma \in (0, 1)$, the **$\gamma$-discounted payoff** of a play
$(s_0, a_0, s_1, a_1, \dots)$ is
$$
\Pi_\gamma = (1 - \gamma) \sum_{t = 0}^{\infty} \gamma^t \, r(s_t, a_t).
$$

The factor $(1 - \gamma)$ normalises so that constant per-stage payoffs
average to themselves, putting $\Pi_\gamma$ on the same scale as the
stage payoff $r$.

## $\gamma$-discounted value

The **$\gamma$-discounted value** $v_\gamma(s)$ at initial state $s$ is
the value of the (zero-sum) game with payoff
$\mathbb{E}_\sigma [\Pi_\gamma | s_0 = s]$:
$$
v_\gamma(s) = \sup_{\sigma_1} \inf_{\sigma_2}\,
  \mathbb{E}_{\sigma_1, \sigma_2}[\Pi_\gamma \mid s_0 = s]
  = \inf_{\sigma_2} \sup_{\sigma_1}\,
  \mathbb{E}_{\sigma_1, \sigma_2}[\Pi_\gamma \mid s_0 = s].
$$

The minimax equality on the RHS is part of Shapley's theorem and is
*not* a definition; it is a consequence of $v_\gamma$ being the unique
fixed point of the Shapley operator
([[game_theory.stochastic_game.value.shapley_operator]],
[[game_theory.stochastic_game.value.discounted_value_fixed_point]]).

## Stationary optimal strategies exist

Shapley 1953 proves that for finite-state, finite-action zero-sum
stochastic games, optimal strategies of both players can be chosen
**stationary** — depending only on the current state, not on the entire
history. This drops the strategy space from doubly-exponential in the
horizon to a Cartesian product of $|S|$ matrix-game mixed strategies.

## Range and continuity

- $v_\gamma : S \to \mathbb{R}$ is bounded by $\|r\|_\infty$.
- $\gamma \mapsto v_\gamma$ is rational in $\gamma$ (semialgebraic), a
  fact that fuels Bewley-Kohlberg's asymptotic value theorem
  ([[game_theory.stochastic_game.asymptotic.bewley_kohlberg_asymptotic_value]]).

## Special cases

- **Repeated game** (1 state, no transitions): $v_\gamma$ equals the
  matrix-game value of the stage game, independent of $\gamma$.
- **MDP** (1 player): $v_\gamma$ is the standard discounted MDP value,
  and the Shapley operator reduces to the Bellman operator.

## References

- Shapley, L. S. (1953). "Stochastic Games". *PNAS* 39: 1095–1100.
- [MFoGT Chapter 8, §8.6.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
