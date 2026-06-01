---
id: game_theory.stochastic_game.core.stochastic_game
title: Stochastic Game
kind: definition
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.core
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - stochastic-game
  - state-dynamics
---

# Stochastic Game

A **stochastic game** carries a state variable, and each state is associated
with its own stage game. At every stage the current state and action profile
jointly determine both

- the current payoff vector, and
- the probability distribution of the next state.

Thus an action affects both the *current payoff* and the *future strategic
opportunities* (through the state transition kernel).

Formally, a stochastic game is a tuple
$\Gamma = (S, (A_i)_{i \in N}, q, (r_i)_{i \in N}, s_0)$
where $S$ is the (finite or measurable) state space, $A_i$ is player
$i$'s action set, $q : S \times A \to \Delta(S)$ is the transition
kernel, $r_i : S \times A \to \mathbb{R}$ is the stage payoff for player
$i$, and $s_0 \in S$ is the initial state (or a distribution over it).

## Two historical branches

The mathematical theory splits cleanly by the number of players and the
zero-sum assumption:

- **Zero-sum two-player stochastic games** (Shapley 1953): the discounted
  value $v_\gamma$ is the unique fixed point of the Shapley operator
  $T$, a $\gamma$-contraction on bounded functions of the state. Pure
  matrix-game theory at each state, glued by dynamic programming. See
  [[game_theory.stochastic_game.value.discounted_value]] and
  [[game_theory.stochastic_game.value.shapley_operator]].

- **General-sum N-player stochastic games** (Fink 1964): Nash equilibrium
  in Markovian strategies exists under analogous assumptions. See
  [[game_theory.stochastic_game.equilibrium.fink_nash_existence]].

The undiscounted / asymptotic / uniform value theory
([[game_theory.stochastic_game.asymptotic.bewley_kohlberg_asymptotic_value]],
[[game_theory.stochastic_game.asymptotic.mertens_neyman_uniform_value]]) lives in
the zero-sum branch.

## Distinguishing from repeated games

Repeated games ([[game_theory.repeated_game.core.repeated_game]]) play the *same*
stage game in every period — no state evolution. Stochastic games are
the natural state-dependent generalisation. A repeated game is the
single-state special case of a stochastic game.

## References

- Shapley, L. S. (1953). "Stochastic Games". *PNAS* 39: 1095–1100.
- Fink, A. M. (1964). "Equilibrium in a Stochastic n-Person Game". *J. Sci. Hiroshima Univ.* 28: 89–93.
- [MFoGT Chapter 8, §8.6.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
