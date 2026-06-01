---
id: game_theory.stochastic_game.core.history
title: Stochastic Game History
kind: definition
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.core
uses:
  - game_theory.stochastic_game.core.stochastic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - stochastic-game
  - history
---

# Stochastic Game History

For a stochastic game $\Gamma = (S, A, q, r, s_0)$
([[game_theory.stochastic_game.core.stochastic_game]]), a **history of length $t$**
is a sequence
$$
h_t = (s_0, a_0, s_1, a_1, \dots, s_{t-1}, a_{t-1}, s_t) \in (S \times A)^t \times S,
$$
recording the visited states and the chosen action profiles up to (and
including) the current state at stage $t$.

The set of length-$t$ histories is denoted $H_t$, and the **infinite
history space** is $H_\infty = (S \times A)^{\mathbb{N}} \times S$ with
the product $\sigma$-algebra.

## Two key sub-shapes

- A **terminal history** $h_t$ ends at the current observed state
  $s_t$; players' next actions are about to be chosen.
- A **public history** records actions that all players observe (the
  standard assumption); games of *incomplete information* impose
  observation filters that hide some of $h_t$ from specific players.

## Strategy spaces over histories

- A **pure strategy** for player $i$ is a function
  $\sigma_i : \bigcup_t H_t \to A_i$.
- A **behavioural / mixed strategy** is a function
  $\sigma_i : \bigcup_t H_t \to \Delta(A_i)$.
- A **Markovian strategy** factors through the current state alone:
  $\sigma_i(h_t) = \sigma_i(s_t)$ depends only on the last component
  of $h_t$.
- A **stationary strategy** is Markovian *and* independent of the stage
  $t$.

The Shapley operator analysis
([[game_theory.stochastic_game.value.shapley_operator]]) shows that in zero-sum
discounted stochastic games, **stationary** optimal strategies always
exist; this dramatically reduces the strategic complexity from
$|H_\infty|$ to $|S|$.

## References

- Shapley, L. S. (1953). "Stochastic Games". *PNAS*.
- Filar, J. and Vrieze, K. (1997). *Competitive Markov Decision Processes.* Springer.
- [MFoGT Chapter 8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
