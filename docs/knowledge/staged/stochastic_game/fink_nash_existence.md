---
id: game_theory.stochastic_game.equilibrium.fink_nash_existence
title: Fink Nash Existence in Stochastic Games
kind: theorem
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.core
uses:
  - game_theory.stochastic_game.core.history
  - game_theory.strategic_game.nash_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - stochastic-game
  - general-sum
  - nash-equilibrium
  - existence
---

# Fink Nash Existence in Stochastic Games

**Theorem (Fink 1964; Takahashi 1964 independently).** Every
finite-state, finite-action $N$-player discounted stochastic game
([[game_theory.stochastic_game.core.stochastic_game]]) has a **Nash equilibrium in
stationary Markovian strategies**.

This is the general-sum analogue of Shapley's zero-sum result
([[game_theory.stochastic_game.value.discounted_value_fixed_point]]).

## Statement

Fix discount factor $\gamma \in (0, 1)$ and consider the stationary
$\gamma$-discounted Nash-equilibrium condition: each player $i$ plays a
stationary (state-only) strategy $\sigma_i : S \to \Delta(A_i)$, and for
every $i$ and every alternative stationary $\sigma_i'$,
$$
\mathbb{E}_{\sigma_1, \dots, \sigma_N}[\Pi_{\gamma,i}]
\;\ge\; \mathbb{E}_{\sigma_1, \dots, \sigma_i', \dots, \sigma_N}[\Pi_{\gamma,i}],
$$
where $\Pi_{\gamma,i}$ is player $i$'s discounted payoff.

Such a Nash equilibrium exists.

## Proof plan

Apply Kakutani's fixed-point theorem to the best-response correspondence
on the compact convex set of stationary strategy profiles
$\prod_i \Delta(A_i)^S$:

1. **Compactness & convexity.** Each $\Delta(A_i)^S$ is a product of
   simplices — compact, convex, finite-dimensional.

2. **Best-response computation.** For each player $i$ and fixed
   opponents $\sigma_{-i}$, player $i$ faces a one-player MDP whose
   value function is the unique fixed point of a Bellman operator (a
   $\gamma$-contraction). The set of $\sigma_i$ that attain this value
   is convex, nonempty, and depends upper-semi-continuously on
   $\sigma_{-i}$.

3. **Closed-graph hypothesis of Kakutani.** The joint best-response
   correspondence has nonempty convex values and a closed graph (by
   the contraction-fixed-point continuity).

4. **Apply Kakutani** to obtain a fixed point — a stationary Nash
   equilibrium.

This is exactly the strategy of the original Fink / Takahashi proofs.

## Restrictions and extensions

- **Markov-perfect equilibrium** is the subgame-perfect refinement
  (Maskin-Tirole 1988+); it coincides with the stationary equilibria
  produced by the above proof in the discounted setting.
- **Undiscounted games** (limit-of-means evaluation) are much harder;
  Nash equilibrium existence is the long-standing **Vrieze-Tijs**
  conjecture and is known only in restricted classes (e.g. games with
  finitely many ergodic classes, irreducible games).

## References

- Fink, A. M. (1964). "Equilibrium in a Stochastic n-Person Game".
  *J. Sci. Hiroshima Univ.* 28: 89–93.
- Takahashi, M. (1964). "Equilibrium Points of Stochastic Noncooperative
  n-Person Games". *J. Sci. Hiroshima Univ.* 28: 95–99.
- Filar, J. and Vrieze, K. (1997). *Competitive Markov Decision Processes.* Ch. 5.
- [MFoGT Chapter 8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
