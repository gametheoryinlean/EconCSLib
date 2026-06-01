---
id: game_theory.repeated_game.core.repeated_game
title: Repeated Game
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.core
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - repeated-game
---

# Repeated Game

A **repeated game** is built from a fixed *stage game*
$G = (N, (A_i)_{i \in N}, (u_i)_{i \in N})$ played at every stage
$t = 0, 1, 2, \dots$. Players observe past play (the *history*) and
condition their stage-$t$ action on it. The aggregated payoff over
stages defines the game's value or equilibrium concept.

Unlike a stochastic game ([[game_theory.stochastic_game.core.stochastic_game]]),
**no state evolves** between stages — the same stage game $G$ is
played every time. The interesting dynamics live entirely in players'
strategic use of history.

## Three evaluation rules

Different aggregations of per-stage payoffs $u_i(a_t)$ give different
games:

- **T-stage average**:
  $\Pi_T^i = \tfrac{1}{T} \sum_{t < T} u_i(a_t)$.
- **$\gamma$-discounted**:
  $\Pi_\gamma^i = (1 - \gamma) \sum_{t \ge 0} \gamma^t u_i(a_t)$,
  with $\gamma \in (0, 1)$.
- **Undiscounted limit-of-means / uniform**:
  $\Pi_\infty^i = \liminf_T \tfrac{1}{T} \sum_{t < T} u_i(a_t)$ for
  Cesàro convergence, or its uniform-in-$T$ refinement.

See [[game_theory.repeated_game.core.payoff_aggregation]] for the formal
definitions and relations.

## Strategy spaces

A behavioural strategy for player $i$ is a function
$\sigma_i : \bigcup_t H_t \to \Delta(A_i)$ where $H_t = A^t$ is the
length-$t$ history of action profiles played so far
([[game_theory.repeated_game.core.history]]). Pure strategies map into $A_i$
directly. Restricting to histories that depend only on the latest
stage (or a fixed-length window) gives *automaton* or *Markovian*
strategies.

## Two central branches

- **Folk theorems** ([[game_theory.repeated_game.folk_theorem]]): every
  individually rational feasible payoff vector is achievable as a Nash
  (or subgame-perfect) equilibrium payoff under suitable discount /
  patience conditions.

- **Repeated games with incomplete information**
  ([[game_theory.repeated_game.incomplete_info]]): players have private information
  about a state drawn once at the start; the value of the long-run
  game characterises information revelation incentives. The
  Aumann-Maschler cav-u theorem
  ([[game_theory.repeated_game.incomplete_info.cav_u_theorem]]) is the zero-sum
  archetype.

## References

- Aumann, R. J. and Shapley, L. S. (1976/1994). "Long-Term Competition
  — A Game-Theoretic Analysis".
- Friedman, J. W. (1971). "A Non-Cooperative Equilibrium for Supergames".
- [MSZ Chapters 13–14] Maschler, Solan, Zamir, *Game Theory*.
- [MFoGT Chapter 8] Laraki, Renault, Sorin, *Mathematical Foundations of Game Theory*.
