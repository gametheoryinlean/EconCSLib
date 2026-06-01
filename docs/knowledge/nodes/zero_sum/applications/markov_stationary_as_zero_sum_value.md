---
id: game_theory.strategic_game.zero_sum.applications.markov_stationary_as_zero_sum_value
title: Markov Stationary Distribution as Zero-Sum Game Value
kind: lemma
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.applications
uses:
  - game_theory.strategic_game.zero_sum.applications.stochastic_matrix_invariant_distribution
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - applications
  - markov
  - stationary-distribution
---

# Markov Stationary Distribution as Zero-Sum Game Value

**Lemma.** Let $A : I \times I \to \mathbb{R}$ be a row-stochastic
matrix (entries $\ge 0$, every row sums to 1), and consider the
*displacement game* with payoff matrix $B := A - \operatorname{Id}$.
Then:

1. The displacement game has value $\operatorname{val}(B) = 0$.
2. Every row-optimal mixed strategy $x^* \in X(B)$ for player 1 is a
   **stationary distribution** of $A$:
   $x^* A = x^*$.

This is the proof structure underlying
[[game_theory.strategic_game.zero_sum.applications.stochastic_matrix_invariant_distribution]] —
the classical von Neumann construction translating
"Markov stationary distribution exists" into "an optimal mixed
strategy in a particular zero-sum game".

## Why this is a useful framing

The standard textbook proof of Markov stationary-distribution existence
uses Brouwer's fixed-point theorem on $\Delta(I)$. The
zero-sum-game-theoretic proof bypasses Brouwer entirely:

- Apply the minimax theorem
  ([[game_theory.strategic_game.zero_sum.von_neumann_minimax]]) to the displacement game
  $B = A - \operatorname{Id}$ — this gives existence of optimal
  strategies for free.
- Reduce stationarity to the *saddle-point characterisation* of those
  optimal strategies (player 1's guarantee inequality, summed across
  columns, forces equality on every column).

The whole argument is purely algebraic / combinatorial once minimax is
in hand, which is itself proved by Loomis induction
([[math.minimax.loomis_induction_proof]]) — no topology required.
This is a satisfying application of zero-sum theory to elementary
Markov-chain theory.

## Bridge to the main theorem

The detailed argument lives in
[[game_theory.strategic_game.zero_sum.applications.stochastic_matrix_invariant_distribution]]
(MFoGT Cor. 2.5.2): the three-step proof there is

1. Show $\operatorname{val}(B) = 0$ (this lemma's statement 1) by
   exhibiting matching upper and lower bounds.
2. Take any $x^* \in X(B)$; saddle-point inequality gives
   $x^* A \ge x^*$ componentwise.
3. Sum across $j$ and use row-stochasticity: total mass forces
   $x^* A = x^*$ pointwise.

This node is the *conceptual restatement* of that argument — the
underlying meta-pattern is "minimax theorem + saddle-point
characterisation + a counting / mass-balance step ⇒ existence of a
matrix-algebraic object".

## References

- von Neumann's original 1928 paper already contains this technique.
- [MFoGT Cor. 2.5.2] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*.
- Owen, G. (1995). *Game Theory*. Ch. 3.
