---
id: game_theory.strategic_game.zero_sum.approachability.blackwell_b_set_approachability
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.applications
title: Blackwell B-Set Approachability
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.zero_sum.approachability.deterministic_blackwell_sequence
verification:
  statement: accepted
  proof: gap
tags:
  - approachability
  - repeated-game
  - vector-payoff
---

# Blackwell B-Set Approachability

Let $A=(a_{ij})$ be a finite matrix with vector payoffs in $\mathbb R^k$, and let
$C\subseteq\mathbb R^k$ be closed and convex. Suppose $C$ is a B-set for player 1:
for every $x\notin C$, there exists $s\in\Delta(I)$ such that for every
$z\in sA$,
$$
  \langle z-\Pi_C(x),\,x-\Pi_C(x)\rangle\le 0.
$$
Then player 1 has a strategy in the repeated vector-payoff game such that, for
every strategy of player 2, the Cesaro average payoff $\bar x_n$ approaches $C$
almost surely:
$$
  d(\bar x_n,C)\to 0.
$$
Moreover MFoGT's exercise asks to show the expected bound
$$
  \mathbb E[d(\bar x_n,C)]\le \frac{2\|A\|_\infty}{\sqrt n}.
$$

## References

- [MFoGT, Section 3.5, Exercise 4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Blackwell approachability theorem for B-sets.
