---
id: math.minimax.minimax_from_deterministic_approachability
title: Minimax From Deterministic Approachability
kind: proof-plan
status: admitted
primary_topic: math
topics:
  - math
  - math.minimax
target: game_theory.strategic_game.zero_sum.von_neumann_minimax
plan_status: candidate
uses:
  - game_theory.strategic_game.zero_sum.approachability.deterministic_blackwell_sequence
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 4(2)"
      format: section
      note: "Derives finite minimax theorem from deterministic approachability"
verification:
  proof: accepted
tags:
  - zero-sum
  - minimax
  - approachability
  - proof-plan
---

# Minimax From Deterministic Approachability

*Proof.* Let $A$ be a finite matrix game and assume its minmax is $0$:
$$
  \bar v=\min_{t\in\Delta(J)}\max_{i\in I} e_iAt=0.
$$
Construct a sequence of rows $x_n$ of $A$ so that its Cesaro averages form a
Blackwell sequence for the cone
$$
  C=\{x\in\mathbb R^J:x\ge 0\}.
$$
The deterministic Blackwell sequence theorem then gives a limit mixed strategy
$s\in\Delta(I)$ with
$$
  sAt\ge 0\quad\text{for all }t\in\Delta(J),
$$
so player 1 can guarantee $0$.

## References

- [MFoGT, Section 2.8, Exercise 4(2)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Derives finite minimax theorem from deterministic approachability.
