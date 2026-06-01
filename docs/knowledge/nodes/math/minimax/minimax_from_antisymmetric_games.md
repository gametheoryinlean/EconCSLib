---
id: math.minimax.minimax_from_antisymmetric_games
title: Minimax From Antisymmetric Games
kind: proof-plan
status: admitted
primary_topic: math
topics:
  - math
  - math.minimax
target: game_theory.strategic_game.zero_sum.von_neumann_minimax
plan_status: candidate
uses:
  - math.minimax.antisymmetric_matrix_game_value
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 10(2)"
      format: section
      note: "Deduce finite minimax from values of antisymmetric games"
verification:
  proof: accepted
tags:
  - zero-sum
  - minimax
  - antisymmetric
  - proof-plan
---

# Minimax From Antisymmetric Games

*Proof.* To prove minimax for an arbitrary matrix $A$, first shift $A$ so that all entries
are positive. Introduce an antisymmetric matrix built from $A$, for example
$$
  B=
  \begin{pmatrix}
    0 & A & -1\\
    -A^T & 0 & 1\\
    1 & -1 & 0
  \end{pmatrix}.
$$
An optimal strategy in the antisymmetric game $B$ yields optimal mixed strategies
for both players in the original game $A$.

## References

- [MFoGT, Section 2.8, Exercise 10(2)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Deduce finite minimax from values of antisymmetric games.
