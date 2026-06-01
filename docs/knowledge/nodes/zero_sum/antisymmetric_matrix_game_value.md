---
id: game_theory.strategic_game.zero_sum.antisymmetric_matrix_game_value
title: Antisymmetric Matrix Game Has Value Zero
kind: theorem
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.Antisymmetric
  declarations:
    - IsAntisymmetric
    - IsAntisymmetric.diag_zero
    - IsAntisymmetric.quadform_zero
    - MatrixGame.antisymmetric_value_zero
    - MatrixGame.antisymmetric_exists_optimal_strategy
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 10(1)"
      format: section
      note: "Antisymmetric matrix games have value zero"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - matrix-game
  - antisymmetric
  - value
---

# Antisymmetric Matrix Game Has Value Zero

A square matrix $B : I \times I \to \mathbb{R}$ is **antisymmetric** if
$B = -B^{\mathsf{T}}$, i.e. $B_{ij} = -B_{ji}$ for all $i,j$ (so in particular
$B_{ii} = 0$). The matrix game $B$ then has value $0$, and there exists
$x \in \Delta(I)$ such that $(Bx)_i \le 0$ for every row $i$.

*Proof.* By the minimax theorem
([[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]]) the game has a
value $v$. Antisymmetry gives $z^{\mathsf{T}} B z = 0$ for every mixed $z$, since
$z^{\mathsf{T}} B z = -z^{\mathsf{T}} B^{\mathsf{T}} z = -(z^{\mathsf{T}} B z)$.
Applying this to an optimal $x^\ast$ for player I,
$0 = \sum_j x^\ast_j (e_j B x^\ast)$ while each $e_j B x^\ast \ge v$, forcing
$v \le 0$; the symmetric argument gives $v \ge 0$, so $v = 0$.

## References

- [MFoGT, Section 2.8, Exercise 10(1)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Antisymmetric matrix games have value zero.
