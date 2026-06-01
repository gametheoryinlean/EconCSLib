---
id: game_theory.strategic_game.zero_sum.examples.diagonal_matrix_game_value
title: Diagonal Matrix Game Value
kind: proposition
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.examples
uses:
  - game_theory.strategic_game.zero_sum.core.value
lean:
  modules:
    - EconCSLib.Examples.StrategicGame.DiagonalGame
  declarations:
    - EconCSLib.StrategicGame.Examples.diagonalGame_value
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 6"
      format: section
      note: "Compute value and optimal strategies for a positive diagonal matrix game"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - matrix-game
  - example
---

# Diagonal Matrix Game Value

Let $A$ be the diagonal $n\times n$ matrix with diagonal entries
$a_i>0$. Then
$$
  \operatorname{val}(A)=
  \left(\sum_{i=1}^n a_i^{-1}\right)^{-1}.
$$
Both players have the same optimal mixed strategy $p\in\Delta(\{1,\ldots,n\})$
given by
$$
  p_i=
  \frac{a_i^{-1}}{\sum_{k=1}^n a_k^{-1}}.
$$

*Proof.* Let
$$
  c=\left(\sum_{k=1}^n a_k^{-1}\right)^{-1}
  \quad\text{and}\quad
  p_i=ca_i^{-1}.
$$
Then $p$ is a probability vector. Against any pure column $j$, the row player's
payoff from $p$ is $p_ja_j=c$, so $p$ guarantees $c$. Against any pure row $i$,
the column player's mixed strategy $p$ gives payoff $a_ip_i=c$, so $p$ holds the
row player to $c$. By weak duality, the value is $c$ and $p$ is optimal for both
players.

## References

- [MFoGT, Section 2.8, Exercise 6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Compute value and optimal strategies for a positive diagonal matrix game.
