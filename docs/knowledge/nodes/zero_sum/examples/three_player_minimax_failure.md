---
id: game_theory.strategic_game.zero_sum.examples.three_player_minimax_failure
title: Three-Player Minimax Failure
kind: example
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.examples
uses:
  - game_theory.strategic_game.zero_sum.maximin_le_minimax
lean:
  modules:
    - EconCSLib.Examples.StrategicGame.ThreePlayerMinimaxFailure
  declarations:
    - EconCSLib.StrategicGame.Examples.ThreePlayerMinimaxFailure.G
    - EconCSLib.StrategicGame.Examples.ThreePlayerMinimaxFailure.maximin_eq_one_quarter
    - EconCSLib.StrategicGame.Examples.ThreePlayerMinimaxFailure.minimax_eq_one_half
    - EconCSLib.StrategicGame.Examples.ThreePlayerMinimaxFailure.maximin_lt_minimax
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 2"
      format: section
      note: "Three-player example where the two-player minimax equality fails when two maximizers are restricted to independent mixed actions"
    - artifact: mfogt
      locator: "Section 9.2, Exercise 2 hints"
      format: section
      note: "Computes the two sides as 1/4 and 1/2"
verification:
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - minimax
  - counterexample
  - example
---

# Three-Player Minimax Failure

MFoGT Exercise 2.8.2 considers a three-player zero-sum interaction where players
1 and 2 are maximizers using independent mixed actions, and player 3 is the
minimizer. Player 1 chooses $T$ or $B$, player 2 chooses $L$ or $R$, and player
3 chooses $W$ or $E$. The payoff to the maximizing side is
$$
  g(T,L,W)=1,\qquad g(B,R,E)=1,
$$
and all other pure outcomes have payoff $0$.

Writing $x$ for the probability of $T$ and $y$ for the probability of $L$, the
two payoff components seen by player 3 are
$$
  xy,\qquad (1-x)(1-y).
$$
Thus
$$
  \max_{x,y\in[0,1]}\min\{xy,(1-x)(1-y)\}=\frac14,
$$
attained at $x=y=1/2$.

On the other hand, if player 3 mixes with probability $z$ on $W$, then the
maximizers can choose between the two matching corners, giving
$$
  \min_{z\in[0,1]}\max\{z,1-z\}=\frac12.
$$
Hence the natural minimax equality fails:
$$
  \max_{x,y}\min_z g(x,y,z)=\frac14
  <\frac12
  =\min_z\max_{x,y}g(x,y,z).
$$
The point of the example is that the joint strategy set of players 1 and 2 is
restricted to product distributions. If they could correlate their actions, the
left side would increase to $1/2$.

## References

- [MFoGT, Section 2.8, Exercise 2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Three-player example where the two-player minimax equality fails when two maximizers are restricted to independent mixed actions.
- [MFoGT, Section 9.2, Exercise 2 hints] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Computes the two sides as 1/4 and 1/2.
