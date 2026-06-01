---
id: game_theory.strategic_game.zero_sum.examples.noisy_duel_one_bullet_value
title: Noisy One-Bullet Duel Value
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.examples
uses:
  - game_theory.strategic_game.zero_sum.core.value
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.5, Exercise 1(1)"
      format: section
      note: "Noisy duel with one bullet for each player"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - duel
  - continuous-game
---

# Noisy One-Bullet Duel Value

In the noisy duel where each player has one bullet and the kill probabilities
$p_1,p_2:[0,1]\to[0,1]$ are strictly increasing continuous functions with
$p_1(0)=p_2(0)=0$ and $p_1(1)=p_2(1)=1$, the game has a value in pure strategies.

The optimal pure strategy of each player is to shoot at the unique time $t_0$
satisfying
$$
  p_1(t_0)+p_2(t_0)=1.
$$

*Proof.* Continuity and monotonicity of $p_1+p_2$ give a unique
$t_0\in[0,1]$ with $p_1(t_0)+p_2(t_0)=1$. If player $1$ shoots before $t_0$,
then player $2$ can wait until $t_0$; the early shot has hit probability below
$p_1(t_0)$, while player $2$'s later shot has hit probability $p_2(t_0)$, so
player $1$ cannot improve past the payoff at $t_0$. If player $1$ waits past
$t_0$, player $2$ shoots at $t_0$ and again player $1$ cannot improve. The same
argument with the players interchanged shows that shooting at $t_0$ is optimal
for player $2$. Thus $(t_0,t_0)$ is a pure saddle point, so the game has a
pure-strategy value.

## References

- [MFoGT, Section 3.5, Exercise 1(1)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Noisy duel with one bullet for each player.
