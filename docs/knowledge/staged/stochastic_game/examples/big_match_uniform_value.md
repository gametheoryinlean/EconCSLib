---
id: game_theory.stochastic_game.examples.big_match_uniform_value
title: Big Match Uniform Value
kind: theorem
status: staged
primary_topic: game_theory.stochastic_game
topics:
  - game_theory.stochastic_game
  - game_theory.stochastic_game.core
uses:
  - game_theory.stochastic_game.asymptotic.mertens_neyman_uniform_value
verification:
  statement: accepted
  proof: gap
tags:
  - stochastic-game
  - zero-sum
  - big-match
  - uniform-value
  - example
---

# Big Match Uniform Value

The **Big Match** (Gillette 1957; rigorous uniform-value analysis by
Blackwell-Ferguson 1968) is a two-player zero-sum stochastic game with one
nonabsorbing state and two absorbing outcomes. It is the canonical hard
case showing that the *uniform value* can exist even when stationary
optimal strategies for the maximizer do not.

The game has uniform value
$$
  \tfrac{1}{2}.
$$

## Structure

- One nonabsorbing state $s^*$ and two absorbing states $s^+$ (payoff 1
  forever) and $s^-$ (payoff 0 forever).
- The minimizer chooses a column $j \in \{1, 2\}$ each stage; the
  maximizer chooses a row $i \in \{1, 2\}$.
- If $i = 1$ the game *absorbs*: enter $s^+$ if $j = 1$, $s^-$ if $j = 2$.
- If $i = 2$ the game stays at $s^*$ and the stage payoff is $1$ if
  $j = 1$, $0$ if $j = 2$.

## Why it is hard

- The minimizer can guarantee $\tfrac12$ by mixing uniformly at every
  stage (regardless of the maximizer's play). This direction is
  immediate.

- The maximizer's guarantee of $\tfrac12$ is subtle: no Markovian
  (state-only-dependent) strategy achieves it. The Blackwell-Ferguson
  ε-optimal strategy uses the *entire history* of the minimizer's plays
  via a delicate count-and-threshold rule, and it works only in the
  uniform / undiscounted limit, not for any fixed discount factor.

## Where it sits in the literature

- It is the canonical example that *discounted optimal strategies need
  not converge to uniform optimal strategies* in stochastic games.
- It motivates the Mertens-Neyman 1981 uniform value theorem
  ([[game_theory.stochastic_game.asymptotic.mertens_neyman_uniform_value]]), which
  establishes uniform-value existence in much greater generality.

## References

- Gillette, D. (1957). "Stochastic Games with Zero Stop Probabilities".
  *Contributions to the Theory of Games* III.
- Blackwell, D. and Ferguson, T. S. (1968). "The Big Match".
  *Annals of Math. Stat.* 39: 159–163.
- [MFoGT Chapter 8, Thm. 8.6.1] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*.
