---
id: game_theory.strategic_game.zero_sum.zero_sum_nash_value_unique
title: Nash Payoff Uniqueness in Zero-Sum Games
kind: theorem
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.minimax
uses:
  - game_theory.strategic_game.nash_equilibrium
  - game_theory.strategic_game.zero_sum.zero_sum_payoff_negation
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.Basic
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - StrategicGame.IsZeroSum.nash_payoff_eq
    - StrategicGame.IsZeroSum.nash_payoff_eq_p1
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 4, Theorems 4.44-4.45"
      format: section
      note: "All Nash equilibria of a zero-sum game have the same payoff value"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Which payoff assumptions are used by the Lean theorem?"
  verdict: "The theorem is stated over a field with a linear order compatible with multiplication."
tags:
  - zero-sum
  - equilibrium
  - value
---

# Nash Payoff Uniqueness in Zero-Sum Games

In a zero-sum game, any two Nash equilibria give the same payoff to player 0
and the same payoff to player 1.  Thus the equilibrium payoff is a value of the
game, independent of which Nash equilibrium is chosen.

The proof compares two equilibria through cross profiles.  One player's best
response inequality is converted into the other player's inequality using
zero-sum payoff negation.

*Proof.* Let $\sigma=(\sigma_0,\sigma_1)$ and
$\tau=(\tau_0,\tau_1)$ be two Nash equilibria, and write $u$ for player $0$'s
payoff. Since $\sigma_0$ is a best response to $\sigma_1$ and $\tau_0$ is an
available deviation,
$$
  u(\sigma_0,\sigma_1)\ge u(\tau_0,\sigma_1).
$$
Since $\tau_1$ is a best response to $\tau_0$ for player $1$, payoff negation
turns player $1$'s best-response inequality into
$$
  u(\tau_0,\sigma_1)\ge u(\tau_0,\tau_1).
$$
Thus $u(\sigma)\ge u(\tau)$. Reversing the roles of $\sigma$ and $\tau$ gives
$u(\tau)\ge u(\sigma)$, so player $0$'s equilibrium payoff is unique. Player
$1$'s payoff is its negative, hence is unique as well.

## References

- [MSZ, Chapter 4, Theorems 4.44-4.45] Maschler, Solan, and Zamir, *Game Theory*. All Nash equilibria of a zero-sum game have the same payoff value.
