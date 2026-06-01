---
id: game_theory.strategic_game.zero_sum.zero_sum_payoff_negation
title: Payoff Negation in Zero-Sum Games
kind: lemma
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.zero_sum_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.Basic
  declarations:
    - StrategicGame.IsZeroSum.neg
    - StrategicGame.IsZeroSum.neg'
    - StrategicGame.IsZeroSum.expectedPayoff_neg
    - StrategicGame.IsZeroSum.expectedPayoff_neg'
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 4, Section 4.4"
      format: section
      note: "Immediate algebraic consequence of zero-sum payoffs"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Does payoff negation require an order on payoffs?"
  verdict: "No. It is algebraic and follows from the additive group structure."
tags:
  - zero-sum
  - payoff
---

# Payoff Negation in Zero-Sum Games

If $G$ is zero-sum, then at every profile $\sigma$ the payoff of either player
determines the other:

$$u_1(\sigma) = -u_0(\sigma), \qquad u_0(\sigma) = -u_1(\sigma).$$

This is the algebraic reduction that lets later value and optimality statements
track only the row player's payoff.

*Proof.* The zero-sum hypothesis says
$$
  u_0(\sigma)+u_1(\sigma)=0
$$
at every profile $\sigma$. Rearranging in the underlying additive group gives
$u_1(\sigma)=-u_0(\sigma)$, and applying the same rearrangement with the players
interchanged gives $u_0(\sigma)=-u_1(\sigma)$.

## References

- [MSZ, Chapter 4, Section 4.4] Maschler, Solan, and Zamir, *Game Theory*. Immediate algebraic consequence of zero-sum payoffs.
