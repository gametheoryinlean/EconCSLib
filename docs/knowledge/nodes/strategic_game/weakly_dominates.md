---
id: game_theory.strategic_game.weakly_dominates
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Weak Dominance
kind: definition
status: admitted
uses:
  - game_theory.strategic_game.unilateral_deviation
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.Dominance
  declarations:
    - WeaklyDominates
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this stated for arbitrary games or restricted to finite games?"
  verdict: "For arbitrary games. No finiteness assumption."
tags:
  - strategic-game
  - dominance
---

# Weak Dominance

A strategy $s_i$ weakly dominates another strategy $s'_i$ for player $i$ if, for
every profile $\sigma$ of the other players, playing $s_i$ yields at least as high
a payoff as playing $s'_i$:

$$\forall \sigma, \quad u_i(\sigma[i \mapsto s'_i]) \le u_i(\sigma[i \mapsto s_i]).$$

## References

- [MSZ, Chapter 2, Section 2.3] Maschler, Solan, and Zamir, *Game Theory*. Definition of weak dominance.
