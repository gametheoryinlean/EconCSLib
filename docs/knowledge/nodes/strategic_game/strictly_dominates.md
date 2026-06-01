---
id: game_theory.strategic_game.strictly_dominates
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Strict Dominance
kind: definition
status: admitted
uses:
  - game_theory.strategic_game.unilateral_deviation
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.Dominance
  declarations:
    - StrictlyDominates
    - StrictlyDominates.weakly
    - IsStrictlyDominant.isWeaklyDominant
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this stated for arbitrary games?"
  verdict: "Yes. Strict inequality for all opponent profiles."
tags:
  - strategic-game
  - dominance
---

# Strict Dominance

A strategy $s_i$ strictly dominates another strategy $s'_i$ for player $i$ if, for
every profile $\sigma$ of the other players, playing $s_i$ yields strictly higher
payoff:

$$\forall \sigma, \quad u_i(\sigma[i \mapsto s'_i]) < u_i(\sigma[i \mapsto s_i]).$$

## References

- [MSZ, Chapter 2, Section 2.3] Maschler, Solan, and Zamir, *Game Theory*. Definition of strict dominance.
