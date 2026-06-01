---
id: game_theory.strategic_game.weakly_dominant_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Weakly Dominant Strategy
kind: definition
status: admitted
uses:
  - game_theory.strategic_game.weakly_dominates
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.Dominance
  declarations:
    - IsWeaklyDominant
    - IsWeaklyDominant.isBestResponse
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this stated for arbitrary games?"
  verdict: "Yes. A strategy that weakly dominates all alternatives."
tags:
  - strategic-game
  - dominance
---

# Weakly Dominant Strategy

A strategy $s_i$ is weakly dominant for player $i$ if it weakly dominates every
other strategy available to $i$:

$$\forall s'_i \in S_i, \quad s_i \text{ weakly dominates } s'_i.$$

## References

- [MSZ, Chapter 2, Section 2.3] Maschler, Solan, and Zamir, *Game Theory*. Definition of weakly dominant strategy.
