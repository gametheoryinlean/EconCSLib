---
id: game_theory.strategic_game.strictly_dominant_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Strictly Dominant Strategy
kind: definition
status: admitted
uses:
  - game_theory.strategic_game.strictly_dominates
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.Dominance
  declarations:
    - IsStrictlyDominant
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this stated for arbitrary games?"
  verdict: "Yes. A strategy that strictly dominates every distinct alternative."
tags:
  - strategic-game
  - dominance
---

# Strictly Dominant Strategy

A strategy $s_i$ is strictly dominant for player $i$ if it strictly dominates
every other strategy available to $i$:

$$\forall s'_i \neq s_i, \quad s_i \text{ strictly dominates } s'_i.$$

A strictly dominant strategy is in particular weakly dominant
([[node:game_theory.strategic_game.weakly_dominant_strategy]]); the Lean
companion lemma `IsStrictlyDominant.isWeaklyDominant` records this and lives with
[[node:game_theory.strategic_game.strictly_dominates]].

## References

- [MFoGT, Section 1.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Strictly dominant and dominant strategies.
