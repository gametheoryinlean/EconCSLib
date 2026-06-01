---
id: game_theory.strategic_game.strategy_profile
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.core
title: Strategy Profile
kind: definition
status: admitted
uses:
  - game_theory.strategic_game.strategic_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.Basic
  declarations:
    - StrategicGame.Profile
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this definition stated for arbitrary player sets?"
  verdict: "Yes, a dependent product over arbitrary player index type."
tags:
  - strategic-game
  - foundational
---

# Strategy Profile

Given a strategic game \((I, (S_i), (u_i))\), a strategy profile is a tuple
\(\sigma = (\sigma_i)_{i \in I}\) where \(\sigma_i \in S_i\) for each player \(i\).

In Lean, a profile is `∀ i, G.strategy i`.

## References

- [MSZ, Chapter 2] Maschler, Solan, and Zamir, *Game Theory*. Definition of strategy profile.
