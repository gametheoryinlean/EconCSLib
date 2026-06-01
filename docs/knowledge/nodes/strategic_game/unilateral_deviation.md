---
id: game_theory.strategic_game.unilateral_deviation
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.core
title: Unilateral Deviation
kind: definition
status: admitted
uses:
  - game_theory.strategic_game.strategy_profile
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.Basic
  declarations:
    - StrategicGame.deviate
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this defined for arbitrary player sets and strategy spaces?"
  verdict: "Yes, uses Function.update which works for any dependent function."
tags:
  - strategic-game
  - foundational
---

# Unilateral Deviation

Given a strategy profile \(\sigma\) and a player \(i\), the unilateral deviation
\((\sigma_{-i}, s'_i)\) is the profile where player \(i\) plays \(s'_i\) and all other
players play according to \(\sigma\). We write \(\sigma[i \mapsto s']\).

In Lean, this is `Function.update σ i s'`.

## References

- [MSZ, Chapter 2] Maschler, Solan, and Zamir, *Game Theory*. Notation for unilateral deviation.
