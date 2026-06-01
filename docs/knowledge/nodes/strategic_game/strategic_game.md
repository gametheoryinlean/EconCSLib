---
id: game_theory.strategic_game.strategic_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.core
title: Strategic Game
kind: definition
status: admitted
uses: []
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.Basic
  declarations:
    - StrategicGame
    - StrategicGame.welfare
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this definition stated for arbitrary player sets and strategy spaces?"
  verdict: "Yes, parameterized by player type N and strategy spaces per player."
tags:
  - strategic-game
  - foundational
---

# Strategic Game

A strategic game (or normal-form game) is a tuple
\((I, (S_i)_{i \in I}, (u_i)_{i \in I})\)
where \(I\) is a set of players, \(S_i\) is the strategy set of player \(i\), and
\(u_i \colon \prod_{j \in I} S_j \to U\) is the payoff function of player \(i\).

In the Lean formalization, this is a structure with fields `strategy : N → Type*` and
`payoff : Profile → N → U`, where `Profile = ∀ i, strategy i`.

## References

- [MSZ, Chapter 2] Maschler, Solan, and Zamir, *Game Theory*. Definition of strategic-form game.
