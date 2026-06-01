---
id: game_theory.strategic_game.nash_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.equilibrium
title: Nash Equilibrium
kind: definition
status: admitted
uses:
  - game_theory.strategic_game.best_response
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NashEquilibrium
    - EconCSLib.GameTheory.StrategicGame.Checker
  declarations:
    - IsNashEquilibrium
    - isNashEq
    - isNashEq_iff
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this the standard definition for arbitrary strategic games?"
  verdict: "Yes. Every player best responds simultaneously."
tags:
  - strategic-game
  - solution-concept
  - equilibrium
---

# Nash Equilibrium

A strategy profile $\sigma$ is a Nash equilibrium if every player is playing a best
response to the strategies of the other players:

$$\forall i \in I, \quad \sigma_i \text{ is a best response to } \sigma.$$

Equivalently, no player can improve their payoff by a unilateral deviation.

## References

- [MSZ, Chapter 2, Section 2.4] Maschler, Solan, and Zamir, *Game Theory*. Definition of Nash equilibrium in pure strategies.
