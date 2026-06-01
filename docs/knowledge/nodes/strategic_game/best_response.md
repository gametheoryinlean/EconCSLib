---
id: game_theory.strategic_game.best_response
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.core
title: Best Response
kind: definition
status: admitted
uses:
  - game_theory.strategic_game.unilateral_deviation
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.BestResponse
  declarations:
    - IsBestResponse
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "Is this definition stated for arbitrary strategy spaces?"
  verdict: "Yes, quantifies over all alternative strategies for the player."
tags:
  - strategic-game
  - solution-concept
---

# Best Response

A strategy $\sigma_i$ is a best response for player $i$ to the profile $\sigma$ if
no unilateral deviation can improve $i$'s payoff:

$$\forall s'_i \in S_i, \quad u_i(\sigma[i \mapsto s'_i]) \le u_i(\sigma).$$

## References

- [MSZ, Chapter 2, Section 2.4] Maschler, Solan, and Zamir, *Game Theory*. Definition of best response.
