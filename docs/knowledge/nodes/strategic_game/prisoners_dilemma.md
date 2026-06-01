---
id: game_theory.strategic_game.prisoners_dilemma
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.core
title: Prisoner's Dilemma
kind: example
status: admitted
uses:
  - game_theory.strategic_game.nash_equilibrium
  - game_theory.strategic_game.weakly_dominant_strategy
lean:
  modules:
    - EconCSLib.Examples.PrisonersDilemma
  declarations:
    - PrisonersDilemma.PD
    - PrisonersDilemma.pd_defect_weakly_dominant
    - PrisonersDilemma.pd_defect_nash
    - PrisonersDilemma.pd_nash_unique
    - PrisonersDilemma.pd_pareto_suboptimal
source:
  artifacts:
    - id: msz
  spans:
    - artifact: msz
      locator: "Chapter 4, Example 4.11"
      format: section
      note: "Prisoner's Dilemma in utility units"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - example
  - classic
---

# Prisoner's Dilemma

The Prisoner's Dilemma is a two-player strategic game where each player can
Cooperate ($C$) or Defect ($D$). The Lean example uses this normalized payoff
matrix:

|       | $C$    | $D$    |
|-------|--------|--------|
| $C$   | (3, 3) | (0, 5) |
| $D$   | (5, 0) | (1, 1) |

Defecting is a weakly dominant strategy for each player. The unique Nash
equilibrium is $(D, D)$ with payoff $(1, 1)$, which is Pareto-dominated by
$(C, C)$ with payoff $(3, 3)$.

## References

- [MSZ, Chapter 4] Maschler, Solan, and Zamir, *Game Theory*. Prisoner's Dilemma in utility units.
