---
id: game_theory.strategic_game.evolution.evolutionarily_stable_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Evolutionarily Stable Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.core.symmetric_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ESS
  declarations:
    - IsESS
    - IsNSS
    - IsESS.isNSS
    - IsESS.nash_condition
    - IsESS.strict_against_other
    - strict_nash_implies_ess
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - evolution
  - ess
---

# Evolutionarily Stable Strategy

For a symmetric two-player game with payoff matrix $A$, a mixed type
$p\in\Delta(K)$ is an evolutionarily stable strategy if every mutant
$q\ne p$ has a threshold $\epsilon(q)>0$ such that, for all
$0<\epsilon\le\epsilon(q)$,
$$
  pA((1-\epsilon)p+\epsilon q)
  >
  qA((1-\epsilon)p+\epsilon q).
$$

Equivalently, $p$ satisfies the symmetric Nash condition
$pAp\ge qAp$ for every $q$, and when equality holds it satisfies the second-order
stability condition $pAq>qAq$.

## References

- [MFoGT, Chapter 5, Def. 5.5.7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Evolutionarily stable strategy in a symmetric two-player game.
