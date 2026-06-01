---
id: game_theory.strategic_game.potential.potential_maximizer_nash
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Potential Maximizer Is Nash
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.potential.potential_game
  - game_theory.strategic_game.nash_equilibrium
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.PotentialGame
  declarations:
    - IsExactPotential.maximizer_is_nash
    - IsOrdinalPotential.isNash_iff_localMax
verification:
  statement: accepted
  proof: gap
  alignment: aligned
tags:
  - strategic-game
  - potential-game
  - nash-equilibrium
---

# Potential Maximizer Is Nash

In a finite exact potential game, every global maximizer of the potential is a
pure Nash equilibrium.

The proof is local: if a unilateral deviation from a potential maximizer were
profitable, exactness would make the same deviation increase the potential,
contradicting maximality.

## References

- [MFoGT, Chapter 5, Section 5.6, Exercise 1(1)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite potential games have pure equilibria by maximizing the potential.
