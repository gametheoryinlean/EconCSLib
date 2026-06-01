---
id: game_theory.cooperative_game.shapley_axioms
title: Shapley Axioms
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.shapley_value
uses:
  - game_theory.cooperative_game.tu_game
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.ShapleyValue
  declarations:
    - CoalitionalGame.AreSymmetric
    - CoalitionalGame.IsNullPlayer
    - CoalitionalGame.SatisfiesEfficiency
    - CoalitionalGame.SatisfiesSymmetry
    - CoalitionalGame.SatisfiesNullPlayer
    - CoalitionalGame.SatisfiesAdditivity
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - shapley-value
  - axioms
---

# Shapley Axioms

The Shapley-value characterization uses four axioms for a single-valued
solution concept $\varphi$ assigning each game a payoff vector:

- **Efficiency:** $\sum_{i \in N} \varphi_i(v)=v(N)$.
- **Symmetry:** symmetric players receive equal payoffs.
- **Null player:** a player who never changes any coalition's worth receives
  payoff zero.
- **Additivity:** $\varphi(v+w)=\varphi(v)+\varphi(w)$.

Lean also defines the supporting predicates for symmetric players and null
players. These are the hypotheses of Shapley's uniqueness theorem
([[game_theory.cooperative_game.shapley_uniqueness]]).

## References

- [MSZ Ch.18, Def 18.2, Def 18.4, Def 18.6, Def 18.8] Maschler, Solan,
  Zamir, *Game Theory*.
