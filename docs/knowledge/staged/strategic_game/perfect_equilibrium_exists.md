---
id: game_theory.strategic_game.refinements.perfect_equilibrium_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Existence Of Perfect Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.refinements.perfect_equilibrium
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - equilibrium-refinement
  - existence
---

# Existence Of Perfect Equilibrium

Every finite normal-form game has at least one perfect equilibrium. Moreover,
every perfect equilibrium is a Nash equilibrium.

## Proof Sketch

Fix a fully mixed profile $\tau$ and $\epsilon\in(0,1)$. Define a perturbed game
with payoff
$$
  \sigma\mapsto g((1-\epsilon)\sigma+\epsilon\tau).
$$
By Nash's theorem, this perturbed game has a Nash equilibrium $\nu^\epsilon$.
Then
$$
  \sigma^\epsilon=(1-\epsilon)\nu^\epsilon+\epsilon\tau
$$
is completely mixed and $\epsilon$-perfect. Compactness gives a convergent
subsequence as $\epsilon\to 0$, and continuity implies that every limit is Nash.

## References

- [MFoGT, Thm. 6.5.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every finite normal-form game has a perfect equilibrium and every perfect equilibrium is Nash.
