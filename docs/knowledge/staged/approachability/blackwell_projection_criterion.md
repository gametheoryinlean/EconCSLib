---
id: game_theory.strategic_game.zero_sum.approachability.blackwell_projection_criterion
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.applications
title: Stochastic Blackwell Projection Criterion
kind: theorem
status: staged
lean:
  modules:
    - EconCSLib.Math.Probability.Blackwell
  declarations:
    - EconCSLib.ApproachesSet
    - EconCSLib.ApproachesSetAE
    - EconCSLib.ClosedConvexTarget
    - EconCSLib.ClosedConvexTarget.projection
    - EconCSLib.ClosedConvexTarget.projection_lipschitz
    - EconCSLib.Blackwell.BlackwellClosedConvexConditionAE
    - EconCSLib.Blackwell.blackwell_approach_closedConvex_ae
    - EconCSLib.Blackwell.blackwell_projectionDistance_tendsto_zero_ae
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - approachability
  - convexity
  - probability
  - vector-payoff
---

# Stochastic Blackwell Projection Criterion

Let $(x_n)$ be a uniformly bounded adapted process in a finite-dimensional
real Hilbert space, let
$$
  y_{n+1}=\mathbb E[x_{n+1}\mid\mathcal F_n],
$$
and let $D$ be nonempty, closed, and convex. If
$$
  \left\langle \bar x_n-\Pi_D(\bar x_n),
    y_{n+1}-\Pi_D(\bar x_n)\right\rangle\le 0
$$
almost surely at every stage, then
$$
  \lVert\bar x_n-\Pi_D(\bar x_n)\rVert\longrightarrow 0
  \qquad\text{almost surely}.
$$

This is MFoGT's stochastic projection criterion. The formal statement is slightly more reusable
than the displayed $\mathbb R^K$ version: it works in every finite-dimensional
real Hilbert space with its Borel measurable structure. Adaptedness is made
explicit because the theorem is stated for an arbitrary filtration rather
than only the natural history filtration.

## Proof Sketch

Use squared distance to $D$ as a potential. Metric projection gives a one-step
deterministic inequality proved directly in the Lean module. Conditional
expectation removes the cross term, leaving an $O(1/n)$ expected-potential
bound. Markov's inequality and Borel--Cantelli give almost-sure convergence on
square checkpoints; uniform boundedness interpolates between checkpoints.

This theorem does not use the separate
[[game_theory.strategic_game.zero_sum.approachability.deterministic_blackwell_sequence]]
node, whose stronger standalone Cesaro-sequence packaging remains a declared
proof gap.

## References

- [MFoGT, Theorem 7.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Almost-sure Blackwell projection criterion for bounded random sequences.
