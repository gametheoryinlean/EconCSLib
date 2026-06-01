---
id: game_theory.strategic_game.dynamics.stable_game_framework
title: Stable Game Framework (Hofbauer–Sandholm)
kind: theorem
status: staged
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
uses:
  - game_theory.strategic_game.population.population_game
  - game_theory.strategic_game.potential.potential_game
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - dynamics
  - potential-game
  - zero-sum
  - lyapunov
  - deferred
---

# Stable Game Framework (Hofbauer–Sandholm)

> **Status: DEFERRED — do not implement.**
> Parked pending sufficient Mathlib infrastructure (differential
> inclusions, LaSalle invariance principle, ω-limit sets for
> continuous-time set-valued dynamics). Tracked as
> [gametheoryinlean/EconCSLib#41](https://github.com/gametheoryinlean/EconCSLib/issues/41).

## Statement

Let $F : X \to \mathbb{R}^n$ be the payoff field of a population game over a
compact convex strategy space $X = \prod_i \Delta(S_i)$. The game is **stable**
if
$$
  (x - y) \cdot (F(x) - F(y)) \le 0, \qquad \forall x, y \in X.
$$
It is **strictly stable** if equality forces $x = y$, and **null stable** if
equality always holds.

**Hofbauer–Sandholm (2009).** Stable games admit a Lyapunov function for the
best response dynamics
$$
  \dot x_t \in BR(x_t) - x_t,
$$
namely the **maximum payoff gain**
$$
  G(x) := \max_{y \in X} (y - x) \cdot F(x) \;\ge\; 0,
$$
which satisfies $\dot G(x_t) \le -G(x_t)$ wherever $F$ is sufficiently regular,
and vanishes exactly on the Nash equilibrium set. By LaSalle's invariance
principle, every solution converges to the set of Nash equilibria.

## Why this unifies potential and zero-sum

- **Potential games** are stable with $G(x) = \max_y \Phi(y) - \Phi(x)$, where
  $\Phi$ is the (concave) potential. See
  [[game_theory.strategic_game.potential.potential_game]] and
  [[game_theory.strategic_game.dynamics.potential_replicator_lyapunov]].
- **Two-player zero-sum games**, viewed as a single population game over the
  product simplex with $F = (Ay, -A^T x)$, are **null stable**. The Lyapunov
  $G$ specialises to the duality gap
  $$
    G(x, y) = \max_i (Ay)_i - \min_j (x^T A)_j,
  $$
  recovering Hofbauer (1995) for continuous-time fictitious play; see
  [[game_theory.strategic_game.zero_sum.learning.continuous_fictitious_play_gap]].

The discrete-time fictitious play convergence
([[game_theory.strategic_game.zero_sum.learning.fictitious_play_convergence]]) is **not** a direct
consequence — the discrete duality gap is non-monotone — and continues to
require Robinson's combinatorial argument
([[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]]).

## Why deferred

Formalising the continuous-time half of the framework requires:

1. **Differential inclusions** (set-valued ODEs with upper-semicontinuous RHS)
   — Filippov / Aubin–Cellina theory. Essentially absent from Mathlib.
2. **LaSalle invariance principle** for continuous-time dynamics on compact
   manifolds. Absent from Mathlib.
3. **ω-limit set machinery** for set-valued flows on convex compact subsets of
   $\mathbb{R}^n$. Mathlib has `Mathlib.Dynamics.OmegaLimit` for single-valued
   topological dynamics; would need extension.
4. **Sub-differential calculus** on the simplex for the directional derivative
   $\dot G$ along BR trajectories.

Each is a multi-month project on its own. The full chain is at the scale of a
PhD-grade formalisation effort and is out of scope for the current focus on
classical zero-sum and matrix-game results.

## What we keep instead

The current library treats potential and zero-sum dynamics as two separate
classical instances:

- **Zero-sum.** Robinson 1951 admissible-sequence proof in
  [[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]].
- **Potential.** Monderer–Shapley-style discrete monotonicity of $\Phi$, with
  the Lyapunov calculation already drafted in
  [[game_theory.strategic_game.dynamics.potential_replicator_lyapunov]].

The unifying picture is recorded here for blueprint readers without taking on
the formalisation cost.

## References

- [Hofbauer–Sandholm 2009] J. Hofbauer and W. H. Sandholm, "Stable games and
  their dynamics", *Econometrica* 77(5), 1665–1683, 2009.
- [Hofbauer 1995] J. Hofbauer, "Stability for the best response dynamics",
  preprint, University of Vienna, 1995.
- [Sandholm 2010] W. H. Sandholm, *Population Games and Evolutionary Dynamics*,
  MIT Press, 2010, Chapters 3 and 7.
- [Monderer–Shapley 1996] D. Monderer and L. S. Shapley, "Fictitious play
  property for games with identical interests", *Journal of Economic Theory*
  68(1), 258–265, 1996.
