---
id: math.minimax.kakutani_minimax_proof
title: Kakutani Fixed-Point Proof of the Minimax Theorem
kind: proof-plan
status: admitted
primary_topic: math
topics:
  - math
  - math.minimax
target: game_theory.strategic_game.zero_sum.von_neumann_minimax
plan_status: candidate
uses:
  - game_theory.strategic_game.zero_sum.matrix_game
  - game_theory.strategic_game.zero_sum.core.saddle_point
verification:
  proof: accepted
tags:
  - zero-sum
  - minimax
  - fixed-point
  - kakutani
  - proof-plan
---

# Kakutani Fixed-Point Proof of the Minimax Theorem

A proof of von Neumann's minimax theorem
([[game_theory.strategic_game.zero_sum.von_neumann_minimax]]) via the **Kakutani
fixed-point theorem**, complementing the Loomis induction proof
([[math.minimax.loomis_induction_proof]]) and the LP-duality
proof ([[math.minimax.lp_duality_minimax_proof]]).

This is the route Nash later generalised to obtain Nash equilibrium
existence in $N$-person finite games — the zero-sum minimax theorem
falls out as the 2-player zero-sum special case.

## Proof plan

For a finite matrix game $A : I \times J \to \mathbb{R}$:

1. **Best-response correspondence.** Define
   $$
   \mathrm{BR} : \Delta(I) \times \Delta(J) \;\rightrightarrows\; \Delta(I) \times \Delta(J)
   $$
   by
   $\mathrm{BR}(x, y) = (\arg\max_{x'} x' A y) \times (\arg\min_{y'} x A y')$.

   Each component is a convex compact subset of the corresponding
   simplex (set of maximisers / minimisers of a continuous linear
   function on a compact convex set).

2. **Kakutani hypotheses.** $\mathrm{BR}$ has nonempty convex compact
   values (linear optimisation on a compact convex set), and its graph
   is closed by continuity of the bilinear $xAy$. The domain
   $\Delta(I) \times \Delta(J)$ is compact, convex, and nonempty.

3. **Apply Kakutani.** $\mathrm{BR}$ has a fixed point
   $(x^*, y^*)$ — a profile that is its own best response.

4. **Fixed point ⇒ saddle point.** At $(x^*, y^*)$:
   - $x^*$ maximises $x A y^*$ over $x \in \Delta(I)$;
   - $y^*$ minimises $x^* A y$ over $y \in \Delta(J)$.

   So for every $x \in \Delta(I)$ and $y \in \Delta(J)$:
   $$
   x A y^* \;\le\; x^* A y^* \;\le\; x^* A y.
   $$

   This is the **saddle-point inequality**
   ([[game_theory.strategic_game.zero_sum.core.saddle_point]]), equivalent to existence of value
   and optimal strategies for both players (the minimax theorem).

## Why this route matters

- **Pedagogical**: gives a clean conceptual proof using a single
  topological theorem (Kakutani), avoiding the combinatorial / LP-
  duality machinery.
- **Strategic**: this is the proof technique Nash generalised to
  multi-player non-zero-sum games. Reading the minimax proof in this
  shape clarifies why Nash equilibrium is the natural generalisation
  of saddle point.
- **Connections**: Kakutani follows from Brouwer; many minimax-style
  results in continuous games (Sion's theorem
  [[game_theory.strategic_game.zero_sum.continuous.sion_minimax_theorem]]) similarly reduce to
  Brouwer / Kakutani arguments.

## Where Kakutani is missing in this library

EconCSLib does not yet carry Kakutani in Lean. Until that infrastructure is
implemented, this proof exists only at blueprint level. The Lean proof of the matrix-game minimax
theorem currently uses Loomis ([[math.minimax.minimax_from_loomis]]) over ℝ,
and `Minimax.minimax` ([[node:math.minimax.ordered_field_minimax]]) over any
linearly ordered field.

## References

- von Neumann, J. (1928). "Zur Theorie der Gesellschaftsspiele".
  *Math. Ann.* 100: 295–320.
- Nash, J. F. (1950). "Equilibrium Points in N-Person Games". *PNAS*.
- Kakutani, S. (1941). "A Generalization of Brouwer's Fixed Point
  Theorem". *Duke Math. J.* 8: 457–459.
- [MSZ Chapter 5] Maschler, Solan, and Zamir, *Game Theory*.
- [MFoGT Chapter 2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*.
