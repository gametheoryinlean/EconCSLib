---
id: math.minimax.lp_duality_minimax_proof
title: LP Duality Proof Of Minimax
kind: proof-plan
status: admitted
primary_topic: math
topics:
  - math
  - math.minimax
target: game_theory.strategic_game.zero_sum.von_neumann_minimax
plan_status: candidate
uses:
  - math.linear_programming.strong_duality
  - game_theory.strategic_game.zero_sum.maximin_le_minimax
  - math.simplex.bounded_by_value
source:
  spans:
    - artifact: mfogt
      locator: "Theorem 2.3.2 and proof after Theorem 2.3.2"
      format: section
      note: "LP duality proof of von Neumann minimax"
verification:
  proof: accepted
tags:
  - zero-sum
  - minimax
  - proof-plan
  - linear-programming
---

# LP Duality Proof Of Minimax

*Proof.* Shift the matrix by adding a positive constant to every entry, so all entries
are positive.  Apply finite-dimensional linear-programming duality
([[node:math.linear_programming.strong_duality]]) to the dual programs
$$
  XA \ge \mathbf{1}, \quad X \ge 0
$$
and
$$
  AY \le \mathbf{1}, \quad Y \ge 0.
$$
The dual optimal solutions have a common objective value $w>0$.  Normalizing
the vectors by $w$ gives mixed strategies $x^*$ and $y^*$, and the inequalities
become the minimax optimality inequalities with value $1/w$ via the simplex
bound transfer [[node:math.simplex.bounded_by_value]].  Weak duality
[[node:game_theory.strategic_game.zero_sum.maximin_le_minimax]] closes the sandwich, and undoing the
constant shift gives the original game.

This proof route is recorded as a `candidate` rather than `selected`: the
library's chosen formalisation route for [[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]]
is the simplified-Loomis induction
([[node:math.minimax.minimax_from_loomis]]). The LP-duality route is now
viable in EconCSLib via the strong-duality node (Farkas → LP strong duality)
landed in #71, but has not been carried through to a Lean proof.

## References

- [MFoGT, Thm. 2.3.2 and proof after Thm. 2.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. LP duality proof of von Neumann minimax.
