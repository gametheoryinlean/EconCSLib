---
id: math.linear_programming.minimax_bridge.zero_sum_lp_bridge
title: Zero-Sum Linear Programming Bridge
kind: proof-plan
status: admitted
primary_topic: math
topics:
  - math
  - math.linear_programming
  - math.linear_programming.minimax_bridge
target: game_theory.strategic_game.zero_sum.von_neumann_minimax
plan_status: candidate
uses:
  - math.linear_programming.strong_duality
source:
  spans:
    - artifact: agt
      locator: "Section 1.4.2, Theorem 1.11"
      format: section
      note: "Optimal zero-sum LP solutions form a Nash equilibrium"
verification:
  statement: accepted
  proof: accepted
generality:
  reviewed: true
  prompt: "How should AGT's LP statement enter the library?"
  verdict: "As a bridge from existing matrix-game guarantees and minimax infrastructure, not as a separate minimax proof."
tags:
  - zero-sum
  - linear-programming
  - nash-equilibrium
  - staged
---

# Zero-Sum Linear Programming Bridge

The row player's maximum safe-value linear program and the column player's
minimum safe-value dual linear program should be connected to the matrix-game
guarantee definitions.  Once optimal row and column safe strategies are
available, they form a mixed Nash equilibrium of the zero-sum game.

This bridge is the natural entry point for algorithmic game theory treatments
of zero-sum computation.

*Proof.* The row LP maximizes a scalar $v$ subject to the inequalities saying
that the chosen mixed row strategy guarantees at least $v$ against every pure
column. The dual column LP minimizes a scalar $w$ subject to the inequalities
saying that the chosen mixed column strategy holds every pure row payoff to at
most $w$. Strong duality gives optimal solutions with $v=w$. These two sets of
inequalities are exactly the saddle-point inequalities for the matrix payoff, so
the resulting mixed strategies form a zero-sum Nash equilibrium and realize the
matrix-game value.

## References

- [AGT, Section 1.4.2, Thm. 1.11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Optimal zero-sum LP solutions form a Nash equilibrium.
