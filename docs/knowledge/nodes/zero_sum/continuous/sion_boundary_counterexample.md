---
id: game_theory.strategic_game.zero_sum.continuous.sion_boundary_counterexample
title: Sion Boundary Counterexample
kind: example
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.continuous.sion_minimax_theorem
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.5, Exercise 2"
      format: section
      note: "Counterexample satisfying Sion hypotheses except at one boundary point"
    - artifact: mfogt
      locator: "Section 9.3, Exercise 2 hints"
      format: section
      note: "Computes the pure gap and mixed value"
verification:
  proof: not_applicable
tags:
  - zero-sum
  - minimax
  - counterexample
---

# Sion Boundary Counterexample

Let $S=T=[0,1]$ and define $f:S\times T\to\{0,-1\}$ by
$$
  f(s,t)=
  \begin{cases}
    -1, & t=0\text{ and }s<1/2,\\
    -1, & t=1\text{ and }s\ge 1/2,\\
    0, & \text{otherwise}.
  \end{cases}
$$
This game has no value in pure strategies, while Sion's hypotheses fail only at
the boundary point $t=1$.

The pure quantities are
$$
  \sup_s\inf_t f(s,t)=-1,\qquad \inf_t\sup_s f(s,t)=0.
$$
Nevertheless, the mixed extension does have a value, equal to $-1/2$. Player 1
can guarantee this by playing uniformly on $[0,1]$, or by mixing equally between
$0$ and $1$.

## References

- [MFoGT, Section 3.5, Exercise 2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Counterexample satisfying Sion hypotheses except at one boundary point.
- [MFoGT, Section 9.3, Exercise 2 hints] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Computes the pure gap and mixed value.
