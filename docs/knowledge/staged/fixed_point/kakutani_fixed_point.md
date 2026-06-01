---
id: math.fixed_point.kakutani_fixed_point
title: Kakutani Fixed Point Theorem
kind: theorem
status: staged
uses:
  - math.fixed_point.brouwer_compact_convex
verification:
  statement: accepted
  proof: gap
tags:
  - fixed-point
  - kakutani
---

# Kakutani Fixed Point Theorem

Let $C$ be a nonempty convex compact subset of a normed vector space. Let
$F:C\rightrightarrows C$ be a correspondence such that:

1. for every $c\in C$, $F(c)$ is nonempty, compact, and convex;
2. the graph $\{(c,d)\in C\times C:d\in F(c)\}$ is closed.

Then the fixed point set
$$
  \{c\in C:c\in F(c)\}
$$
is nonempty and compact.

## References

- [MFoGT, Thm. 4.11.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Kakutani fixed point theorem for closed-graph convex compact valued correspondences.
