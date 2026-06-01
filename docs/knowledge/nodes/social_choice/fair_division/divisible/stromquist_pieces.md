---
id: social_choice.fair_division.divisible.stromquist_pieces
title: Stromquist Pieces from the Division Simplex
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.stromquist
uses:
  - social_choice.fair_division.divisible.allocation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.Existence
  declarations:
    - SocialChoice.FairDivision.Divisible.strom_piece
    - SocialChoice.FairDivision.Divisible.strom_piece_partition
    - SocialChoice.FairDivision.Divisible.strom_piece_empty_iff
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - stromquist
  - simplex
---

# Stromquist Pieces from the Division Simplex

Stromquist's proof parametrizes contiguous $n$-piece partitions of the
real line $\mathbb{R}$ by points in the standard simplex
$$
S = \mathrm{stdSimplex}\ \mathbb{R}\ (\mathrm{Fin}\ n) \;=\;
\{x : \mathrm{Fin}\ n \to \mathbb{R} \mid x_i \ge 0,\ \sum_i x_i = 1\}.
$$

A point $x \in S$ encodes the *fractional lengths* of $n$ consecutive
pieces; the actual cut points in $\mathbb{R}$ are recovered via a fixed
homeomorphism $\varphi : (0, 1) \to \mathbb{R}$ (a homeomorphism).

## The $i$-th piece at division $x$

In Lean: `strom_piece (x : Fin n → ℝ) (i : Fin n) : Set ℝ`. Informally:
$$
\mathrm{piece}(x, i) \;=\; \varphi\bigl(\bigl(\sum_{j < i} x_j,\ \sum_{j \le i} x_j\bigr]\bigr).
$$

The piece collapses to the empty set exactly when its fractional length
is zero — `strom_piece_empty_iff`:
$$
\mathrm{piece}(x, i) = \emptyset \;\iff\; x_i = 0.
$$

## Partition property

For every $x \in S$, the pieces $\{\mathrm{piece}(x, i) : i \in \mathrm{Fin}\ n\}$
form a complete measurable partition of $\mathbb{R}$:

- measurability of each piece (from the half-open interval form);
- pairwise disjointness (by the ordering of the partial sums $\sum_{j < i} x_j$);
- cover of $\mathbb{R}$ (the union of all half-open intervals over a partition
  of $(0, 1)$, transported by $\varphi$).

In Lean: `strom_piece_partition`. This is the building block that turns a
KKM-found simplex point into a divisible allocation in
[[social_choice.fair_division.divisible.stromquist_assignment]].

## References

- Stromquist, W. (1980). "How to Cut a Cake Fairly". *Amer. Math. Monthly* 87: 640–644.
