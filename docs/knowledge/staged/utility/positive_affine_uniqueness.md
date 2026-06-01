---
id: foundation.utility.positive_affine_uniqueness
title: Positive Affine Uniqueness Of Utility
kind: theorem
status: staged
uses:
  - foundation.utility.expected_utility_representation
lean:
  modules:
    - EconCSLib.Foundation.Utility.AffineTransform
  declarations:
    - IsPositiveAffineOf
    - IsPositiveAffineOf.preserves_le
    - IsPositiveAffineOf.preserves_representation
    - IsPositiveAffineOf.symm
verification:
  statement: accepted
  proof: gap
  alignment: pending
tags:
  - utility
  - affine
  - vnm
---

# Positive Affine Uniqueness Of Utility

If two expected-utility functions represent the same preference over lotteries,
then they differ by a positive affine transformation:
$$
  v(L)=a u(L)+b
  \quad\text{with}\quad a>0.
$$

Conversely, a positive affine transformation of a representing utility function
represents the same preference relation.

## Proof Sketch

The order-preserving direction is immediate from $a>0$. For uniqueness, compare
the two representations on degenerate lotteries and use linearity over lotteries
to extend the affine relation from outcomes to all lotteries.

The Lean library has the positive-affine relation and its order-preservation and
inverse lemmas. The full uniqueness theorem for linear utility functionals is
still an open theorem target in `EconCSLib/Utility/Lottery.lean`.

## References

- [MSZ, Chapter 2, Thm. 2.22] Maschler, Solan, and Zamir, *Game Theory*. Uniqueness of expected utility up to positive affine transformation.
- [MSZ, Chapter 2, Exercise 2.19] Maschler, Solan, and Zamir, *Game Theory*. Inverse of a positive affine transformation.
