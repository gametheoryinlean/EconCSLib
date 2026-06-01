---
id: foundation.utility.risk_neutrality
title: Risk Neutrality
kind: theorem
status: staged
uses:
  - foundation.utility.expected_utility_representation
lean:
  modules:
    - EconCSLib.Foundation.Utility.Basic
  declarations:
    - IsAffineUtility
    - IsRiskNeutral
    - IsAffineUtility.isRiskNeutral
    - IsRiskNeutral.isAffine
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - utility
  - risk
---

# Risk Neutrality

A utility function over monetary outcomes is risk neutral when evaluating the
expected monetary payoff first and then applying utility gives the same result as
taking the expectation of utility:
$$
  u\left(\sum_i p_i x_i\right)=\sum_i p_i u(x_i).
$$

In the finite setting, this is equivalent to $u$ being affine:
$$
  u(x)=a x+b.
$$

## Proof Sketch

The affine-to-risk-neutral direction follows by distributing the affine formula
through the finite weighted sum. For the reverse direction, use two-outcome
lotteries to derive preservation of all convex combinations, then recover the
affine formula from the values of $u(0)$ and $u(1)$.

## References

- [MSZ, Chapter 2, Definitions 2.24-2.27] Maschler, Solan, and Zamir, *Game Theory*. Risk attitudes and risk neutrality.
