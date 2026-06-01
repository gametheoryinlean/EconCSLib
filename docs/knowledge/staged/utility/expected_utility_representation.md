---
id: foundation.utility.expected_utility_representation
title: Expected Utility Representation
kind: theorem
status: staged
uses:
  - foundation.preference.represents_preference
  - foundation.utility.vnm_axioms
lean:
  modules:
    - EconCSLib.Foundation.Utility.Lottery
  declarations:
    - Lottery.expectedValue
    - Lottery.expectedValue_pure
    - Lottery.expectedValue_mix
    - IsLinearUtility
    - expectedValue_isLinearUtility
verification:
  statement: accepted
  proof: gap
  alignment: pending
tags:
  - utility
  - vnm
  - expected-utility
---

# Expected Utility Representation

If a preference relation over lotteries satisfies the vNM axioms, then there is
a utility index $u:O\to \mathbb{R}$ such that the preference over lotteries is
represented by expected utility:
$$
  L \mapsto \sum_{o\in O} L(o)u(o).
$$

Equivalently, a linear utility functional on lotteries is determined by its
values on degenerate lotteries.

## Proof Sketch

MSZ first uses continuity to normalize every lottery between a best and a worst
outcome, then uses independence to show that the resulting numerical index is
linear with respect to compound lotteries. The expected value formula follows by
decomposing a finite lottery into degenerate lotteries.

The current Lean library already has the expected-value operator and the
linearity statement for expected value. The full representation theorem is
present as a theorem target in `EconCSLib/Utility/Lottery.lean`, but its
proof is still open.

## References

- [MSZ, Chapter 2, Thm. 2.18] Maschler, Solan, and Zamir, *Game Theory*. Expected-utility representation theorem.
