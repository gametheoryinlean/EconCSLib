---
id: mechanism_design.vcg.welfare_without
title: VCG Welfare Without Agent i
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.vcg
uses:
- mechanism_design.vcg.social_welfare
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.VCG
  declarations:
  - welfareWithout
  - socialWelfare_eq_value_add_welfareWithout
  - welfareWithout_le_socialWelfare
  - welfareWithout_le_socialWelfare_of_nonneg_i
  - welfareWithout_update_self
  - maxWelfareWithout
  - maxWelfareWithout_update_self
  - exists_withoutAllocation
  - withoutAllocation
  - withoutAllocation_isOptimal
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- vcg
- clarke-pivot
- welfare-without
---

# VCG Welfare Without Agent i

The "welfare-without-$i$" construction strips agent $i$'s own value
contribution from the social welfare functional, retaining only the
other agents' valuations at the same allocation:
$$
W_{-i}(v, a) \;=\; \sum_{j \neq i} v_j(a).
$$

Together with `maxWelfareWithout v i := \max_a W_{-i}(v, a)` it
underpins the Clarke-pivot payment $p_i(v) = \max_a W_{-i}(v, a) - W_{-i}(v, a^*)$
(see [[mechanism_design.vcg.payment_identity]]).

## Core identities and bounds

- **Decomposition** (`socialWelfare_eq_value_add_welfareWithout`):
  $W(v, a) = v_i(a) + W_{-i}(v, a)$ for every agent $i$ and allocation $a$.
- **Monotonicity** (`welfareWithout_le_socialWelfare`):
  $W_{-i}(v, a) \le W(v, a)$ when $v_i(a) \ge 0$, with a non-negativity
  variant `welfareWithout_le_socialWelfare_of_nonneg_i`.
- **Report independence** (`welfareWithout_update_self`,
  `maxWelfareWithout_update_self`): replacing agent $i$'s reported
  valuation does not change $W_{-i}$ or its max — by construction,
  agent $i$'s report is the one term excluded from the sum. This is
  the *strategic core* of the Clarke pivot: agent $i$ cannot influence
  $\max_a W_{-i}$.
- **Existence and choice** (`exists_withoutAllocation`,
  `withoutAllocation`, `withoutAllocation_isOptimal`): a welfare-
  without-$i$-maximising allocation always exists for finite $A$ and is
  selected noncomputably via choice.

## References

- [AGT Chapter 9, §9.3.4, Def 9.19] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*. Clarke-pivot payments.
