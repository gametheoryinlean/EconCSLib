---
id: mechanism_design.vcg.payment_identity
title: VCG Payment Identity
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.vcg
uses:
- mechanism_design.vcg.social_welfare
- mechanism_design.vcg.welfare_without
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.VCG
  declarations:
  - VCGMechanism_quasiLinearUtility_eq_socialWelfare_sub_maxWelfareWithout
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
- mechanism-design
- vcg
- payment-identity
- clarke-pivot
---

# VCG Payment Identity

**Theorem.** Under the VCG mechanism with valuation profile $v$ and
allocation $a^* = \mathrm{efficientAllocation}\ v$, every agent $i$'s
quasi-linear utility under truthful reporting equals
$$
u_i \;=\; W(v, a^*) \;-\; \max_{a \in A} W_{-i}(v, a).
$$

Equivalently: **agent $i$'s utility is their marginal contribution to
social welfare.**

In Lean: `VCGMechanism_quasiLinearUtility_eq_socialWelfare_sub_maxWelfareWithout`.

## Why this is the soul of VCG

The two headline VCG properties fall out of this identity almost
immediately:

- **Truthfulness** ([[mechanism_design.vcg_truthfulness_and_ir]]):
  $u_i$ depends on $i$'s reported valuation only through $a^*$ (the
  $W_{-i}$ term is *report-independent*, see
  [[mechanism_design.vcg.welfare_without]] `_update_self` lemmas).
  Hence maximising $u_i$ over $i$'s report is equivalent to
  maximising $v_i(a^*)$ given the other agents' reports — which truthful
  reporting achieves by definition of $a^*$.

- **Individual rationality** (under non-negative valuations): $u_i \ge 0$
  iff $W(v, a^*) \ge \max_a W_{-i}(v, a)$, i.e. agent $i$'s presence
  weakly increases the achievable social welfare. This is automatic
  when $v_i \ge 0$ pointwise — adding agent $i$'s valuation can only
  raise the max.

## Proof sketch

Substitute the Clarke-pivot payment
$p_i = \max_a W_{-i}(v, a) - W_{-i}(v, a^*)$ into the quasi-linear
utility $u_i = v_i(a^*) - p_i$:
$$
u_i \;=\; v_i(a^*) + W_{-i}(v, a^*) - \max_a W_{-i}(v, a)
   \;=\; W(v, a^*) - \max_a W_{-i}(v, a),
$$
using `socialWelfare_eq_value_add_welfareWithout`.

## References

- [AGT Chapter 9, §9.3.4] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
  VCG mechanism and the payment identity.
- Vickrey, W. (1961); Clarke, E. H. (1971); Groves, T. (1973). Original
  VCG papers.
