---
id: mechanism_design.vcg.social_welfare
title: VCG Social Welfare
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.vcg
uses:
- mechanism_design.transfer.multiple_parameter_transfer_layer
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.VCG
  declarations:
  - socialWelfare
  - maxSocialWelfare
  - exists_efficientAllocation
  - efficientAllocation
  - efficientAllocation_isOptimal
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- vcg
- social-welfare
---

# VCG Social Welfare

For a multiple-parameter mechanism with valuation profile
$v : I \to (A \to \mathbb{R})$, the **social welfare** of allocation
$a \in A$ is
$$
W(v, a) \;=\; \sum_{i \in I} v_i(a).
$$

`maxSocialWelfare v` is the supremum of $W(v, \cdot)$ over $A$; for a
finite outcome set this maximum is attained, and `efficientAllocation v`
is a chosen welfare-maximiser (noncomputable via choice). The
correctness lemma `efficientAllocation_isOptimal` states
$W(v, \mathrm{efficientAllocation}\ v) \ge W(v, a)$ for every $a \in A$.

This is the welfare-maximisation layer that the VCG mechanism's
allocation rule and Clarke-pivot payment construction both build on:

- The VCG allocation rule simply returns the efficient allocation.
- The Clarke-pivot payment for agent $i$ subtracts the
  "welfare-without-$i$" max ([[mechanism_design.vcg.welfare_without]])
  from the realised social welfare, giving the VCG identity
  ([[mechanism_design.vcg.payment_identity]]).

## References

- [AGT Chapter 9, §9.3.3, Def 9.16] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*. Welfare-maximising allocation
  rules for VCG.
