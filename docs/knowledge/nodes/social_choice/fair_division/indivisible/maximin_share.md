---
id: social_choice.fair_division.indivisible.maximin_share
title: Maximin Share (MMS) Allocation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.mms
uses:
  - social_choice.fair_division.indivisible.allocation
  - social_choice.fair_division.indivisible.valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsMaxminShare
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - mms
  - maximin-share
  - fairness
---

# Maximin Share (MMS) Allocation

The *maximin share* (MMS) guarantee asks that each agent's bundle be at
least as valuable as the best worst-piece they could guarantee by
self-partitioning.

In Lean: `SocialChoice.FairDivision.Indivisible.IsMaxminShare`. The
formulation used in the library, which avoids `iSup` / `iInf`, says:
$$
\forall i \in N,\ \forall B,\ \mathrm{IsAllocation}\ \mathrm{allGoods}\ B \Rightarrow
\exists j,\ v_i(B(j)) \le v_i(A(i)).
$$

That is: for every alternative complete allocation $B$ of `allGoods`,
*some* bundle in $B$ has value $\le v_i(A(i))$ from agent $i$'s
perspective.

## Equivalence to the standard MMS definition

The standard textbook MMS definition is
$$
v_i(A(i)) \;\ge\; \mathrm{MMS}_i \;=\;
\max_{B \text{ complete}}\ \min_{j} v_i(B(j)),
$$
i.e. agent $i$'s bundle weakly exceeds the maximum, over $i$'s own
self-partitions, of the worst bundle value. The library's definition is
equivalent: $\forall B,\ \exists j,\ v_i(B(j)) \le v_i(A(i))$ is the
same as $\forall B,\ \min_j v_i(B(j)) \le v_i(A(i))$, which rearranges
to $v_i(A(i)) \ge \max_B \min_j v_i(B(j))$.

The library makes this equivalence explicit:
[[social_choice.fair_division.indivisible.mms_value]] introduces the
extremal $\mathrm{MMS}_i$ value, and the bidirectional bridge
[[social_choice.fair_division.indivisible.is_alpha_mms_one]] shows
`IsMaxminShare` is exactly the $\alpha = 1$ case of α-MMS.

## Position in the hierarchy

For additive valuations on complete allocations, the chain
$$
\mathrm{EF} \Rightarrow \mathrm{EFX} \Rightarrow \mathrm{EF1} \Rightarrow \mathrm{PROP} \Rightarrow \mathrm{MMS}
$$
holds via the implication theorems
([[social_choice.fair_division.indivisible.efx_implies_ef1]],
[[social_choice.fair_division.indivisible.ef_implies_efx_mono]],
[[social_choice.fair_division.indivisible.ef_implies_proportional_additive]],
[[social_choice.fair_division.indivisible.proportional_implies_mms_additive]]).

## Existence

- MMS allocations exist *almost always* for additive valuations
  (Bouveret–Lemaître 2014).
- Procaccia–Wang (2014) construct a counterexample showing MMS need
  not always exist.
- A $\frac{3}{4}$-MMS allocation is always achievable for additive preferences;
  see the α-MMS definition
  ([[social_choice.fair_division.indivisible.is_alpha_mms]]).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Maximin share guarantee.
- Budish, E. (2011). "The Combinatorial Assignment Problem". *J. Pol. Econ.*
- Bouveret, Chevaleyre, and Maudet (2016). "Fair Allocation of Indivisible Goods", COMSOC Handbook Ch. 12.
