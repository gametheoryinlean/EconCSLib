---
id: social_choice.fair_division.indivisible.egalitarian_welfare
title: Indivisible Egalitarian (Maximin) Welfare
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.allocation
  - social_choice.fair_division.indivisible.valuation
  - social_choice.fair_division.egalitarian_welfare
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.SocialWelfare
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsMaxmin
    - SocialChoice.FairDivision.Indivisible.egalitarianWelfare_le
    - SocialChoice.FairDivision.Indivisible.nsmul_egalitarianWelfare_le_utilitarianWelfare
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - welfare
  - egalitarian
  - maximin
---

# Indivisible Egalitarian (Maximin) Welfare

Specialisation of the generic egalitarian welfare
([[social_choice.fair_division.egalitarian_welfare]]) to the
indivisible setting: for a valuation $v$ and allocation $A$ on a finite
nonempty agent type,
$$
W_{\mathrm{egal}}(v, A) = \min_{i \in N} v_i(A(i)).
$$

The same definition `egalitarianWelfare` (under
`SocialChoice.FairDivision`) applies, taking `v.val` for the per-agent
utility function and the indivisible allocation
([[social_choice.fair_division.indivisible.allocation]]) for the share
assignment.

The instance-keyed *optimality* predicate is wrapped here:

- `IsMaxmin` (abbrev): no complete allocation
  (`IsAllocation allGoods B`) has strictly larger egalitarian welfare.

## Basic lemmas

Re-exported from the generic layer with the indivisible-friendly
hypotheses:

- `egalitarianWelfare_le`: $W_{\mathrm{egal}}(v, A) \le v_i(A(i))$ for
  every agent $i$.
- `nsmul_egalitarianWelfare_le_utilitarianWelfare`: combined with
  [[social_choice.fair_division.indivisible.utilitarian_welfare]],
  $|N| \cdot W_{\mathrm{egal}} \le W_{\mathrm{util}}$.

## Relation to MMS

Egalitarian welfare is a *global* maximin (over all $i$, take the
worst-off), while MMS
([[social_choice.fair_division.indivisible.maximin_share]]) is a
*per-agent* maximin (over self-partitions). They are conceptually
related but distinct: $W_{\mathrm{egal}}$ depends only on the bundle
values, while MMS additionally depends on each agent's full valuation
structure.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Egalitarian welfare for indivisible goods.
