---
id: social_choice.fair_division.indivisible.mms_value_bounds
title: MMS Value — Basic Bounds
kind: lemma
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.mms
uses:
  - social_choice.fair_division.indivisible.mms_value
  - social_choice.fair_division.indivisible.additive_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.MMS
  declarations:
    - SocialChoice.FairDivision.Indivisible.iInf_partition_le_mmsValue
    - SocialChoice.FairDivision.Indivisible.mmsValue_le_of_forall
    - SocialChoice.FairDivision.Indivisible.mmsValue_nonneg
    - SocialChoice.FairDivision.Indivisible.mmsValue_le_proportional_share_additive
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - mms
  - bounds
---

# MMS Value — Basic Bounds

Four foundational bounds on $\mathrm{MMS}_i$
([[social_choice.fair_division.indivisible.mms_value]]).

## Lower bound from any partition

`iInf_partition_le_mmsValue`: for every complete allocation $B$ of
`allGoods`, the worst-bundle value provides a lower bound:
$$
\min_{j} v_i(B(j)) \le \mathrm{MMS}_i.
$$

This is one direction of the max-of-mins definition: any specific $B$
yields a min that the max-over-all-$B$ must dominate.

## Upper bound from a uniform agent guarantee

`mmsValue_le_of_forall`: if some value $c$ satisfies "every complete
allocation $B$ has some bundle $j$ with $v_i(B(j)) \le c$", then
$\mathrm{MMS}_i \le c$.

This is the dual direction: any uniform upper bound on the worst-piece
across all partitions provides an upper bound on the maximin value.

## Nonnegativity

`mmsValue_nonneg`: when values are nonnegative, $\mathrm{MMS}_i \ge 0$.
The empty allocation (`B(j) = ∅` for all $j$, valid only when
$\mathrm{allGoods} = \emptyset$) trivially has all bundles of value $0$,
giving the nonnegativity bound.

## MMS bounded by proportional share (additive valuations)

`mmsValue_le_proportional_share_additive` (for an additive valuation
[[social_choice.fair_division.indivisible.additive_valuation]] with
nonnegative weights):
$$
n \cdot \mathrm{MMS}_i \le v_i(\mathrm{allGoods}).
$$

Equivalently, $\mathrm{MMS}_i \le v_i(\mathrm{allGoods}) / n$. The
argument: take any complete allocation $B$; the sum of $v_i(B(j))$
over $j$ equals $v_i(\mathrm{allGoods})$ by additivity; the worst
bundle is at most the average, i.e. $\le v_i(\mathrm{allGoods}) / n$.
Taking $\sup_B$ preserves this bound.

This is a *foundational* fact: it shows the MMS guarantee is at most
the proportional share, hence MMS is a *weaker* notion than PROP for
additive valuations.

## References

- Budish, E. (2011). "The Combinatorial Assignment Problem". *J. Pol. Econ.*
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. MMS value bounds.
