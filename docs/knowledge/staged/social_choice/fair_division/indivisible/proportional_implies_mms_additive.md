---
id: social_choice.fair_division.indivisible.proportional_implies_mms_additive
title: PROP ⇒ MMS (Additive Valuations, Complete Allocations)
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.mms
uses:
  - social_choice.fair_division.indivisible.proportional
  - social_choice.fair_division.indivisible.maximin_share
  - social_choice.fair_division.indivisible.additive_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Implications
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsProportional.isMaxminShare
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - additive
  - proportional
  - mms
---

# PROP ⇒ MMS (Additive Valuations, Complete Allocations)

**Theorem.** Let $w$ be an additive valuation, `allGoods` the outer
good set, and $A$ a proportional allocation
([[social_choice.fair_division.indivisible.proportional]]) under
$w.\mathrm{toValuation}$. Then $A$ satisfies the maximin-share guarantee
([[social_choice.fair_division.indivisible.maximin_share]]).

In Lean: `SocialChoice.FairDivision.Indivisible.IsProportional.isMaxminShare`.

## Proof (by contradiction)

Fix an agent $i$ and an alternative complete allocation $B$. Suppose for
contradiction that no bundle of $B$ has value $\le v_i(A(i))$ from
agent $i$'s perspective. By linear ordering on $\mathbb{R}$,
$\forall j,\ v_i(A(i)) < v_i(B(j))$.

By `Finset.sum_lt_sum` (using the strict inequality at least once for
the nonempty population), the constant sum strictly beats the
$B$-sum:
$$
|N| \cdot v_i(A(i)) = \sum_{j} v_i(A(i)) < \sum_{j} v_i(B(j)).
$$

By additivity of $w$ and the cover property of $B$:
$$
\sum_{j} v_i(B(j)) = v_i(\mathrm{allGoods}).
$$

Combining with proportionality of $A$
([[social_choice.fair_division.indivisible.ef_implies_proportional_additive]]
or equivalently the hypothesis here):
$$
v_i(\mathrm{allGoods}) \le |N| \cdot v_i(A(i)).
$$

Chaining gives $|N| \cdot v_i(A(i)) < |N| \cdot v_i(A(i))$, a
contradiction. Hence some bundle of $B$ does satisfy the MMS
inequality. $\square$

## Significance

This is the last link in the additive-valuations chain
$\mathrm{EF} \Rightarrow \mathrm{PROP} \Rightarrow \mathrm{MMS}$. Combined
with [[social_choice.fair_division.indivisible.efx_implies_ef1]] and
[[social_choice.fair_division.indivisible.ef_implies_efx_mono]], it
gives the full chain
$\mathrm{EF} \Rightarrow \mathrm{EFX} \Rightarrow \mathrm{EF1} \Rightarrow \mathrm{PROP} \Rightarrow \mathrm{MMS}$
for additive valuations on complete allocations.

Note the converse $\mathrm{MMS} \Rightarrow \mathrm{PROP}$ does not
hold in general (MMS is strictly weaker than PROP).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. PROP–MMS implication.
- Budish, E. (2011). "The Combinatorial Assignment Problem". *J. Pol. Econ.*
- Bouveret, Chevaleyre, and Maudet (2016). "Fair Allocation of Indivisible Goods", COMSOC Handbook Ch. 12.
