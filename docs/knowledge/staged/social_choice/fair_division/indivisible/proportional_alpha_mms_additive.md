---
id: social_choice.fair_division.indivisible.proportional_alpha_mms_additive
title: PROP ⇒ α-MMS (Additive Valuations)
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
  - social_choice.fair_division.indivisible.is_alpha_mms
  - social_choice.fair_division.indivisible.mms_value_bounds
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.MMS
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsProportional.isAlphaMMS_additive
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - additive
  - proportional
  - alpha-mms
---

# PROP ⇒ α-MMS (Additive Valuations)

**Theorem.** For an additive valuation
([[social_choice.fair_division.indivisible.additive_valuation]]) with
nonnegative weights, every proportional allocation
([[social_choice.fair_division.indivisible.proportional]]) is
*1-MMS* — i.e. it satisfies the α-MMS guarantee
([[social_choice.fair_division.indivisible.is_alpha_mms]]) at the
maximum α.

In Lean: `SocialChoice.FairDivision.Indivisible.IsProportional.isAlphaMMS_additive`.

## Proof

The MMS value is bounded above by the proportional share
$v_i(\mathrm{allGoods}) / n$ in the additive case
([[social_choice.fair_division.indivisible.mms_value_bounds]]'s
`mmsValue_le_proportional_share_additive`):
$$
n \cdot \mathrm{MMS}_i \le v_i(\mathrm{allGoods}).
$$

The PROP hypothesis gives
$v_i(\mathrm{allGoods}) \le n \cdot v_i(A(i))$. Combining:
$$
n \cdot \mathrm{MMS}_i \le n \cdot v_i(A(i)).
$$

Dividing by $n > 0$ (or staying in integer form via the no-division
trick) gives $\mathrm{MMS}_i \le v_i(A(i))$, which is the 1-MMS
condition.

## Relation to the exact-MMS implication

The exact `IsMaxminShare` implication
([[social_choice.fair_division.indivisible.proportional_implies_mms_additive]])
is the equivalent statement in the alternative formulation; the two
agree by [[social_choice.fair_division.indivisible.mms_iff_alpha_one]].

## Significance

This closes the implication chain for additive valuations:
$$
\mathrm{EF} \Rightarrow \mathrm{PROP} \Rightarrow \mathrm{1\text{-}MMS} \;\iff\; \mathrm{IsMaxminShare}.
$$

So *every* EF allocation in the additive setting is automatically
MMS-fair — though the converse fails (PROP and MMS are strictly weaker
than EF).

## References

- Budish, E. (2011). "The Combinatorial Assignment Problem". *J. Pol. Econ.*
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. PROP-MMS implication.
