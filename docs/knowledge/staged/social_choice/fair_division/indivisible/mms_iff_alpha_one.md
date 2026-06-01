---
id: social_choice.fair_division.indivisible.mms_iff_alpha_one
title: IsMaxminShare ↔ IsAlphaMMS 1
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.mms
uses:
  - social_choice.fair_division.indivisible.maximin_share
  - social_choice.fair_division.indivisible.is_alpha_mms
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.MMS
  declarations:
    - SocialChoice.FairDivision.Indivisible.isMaxminShare_iff_isAlphaMMS_one
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - mms
  - alpha-mms
  - equivalence
---

# IsMaxminShare ↔ IsAlphaMMS 1

**Theorem.** An allocation $A$ satisfies the exact MMS guarantee
([[social_choice.fair_division.indivisible.maximin_share]]) if and only
if it is 1-MMS in the α-MMS sense
([[social_choice.fair_division.indivisible.is_alpha_mms]]):
$$
\mathrm{IsMaxminShare}\ v\ \mathrm{allGoods}\ A \;\iff\; \mathrm{IsAlphaMMS}\ 1\ v\ \mathrm{allGoods}\ A.
$$

In Lean: `SocialChoice.FairDivision.Indivisible.isMaxminShare_iff_isAlphaMMS_one`.

## Proof

Unfold both predicates against the MMS value
([[social_choice.fair_division.indivisible.mms_value]]):

- *IsAlphaMMS 1* states $1 \cdot \mathrm{MMS}_i \le v_i(A(i))$, i.e.\
  $\mathrm{MMS}_i \le v_i(A(i))$, i.e.\ agent $i$'s bundle value beats
  the maximin threshold.
- *IsMaxminShare* states the worst-bundle-of-any-partition $B$ is
  bounded by $v_i(A(i))$:
  $\forall B,\ \exists j,\ v_i(B(j)) \le v_i(A(i))$.

The bridge: $\forall B,\ \exists j,\ v_i(B(j)) \le v_i(A(i))$ is
exactly the statement that the maximin value $\max_B \min_j v_i(B(j))$
is bounded by $v_i(A(i))$, which is $\mathrm{MMS}_i \le v_i(A(i))$.

Both directions follow from the `mmsValue_le_of_forall` and
`iInf_partition_le_mmsValue` building blocks
([[social_choice.fair_division.indivisible.mms_value_bounds]]).

## Why both predicates exist

The two formulations are complementary:

- *IsMaxminShare* avoids `Finset.sup'` / `Finset.inf'` — a slick
  definition for *exact* MMS that doesn't require the auxiliary
  `mmsValue` function. Useful for stating theorems compactly.
- *IsAlphaMMS* parameterises smoothly over the approximation
  parameter — needed for $\alpha < 1$ approximation results.

This equivalence theorem lets call sites switch freely between the
two.

## References

- Budish, E. (2011). "The Combinatorial Assignment Problem". *J. Pol. Econ.*
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. MMS vs α-MMS equivalence at α = 1.
