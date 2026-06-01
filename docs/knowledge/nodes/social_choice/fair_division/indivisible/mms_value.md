---
id: social_choice.fair_division.indivisible.mms_value
title: Maximin Share Value
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.mms
uses:
  - social_choice.fair_division.indivisible.valuation
  - social_choice.fair_division.indivisible.allocation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.MMS
  declarations:
    - SocialChoice.FairDivision.Indivisible.mmsValue
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - mms
  - maximin-share
---

# Maximin Share Value

For an agent $i$, a valuation $v$
([[social_choice.fair_division.indivisible.valuation]]), and an outer
good set `allGoods : Finset G`, the *maximin share value* is
$$
\mathrm{MMS}_i \;=\; \max_{B \text{ complete}}\ \min_{j} v_i(B(j)),
$$
i.e. the maximum, over agent $i$'s self-partitions of `allGoods` into
$n$ bundles, of the worst-bundle value (from $i$'s own perspective).

In Lean: `SocialChoice.FairDivision.Indivisible.mmsValue v allGoods i`,
defined `noncomputable` with hypotheses `[Fintype N] [DecidableEq G]`.

The Lean definition packages the supremum-of-minimums using
`Finset.sup'` / `Finset.inf'` constructions over the set of complete
allocations.

## Why the definition is well-posed

- The set of complete allocations of `allGoods` is finite (a function
  from $N$ to a $\mathrm{Finset}\ G$, constrained by the partition
  property).
- For each complete allocation $B$, $\min_j v_i(B(j))$ is a finite min
  over the finite type $N$.

So $\mathrm{MMS}_i$ exists as a finite max of finite mins.

## Use

`mmsValue` is the threshold appearing in the *exact* MMS guarantee
([[social_choice.fair_division.indivisible.maximin_share]]) and in the
α-MMS approximation
([[social_choice.fair_division.indivisible.is_alpha_mms]]). The
predicate `IsMaxminShare A` (every agent's bundle has value $\ge
\mathrm{MMS}_i$) and the bound `mmsValue_le_proportional_share_additive`
([[social_choice.fair_division.indivisible.mms_value_bounds]]) both
quantify how close $A$ comes to this threshold.

## References

- Budish, E. (2011). "The Combinatorial Assignment Problem". *J. Pol. Econ.*
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Maximin share value.
