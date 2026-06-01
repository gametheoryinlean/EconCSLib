---
id: social_choice.fair_division.divisible.cut_and_choose_partition
title: Cut-and-Choose Output Is a Complete Partition
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.divisible
  - social_choice.fair_division.divisible.cut_and_choose
uses:
  - social_choice.fair_division.divisible.cut_and_choose_alloc
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Divisible.CutAndChoose
  declarations:
    - SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_isAllocation
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - divisible
  - cut-and-choose
---

# Cut-and-Choose Output Is a Complete Partition

**Theorem.** For any cut point $t \in I$ and any two-agent measure family
$\mu : \mathrm{Fin}\ 2 \to \mathrm{Measure}\ I$, the allocation produced by
cut-and-choose ([[social_choice.fair_division.divisible.cut_and_choose_alloc]])
is a complete measurable partition of the cake.

That is, `cutAndChooseAlloc μ t` satisfies the divisible
`IsAllocation` predicate ([[social_choice.fair_division.divisible.allocation]]):

- both pieces are measurable;
- the cutter's piece and the chooser's piece are disjoint;
- their union is the whole cake $I$.

In Lean: `cutAndChooseAlloc_isAllocation`.

## Proof outline

By case analysis on whether the chooser picks left or right:

- If $\mu_1(L) \ge \mu_1(R)$, agent 0 receives $R = (t, 1]$ and agent 1
  receives $L = [0, t]$. Both are measurable; $L \cap R = \emptyset$;
  $L \cup R = I$.

- Otherwise (the other branch of the protocol), the assignment is the
  same partition with pieces swapped between agents. The same three
  facts hold.

In either branch, the disjointness and cover conditions are immediate
properties of $[0, t]$ and $(t, 1]$ on the unit interval, and
measurability comes from the standard half-open / closed interval
constructors.

## Significance

This is the *feasibility* lemma for cut-and-choose: regardless of whether
the cut is "fair" for the cutter
([[social_choice.fair_division.divisible.cut_and_choose_alloc]]) or
arbitrary, the protocol always produces a valid measurable partition.
Fairness only enters when we ask whether the cutter is envy-free
([[social_choice.fair_division.divisible.cutter_envy_free_of_fair]]).

## References

- Robertson, J. M. and Webb, W. A. (1998). *Cake-Cutting Algorithms*, Ch. 1.
